//! Low-level WGSL lexer.
//! Written in the style of rustc_lexer

use std::{ops::Range, str::Chars};

use super::parser::{Diagnostic, Span};
use crate::SyntaxKind;

pub struct Token {
    pub kind: SyntaxKind,
    pub len: u32,
}
impl Token {
    fn new(kind: SyntaxKind, len: u32) -> Token {
        Token { kind, len }
    }
}

/// Peekable iterator over a char sequence.
///
/// Next characters can be peeked via `first` method,
/// and position can be shifted forward via `bump` method.
pub struct Cursor<'a> {
    len_remaining: usize,
    /// Iterator over chars. Slightly faster than a &str.
    chars: Chars<'a>,
    #[cfg(debug_assertions)]
    prev: char,
}

const EOF_CHAR: char = '\0';

impl<'a> Cursor<'a> {
    pub fn new(input: &'a str) -> Cursor<'a> {
        Cursor {
            len_remaining: input.len(),
            chars: input.chars(),
            #[cfg(debug_assertions)]
            prev: EOF_CHAR,
        }
    }

    pub fn as_str(&self) -> &'a str {
        self.chars.as_str()
    }

    /// Returns the last eaten symbol (or `'\0'` in release builds).
    /// (For debug assertions only.)
    pub(crate) fn prev(&self) -> char {
        #[cfg(debug_assertions)]
        {
            self.prev
        }

        #[cfg(not(debug_assertions))]
        {
            EOF_CHAR
        }
    }

    /// Peeks the next symbol from the input stream without consuming it.
    /// If requested position doesn't exist, `EOF_CHAR` is returned.
    /// However, getting `EOF_CHAR` doesn't always mean actual end of file,
    /// it should be checked with `is_eof` method.
    pub fn first(&self) -> char {
        // `.next()` optimizes better than `.nth(0)`
        self.chars.clone().next().unwrap_or(EOF_CHAR)
    }

    /// Peeks the second symbol from the input stream without consuming it.
    pub(crate) fn second(&self) -> char {
        // `.next()` optimizes better than `.nth(1)`
        let mut iter = self.chars.clone();
        iter.next();
        iter.next().unwrap_or(EOF_CHAR)
    }

    /// Peeks the third symbol from the input stream without consuming it.
    pub fn third(&self) -> char {
        // `.next()` optimizes better than `.nth(2)`
        let mut iter = self.chars.clone();
        iter.next();
        iter.next();
        iter.next().unwrap_or(EOF_CHAR)
    }

    /// Checks if there is nothing more to consume.
    pub(crate) fn is_eof(&self) -> bool {
        self.chars.as_str().is_empty()
    }

    /// Returns amount of already consumed symbols.
    pub(crate) fn pos_within_token(&self) -> u32 {
        (self.len_remaining - self.chars.as_str().len()) as u32
    }

    /// Resets the number of bytes consumed to 0.
    pub(crate) fn reset_pos_within_token(&mut self) {
        self.len_remaining = self.chars.as_str().len();
    }

    /// Moves to the next character.
    pub(crate) fn bump(&mut self) -> Option<char> {
        let c = self.chars.next()?;

        #[cfg(debug_assertions)]
        {
            self.prev = c;
        }

        Some(c)
    }

    /// Moves to a substring by a number of bytes.
    pub(crate) fn bump_bytes(&mut self, n: usize) {
        self.chars = self.as_str()[n..].chars();
    }

    /// Eats symbols while predicate returns true or until the end of file is reached.
    pub(crate) fn eat_while(&mut self, mut predicate: impl FnMut(char) -> bool) {
        // It was tried making optimized version of this for eg. line comments, but
        // LLVM can inline all of this and compile it down to fast iteration over bytes.
        while predicate(self.first()) && !self.is_eof() {
            self.bump();
        }
    }

    pub(crate) fn eat_until(&mut self, byte: u8) {
        self.chars = match self.as_str().as_bytes().iter().position(|&b| b == byte) {
            Some(index) => self.as_str()[index..].chars(),
            None => "".chars(),
        }
    }

    /// Parses a token from the input string.
    pub fn advance_token(&mut self) -> Token {
        use crate::syntax_kind::SyntaxKind::*;

        let Some(first_char) = self.bump() else {
            return Token::new(SyntaxKind::EOF, 0);
        };

        // Ordered like naga
        // https://github.com/gfx-rs/wgpu/blob/10ce22b2ea0a01766b39d462cc3a1fd9495a43b1/naga/src/front/wgsl/parse/lexer.rs#L272
        let token_kind = match first_char {
            ':' => match self.first() {
                ':' => {
                    self.bump();
                    ColonColon
                }
                _ => Colon,
            },
            ';' => Semicolon,
            ',' => Comma,
            '.' => match self.first() {
                c @ '0'..='9' => self.number(c),
                _ => Period,
            },
            '@' => AttributeOperator,
            '(' => ParenthesisLeft,
            ')' => ParenthesisRight,
            '{' => BraceLeft,
            '}' => BraceRight,
            '[' => BracketLeft,
            ']' => BracketRight,

            // The actual templates are created in `collect_with_templates`
            '<' => match self.first() {
                '<' => {
                    self.bump();
                    match self.first() {
                        '=' => ShiftLeftEqual,
                        _ => ShiftLeft,
                    }
                }
                '=' => {
                    self.bump();
                    LessThanEqual
                }
                _ => LessThan,
            },
            '>' => match self.first() {
                // GreaterThanEqual and ShiftRight and ShiftRightEqual are purposefully skipped here
                _ => GreaterThan,
            },

            c @ '0'..='9' => self.number(c),
            '/' => match self.first() {
                '/' => self.line_comment(),
                '*' => self.block_comment(),
                '=' => {
                    self.bump();
                    DivisionEqual
                }
                _ => ForwardSlash,
            },

            '-' => match self.first() {
                '>' => {
                    self.bump();
                    Arrow
                }
                '-' => {
                    self.bump();
                    MinusMinus
                }
                '=' => {
                    self.bump();
                    MinusEqual
                }
                _ => Minus,
            },
            '+' => match self.first() {
                '+' => {
                    self.bump();
                    PlusPlus
                }
                '=' => {
                    self.bump();
                    PlusEqual
                }
                _ => Plus,
            },
            '*' => match self.first() {
                '=' => {
                    self.bump();
                    TimesEqual
                }
                _ => Star,
            },
            '%' => match self.first() {
                '=' => {
                    self.bump();
                    ModuloEqual
                }
                _ => Modulo,
            },
            '^' => match self.first() {
                '=' => {
                    self.bump();
                    XorEqual
                }
                _ => Xor,
            },
            '~' => Tilde,
            '=' => match self.first() {
                '=' => {
                    self.bump();
                    EqualEqual
                }
                _ => Equal,
            },
            '!' => match self.first() {
                '=' => {
                    self.bump();
                    NotEqual
                }
                _ => Bang,
            },

            '&' => match self.first() {
                '&' => {
                    self.bump();
                    AndAnd
                }
                '=' => {
                    self.bump();
                    AndEqual
                }
                _ => And,
            },
            '|' => match self.first() {
                '|' => {
                    self.bump();
                    OrOr
                }
                '=' => {
                    self.bump();
                    OrEqual
                }
                _ => Or,
            },

            '_' if unicode_ident::is_xid_continue(self.first()) => {
                self.bump();
                self.eat_while(unicode_ident::is_xid_continue);

                Identifier
            }
            '_' => Underscore,

            // Whitespace sequence.
            c if is_blankspace(c) => self.blankspace(),

            // Identifier (this should be checked after other variant that can
            // start as identifier).
            c if unicode_ident::is_xid_start(c) => self.ident_or_keyword(),

            _ => SyntaxKind::Error,
        };

        let res = Token::new(token_kind, self.pos_within_token());
        self.reset_pos_within_token();
        res
    }

    /// A line-ending comment is a kind of comment consisting of the two code points `//` (U+002F followed by U+002F)
    /// and the code points that follow, up until but not including:
    /// - the next line break, or
    /// - the end of the program.
    fn line_comment(&mut self) -> SyntaxKind {
        debug_assert!(self.prev() == '/' && self.first() == '/');
        self.bump();
        self.eat_while(|char| !is_line_ending_comment_end(char));
        SyntaxKind::LineEndingComment
    }

    fn block_comment(&mut self) -> SyntaxKind {
        debug_assert!(self.prev() == '/' && self.first() == '*');
        self.bump();

        let mut depth = 1usize;
        while let Some(c) = self.bump() {
            match c {
                '/' if self.first() == '*' => {
                    self.bump();
                    depth += 1;
                }
                '*' if self.first() == '/' => {
                    self.bump();
                    depth -= 1;
                    if depth == 0 {
                        // This block comment is closed, so for a construction like "/* */ */"
                        // there will be a successfully parsed block comment "/* */"
                        // and " */" will be processed separately.
                        break;
                    }
                }
                _ => (),
            }
        }

        let terminated = depth == 0;
        if terminated {
            SyntaxKind::BlockComment
        } else {
            SyntaxKind::Error
        }
    }

    fn blankspace(&mut self) -> SyntaxKind {
        debug_assert!(is_blankspace(self.prev()));
        self.eat_while(is_blankspace);
        SyntaxKind::Blankspace
    }

    fn ident_or_keyword(&mut self) -> SyntaxKind {
        debug_assert!(unicode_ident::is_xid_start(self.prev()));
        // Start is already eaten, eat the rest of identifier.
        self.eat_while(unicode_ident::is_xid_continue);

        SyntaxKind::Identifier
    }

    fn number(&mut self, first_digit: char) -> SyntaxKind {
        debug_assert!(('0' <= self.prev() && self.prev() <= '9') || self.prev() == '.');

        self.eat_decimal_digits();
        SyntaxKind::IntLiteral
    }

    fn eat_decimal_digits(&mut self) -> bool {
        let mut has_digits = false;
        loop {
            match self.first() {
                '_' => {
                    self.bump();
                }
                '0'..='9' => {
                    has_digits = true;
                    self.bump();
                }
                _ => break,
            }
        }
        has_digits
    }

    fn eat_hexadecimal_digits(&mut self) -> bool {
        let mut has_digits = false;
        loop {
            match self.first() {
                '_' => {
                    self.bump();
                }
                '0'..='9' | 'a'..='f' | 'A'..='F' => {
                    has_digits = true;
                    self.bump();
                }
                _ => break,
            }
        }
        has_digits
    }

    /// Eats the float exponent. Returns true if at least one digit was met,
    /// and returns false otherwise.
    fn eat_float_exponent(&mut self) -> bool {
        debug_assert!(self.prev() == 'e' || self.prev() == 'E');
        if self.first() == '-' || self.first() == '+' {
            self.bump();
        }
        self.eat_decimal_digits()
    }
}

/// See: <https://www.w3.org/TR/WGSL/#blankspace-and-line-breaks>
/// The comment does not include the line break.
fn is_line_ending_comment_end(character: char) -> bool {
    [
        '\u{000A}', // line feed
        '\u{000B}', // vertical tab
        '\u{000C}', // form feed
        '\u{000D}', // carriage return when not also followed by line feed or carriage return followed by line feed
        '\u{0085}', // next line
        '\u{2028}', // line separator
        '\u{2029}', // paragraph separator
    ]
    .contains(&character)
}

fn is_blankspace(c: char) -> bool {
    match c {
        '\u{0020}'
        | '\u{0009}'..='\u{000d}'
        | '\u{0085}'
        | '\u{200e}'
        | '\u{200f}'
        | '\u{2028}'
        | '\u{2029}' => true,
        _ => false,
    }
}

/// Mutate tokens to be templates using <https://www.w3.org/TR/WGSL/#template-list-discovery>.
/// `<` and `>` tokens can be turned into template starts.
/// A pair of `>` `>` can start with a template end, or be a right shift.
/// Same goes for `>` `=` and `>` `>` `=`.
///
/// Meanwhile `<<` and `<<=` are unambiguously handled in the lexer,
/// since a template cannot start with those.
pub fn tokenize(
    source: &str,
    diagnostics: &mut Vec<Diagnostic>,
) -> (Vec<SyntaxKind>, Vec<Range<usize>>) {
    let mut cursor = Cursor::new(source);
    let mut prev_end = 0usize;
    let mut tokens_iter = std::iter::from_fn(move || {
        let token = cursor.advance_token();
        let span: Range<usize> = {
            let start = prev_end;
            let end = start + token.len as usize;
            prev_end = end;
            start..end
        };

        if token.kind != SyntaxKind::EOF {
            Some((token.kind, span))
        } else {
            None
        }
    })
    .peekable();

    let mut nesting_depth = 0;
    let mut pending: Vec<(usize, i32)> = vec![];
    let mut tokens = vec![];
    let mut spans = vec![];

    while let Some((mut token, span)) = tokens_iter.next() {
        if token == SyntaxKind::Identifier {
            token = match &source[span.clone()] {
                "alias" => SyntaxKind::Alias,
                "break" => SyntaxKind::Break,
                "case" => SyntaxKind::Case,
                "const_assert" => SyntaxKind::ConstantAssert,
                "const" => SyntaxKind::Const,
                "continue" => SyntaxKind::Continue,
                "continuing" => SyntaxKind::Continuing,
                "default" => SyntaxKind::Default,
                "diagnostic" => SyntaxKind::Diagnostic,
                "discard" => SyntaxKind::Discard,
                "else" => SyntaxKind::Else,
                "enable" => SyntaxKind::Enable,
                "false" => SyntaxKind::False,
                "fn" => SyntaxKind::Fn,
                "for" => SyntaxKind::For,
                "if" => SyntaxKind::If,
                "let" => SyntaxKind::Let,
                "loop" => SyntaxKind::Loop,
                "override" => SyntaxKind::Override,
                "requires" => SyntaxKind::Requires,
                "return" => SyntaxKind::Return,
                "struct" => SyntaxKind::Struct,
                "switch" => SyntaxKind::Switch,
                "true" => SyntaxKind::True,
                "var" => SyntaxKind::Var,
                "while" => SyntaxKind::While,

                // These WGSL reserved words are keywords in WESL
                "import" => SyntaxKind::Import,
                "package" => SyntaxKind::Package,
                "super" => SyntaxKind::Super,
                "as" => SyntaxKind::As,

                _ => SyntaxKind::Identifier,
            };
        }

        tokens.push(token);
        spans.push(span.clone());
        match token {
            SyntaxKind::Identifier | SyntaxKind::Var => {
                // Skip to next non-whitespace token
                while let Some((
                    SyntaxKind::Blankspace
                    | SyntaxKind::LineEndingComment
                    | SyntaxKind::BlockComment,
                    _,
                )) = tokens_iter.peek()
                {
                    let (next_token, next_span) = tokens_iter.next().unwrap();
                    tokens.push(next_token);
                    spans.push(next_span);
                }

                if let Some((SyntaxKind::LessThan, _)) = tokens_iter.peek() {
                    let (next_token, next_span) = tokens_iter.next().unwrap();
                    tokens.push(next_token);
                    spans.push(next_span);

                    pending.push((tokens.len() - 1, nesting_depth));
                }
            }
            SyntaxKind::GreaterThan => {
                if let Some((start_token, _)) = pending.pop_if(|(_, depth)| *depth == nesting_depth)
                {
                    // We found templates!
                    tokens[start_token] = SyntaxKind::TemplateStart;
                    *tokens.last_mut().unwrap() = SyntaxKind::TemplateEnd;
                } else {
                    // Patch up >>, >>=, >>==, >=, >==
                    // Precondition: pending.last().depth != nesting_depth
                    match tokens_iter.peek() {
                        Some((SyntaxKind::GreaterThan, span)) => {
                            // Might be a `>>`
                            *tokens.last_mut().unwrap() = SyntaxKind::ShiftRight;
                            spans[tokens.len() - 1].end = span.end;
                            tokens_iter.next();
                            match tokens_iter.peek() {
                                Some((SyntaxKind::Equal, span)) => {
                                    // Is a >>=
                                    *tokens.last_mut().unwrap() = SyntaxKind::ShiftRightEqual;
                                    spans[tokens.len() - 1].end = span.end;
                                    tokens_iter.next();
                                }
                                Some((SyntaxKind::EqualEqual, span)) => {
                                    // Is a >>= =
                                    *tokens.last_mut().unwrap() = SyntaxKind::ShiftRightEqual;
                                    let middle = span.start + 1;
                                    spans[tokens.len() - 1].end = middle;
                                    tokens.push(SyntaxKind::Equal);
                                    spans.push(middle..span.end);
                                    nesting_depth = 0;
                                    pending.clear();
                                    tokens_iter.next();
                                }
                                _ => {}
                            }
                        }
                        Some((SyntaxKind::Equal, span)) => {
                            // Is a >=
                            *tokens.last_mut().unwrap() = SyntaxKind::GreaterThanEqual;
                            spans[tokens.len() - 1].end = span.end;
                            tokens_iter.next();
                        }
                        Some((SyntaxKind::EqualEqual, span)) => {
                            // Is a >= =
                            *tokens.last_mut().unwrap() = SyntaxKind::GreaterThanEqual;
                            let middle = span.start + 1;
                            spans[tokens.len() - 1].end = middle;
                            tokens.push(SyntaxKind::Equal);
                            spans.push(middle..span.end);
                            nesting_depth = 0;
                            pending.clear();
                            tokens_iter.next();
                        }
                        _ => {}
                    }
                }
            }
            SyntaxKind::ParenthesisLeft | SyntaxKind::BracketLeft => {
                nesting_depth += 1;
            }
            SyntaxKind::ParenthesisRight | SyntaxKind::BracketRight => {
                // Pop Pending stack until its top entry has depth < NestingDepth.
                while pending
                    .pop_if(|(_, depth)| *depth >= nesting_depth)
                    .is_some()
                {}
                nesting_depth = (nesting_depth - 1).max(0);
            }
            SyntaxKind::Equal
            | SyntaxKind::Semicolon
            | SyntaxKind::BraceLeft
            | SyntaxKind::Colon => {
                // These tokens do not appear in expressions,
                // so they aren't in a template
                nesting_depth = 0;
                pending.clear();
            }
            SyntaxKind::AndAnd | SyntaxKind::OrOr => {
                while pending
                    .pop_if(|(_, depth)| *depth >= nesting_depth)
                    .is_some()
                {}
            }
            SyntaxKind::Error => {
                diagnostics.push(Diagnostic {
                    message: "unexpected tokens".to_owned(),
                    range: span,
                });
            }
            _ => {}
        }
    }

    (tokens, spans)
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use expect_test::expect;

    use super::{Token, tokenize};

    fn check_lex(source: &str, expect: expect_test::Expect) {
        let mut diagnostics = vec![];
        let (tokens, _) = tokenize(source, &mut diagnostics);
        let mut expected = format!("{tokens:?}");
        if !diagnostics.is_empty() {
            writeln!(expected, "\n{diagnostics:?}");
        }
        expect.assert_eq(&expected);
    }

    #[expect(clippy::needless_pass_by_value, reason = "intended API")]
    fn check_lex_spanned(source: &str, expect: expect_test::Expect) {
        let mut diagnostics = Vec::new();
        let (tokens, spans) = tokenize(source, &mut diagnostics);
        let mut tokens_with_spans: String =
            tokens
                .into_iter()
                .zip(spans)
                .fold(String::new(), |mut output, (token, span)| {
                    _ = writeln!(output, "{token:?}@{}..{}", span.start, span.end);
                    output
                });
        for diagnostic in diagnostics {
            _ = writeln!(
                tokens_with_spans,
                "Error: {}@{}..{}",
                diagnostic.message, diagnostic.range.start, diagnostic.range.end
            );
        }
        expect.assert_eq(&tokens_with_spans);
    }

    #[test]
    fn lex_decimal_float() {
        check_lex("10.0", expect![["[FloatLiteral]"]]);
        check_lex("-10.0", expect![["[Minus, FloatLiteral]"]]);
        check_lex("1e9f", expect![["[FloatLiteral]"]]);
        check_lex("-0.0e7", expect!["[Minus, FloatLiteral]"]);
        check_lex(".1", expect![["[FloatLiteral]"]]);
        check_lex("1.", expect![["[FloatLiteral]"]]);
    }

    #[test]
    fn lex_hex_float() {
        check_lex("0x0.0", expect![["[FloatLiteral]"]]);
        check_lex("0X1p9", expect![["[FloatLiteral]"]]);
        check_lex("-0x0.0", expect![["[Minus, FloatLiteral]"]]);
        check_lex("0xff.13p13", expect![["[FloatLiteral]"]]);
    }

    #[test]
    fn lex_comment() {
        check_lex(
            "// test asdf\nnot_comment",
            expect![["[LineEndingComment, Blankspace, Identifier]"]],
        );
    }

    #[test]
    fn lex_odd_whitespace_comment() {
        check_lex_spanned(
            "\n\r//\r\nnot_comment\r\n//foo\n\ra",
            expect![["
                Blankspace@0..2
                LineEndingComment@2..4
                Blankspace@4..6
                Identifier@6..17
                Blankspace@17..19
                LineEndingComment@19..24
                Blankspace@24..26
                Identifier@26..27
            "]],
        );
    }

    #[test]
    fn lex_nested_brackets() {
        // Expect: Identifier (a), [, Identifier (a), [, IntLiteral (0), ], ]
        check_lex(
            "a[a[0]]",
            expect![
                "[Identifier, BracketLeft, Identifier, BracketLeft, IntLiteral, BracketRight, BracketRight]"
            ],
        );
    }

    #[test]
    fn lex_nested_templates() {
        check_lex_spanned(
            "foo<X>",
            expect![["
            Identifier@0..3
            TemplateStart@3..4
            Identifier@4..5
            TemplateEnd@5..6
        "]],
        );
        check_lex_spanned(
            "foo<X<Y>>",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                Identifier@4..5
                TemplateStart@5..6
                Identifier@6..7
                TemplateEnd@7..8
                TemplateEnd@8..9
            "]],
        );
        check_lex_spanned(
            "foo<X<Y<Z>>>",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                Identifier@4..5
                TemplateStart@5..6
                Identifier@6..7
                TemplateStart@7..8
                Identifier@8..9
                TemplateEnd@9..10
                TemplateEnd@10..11
                TemplateEnd@11..12
            "]],
        );
    }

    #[test]
    fn lex_template_with_brackets() {
        // cases from the WGSL spec
        check_lex_spanned(
            "foo<i32,select(2,3,a>b)>",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                Identifier@4..7
                Comma@7..8
                Identifier@8..14
                ParenthesisLeft@14..15
                IntLiteral@15..16
                Comma@16..17
                IntLiteral@17..18
                Comma@18..19
                Identifier@19..20
                GreaterThan@20..21
                Identifier@21..22
                ParenthesisRight@22..23
                TemplateEnd@23..24
            "]],
        );
        check_lex_spanned(
            "foo<(B>=C)>a",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                ParenthesisLeft@4..5
                Identifier@5..6
                GreaterThanEqual@6..8
                Identifier@8..9
                ParenthesisRight@9..10
                TemplateEnd@10..11
                Identifier@11..12
            "]],
        );
        check_lex_spanned(
            "foo<(B!=C)>a",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                ParenthesisLeft@4..5
                Identifier@5..6
                NotEqual@6..8
                Identifier@8..9
                ParenthesisRight@9..10
                TemplateEnd@10..11
                Identifier@11..12
            "]],
        );
        check_lex_spanned(
            "foo<(B==C)>a",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                ParenthesisLeft@4..5
                Identifier@5..6
                EqualEqual@6..8
                Identifier@8..9
                ParenthesisRight@9..10
                TemplateEnd@10..11
                Identifier@11..12
            "]],
        );
    }

    #[test]
    fn lex_not_templates() {
        check_lex_spanned(
            "foo<d]>",
            expect![["
                Identifier@0..3
                LessThan@3..4
                Identifier@4..5
                BracketRight@5..6
                GreaterThan@6..7
            "]],
        );
        check_lex_spanned(
            "foo",
            expect![["
            Identifier@0..3
        "]],
        );
        check_lex_spanned(
            "foo<b || c>d",
            expect![["
            Identifier@0..3
            LessThan@3..4
            Identifier@4..5
            Blankspace@5..6
            OrOr@6..8
            Blankspace@8..9
            Identifier@9..10
            GreaterThan@10..11
            Identifier@11..12
        "]],
        );
    }

    #[test]
    fn lex_templates_with_symbols() {
        check_lex_spanned(
            "foo<B<<C>",
            expect![["
                Identifier@0..3
                TemplateStart@3..4
                Identifier@4..5
                ShiftLeft@5..7
                Identifier@7..8
                TemplateEnd@8..9
            "]],
        );
        check_lex_spanned(
            "foo<B<=C>",
            expect![["
            Identifier@0..3
            TemplateStart@3..4
            Identifier@4..5
            LessThanEqual@5..7
            Identifier@7..8
            TemplateEnd@8..9
        "]],
        );

        check_lex_spanned(
            "foo<>",
            expect![["
            Identifier@0..3
            TemplateStart@3..4
            TemplateEnd@4..5
        "]],
        );
    }

    #[test]
    fn lex_templates_with_ends() {
        check_lex_spanned(
            "A<B>>C",
            expect![["
                Identifier@0..1
                TemplateStart@1..2
                Identifier@2..3
                TemplateEnd@3..4
                GreaterThan@4..5
                Identifier@5..6
            "]],
        );
        check_lex_spanned(
            "A<B>==C",
            expect![["
                Identifier@0..1
                TemplateStart@1..2
                Identifier@2..3
                TemplateEnd@3..4
                EqualEqual@4..6
                Identifier@6..7
            "]],
        );
        check_lex_spanned(
            "C<A<B>=C>",
            expect![["
                Identifier@0..1
                LessThan@1..2
                Identifier@2..3
                TemplateStart@3..4
                Identifier@4..5
                TemplateEnd@5..6
                Equal@6..7
                Identifier@7..8
                GreaterThan@8..9
            "]],
        );
    }

    #[test]
    fn lex_bitcast_template() {
        check_lex_spanned(
            "bitcast<vec4<u32>>(x)",
            expect![["
                Identifier@0..7
                TemplateStart@7..8
                Identifier@8..12
                TemplateStart@12..13
                Identifier@13..16
                TemplateEnd@16..17
                TemplateEnd@17..18
                ParenthesisLeft@18..19
                Identifier@19..20
                ParenthesisRight@20..21
            "]],
        );
    }

    #[test]
    fn lex_var_template() {
        check_lex_spanned(
            "var<function> x: u32;",
            expect![["
                Var@0..3
                TemplateStart@3..4
                Identifier@4..12
                TemplateEnd@12..13
                Blankspace@13..14
                Identifier@14..15
                Colon@15..16
                Blankspace@16..17
                Identifier@17..20
                Semicolon@20..21
            "]],
        );
    }

    #[test]
    fn lex_template_trailing_comment() {
        check_lex_spanned(
            "override x: array<
                u32,
                2,
            >;",
            expect![[r#"
                Override@0..8
                Blankspace@8..9
                Identifier@9..10
                Colon@10..11
                Blankspace@11..12
                Identifier@12..17
                TemplateStart@17..18
                Blankspace@18..35
                Identifier@35..38
                Comma@38..39
                Blankspace@39..56
                IntLiteral@56..57
                Comma@57..58
                Blankspace@58..71
                TemplateEnd@71..72
                Semicolon@72..73
            "#]],
        );
    }

    #[test]
    fn lex_nested_comment() {
        check_lex_spanned(
            "foo /* bar /* // */ baz */",
            expect![["
                Identifier@0..3
                Blankspace@3..4
                BlockComment@4..26
            "]],
        );
    }

    #[test]
    fn lex_unclosed_comment() {
        check_lex_spanned(
            "foo /*",
            expect![["
                Identifier@0..3
                Blankspace@3..4
                Error@4..6
                Error: unexpected tokens@4..6
            "]],
        );
    }

    #[test]
    fn lex_leading_zeros() {
        check_lex_spanned(
            "007",
            expect![[r#"
                IntLiteral@0..1
                IntLiteral@1..2
                IntLiteral@2..3
            "#]],
        );
    }
}
