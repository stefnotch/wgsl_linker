use std::ops::Range;

use winnow::{
    ascii::{digit0, digit1, hex_digit1},
    combinator::{alt, cut_err, dispatch, empty, eof, fail, opt, peek, repeat, terminated, trace},
    error::ContextError,
    stream::Recoverable,
    token::{any, one_of, take_till, take_while},
    Located, PResult, Parser,
};

use crate::WgslParseError;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Token<'a> {
    Symbol(char),
    Paren(char),
    Number,
    Word(&'a str),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SpannedToken<'a> {
    pub token: Token<'a>,
    pub span: (usize, usize),
}
impl<'a> From<(Token<'a>, Range<usize>)> for SpannedToken<'a> {
    fn from((token, span): (Token<'a>, Range<usize>)) -> Self {
        Self {
            token,
            span: (span.start, span.end),
        }
    }
}

pub type TokenizerInput<'a> = Recoverable<Located<&'a str>, ContextError>;

// We implement ContainsToken so that we can match against tokens in the parser.
// (https://docs.rs/winnow/latest/winnow/_topic/stream/index.html)

impl<'a> winnow::stream::ContainsToken<SpannedToken<'a>> for SpannedToken<'a> {
    #[inline(always)]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        *self == token
    }
}

impl<'a> winnow::stream::ContainsToken<SpannedToken<'a>> for &'_ [SpannedToken<'a>] {
    #[inline]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        self.iter().any(|t| *t == token)
    }
}

impl<'a, const LEN: usize> winnow::stream::ContainsToken<SpannedToken<'a>>
    for &'_ [SpannedToken<'a>; LEN]
{
    #[inline]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        self.iter().any(|t| *t == token)
    }
}

impl<'a, const LEN: usize> winnow::stream::ContainsToken<SpannedToken<'a>>
    for [SpannedToken<'a>; LEN]
{
    #[inline]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        self.iter().any(|t| *t == token)
    }
}

impl<'a> winnow::stream::ContainsToken<SpannedToken<'a>> for Token<'a> {
    #[inline(always)]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        *self == token.token
    }
}

impl<'a> winnow::stream::ContainsToken<SpannedToken<'a>> for &'_ [Token<'a>] {
    #[inline]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        self.iter().any(|t| *t == token.token)
    }
}

impl<'a, const LEN: usize> winnow::stream::ContainsToken<SpannedToken<'a>>
    for &'_ [Token<'a>; LEN]
{
    #[inline]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        self.iter().any(|t| *t == token.token)
    }
}

impl<'a, const LEN: usize> winnow::stream::ContainsToken<SpannedToken<'a>> for [Token<'a>; LEN] {
    #[inline]
    fn contains_token(&self, token: SpannedToken<'a>) -> bool {
        self.iter().any(|t| *t == token.token)
    }
}

pub struct Tokenizer;

/// Similar in purpose to https://github.com/gfx-rs/wgpu/blob/trunk/naga/src/front/wgsl/parse/lexer.rs
impl Tokenizer {
    pub fn tokenize(input: &str) -> Result<Vec<SpannedToken>, WgslParseError> {
        let input = TokenizerInput::new(Located::new(input));
        let result = trace("tokenization", Self::tokens).parse(input);
        result.map_err(|e| WgslParseError {
            message: e.to_string(),
            position: e.offset(),
            context: e.into_inner(),
        })
    }

    pub fn tokens<'a>(input: &mut TokenizerInput<'a>) -> PResult<Vec<SpannedToken<'a>>> {
        terminated(
            repeat(0.., Self::token_fast).fold(
                || Vec::new(),
                |mut acc, token| {
                    match token {
                        Some(token) => acc.push(token),
                        None => {}
                    }
                    acc
                },
            ),
            cut_err(eof),
        )
        .parse_next(input)
    }

    pub fn token_fast<'a>(input: &mut TokenizerInput<'a>) -> PResult<Option<SpannedToken<'a>>> {
        dispatch! {peek(any);
            '_' => Self::word.map(Some),
            c if unicode_ident::is_xid_start(c) => Self::word.map(Some),
            '0' => dispatch! {peek((any, any)).map(|(_, b)| b);
                'x' | 'X' => Self::hex_literal.map(Some),
                _ => Self::decimal_literal.map(Some),
            },
            c if c.is_ascii_digit() => Self::decimal_literal.map(Some),
            '.' => dispatch! {peek((any, any)).map(|(_, b): (char, char)| b);
                c if c.is_ascii_digit() => Self::decimal_literal.map(Some),
                _ => Self::symbol.map(Some),
            },
            c if c.is_whitespace() => take_while(1.., |c: char| c.is_whitespace()).map(|_| None),
            '/' => dispatch! {peek((any, any)).map(|(_, b)| b);
                '/' => Self::single_line_comment.map(|_| None),
                '*' => Self::multi_line_comment.map(|_| None),
                _ => Self::symbol.map(Some),
            },
            '(' | ')' | '[' | ']' | '{' | '}' => Self::paren.map(Some),
            ':' | ';' | ',' |  '@' | '<' | '>' | '=' | '+' | '-' | '*' | '%' | '&' | '|' | '^' | '!' | '~' => Self::symbol.map(Some),
            _ => fail
        }
        .parse_next(input)
    }

    pub fn symbol<'a>(input: &mut TokenizerInput<'a>) -> PResult<SpannedToken<'a>> {
        one_of([
            ':', ';', ',', '.', '@', '<', '>', '=', '+', '-', '*', '/', '%', '&', '|', '^', '!',
            '~',
            // For the linker. Maybe we also need to support `#` for preprocessor directives.
            // And "quotes" for import paths.
            ':',
        ])
        .with_span()
        .map(|(v, span)| (Token::Paren(v), span).into())
        .parse_next(input)
    }

    pub fn paren<'a>(input: &mut TokenizerInput<'a>) -> PResult<SpannedToken<'a>> {
        one_of(['(', ')', '[', ']', '{', '}'])
            .with_span()
            .map(|(v, span)| (Token::Paren(v), span).into())
            .parse_next(input)
    }

    fn single_line_comment(input: &mut TokenizerInput<'_>) -> PResult<()> {
        let _start = "//".parse_next(input)?;
        let _text = take_till(0.., Self::is_newline_start).parse_next(input)?;
        let _newline = Self::new_line.parse_next(input)?;
        Ok(())
    }

    fn multi_line_comment(input: &mut TokenizerInput<'_>) -> PResult<()> {
        let _start = "/*".parse_next(input)?;
        loop {
            if let Some(_end) = opt("*/").parse_next(input)? {
                return Ok(());
            } else if let Some(_) = opt(Self::multi_line_comment).parse_next(input)? {
                // We found a nested comment, skip it
            } else {
                // Skip any other character
                // TODO: Eof error recovery
                let _ = take_till(1.., ('*', '/')).parse_next(input)?;
            }
        }
    }

    /// Checks if it's part of a Unicode line break, according to https://www.w3.org/TR/WGSL/#line-break
    fn is_newline_start(c: char) -> bool {
        c == '\u{000A}'
            || c == '\u{000B}'
            || c == '\u{000C}'
            || c == '\u{000D}'
            || c == '\u{0085}'
            || c == '\u{2028}'
            || c == '\u{2029}'
    }

    fn new_line(input: &mut TokenizerInput<'_>) -> PResult<()> {
        alt((
            "\u{000D}\u{000A}".map(|_| ()),
            one_of(Self::is_newline_start).map(|_| ()),
            eof.map(|_| ()),
        ))
        .parse_next(input)
    }

    pub fn word<'a>(input: &mut TokenizerInput<'a>) -> PResult<SpannedToken<'a>> {
        Self::ident_pattern_token
            .with_span()
            .map(|(v, span)| (Token::Word(v), span).into())
            .parse_next(input)
    }

    pub fn ident_pattern_token<'a>(input: &mut TokenizerInput<'a>) -> PResult<&'a str> {
        dispatch! {any;
            '_' => cut_err(take_while(1.., |c: char| unicode_ident::is_xid_continue(c))),
            c if unicode_ident::is_xid_start(c) => cut_err(take_while(0.., |c: char| unicode_ident::is_xid_continue(c))),
            _ => fail
        }
        .parse_next(input)
    }

    /// Combination of hex_int_literal and hex_float_literal
    pub fn hex_literal<'a>(input: &mut TokenizerInput<'a>) -> PResult<SpannedToken<'a>> {
        let _prefix = ('0', one_of(['x', 'X'])).parse_next(input)?;
        let start = opt(hex_digit1).parse_next(input)?;

        fn float_postfix(input: &mut TokenizerInput<'_>) -> PResult<()> {
            (
                one_of(['p', 'P']),
                opt(one_of(['+', '-'])),
                digit1,
                opt(one_of(['f', 'h'])),
            )
                .void()
                .parse_next(input)
        }

        if start.is_none() {
            return ('.', digit1, opt(float_postfix))
                .span()
                .map(|span| (Token::Number, span).into())
                .parse_next(input);
        }

        alt((
            one_of(['i', 'u']).void(),
            float_postfix.void(),
            ('.', digit0, opt(float_postfix)).void(),
            empty,
        ))
        .span()
        .map(|span| (Token::Number, span).into())
        .parse_next(input)
    }

    /// Combination of decimal_float_literal and decimal_int_literal
    pub fn decimal_literal<'a>(input: &mut TokenizerInput<'a>) -> PResult<SpannedToken<'a>> {
        fn e_part(input: &mut TokenizerInput<'_>) -> PResult<()> {
            (one_of(['e', 'E']), opt(one_of(['+', '-'])), digit1)
                .void()
                .parse_next(input)
        }
        fn fh(input: &mut TokenizerInput<'_>) -> PResult<()> {
            one_of(['f', 'h']).void().parse_next(input)
        }

        alt((
            ("00", cut_err(digit0), '.', digit0, opt(e_part), opt(fh)).void(),
            ('.', digit1, opt(e_part), opt(fh)).void(),
            (
                digit1,
                alt((
                    ('.', digit0, opt(e_part), opt(fh)).void(),
                    (e_part, opt(fh)).void(),
                    fh.void(),
                    (one_of(['i', 'u'])).void(), // Integer
                    empty,                       // Fall back to integer
                )),
            )
                .void(),
        ))
        .span()
        .map(|span| (Token::Number, span).into())
        .parse_next(input)
    }
}
