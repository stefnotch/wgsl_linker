use winnow::{
    ascii::{digit0, digit1, hex_digit1},
    combinator::{alt, cut_err, dispatch, empty, eof, fail, opt, peek, repeat, terminated, trace},
    error::ContextError,
    stream::Recoverable,
    token::{any, one_of, take_till, take_while},
    Located, PResult, Parser,
};

use crate::{
    token::{SpannedToken, Token},
    WgslParseError,
};

pub type TokenizerInput<'a> = Recoverable<Located<&'a str>, ContextError>;

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
            repeat(0.., Self::token_fast.with_span()).fold(Vec::new, |mut acc, (token, span)| {
                if let Some(token) = token {
                    acc.push((token, span).into())
                }
                acc
            }),
            cut_err(eof),
        )
        .parse_next(input)
    }

    pub fn token_fast<'a>(input: &mut TokenizerInput<'a>) -> PResult<Option<Token<'a>>> {
        dispatch! {peek(any);
            '_' => dispatch! {peek((any, any)).map(|(_, b)| b);
                c if unicode_ident::is_xid_continue(c) => Self::word.map(Some),
                _ => Self::symbol.map(Some),
            },
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

    pub fn symbol<'a>(input: &mut TokenizerInput<'a>) -> PResult<Token<'a>> {
        one_of([
            ':', ';', ',', '.', '@', '<', '>', '=', '+', '-', '*', '/', '%', '&', '|', '^', '!',
            '~', // Extra token for the _ = expr; syntax
            '_',
            // For the linker. Maybe we also need to support `#` for preprocessor directives.
            // And "quotes" for import paths.
            ':',
        ])
        .map(Token::Symbol)
        .parse_next(input)
    }

    pub fn paren<'a>(input: &mut TokenizerInput<'a>) -> PResult<Token<'a>> {
        one_of(['(', ')', '[', ']', '{', '}'])
            .map(Token::Paren)
            .parse_next(input)
    }

    fn single_line_comment(input: &mut TokenizerInput<'_>) -> PResult<()> {
        ("//", take_till(0.., Self::is_newline_start), Self::new_line)
            .void()
            .parse_next(input)
    }

    fn multi_line_comment(input: &mut TokenizerInput<'_>) -> PResult<()> {
        let _start = "/*".parse_next(input)?;
        loop {
            if let Some(_end) = opt("*/").parse_next(input)? {
                return Ok(());
            } else if let Some(_nested_comment) = opt(Self::multi_line_comment).parse_next(input)? {
                // Skip nested comments
            } else {
                // Skip any other character
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
            "\u{000D}\u{000A}".void(),
            one_of(Self::is_newline_start).void(),
            eof.void(),
        ))
        .parse_next(input)
    }

    pub fn word<'a>(input: &mut TokenizerInput<'a>) -> PResult<Token<'a>> {
        Self::ident_pattern_token.map(Token::Word).parse_next(input)
    }

    pub fn ident_pattern_token<'a>(input: &mut TokenizerInput<'a>) -> PResult<&'a str> {
        dispatch! {any;
            '_' => cut_err(take_while(1.., unicode_ident::is_xid_continue)),
            c if unicode_ident::is_xid_start(c) => cut_err(take_while(0.., unicode_ident::is_xid_continue)),
            _ => fail
        }
        .take()
        .parse_next(input)
    }

    /// Combination of hex_int_literal and hex_float_literal
    pub fn hex_literal<'a>(input: &mut TokenizerInput<'a>) -> PResult<Token<'a>> {
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
                .map(|_| Token::Number)
                .parse_next(input);
        }

        alt((
            one_of(['i', 'u']).void(),
            float_postfix.void(),
            ('.', digit0, opt(float_postfix)).void(),
            empty,
        ))
        .map(|_| Token::Number)
        .parse_next(input)
    }

    /// Combination of decimal_float_literal and decimal_int_literal
    pub fn decimal_literal<'a>(input: &mut TokenizerInput<'a>) -> PResult<Token<'a>> {
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
        .map(|_| Token::Number)
        .parse_next(input)
    }
}
