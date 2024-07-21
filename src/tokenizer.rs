use std::ops::Range;

use winnow::{
    combinator::{alt, eof, opt, repeat},
    error::ContextError,
    stream::Recoverable,
    token::{one_of, take_till, take_while},
    Located, PResult, Parser,
};

pub type Input<'a> = Recoverable<Located<&'a str>, ContextError>;

pub struct Spaces {
    /// Comments that are in this "spaces" block
    pub comments: Vec<Range<usize>>,
}

/// Parses whitespaces or comments if there are any.
pub fn opt_spaces(input: &mut Input<'_>) -> PResult<Option<Spaces>> {
    opt(spaces).parse_next(input)
}

/// Parses at least one whitespace or comment.
pub fn spaces(input: &mut Input<'_>) -> PResult<Spaces> {
    repeat(
        1..,
        alt((
            take_while(1.., |c: char| c.is_whitespace()).map(|_| None),
            single_line_comment.span().map(|c| Some(c)),
            multi_line_comment.span().map(|c| Some(c)),
        )),
    )
    .fold(
        || Vec::new(),
        |mut comments, comment| {
            if let Some(comment) = comment {
                comments.push(comment);
            }
            comments
        },
    )
    .map(|comments| Spaces { comments })
    .parse_next(input)
}

fn single_line_comment(input: &mut Input<'_>) -> PResult<()> {
    let _start = "//".parse_next(input)?;
    let _text = take_till(0.., is_newline_start).parse_next(input)?;
    let _newline = new_line.parse_next(input)?;
    Ok(())
}

fn multi_line_comment(input: &mut Input<'_>) -> PResult<()> {
    let _start = "/*".parse_next(input)?;
    loop {
        if let Some(_end) = opt("*/").parse_next(input)? {
            return Ok(());
        } else if let Some(_) = opt(multi_line_comment).parse_next(input)? {
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

fn new_line(input: &mut Input<'_>) -> PResult<()> {
    alt((
        "\u{000D}\u{000A}".map(|_| ()),
        one_of(is_newline_start).map(|_| ()),
        eof.map(|_| ()),
    ))
    .parse_next(input)
}
