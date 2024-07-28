use std::ops::Range;

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
