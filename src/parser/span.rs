#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}
impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn range(&self) -> std::ops::Range<usize> {
        self.start..self.end
    }

    pub fn text<'source>(&self, source: &'source str) -> &'source str {
        let range = self.range();
        &source[range]
    }
}

impl From<(usize, usize)> for Span {
    fn from(range: (usize, usize)) -> Self {
        Self::new(range.0, range.1)
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self::new(range.start, range.end)
    }
}
