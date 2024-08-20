mod parser_output;
mod rewriter;
mod span;
mod token;
mod tokenizer;

pub use span::Span;
pub use tokenizer::Tokenizer;
use winnow::{
    combinator::{
        alt, cut_err, delimited, dispatch, empty, eof, fail, not, opt, peek, preceded, repeat,
        separated, seq, terminated,
    },
    error::{
        ContextError, ErrMode, ErrorKind, ParseError, ParserError, StrContext, StrContextValue,
    },
    stream::Stream,
    token::{any, one_of, take_till},
    PResult, Parser,
};

pub use parser_output::{Ast, AstNode, VariableSpan, WgslParseError};
pub use rewriter::{PropertiesIter, RewriteAction, Rewriter, VariableRewriteAction, Visitor};
pub use token::{SpannedToken, Token};

pub fn parse(input: &str) -> Result<Ast, WgslParseError> {
    let tokens = Tokenizer::tokenize(input)?;
    let ast = WgslParser::parse(&tokens)?;
    Ok(ast)
}

// winnow::error::TreeError<&'a [SpannedToken<'a>]>
pub type Input<'a> = &'a [SpannedToken<'a>];

/// A basic parser for the purposes of linking multiple WGSL modules together.
pub struct WgslParser;

#[derive(Copy, Clone, PartialEq, Eq)]
enum IsTemplateResult {
    Yes,
    No,
}
#[derive(Default)]
enum Op {
    AndOr,
    GreaterThan,
    #[default]
    Other,
}

struct DisplayParseError<'error, T> {
    error: &'error T,
}

impl<'a, 'error> core::fmt::Display
    for DisplayParseError<'error, ParseError<&'a [SpannedToken<'a>], ContextError>>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let tokens = self.error.input();
        let offset = self.error.offset();
        let tokens_at_error = &tokens[offset..];
        let error_message = self.error.inner().to_string();

        match tokens_at_error.first() {
            Some(token) => {
                writeln!(f, "parse error at offset {}.", token.span.start)?;
                let tokens_before_error = &tokens[offset.saturating_sub(2)..offset];
                let tokens_after_error = &tokens[offset..(offset + 5).min(tokens.len())];
                let mut tokens_before_text = String::new();
                for token in tokens_before_error {
                    tokens_before_text.push_str(format!("{:?} ", token.token).as_str());
                }
                write!(f, "{}", tokens_before_text)?;
                for token in tokens_after_error {
                    write!(f, "{:?} ", token.token)?;
                }
                writeln!(f)?;
                for _ in 0..tokens_before_text.len() {
                    write!(f, " ")?;
                }
                writeln!(f, "^{}", error_message)?;
            }
            None => writeln!(f, "{}.", error_message)?,
        };
        Ok(())
    }
}

impl<'a> From<ParseError<&'a [SpannedToken<'a>], ContextError>> for WgslParseError {
    fn from(error: ParseError<&'a [SpannedToken<'a>], ContextError>) -> Self {
        let position = error.offset();
        let message = (DisplayParseError { error: &error }).to_string();
        let context = error.into_inner().context().cloned().collect();

        WgslParseError {
            message,
            position,
            context,
        }
    }
}

impl WgslParser {
    pub fn parse<'a>(input: &'a [SpannedToken<'a>]) -> Result<Ast, WgslParseError> {
        Self::translation_unit.parse(input).map_err(|e| e.into())
    }

    pub fn translation_unit(input: &mut Input<'_>) -> PResult<Ast> {
        let imports = Self::imports
            .context(StrContext::Label("imports"))
            .parse_next(input)?;
        Self::global_directives
            .context(StrContext::Label("directives"))
            .parse_next(input)?;
        let declarations = Self::global_decls
            .context(StrContext::Label("global declarations"))
            .parse_next(input)?;
        let _ = cut_err(eof)
            .context(StrContext::Label("end of WGSL file"))
            .parse_next(input)?;

        Ok(imports.into_iter().chain(declarations).collect())
    }

    pub fn imports(input: &mut Input<'_>) -> PResult<Vec<Ast>> {
        repeat(0.., Self::import).parse_next(input)
    }

    pub fn import(input: &mut Input<'_>) -> PResult<Ast> {
        preceded(word("import"), cut_err(Self::import_path))
            .context(StrContext::Label("import statement"))
            .parse_next(input)
    }

    fn import_path(input: &mut Input<'_>) -> PResult<Ast> {
        let parts = repeat(
            1..,
            terminated(
                alt((
                    symbol_pair(['.', '.']).map(|_| AstNode::ImportDotDotPart),
                    symbol('.').map(|_| AstNode::ImportDotPart),
                    Self::ident.map(AstNode::ImportModulePart),
                )),
                symbol('/'),
            ),
        )
        .map(|v: Vec<_>| v.into_iter().collect::<Ast>())
        .verify(|v| matches!(v.0.last(), Some(&AstNode::ImportModulePart(_))))
        .parse_next(input)?;
        let end = alt((
            Self::import_collection,
            Self::item_import,
            Self::star_import,
        ))
        .parse_next(input)?;
        Ok(parts.join(end))
    }

    fn import_collection(input: &mut Input<'_>) -> PResult<Ast> {
        parens(
            '{',
            cut_err(comma_separated(
                1..,
                alt((Self::import_path, Self::item_import)),
            ))
            .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
            '}',
        )
        .context(StrContext::Label("import collection"))
        .parse_next(input)
    }

    fn star_import(input: &mut Input<'_>) -> PResult<Ast> {
        preceded(
            symbol('*'),
            opt(preceded(word("as"), cut_err(Self::ident)))
                .context(StrContext::Label("import alias")),
        )
        .context(StrContext::Label("star import"))
        .map(|alias| Ast::single(AstNode::ImportStar { alias }))
        .parse_next(input)
    }

    fn item_import(input: &mut Input<'_>) -> PResult<Ast> {
        (
            Self::ident,
            opt(preceded(word("as"), cut_err(Self::ident)))
                .context(StrContext::Label("import alias")),
        )
            .context(StrContext::Label("item import"))
            .map(|(variable, alias)| Ast::single(AstNode::ImportVariable { variable, alias }))
            .parse_next(input)
    }

    /// We don't verify the global_directives rules.
    /// Instead we just trust the shader author to have specified all the important ones in the main file.
    pub fn global_directives(input: &mut Input<'_>) -> PResult<()> {
        repeat(0.., Self::global_directive).parse_next(input)
    }

    pub fn global_directive(input: &mut Input<'_>) -> PResult<()> {
        let _start = alt((
            keyword("diagnostic"),
            keyword("enable"),
            keyword("requires"),
        ))
        .parse_next(input)?;
        let _rule = cut_err(take_till(1.., Token::Symbol(';')))
            .context(StrContext::Label("directive"))
            .parse_next(input)?;
        let _end = must_symbol(';').parse_next(input)?;
        Ok(())
    }

    pub fn global_decls(input: &mut Input<'_>) -> PResult<Vec<Ast>> {
        repeat(
            0..,
            Self::global_decl.context(StrContext::Label("top level declaration")),
        )
        .parse_next(input)
    }

    pub fn global_decl(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some(non_attributed_global) = opt(dispatch! {any.map(|v: SpannedToken| v.token);
                Token::Symbol(';') => empty.default_value::<Ast>(),
                Token::Keyword("alias") => cut_err(Self::continue_global_alias).context(StrContext::Label("alias")),
                Token::Keyword("const_assert") => cut_err(terminated(Self::expression, must_symbol(';'))).context(StrContext::Label("const assertion")),
                Token::Keyword("struct") => cut_err(Self::continue_global_struct).context(StrContext::Label("struct")),
                Token::Keyword("const") => cut_err(Self::continue_global_const).context(StrContext::Label("constant")),
                _ => fail,
        })
        .parse_next(input)?
        {
            return Ok(non_attributed_global);
        }

        let attributes = Self::attributes.parse_next(input)?;

        let decl =
            alt((Self::global_fn, Self::global_var, Self::global_override)).parse_next(input)?;
        Ok(attributes.join(decl))
    }

    fn attributes(input: &mut Input<'_>) -> PResult<Ast> {
        repeat(0.., Self::attribute)
            .context(StrContext::Label("optional attributes"))
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }

    fn continue_global_alias(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            cut_err(Self::declare_ident).context(StrContext::Label("alias name")),
            _: must_symbol('='),
            cut_err(Self::type_specifier).context(StrContext::Label("alias type")),
            _: must_symbol(';'),
        )
        .map(|(a, c)| a.join(c))
        .parse_next(input)
    }

    fn continue_global_struct(input: &mut Input<'_>) -> PResult<Ast> {
        (
            cut_err(Self::declare_ident).context(StrContext::Label("struct name")),
            cut_err(parens(
                '{',
                comma_separated(
                    1..,
                    (
                        Self::attributes,
                        (Self::ident.void(), must_symbol(':')),
                        Self::type_specifier,
                    )
                        .map(|(a, _, b)| a.join(b)),
                )
                .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
                '}',
            ))
            .context(StrContext::Label("struct body")),
        )
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    fn continue_global_const(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            cut_err(Self::declare_typed_ident).context(StrContext::Label("constant name")),
            _: must_symbol('='),
            cut_err(Self::expression).context(StrContext::Label("constant value")),
            _: must_symbol(';'),
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }

    fn global_fn(input: &mut Input<'_>) -> PResult<Ast> {
        let _ = keyword("fn").parse_next(input)?;
        let name = cut_err(Self::declare_ident)
            .context(StrContext::Label("function name"))
            .parse_next(input)?;

        let params = cut_err(parens(
            '(',
            comma_separated(0.., Self::fn_param).map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
            ')',
        ))
        .context(StrContext::Label("function parameters"))
        .parse_next(input)?;

        let return_type = opt(preceded(
            // Unambiguous
            symbol_pair(['-', '>']),
            cut_err((Self::attributes, Self::type_specifier))
                .context(StrContext::Label("return type"))
                .map(|(a, b)| a.join(b)),
        ))
        .parse_next(input)?;
        let body = cut_err(Self::compound_statement)
            .context(StrContext::Label("function body"))
            .parse_next(input)?;

        Ok(name
            .join(Ast::single(AstNode::OpenBlock))
            .join(params)
            .join(return_type)
            .join(body)
            .join(Ast::single(AstNode::CloseBlock)))
    }

    fn fn_param(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            Self::attributes,
            Self::declare_ident,
            cut_err(preceded(must_symbol(':'), Self::type_specifier))
                .context(StrContext::Label("function parameter type")),
        )
        .map(|(a, b, c)| a.join(b).join(c))
        .parse_next(input)
    }

    fn global_var(input: &mut Input<'_>) -> PResult<Ast> {
        terminated(Self::var_statement, must_symbol(';')).parse_next(input)
    }
    fn var_statement(input: &mut Input<'_>) -> PResult<Ast> {
        // Things like var<private> d: f32
        preceded(
            keyword("var"),
            (
                opt(Self::template_args),
                cut_err(Self::declare_typed_ident)
                    .context(StrContext::Label("variable name and type")),
                opt(preceded(
                    symbol('='),
                    cut_err(Self::expression).context(StrContext::Label("variable value")),
                )),
            )
                .map(|(a, b, c)| a.unwrap_or_default().join(b).join(c)),
        )
        .parse_next(input)
    }
    fn global_override(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            _: keyword("override"),
            cut_err(Self::declare_typed_ident)
                .context(StrContext::Label("pipeline overridable constant name and type")),
            opt(preceded(
                symbol('='),
                cut_err(Self::expression)
                    .context(StrContext::Label("pipeline overridable constant value")),
            )),
            _: must_symbol(';')
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }

    pub fn statements(input: &mut Input<'_>) -> PResult<Ast> {
        repeat(0.., Self::statement.context(StrContext::Label("statement")))
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }

    pub fn compound_statement(input: &mut Input<'_>) -> PResult<Ast> {
        (Self::attributes, parens('{', Self::statements, '}'))
            .context(StrContext::Label("compound statement"))
            .map(|(a, b)| {
                Ast::single(AstNode::OpenBlock)
                    .join(a)
                    .join(b)
                    .join(Ast::single(AstNode::CloseBlock))
            })
            .parse_next(input)
    }

    pub fn statement(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some(non_attributed_statement) = opt(terminated(
            alt((
                // Ambiguity between break and break if
                (keyword("break"), peek(not(keyword("if")))).map(|_| Ast::default()),
                (keyword("continue")).map(|_| Ast::default()),
                (keyword("const_assert"), Self::expression).map(|(_, a)| a),
                (keyword("discard")).map(|_| Ast::default()),
                (keyword("return"), opt(Self::expression)).map(|(_, a)| a.unwrap_or_default()),
                (
                    Self::use_qualified_ident,
                    opt(Self::template_args),
                    // Ambiguity between this and variable_updating_statement needs to be resolved
                    // before cut_err happens
                    peek(paren('(')),
                    cut_err(Self::argument_expression_list)
                        .context(StrContext::Label("function call")),
                )
                    .map(|(a, b, _, c)| a.join(b).join(c)),
                Self::variable_or_value_statement,
                Self::variable_updating_statement,
            )),
            must_symbol(';'),
        ))
        .parse_next(input)?
        {
            return Ok(non_attributed_statement);
        }
        // Semicolon only statement
        if (opt(symbol(';').void()).parse_next(input)?).is_some() {
            return Ok(Ast::default());
        }

        let attributes = Self::attributes.parse_next(input)?;
        let statement = alt((
            preceded(
                keyword("for"),
                (
                    cut_err(parens(
                        '(',
                        seq!(
                            opt(Self::for_init),
                            _: must_symbol(';'),
                            opt(Self::expression),
                            _: must_symbol(';'),
                            opt(Self::for_update),
                        ),
                        ')',
                    ))
                    .context(StrContext::Label("for loop definition"))
                    .map(|(a, b, c)| a.unwrap_or_default().join(b).join(c)),
                    cut_err(Self::compound_statement).context(StrContext::Label("for loop body")),
                ),
            )
            .map(|(a, b)| {
                Ast::single(AstNode::OpenBlock)
                    .join(a)
                    .join(b)
                    .join(Ast::single(AstNode::CloseBlock))
            }),
            (
                keyword("if"),
                cut_err(Self::expression).context(StrContext::Label("if condition")),
                cut_err(Self::compound_statement).context(StrContext::Label("if body")),
                repeat(
                    0..,
                    preceded(
                        (keyword("else"), keyword("if")),
                        (
                            cut_err(Self::expression)
                                .context(StrContext::Label("else if condition")),
                            cut_err(Self::compound_statement)
                                .context(StrContext::Label("else if body")),
                        ),
                    )
                    .map(|(a, b)| a.join(b)),
                )
                .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
                opt(preceded(
                    keyword("else"),
                    cut_err(Self::compound_statement).context(StrContext::Label("else body")),
                )),
            )
                .map(|(_, a, b, c, d)| a.join(b).join(c).join(d)),
            (
                keyword("loop"),
                Self::attributes,
                cut_err(parens(
                    '{',
                    (Self::statements, opt(Self::loop_continuing_block)),
                    '}',
                ))
                .context(StrContext::Label("loop body")),
            )
                .map(|(_, a, (b, c))| a.join(b).join(c)),
            (
                keyword("switch"),
                cut_err(Self::expression).context(StrContext::Label("switch expression")),
                Self::attributes,
                cut_err(parens(
                    '{',
                    repeat(0.., Self::switch_clause)
                        .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
                    '}',
                ))
                .context(StrContext::Label("switch body")),
            )
                .map(|(_, a, b, c)| a.join(b).join(c)),
            (
                keyword("while"),
                cut_err(Self::expression).context(StrContext::Label("while condition")),
                cut_err(Self::compound_statement).context(StrContext::Label("while body")),
            )
                .map(|(_, a, b)| a.join(b)),
            Self::compound_statement,
        ))
        .parse_next(input)?;

        Ok(attributes.join(statement))
    }

    fn loop_continuing_block(input: &mut Input<'_>) -> PResult<Ast> {
        preceded(
            keyword("continuing"),
            (
                Self::attributes,
                cut_err(parens(
                    '{',
                    (
                        Self::statements,
                        opt(delimited(
                            (keyword("break"), keyword("if")),
                            cut_err(Self::expression)
                                .context(StrContext::Label("break if condition")),
                            must_symbol(';'),
                        )),
                    )
                        .map(|(a, b)| a.join(b)),
                    '}',
                ))
                .context(StrContext::Label("loop continuing block")),
            )
                .map(|(a, b)| {
                    Ast::single(AstNode::OpenBlock)
                        .join(a)
                        .join(b)
                        .join(Ast::single(AstNode::CloseBlock))
                }),
        )
        .parse_next(input)
    }

    pub fn variable_or_value_statement(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            Self::var_statement,
            (
                keyword("const"),
                cut_err(Self::declare_typed_ident).context(StrContext::Label("constant name")),
                must_symbol('='),
                cut_err(Self::expression).context(StrContext::Label("constant value")),
            )
                .map(|(_, a, _, b)| a.join(b)),
            (
                keyword("let"),
                cut_err(Self::declare_typed_ident).context(StrContext::Label("variable name")),
                must_symbol('='),
                cut_err(Self::expression).context(StrContext::Label("variable value")),
            )
                .map(|(_, a, _, b)| a.join(b)),
        ))
        .parse_next(input)
    }
    pub fn variable_updating_statement(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (
                Self::lhs_expression,
                alt((
                    preceded(symbol('='), cut_err(Self::expression)),
                    // Unambiguous, lhs_expression cannot have a template at the end
                    preceded(
                        (symbol('<'), symbol('<'), symbol('=')),
                        cut_err(Self::expression),
                    ),
                    preceded(
                        (symbol('>'), symbol('>'), symbol('=')),
                        cut_err(Self::expression),
                    ),
                    preceded((symbol('%'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('&'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('*'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('+'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('-'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('/'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('^'), symbol('=')), cut_err(Self::expression)),
                    preceded((symbol('|'), symbol('=')), cut_err(Self::expression)),
                    (symbol('+'), symbol('+')).default_value(),
                    (symbol('-'), symbol('-')).default_value(),
                ))
                .context(StrContext::Label("variable updating expression")),
            )
                .map(|(a, b)| a.join(b)),
            preceded(
                (symbol('_'), symbol('=')),
                cut_err(Self::expression).context(StrContext::Label("discard expression")),
            ),
        ))
        .parse_next(input)
    }

    pub fn lhs_expression(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (Self::use_ident, opt(Self::component_or_swizzle_specifier)).map(|(a, b)| a.join(b)),
            (
                parens(
                    '(',
                    cut_err(Self::lhs_expression)
                        .context(StrContext::Label("nested lhs expression")),
                    ')',
                ),
                opt(Self::component_or_swizzle_specifier),
            )
                .map(|(a, b)| a.join(b)),
            preceded(
                symbol('&'),
                cut_err(Self::lhs_expression).context(StrContext::Label("lhs expression")),
            ),
            preceded(
                symbol('*'),
                cut_err(Self::lhs_expression).context(StrContext::Label("lhs expression")),
            ),
        ))
        .parse_next(input)
    }

    pub fn for_init(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (
                Self::use_qualified_ident,
                opt(Self::template_args),
                // Ambiguity between this and variable_updating_statement
                peek(paren('(')),
                cut_err(Self::argument_expression_list),
            )
                .map(|(a, b, _, c)| a.join(b).join(c)),
            Self::variable_or_value_statement,
            Self::variable_updating_statement,
        ))
        .parse_next(input)
    }

    pub fn for_update(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (
                Self::use_qualified_ident,
                opt(Self::template_args),
                // Ambiguity between this and the Self::variable_updating_statement branch
                peek(paren('(')),
                cut_err(Self::argument_expression_list),
            )
                .map(|(a, b, _, c)| a.join(b).join(c)),
            Self::variable_updating_statement,
        ))
        .parse_next(input)
    }

    pub fn switch_clause(input: &mut Input<'_>) -> PResult<Ast> {
        let case_start = alt((
            preceded(
                keyword("case"),
                cut_err(comma_separated(
                    1..,
                    alt((keyword("default").default_value::<Ast>(), Self::expression)),
                ))
                .context(StrContext::Label("switch case expression"))
                .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
            ),
            keyword("default").default_value::<Ast>(),
        ))
        .parse_next(input)?;
        let case_body = preceded(
            opt(symbol(':')),
            cut_err(Self::compound_statement).context(StrContext::Label("switch case body")),
        )
        .parse_next(input)?;
        Ok(case_start.join(case_body))
    }

    /// A optionally_typed_ident that leads to a variable declaration.
    pub fn declare_typed_ident(input: &mut Input<'_>) -> PResult<Ast> {
        (
            Self::declare_ident,
            opt(preceded(symbol(':'), Self::type_specifier)),
        )
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    pub fn type_specifier(input: &mut Input<'_>) -> PResult<Ast> {
        // Unambiguous, except for the fact that template_args can contain expressions
        (Self::use_qualified_ident, opt(Self::template_args))
            .context(StrContext::Label("type specifier"))
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    pub fn attribute(input: &mut Input<'_>) -> PResult<Ast> {
        let _start = symbol('@').parse_next(input)?;
        let name = cut_err(any.verify_map(|v: SpannedToken<'_>| match v.token {
            Token::Word(a) | Token::Keyword(a) => Some(a),
            _ => None,
        }))
        .context(StrContext::Label("attribute name"))
        .parse_next(input)?;

        match name {
            // These attributes have no arguments
            "compute" | "const" | "fragment" | "invariant" | "must_use" | "vertex" => {
                Ok(Ast::default())
            } // These attributes have arguments, but the argument doesn't have any identifiers
            "interpolate" | "builtin" | "diagnostic" => cut_err(Self::argument_expression_list)
                .default_value()
                .context(StrContext::Label("attribute expression"))
                .parse_next(input),
            // These are normal attributes
            "workgroup_size" | "align" | "binding" | "blend_src" | "group" | "id" | "location"
            | "size" => cut_err(Self::argument_expression_list)
                .context(StrContext::Label("attribute expression"))
                .parse_next(input),
            // Everything else is also a normal attribute, it might have an expression list
            _ => opt(Self::argument_expression_list)
                .map(|v| v.unwrap_or_default())
                .context(StrContext::Label("attribute expression"))
                .parse_next(input),
        }
    }

    pub fn argument_expression_list(input: &mut Input<'_>) -> PResult<Ast> {
        parens(
            '(',
            comma_separated(0.., Self::expression).map(|v: Vec<_>| v.into_iter().collect()),
            ')',
        )
        .context(StrContext::Label("argument expression list"))
        .parse_next(input)
    }

    pub fn template_expression(input: &mut Input<'_>) -> PResult<Ast> {
        let start_checkpoint = input.checkpoint();
        let mut ast = Self::unary_expression.parse_next(input)?;

        loop {
            if (opt(peek(symbol(','))).parse_next(input)?).is_some() {
                // This is the end of a template
                return Ok(ast);
            }

            let checkpoint = input.checkpoint();
            let operator = Self::maybe_template_expression_operator.parse_next(input);
            match operator {
                Err(_) | Ok(Op::AndOr) => {
                    // - No token matched, template end is not found
                    // - Syntax error, cannot have && or || inside a template
                    input.reset(&start_checkpoint);
                    return cut_err(fail)
                        .context(StrContext::Label("template expression ending"))
                        .parse_next(input);
                }
                Ok(Op::GreaterThan) => {
                    // This is the end of a template
                    input.reset(&checkpoint);
                    return Ok(ast);
                }
                Ok(Op::Other) => {
                    // Valid operator, continue parsing
                }
            };

            let next = cut_err(Self::unary_expression)
                .context(StrContext::Label("expression after operator (in template)"))
                .parse_next(input)?;
            ast = ast.join(next);
        }
    }

    fn maybe_template_expression(input: &mut Input<'_>) -> PResult<(Ast, IsTemplateResult)> {
        let mut ast = Self::unary_expression.parse_next(input)?;

        loop {
            if (opt(peek(symbol(','))).parse_next(input)?).is_some() {
                // This is the end of a template
                return Ok((ast, IsTemplateResult::Yes));
            }
            let checkpoint = input.checkpoint();
            let operator = Self::maybe_template_expression_operator.parse_next(input);
            match operator {
                Err(_) => {
                    // No token matched, template end is not found
                    input.reset(&checkpoint);
                    return Ok((ast, IsTemplateResult::No));
                }
                Ok(Op::AndOr) => {
                    // Cannot be a template if we have an && or || operator
                    input.reset(&checkpoint);
                    return Ok((ast, IsTemplateResult::No));
                }
                Ok(Op::GreaterThan) => {
                    // This is the end of a template
                    input.reset(&checkpoint);
                    return Ok((ast, IsTemplateResult::Yes));
                }
                Ok(Op::Other) => {
                    // Valid operator, continue parsing
                }
            };

            let next = cut_err(Self::unary_expression)
                .context(StrContext::Label("expression after operator (in template)"))
                .parse_next(input)?;
            ast = ast.join(next);
        }
    }

    /// Parses an expression while ignoring the order of operations.
    pub fn expression(input: &mut Input<'_>) -> PResult<Ast> {
        let start = Self::unary_expression.parse_next(input)?;

        let next = repeat(
            0..,
            preceded(
                Self::expression_operator,
                cut_err(Self::unary_expression)
                    .context(StrContext::Label("expression after operator")),
            ),
        )
        .map(|v: Vec<_>| -> Ast { v.into_iter().collect() })
        .parse_next(input)?;

        Ok(start.join(next))
    }

    fn expression_operator(input: &mut Input<'_>) -> PResult<Op> {
        // bitwise_expression.post.unary_expression
        // & ^ |
        // expression
        // && ||
        // relational_expression.post.unary_expression
        // > >= < <= != ==
        // shift_expression.post.unary_expression
        // % * / + - << >>
        alt((
            // This one cannot appear inside a template arg
            symbol_pair(['&', '&']).map(|_| Op::AndOr),
            symbol('&').default_value(),
            // This one cannot appear inside a template arg
            symbol_pair(['|', '|']).map(|_| Op::AndOr),
            symbol('|').default_value(),
            symbol('^').default_value(),
            symbol_pair(['>', '>']).default_value(),
            symbol_pair(['>', '=']).default_value(),
            // This one ends a template, if there is one
            symbol('>').map(|_| Op::GreaterThan),
            symbol_pair(['<', '<']).default_value(),
            symbol_pair(['<', '=']).default_value(),
            // This one is a comparison operator, because unary_expression/primary_expression has already checked for the template symbol
            symbol('<').default_value(),
            symbol_pair(['!', '=']).default_value(),
            symbol_pair(['=', '=']).default_value(),
            symbol('%').default_value(),
            symbol('*').default_value(),
            symbol('/').default_value(),
            symbol('+').default_value(),
            symbol('-').default_value(),
        ))
        .parse_next(input)
    }

    fn maybe_template_expression_operator(input: &mut Input<'_>) -> PResult<Op> {
        alt((
            // If we have a template candidate, we need to check for the end of the template
            symbol('>').map(|_| Op::GreaterThan),
            Self::expression_operator,
        ))
        .parse_next(input)
    }

    pub fn unary_expression(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            preceded(
                one_of([
                    Token::Symbol('!'),
                    Token::Symbol('&'),
                    Token::Symbol('*'),
                    Token::Symbol('-'),
                    Token::Symbol('~'),
                ]),
                cut_err(Self::unary_expression)
                    .context(StrContext::Label("expression after unary operator")),
            ),
            (
                Self::primary_expression.context(StrContext::Label("primary expression")),
                opt(Self::component_or_swizzle_specifier),
            )
                .map(|(a, b)| a.join(b)),
        ))
        .context(StrContext::Label("unary expression"))
        .parse_next(input)
    }

    pub fn primary_expression(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some(ident) = opt(Self::use_qualified_ident).parse_next(input)? {
            // This one is ambiguous, because it could either
            // - be a template or
            // - be skipped and be a less than operator
            let template_args =
                opt(Self::maybe_template_args.context(StrContext::Label("template or less than")))
                    .parse_next(input)?;
            // Only parse the arguments if could be a template
            let arguments = match template_args {
                None | Some((_, IsTemplateResult::Yes)) => {
                    opt(Self::argument_expression_list).parse_next(input)?
                }
                _ => None,
            };

            Ok(ident.join(template_args.map(|v| v.0)).join(arguments))
        } else {
            alt((
                Self::literal.default_value::<Ast>(),
                parens(
                    '(',
                    cut_err(Self::expression).context(StrContext::Label("nested expression")),
                    ')',
                ),
            ))
            .parse_next(input)
        }
    }

    pub fn template_args(input: &mut Input<'_>) -> PResult<Ast> {
        delimited(
            symbol('<'),
            cut_err(comma_separated(1.., Self::template_expression)),
            must_symbol('>'),
        )
        .map(|v: Vec<_>| {
            Ast::from_iter(
                std::iter::once(Ast::single(AstNode::TemplateStart))
                    .chain(v)
                    .chain(std::iter::once(Ast::single(AstNode::TemplateEnd))),
            )
        })
        .context(StrContext::Label("template arguments"))
        .parse_next(input)
    }

    fn maybe_template_args(input: &mut Input<'_>) -> PResult<(Ast, IsTemplateResult)> {
        let _ = symbol('<').parse_next(input)?;
        let (mut ast, is_template) = Self::maybe_template_expression
            .context(StrContext::Label(
                "expression in template or after less than",
            ))
            .parse_next(input)?;
        if is_template == IsTemplateResult::No {
            return Ok((ast, IsTemplateResult::No));
        }
        loop {
            if let Some(_end) = opt(symbol('>')).parse_next(input)? {
                break;
            }
            // If the template isn't finished, we need at least one more comma
            // This can be the trailing comma
            let _separator = must_symbol(',').parse_next(input)?;
            let checkpoint = input.checkpoint();
            let next = match Self::template_expression.parse_next(input) {
                Ok(v) => v,
                Err(ErrMode::Backtrack(_)) => {
                    input.reset(&checkpoint);
                    break;
                }
                Err(e) => return Err(e),
            };

            ast = ast.join(next);
        }
        Ok((
            Ast::single(AstNode::TemplateStart)
                .join(ast)
                .join(Ast::single(AstNode::TemplateEnd)),
            IsTemplateResult::Yes,
        ))
    }

    pub fn literal(input: &mut Input<'_>) -> PResult<()> {
        alt((
            keyword("false").void(),
            keyword("true").void(),
            number().void(),
        ))
        .parse_next(input)
    }

    pub fn component_or_swizzle_specifier(input: &mut Input<'_>) -> PResult<Ast> {
        (
            alt((
                (symbol('.'), cut_err(Self::ident))
                    .context(StrContext::Label("property access or swizzle"))
                    .map(|(dot, property)| {
                        Ast::single(AstNode::PropertyUse {
                            dot: dot.span.start,
                            property,
                        })
                    }),
                parens(
                    '[',
                    cut_err(Self::expression).context(StrContext::Label("nested expression")),
                    ']',
                ),
            )),
            opt(Self::component_or_swizzle_specifier),
        )
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    pub fn use_qualified_ident(input: &mut Input<'_>) -> PResult<Ast> {
        (
            Self::use_ident,
            opt((symbol('.'), Self::ident).map(|(dot, property)| {
                Ast::single(AstNode::PropertyUse {
                    dot: dot.span.start,
                    property,
                })
            })),
        )
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    pub fn use_ident(input: &mut Input<'_>) -> PResult<Ast> {
        Self::ident
            .map(|v| Ast::single(AstNode::Use(v)))
            .parse_next(input)
    }

    pub fn declare_ident(input: &mut Input<'_>) -> PResult<Ast> {
        Self::ident
            .map(|v| Ast::single(AstNode::Declare(v)))
            .parse_next(input)
    }

    pub fn ident(input: &mut Input<'_>) -> PResult<VariableSpan> {
        any.verify_map(|v: SpannedToken<'_>| match v.token {
            Token::Word(_) => Some(v.span),
            _ => None,
        })
        .parse_next(input)
    }
}

fn word(
    a: &str,
) -> impl Parser<Input<'_>, <Input<'_> as winnow::stream::Stream>::Token, ContextError> {
    token_kind(Token::Word(a))
}

fn keyword(
    a: &str,
) -> impl Parser<Input<'_>, <Input<'_> as winnow::stream::Stream>::Token, ContextError> {
    token_kind(Token::Keyword(a))
}

fn symbol<'a>(
    a: char,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    token_kind(Token::Symbol(a))
}

fn must_symbol<'a>(
    a: char,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    cut_err(symbol(a)).context(StrContext::Expected(StrContextValue::CharLiteral(a)))
}

fn symbol_pair<'a>(
    a: [char; 2],
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Slice, ContextError> {
    (symbol(a[0]), symbol(a[1]))
        .take()
        .context(StrContext::Label("symbols"))
}

fn paren<'a>(
    a: char,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    token_kind(Token::Paren(a))
}

fn parens<'a, Output>(
    a: char,
    parser: impl Parser<Input<'a>, Output, ContextError>,
    b: char,
) -> impl Parser<Input<'a>, Output, ContextError> {
    delimited(
        paren(a),
        parser,
        cut_err(paren(b)).context(StrContext::Expected(StrContextValue::CharLiteral(b))),
    )
    .context(StrContext::Label("parentheses"))
}

fn comma_separated<'a, Accumulator, Output>(
    occurrences: impl Into<winnow::stream::Range>,
    parser: impl Parser<Input<'a>, Output, ContextError>,
) -> impl Parser<Input<'a>, Accumulator, ContextError>
where
    Accumulator: winnow::stream::Accumulate<Output>,
{
    terminated(
        separated(occurrences, parser, symbol(',')),
        opt(symbol(',')),
    )
    .context(StrContext::Label("comma separated"))
}

fn number<'a>() -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError>
{
    token_kind(Token::Number)
}

fn token_kind<'a>(
    token_kind: Token<'a>,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    move |input: &mut Input<'a>| {
        let checkpoint = input.checkpoint();
        match input.next_token() {
            Some(v) if v.token == token_kind => Ok(v),
            Some(_) => {
                input.reset(&checkpoint);
                Err(ErrMode::from_error_kind(input, ErrorKind::Verify))
            }
            None => Err(ErrMode::from_error_kind(input, ErrorKind::Token)),
        }
    }
}
