use winnow::{
    combinator::{
        alt, cut_err, delimited, dispatch, empty, fail, opt, peek, preceded, repeat, separated,
        seq, terminated,
    },
    error::{ContextError, ErrMode, StrContext},
    stream::{Recoverable, Stream},
    token::{any, one_of, take_till},
    PResult, Parser,
};

use crate::{
    parser_output::{Ast, AstNode, Variable},
    token::{SpannedToken, Token},
    WgslParseError,
};

// winnow::error::TreeError<&'a [SpannedToken<'a>]>
pub type Input<'a> = Recoverable<&'a [SpannedToken<'a>], ContextError>;

/// A basic parser for the purposes of linking multiple WGSL modules together. It needs to parse
/// - Identifiers in declarations
/// - Import statements
/// - Export statements
///
/// It does not need to precisely parse
/// - Comments
/// - Template lists https://www.w3.org/TR/WGSL/#template-lists-sec
/// - Operators
/// ...
/// Instead, there it is good enough to parse a simplified superset of WGSL. As long as identifiers
/// are resolved correctly, the parsing is a success.
pub struct WgslParser;

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum IsTemplateStart {
    Yes,
    Maybe,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum IsTemplateResult {
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

impl WgslParser {
    pub fn parse<'a>(input: &'a [SpannedToken<'a>]) -> Result<Ast, WgslParseError> {
        let input = Recoverable::new(input);
        Self::translation_unit
            .parse(input)
            .map_err(|e| WgslParseError {
                message: format!("{:?} {:?}", e, e.inner().cause()),
                position: e.offset(),
                context: e.into_inner(),
            })
    }

    pub fn translation_unit(input: &mut Input<'_>) -> PResult<Ast> {
        // TODO: Add import statement here
        let _directives = Self::global_directives.parse_next(input)?;
        let declarations = Self::global_decls.parse_next(input)?;

        Ok(declarations.into_iter().collect())
    }

    /// We don't verify the global_directives rules.
    /// Instead we just trust the shader author to have specified all the important ones in the main file.
    pub fn global_directives(input: &mut Input<'_>) -> PResult<()> {
        repeat(0.., Self::global_directive).parse_next(input)
    }

    pub fn global_directive(input: &mut Input<'_>) -> PResult<()> {
        let _start =
            alt((word("diagnostic"), word("enable"), word("requires"))).parse_next(input)?;
        let _rule = cut_err(take_till(1.., Token::Symbol(';'))).parse_next(input)?;
        let _end = symbol(';').parse_next(input)?;
        Ok(())
    }

    pub fn global_decls(input: &mut Input<'_>) -> PResult<Vec<Ast>> {
        repeat(0.., Self::global_decl).parse_next(input)
    }

    pub fn global_decl(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some(non_attributed_global) = opt(dispatch! {any.map(|v: SpannedToken| v.token);
                Token::Symbol(';') => empty.default_value::<Ast>(),
                Token::Word("alias") => Self::continue_global_alias,
                Token::Word("const_assert") => terminated(Self::expression, symbol(';')),
                Token::Word("struct") => Self::continue_global_struct,
                Token::Word("const") => Self::continue_global_const,
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
            Self::ident,
            _: symbol('='),
            Self::type_specifier,
            _: symbol(';'),
        )
        .map(|(a, c)| Ast::single(AstNode::Use(a)).join(c))
        .parse_next(input)
    }

    fn continue_global_struct(input: &mut Input<'_>) -> PResult<Ast> {
        (
            Self::ident,
            parens(
                '{',
                comma_separated(
                    1..,
                    (
                        Self::attributes,
                        (Self::ident_pattern_token, symbol(':')),
                        Self::type_specifier,
                    )
                        .map(|(a, _, b)| a.join(b)),
                )
                .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
                '}',
            ),
        )
            .map(|(a, b)| Ast::single(AstNode::Declare(a)).join(b))
            .parse_next(input)
    }

    fn continue_global_const(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            Self::declare_typed_ident,
            _: symbol('='),
            Self::expression,
            _: symbol(';'),
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }

    fn global_fn(input: &mut Input<'_>) -> PResult<Ast> {
        let _ = word("fn").parse_next(input)?;
        let name = Self::ident.parse_next(input)?;

        let params = parens(
            '(',
            comma_separated(0.., Self::fn_param).map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
            ')',
        )
        .parse_next(input)?;

        let return_type = opt(preceded(
            // Unambiguous
            symbol_pair(['-', '>']),
            (Self::attributes, Self::type_specifier).map(|(a, b)| a.join(b)),
        ))
        .parse_next(input)?;
        let body = Self::compound_statement.parse_next(input)?;

        Ok(Ast::single(AstNode::Declare(name))
            .join(Ast::single(AstNode::OpenBlock))
            .join(params)
            .join(return_type)
            .join(body)
            .join(Ast::single(AstNode::CloseBlock)))
    }

    fn fn_param(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            Self::attributes,
            Self::ident,
            preceded(symbol(':'), Self::type_specifier),
        )
        .map(|(a, b, c)| a.join(Ast::single(AstNode::Declare(b))).join(c))
        .parse_next(input)
    }

    fn global_var(input: &mut Input<'_>) -> PResult<Ast> {
        terminated(Self::var_statement, symbol(';')).parse_next(input)
    }
    fn var_statement(input: &mut Input<'_>) -> PResult<Ast> {
        // Things like var<private> d: f32
        preceded(
            (word("var"), opt(Self::template_args)),
            (
                Self::declare_typed_ident,
                opt(preceded(symbol('='), Self::expression)),
            )
                .map(|(a, b)| a.join(b)),
        )
        .parse_next(input)
    }
    fn global_override(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            _: word("override"),
            Self::declare_typed_ident,
            opt(preceded(
                symbol('='),
                Self::expression
            )),
            _: symbol(';')
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }

    pub fn statements(input: &mut Input<'_>) -> PResult<Ast> {
        repeat(0.., Self::statement)
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }

    pub fn compound_statement(input: &mut Input<'_>) -> PResult<Ast> {
        (Self::attributes, parens('{', Self::statements, '}'))
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    pub fn statement(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some(non_attributed_statement) = opt(terminated(
            alt((
                (
                    Self::ident,
                    // At this point, the ambiguity between this and variable_updating_statement is resolved
                    opt(Self::template_args),
                    Self::argument_expression_list,
                )
                    .map(|(a, b, c)| Ast::single(AstNode::Use(a)).join(b).join(c)),
                Self::variable_or_value_statement,
                Self::variable_updating_statement,
                (word("break")).map(|_| Ast::default()),
                (word("continue")).map(|_| Ast::default()),
                (word("const_assert"), Self::expression).map(|(_, a)| a),
                (word("discard")).map(|_| Ast::default()),
                (word("return"), opt(Self::expression)).map(|(_, a)| a.unwrap_or_default()),
            )),
            symbol(';'),
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
            seq!(
                _: word("for"),
                _: paren('('),
                opt(Self::for_init),
                _: symbol(';'),
                opt(Self::expression),
                _: symbol(';'),
                opt(Self::for_update),
                _: paren(')'),
                Self::compound_statement,
            )
            .map(|(a, b, c, d)| a.unwrap_or_default().join(b).join(c).join(d)),
            (
                word("if"),
                Self::expression,
                Self::compound_statement,
                repeat(
                    0..,
                    preceded(
                        (word("else"), word("if")),
                        (Self::expression, Self::compound_statement),
                    )
                    .map(|(a, b)| a.join(b)),
                )
                .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
                opt(preceded(word("else"), Self::compound_statement)),
            )
                .map(|(_, a, b, c, d)| a.join(b).join(c).join(d)),
            (
                word("loop"),
                Self::attributes,
                paren('{'),
                Self::statements,
                opt((
                    word("continuing"),
                    Self::attributes,
                    paren('{'),
                    Self::statements,
                    opt(delimited(
                        (word("break"), word("if")),
                        Self::expression,
                        symbol(';'),
                    )),
                    paren('}'),
                )
                    .map(|(_, a, _, b, c, _)| a.join(b).join(c))),
                paren('}'),
            )
                .map(|(_, a, _, b, c, _)| a.join(b).join(c)),
            (
                word("switch"),
                Self::expression,
                Self::attributes,
                parens(
                    '{',
                    repeat(0.., Self::switch_clause)
                        .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
                    '}',
                ),
            )
                .map(|(_, a, b, c)| a.join(b).join(c)),
            (word("while"), Self::expression, Self::compound_statement).map(|(_, a, b)| a.join(b)),
            Self::compound_statement,
        ))
        .parse_next(input)?;

        Ok(attributes.join(statement))
    }

    pub fn variable_or_value_statement(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            Self::var_statement,
            (
                word("const"),
                Self::declare_typed_ident,
                symbol('='),
                Self::expression,
            )
                .map(|(_, a, _, b)| a.join(b)),
            (
                word("let"),
                Self::declare_typed_ident,
                symbol('='),
                Self::expression,
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
                    preceded(symbol('='), Self::expression),
                    // Unambiguous, lhs_expression cannot have a template at the end
                    preceded((symbol('<'), symbol('<'), symbol('=')), Self::expression),
                    preceded((symbol('>'), symbol('>'), symbol('=')), Self::expression),
                    preceded((symbol('%'), symbol('=')), Self::expression),
                    preceded((symbol('&'), symbol('=')), Self::expression),
                    preceded((symbol('*'), symbol('=')), Self::expression),
                    preceded((symbol('+'), symbol('=')), Self::expression),
                    preceded((symbol('-'), symbol('=')), Self::expression),
                    preceded((symbol('/'), symbol('=')), Self::expression),
                    preceded((symbol('^'), symbol('=')), Self::expression),
                    preceded((symbol('|'), symbol('=')), Self::expression),
                    (symbol('+'), symbol('+')).default_value(),
                    (symbol('-'), symbol('-')).default_value(),
                )),
            )
                .map(|(a, b)| a.join(b)),
            preceded((symbol('_'), symbol('=')), Self::expression),
        ))
        .parse_next(input)
    }

    pub fn lhs_expression(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (Self::ident, opt(Self::component_or_swizzle_specifier))
                .map(|(a, b)| Ast::single(AstNode::Use(a)).join(b)),
            (
                parens('(', Self::lhs_expression, ')'),
                opt(Self::component_or_swizzle_specifier),
            )
                .map(|(a, b)| a.join(b)),
            preceded(symbol('&'), Self::lhs_expression),
            preceded(symbol('*'), Self::lhs_expression),
        ))
        .parse_next(input)
    }

    pub fn for_init(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            // TODO: Ambiguity between this and the Self::global_var branch of variable_or_value_statement
            (
                Self::ident,
                opt(Self::template_args),
                Self::argument_expression_list,
            )
                .map(|(a, b, c)| Ast::single(AstNode::Use(a)).join(b).join(c)),
            Self::variable_or_value_statement,
            Self::variable_updating_statement,
        ))
        .parse_next(input)
    }

    pub fn for_update(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (
                Self::ident,
                opt(Self::template_args),
                Self::argument_expression_list,
            )
                .map(|(a, b, c)| Ast::single(AstNode::Use(a)).join(b).join(c)),
            Self::variable_updating_statement,
        ))
        .parse_next(input)
    }

    pub fn switch_clause(input: &mut Input<'_>) -> PResult<Ast> {
        let case_start = alt((
            preceded(
                word("case"),
                comma_separated(
                    1..,
                    alt((word("default").default_value::<Ast>(), Self::expression)),
                )
                .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
            ),
            word("default").default_value::<Ast>(),
        ))
        .parse_next(input)?;
        let case_body = preceded(opt(symbol(':')), Self::compound_statement).parse_next(input)?;
        Ok(case_start.join(case_body))
    }

    /// A optionally_typed_ident that leads to a variable declaration.
    pub fn declare_typed_ident(input: &mut Input<'_>) -> PResult<Ast> {
        (
            Self::ident,
            opt(preceded(symbol(':'), Self::type_specifier)),
        )
            .map(|(a, b)| Ast::single(AstNode::Declare(a)).join(b))
            .parse_next(input)
    }

    pub fn type_specifier(input: &mut Input<'_>) -> PResult<Ast> {
        // Unambiguous, except for the fact that template_args can contain expressions
        (Self::ident, opt(Self::template_args))
            .map(|(a, b)| Ast::single(AstNode::Use(a)).join(b))
            .parse_next(input)
    }

    pub fn attribute(input: &mut Input<'_>) -> PResult<Ast> {
        let _start = symbol('@').parse_next(input)?;
        let name = Self::ident_pattern_token.parse_next(input)?;
        let expressions = Self::argument_expression_list.parse_next(input)?;

        match name {
            "compute" | "const" | "fragment" | "interpolate" | "invariant" | "must_use"
            | "vertex" | "builtin" | "diagnostic" => Ok(Default::default()),
            "workgroup_size" | "align" | "binding" | "blend_src" | "group" | "id" | "location"
            | "size" => Ok(expressions),
            _ => fail.parse_next(input),
        }
    }

    pub fn argument_expression_list(input: &mut Input<'_>) -> PResult<Ast> {
        parens(
            '(',
            comma_separated(0.., Self::expression).map(|v: Vec<_>| v.into_iter().collect()),
            ')',
        )
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
            let operator = Self::expression_operator.parse_next(input);
            match operator {
                Err(_) | Ok(Op::AndOr) => {
                    // - No token matched, template end is not found
                    // - Syntax error, cannot have && or || inside a template
                    input.reset(&start_checkpoint);
                    return fail.parse_next(input);
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

            let next = Self::unary_expression.parse_next(input)?;
            ast = ast.join(next);
        }
    }

    pub fn maybe_template_expression(input: &mut Input<'_>) -> PResult<(Ast, IsTemplateResult)> {
        let mut ast = Self::unary_expression.parse_next(input)?;

        loop {
            if (opt(peek(symbol(','))).parse_next(input)?).is_some() {
                // This is the end of a template
                return Ok((ast, IsTemplateResult::Yes));
            }
            let checkpoint = input.checkpoint();
            let operator = Self::expression_operator.parse_next(input);
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

            let next = Self::unary_expression.parse_next(input)?;
            ast = ast.join(next);
        }
    }

    /// Parses an expression while ignoring the order of operations.
    pub fn expression(input: &mut Input<'_>) -> PResult<Ast> {
        let start = Self::unary_expression.parse_next(input)?;

        let next = repeat(
            0..,
            preceded(Self::expression_operator, Self::unary_expression),
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
                Self::unary_expression,
            ),
            (
                Self::primary_expression,
                opt(Self::component_or_swizzle_specifier),
            )
                .map(|(a, b)| a.join(b)),
        ))
        .parse_next(input)
    }

    pub fn primary_expression(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some((ident, tokens)) = opt(Self::ident.with_taken()).parse_next(input)? {
            if tokens.len() == 1
                && (tokens[0].token == Token::Word("true")
                    || tokens[0].token == Token::Word("false"))
            {
                Ok(Ast::default())
            } else {
                // This one is ambiguous, because it could either
                // - be a template or
                // - be skipped and be a less than operator
                let template_args = opt(Self::maybe_template_args).parse_next(input)?;
                let arguments = match template_args {
                    Some((_, IsTemplateResult::No)) => None,
                    _ => opt(Self::argument_expression_list).parse_next(input)?,
                };

                Ok(Ast::single(AstNode::Use(ident))
                    .join(template_args.map(|v| v.0))
                    .join(arguments))
            }
        } else {
            alt((
                Self::literal.default_value::<Ast>(),
                parens('(', Self::expression, ')'),
            ))
            .parse_next(input)
        }
    }

    pub fn template_args(input: &mut Input<'_>) -> PResult<Ast> {
        delimited(
            symbol('<'),
            comma_separated(1.., Self::template_expression)
                .map(|v: Vec<_>| v.into_iter().collect()),
            symbol('>'),
        )
        .parse_next(input)
    }

    pub fn maybe_template_args(input: &mut Input<'_>) -> PResult<(Ast, IsTemplateResult)> {
        let _ = symbol('<').parse_next(input)?;
        let (mut ast, is_template) = Self::maybe_template_expression.parse_next(input)?;
        if is_template == IsTemplateResult::No {
            return Ok((ast, IsTemplateResult::No));
        }
        loop {
            let separator = opt(symbol(',')).parse_next(input)?;
            if separator.is_none() {
                break;
            }
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
        Ok((ast, IsTemplateResult::Yes))
    }

    pub fn literal(input: &mut Input<'_>) -> PResult<()> {
        alt((word("false").void(), word("true").void(), number().void())).parse_next(input)
    }

    pub fn component_or_swizzle_specifier(input: &mut Input<'_>) -> PResult<Ast> {
        (
            alt((
                (symbol('.'), Self::ident_pattern_token).default_value::<Ast>(),
                parens('[', Self::expression, ']'),
            )),
            opt(Self::component_or_swizzle_specifier),
        )
            .map(|(a, b)| a.join(b))
            .parse_next(input)
    }

    pub fn ident(input: &mut Input<'_>) -> PResult<Variable> {
        any.verify_map(|v: SpannedToken<'_>| match v.token {
            Token::Word(_) => Some(Variable(v.span)),
            _ => None,
        })
        .parse_next(input)
    }

    pub fn ident_pattern_token<'a>(input: &mut Input<'a>) -> PResult<&'a str> {
        any.verify_map(|v: SpannedToken<'a>| match v.token {
            Token::Word(a) => Some(a),
            _ => None,
        })
        .parse_next(input)
    }
}

fn word(
    a: &str,
) -> impl Parser<Input<'_>, <Input<'_> as winnow::stream::Stream>::Token, ContextError> {
    one_of::<Input, Token<'_>, ContextError>(Token::Word(a)).context(StrContext::Label("word"))
}

fn symbol<'a>(
    a: char,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    one_of::<Input, Token<'a>, ContextError>(Token::Symbol(a)).context(StrContext::Label("symbol"))
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
    one_of::<Input, Token<'a>, ContextError>(Token::Paren(a))
        .context(StrContext::Label("parenthesis"))
}

fn parens<'a, Output>(
    a: char,
    parser: impl Parser<Input<'a>, Output, ContextError>,
    b: char,
) -> impl Parser<Input<'a>, Output, ContextError> {
    delimited(paren(a), parser, paren(b))
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
    one_of::<Input, Token<'a>, ContextError>(Token::Number).context(StrContext::Label("number"))
}
