use winnow::{
    combinator::{
        alt, cut_err, delimited, fail, opt, preceded, repeat, separated, seq, terminated,
    },
    error::ContextError,
    stream::Recoverable,
    token::one_of,
    Located, PResult, Parser,
};

use crate::{
    parser_output::{Ast, AstNode, Variable},
    tokenizer::{SpannedToken, Token},
    WgslParseError,
};

pub type Input<'a> = Recoverable<Located<&'a [SpannedToken<'a>]>, ContextError>;

// TODO: Impl Location for Input https://docs.rs/winnow/latest/src/winnow/stream/mod.rs.html#1330

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

impl WgslParser {
    pub fn parse<'a>(input: &'a [SpannedToken<'a>]) -> Result<Ast, WgslParseError> {
        let input = Recoverable::new(Located::new(input));
        Self::translation_unit
            .parse(input)
            .map_err(|e| WgslParseError {
                message: todo!("e.to_string() needs to be implemented"),
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
        let _rule = repeat(1.., symbol(';').void()).parse_next(input)?;
        let _end = symbol(';').parse_next(input)?;
        Ok(())
    }

    pub fn global_decls(input: &mut Input<'_>) -> PResult<Vec<Ast>> {
        repeat(0.., Self::global_decl).parse_next(input)
    }

    pub fn global_decl(input: &mut Input<'_>) -> PResult<Ast> {
        if let Some(non_attributed_global) = opt(alt((
            cut_err(symbol(';')).default_value::<Ast>(),
            Self::global_alias,
            Self::global_const_assert,
            Self::global_struct,
            Self::global_const,
        )))
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
        repeat(0.., cut_err(Self::attribute))
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }

    fn global_alias(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            _: cut_err(word("alias")),
            Self::ident,
            _: symbol('='),
            Self::type_specifier,
            _: symbol(';'),
        )
        .map(|(a, c)| Ast::single(AstNode::Use(a)).join(c))
        .parse_next(input)
    }

    fn global_const_assert(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            _: cut_err(word("const_assert")),
            Self::expression,
            _: symbol(';'),
        )
        .map(|(a,)| a)
        .parse_next(input)
    }

    fn global_struct(input: &mut Input<'_>) -> PResult<Ast> {
        (
            cut_err(word("struct")),
            Self::ident,
            paren('{'),
            repeat(
                1..,
                (
                    Self::attributes,
                    (Self::ident_pattern_token, symbol(':')),
                    Self::type_specifier,
                )
                    .map(|(a, _, b)| a.join(b)),
            )
            .map(|v: Vec<_>| v.into_iter().collect::<Ast>()),
            (opt(symbol(',')), paren('}')),
        )
            .map(|(_, a, _, b, _)| Ast::single(AstNode::Declare(a)).join(b))
            .parse_next(input)
    }

    fn global_fn(input: &mut Input<'_>) -> PResult<Ast> {
        let _ = cut_err(word("fn")).parse_next(input)?;
        let name = Self::ident.parse_next(input)?;
        let _ = paren('(').parse_next(input)?;
        let params = separated(0.., Self::fn_param, symbol(','))
            .map(|v: Vec<_>| v.into_iter().collect::<Ast>())
            .parse_next(input)?;
        let _ = (opt(symbol(',')), paren(')')).parse_next(input)?;
        let return_type = opt((
            (symbol('-'), symbol('>')),
            Self::attributes,
            Self::type_specifier,
        )
            .map(|(_, a, b)| a.join(b)))
        .parse_next(input)?;
        let body_attributes = Self::attributes.parse_next(input)?;
        let _ = paren('{').parse_next(input)?;
        let body = Self::statements.parse_next(input)?;
        let _ = paren('}').parse_next(input)?;

        Ok(Ast::single(AstNode::Declare(name))
            .join(Ast::single(AstNode::OpenBlock))
            .join(params)
            .join(return_type)
            .join(body_attributes)
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
        // Things like var<private> d: f32;
        seq!(
            _: cut_err(word("var")),
            _: Self::maybe_template_args,
            Self::declare_typed_ident,
            opt(preceded(
               symbol ('='),
                Self::expression
            )),
            _: symbol(';'),
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }
    fn global_override(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            _: cut_err(word("override")),
            Self::declare_typed_ident,
            opt(preceded(
                symbol( '='),
                Self::expression
            )),
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }
    fn global_const(input: &mut Input<'_>) -> PResult<Ast> {
        seq!(
            _:cut_err(word("const")),
            Self::declare_typed_ident,
            _: symbol('='),
            Self::expression,
            _: symbol(';'),
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }

    pub fn statements(input: &mut Input<'_>) -> PResult<Ast> {
        repeat(0.., Self::statement)
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }
    pub fn statement(input: &mut Input<'_>) -> PResult<Ast> {
        todo!()
    }

    pub fn declare_typed_ident(input: &mut Input<'_>) -> PResult<Ast> {
        (
            Self::ident,
            opt(preceded(symbol(':'), Self::type_specifier)),
        )
            .map(|(a, b)| Ast::single(AstNode::Declare(a)).join(b))
            .parse_next(input)
    }

    pub fn type_specifier(input: &mut Input<'_>) -> PResult<Ast> {
        (Self::ident, Self::maybe_template_args)
            .map(|(a, b)| Ast::single(AstNode::Use(a)).join(b))
            .parse_next(input)
    }

    pub fn attribute(input: &mut Input<'_>) -> PResult<Ast> {
        let _start = symbol('@').parse_next(input)?;
        let name = Self::ident_pattern_token.parse_next(input)?;
        let _opening = paren('(').parse_next(input)?;
        let expressions = Self::expression_comma_list.parse_next(input)?;
        let _closing = paren(')').parse_next(input)?;

        match name {
            "compute" | "const" | "fragment" | "interpolate" | "invariant" | "must_use"
            | "vertex" | "builtin" | "diagnostic" => Ok(Default::default()),
            "workgroup_size" | "align" | "binding" | "blend_src" | "group" | "id" | "location"
            | "size" => Ok(expressions.into_iter().collect()),
            _ => fail.parse_next(input),
        }
    }

    pub fn argument_expression_list(input: &mut Input<'_>) -> PResult<Ast> {
        delimited(
            cut_err(paren('(')),
            Self::expression_comma_list.map(|v| v.into_iter().collect()),
            paren(')'),
        )
        .parse_next(input)
    }

    pub fn expression_comma_list(input: &mut Input<'_>) -> PResult<Vec<Ast>> {
        terminated(
            separated(1.., Self::expression, symbol(',')),
            opt(symbol(',')),
        )
        .parse_next(input)
    }

    /// Parses an expression while ignoring the order of operations.
    pub fn expression(input: &mut Input<'_>) -> PResult<Ast> {
        let start = Self::unary_expression.parse_next(input)?;

        fn operator(input: &mut Input<'_>) -> PResult<()> {
            // bitwise_expression.post.unary_expression
            // & ^ |
            // expression
            // && ||
            // relational_expression.post.unary_expression
            // > >= < <= != ==
            // shift_expression.post.unary_expression
            // % * / + - << >>
            alt((
                symbol_pair(['&', '&']).void(),
                symbol('&').void(),
                symbol_pair(['|', '|']).void(),
                symbol('|').void(),
                symbol('^').void(),
                //
                symbol_pair(['>', '>']).void(),
                symbol_pair(['>', '=']).void(),
                symbol('>').void(),
                symbol_pair(['<', '<']).void(),
                symbol_pair(['<', '=']).void(),
                symbol('<').void(),
                symbol_pair(['!', '=']).void(),
                symbol_pair(['=', '=']).void(),
                //
                symbol('%').void(),
                symbol('*').void(),
                symbol('/').void(),
                symbol('+').void(),
                symbol('-').void(),
            ))
            .void()
            .parse_next(input)
        }

        let next = repeat(1.., preceded(operator, Self::unary_expression))
            .map(|v: Vec<_>| -> Ast { v.into_iter().collect() })
            .parse_next(input)?;

        Ok(start.join(next))
    }

    pub fn unary_expression(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            preceded(
                cut_err(one_of([
                    Token::Symbol('!'),
                    Token::Symbol('&'),
                    Token::Symbol('*'),
                    Token::Symbol('-'),
                    Token::Symbol('~'),
                ])),
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
        if let Some((ident, tokens)) =
            opt(cut_err(Self::ident).with_recognized()).parse_next(input)?
        {
            if tokens.len() == 1
                && (tokens[0].token == Token::Word("true")
                    || tokens[0].token == Token::Word("false"))
            {
                Ok(Ast::default())
            } else {
                let template_args = Self::maybe_template_args.parse_next(input)?;
                let arguments = opt(Self::argument_expression_list).parse_next(input)?;
                Ok(Ast::single(AstNode::Use(ident))
                    .join(template_args)
                    .join(arguments))
            }
        } else {
            alt((
                Self::literal.default_value::<Ast>(),
                delimited(cut_err(paren('(')), Self::expression, paren(')')),
            ))
            .parse_next(input)
        }
    }

    /// Can either be a normal comparison, or a template. We don't know yet.
    pub fn maybe_template_args(input: &mut Input<'_>) -> PResult<Ast> {
        opt(delimited(
            symbol('<'),
            Self::expression_comma_list,
            opt(symbol('>')),
        ))
        .map(|v| match v {
            Some(v) => v.into_iter().collect(),
            None => Ast::default(),
        })
        .parse_next(input)
    }

    pub fn literal(input: &mut Input<'_>) -> PResult<()> {
        alt((word("false").void(), word("true").void(), number().void())).parse_next(input)
    }

    pub fn component_or_swizzle_specifier(input: &mut Input<'_>) -> PResult<Ast> {
        alt((
            (
                cut_err(symbol('.')),
                Self::ident_pattern_token,
                opt(Self::component_or_swizzle_specifier),
            )
                .default_value::<Ast>(),
            seq!(
                _:cut_err(symbol('[')),
                Self::expression,
                _:symbol(']'),
                opt(Self::component_or_swizzle_specifier),
            )
            .map(|(a, b)| a.join(b)),
        ))
        .parse_next(input)
    }

    pub fn ident(input: &mut Input<'_>) -> PResult<Variable> {
        one_of(|v: SpannedToken<'_>| matches!(v.token, Token::Word(_)))
            .map(|v: SpannedToken<'_>| Variable(v.span))
            .parse_next(input)
    }

    pub fn ident_pattern_token<'a>(input: &mut Input<'a>) -> PResult<&'a str> {
        one_of(|v: SpannedToken<'a>| matches!(v.token, Token::Word(_)))
            .map(|v: SpannedToken<'a>| match v.token {
                Token::Word(a) => a,
                _ => unreachable!(),
            })
            .parse_next(input)
    }
}

fn word(
    a: &str,
) -> impl Parser<Input<'_>, <Input<'_> as winnow::stream::Stream>::Token, ContextError> {
    one_of::<Input, crate::tokenizer::Token<'_>, ContextError>(Token::Word(a))
}

fn symbol<'a>(
    a: char,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    one_of::<Input, crate::tokenizer::Token<'a>, ContextError>(Token::Symbol(a))
}

fn symbol_pair<'a>(
    a: [char; 2],
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Slice, ContextError> {
    (symbol(a[0]), symbol(a[1])).recognize()
}

fn paren<'a>(
    a: char,
) -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError> {
    one_of::<Input, crate::tokenizer::Token<'a>, ContextError>(Token::Symbol(a))
}
fn number<'a>() -> impl Parser<Input<'a>, <Input<'a> as winnow::stream::Stream>::Token, ContextError>
{
    one_of::<Input, crate::tokenizer::Token<'a>, ContextError>(Token::Number)
}
