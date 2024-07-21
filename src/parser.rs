use winnow::{
    ascii::{digit0, digit1, hex_digit0, hex_digit1},
    combinator::{
        alt, cut_err, delimited, empty, eof, fail, not, opt, preceded, repeat, separated,
        separated_pair, seq, terminated,
    },
    error::ContextError,
    stream::Recoverable,
    token::{none_of, one_of, take_until, take_while},
    Located, PResult, Parser,
};

use crate::{parser_output::Ast, tokenizer::SpannedToken, WgslParseError};

pub type Input<'a> = Recoverable<Located<&'a [SpannedToken<'a>]>, ContextError>;

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
        Ok(())
    }

    /// We don't verify the global_directives rules.
    /// Instead we just trust the shader author to have specified all the important ones in the main file.
    pub fn global_directives(input: &mut Input<'_>) -> PResult<Ast> {
        repeat(0.., preceded(opt_spaces, Self::global_directive)).parse_next(input)
    }

    pub fn global_directive(input: &mut Input<'_>) -> PResult<Ast> {
        let _start = alt(("diagnostic", "enable", "requires")).parse_next(input)?;
        let _rule = repeat(1.., alt((spaces.void(), none_of(';').void()))).parse_next(input)?;
        let _end = ';'.parse_next(input)?;
        Ok(())
    }

    pub fn global_decls(input: &mut Input<'_>) -> PResult<Vec<GlobalItems>> {
        repeat(0.., preceded(opt_spaces, Self::global_decl)).parse_next(input)
    }

    pub fn global_decl(input: &mut Input<'_>) -> PResult<GlobalItems> {
        if let Some(non_attributed_global) = opt(alt((
            cut_err(";").default_value::<GlobalItems>(),
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

    fn attributes(input: &mut Input<'_>) -> PResult<GlobalItems> {
        repeat(0.., terminated(cut_err(Self::attribute), opt_spaces))
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }

    fn global_alias(input: &mut Input<'_>) -> PResult<GlobalItems> {
        seq!(
            _: cut_err("alias"),
            _: spaces,
            Self::ident,
            _: opt_spaces,
            _: '=',
            _: opt_spaces,
            Self::type_specifier,
            _: opt_spaces,
            _: ';'
        )
        .map(|(a, c)| GlobalItems::single(a).join(c))
        .parse_next(input)
    }

    fn global_const_assert(input: &mut Input<'_>) -> PResult<GlobalItems> {
        seq!(
            _: cut_err("const_assert"),
            _: opt_spaces,
            Self::expression,
            _: opt_spaces,
            _: ';',
        )
        .map(|(a,)| a)
        .parse_next(input)
    }

    fn global_struct(input: &mut Input<'_>) -> PResult<GlobalItems> {
        (
            cut_err("struct"),
            Self::ident,
            (opt_spaces, '{', opt_spaces),
            repeat(
                1..,
                terminated(
                    Self::attributes,
                    (
                        opt_spaces,
                        Self::ident_pattern_token,
                        opt_spaces,
                        ':',
                        Self::type_specifier,
                        opt_spaces,
                    ),
                ),
            )
            .map(|v: Vec<_>| v.into_iter().collect::<GlobalItems>()),
            (opt_spaces, opt(','), opt_spaces, '}'),
        )
            .map(|(_, a, _, b, _)| GlobalItems { items: vec![a] }.join(b))
            .parse_next(input)
    }

    fn global_fn(input: &mut Input<'_>) -> PResult<GlobalItems> {
        let _ = cut_err("fn").parse_next(input)?;
        let _ = spaces.parse_next(input)?;
        let name = Self::ident.parse_next(input)?;
        let _ = (opt_spaces, '(', opt_spaces).parse_next(input)?;
        let params = separated(0.., Self::fn_param, (opt_spaces, ',', opt_spaces))
            .map(|v: Vec<_>| v.into_iter().collect::<GlobalItems>())
            .parse_next(input)?;
        let _ = (opt_spaces, opt(','), opt_spaces, ')', opt_spaces).parse_next(input)?;
        let return_type = opt((
            " ->",
            opt_spaces,
            Self::attributes,
            opt_spaces,
            Self::type_specifier,
        )
            .map(|(_, _, a, _, b)| a.join(b)))
        .parse_next(input)?;
        let _ = opt_spaces.parse_next(input)?;
        let body_attributes = Self::attributes.parse_next(input)?;
        let _ = (opt_spaces, '{', opt_spaces).parse_next(input)?;
        let body = Self::statements.parse_next(input)?;
        let _ = (opt_spaces, '}').parse_next(input)?;

        Ok(GlobalItems::single(name)
            .join(params)
            .join(return_type)
            .join(body_attributes)
            .join(body))
    }

    fn fn_param(input: &mut Input<'_>) -> PResult<GlobalItems> {
        seq!(
            Self::attributes,
            Self::ident,
            preceded((opt_spaces, ':', opt_spaces), Self::type_specifier,),
        )
        .map(|(a, b, c)| a.join(GlobalItems::single(b)).join(c))
        .parse_next(input)
    }

    fn global_var(input: &mut Input<'_>) -> PResult<GlobalItems> {
        // Things like var<private> d: f32;
        seq!(
            _: cut_err("var"),
            _: spaces,
            _: Self::maybe_template_args,
            Self::optionally_typed_ident,
            opt(preceded(
                (opt_spaces, '=', opt_spaces),
                Self::expression
            )),
            _: opt_spaces,
            _: ';',
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }
    fn global_override(input: &mut Input<'_>) -> PResult<GlobalItems> {
        seq!(
            _: cut_err("override"),
            _: opt_spaces,
            Self::optionally_typed_ident,
            opt(preceded(
                (opt_spaces, '=', opt_spaces),
                Self::expression
            )),
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }
    fn global_const(input: &mut Input<'_>) -> PResult<GlobalItems> {
        seq!(
            _:cut_err("const"),
            Self::optionally_typed_ident,
            _: opt_spaces,
            _: '=',
            _: opt_spaces,
            Self::expression,
            _: opt_spaces,
            _: ';',
        )
        .map(|(a, b)| a.join(b))
        .parse_next(input)
    }

    pub fn statements(input: &mut Input<'_>) -> PResult<GlobalItems> {
        repeat(0.., terminated(Self::statement, opt_spaces))
            .map(|v: Vec<_>| v.into_iter().collect())
            .parse_next(input)
    }
    pub fn statement(input: &mut Input<'_>) -> PResult<GlobalItems> {}

    pub fn optionally_typed_ident(input: &mut Input<'_>) -> PResult<GlobalItems> {
        (
            Self::ident,
            opt(preceded(
                (opt_spaces, ':', opt_spaces),
                Self::type_specifier,
            )),
        )
            .map(|(a, b)| GlobalItems::single(a).join(b))
            .parse_next(input)
    }

    pub fn type_specifier(input: &mut Input<'_>) -> PResult<GlobalItems> {
        (Self::ident, opt_spaces, Self::maybe_template_args)
            .map(|(a, _, b)| GlobalItems::single(a).join(b))
            .parse_next(input)
    }

    pub fn attribute(input: &mut Input<'_>) -> PResult<GlobalItems> {
        let _start = '@'.parse_next(input)?;
        let _ = opt_spaces.parse_next(input)?;
        let name = Self::ident_pattern_token.parse_next(input)?;
        let _ = opt_spaces.parse_next(input)?;
        let _opening = '('.parse_next(input)?;
        let _ = opt_spaces.parse_next(input)?;
        let expressions = Self::expression_comma_list.parse_next(input)?;
        let _ = opt_spaces.parse_next(input)?;
        let _closing = ')'.parse_next(input)?;

        match name {
            "compute" | "const" | "fragment" | "interpolate" | "invariant" | "must_use"
            | "vertex" | "builtin" | "diagnostic" => Ok(Default::default()),
            "workgroup_size" | "align" | "binding" | "blend_src" | "group" | "id" | "location"
            | "size" => Ok(expressions.into_iter().collect()),
            _ => fail.parse_next(input),
        }
    }

    pub fn argument_expression_list(input: &mut Input<'_>) -> PResult<GlobalItems> {
        delimited(
            (cut_err('('), opt_spaces),
            Self::expression_comma_list.map(|v| v.into_iter().collect()),
            (opt_spaces, ')'),
        )
        .parse_next(input)
    }

    pub fn expression_comma_list(input: &mut Input<'_>) -> PResult<Vec<GlobalItems>> {
        terminated(
            separated(1.., Self::expression, (opt_spaces, ",", opt_spaces)),
            (opt_spaces, ","),
        )
        .parse_next(input)
    }

    /// Parses an expression while ignoring the order of operations.
    pub fn expression(input: &mut Input<'_>) -> PResult<GlobalItems> {
        let start = Self::unary_expression.parse_next(input)?;
        let _ = opt_spaces.parse_next(input)?;

        fn operator(input: &mut Input<'_>) -> PResult<()> {
            // bitwise_expression.post.unary_expression
            // & ^ |
            // expression
            // && ||
            // relational_expression.post.unary_expression
            // > >= < <= != ==
            // shift_expression.post.unary_expression
            // % * / + - << >>
            alt([
                "&&", "&", "||", "|", "^", //
                ">>", ">=", ">", "<<", "<=", "<", "!=", "==", //
                "%", "*", "/", "+", "-",
            ])
            .void()
            .parse_next(input)
        }

        let next = repeat(
            1..,
            preceded((opt_spaces, operator, opt_spaces), Self::unary_expression),
        )
        .map(|v: Vec<_>| -> GlobalItems { v.into_iter().collect() })
        .parse_next(input)?;

        Ok(start.join(next))
    }

    pub fn unary_expression(input: &mut Input<'_>) -> PResult<GlobalItems> {
        alt((
            preceded(
                (cut_err(one_of(['!', '&', '*', '-', '~'])), opt_spaces),
                Self::unary_expression,
            ),
            separated_pair(
                Self::primary_expression,
                opt_spaces,
                opt(Self::component_or_swizzle_specifier),
            )
            .map(|(a, b)| a.join(b)),
        ))
        .parse_next(input)
    }

    pub fn primary_expression(input: &mut Input<'_>) -> PResult<GlobalItems> {
        if let Some((ident, span)) =
            opt(cut_err(Self::ident_pattern_token).with_span()).parse_next(input)?
        {
            if ident == "true" || ident == "false" {
                Ok(GlobalItems::default())
            } else {
                let _ = opt_spaces.parse_next(input)?;
                let template_args = Self::maybe_template_args.parse_next(input)?;
                let _ = opt_spaces.parse_next(input)?;
                let arguments = opt(Self::argument_expression_list).parse_next(input)?;
                Ok(GlobalItems::single(GlobalItem(span))
                    .join(template_args)
                    .join(arguments))
            }
        } else {
            alt((
                Self::literal.default_value::<GlobalItems>(),
                delimited(
                    (cut_err('('), opt_spaces),
                    Self::expression,
                    (opt_spaces, ')'),
                ),
            ))
            .parse_next(input)
        }
    }

    /// Can either be a normal comparison, or a template. We don't know yet.
    pub fn maybe_template_args(input: &mut Input<'_>) -> PResult<GlobalItems> {
        opt(delimited('<', Self::expression_comma_list, opt('>')))
            .map(|v| match v {
                Some(v) => v.into_iter().collect(),
                None => GlobalItems::default(),
            })
            .parse_next(input)
    }

    pub fn literal(input: &mut Input<'_>) -> PResult<()> {
        alt((
            "false".void(),
            "true".void(),
            Self::hex_literal,
            Self::decimal_literal,
        ))
        .parse_next(input)
    }

    pub fn component_or_swizzle_specifier(input: &mut Input<'_>) -> PResult<GlobalItems> {
        alt((
            (
                cut_err('.'),
                opt_spaces,
                Self::ident_pattern_token,
                opt_spaces,
                opt(Self::component_or_swizzle_specifier),
            )
                .default_value::<GlobalItems>(),
            seq!(
                _:cut_err('['),
                _:opt_spaces,
                Self::expression,
                _:opt_spaces,
                _:']',
                _:opt_spaces,
                opt(Self::component_or_swizzle_specifier),
            )
            .map(|(a, b)| a.join(b)),
        ))
        .parse_next(input)
    }
}
