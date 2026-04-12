#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[repr(u16)]
pub enum SyntaxKind {
    /// Hope that you never get one of these!
    #[doc(hidden)]
    TOMBSTONE,
    SourceFile,
    /// A name that can be referenced by a [`NameRef`]
    Name,
    /// a function
    FunctionDeclaration,
    /// the <a, b, c> of a template
    TemplateList,
    /// The parameters to a function call
    FunctionParameters,
    /// a function parameter
    Parameter,
    /// a function return type
    ReturnType,
    /// a group of statements contained in braces

    // Statements https://www.w3.org/TR/WGSL/#statements

    /// [10.1. Const Assert Statement](https://www.w3.org/TR/WGSL/#const-assert-statement)
    /// `const_assert 1 < 2;`
    AssertStatement,

    /// [9.1. Compound Statement](https://www.w3.org/TR/WGSL/#compound-statement-section)
    ///
    /// ```wgsl
    /// { }
    /// ```
    CompoundStatement,

    /// [9.2. Assignment Statement](https://www.w3.org/TR/WGSL/#assignment)
    ///
    /// ```wgsl
    /// a = b
    /// ```
    AssignmentStatement,

    /// ```wgsl
    /// _ = b
    /// ```
    PhonyAssignmentStatement,

    /// ```wgsl
    /// a += b
    /// ```
    CompoundAssignmentStatement,

    /// `break;`
    BreakStatement,
    /// `break if 4 < 5;`
    BreakIfStatement,

    /// `continue;`
    ContinueStatement,

    /// `discard;`
    DiscardStatement,

    /// A lonely `;`
    EmptyStatement,
    /// [9.5. Function Call Statement](https://www.w3.org/TR/WGSL/#function-call-statement)
    FunctionCallStatement,

    /// [9.4.3. Loop Statement](https://www.w3.org/TR/WGSL/#loop-statement)
    /// Structurally very similar to a compound statement
    /// ```wgsl
    /// loop { statements }
    /// ```
    LoopStatement,
    /// `while (expression) { statements }`
    WhileStatement,
    /// `if (expression) { statements }`
    IfStatement,
    /// `switch expression { case 1, 2: {} default: {} }`
    SwitchStatement,
    /// The body of a switch statement
    SwitchBody,
    /// `case 1, 2: {};`
    SwitchBodyCase,
    /// The `1, 2` in `case 1, 2: {}`
    SwitchCaseSelectors,
    /// `default` when it appears in a `case default`
    SwitchDefaultSelector,

    /// `i++`, `i--`
    IncrementDecrementStatement,
    IfClause,
    ElseIfClause,
    ElseClause,
    /// `for(init, cmp, update) {}`
    ForStatement,
    ForInitializer,
    ForCondition,
    ForContinuingPart,
    /// `a.b`
    FieldExpression,
    /// `pow(2, 3)`
    FunctionCall,
    /// Arguments in an attribute or in a function call
    Arguments,
    /// an identifier with an optional template `foo<bar>`
    /// can refer to a type
    IdentExpression,
    /// A WESL fully qualified identifier.
    /// `foo::bar::baz`
    Path,
    /// `a\[0\]`
    IndexExpression,
    /// `return foo;`
    ReturnStatement,
    /// an expression of the form `left_side <operator> right_side`
    InfixExpression,
    /// an expression of the form `<operator> right_side`
    PrefixExpression,
    /// a literal expression
    Literal,
    /// an expression inside parenthesis
    ParenthesisExpression,
    /// a type with an optional template `foo<bar>`
    TypeSpecifier,
    /// `location(0, 1, 2)`
    Attribute,
    /// the definition of a struct
    StructDeclaration,
    /// the members of a struct definition inside of braces
    StructBody,
    /// one field of a struct declaration
    StructMember,
    /// `const global: u32 = 10u`
    ConstantDeclaration,
    /// `var<uniform> test: u32`
    VariableDeclaration,
    /// `let test: u32 = 3;`
    LetDeclaration,
    /// `override test: u32`
    OverrideDeclaration,

    /// `continuing { statements }`
    ContinuingStatement,
    /// Type alias declaration: `alias float4 = vec4<f32>`
    TypeAliasDeclaration,

    /// `enable f16`
    EnableDirective,
    EnableExtensionName,
    /// `requires unrestricted_pointer_parameters`
    RequiresDirective,
    LanguageExtensionName,

    /// `import foo::bar as baz;`
    ImportStatement,
    /// The `package` token in an import
    ImportPackageRelative,
    /// The `super` token in an import
    ImportSuperRelative,
    /// `bar as baz`
    ImportItem,
    /// A recursive segment with a name `foo::...`
    ImportPath,
    /// A list of imports `{foo, bar, baz}`
    ImportCollection,

    // Tokens
    /// Source: <https://www.w3.org/TR/WGSL/#blankspace-and-line-breaks>
    Blankspace,
    /// `//`
    LineEndingComment,
    /// `/*`
    BlockComment,

    Identifier,
    // #[regex(r"0[fh]")]
    // #[regex(r"[1-9][0-9]*[fh]")]
    // // We need priorities because some cases (for example, 1.2) would match both
    // #[regex(r"[0-9]*\.[0-9]+([eE][+-]?[0-9]+)?[fh]?", priority = 5)]
    // #[regex(r"[0-9]+\.[0-9]*([eE][+-]?[0-9]+)?[fh]?")]
    // #[regex(r"[0-9]+[eE][+-]?[0-9]+[fh]?")]
    // #[regex(
    //     r"0[xX][0-9a-fA-F]*\.[0-9a-fA-F]+([pP][+-]?[0-9]+[fh]?)?",
    //     priority = 9
    // )]
    // #[regex(r"0[xX][0-9a-fA-F]+\.[0-9a-fA-F]*([pP][+-]?[0-9]+[fh]?)?")]
    // #[regex(r"0[xX][0-9a-fA-F]+[pP][+-]?[0-9]+[fh]?")]
    FloatLiteral,
    // #[regex(r"0(i|u|li|lu)?")]
    // #[regex(r"[1-9][0-9]*(i|u|li|lu)?")]
    // #[regex(r"0[xX][0-9a-fA-F]+(i|u|li|lu)?")]
    IntLiteral,
    StringLiteral,
    Alias,
    Break,
    Case,
    /// <https://www.w3.org/TR/WGSL/#syntax_kw-const>
    Const,
    ConstantAssert,
    Continue,
    Continuing,
    Default,
    // This is a keyword. It could be part of the global directive or an attribute.
    Diagnostic,
    DiagnosticControl,
    DiagnosticDirective,
    DiagnosticRuleName,
    SeverityControlName,
    DiagnosticAttribute,
    OtherAttribute,
    AlignAttribute,
    BindingAttribute,
    BlendSrcAttribute,
    BuiltinAttribute,
    ConstantAttribute,
    GroupAttribute,
    IdAttribute,
    InterpolateAttribute,
    InvariantAttribute,
    LocationAttribute,
    MustUseAttribute,
    SizeAttribute,
    WorkgroupSizeAttribute,
    VertexAttribute,
    FragmentAttribute,
    ComputeAttribute,
    Align,
    Builtin,
    Binding,
    BlendSrc,
    Group,
    Id,
    Interpolate,
    Invariant,
    Location,
    MustUse,
    Size,
    WorkgroupSize,
    Vertex,
    Fragment,
    Compute,
    Perspective,
    Linear,
    Flat,
    Center,
    Centroid,
    Sample,
    First,
    Either,
    BuiltinValueName,
    InterpolateSamplingName,
    InterpolateTypeName,
    Discard,
    Else,
    Enable,
    False,
    Fn,
    For,
    If,
    Let,
    Loop,
    Override,
    Requires,
    Return,
    Struct,
    Switch,
    True,
    Var,
    While,
    // syntactic tokens
    /// `&`
    And,
    /// `&&`
    AndAnd,
    /// `->`
    Arrow,
    /// `@`
    AttributeOperator,
    /// `/`
    ForwardSlash,
    /// `!`
    Bang,
    /// `[`
    BracketLeft,
    /// `]`
    BracketRight,
    /// `{`
    BraceLeft,
    /// `}`
    BraceRight,
    /// `:`
    Colon,
    /// `::`
    ColonColon,
    /// `,`
    Comma,
    /// `=`
    Equal,
    /// `==`
    EqualEqual,
    /// `!=`
    NotEqual,
    /// `>`
    GreaterThan,
    /// `>=`
    /// Note: lexer has special case for this one
    GreaterThanEqual,
    /// `<`
    LessThan,
    /// `<=`
    LessThanEqual,
    /// `%`
    Modulo,
    /// `-`
    Minus,
    /// `--`
    MinusMinus,
    /// `.`
    Period,
    /// `+`
    Plus,
    /// `++`
    PlusPlus,
    /// `|`
    Or,
    /// `||`
    OrOr,
    /// `(`
    ParenthesisLeft,
    /// `)`
    ParenthesisRight,
    /// `;`
    Semicolon,
    /// `*`
    Star,
    // `~`
    Tilde,
    /// `_`
    Underscore,
    /// `^`
    Xor,

    Import,
    Package,
    Super,
    As,

    /// `+=`
    PlusEqual,
    /// `-=`
    MinusEqual,
    /// `*=`
    TimesEqual,
    /// `/=`
    DivisionEqual,
    /// `%=`
    ModuloEqual,
    /// `&=`
    AndEqual,
    /// `|=`
    OrEqual,
    /// `^=`
    XorEqual,
    /// `>>=`
    /// Note: lexer has special case for this one
    ShiftRightEqual,
    /// `<<=`
    ShiftLeftEqual,
    /// `<<`
    ShiftLeft,
    /// `>>`
    /// Note: lexer has special case for this one
    ShiftRight,
    TemplateStart,
    TemplateEnd,

    // Only used internally by the parser
    #[doc(hidden)]
    EOF,
    #[doc(hidden)]
    EOFAttribute,
    #[doc(hidden)]
    EOFExpression,
    #[doc(hidden)]
    EOFStatement,
    #[doc(hidden)]
    EOFTypeSpecifier,

    Error,
}

impl SyntaxKind {
    #[must_use]
    pub const fn is_whitespace(self) -> bool {
        matches!(self, Self::Blankspace)
    }

    #[must_use]
    pub const fn is_trivia(self) -> bool {
        matches!(
            self,
            Self::Blankspace | Self::LineEndingComment | Self::BlockComment
        )
    }

    #[must_use]
    pub const fn is_directive(self) -> bool {
        matches!(
            self,
            Self::SourceFile
                | Self::EnableDirective
                | Self::RequiresDirective
                | Self::DiagnosticDirective
                | Self::Attribute
                | Self::ImportStatement
                | Self::ImportPath
                | Self::ImportCollection
                | Self::ImportItem
                | Self::ImportPackageRelative
                | Self::ImportSuperRelative
        )
    }

    #[must_use]
    pub const fn is_declaration(self) -> bool {
        matches!(
            self,
            Self::FunctionDeclaration
                | Self::Parameter
                | Self::ReturnType
                | Self::StructDeclaration
                | Self::StructMember
                | Self::VariableDeclaration
                | Self::LetDeclaration
                | Self::ConstantDeclaration
                | Self::OverrideDeclaration
                | Self::TypeAliasDeclaration
        )
    }

    #[must_use]
    pub const fn is_statement(self) -> bool {
        matches!(
            self,
            Self::IfStatement
                | Self::WhileStatement
                | Self::SwitchStatement
                | Self::LoopStatement
                | Self::ContinuingStatement
                | Self::BreakIfStatement
                | Self::SwitchBodyCase
                | Self::ForStatement
                | Self::CompoundStatement
                | Self::AssignmentStatement
                | Self::CompoundAssignmentStatement
                | Self::IncrementDecrementStatement
                | Self::ReturnStatement
                | Self::PhonyAssignmentStatement
                | Self::AssertStatement
        )
    }

    #[must_use]
    #[expect(clippy::as_conversions, reason = "repr(u16)")]
    pub const fn as_u16(self) -> u16 {
        self as u16
    }

    #[must_use]
    pub const fn from_u16(value: u16) -> Self {
        // Safety: SyntaxKind is #[repr(u16)] and in range
        unsafe { std::mem::transmute::<u16, Self>(value) }
    }
}
