from dataclasses import dataclass


# --- expressions ---
@dataclass
class Expr:
    """Base class for all expressions."""

    pass


# --- Atomic Values ---


@dataclass
class Literal(Expr):
    """
    example: 42
    """

    val: int


@dataclass
class Var(Expr):
    """
    example: x
    """

    name: str


# --- Arithmetic Expressions ---


@dataclass
class BinOp(Expr):
    """
    Represents binary arithmetic operations.
    Supported: +, -, *
    """

    left: Expr
    op: str  # '+', '-', '*'
    right: Expr


# --- Boolean / Logical Expressions ---
# These are used in 'if' conditions, 'while' loops, and Invariants.


@dataclass
class BoolConst(Expr):
    """
    Represent true or false
    """

    val: bool


@dataclass
class Compare(Expr):
    """
    Represents a comparison between two arithmetic expressions.
    """

    left: Expr
    op: str  # '<', '<=', '==', '>=', '>'
    right: Expr


@dataclass
class LogicOp(Expr):
    """
    Represents logical connections.
    """

    left: Expr
    op: str  # 'and', 'or', 'implies'
    right: Expr


@dataclass
class Not(Expr):
    """
    Represents logical negation.
    """

    expr: Expr  # not


# ---- statements -------
@dataclass
class Stmt:
    pass


@dataclass
class Skip(Stmt):
    pass


@dataclass
class Assign(Stmt):
    """
    represents: x = e
    """

    name: str  # The variable name on the LHS
    expr: Expr  # The expression on the RHS


@dataclass
class If(Stmt):
    """
    Represents: if cond: then_stmt else: else_stmt
    """

    cond: Expr
    then_stmt: Stmt
    else_stmt: Stmt = Skip()  # Can be an empty 'Seq' or 'Pass' if there is no else


@dataclass
class While(Stmt):
    """
    Represents:
        # inv: ...
        while cond: body

    """

    cond: Expr
    inv: Expr  # The Loop Invariant formula
    body: Stmt


@dataclass
class Seq(Stmt):
    """
    Represents: s1; s2

    This splits the code into a 'head' (s1) and the 'rest' (s2).
    """

    s1: Stmt = Skip()
    s2: Stmt = Skip()
