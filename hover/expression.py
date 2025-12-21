from dataclasses import dataclass


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
