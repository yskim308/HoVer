from dataclasses import dataclass


# Base classes
@dataclass
class Expr:
    pass


@dataclass
class Stmt:
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
    else_stmt: Stmt  # Can be an empty 'Seq' or 'Pass' if there is no else


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

    s1: Stmt
    s2: Stmt
