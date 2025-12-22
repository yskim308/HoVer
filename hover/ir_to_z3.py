import z3

from . import ir


def ir_to_z3(expr, z3_vars):
    """
    Convert an IR expression to a Z3 expression.
    z3_vars: dict mapping variable names to Z3 variables
    """

    if isinstance(expr, ir.Literal):
        return expr.val

    elif isinstance(expr, ir.BoolConst):
        return expr.val

    elif isinstance(expr, ir.Var):
        if expr.name not in z3_vars:
            z3_vars[expr.name] = z3.Int(expr.name)
        return z3_vars[expr.name]

    elif isinstance(expr, ir.BinOp):
        left = ir_to_z3(expr.left, z3_vars)
        right = ir_to_z3(expr.right, z3_vars)

        if expr.op == "+":
            return left + right
        elif expr.op == "-":
            return left - right
        elif expr.op == "*":
            return left * right

    elif isinstance(expr, ir.Compare):
        left = ir_to_z3(expr.left, z3_vars)
        right = ir_to_z3(expr.right, z3_vars)

        if expr.op == "<":
            return left < right
        elif expr.op == "<=":
            return left <= right
        elif expr.op == "==":
            return left == right
        elif expr.op == ">=":
            return left >= right
        elif expr.op == ">":
            return left > right
        elif expr.op == "!=":
            return left != right

    elif isinstance(expr, ir.LogicOp):
        left = ir_to_z3(expr.left, z3_vars)
        right = ir_to_z3(expr.right, z3_vars)

        if expr.op == "and":
            return z3.And(left, right)
        elif expr.op == "or":
            return z3.Or(left, right)
        elif expr.op == "implies":
            return z3.Implies(left, right)

    elif isinstance(expr, ir.Not):
        return z3.Not(ir_to_z3(expr.expr, z3_vars))

    else:
        raise ValueError(f"Unknown expression type: {type(expr)}")
