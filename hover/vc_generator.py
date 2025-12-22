from . import ir


class VCGenerator:
    def __init__(self):
        self.vc_list = []  # List of VCs to prove

    def generate(self, stmt, postcond):
        return self.wp(stmt, postcond)

    def wp(self, stmt, postcond):
        """
        Compute weakest precondition: wp(stmt, postcond)
        """
        if isinstance(stmt, ir.Skip):
            return postcond

        elif isinstance(stmt, ir.Assign):
            # wp(x = e, Q) = Q[e/x]  (substitute e for x in Q)
            return self.substitute(postcond, stmt.name, stmt.expr)

        elif isinstance(stmt, ir.Seq):
            # wp(s1; s2, Q) = wp(s1, wp(s2, Q))
            wp2 = self.wp(stmt.s2, postcond)
            return self.wp(stmt.s1, wp2)

        elif isinstance(stmt, ir.If):
            # wp(if c then s1 else s2, Q) = (c => wp(s1, Q)) and (not c => wp(s2, Q))
            wp_then = self.wp(stmt.then_stmt, postcond)
            wp_else = self.wp(stmt.else_stmt, postcond)

            return ir.LogicOp(
                ir.LogicOp(stmt.cond, "implies", wp_then),
                "and",
                ir.LogicOp(ir.Not(stmt.cond), "implies", wp_else),
            )

        elif isinstance(stmt, ir.While):
            # We need to generate 3 VCs:
            # 1. Invariant holds initially (handled by caller)
            # 2. Invariant + condition => invariant after body (preservation)
            # 3. Invariant + not condition => postcondition (termination)

            inv = stmt.inv
            cond = stmt.cond
            body = stmt.body

            # VC2: Invariant preservation
            # inv and cond => wp(body, inv)
            wp_body = self.wp(body, inv)
            vc_preservation = ir.LogicOp(
                ir.LogicOp(inv, "and", cond), "implies", wp_body
            )
            self.vc_list.append(("Loop preservation", vc_preservation))

            # VC3: Loop exit ensures postcondition
            # inv and not cond => postcond
            vc_exit = ir.LogicOp(
                ir.LogicOp(inv, "and", ir.Not(cond)), "implies", postcond
            )
            self.vc_list.append(("Loop exit", vc_exit))

            # The precondition for the while loop is the invariant
            return inv

        else:
            raise ValueError(f"Unknown statement type: {type(stmt)}")

    def substitute(self, expr, var_name, replacement):
        """
        Replace all occurrences of var_name in expr with replacement.
        """
        if isinstance(expr, ir.Literal) or isinstance(expr, ir.BoolConst):
            return expr

        elif isinstance(expr, ir.Var):
            if expr.name == var_name:
                return replacement
            return expr

        elif isinstance(expr, ir.BinOp):
            return ir.BinOp(
                self.substitute(expr.left, var_name, replacement),
                expr.op,
                self.substitute(expr.right, var_name, replacement),
            )

        elif isinstance(expr, ir.Compare):
            return ir.Compare(
                self.substitute(expr.left, var_name, replacement),
                expr.op,
                self.substitute(expr.right, var_name, replacement),
            )

        elif isinstance(expr, ir.LogicOp):
            return ir.LogicOp(
                self.substitute(expr.left, var_name, replacement),
                expr.op,
                self.substitute(expr.right, var_name, replacement),
            )

        elif isinstance(expr, ir.Not):
            return ir.Not(self.substitute(expr.expr, var_name, replacement))

        else:
            raise ValueError(f"Unknown expression type in substitute: {type(expr)}")

    def get_vcs(self):
        """Return all generated VCs."""
        return self.vc_list
