import ast

import ir


class ASTTranslator:
    def __init__(self, source_code, annotations):
        self.source = source_code
        self.inv_map = annotations["invariants"]  # {line_no: "invariant_string"}

    def parse(self):
        """Main entry point."""
        tree = ast.parse(self.source)

        if not tree.body:
            return ir.Skip

        return self.translate_stmt_list(tree.body)

    def translate_stmt_list(self, stmts):
        """
        Converts a list of Python AST statements [s1, s2, s3]
        into a nested IR: Seq(s1, Seq(s2, s3)).
        """
        if not stmts:
            return None  # End of sequence

        first = self.translate_stmt(stmts[0])
        rest = self.translate_stmt_list(stmts[1:])

        if rest is None:
            return first
        else:
            return ir.Seq(first, rest)

    def translate_stmt(self, node):
        """Dispatches to specific handlers based on node type."""
        if isinstance(node, ast.Assign):
            return self._trans_assign(node)
        elif isinstance(node, ast.If):
            return self._trans_if(node)
        elif isinstance(node, ast.While):
            return self._trans_while(node)
        else:
            raise ValueError(
                f"Unsupported statement type: {type(node).__name__} at line {node.lineno}"
            )

    def translate_expr(self, node):
        """Recursively converts AST expressions to IR expressions."""
        if isinstance(node, ast.Constant):  # Python 3.8+ uses Constant for numbers
            if isinstance(node.value, int):
                return ir.Literal(node.value)
            if isinstance(node.value, bool):
                return ir.BoolConst(node.value)
            raise ValueError(f"Unsupported constant: {node.value!r}")

        elif isinstance(node, ast.Name):
            return ir.Var(node.id)

        elif isinstance(node, ast.BinOp):
            return self._trans_binop(node)

        elif isinstance(node, ast.Compare):
            return self._trans_compare(node)

        elif isinstance(node, ast.BoolOp):
            return self._trans_boolop(node)

        elif isinstance(node, ast.UnaryOp):
            return self._trans_unaryop(node)

        else:
            raise ValueError(f"Unsupported expression: {type(node).__name__}")

    # --- Specific Handlers ---

    def _trans_assign(self, node):
        target = node.targets[0]
        if not isinstance(target, ast.Name):
            raise ValueError("Assignments must be to simple variables.")

        return ir.Assign(target.id, self.translate_expr(node.value))

    def _trans_if(self, node):
        # Recursively translate the 'then' block
        then_part = self.translate_stmt_list(node.body)

        # Recursively translate the 'else' block (if it exists)
        else_part = self.translate_stmt_list(node.orelse) if node.orelse else ir.Seq()

        # For now, let's assume your S.If supports None or you wrap it in an empty Seq.
        return ir.If(self.translate_expr(node.test), then_part, else_part)

    def _trans_while(self, node):
        # 1. Look for the invariant in our map
        # Logic: The invariant must be IMMEDIATELY preceding.
        # Typically, if the 'while' is on line N, the comment is on N-1.
        inv_line = node.lineno - 1
        inv_str = self.inv_map.get(inv_line)

        if not inv_str:
            raise ValueError(
                f"Missing #inv: annotation for while loop at line {node.lineno}"
            )

        # 2. Parse the invariant string itself!
        inv_ast = ast.parse(inv_str, mode="eval").body
        inv_expr = self.translate_expr(inv_ast)

        body = self.translate_stmt_list(node.body)

        return ir.While(self.translate_expr(node.test), inv_expr, body)

    def _trans_binop(self, node):
        op_map = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}
        op_type = type(node.op)

        if op_type not in op_map:
            raise ValueError(f"Unsupported arithmetic operator: {op_type}")

        return ir.BinOp(
            self.translate_expr(node.left),
            op_map[op_type],
            self.translate_expr(node.right),
        )

    def _trans_compare(self, node):
        """
        Handle comparisons, including chained ones like 0 < x < 10.
        Chained comparisons are converted to conjunctions:
        0 < x < 10  =>  (0 < x) and (x < 10)
        """
        op_map = {
            ast.Lt: "<",
            ast.LtE: "<=",
            ast.Eq: "==",
            ast.GtE: ">=",
            ast.Gt: ">",
            ast.NotEq: "!=",
        }

        # Handle chained comparisons
        if len(node.ops) > 1:
            # Build chain: left op1 comparators[0] op2 comparators[1] ...
            # Convert to: (left op1 comparators[0]) and (comparators[0] op2 comparators[1]) and ...
            comparisons = []

            prev_expr = self.translate_expr(node.left)

            for op, comparator in zip(node.ops, node.comparators):
                curr_expr = self.translate_expr(comparator)

                op_type = type(op)
                if op_type not in op_map:
                    raise ValueError(f"Unsupported comparison operator: {op_type}")

                comparisons.append(ir.Compare(prev_expr, op_map[op_type], curr_expr))
                prev_expr = curr_expr

            # Chain all comparisons with 'and'
            result = comparisons[0]
            for comp in comparisons[1:]:
                result = ir.LogicOp(result, "and", comp)

            return result

        # Simple comparison (single operator)
        left = self.translate_expr(node.left)
        right = self.translate_expr(node.comparators[0])

        op_type = type(node.ops[0])
        if op_type not in op_map:
            raise ValueError(f"Unsupported comparison operator: {op_type}")

        return ir.Compare(left, op_map[op_type], right)

    def _trans_boolop(self, node):
        """
        Handle boolean operators (and, or).
        """
        op_map = {ast.And: "and", ast.Or: "or"}
        op_type = type(node.op)

        if op_type not in op_map:
            raise ValueError(f"Unsupported boolean operator: {op_type}")

        # BoolOp can have multiple values: (a and b and c)
        # We need to chain them: LogicOp(a, 'and', LogicOp(b, 'and', c))
        values = [self.translate_expr(v) for v in node.values]

        result = values[0]
        for val in values[1:]:
            result = ir.LogicOp(result, op_map[op_type], val)

        return result

    def _trans_unaryop(self, node):
        """
        Handle unary operators (mainly 'not').
        """
        if isinstance(node.op, ast.Not):
            return ir.Not(self.translate_expr(node.operand))
        else:
            raise ValueError(f"Unsupported unary operator: {type(node.op).__name__}")
