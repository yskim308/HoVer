import ast

import expression as E  # for expressions,
import representation as S  # for statements


class ASTTranslator:
    def __init__(self, source_code, annotations):
        self.source = source_code
        self.inv_map = annotations["invariants"]  # {line_no: "invariant_string"}

    def parse(self):
        """Main entry point."""
        tree = ast.parse(self.source)

        if not tree.body:
            return None  # Or a 'Pass' statement if you defined one

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
            return S.Seq(first, rest)

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
                return E.Literal(node.value)
            elif isinstance(node.value, bool):
                return E.BoolConst(node.value)

        elif isinstance(node, ast.Name):
            return E.Var(node.id)

        elif isinstance(node, ast.BinOp):
            return self._trans_binop(node)

        elif isinstance(node, ast.Compare):
            return self._trans_compare(node)

        elif isinstance(node, ast.BoolOp):
            return self._trans_boolop(node)

        else:
            raise ValueError(f"Unsupported expression: {type(node).__name__}")

    # --- Specific Handlers ---

    def _trans_assign(self, node):
        # [cite_start]Restriction: Only integer values allowed [cite: 20]
        target = node.targets[0]  # We assume single assignment (x = 1, not x = y = 1)
        if not isinstance(target, ast.Name):
            raise ValueError("Assignments must be to simple variables.")

        return S.Assign(target.id, self.translate_expr(node.value))

    def _trans_if(self, node):
        # Recursively translate the 'then' block
        then_part = self.translate_stmt_list(node.body)

        # Recursively translate the 'else' block (if it exists)
        else_part = self.translate_stmt_list(node.orelse) if node.orelse else None

        # NOTE: If else_part is None, you might want to return a generic 'Pass' or handle it in VC generation.
        # For now, let's assume your S.If supports None or you wrap it in an empty Seq.
        return S.If(self.translate_expr(node.test), then_part, else_part)

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
        # This is tricky: The invariant is a string like "x > 0".
        # We need to parse this string into an Expression IR too.
        inv_ast = ast.parse(inv_str, mode="eval").body
        inv_expr = self.translate_expr(inv_ast)

        body = self.translate_stmt_list(node.body)

        return S.While(self.translate_expr(node.test), inv_expr, body)

    def _trans_binop(self, node):
        # [cite_start]Supported: +, -, * [cite: 21]
        op_map = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}
        op_type = type(node.op)

        if op_type not in op_map:
            raise ValueError(f"Unsupported arithmetic operator: {op_type}")

        return E.BinOp(
            self.translate_expr(node.left),
            op_map[op_type],
            self.translate_expr(node.right),
        )

    def _trans_compare(self, node):
        # [cite_start]Supported: <, <=, ==, >=, > [cite: 21]
        # HANDLE CHAINED COMPARISONS: 0 < x < 10
        if len(node.ops) > 1:
            # You must unroll this into (0 < x) and (x < 10)
            # This is complex; for a "dumb" start, you can raise an error
            # or implement the "LogicOp(and)" splitting here.
            raise NotImplementedError(
                "Chained comparisons (0 < x < 10) require special handling."
            )

        left = self.translate_expr(node.left)
        right = self.translate_expr(node.comparators[0])

        op_map = {ast.Lt: "<", ast.LtE: "<=", ast.Eq: "==", ast.GtE: ">=", ast.Gt: ">"}
        op_type = type(node.ops[0])

        if op_type not in op_map:
            raise ValueError(f"Unsupported comparison operator: {op_type}")

        return E.Compare(left, op_map[op_type], right)
