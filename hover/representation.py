class Assign:
    def __init__(self, target, expr):
        self.target = target
        self.expr = expr


class While:
    def __init__(self, condition, invariant, body, line_number):
        self.condition = condition
        self.invariant = invariant
        self.body = body
        self.line_number = line_number


class If:
    def __init__(self, condition, true_branch, else_branch):
        self.condition = condition
        self.true_branch = true_branch
        self.else_branch = else_branch


class Program:
    def __init__(self, pre, post, stmts):
        self.pre = pre
        self.post = post
        self.stmts = stmts
