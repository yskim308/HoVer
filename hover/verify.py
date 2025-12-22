import ast

import z3

from . import ast_to_ir, ir, vc_generator
from .ir_to_z3 import ir_to_z3


def verify_program(source_code, annotations, precondition_str, postcondition_str):
    """
    Complete verification workflow.
    """

    # Parse the program
    translator = ast_to_ir.ASTTranslator(source_code, annotations)
    program_ir = translator.parse()

    # Parse pre/postconditions
    pre_ast = ast.parse(precondition_str, mode="eval").body
    precond = translator.translate_expr(pre_ast)

    post_ast = ast.parse(postcondition_str, mode="eval").body
    postcond = translator.translate_expr(post_ast)

    # Generate VCs
    vcgen = vc_generator.VCGenerator()
    computed_precond = vcgen.generate(program_ir, postcond)

    z3_vars = {}
    solver = z3.Solver()

    all_valid = True
    for name, vc in vcgen.get_vcs():
        z3_vc = ir_to_z3(vc, z3_vars)

        # Check if VC is valid (always true)
        solver.push()
        solver.add(z3.Not(z3_vc))  # Try to find counterexample

        result = solver.check()
        # if result == z3.unsat:
        #     print("  VALID")
        # else:
        #     print("  ✗ INVALID")
        #     print(f"  Counterexample: {solver.model()}")
        #     all_valid = False
        if result != z3.unsat:
            print("unverified")
            print(f"  Counterexample: {solver.model()}")
            all_valid = False
            break

        solver.pop()

    if all_valid:
        print("verified")

    return all_valid
