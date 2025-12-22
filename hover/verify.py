import ast

import z3

from . import ast_to_ir, vc_generator
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

    # VC1: Check that actual precondition implies computed precondition
    vc_initial = ir.LogicOp(precond, "implies", computed_precond)
    vcgen.vc_list.insert(0, ("Initial condition", vc_initial))

    # Verify all VCs with Z3
    print("Verification Conditions:")
    print("=" * 60)

    z3_vars = {}
    solver = z3.Solver()

    all_valid = True
    for name, vc in vcgen.get_vcs():
        print(f"\n{name}:")
        z3_vc = ir_to_z3(vc, z3_vars)

        # Check if VC is valid (always true)
        solver.push()
        solver.add(z3.Not(z3_vc))  # Try to find counterexample

        result = solver.check()
        if result == z3.unsat:
            print("  ✓ VALID")
        else:
            print("  ✗ INVALID")
            print(f"  Counterexample: {solver.model()}")
            all_valid = False

        solver.pop()

    print("\n" + "=" * 60)
    if all_valid:
        print("✓ Program verified successfully!")
    else:
        print("✗ Verification failed!")

    return all_valid
