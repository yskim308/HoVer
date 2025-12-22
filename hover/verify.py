import ast

import z3

from . import ast_to_ir, ir, vc_generator
from .ir_to_z3 import ir_to_z3


def verify_program(source_code, annotations, precondition_str, postcondition_str):
    # print("=" * 60)
    # print("VERIFICATION DEBUG")
    # print("=" * 60)

    # Parse the program
    translator = ast_to_ir.ASTTranslator(source_code, annotations)
    program_ir = translator.parse()
    # print(f"Program IR: {program_ir}")

    # Parse pre/postconditions
    pre_ast = ast.parse(precondition_str, mode="eval").body
    precond = translator.translate_expr(pre_ast)
    # print(f"Precondition: {precond}")

    post_ast = ast.parse(postcondition_str, mode="eval").body
    postcond = translator.translate_expr(post_ast)
    # print(f"Postcondition: {postcond}")

    # Generate VCs
    vcgen = vc_generator.VCGenerator()
    computed_precond = vcgen.generate(program_ir, postcond)
    # print(f"Computed Precondition: {computed_precond}")

    # ⚠️ ADD THIS: Check initial condition
    vc_initial = ir.LogicOp(precond, "implies", computed_precond)
    all_vcs = [("Initial condition", vc_initial)] + vcgen.get_vcs()

    # print(f"\nTotal VCs to check: {len(all_vcs)}")

    z3_vars = {}
    solver = z3.Solver()
    all_valid = True

    for i, (name, vc) in enumerate(all_vcs):
        # print(f"\n[VC {i+1}] {name}")
        # print(f"  IR: {vc}")

        z3_vc = ir_to_z3(vc, z3_vars)
        # print(f"  Z3: {z3_vc}")

        # Check if VC is valid (always true)
        solver.push()
        solver.add(z3.Not(z3_vc))  # Try to find counterexample

        result = solver.check()
        if result != z3.unsat:
            print(f"Unverified")
            print(f"  Counterexample: {solver.model()}")
            all_valid = False
            break
        else:
            # print(f"  ✓ VALID")
            pass

        solver.pop()

    # print("\n" + "=" * 60)
    if all_valid:
        print("Verified")

    return all_valid
