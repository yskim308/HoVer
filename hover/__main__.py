# When grading, the contents of this file will be interpreted.
#
# You are free to add other files to organize your code, but keep in mind that
# the entrypoint is *this file*.

from pathlib import Path

from hover import ast_to_ir, parser

print("Hello, world!")

file_path = Path("examples/sample/loop_invariant.py")
source_code = file_path.read_text()
annotations = parser.extract_annotations(source_code)

translator = ast_to_ir.ASTTranslator(source_code, annotations)
statements = translator.parse()

print(statements)
