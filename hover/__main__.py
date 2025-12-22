# When grading, the contents of this file will be interpreted.
#
# You are free to add other files to organize your code, but keep in mind that
# the entrypoint is *this file*.

import sys
from pathlib import Path

from hover import parser

from .verify import verify_program

if len(sys.argv) < 2:
    print("Usage: python -m hover <path_to_file.py>")
file_path = Path(sys.argv[1])
source_code = file_path.read_text()
annotations = parser.extract_annotations(source_code)

verify_program(source_code, annotations, annotations["pre"], annotations["post"])
