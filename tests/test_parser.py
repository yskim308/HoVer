from pathlib import Path

import pytest

from hover import parser


def test_simple_assignment_parsing():
    file_path = Path("examples/sample/simple_assignment.py")
    source_code = file_path.read_text()
    annotations = parser.extract_annotations(source_code)
    assert annotations["pre"] == "x >= 0"
    assert annotations["post"] == "y == x + 1"


def test_loop_invariant_parsing():
    file_path = Path("examples/sample/loop_invariant.py")
    source_code = file_path.read_text()
    annotations = parser.extract_annotations(source_code)
    assert annotations["pre"] == "n >= 0"
    assert annotations["post"] == "2 * s == n * (n + 1)"
    assert annotations["invariants"] == {6: "0 <= i <= n and 2 * s == i * (i + 1)"}
