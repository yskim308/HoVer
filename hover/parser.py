import tokenize
from io import BytesIO


def extract_annotations(source_code):
    annotations = {
        "pre": None,
        "post": None,
        "invariants": {},  # Map line_number -> invariant_string
    }

    tokens = tokenize.tokenize(BytesIO(source_code.encode("utf-8")).readline)

    for tok in tokens:
        if tok.type == tokenize.COMMENT:
            content = tok.string.strip()
            # Check for the magic headers
            if content.startswith("#pre:"):
                annotations["pre"] = content[5:].strip()
            elif content.startswith("#post:"):
                annotations["post"] = content[6:].strip()
            elif content.startswith("#inv:"):
                # Map the invariant to the line number so we can link it to a While loop later
                # tok.start is a tuple (row, col)
                line_no = tok.start[0]
                annotations["invariants"][line_no] = content[5:].strip()

    return annotations
