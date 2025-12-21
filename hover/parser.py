import tokenize
from io import BytesIO


class MagicCommentError(Exception):
    pass


def extract_annotations(source_code):
    annotations = {
        "pre": None,
        "post": None,
        "invariants": {},  # Map line_number -> invariant_string
    }

    tokens = tokenize.tokenize(BytesIO(source_code.encode("utf-8")).readline)

    pre_found, post_found, inv_found = False, False, False
    for tok in tokens:
        if tok.type == tokenize.COMMENT:
            content = tok.string.strip().replace(" ", "")
            if content.startswith("#pre:"):
                if pre_found:
                    raise MagicCommentError("duplicate pre at line {}", tok.start[0])
                annotations["pre"] = content[5:].strip()
                pre_found = True

            elif content.startswith("#post:"):
                if post_found:
                    raise MagicCommentError("duplicate post at line {}", tok.start[0])
                annotations["post"] = content[6:].strip()

            elif content.startswith("#inv:"):
                if inv_found:
                    raise MagicCommentError(
                        "duplicate inv found at line {}", tok.start[0]
                    )
                line_no = tok.start[0]
                annotations["invariants"][line_no] = content[5:].strip()

    return annotations
