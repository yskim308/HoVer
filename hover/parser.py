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
            raw_comment = tok.string.strip()

            parts = raw_comment.split(":", 1)

            if len(parts) < 2:
                continue

            key = parts[0].replace("#", "", 1).strip().lower()

            value = parts[1].strip()
            if key == "pre":
                if pre_found:
                    raise MagicCommentError("duplicate pre at line {}", tok.start[0])
                annotations["pre"] = value
                pre_found = True

            elif key == "post":
                if post_found:
                    raise MagicCommentError("duplicate post at line {}", tok.start[0])
                annotations["post"] = value

            elif key == "inv":
                if inv_found:
                    raise MagicCommentError(
                        "duplicate inv found at line {}", tok.start[0]
                    )
                line_no = tok.start[0]
                annotations["invariants"][line_no] = value

    return annotations
