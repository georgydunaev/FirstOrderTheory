import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]


def read(relpath: str) -> str:
    return (ROOT / relpath).read_text(encoding="utf-8", errors="replace")


def strip_comments(text: str):
    """Replace every Coq comment (nested ``(* ... *)``) by blanks.

    Returns ``(stripped, final_depth, min_depth)``.  Newlines are preserved so
    that line numbers stay meaningful; anything inside a comment becomes a
    space.  Raises AssertionError on negative (unbalanced) nesting.
    """
    out = []
    depth = 0
    min_depth = 0
    i = 0
    n = len(text)
    while i < n:
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if two == "*)":
            depth -= 1
            if depth < min_depth:
                min_depth = depth
            out.append("  ")
            i += 2
            continue
        ch = text[i]
        out.append(ch if depth == 0 else (" " if ch != "\n" else "\n"))
        i += 1
    assert depth == 0, f"Unbalanced comments: depth={depth}"
    return "".join(out), depth, min_depth
