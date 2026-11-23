"""Reject Lean admissions in source while ignoring nested comments and strings.

This is a conservative lexical check, not a replacement for the Lean compiler
or a kernel-level audit of imported axioms.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PROHIBITED = re.compile(r"(?<![\w'])\b(sorry|admit|axiom|sorryAx)\b")


def erase_comments_and_strings(text: str) -> str:
    """Preserve offsets/newlines while ignoring nested Lean block comments."""
    output = list(text)
    i = 0
    block_depth = 0
    in_string = False
    in_line_comment = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
            else:
                output[i] = " "
            i += 1
        elif block_depth:
            if ch == "/" and nxt == "-":
                output[i] = output[i + 1] = " "
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                output[i] = output[i + 1] = " "
                block_depth -= 1
                i += 2
            else:
                if ch != "\n":
                    output[i] = " "
                i += 1
        elif in_string:
            if ch == "\\" and nxt:
                output[i] = " "
                if nxt != "\n":
                    output[i + 1] = " "
                i += 2
            elif ch == '"':
                output[i] = " "
                in_string = False
                i += 1
            else:
                if ch != "\n":
                    output[i] = " "
                i += 1
        elif ch == "-" and nxt == "-":
            output[i] = output[i + 1] = " "
            in_line_comment = True
            i += 2
        elif ch == "/" and nxt == "-":
            output[i] = output[i + 1] = " "
            block_depth = 1
            i += 2
        elif ch == '"':
            output[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    return "".join(output)


def main() -> int:
    files = [Path("W5.lean"), *sorted(Path("W5").rglob("*.lean"))]
    failures = []
    for file in files:
        if not file.is_file():
            continue
        cleaned = erase_comments_and_strings(file.read_text(encoding="utf-8"))
        for match in PROHIBITED.finditer(cleaned):
            lineno = cleaned.count("\n", 0, match.start()) + 1
            failures.append(f"{file}:{lineno}: forbidden Lean token {match.group(1)}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"PASS: checked {len(files)} Lean files; no admission tokens in Lean source")
    return 0


if __name__ == "__main__":
    sys.exit(main())
