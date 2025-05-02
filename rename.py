import argparse
import json
import random
import string
import re
import sys
from pathlib import Path


def fresh_valid_name(old_name: str, existing: set[str]) -> str:
    """
    Generate a fresh Coq-valid identifier that does not collide with existing names.
    Coq identifiers start with a letter and may contain letters, digits, underscores, and apostrophes.
    """
    i = 8
    while True:
        start = "".join(random.choices(string.ascii_lowercase + string.ascii_uppercase))
        rest = "".join(
            random.choices(
                string.ascii_lowercase
                + string.ascii_uppercase
                + string.digits
                + "'"
                + "_",
                k=i,
            )
        )
        new_name = start + rest
        if new_name not in existing:
            return new_name
        i += 1


def mask_comments_and_strings(text: str):
    comment_pattern = re.compile(r"\(\*.*?\*\)", re.DOTALL)
    string_pattern = re.compile(r'"(?:\\.|[^"\\])*"')

    comments = []

    def _mask_comment(m):
        comments.append(m.group(0))
        return f"__COMMENT_{len(comments)-1}__"

    strings = []

    def _mask_string(m):
        strings.append(m.group(0))
        return f"__STRING_{len(strings)-1}__"

    text_no_comments = comment_pattern.sub(_mask_comment, text)
    text_masked = string_pattern.sub(_mask_string, text_no_comments)
    return text_masked, comments, strings


def restore_comments_and_strings(
    text: str, comments: list[str], strings: list[str]
) -> str:
    def _restore_comment(m):
        return comments[int(m.group(1))]

    def _restore_string(m):
        return strings[int(m.group(1))]

    text = re.sub(r"__COMMENT_(\d+)__", _restore_comment, text)
    text = re.sub(r"__STRING_(\d+)__", _restore_string, text)
    return text


def collect_defs(text: str) -> set[str]:
    defs = set()
    # Find the inductive definitions
    pattern = re.compile(
        r"^\s*Inductive\s+([A-Za-z][A-Za-z0-9_']*)\b(.*?\.)", re.MULTILINE | re.DOTALL
    )
    for m in pattern.finditer(text):
        name = m.group(1)
        defs.add(name)
        body = m.group(2)
        # Find the constructors
        for c in re.finditer(r"\|\s*([A-Za-z][A-Za-z0-9_']*)\b", body):
            defs.add(c.group(1))
    return defs


def apply_renames(text: str, rename_map: dict[str, str]) -> str:
    # Sort by length desc to avoid partial overlaps
    for old in sorted(rename_map, key=len, reverse=True):
        new = rename_map[old]
        text = re.sub(rf"\b{re.escape(old)}\b", new, text)
    return text


def main():
    parser = argparse.ArgumentParser(
        description="Coq inductive/constructor renaming tool"
    )
    parser.add_argument("input", type=Path, help="Input Coq .v file")
    parser.add_argument("output", type=Path, help="Output Coq .v file")
    parser.add_argument(
        "--mapping",
        type=Path,
        help="Optional JSON file with { old_name: new_name } mapping",
    )
    args = parser.parse_args()

    text = args.input.read_text(encoding="utf-8")
    masked, comments, strings = mask_comments_and_strings(text)

    defs = collect_defs(masked)
    rename_map: dict[str, str] = {}

    user_map = {}
    if args.mapping:
        user_map = json.loads(args.mapping.read_text(encoding="utf-8"))

    # Build rename_map
    for name in defs:
        if name in user_map:
            rename_map[name] = user_map[name]
        else:
            # generate fresh name
            rename_map[name] = fresh_valid_name(name, defs | set(user_map.values()))

    if not rename_map:
        print("No inductives or constructors found for renaming.", file=sys.stderr)
        sys.exit(1)

    rewritten = apply_renames(masked, rename_map)
    final = restore_comments_and_strings(rewritten, comments, strings)
    args.output.write_text(final, encoding="utf-8")
    print(f"Renamed {len(rename_map)} identifiers.")


if __name__ == "__main__":
    main()
