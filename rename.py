import argparse
import random
import string
import re
import sys
from pathlib import Path

my_boundary = r"[\s():\.,;\[\]]"


def fresh_valid_name(old_name: str, existing: set[str]) -> str:
    """
    Generate a fresh Coq-valid identifier that does not collide with existing names.
    Coq identifiers start with a letter and may contain letters, digits, underscores, and apostrophes.
    """
    i = random.randint(6, 16)
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


def mask_comments_and_strings_modules(text: str):
    comment_pattern = re.compile(r"\(\*.*?\*\)", re.DOTALL)
    # string_pattern = re.compile(r'(?<!(Warnings|Notation)\s)"(?:\\.|[^"\\])*"')
    module_pattern = re.compile(r"Module\s+([\w0-9']+).((\n|.)+)End \1\.", re.MULTILINE)

    comments = []

    def _mask_comment(m):
        comments.append(m.group(0))
        return f"__COMMENT_{len(comments)-1}__"

    strings = []

    def _mask_string(m):
        strings.append(m.group(0))
        return f"__STRING_{len(strings)-1}__"

    def _mask_module(m):
        # Mask the module name
        return f""

    text_masked = comment_pattern.sub(_mask_comment, text)
    # text_masked = string_pattern.sub(_mask_string, text_no_comments)
    text_masked = module_pattern.sub(_mask_module, text_masked)
    return text_masked, comments, strings


def restore_strings(
    # NOTE: We don't restore comments because they may reveal too much underlying structure
    text: str,
    strings: list[str],
) -> str:
    def _restore_string(m):
        return strings[int(m.group(1))]

    text = re.sub(r"__STRING_(\d+)__", _restore_string, text)
    return text


def blast_away_comments(text: str, comments: list[str]) -> str:
    # Deletes comments but keeps the structure of the code
    def _blast_comment(m):
        # We can use the comment text to determine the length of the comment
        # and replace it with a space of the same length
        return " " * len(comments[int(m.group(1))])

    text = re.sub(r"__COMMENT_(\d+)__", _blast_comment, text)
    return text


def collect_ind_defs(text: str) -> dict[str, str]:
    defs = {}
    # Find the inductive definitions
    pattern = re.compile(
        r"^\s*Inductive\s+([A-Za-z][A-Za-z0-9_']*)" + my_boundary + r"(.*?\.)",
        re.MULTILINE | re.DOTALL,
    )
    for m in pattern.finditer(text):
        name = m.group(1)
        print(name)
        print(m.groupdict())
        FORBIDDEN = ["com", "com_aux"]
        if name in FORBIDDEN:
            continue
        defs[name] = fresh_valid_name(name, set(defs.keys()))
        body = m.group(2)
        # Find the constructors
        for c in re.finditer(r"\|\s*([A-Za-z][A-Za-z0-9_']*)" + my_boundary, body):
            defs[c.group(1)] = fresh_valid_name(c.group(1), set(defs.keys()))
        # find things that used this inductive name in form `IH<m>number`
        test_pat = re.compile(r"\bIH" + name + r"(\d+)\b")
        for c in re.finditer(test_pat, text):
            defs[c.group(0)] = "IH" + defs[name] + c.group(1)
        # find things that used the inductive principle manually
        test_pat = re.compile(r"\b" + name + r"_ind\b")
        for c in re.finditer(test_pat, text):
            defs[c.group(0)] = defs[name] + "_ind"
    return defs


def collect_other_defs(text: str, previous_defs: dict[str, str]) -> dict[str, str]:
    """Collect definitions from Fixpoint, Definition, Theorem, Lemma."""
    # Pattern to find definitions like 'Fixpoint name ...', 'Definition name ...', etc.
    # It captures the identifier immediately following the keyword.
    pattern = re.compile(
        r"^\s*(?:Fixpoint|Definition|Theorem|Lemma)\s+([A-Za-z][A-Za-z0-9_']*)"
        + my_boundary,
        re.MULTILINE,
    )
    FORBIDDEN = ["f_equal", "string", "app_nil_r"]
    for m in pattern.finditer(text):
        if m.group(1) in FORBIDDEN:
            continue
        previous_defs[m.group(1)] = fresh_valid_name(
            m.group(1), set(previous_defs.keys())
        )
    return previous_defs


def apply_renames(text: str, rename_map: dict[str, str]) -> str:
    # Sort by length desc to avoid partial overlaps
    for old in sorted(rename_map, key=len, reverse=True):
        new = rename_map[old]
        text = re.sub(rf"\b{re.escape(old)}({my_boundary})", new + r"\1", text)
    return text


def rename(filetext: str) -> tuple[str, str, dict[str, str]]:
    masked, comments, strings = mask_comments_and_strings_modules(filetext)

    # Collect all definitions
    ind_defs = collect_ind_defs(masked)
    print(ind_defs)
    all_renames = collect_other_defs(masked, ind_defs)
    print(all_renames)

    if not all_renames:
        print("No definitions found for renaming.", file=sys.stderr)
        sys.exit(1)

    final_orig = blast_away_comments(masked, comments)
    rewritten = apply_renames(masked, all_renames)
    # final = restore_strings(rewritten, strings)
    final_mod = blast_away_comments(rewritten, comments)
    return final_orig, final_mod, all_renames


def main():
    parser = argparse.ArgumentParser(
        description="Coq inductive/constructor renaming tool"
    )
    parser.add_argument("input", type=Path, help="Input Coq .v file")
    parser.add_argument("output-orig", type=Path, help="Output Coq .v file")
    parser.add_argument("output-mod", type=Path, help="Output Coq .v file")
    args = parser.parse_args()

    text = args.input.read_text(encoding="utf-8")
    final_orig, final_mod, rename_map = rename(text)
    args.output.write_text(final_orig, encoding="utf-8")
    args.output.write_text(final_mod, encoding="utf-8")
    print(f"Renamed {len(rename_map)} identifiers.")


if __name__ == "__main__":
    main()
