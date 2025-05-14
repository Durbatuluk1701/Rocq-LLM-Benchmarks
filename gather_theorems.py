import argparse
import json
import re
from pathlib import Path


def collect_theorems(text: str):
    """
    Extract each Theorem/Lemma/Fact statement (up to, but not including, the 'Proof.' line)
    along with the preceding context (everything before the theorem declaration).
    Returns a list of dicts: {type, name, statement, context}.
    """
    lines = text.splitlines(keepends=True)
    results = []
    i = 0
    while i < len(lines):
        line = lines[i]
        # Detect the start of a theorem/lemma/fact
        m = re.match(r"\s*(Theorem|Lemma|Fact)\s+([A-Za-z][A-Za-z0-9_']*)", line)
        if m:
            decl_type = m.group(1)
            name = m.group(2)
            # Accumulate all lines of the statement until the 'Proof.' line
            stmt_lines = [line]
            j = i + 1
            while j < len(lines) and not re.match(r"\s*Proof\.", lines[j]):
                stmt_lines.append(lines[j])
                j += 1
            # Combine statement and ensure it ends with a period
            statement = "".join(stmt_lines).strip()
            if not statement.endswith("."):
                statement += "."
            # Context is everything before this theorem declaration
            context = "".join(lines[:i]).rstrip()
            results.append(
                {
                    "type": decl_type,
                    "name": name,
                    "statement": statement,
                    "context": context,
                }
            )
            # Skip past the 'Proof.' line
            i = j + 1
        else:
            i += 1
    return results


def main():
    parser = argparse.ArgumentParser(
        description="Gather theorem statements and their contexts from a Coq file"
    )
    parser.add_argument("--input", type=Path, help="Input Coq .v file")
    parser.add_argument(
        "--input_dir", type=Path, help="Input Directory of Coq .v files"
    )
    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        help="Optional JSON output file; defaults to stdout",
    )
    args = parser.parse_args()

    if args.input and args.input_dir:
        raise ValueError(
            "Please provide either an input file or an input directory, not both."
        )

    overall_theorems = []
    if args.input_dir:
        # get all .v files in the directory
        files = list(args.input_dir.glob("**/*.v"))
        for file in files:
            print(f"Processing {file}")
            text = file.read_text(encoding="utf-8")
            overall_theorems.extend(collect_theorems(text))
    else:
        text = args.input.read_text(encoding="utf-8")
        theorems = collect_theorems(text)

    output = {"file": str(args.input), "theorems": overall_theorems}

    if args.output:
        args.output.write_text(json.dumps(output, indent=2), encoding="utf-8")
        print(f"Wrote {len(overall_theorems)} theorems to {args.output}")
    else:
        print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
