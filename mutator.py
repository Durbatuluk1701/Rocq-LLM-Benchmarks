"""
Steps:
1. Read from a directory all *.v files
2. For each file:
   2.0 Ensure that "coqc <file>" works
   2.1 Read the file
   2.2 Apply the "rename" function to the text
   2.3 Apply the "rewrite_theorems" function to the text (NOTE: This function is not defined, skipping)
   2.4 Write the modified text to a <name>_modified.v file
   2.5 Ensure that "coqc <name>_modified.v" works
   2.6 Add to a dictionary the name of the original file and the name of the modified file
3. Return the dictionary
"""

import argparse
import subprocess
import sys
from pathlib import Path
import rename


def check_coqc(filepath: Path) -> bool:
    """Runs coqc on the file and returns True if successful, False otherwise."""
    try:
        result = subprocess.run(
            ["coqc", str(filepath), "-Q", ".", "LF"],
            check=False,  # Don't raise exception on failure
            capture_output=True,
            text=True,
            timeout=60,  # Add a timeout to prevent hanging
        )
        if result.returncode == 0:
            print(f"Check successful: {filepath}", file=sys.stderr)
            return True
        else:
            print(f"Check failed for {filepath}:", file=sys.stderr)
            print(result.stderr, file=sys.stderr)
            return False
    except FileNotFoundError:
        print(
            "Error: 'coqc' command not found. Is Coq installed and in PATH?",
            file=sys.stderr,
        )
        return False
    except subprocess.TimeoutExpired:
        print(f"Check timed out for {filepath}", file=sys.stderr)
        return False
    except Exception as e:
        print(
            f"An unexpected error occurred during coqc check for {filepath}: {e}",
            file=sys.stderr,
        )
        return False


def mutate_coq_files(input_dir: Path) -> dict[str, str]:
    """
    Mutates Coq files in a directory according to the specified steps.
    """
    if not input_dir.is_dir():
        print(f"Error: Input path '{input_dir}' is not a directory.", file=sys.stderr)
        return {}

    mutated_files_map: dict[str, str] = {}

    for original_file in input_dir.glob("*.v"):
        if "_modified" in original_file.name:
            print(
                f"Skipping already modified file: {original_file.name}",
                file=sys.stderr,
            )
            continue
        print(f"\nProcessing file: {original_file.name}")

        # 2.0 Ensure that "coqc <file>" works
        if not check_coqc(original_file):
            print(
                f"Skipping {original_file.name} due to compilation errors.",
                file=sys.stderr,
            )
            continue

        # 2.1 Read the file
        try:
            original_text = original_file.read_text(encoding="utf-8")
        except Exception as e:
            print(f"Error reading file {original_file.name}: {e}", file=sys.stderr)
            continue

        # 2.2 Apply the "rename" function to the text
        try:
            final_orig, final_mod, rename_map = rename.rename(original_text)
            if not rename_map:
                print(
                    f"No definitions found to rename in {original_file.name}, skipping.",
                    file=sys.stderr,
                )
                continue
            print(f"Renamed {len(rename_map)} identifiers in {original_file.name}.")
        except Exception as e:
            print(
                f"Error applying rename to {original_file.name}: {e}", file=sys.stderr
            )
            continue

        # 2.3 Apply the "rewrite_theorems" function (Skipped as noted in docstring)
        # modified_text = rewrite_theorems(modified_text) # Placeholder

        # 2.4 Write the modified text to a <name>_modified.v file
        modified_filename = original_file.stem + "_modified.v"
        orig_filename = original_file.stem + "_orig.v"
        modified_filepath = original_file.with_name(modified_filename)
        orig_filepath = original_file.with_name(orig_filename)
        try:
            orig_filepath.write_text(final_orig, encoding="utf-8")
            modified_filepath.write_text(final_mod, encoding="utf-8")
            print(f"Written modified file: {modified_filepath.name}")
        except Exception as e:
            print(
                f"Error writing modified file {modified_filepath.name}: {e}",
                file=sys.stderr,
            )
            continue  # Skip trying to compile if writing failed

        # 2.5 Ensure that "coqc <name>_modified.v" works
        if check_coqc(modified_filepath):
            # 2.6 Add to a dictionary
            mutated_files_map[str(original_file)] = str(modified_filepath)
            print(
                f"Successfully processed and verified: {original_file.name} -> {modified_filepath.name}"
            )
        else:
            print(
                f"Modified file {modified_filepath.name} failed compilation check. Discarding.",
                file=sys.stderr,
            )
            # Clean up the failed modified file
            try:
                sys.exit(1)
                # modified_filepath.unlink()
            except OSError as e:
                print(
                    f"Error removing failed file {modified_filepath.name}: {e}",
                    file=sys.stderr,
                )

    # 3. Return the dictionary
    return mutated_files_map


def main():
    parser = argparse.ArgumentParser(
        description="Mutate Coq *.v files in a directory by renaming definitions."
    )
    parser.add_argument(
        "input_dir",
        type=Path,
        help="Directory containing the input Coq .v files.",
    )
    # Optional: Add argument for output directory if needed later
    # parser.add_argument(
    #     "-o", "--output_dir", type=Path, default=None,
    #     help="Directory to store modified files (defaults to input directory)."
    # )

    args = parser.parse_args()

    # if args.output_dir:
    #     args.output_dir.mkdir(parents=True, exist_ok=True)
    # output_dir = args.output_dir or args.input_dir # Decide where to put files

    results = mutate_coq_files(args.input_dir)

    print("\n--- Mutation Summary ---")
    if results:
        print("Successfully mutated files:")
        for original, modified in results.items():
            print(f"  {Path(original).name} -> {Path(modified).name}")
    else:
        print("No files were successfully mutated.")


if __name__ == "__main__":
    main()
