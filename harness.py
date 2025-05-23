# harness.py
# Harness objectives:
# 1. Generation of prompts for distribution to LLMs
## -- Locate modified files [complete]
## -- Run gather theorems on all modified files [complete]
## -- Create prompts based on context/theorem pairs [complete]
# 2. Automated distribution of prompts
## -- Talk to Ollama

import csv
from dataclasses import dataclass
import os
import re
import argparse
from pathlib import Path
import sys

import gather_theorems
from ollama import Client, GenerateResponse

from mutator import check_coqc, mutate_coq_files


@dataclass
class Theorem:
    name: str
    context: str
    statement: str
    file: str
    prompt: str
    response: str | None = None
    cleaned_response: str | None = None
    compiles: bool = False
    failed: bool = False


def flatten(s: str) -> str:
    """
    Flattens a string by removing newlines and extra spaces.
    """
    return re.sub(r"\s+", " ", s).strip()


proof_blob_regex = re.compile(r"Proof\.(.*?)(Qed\.|Defined\.|```)", re.DOTALL)


def extract_proof_from_response(theorem_name: str, text: str) -> str | None:
    # mask all the <think>...</think> out
    text = re.sub(r"<think>.*?</think>", "", text, flags=re.DOTALL)

    theorem_match = re.search(
        rf"(Theorem|Lemma|Corollary|Fact|Proposition|Example)\s+{theorem_name}", text
    )
    if theorem_match is None:
        # Case 2: theorem name not found — check for exactly one proof segment
        matches = re.findall(proof_blob_regex, text)
        if len(matches) == 1:
            match = matches[0]
            if match[1] == "```":
                # If the proof ends with a code block, we need to just end it with a Qed.
                return "Proof." + match[0] + "Qed."
            return "Proof." + match[0] + match[1]
        else:
            return None  # Either no matches or ambiguous multiple matches
    else:
        theorem_index = theorem_match.start()
        # Case 1: theorem name found — search after it
        sliced_text = text[theorem_index:]
        match = re.search(proof_blob_regex, sliced_text)
        if match:
            if match.group(2) == "```":
                # If the proof ends with a code block, we need to just end it with a Qed.
                return "Proof." + match.group(1) + "Qed."
            return "Proof." + match.group(1) + match.group(2)
        else:
            return None  # No proof segment after theorem name


def recombine_file(prompt_dict: Theorem) -> str:
    # Recombine the original file with the response
    return f"""
{prompt_dict.context}
{prompt_dict.statement}
{prompt_dict.cleaned_response}
"""


def check_coq_compile_temp(
    folder_path: str,
    file_contents: str,
    file_name: str | None = None,
    debug: bool = False,
) -> bool:
    # Write the contents to a temporary file
    tempfile = Path(folder_path).joinpath(
        Path("tempfile.v" if file_name is None else file_name)
    )
    tempfile.write_text(file_contents, encoding="utf-8")
    # Check if the file compiles
    result = check_coqc(tempfile)
    # Clean up the temporary file
    if not debug:
        tempfile.unlink()
    return result


# Writing a prompt based on the arguments
def mad_lib_prompt(name, statement, context):
    return f"""
Prove the following theorem {name} in the Coq proof language.
The context for the proof is as follows:
```coq
{context}
```
The statement of the theorem to be proved is as follows:
```coq
{statement}
```
Supply only the complete proof body in the Coq proof language following the template:
```coq
Proof.
    <proof body here>
Qed.
```
"""


# For each modified file,
# generate prompts for all gathered theorems and return all in a list.
def write_prompts_per_modified_file(path) -> list[Theorem]:
    prompt_dict: dict[str, str | bool] = {}
    # Gather context/theorem pairs using gather_theorems.collect_theorems()
    text = path.read_text(encoding="utf-8")
    ct_pairs = gather_theorems.collect_theorems(text)
    theorem_list = []
    for elem in ct_pairs:
        name = elem.get("name")
        context = elem.get("context")
        statement = elem.get("statement")
        theorem_list.append(
            Theorem(
                name, context, statement, path, mad_lib_prompt(name, statement, context)
            )
        )
    return theorem_list


# Collect all modified files
def gather_modified_files(path):
    # make an OS request to files in a certain directory
    # look for all files suffixed with '_modified' that are .v files

    potential_filenames = os.listdir(path)

    good_files: list[tuple[str, str]] = []

    for filename in potential_filenames:
        match = re.search(r"(.+)_modified.v$", filename)
        # pull out the original filename and the moidified filename
        if match:
            original_filename = match.group(1) + "_orig.v"
            modified_filename = filename
            good_files.append((original_filename, modified_filename))

    # The folder exists but contains no candidates
    if len(good_files) == 0:
        raise RuntimeError("Error: folder exists but contains no mutated files")

    return good_files


# Write all prompts for ollama and return as a list.
def write_all_prompts(path) -> list[tuple[Theorem, Theorem]]:

    all_prompts: list[tuple[Theorem, Theorem]] = []

    # Collect all files to scrape for theorems.
    mutated_filenames: list[tuple[str, str]] = gather_modified_files(path)

    # Write all prompts per file
    for orig_file, mut_file in mutated_filenames:
        orig_prompt = write_prompts_per_modified_file(path / orig_file)
        mut_prompt = write_prompts_per_modified_file(path / mut_file)
        if len(orig_prompt) != len(mut_prompt):
            raise RuntimeError(
                f"Error: {orig_file} and {mut_file} have different number of theorems."
            )
        all_prompts += zip(orig_prompt, mut_prompt)
        print("Number of prompts for file", orig_file, ":", len(orig_prompt))

    return all_prompts


## UNUSED, UNSURE IF THIS WORKS
## Formatting at https://github.com/ollama/ollama-python, Custom client
# Sends a request to our local instance of ollama with our prompt.
# Returns the response of the prompt.
def send_ollama_request(
    client: Client, model_name: str, prompt: str
) -> GenerateResponse:
    response = client.generate(
        model=model_name,
        prompt=prompt,
    )
    return response


def main():
    # Argument parser
    parser = argparse.ArgumentParser(
        description="Create prompts from mutated Coq .v files to serve to target LLM."
    )
    parser.add_argument(
        "input_dir",
        type=Path,
        help="Directory containing the input Coq .v files.",
    )

    args = parser.parse_args()

    # First, mutate the Coq files
    mut_results = mutate_coq_files(args.input_dir)

    # Write all prompts for ollama.
    MODELS = [
        "llama3.1",
        # "deepseek-r1:32b",
        # "mixtral:8x7b",
        "phi4",
    ]
    # MODELS = ["gemma3:1b", "llama3"]
    overall_prompts: dict[str, list[tuple[Theorem, Theorem]]] = {
        model_key: write_all_prompts(args.input_dir) for model_key in MODELS
    }
    client = Client(host="http://localhost:11434")

    csv_output = Path("results.csv")
    with csv_output.open("w", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            (
                "File",
                "Model",
                "Orig Theorem Name",
                "Mut Theorem Name",
                "Orig Statement",
                "Mut Statement",
                "Original Compiles",
                "Original Failed",
                "Mutated Compiles",
                "Mutated Failed",
            )
        )
        for model in MODELS:
            client.pull(model)
            print(f"Running model {model}...")
            prompts = overall_prompts[model]
            for orig_prompt, mut_prompt in prompts:
                print("\n--- Original Prompt ---")
                print(orig_prompt.statement)
                print("\n--- End of Original Prompt ---\n\n")
                # Send the prompt to ollama and get the response
                orig_response = send_ollama_request(client, model, orig_prompt.prompt)
                print("\n--- Orig Response ---")
                resp_content = orig_response.response
                if resp_content:
                    print(resp_content)
                    orig_prompt.response = resp_content
                else:
                    print("NO ORIG REPONSE CONTENT RECEIVED!!!")
                print("\n--- End of Orig Response ---\n\n")

                print("\n--- Mutated Prompt ---")
                print(mut_prompt.statement)
                print("\n--- End of Mutated Prompt ---\n\n")
                # Send the prompt to ollama and get the response
                mut_response = send_ollama_request(client, model, mut_prompt.prompt)
                print("\n--- Mut Response ---")
                resp_content = mut_response.response
                if resp_content:
                    print(resp_content)
                    mut_prompt.response = resp_content
                else:
                    print("NO MUT REPONSE CONTENT RECEIVED!!!")
                print("\n--- End of Mut Response ---\n\n")

                # Now, see if we can run the files that are completed properly.
                # Check if the original file is valid
                if orig_prompt.response is None:
                    print("No response for original file.")
                    orig_prompt.failed = True
                else:
                    orig_cleaned = extract_proof_from_response(
                        orig_prompt.name, orig_prompt.response
                    )
                    if orig_cleaned is None:
                        print("No proof found in original response.")
                        orig_prompt.failed = True
                    orig_prompt.cleaned_response = orig_cleaned
                if mut_prompt.response is None:
                    print("No response for mutated file.")
                    mut_prompt.failed = True
                else:
                    mut_cleaned = extract_proof_from_response(
                        mut_prompt.name, mut_prompt.response
                    )
                    if mut_cleaned is None:
                        print("No proof found in mutated response.")
                        mut_prompt.failed = True
                    mut_prompt.cleaned_response = mut_cleaned
                # Recombine and check compilation
                new_orig_file = recombine_file(orig_prompt)
                new_mut_file = recombine_file(mut_prompt)
                # Now check each of the re-written files compiles in Coq
                orig_prompt.compiles = check_coq_compile_temp(
                    args.input_dir, new_orig_file
                )
                mut_prompt.compiles = check_coq_compile_temp(
                    args.input_dir, new_mut_file
                )

                # Now we can process our results.
                # We want a CSV file
                # file, theorem name, statement, orig_compiles, mut_compiles
                # Write to CSV
                writer.writerow(
                    (
                        orig_prompt.file,
                        model,
                        orig_prompt.name,
                        mut_prompt.name,
                        flatten(orig_prompt.statement),
                        flatten(mut_prompt.statement),
                        orig_prompt.compiles,
                        orig_prompt.failed,
                        mut_prompt.compiles,
                        mut_prompt.failed,
                    )
                )


if __name__ == "__main__":
    main()
