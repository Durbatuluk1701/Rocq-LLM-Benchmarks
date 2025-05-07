# harness.py
# Harness objectives:
# 1. Generation of prompts for distribution to LLMs
## -- Locate modified files [complete]
## -- Run gather theorems on all modified files [complete]
## -- Create prompts based on context/theorem pairs [complete]
# 2. Automated distribution of prompts
## -- Talk to Ollama

import os
import re
import argparse
from pathlib import Path

import gather_theorems
from ollama import ChatResponse, Client

from mutator import check_coqc, mutate_coq_files


def clean_response(response: str) -> str:
    return NotImplemented


def recombine_file(prompt_dict: dict[str, str]) -> str:
    # Recombine the original file with the response
    return f"""
{prompt_dict["context"]}
{prompt_dict["statement"]}
{prompt_dict["cleaned_response"]}
"""


def check_coq_compile_temp(file_contents: str) -> str:
    # Write the contents to a temporary file
    tempfile = Path("tempfile.v")
    tempfile.write_text(file_contents, encoding="utf-8")
    # Check if the file compiles
    result = check_coqc(tempfile)
    # Clean up the temporary file
    tempfile.unlink()
    if result:
        return "True"
    else:
        return "False"


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
Supply only the complete proof body in the Coq proof language and no extra information.
"""


# For each modified file,
# generate prompts for all gathered theorems and return all in a list.
def write_prompts_per_modified_file(path) -> dict[str, str]:
    prompt_dict: dict[str, str] = {}
    # Gather context/theorem pairs using gather_theorems.collect_theorems()
    text = path.read_text(encoding="utf-8")
    ct_pairs = gather_theorems.collect_theorems(text)
    for elem in ct_pairs:
        name = elem.get("name")
        context = elem.get("context")
        statement = elem.get("statement")
        prompt_dict["theorem_name"] = name
        prompt_dict["context"] = context
        prompt_dict["statement"] = statement
        prompt_dict["file"] = path
        # Generate the prompt string
        prompt_dict["prompt"] = mad_lib_prompt(name, statement, context)
    return prompt_dict


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
            original_filename = match.group(1) + ".v"
            modified_filename = filename
            good_files.append((original_filename, modified_filename))

    # The folder exists but contains no candidates
    if len(good_files) == 0:
        raise RuntimeError("Error: folder exists but contains no mutated files")

    return good_files


# Write all prompts for ollama and return as a list.
def write_all_prompts(path) -> list[tuple[dict[str, str], dict[str, str]]]:

    all_prompts: list[tuple[dict[str, str], dict[str, str]]] = []

    # Collect all files to scrape for theorems.
    mutated_filenames: list[tuple[str, str]] = gather_modified_files(path)

    # Write all prompts per file
    for orig_file, mut_file in mutated_filenames:
        orig_prompt = write_prompts_per_modified_file(path / orig_file)
        mut_prompt = write_prompts_per_modified_file(path / mut_file)
        all_prompts.append((orig_prompt, mut_prompt))

    return all_prompts


## UNUSED, UNSURE IF THIS WORKS
## Formatting at https://github.com/ollama/ollama-python, Custom client
# Sends a request to our local instance of ollama with our prompt.
# Returns the response of the prompt.
def send_ollama_request(model_name: str, prompt: str) -> ChatResponse:
    client = Client(
        host="http://localhost:11434", headers={"x-some-header": "some-value"}
    )
    client.pull(model_name)
    response = client.chat(
        model=model_name,
        messages=[
            {
                "role": "user",
                "content": prompt,
            },
        ],
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
    prompts: list[tuple[dict[str, str], dict[str, str]]] = write_all_prompts(
        args.input_dir
    )

    MODEL_NAME = "llama3"
    for orig_prompt, mut_prompt in prompts:
        print("\n--- Original Prompt ---")
        print(orig_prompt["prompt"])
        print("\n--- End of Original Prompt ---\n\n")
        # Send the prompt to ollama and get the response
        orig_response = send_ollama_request(MODEL_NAME, orig_prompt["prompt"])
        print("\n--- Orig Response ---")
        resp_content = orig_response.message.content
        if resp_content:
            print(resp_content)
            orig_prompt["response"] = resp_content
        else:
            print("NO ORIG REPONSE CONTENT RECEIVED!!!")
        print("\n--- End of Orig Response ---\n\n")

        print("\n--- Mutated Prompt ---")
        print(mut_prompt["prompt"])
        print("\n--- End of Mutated Prompt ---\n\n")
        # Send the prompt to ollama and get the response
        mut_response = send_ollama_request(MODEL_NAME, mut_prompt["prompt"])
        print("\n--- mut Response ---")
        resp_content = mut_response.message.content
        if resp_content:
            print(resp_content)
            mut_prompt["response"] = resp_content
        else:
            print("NO mut REPONSE CONTENT RECEIVED!!!")
        print("\n--- End of mut Response ---\n\n")

    """
    At this point, we should have the dictionaries all contain:
    {
        "theorem_name": <name>,
        "context": <context>,
        "statement": <statement>,
        "file": <file>,
        "prompt": <prompt>,
        "response": <response>
    }
    """
    # Now, see if we can run the files that are completed properly.

    for orig_dict, mut_dict in prompts:
        # Check if the original file is valid
        orig_dict["cleaned_response"] = clean_response(orig_dict["response"])
        mut_dict["cleaned_response"] = clean_response(mut_dict["response"])
        # Recombine and check compilation
        new_orig_file = recombine_file(orig_dict)
        new_mut_file = recombine_file(mut_dict)
        # Now check each of the re-written files compiles in Coq
        orig_dict["works"] = check_coq_compile_temp(new_orig_file)
        mut_dict["works"] = check_coq_compile_temp(new_mut_file)

    """
    print("\n--- Harness s ---")
    if results:
        print("Successfully mutated files:")
        for original, modified in results.items():
            print(f"  {Path(original).name} -> {Path(modified).name}")
    else:
        print("No files were successfully mutated.")
    """


if __name__ == "__main__":
    main()
