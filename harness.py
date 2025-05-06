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
from ollama import Client
import sys

# Writing a prompt based on the arguments
def mad_lib_prompt(name, statement, context):
    return(
    f"Prove the following theorem {name} in the Coq proof automation language.\n"
    +\
    "The context for the proof is as follows:\n\n"
    +\
    f"{context}\n\n"
    +\
    "The statement for the proof is as follows:\n\n"
    +\
    f"{statement}\n\n"
    +\
    "Supply the complete proof and only the proof in your response.\n"
    )

# For each modified file,
# generate prompts for all gathered theorems and return all in a list.
def write_prompts_per_modified_file(path):
    prompt_strings = []
    # Gather context/theorem pairs using gather_theorems.collect_theorems()
    text = path.read_text(encoding="utf-8")
    ct_pairs = gather_theorems.collect_theorems(text)
    for elem in ct_pairs:
        name = elem.get("name")
        context = elem.get("context")
        statement = elem.get("statement")
        prompt_strings.append(mad_lib_prompt(name, context, statement))
    return prompt_strings

# Collect all modified files
def gather_modified_files(path): 
    # make an OS request to files in a certain directory
    # look for all files suffixed with '_modified' that are .v files
                
    potential_filenames = os.listdir(path)
                
    mutated_filenames = []

    for filename in potential_filenames:
        if(re.search(".+_modified.v$", filename)):
            mutated_filenames.append(filename)

    # The folder exists but contains no candidates
    if(len(mutated_filenames) == 0):
         raise RuntimeError("Error: folder exists but contains no mutated files")
    
    return mutated_filenames


# Write all prompts for ollama and return as a list.
def write_all_prompts(path):

    all_prompts = []

    # Collect all files to scrape for theorems.
    mutated_filenames = gather_modified_files(path)

    # Write all prompts per file
    for filename in mutated_filenames:
        individual_prompts = write_prompts_per_modified_file(path / filename)
        all_prompts = all_prompts + individual_prompts
    
    return all_prompts

## UNUSED, UNSURE IF THIS WORKS
## Formatting at https://github.com/ollama/ollama-python, Custom client
# Sends a request to our local instance of ollama with our prompt.
# Returns the response of the prompt.
def send_ollama_request(prompt):
    client = Client(
        host='http://localhost:11434',
        headers={'x-some-header': 'some-value'}
    )
    response = client.chat(model='llama3.2', messages=[
        {
            'role': 'user',
    '       content': prompt,
        },
    ])
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

    # Write all prompts for ollama.
    prompts = write_all_prompts(args.input_dir)

    # Print all prompts for now.
    for prompt in prompts:
        print(prompt)

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


'''
# Timeout for python in linux use if needed 
def handler(signum, frame):
    raise Exception('TIMEOUT\n\n')


signal.signal(signal.SIGALRM, handler)

signal.alarm(totalTime)
time = lap()
try:

except Exception as e:
'''