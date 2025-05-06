# harness.py
# Harness objectives:
# 1. Generation of prompts for distribution to LLMS
# 2. Automated distribution of prompts as feasible.

import os
import re

# Any prompt engineering to add to the beginning of the proof.
def prompt_front():
    return "Prove the following theorem in the Rocq language. Show all necessary work: \n"

def write_prompt(path, filename):
    # Open input file
    with open(path + '/' + filename, "r") as input_file:
            # Open output file
            with open('prompts/' + filename + "-prompt.txt", "w") as prompt_file:
                 # 1: Write any pre-material for the prompt
                 prompt_file.write(prompt_front())
                 for line in input_file:
                      prompt_file.write(line)
                 


def main():    
    # invoke mutator on files in a certain directory
    # CODE HERE
    
    # make an OS request to files in a certain directory
    path = 'test2'
    potential_filenames = os.listdir(path)
    mutated_filenames = []
    for filename in potential_filenames:
        if(re.search(".+_modified.v$", filename)):
            mutated_filenames.append(filename)
    print(mutated_filenames)

    # read from file and append prompt
    for filename in mutated_filenames:
        write_prompt(path, filename)
            

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