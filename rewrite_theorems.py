import gather_theorems
from random import randint
import re
from typing import Callable

def rewrite_theorems(file_contents: str) -> str:
    # TODO: Mostly got it done, have the parser and mutator in place as yielding functions, just need to utilize them, need to 
    # add in a few more mutations
    # finally need to double check my parsing on a more expressive theorem
    return file_contents
    

def rectify_proofs(file_contents: str) -> str:
    """Rewrites all proofs to undo the rewrites to theorems, 
    so that the original proofs continue to work as before"""

    # todo, this shouldn't be difficult at all, just need to get on it. 
    # TODO: Fill in
    return file_contents


def preprocess(string): 
    for i in ["(", ")", ",", "="]: 
        string = string.replace(i, f" {i} ")
    return string.split()

def parens(string):
    
    parenthed = []
    while string != []: 
        
        token = string.pop(0).strip()
        if token == "(": 
            parenthed.append(["("] + parens(string))
        elif token == ")":
            return parenthed + [")"]
        else: 
            parenthed.append(token)

    return parenthed




def parselogical(stringlist): 
    binary_conn =  [ "<->", "<-", "->", " iff ", "/\\", "\\/", ":"]
    

    prog = []
    while stringlist != []:
        token = stringlist.pop(0)
        if isinstance(token, list): 
            _, prog1 = parselogical(token[1:-1])
            prog.append(["()", prog1])

        elif token in binary_conn: 
            stringlist, prog2 = parselogical(stringlist)
            return  stringlist, [token, prog, prog2]
        
        else: 

            prog.append(token)
    
    return stringlist, prog

def parseminor(proglist):
    "Second round of parse to catch the minor operators"
    minor_conn = ["=", "<=", ">=", "<", ">"]

    prog = []
    while proglist != []: 

        term = proglist.pop(0)
        if isinstance(term, list): 
            prog.append(parseminor(term))
        elif term in minor_conn: 
            prog = [term, prog, parseminor(proglist)]
        else: 
            prog.append(term)
        
    return prog



def equality_ids(tree: list[list[str]]): 

    if tree == []: 
        return [] 

    if tree[0] == "=": 
        yield [tree[0], tree[2], tree[1]]
        for i in equality_ids(tree[1]): 
            if i != []: 
                yield [tree[0], i, tree[2]]
        
        for i in equality_ids(tree[2]): 
            if i != []: 
                yield [tree[0], tree[1], i]
        return []
        
    elif tree[0] == ":": 

        for mutation in equality_ids(tree[2]):
            if mutation != []:
                yield [tree[0], tree[1], mutation]


    elif tree[0] == "<->": 

        yield [tree[0], tree[2], tree[1]]
        yield ["/\\", ["->", tree[2], tree[1]], ["->", tree[1], tree[2]]]
        
        for mut in equality_ids(tree[1]): 
            if mut != []: 
                yield [tree[0], mut, tree[2]]

        for mut in equality_ids(tree[2]): 
            if mut != []: 
                yield [tree[0], tree[1], mut]

    return []



def infix_traverse(tree): 

    connectives = ["=", "<=", ">=", "<", ">", "<->", "<-", "->", " iff ", "/\\", "\\/", ":"]

    if isinstance(tree, list): 
        if tree[0] in connectives: 
            for i in infix_traverse(tree[1]):
                yield i
            yield tree[0]
            for i in infix_traverse(tree[2]):
                yield i
        elif tree[0] == "()":
            yield "("
            for i in tree[1:]: 
                for j in infix_traverse(i):
                    yield j
            yield ")"
        else:
            for i in  tree: 
                for j in infix_traverse(i):
                    yield j
    else:
        yield tree
        
    return 

def prefix_to_str(str): 

    string = ""

    for i in infix_traverse(str):
        string += i + " "
    return string

'''
k = "Theorem tree_depth_zero_iff {A} (t : Tree A) : (tree_depth t) = 0 <-> t = Leaf."
            
test = parseminor(parselogical(parens(preprocess(k)))[1])
for i in equality_ids(test): 

    print(f"------------\n"\
          f"{prefix_to_str(i)}\n")

'''


