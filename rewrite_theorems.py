import gather_theorems
from random import randint
import re
from typing import Generator
from typing import Tuple
from typing import List, Union
from copy import deepcopy


Tree = Union[Union[List[Union["Tree", str]], str], str]

"""
def list_to_str(item: list[]) -> Tree: 
    return list
"""


def rewrite_theorems(file_contents: str) -> str:

    lines = file_contents.split("\n")
    newlines = []
    while lines != []:

        line = lines.pop(0)
        m = re.match(r"\s*(Theorem|Lemma|Fact)\s+([A-Za-z][A-Za-z0-9_']*)", line)

        if m:
            stmt_lines = [line]
            while lines != [] and not re.match(r"\s*Proof\.", lines[0].strip()):
                stmt_lines.append(lines.pop(0).strip())

            stmt_lines = " ".join(stmt_lines)

            mutations = list(full_generator(stmt_lines))

            if len(mutations) > 0:
                _, inverse, mutation = mutations[randint(0, len(mutations) - 1)]
                mutation = tree_to_string(mutation)
                newlines.append(mutation)
                newlines += "\n"
                newlines.append(lines.pop(0))
                # Current proofs are both to resiliant and too rigid to insert tactics at beginning.
                newlines += "\n"
                newlines.append(inverse)
                newlines += "\n"

            else:
                newlines.append(stmt_lines)
                newlines += "\n"
        else:
            newlines.append(line)
            newlines += "\n"

    return " ".join(newlines)


def build_inverse(rewrite: str, oldThrm: Tree, newThrm: Tree) -> str:
    if rewrite != "eq_sym":
        return f"apply {rewrite}."
    else:
        return ""


"""


    #provides the code needed to repair the proof
    freshname = "freshname" + str(randint(1, 10000))
    inverse = "(assert"
    if rewrite == "eq_sym" or rewrite == "iff_sym" or rewrite == "iff_to_and" or rewrite == "not_eq_sym": 
        inverse += f"({freshname} : ({tree_to_string(newThrm).strip('.')}) ->"
        inverse += f"({tree_to_string(oldThrm).strip('.')}))\n" 
        inverse += f"by apply {rewrite}).\napply {freshname}." 
        return inverse
    
    if rewrite == "neg_false": 
        inverse += f"({freshname} : ({tree_to_string(newThrm).strip('.')}) -> (~ {tree_to_string(newThrm[1][1]).strip()}))\n"
        inverse += f"by apply {rewrite}).\napply {freshname}."
    
        return inverse
    
    else:
        print("BAD INVERSE INPUT")
        return None
"""


def preprocess(thrm: str) -> Tree:
    """insert spaces"""

    for i in [
        "(",
        ")",
        ",",
        "<=",
        ">=",
        r"(?<!<)>(?!=)",
        r"<(?!(=|>))",
        r"(?<!<)=(?!>)",
        r"(?<!<)->",
        r"<-(?!>)",
        "<->",
        ".",
        "<>",
        "~",
    ]:
        thrm = thrm.replace(i, f" {i} ")
    return [x for x in thrm.split() if x.strip() != ""]


def parens(thrm: Tree) -> Tree:
    """Turn parenthesis into sub lists"""
    parenthed = []
    while thrm != []:
        if isinstance(thrm, list):
            token = thrm.pop(0)
            if isinstance(token, str):
                token.strip()
            if token == "(":
                j = parens(thrm)
                if isinstance(j, list):
                    parenthed.append(["()"] + j)
            elif token == ")":
                return parenthed
            else:
                parenthed.append(token)

    return parenthed


def parselogical(thrmTree: Tree) -> Tuple[Tree, Tree]:
    """Create Parse Tree"""

    binary_conn = ["<->", "<-", "->", " iff ", "/\\", "\\/", ":"]
    prefix_conn = ["forall", "exists!"]
    prog = []

    while thrmTree != [] and isinstance(thrmTree, List):
        token = thrmTree.pop(0)

        if isinstance(token, list):
            _, prog1 = parselogical(token)
            prog.append(prog1)

        elif token == "()":
            _, t = parselogical(thrmTree)
            return [], [
                "()",
                t,
            ]  # we have already handled the parens so we know we are in a sublist

        elif token == ".":
            return [], prog  # This will be the end of the theorem

        elif token in binary_conn:
            thrmTree, prog2 = parselogical(thrmTree)
            prog = unpack(prog)
            prog2 = unpack(prog2)
            prog = [token, prog, prog2]
            return (
                thrmTree,
                prog,
            )  # return the binary connective that was in infix order

        elif token in prefix_conn:
            thrmTree, prog1 = parselogical(thrmTree)
            thrmTree, prog2 = parselogical(thrmTree)
            prog1 = unpack(prog1)
            prog2 = unpack(prog2)
            prog.append([token, prog1, prog2])

        elif token == ",":  # This marks the end of a existential qualifier
            prog.append(["TOKEN", ","])
            return thrmTree, prog

        else:  # all other tokens are treated as constant identifiers technically this should be of the form ["Token"]
            prog.append(["TOKEN", token])

    return thrmTree, prog


def unpack(item: Tree) -> Tree:
    """Helper Function for cleaning extra parentheticals"""
    if len(item) == 1 and isinstance(item[0], list):
        return item[0]
    else:
        return item


def parsealgebraic(thrmTree: Tree) -> Tree:
    "Second round of parse to catch the algebraic operators"

    minor_conn = ["=", "<=", ">=", "<", ">", "<>"]
    prog = []
    while thrmTree != []:
        if isinstance(thrmTree, list):
            term = thrmTree.pop(0)
        else:
            term = thrmTree

        if isinstance(term, list):
            if term[0] == "TOKEN":
                t = term[1]
                if t in minor_conn:
                    return [t, unpack(prog), parsealgebraic(thrmTree)]
                else:
                    prog.append(term)
            else:
                prog.append(parsealgebraic(term))
        else:
            prog.append(term)

    return unpack(prog)


def mutate_generator(tree: Tree) -> Generator[Tuple[str, str, Tree], None, None]:
    """Generator Function returns iterable of all possible mutations"""

    if not isinstance(tree, list):
        return None

    # if tree[0] == "=":

    #     original = [tree[0], tree[1], tree[2]]
    #     mutated = [tree[0], tree[2], tree[1]]

    #     yield "eq_sym", build_inverse("eq_sym", original, mutated), mutated  # yield

    #     for name, inverse, mutation in mutate_generator(
    #         tree[1]
    #     ):  # get remainder of mutations
    #         if mutation != []:
    #             yield name, inverse, [tree[0], mutation, tree[2]]

    #     for name, inverse, mutation in mutate_generator(
    #         tree[2]
    #     ):  # get remainder of mutataions
    #         if mutation != []:
    #             yield name, inverse, [tree[0], tree[1], mutation]
    #     return None

    if tree[0] == "<>":

        mut = ["<>", tree[2], tree[1]]
        yield "not_eq_sym", build_inverse("not_eq_sym", tree, mut), mut

        for name, inverse, mutation in mutate_generator(
            tree[1]
        ):  # get remainder of mutations
            if mutation != []:
                yield name, inverse, [tree[0], mutation, tree[2]]

        for name, inverse, mutation in mutate_generator(
            tree[2]
        ):  # get remainder of mutataions
            if mutation != []:
                yield name, inverse, [tree[0], tree[1], mutation]
        return None

    elif tree[0] == ":":

        for name, inverse, mutation in mutate_generator(
            tree[2]
        ):  # no changes to type declarations yeild remainder
            if mutation != []:
                yield name, inverse, [tree[0], tree[1], mutation]
        return None

    elif tree[0] == "<->":

        mutation = [tree[0], tree[2], tree[1]]
        yield "iff_sym", build_inverse("iff_sym", tree, mutation), mutation
        # ------------------- comment out if this is giving problems begin
        mutation = [
            "/\\",
            ["()", ["->", tree[1], tree[2]]],
            ["()", ["->", tree[2], tree[1]]],
        ]
        yield "iff_to_and", build_inverse("iff_to_and", tree, mutation), mutation
        # continue mutations on branches
        # ------------------- end
        for name, inverse, mut in mutate_generator(tree[1]):
            if mut != []:
                yield name, inverse, [tree[0], mut, tree[2]]

        for name, inverse, mut in mutate_generator(tree[2]):
            if mut != []:
                yield name, inverse, [tree[0], tree[1], mut]
        return None

    elif tree[0] == "TOKEN":
        return None

    else:

        for i, v in enumerate(tree):

            # if v == ["TOKEN", "~"]:

            #     t = deepcopy(tree)
            #     # neg_false theorem
            #     mut = ["()", ["->", t[i + 1], "False"]]
            #     t[i] = mut
            #     t.pop(i + 1)

            #     yield "neg_false", build_inverse("neg_false", tree[i : i + 2], mut), t

            # else:
            for name, inverse, mut in mutate_generator(v):  #
                tree[i] = mut
                yield name, inverse, tree
            tree[i] = v

        return None


def infix_traverse(tree: Tree) -> Generator[str, None, None]:
    """traverses tree in infix order (excepting where prefix order is needed)"""

    bin_connectives = [
        "=",
        "<=",
        ">=",
        "<",
        ">",
        "<->",
        "<-",
        "->",
        " iff ",
        "/\\",
        "\\/",
        ":",
    ]

    if isinstance(tree, list):

        if tree[0] in bin_connectives:
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
        elif tree[0] == "TOKEN":
            if isinstance(tree[1], str):
                yield tree[1]
        else:
            for i in tree:
                for j in infix_traverse(i):
                    yield j
    else:
        yield tree

    return None


def tree_to_string(tree: Tree) -> str:
    """Returns String form of parse tree, strips all token tags"""

    string = ""

    for i in infix_traverse(tree):
        string += i + " "

    string += "."
    return string


def full_generator(theorem: str) -> Generator[Tuple[str, str, Tree], None, None]:
    """Parses theorem and returns a mutation generator"""

    j = parselogical(parens(preprocess(theorem)))[1]
    j = parsealgebraic(j)
    for i in mutate_generator(j):
        yield deepcopy(i)
    return None


# with open("mini_test/example.v", 'r') as f:

#         contents = f.read()

# j = rewrite_theorems(contents)

# with open("mini_test/testoutput.v", "w") as f:

#     f.write(j)
