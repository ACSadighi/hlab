

#!/usr/bin/env python3
from math import floor
from pyeda.inter import *
from itertools import combinations

class Node:
    """
    The Node class represents a conditional norm in the context of a proof represented by a directed
    acyclic graph. The root of the graph is the given conclusion. Each node contains the input and output of
    the conditional norm it represents, its parent Node representing the norm yielded by the current norm,
    the name of the operation ('Node.op') performed on the norm in the proof, the Node whose norm is used
    with the current norm if the operation takes two norms ('Node.partner'), a list of child Nodes whose norm
    yields the current norm, and a label for if the norm of the current Node is a given premise.
    """
    def __init__(self, inp, out, par):
        self.input = inp        # Norm input
        self.output = out       # Norm output
        self.parent = par       # Consequent norm
        self.op = None          # Operation applied to norm in proof
        self.partner = None     # Norm used in same operation
        self.children = []      # Antecedent norms
        self.premise = False    # Label for if norm is a given premise

def printNodes(node):
    print('Node: ' + '(' + str(node.input) + ',' + str(node.output) + ')')
    print('Children:')
    for i in node.children:
        print('(' + str(i.input) + ',' + str(i.output) + ')')

def free_nodes(node):
    lst = []
    if len(node.children) == 0:
        if node.premise == False:
            lst += [node]
        return lst
    for child in node.children:
        lst += free_nodes(child)
    for child in node.children:
        if child not in lst:
            return lst
    return lst + [node] 

def prune(node):
    par = node.parent
    par.children = [node]
    if node.partner != None:
        par.children.append(node.partner)
    if par.parent != None:
        prune(par)

def rev_or_prep(node, p):
    if isinstance(node.input, Variable) == False:
        for r in range(1,floor(len(node.input.xs)/2)+1):
            n = len(node.input.xs)
            data = [0]*r
            rev_or(node, data, 0, n - 1, 0, r, p)

def rev_or(node, data, start, end, index, r, p):
    arr = node.input.xs

    if (index == r):
        for child in node.children:
            if child.premise == True:
                return
        first = Or(0)
        second = Or(0)
        ind = 0
        for j in range(end+1):
            if ind < r and arr[j] == data[ind]:
                first = Or(first, Or(data[ind]))
                ind += 1
            else:
                second = Or(second, Or(arr[j]))
        for child in node.children:
            if child.input.equivalent(first) or child.input.equivalent(second):
                return
        child1 = Node(first, node.output, node)
        child2 = Node(second, node.output, node)
        node.children.append(child1)
        node.children.append(child2)
        child1.op = 'OR'
        child2.op = 'OR'
        child1.partner = child2
        child2.partner = child1
        for prem in p:
            if str(prem[0])==str(child1.input) and str(prem[1])==str(child1.output):
                child1.premise = True
            if str(prem[0])==str(child2.input) and str(prem[1])==str(child2.output):
                child2.premise = True
        if child1.premise == True or child2.premise == True:
            prune(child1)
            if child1.premise == True and child2.premise == True:
                return
            elif child1.premise == True:
                rev_or_prep(child2, p)
                return
            else:
                rev_or_prep(child1, p)
                return

        return

    i = start
    while(i <= end and end - i + 1 >= r - index):
        data[index] = arr[i]
        rev_or(node, data, i + 1, end, index + 1, r, p)
        i += 1

def rev_and_prep(node, p):
    if isinstance(node.output, Variable) == False:
        for r in range(1,floor(len(node.output.xs)/2)+1):
            n = len(node.output.xs)
            data = [0]*r
            rev_and(node, data, 0, n - 1, 0, r, p)

def rev_and(node, data, start, end, index, r, p):
    arr = node.output.xs

    if (index == r):
        for child in node.children:
            if child.premise == True:
                return
        first = And(1)
        second = And(1)
        ind = 0
        for j in range(end+1):
            if ind < r and arr[j] == data[ind]:
                first = And(first, And(data[ind]))
                ind += 1
            else:
                second = And(second, And(arr[j]))
        for child in node.children:
            if child.output.equivalent(first) or child.output.equivalent(second):
                return
        child1 = Node(node.input, first, node)
        node.children.append(child1)
        child2 = Node(node.input, second, node)
        node.children.append(child2)
        child1.op = 'AND'
        child2.op = 'AND'
        child1.partner = child2
        child2.partner = child1
        for prem in p:
            if prem[0]==child1.input and str(prem[1])==str(child1.output):
                child1.premise = True
            if prem[0]==child2.input and str(prem[1])==str(child2.output):
                child2.premise = True
        if child1.premise == True or child2.premise == True:
            prune(child1)
            if child1.premise == True and child2.premise == True:
                return
            elif child1.premise == True:
                rev_and_prep(child2, p)
                return
            else:
                rev_and_prep(child1, p)
                return

        return

    i = start
    while(i <= end and end - i + 1 >= r - index):
        data[index] = arr[i]
        rev_and(node, data, i + 1, end, index + 1, r, p)
        i += 1

def rev_wo(node, exprs, p):
    for child in node.children:
        if child.premise == True:
            return

    for ex in exprs:
        if str(ex) != '1':
            child = Node(node.input, And(node.output, ex), node)
            if node.input.equivalent(child.input) and node.output.equivalent(child.output):
                continue
            child.op = 'WO'
            node.children.append(child)
            for prem in p:
                if prem[0].equivalent(child.input) and prem[1].equivalent(child.output):
                    child.premise = True
                    prune(child)
                    return

def rev_si(node, exprs, p):
    for child in node.children:
        if child.premise == True:
            return

    for ex in exprs:
        if str(ex) != '0':
            child = Node(Or(node.input, ex), node.output, node)
            if node.input.equivalent(child.input) and node.output.equivalent(child.output):
                continue
            child.op = 'SI'
            node.children.append(child)
            for prem in p:
                if prem[0].equivalent(child.input) and prem[1].equivalent(child.output):
                    child.premise = True
                    prune(child)
                    return
    
def find_prems(node):
    if node.premise:
        print(node.input,' ',node.output,node.op,'  ',node.parent.input,' ',node.parent.output, node.parent.op, '   ',node.parent.parent.input,node.parent.parent.output)
    if len(node.children) == 0:
        return
    else:
        for i in node.children:
            find_prems(i)

def proof_search(c, p):
    conclusion = Node(c[0], c[1], None)
    conclusion.input = conclusion.input.to_dnf()
    conclusion.output = conclusion.output.to_cnf()
    rev_or_prep(conclusion, p)
    f = free_nodes(conclusion)
    if len(f) == 0:
        return conclusion
    for node in f:
        rev_and_prep(node, p)
    if len(free_nodes(conclusion)) == 0:
        return conclusion

    in_forms = []
    out_forms = []
    for prem in p:
        if isinstance(prem[0], Variable):
            if prem[0] not in in_forms:
                in_forms.append(prem[0])
        else:
            for formula in prem[0].xs:
                if formula not in in_forms:
                    in_forms.append(formula)
        if isinstance(prem[1], Variable):
            if prem[1] not in out_forms:
                out_forms.append(prem[1])
        else:
            for formula in prem[1].xs:
                if formula not in out_forms:
                    out_forms.append(formula)

    if isinstance(conclusion.input, Variable):
        if conclusion.input not in in_forms:
            in_forms.append(conclusion.input)
    else:
        for formula in conclusion.input.xs:
            if formula not in in_forms:
                in_forms.append(formula)
    if isinstance(conclusion.output, Variable):
        if conclusion.output not in out_forms:
            out_forms.append(conclusion.output)
    else:
        for formula in conclusion.output.xs:
            if formula not in in_forms:
                out_forms.append(formula)
    in_forms = list(set(in_forms))
    out_forms = list(set(out_forms))
    negs = []
    for formula in in_forms:
        negs += [Not(formula)]
    in_forms += negs
    negs = []
    for formula in out_forms:
        negs += [Not(formula)]
    out_forms += negs

    in_exprs = list()
    for n in range(int(len(in_forms)/2+1)):
        in_exprs += list(combinations(in_forms,n))
    in_exprs.pop(0)
    for i in range(len(in_exprs)):
        if len(in_exprs[i]) > 1:
            and_phrase = And(1)
            for j in in_exprs[i]:
                and_phrase = And(and_phrase, And(j))
            in_exprs[i] = and_phrase
        else:
            in_exprs[i] = in_exprs[i][0]

    out_exprs = list()
    for n in range(int(len(out_forms)/2+1)):
        out_exprs += list(combinations(out_forms,n))
    out_exprs.pop(0)
    for i in range(len(out_exprs)):
        if len(out_exprs[i]) > 1:
            or_phrase = Or(0)
            for j in out_exprs[i]:
                or_phrase = Or(or_phrase, Or(j))
            out_exprs[i] = or_phrase
        else:
            out_exprs[i] = out_exprs[i][0]

    f = free_nodes(conclusion)
    if len(f) == 0:
        return conclusion
    for node in f:
        if node in free_nodes(conclusion):
            rev_wo(node, out_exprs, p)
        if node in free_nodes(conclusion):
            rev_si(node, in_exprs, p)

    f = free_nodes(conclusion)
    if len(f) == 0:
        return conclusion
    else:
        additions = []
        while free_nodes(conclusion):
            new = f.pop()
            additions.append(new)
            new.premise = True
            new.children = []
            prune(new)
        return additions


    

a, b, c, d, w, x, y, z= map(exprvar, 'abcdwxyz')
result = tree_root = proof_search((Or(a, b), And(x, y)),[(Or(a, b), x), (a, y), (b, y)])
print()
if isinstance(result, list):
    print('No proof. Add the following premises for a complete proof:')
    for i in result:
        print('(',i.input,',',i.output, ')')
else:
    print('A proof exists')
print()