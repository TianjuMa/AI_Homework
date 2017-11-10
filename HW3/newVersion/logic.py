import copy
from read import *


'''
AI Assignment 3
Team Members: Tianju Ma(tml5872) Menglei Lei(mlj3199)
'''
#Record the original KB and RB
original_facts_pretty = []
original_facts, original_rules = read_tokenize("asserts.txt")


#Match function and its dependent functions
def pattern_match(p, fact):
    f = fact.full
    if p[0] != f[0]:
        return False
    return match_args(p[1:],f[1:], {})


def match(pattern, fact):
    p = pattern.full
    f = fact.full
    if p[0] != f[0]:
        return False
    return match_args(p[1:],f[1:], {})

def match_args(pattern_args, fact_args, bindings):
    for p, f in zip(pattern_args, fact_args):
        bindings = match_element(p, f, bindings)
        if False == bindings:
            return False
    return bindings

def match_element(p, f, bindings):
    if p == f:
        return bindings
    elif varq(p):
        bound = bindings.get(p, False)
        if bound:
            if f == bound:
                return bindings
            else:
                return False
        else:
            bindings[p] = f
            return bindings
    else:
        return False

def varq(item):
    if item[0] == "?":
        return True
    else:
        return False

def instantiate(pattern, bindings):
    predicate = pattern[0]
    args = map(lambda x: bindings.get(x, x), pattern[1:])
    args.insert(0, predicate)
    return args
#=============================Objects=============================#
#Fact object
class Fact(object):
    def __init__(self, pattern):
        self.full = pattern
        self.predicate = pattern[0].upper()
        self.args = pattern[1:]
        self.facts = []
        self.rules = []


    def add_fact(self, fact):
        self.facts.append(fact)

    def add_rule(self, rule):
        self.rules.append(rule)

    def output(self):
        return "(" + " ".join(self.full) + ")"
#Rule Object
class Rule(object):
    def __init__(self, lhs, rhs):
        self.full = lhs + rhs
        self.lhs = map(lambda x: Fact(x), lhs)
        self.rhs = Fact(rhs)
        self.facts = []
        self.rules = []

    def add_fact(self, fact):
        self.facts.append(fact)

    def add_rule(self, rule):
        self.rules.append(rule)

    def output(self):
        return " ".join(map(lambda x: x.output(), self.lhs)) + "> " + "->" + " " + self.rhs.output()
#KB Object
class KB(object):
    def __init__(self, file_name):
        self.tokenized_facts, self.tokenized_rules = read_tokenize(file_name)
        self.KB = []
        self.RB = []

    def KB_AssertFact(self, fact):
        self.KB.append(fact)
        self.KB_InferFact(fact)

    def KB_AssertRule(self, rule):
        self.RB.append(rule)
        self.KB_InferRule(rule)


    def KB_InferFact(self, fact):
        for r in self.RB:
            bd = match(r.lhs[0], fact)
            if bd != False:
                if len(r.lhs) == 1:
                    fact_rhs = Fact(instantiate(r.rhs.full, bd))
                    self.KB_AssertFact(fact_rhs)
                    fact.add_fact(fact_rhs)
                else:
                    ins_lhs = map(lambda x : instantiate(x.full, bd), r.lhs[1:])
                    ins_rhs = instantiate(r.rhs.full, bd)
                    newRule = Rule(ins_lhs, ins_rhs)
                    fact.add_rule(newRule)
                    self.KB_AssertRule(newRule)


    def KB_InferRule(self, rule):
        for f in self.KB:
            bd = match(rule.lhs[0], f)
            if bd != False:
                if len(rule.lhs) == 1:
                    fact_rhs = Fact(instantiate(rule.rhs.full, bd))
                    self.KB_AssertFact(fact_rhs)
                    f.add_fact(fact_rhs)
                else:
                    ins_lhs = map(lambda x : instantiate(x.full, bd), rule.lhs[1:])
                    ins_rhs = instantiate(rule.rhs.full, bd)
                    newRule = Rule(ins_lhs, ins_rhs)
                    f.add_rule(newRule)
                    self.KB_AssertRule(newRule)


    def KB_Retract(self, stat):
        for f in self.KB:
            if f.full == stat:
                fact = f
                print 'Retract:', f.output()
                self.KB.remove(f)
                for f in fact.facts:
                    self.KB_Retract(f.full)
                for r in fact.rules:
                    if '?' in r.rhs.output():
                        bd_list = self.KB_ASK(r.rhs)
                        for bd in bd_list:
                            rhs = instantiate(r.rhs.full, bd)
                            self.KB_Retract(rhs)
                    else:
                        for facts in self.KB:
                            if facts.full == r.rhs.full:
                                self.KB_Retract(r.rhs.full)

                    if r in self.RB:
                        self.RB.remove(r)
                        print 'Retract:', r.output()



    def KB_ASK(self, stat):
        bd_list = []
        for f in self.KB:
            bd = match(stat, f)
            if bd and bd not in bd_list:
                bd_list.append(bd)
        if len(bd_list) == 0:
            return "There is no match"
        return bd_list


    def KB_ASKplus(self, stats):
        bd_list = []
        for stat in stats:
            if bd_list == []:
                for fact in self.KB:
                    bindings = pattern_match(stat, fact)
                    if bindings != False:
                        bd_list.append(bindings)
            else:
                for ins in map(lambda x: (instantiate(stat, x), x), bd_list):
                    for fact in self.KB:
                        bindings = pattern_match(ins[0], fact)
                        if bindings != False:
                            for key in ins[1]:
                                bindings[key] = ins[1][key]
                            bd_list.append(bindings)
        L = map(lambda x : len(x), bd_list)
        result = [item for item in bd_list if len(item) == max(L)]
        f = lambda x,y : x if y in x else x + [y]
        result = reduce(f, [[], ] + result)
        return result


    def KB_Why(self, fact):
        path = []
        rule = []
        infer_KB_pretty = []
        original_facts_pretty = map(lambda x : Fact(x).output(), original_facts)
        for r in self.RB:
            bd = match(r.rhs, fact)
            if bd != False:
                stats = [r.rhs.full]
                for lhs in r.lhs:
                    stats.append(lhs.full)
                ans = self.KB_ASKplus(stats)
                for b in ans:
                    if len([i for i in b.items() if i in bd.items()]) == len(bd.items()):
                        ins_lhs = map(lambda x : instantiate(x.full, b), r.lhs)
                        pre_lhs = map(lambda x : Fact(x).output(), ins_lhs)
                        rule.append(r.output())
                        if set(pre_lhs).issubset(set(original_facts_pretty + infer_KB_pretty)):
                            for lhs in ins_lhs:
                                if lhs in original_facts:
                                    path.append(Fact(lhs).output())
                                else:
                                    self.why(Fact(lhs))
        path = list(set(path))
        if len(path) == 0:
            print fact.full
        else:
            print path + list(set(rule))
