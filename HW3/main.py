import copy

import read

'''
AI Assignment 3
Team Members: Tianju Ma(tml5872) Menglei Lei(mlj3199)
'''

original_KB = []


class Action(object):
    def __init__(self, cur_type, statement):
        self.type = cur_type
        self.preconditions = []
        self.add = []
        self.retract = []
        self.kb = kb()
        self.statement = statement
        self.act_ask()
        self.act_assert()
        self.act_retract()

    def act_assert(self):
        if self.type == "assert":
            self.kb.kb_assert(self.statement)

    def act_ask(self):
        if self.type == "ask":
            self.kb.kb_ask(self.statement)

    def act_retract(self):
        if self.type == "retract":
            self.kb.kb_retract(self.statement)


# define Statement object for convenient use
class Statement(object):
    def __init__(self, pattern):
        self.full = pattern
        self.predicate = pattern[0].upper()
        self.args = pattern[1:]
        self.facts = []
        self.rules = []


# define Fact object for convenient use
class Fact(object):
    count = 0

    def __init__(self, statement, supported_by=None):
        self.count = Fact.count + 1
        Fact.count += 1
        if supported_by is None:
            supported_by = []

        self.statement = statement
        if not supported_by:
            self.asserted = True
        else:
            self.asserted = False

        self.supported_by = supported_by
        self.facts_supported = []
        self.rules_supported = []

    def __repr__(self):
        return self.statement.__repr__()


# define Rule object for convenient use
class Rule(object):
    count = 0

    def __init__(self, statement=None, lhs=None, rhs=None, supported_by=None):
        self.count = Rule.count + 1
        Rule.count += 1
        if supported_by is None:
            supported_by = []

        if statement is None:
            self.LHS = lhs
            self.RHS = rhs
        else:
            self.LHS = statement[0]
            self.RHS = statement[1]

        if not supported_by:
            self.asserted = True
        else:
            self.asserted = False

        self.supported_by = supported_by
        self.facts_supported = []
        self.rules_supported = []

    def __repr__(self):
        return self.LHS.__repr__() + "====>" + self.RHS.__repr__()


# define KB object for convenient use
class kb(object):
    def __init__(self):
        self.facts = []
        self.rules = []

    def add_fact(self, cur_fact):
        self.facts.append(cur_fact)

    def add_rule(self, cur_rule):
        self.rules.append(cur_rule)

    def rem_fact(self, cur_fact):
        self.facts.remove(cur_fact)

    def rem_rule(self, cur_rule):
        self.rules.remove(cur_rule)

    # Complete assert function which allows to add fact and rule into KB
    def kb_assert(self, statement):
        if type(statement) == list:
            my_fact = Fact(statement)
            self.add_fact(my_fact)
            self.infer_from_fact(my_fact)
        else:
            temp_r = Rule(statement)
            self.add_rule(temp_r)

    # Complete Ask function to see if the statement is existing in KB
    def kb_ask(self, statement):
        bindings = {}
        for cur_fact in self.facts:
            bindings = match(statement, cur_fact.statement)
            if bindings:
                break
        if len(bindings) == 0:
            return 'No matching solutions \n'
        return bindings

    # Complete ask + function to see a list of statments is existing in KB
    # if the bindings are not consistent, then throw exceptions
    def kb_ask_plus(self, statement_list):
        list_of_bindings_lists_result = []
        all_match = {}
        for st in statement_list:
            for cur_fact in self.facts:
                bindings = match(st, cur_fact.statement)
                if bindings:
                    for b in bindings.keys():
                        if b in all_match and all_match[b] != bindings.get(b):
                            return False
                        else:
                            all_match[b] = bindings.get(b)
                    if len(bindings) != 0:
                        list_of_bindings_lists_result.append(bindings)
                        break
        return list_of_bindings_lists_result

    # Complete infer function to infer new rules and facts and add them to KB
    def kb_infer(self, cur_fact, cur_rule):
        bindings = match(cur_rule.LHS[0], cur_fact.statement)
        if bindings:
            if len(cur_rule.LHS) == 1:
                new_fact = Fact(instantiate(cur_rule.RHS, bindings), supported_by=[cur_fact, cur_rule])
                cur_fact.facts_supported.append(new_fact)
                cur_rule.rules_supported.append(new_fact)
                self.add_fact(new_fact)
            else:
                lhs = map(lambda x: instantiate(x, bindings), cur_rule.LHS[1:])
                rhs = instantiate(cur_rule.RHS, bindings)
                new_rule = Rule(None, lhs, rhs, supported_by=[cur_fact, cur_rule])
                cur_fact.facts_supported.append(new_rule)
                cur_rule.rules_supported.append(new_rule)
                self.add_rule(new_rule)

    # Complete why function to backtrack back to the original facts and rules of a new fact or rule.
    def kb_why(self, statement):
        result_facts = []
        visited = set()
        result_fact = []
        for temp_f in self.facts:
            if temp_f.statement == statement.full:
                visited.add(temp_f)
                if temp_f in original_KB:
                    result_fact.append(temp_f)
                self.dfs(result_facts, visited, result_fact, temp_f)
        return result_facts

    def kb_retract(self, statement):
        return

    # helper function for why function
    def dfs(self, result_facts, visited, result_fact, cur_fac_rule):
        for fac_rule in cur_fac_rule.supported_by:
            if fac_rule not in visited:
                visited.add(fac_rule)
                result_fact.append(fac_rule)
                self.dfs(result_facts, visited, result_fact, fac_rule)
                visited.remove(fac_rule)
                result_fact.pop()
        if len(result_fact) != 0:
            result_facts.append(copy.deepcopy(result_fact))

    def infer_from_fact(self, cur_fact):
        for temp_r in self.rules:
            self.kb_infer(cur_fact, temp_r)


# Match function to compare two statements and return a binding list if these two are matched
def match(target, cur):
    if len(target) != len(cur) or target[0] != cur[0]:
        return False
    return match_args(target[1:], cur[1:])


# use A statement and a list of bindings to Replace all of the variables with the constants they are bound to
def instantiate(pattern, bindings):
    predicate = pattern[0]
    pattern = map(lambda x: bindings.get(x, x), pattern[1:])
    pattern.insert(0, predicate)
    return pattern


# helper function of Match
def match_args(pattern_args, fact_args):
    bindings = {}
    for p, temp_f in zip(pattern_args, fact_args):
        if p == temp_f:
            continue
        match_element(p, temp_f, bindings)
        if not bindings:
            return False
    return bindings


# helper function of Match
def match_element(p, temp_f, bindings):
    if varq(p):
        bound = bindings.get(p, False)
        if bound:
            if temp_f == bound:
                return bindings
            else:
                return False
        else:
            bindings[p] = temp_f
            return bindings
    else:
        return False


# To check if there if '?'
def varq(item):
    if item[0] == "?":
        return True
    else:
        return False


# main function to test
if __name__ == "__main__":

    facts, rules = read.read_tokenize("statements.txt")

    kb1 = kb()
    for fact in facts:
        kb1.kb_assert(fact)

    for rule in rules:
        kb1.kb_assert(rule)

    original_KB = copy.deepcopy(kb1.facts)

    # Test Guide:
    # For each function, we call it under the print('*******function name*******')
    # Run python main.py in terminal to test
    # To modified test case, change the rules or facts in function parameters.

    print ('\n*******************************  Knowledge Base  *********************************\n')
    # display the original Knowledge Base
    for f in kb1.facts:
        print (f.count, f.statement)

    print ('\n*******************************  Rule Base  **************************************\n')
    # display the original Rule Base
    for r in kb1.rules:
        print(r.count, r.LHS, "====>", r.RHS)

    print ('\n*******************************  Ask  *******************************************\n')
    # display the result of Ask function
    # Result is {'?x': 'block'}. Because we can find {'isa', 'pyramid', 'block'} in KB.
    # To change the test case, change it directly in parameters below.
    print (kb1.kb_ask(['isa', 'pyramid', '?x']))

    print ('\n*******************************  Ask+  *******************************************\n')
    # display the result of Ask+ function
    # To change the test case, change it directly in parameters below.

    # Result is 'No correct match !!!!!'. Because same variable will match two different facts.
    ll = [['isa', 'cube', '?x'], ['isa', 'pyramid', '?x']]
    result = kb1.kb_ask_plus(ll)
    if result:
        print (result)
    else:
        print("No correct match !!!!!!!")

    # Result is [{'?x': 'block'}, {'?y': 'block'}]. Because we can find {'isa', 'pyramid', 'block'} in KB.
    ll = [['isa', 'cube', '?x'], ['isa', 'pyramid', '?y']]
    result = kb1.kb_ask_plus(ll)
    if result:
        print (result)
    else:
        print("No correct match !!!!!!!")

    print ('\n*******************************  Match *******************************************\n')
    # display the result of Match function
    # To change the test case, change it directly in parameters below.
    # Result is {'?x': 'block'} because if we want the binding to be true, x must be block
    print (match(['isa', 'pyramid', '?x'], ['isa', 'pyramid', 'block']))

    print ('\n*******************************  Infer  *******************************************\n')
    # Execute Infer function
    # To change the test case, change it directly in parameters below.
    for fact in kb1.facts:
        for rule in kb1.rules:
            kb1.kb_infer(fact, rule)

    print ('\n**********************  Knowledge Base After Infer ********************************\n')
    # display the result of KB after executing Infer function
    for f in kb1.facts:
        print (f.count, f.statement)

    print ('\n**********************  Rule Base After Infer *************************************\n')
    # display the result of Rule Base after executing Infer function
    for r in kb1.rules:
        print(r.count, r.LHS, "====>", r.RHS)

    print ('\n*******************************  Instantiate  ***************************************\n')
    # Execute Instantiate function
    # To change the test case, change it directly in parameters below.
    # Result is ['size', 'pyramid4', 'blue'] because x is binded to blue.
    sta = Statement(['size', 'pyramid4', '?x'])
    input_binding_list = [['?x', 'blue']]

    bindingList = {}
    for val in input_binding_list:
        bindingList[val[0]] = val[1]

    print(instantiate(sta.full, bindingList))

    print ('\n*******************************  Why **************************************\n')
    # Execute Why function
    # To change the test case, change it directly in parameters below.
    # Result is [['inst', 'sphere1', 'sphere']], [[['inst', '?x', 'cube']]====>['flat', '?x']]
    # Because ['flat', 'sphere1'] can be inferred from the result
    result = kb1.kb_why(Statement(['flat', 'sphere1']))
    for l in result:
        print(l)
