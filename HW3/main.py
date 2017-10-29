import copy

import read


class Statement(object):
    def __init__(self, pattern):
        self.full = pattern
        self.predicate = pattern[0].upper()
        self.args = pattern[1:]
        self.facts = []
        self.rules = []


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

    def kb_assert(self, statement):
        if type(statement) == list:
            self.add_fact(Fact(statement))
        else:
            self.add_rule(Rule(statement))

    def kb_ask(self, statement):
        list_of_bindings_lists = []
        for cur_fact in self.facts:
            bindings = match(statement, cur_fact.statement)
            if bindings and not (bindings in list_of_bindings_lists):
                list_of_bindings_lists.append(bindings)
        if len(list_of_bindings_lists) == 0:
            return 'No matching solutions \n'
        return list_of_bindings_lists

    def kb_ask_plus(self, statement_list):
        list_of_bindings_lists_result = []
        for st in statement_list:
            for cur_fact in self.facts:
                bindings = match(st, cur_fact.statement)
                if bindings and not (bindings in list_of_bindings_lists_result):
                    list_of_bindings_lists_result.append(bindings)

        return list_of_bindings_lists_result

    def kb_infer(self, cur_fact, cur_rule):
        bindings = match(cur_rule.LHS[0], cur_fact.statement)
        if bindings:
            if len(cur_rule.LHS) == 1:
                new_fact = Fact(instantiate(cur_rule.RHS, bindings), supported_by=[cur_fact, cur_rule])
                new_fact.facts_supported.append(cur_fact)
                new_fact.rules_supported.append(cur_rule)
                self.add_fact(new_fact)
            else:
                lhs = map(lambda x: instantiate(x, bindings), cur_rule.LHS[1:])
                rhs = instantiate(cur_rule.RHS, bindings)
                new_rule = Rule(None, lhs, rhs, supported_by=[cur_fact, cur_rule])
                new_rule.facts_supported.append(cur_fact)
                new_rule.rules_supported.append(cur_rule)
                self.add_rule(new_rule)

    def kb_why(self, statement):
        result_facts = []
        visited = set()
        result_fact = []
        for temp_f in self.facts:
            if temp_f.statement == statement.full:
                self.dfs(result_facts, visited, result_fact, temp_f)
        return result_facts

    def dfs(self, result_facts, visited, result_fact, cur_fac_rule):
        visited.add(cur_fac_rule)
        result_fact.append(cur_fac_rule)
        for fac_rule in cur_fac_rule.supported_by:
            if fac_rule not in visited:
                self.dfs(result_facts, visited, result_fact, fac_rule)
        if len(result_fact) != 0:
            result_facts.append(copy.deepcopy(result_fact))
            result_fact.pop()
        visited.remove(cur_fac_rule)


def match(target, cur):
    if len(target) != len(cur) or target[0] != cur[0]:
        return False
    return match_args(target[1:], cur[1:])


def instantiate(pattern, bindings):
    predicate = pattern[0]
    pattern = map(lambda x: bindings.get(x, x), pattern[1:])
    pattern.insert(0, predicate)
    return pattern


def match_args(pattern_args, fact_args):
    bindings = {}
    for p, temp_f in zip(pattern_args, fact_args):
        if p == temp_f:
            continue
        match_element(p, temp_f, bindings)
        if not bindings:
            return False
    return bindings


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


def varq(item):
    if item[0] == "?":
        return True
    else:
        return False


if __name__ == "__main__":

    facts, rules = read.read_tokenize("statements.txt")

    kb1 = kb()
    for fact in facts:
        kb1.kb_assert(fact)

    for rule in rules:
        kb1.kb_assert(rule)

    # print ('\n*******************************  Knowledge Base  *********************************\n')
    # for f in kb1.facts:
    #     print (f.count, f.statement)
    #
    # print ('\n*******************************  Rule Base  **************************************\n')
    # for r in kb1.rules:
    #     print(r.count, r.LHS, "====>", r.RHS)
    #
    # print ('\n*******************************  Ask  *******************************************\n')
    # print (kb1.kb_ask(['isa', 'pyramid', '?x']))

    # print ('\n*******************************  Match *******************************************\n')
    # print (match(['isa', 'pyramid', '?x'], ['isa', 'pyramid', 'block']))
    #
    # print ('\n*******************************  Infer *******************************************\n')
    # fa = Fact(['size', 'pyramid4', 'big'])
    # ru = Rule(([['size', '?x', '?y']], ['isa', '?x', 'block']))
    # kb1.kb_infer(fa, ru)
    #
    # print ('\n**********************  Knowledge Base After Infer ********************************\n')
    # for f in kb1.facts:
    #     print (f.statement)
    #
    # print ('\n**********************  Rule Base After Infer *************************************\n')
    # for r in kb1.rules:
    #     print(r.LHS, "====>", r.RHS)
    #
    # print ('\n*******************************  Instantiate  ***************************************\n')
    # sta = Statement(['size', 'pyramid4', '?x'])
    # input_binding_list = [['?x', 'blue']]
    #
    # bindingList = {}
    # for val in input_binding_list:
    #     bindingList[val[0]] = val[1]
    #
    # print(instantiate(sta.full, bindingList))
    #
    # print ('\n*******************************  Why  ***************************************\n')
    # sta = Statement(['size', 'pyramid4', '?x'])

    for fact in kb1.facts:
        for rule in kb1.rules:
            kb1.kb_infer(fact, rule)
    #
    print ('\n*******************************  Knowledge Base After update *********************************\n')
    for f in kb1.facts:
        print (f.count, f.statement)

    print ('\n*******************************  Rule Base After update **************************************\n')
    for r in kb1.rules:
        print(r.count, r.LHS, "====>", r.RHS)

    print ('\n*******************************  Why **************************************\n')

    result = kb1.kb_why(Statement(['flat', 'pyramid1']))
    print(result)
    for l in result:
        for fr in l:
            if type(fr) == Fact:
                print (fr.statement)
            else:
                print(fr.LHS, "====>", fr.RHS)

    # for f in kb1.facts:
    #     print (f.statement, "supported by", map(lambda x: printHelper(x), f.supported_by))


# def printHelper(fac_ru):
#     if type(fac_ru) == Fact:
#         return fac_ru.statement
#     else:
#         return fac_ru.LHS, "=====>", fac_ru.RHS