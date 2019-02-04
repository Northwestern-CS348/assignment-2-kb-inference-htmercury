import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB
        Args:
            fact (Fact) - Fact to be retracted
        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here
        if (fact in self.facts):
            f = self._get_fact(fact)

            # remove asserted fact if it is unsupported
            if (len(f.supported_by) == 0):
                self.facts.remove(f)

                # supported facts
                for sf in f.supports_facts:
                    for pair in sf.supported_by:
                        # remove pair if our f is in the pair (fact, rule)
                        if (f in pair):
                            sf.supported_by.remove(pair)
                    # handle remove of sf
                    self.kb_retract(sf)

                # supported rules
                for sr in f.supports_rules:
                    for pair in sr.supported_by:
                        # remove pair if our f is in the pair (fact, rule)
                        if (f in pair):
                            sr.supported_by.remove(pair)
                    # handle remove of sr
                    self.kb_retract(sr)
            # fact is supported
            else:
                f.asserted = False
        # rules should not be retracted and asserted rules cannot be removed
        elif (fact in self.rules and fact.asserted is False):
            r = self._get_rule(fact)

            # remove rule if it is unsupported
            if (len(r.supported_by) == 0):
                self.rules.remove(r)

                # supported facts
                for sf in r.supports_facts:
                    for pair in sf.supported_by:
                        # remove pair if our r is in the pair (fact, rule)
                        if (r in pair):
                            sf.supported_by.remove(pair)
                    # handle remove of sf
                    self.kb_retract(sf)

                # supported rules
                for sr in r.supports_rules:
                    for pair in sr.supported_by:
                        # remove pair if our r is in the pair (fact, rule)
                        if (r in pair):
                            sr.supported_by.remove(pair)
                    # handle remove of sr
                    self.kb_retract(sr)
        else:
            print('No matches')

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here       
        # check only first element of rule LHS against facts in KB
        check = match(fact.statement, rule.lhs[0])

        # if there is a match, add a new statement paired with bindings for that match
        if (check):
            pair = [fact, rule]

            if (len(rule.lhs) == 1):
                infer_s = instantiate(rule.rhs, check)
                infer_f = Fact(infer_s, supported_by=[pair])
                # check if exists
                if (infer_f in kb.facts):
                    infer_f = kb._get_fact(infer_f)
                # check if this pair (fact, rule) is in supported_by
                if pair not in infer_f.supported_by:
                    infer_f.supported_by.append(pair)
                # add the infer_f
                fact.supports_facts.append(infer_f)
                rule.supports_facts.append(infer_f)
                # add to kb if not already added
                if infer_f not in kb.facts:
                    kb.kb_assert(infer_f)
            else:
                # instantiate remaining lhs statements
                infer_lhs = list(map(lambda s: instantiate(s, check), rule.lhs[1:]))
                infer_rhs = instantiate(rule.rhs, check)
                infer_r = Rule([infer_lhs, infer_rhs], supported_by=[pair])
                # check if exists
                if (infer_r in kb.rules):
                    infer_r = kb._get_rule(infer_r)
                # check if this pair (fact, rule) is in supported_by
                if (pair not in infer_r.supported_by):
                    infer_r.supported_by.append(pair)
                # add the infer_r
                fact.supports_rules.append(infer_r)
                rule.supports_rules.append(infer_r)
                # add to kb if not already added
                if (infer_r not in kb.rules):
                    kb.kb_assert(infer_r)
