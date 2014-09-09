####################################################################################################
#
# minumum_module.py
#
# Author:
# Jeremy Avigad
#
# The routine for learning facts about terms with min
#
#
####################################################################################################

import polya.main.terms as terms
import polya.main.messages as messages
import polya.main.formulas as formulas
import polya.util.timer as timer
import polya.util.num_util as num_util
import fractions
import copy


class MinimumModule:

    def __init__(self):
        pass

    def update_blackboard(self, B):
        messages.announce_module('minimum module')
        for i in range(B.num_terms):
            if isinstance(B.term_defs[i], terms.FuncTerm) and B.term_defs[i].func_name == 'minm':
                # t_i is of the form minm(...)
                args = B.term_defs[i].args
                # assert that t_i is le all of its arguments
                for a in args:
                    B.assert_comparison(terms.IVar(i) <= a)
                # if any argument is the smallest, t_i is equal to that
                if a in args:
                    if all((a is a1) or B.implies_comparison(a <= a1) for a1 in args):
                            B.assert_comparison(terms.IVar(i) == a)
                # see if any problem term is known to be less than all the arguments
                # TODO: note, we could also do this by adding clauses
                for j in range(B.num_terms):
                    if j != i:
                        if all(B.implies_comparison(terms.IVar(j) < a) for a in args):
                            B.assert_comparison(terms.IVar(j) < terms.IVar(i))
                        elif all(B.implies_comparison(terms.IVar(j) <= a) for a in args):
                            B.assert_comparison(terms.IVar(j) <= terms.IVar(i))

                        # if all(B.implies(j, terms.LT, a.coeff, a.term.index) for a in args):
                        #     B.assert_comparison(terms.IVar(j) < terms.IVar(i))
                        # elif all(B.implies(j, terms.LE, a.coeff, a.term.index) for a in args):
                        #     B.assert_comparison(terms.IVar(j) <= terms.IVar(i))