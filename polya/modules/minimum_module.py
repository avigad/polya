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
# import polya.main.formulas as formulas
import polya.util.timer as timer
# import polya.util.num_util as num_util
import polya.util.geometry as geometry
# import fractions
# import copy


class MinimumModule:

    def __init__(self):
        pass

    def update_blackboard(self, B):
        """
        Asserts identities about minm terms
        """
        messages.announce_module('minimum module')
        timer.start(timer.MINM)
        for i in range(B.num_terms):
            if isinstance(B.term_defs[i], terms.FuncTerm) and B.term_defs[i].func_name == 'minm':
                # t_i is of the form minm(...)
                args = B.term_defs[i].args
                # assert that t_i is le all of its arguments
                for a in args:
                    B.assert_comparison(terms.IVar(i) <= a)
                # see if we can infer the sign
                # TODO: optimize
                if all(B.implies_comparison(a > 0) for a in args):
                    B.assert_comparison(terms.IVar(i) > 0)
                elif all(B.implies_comparison(a >= 0) for a in args):
                    B.assert_comparison(terms.IVar(i) >= 0)
                if any(B.implies_comparison(a < 0) for a in args):
                    B.assert_comparison(terms.IVar(i) < 0)
                elif any(B.implies_comparison(a <= 0) for a in args):
                    B.assert_comparison(terms.IVar(i) <= 0)
                # see if any multiple of another problem term is known to be less than all the
                # arguments.
                for j in range(B.num_terms):
                    if  j != i:
                        comp_range = geometry.ComparisonRange(geometry.neg_infty, geometry.infty,
                                                              True, True, True)
                        for a in args:
                            new_comp_range = B.le_coeff_range(j, a.term.index, a.coeff)
                            comp_range = comp_range & new_comp_range
                            if comp_range.is_empty():
                                break
                        if not comp_range.is_empty():
                            if comp_range.lower.type == geometry.VAL:
                                c = comp_range.lower.val
                                if comp_range.lower_strict:
                                    B.assert_comparison(c * terms.IVar(j) < terms.IVar(i))
                                else:
                                    B.assert_comparison(c * terms.IVar(j) <= terms.IVar(i))
                            if comp_range.upper.type == geometry.VAL:
                                c = comp_range.upper.val
                                if comp_range.upper_strict:
                                    B.assert_comparison(c * terms.IVar(j) < terms.IVar(i))
                                else:
                                    B.assert_comparison(c * terms.IVar(j) <= terms.IVar(i))
        timer.stop(timer.MINM)

    def get_split_weight(self, B):
        return None
