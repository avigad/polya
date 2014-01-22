####################################################################################################
#
# congruence_closure_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# This module maintains a union-find structure for terms in Blackboard, which is currently only used
# for congruence closure. It should perhaps be integrated differently into Blackboard.
#
# Contains a set for each equality class (up to constant multiples) of terms, and tracks which terms
# appear as arguments to which function terms.
#
####################################################################################################

import polya.main.terms as terms
import polya.main.messages as messages
import polya.util.timer as timer
import fractions
import itertools


# def equiv_class_from_bb(i, B):
#     if B.implies(i, terms.EQ, 0, 0):
#         comps = {j: 0 for j in B.zero_equalities}
#         return EquivClass(i, comps)
#     eqs = B.get_equalities()
#     comps = {}
#     for e in eqs:
#         if e.term1.index == i:
#             comps[e.term2.term.index] = e.term2.coeff
#         elif e.term2.term.index == i:
#             comps[e.term1.index] = fractions.Fraction(1, e.term2.term.coeff)
#     return EquivClass(i, comps)
#
# class ZeroException(Exception):
#     pass
#
# class EquivClass:
#     def __init__(self, i, comps):
#         """
#         Creates the equivalence class of ti with data from B.
#         """
#         self.repr = i
#         self.comps = comps
#
#     def union(self, coeff, other):
#         """
#         Returns one equivalence class that represents self.repr = coeff * other.repr
#         """
#         if other.repr in self.comps and self.comps[other.repr != coeff]:
#             raise ZeroException
#
#         comps = self.comps
#
#         for k in other.comps:
#             if k in self.comps:
#                 icoeff, jcoeff = self.comps[k], other.comps[k]
#                 if coeff*jcoeff != icoeff:
#                     raise ZeroException
#                 # otherwise, they match.
#             else:
#                 comps[k] = coeff*other.comps[k]
#         return EquivClass(self.repr, comps)
#
#
# class CongClosureModule:
#
#     def __init__(self, B):
#         self.equiv_classes = []
#         self.arg_map = {}

class CongClosureModule:
    def __init__(self):
        pass

    def update_blackboard(self, B):
        def eq_func_terms(f1, f2):
            """
            Returns true if f1 and f2 have the same name and arity, and all args are equal.
            """
            if f1.func_name != f2.func_name or len(f1.args) != len(f2.args):
                return False
            for i in range(len(f1.args)):
                arg1, arg2 = f1.args[i], f2.args[i]
                if arg1.coeff == 0:
                    eq = B.implies(arg2.term.index, terms.EQ, 0, 0)
                else:
                    eq = B.implies(arg1.term.index, terms.EQ,
                                   fractions.Fraction(arg2.coeff, arg1.coeff), arg2.term.index)
                if not eq:
                    return False
            return True

        timer.start(timer.CCM)
        messages.announce_module('congruence closure module')

        func_classes = {}
        for i in (d for d in range(B.num_terms) if isinstance(B.term_defs[d], terms.FuncTerm)):
            name = B.term_defs[i].func_name
            func_classes[name] = func_classes.get(name, []) + [i]

        for name in func_classes:
            tinds = func_classes[name]
            for (i, j) in itertools.combinations(tinds, 2):
                # ti and tj are function terms with the same symbols. check if they're equal.
                f1, f2 = B.term_defs[i], B.term_defs[j]
                if eq_func_terms(f1, f2):
                    B.assert_comparison(terms.IVar(i) == terms.IVar(j))
        timer.stop(timer.CCM)