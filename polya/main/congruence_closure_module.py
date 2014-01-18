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
import fractions


def equiv_class_from_bb(i, B):
    if B.implies(i, terms.EQ, 0, 0):
        comps = {j: 0 for j in B.zero_equalities}
        return EquivClass(i, comps)
    eqs = B.get_equalities()
    comps = {}
    for e in eqs:
        if e.term1.index == i:
            comps[e.term2.term.index] = e.term2.coeff
        elif e.term2.term.index == i:
            comps[e.term1.index] = fractions.Fraction(1, e.term2.term.coeff)
    return EquivClass(i, comps)

class ZeroException(Exception):
    pass

class EquivClass:
    def __init__(self, i, comps):
        """
        Creates the equivalence class of ti with data from B.
        """
        self.repr = i
        self.comps = comps

    def union(self, coeff, other):
        """
        Returns one equivalence class that represents self.repr = coeff * other.repr
        """
        if other.repr in self.comps and self.comps[other.repr != coeff]:
            raise ZeroException

        comps = self.comps

        for k in other.comps:
            if k in self.comps:
                icoeff, jcoeff = self.comps[k], other.comps[k]
                if coeff*jcoeff != icoeff:
                    raise ZeroException
                # otherwise, they match.
            else:
                comps[k] = coeff*other.comps[k]
        return EquivClass(self.repr, comps)


class CongClosureModule:

    def __init__(self, B):
        self.equiv_classes = []
        self.arg_map = {}