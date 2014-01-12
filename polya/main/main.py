####################################################################################################
#
# main.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Contains the main module for running the Polya solver engine.
#
#
####################################################################################################

from __future__ import division
import polya.main.terms as terms
import polya.main.blackboard as blackboard
import polya.polyhedron.poly_add_module as poly_add_module
import polya.polyhedron.poly_mult_module as poly_mult_module
import polya.fourier_motzkin.addition_module as fm_add_module
import polya.main.messages as messages
import polya.main.function_module as function_module
import polya.main.formulas as formulas

from terms import Vars, UVar, Func, Contradiction
from formulas import ForAll, Implies
from blackboard import Blackboard

def run(B, poly=None, debug=None):
    if poly:
        pa, pm = poly_add_module.PolyAdditionModule(), poly_mult_module.PolyMultiplicationModule()
    else:
        pa, pm = fm_add_module.FMAdditionModule(), poly_mult_module.PolyMultiplicationModule()
    try:
        s, s2 = '', '1'
        while s != s2:
            s = s2
            if debug:
                B.info_dump()
            pa.update_blackboard(B)
            if debug:
                B.info_dump()
            pm.update_blackboard(B)
            s2 = str(B.get_equalities()) + str(B.get_disequalities()) + str(B.get_inequalities())
        return False
    except terms.Contradiction as e:
        if debug:
            print e.msg
            print
        messages.announce(e.msg, messages.ASSERTION)
        return True


def solve(*assertions):
    B = blackboard.Blackboard()
    B.assert_comparisons(*assertions)
    return run(B)
