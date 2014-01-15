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
#import polya.main.terms as terms
#import polya.main.blackboard as blackboard
#import polya.polyhedron.poly_add_module as poly_add_module
#import polya.polyhedron.poly_mult_module as poly_mult_module
#import polya.fourier_motzkin.fm_add_module as fm_add_module
#import polya.fourier_motzkin.fm_mult_module as fm_mult_module
import polya.main.messages as messages
#import polya.main.function_module as function_module
import polya.main.formulas as formulas

from terms import Var, Vars, UVar, Func, Contradiction
from formulas import ForAll, Implies, And, Or, Not
from polya.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.polyhedron.poly_add_module import PolyAdditionModule
from polya.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.main.function_module import FunctionModule
from blackboard import Blackboard

def run(B, poly=None, debug=None):
    if poly:
        pa, pm = PolyAdditionModule(), PolyMultiplicationModule()
    else:
        pa, pm = FMAdditionModule(), FMMultiplicationModule()
    return run_modules(B, pa, pm)

def run_modules(B, *modules):
    try:
        id = B.identify()
        while len(B.get_new_info(id)) > 0:
            for m in modules:
                messages.announce(B.info_dump(), messages.DEBUG)
                m.update_blackboard(B)

        return False
    except Contradiction as e:
        messages.announce(e.msg, messages.ASSERTION)
        return True


def solve(*assertions):
    B = Blackboard()
    B.assert_comparisons(*assertions)
    return run(B)

def solve_poly(*assertions):
    B = Blackboard()
    B.assert_comparisons(*assertions)
    return run(B, poly=True)

class Solver:
    def __init__(self, assertions = list(), axioms = list(), poly = False):
        self.B = Blackboard()
        modules = []
        modules.append(PolyAdditionModule() if poly else FMAdditionModule())
        modules.append(PolyMultiplicationModule() if poly else FMMultiplicationModule())
        if len(axioms) > 0:
            modules = [FunctionModule(axioms)] + modules
            self.fm = modules[0]
        self.B.assert_comparisons(*assertions)
        self.modules = modules

    def check(self):
        return run_modules(self.B, *self.modules)

    def assert_comparison(self, c):
        self.B.assert_comparison(c)

    def assert_comparisons(self, *c):
        self.B.assert_comparisons(*c)

    def add_axiom(self, a):
        if self.fm:
            self.fm.add_axiom(a)
        else:
            self.modules = [FunctionModule([a])] + self.modules
            self.fm = self.modules[0]