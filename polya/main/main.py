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
import polya.polyhedron.lrs as lrs
import polya.fourier_motzkin.fm_add_module as fm_add_module
import polya.fourier_motzkin.fm_mult_module as fm_mult_module
import polya.main.messages as messages
import polya.main.function_module as function_module
import polya.main.formulas as formulas

from terms import Var, Vars, UVar, Func, Contradiction
from formulas import ForAll, Implies, And, Or, Not
from polya.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.polyhedron.poly_add_module import PolyAdditionModule
from polya.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.main.function_module import FunctionModule
from blackboard import Blackboard


solver_options = ['fm', 'poly']

if lrs.lrs_path and lrs.redund_path:
    default_solver = 'poly'
else:
    default_solver = 'fm'

def polya_set_solver_type(s):
    """Set the solver to a given method in
    solver_options
    
    Arguments:
    - `s`:
    """
    if s in solver_options:
        print "Setting solver type:", s
        print
        default_solver = s
    else:
        print "Error: {0!s} is not in the list of possible arithmetic solvers:"
        print 'solver options =', solver_options
        print


def run(B, debug=None):
    if default_solver == 'poly':
        pa, pm = poly_add_module.PolyAdditionModule(), poly_mult_module.PolyMultiplicationModule()
    elif default_solver == 'fm':
        pa, pm = fm_add_module.FMAdditionModule(), fm_mult_module.FMMultiplicationModule()
    else:
        print 'Unsupported option:', default_solver
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
    return run(B)

class Solver:
    def __init__(self, assertions = list(), axioms = list()):
        self.B = Blackboard()
        modules = []
        if default_solver == 'poly':
            pa, pm = poly_add_module.PolyAdditionModule(), poly_mult_module.PolyMultiplicationModule()
        elif default_solver == 'fm':
            pa, pm = fm_add_module.FMAdditionModule(), fm_mult_module.FMMultiplicationModule()
        else:
            print 'Unsupported option:', default_solver
        modules.append(pa)
        modules.append(pm)
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
