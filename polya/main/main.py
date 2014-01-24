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
import polya.main.messages as messages
import polya.polyhedron.lrs as lrs
import copy

# import polya.main.blackboard as blackboard
import polya.polyhedron.poly_add_module as poly_add_module
import polya.polyhedron.poly_mult_module as poly_mult_module
# import polya.polyhedron.lrs as lrs
import polya.fourier_motzkin.fm_add_module as fm_add_module
import polya.fourier_motzkin.fm_mult_module as fm_mult_module
# import polya.main.messages as messages
# import polya.main.function_module as function_module
# import polya.main.formulas as formulas
from terms import Var, Vars, UVar, Func, Contradiction
from formulas import Forall, Implies, And, Or, Not
from polya.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.polyhedron.poly_add_module import PolyAdditionModule
from polya.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.main.congruence_closure_module import CongClosureModule
from polya.main.function_module import FunctionModule
from blackboard import Blackboard


solver_options = ['fm', 'poly']
default_solver = 'none'
try:
    import cdd
    have_cdd = True
except Exception:
    have_cdd = False

if lrs.lrs_path and lrs.redund_path and have_cdd:
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
        global default_solver
        default_solver = s
    else:
        print "Error: {0!s} is not in the list of possible arithmetic solvers:"
        print 'solver options =', solver_options
        print


def run(B):
    if default_solver == 'poly':
        pa, pm = poly_add_module.PolyAdditionModule(), poly_mult_module.PolyMultiplicationModule()
    elif default_solver == 'fm':
        pa, pm = fm_add_module.FMAdditionModule(), fm_mult_module.FMMultiplicationModule()
    else:
        print 'Unsupported option:', default_solver
        return

    cm = CongClosureModule()

    return run_modules(B, cm, pa, pm)


def run_modules(B, *modules):
    """
    Given a blackboard B, iteratively runs the modules in modules until either a contradiction is
    found or no new information is learned.
    Returns True if a contradiction is found, False otherwise.
    """
    try:
        id = B.identify()
        while len(B.get_new_info(id)) > 0:
            for m in modules:
                messages.announce(B.info_dump(), messages.DEBUG)
                m.update_blackboard(B)

        return False
    except Contradiction as e:
        messages.announce(e.msg+"\n", messages.ASSERTION)
        return True


def solve(*assertions):
    """
    Given TermComparisons assertions, returns True if they are found to be inconsistent,
     false otherwise. Uses geometric methods if available, otherwise FM.
    """
    B = Blackboard()
    try:
        B.assert_comparisons(*assertions)
    except Contradiction as e:
        messages.announce(e.msg+"\n", messages.ASSERTION)
        return True
    return run(B)


class Solver:
    def __init__(self, assertions=list(), axioms=list(), modules=list()):
        """
        assertions: a list of TermComparisons to be asserted to the blackboard.
        axioms: a list of Axioms
        poly: True if the Solver should try to use the polyhedron modules
        """
        if not isinstance(assertions, list) or not isinstance(axioms, list):
            print 'Error: assertions and axioms must be passed as lists.'
            print 'Usage: Solver([assertions=list()[, axioms=list()[, poly=True]]])'
            raise Exception

        self.B = Blackboard()
        self.fm = None
        if len(modules) == 0:
            modules.append(CongClosureModule())
            if default_solver == 'poly':
                pa = poly_add_module.PolyAdditionModule()
                pm = poly_mult_module.PolyMultiplicationModule()
            elif default_solver == 'fm':
                pa = fm_add_module.FMAdditionModule()
                pm = fm_mult_module.FMMultiplicationModule()
            else:
                print 'Unsupported option:', default_solver
                raise Exception

            modules.extend([pa, pm])

            if len(axioms) > 0:
                modules = [FunctionModule(axioms)] + modules
                self.fm = modules[0]
        self.assert_comparisons(*assertions)
        self.modules = modules

    def set_modules(self, modules):
        self.modules = modules

    def check(self):
        """
        Searches for a contradiction in what has been asserted to the solver.
        Returns True if a contradiction is found, false otherwise.
        """
        return run_modules(self.B, *self.modules)

    def prove(self, claim):
        """
        Tries to establish the truth of TermComparison claim from what is already known.
        Returns true if claim follows from the current blackboard, false otherwise.
        """
        B = copy.deepcopy(self.B)
        a = terms.TermComparison(claim.term1, terms.comp_negate(claim.comp), claim.term2)
        try:
            B.assert_comparison(a)
        except Contradiction as e:
            messages.announce(e.msg, messages.ASSERTION)
            return True
        return run_modules(B, *self.modules)

    def assert_comparison(self, c):
        """
        Adds a single comparison to the Solver's blackboard.
        """
        try:
            self.B.assert_comparison(c)
        except Contradiction as e:
            messages.announce(e.msg, messages.ASSERTION)

    def assert_comparisons(self, *c):
        """
        Adds multiple comparisons to the Solver's blackboard.
        """
        try:
            self.B.assert_comparisons(*c)
        except Contradiction as e:
            messages.announce(e.msg, messages.ASSERTION)


    def add_axiom(self, a):
        """
        Adds an axiom to the solver, and instantiates a FunctionModule if necessary.
        """
        if self.fm:
            self.fm.add_axiom(a)
        else:
            self.modules = [FunctionModule([a])] + self.modules
            self.fm = self.modules[0]