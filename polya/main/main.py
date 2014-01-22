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

from terms import Var, Vars, UVar, Func, Contradiction
from formulas import ForAll, Implies, And, Or, Not
from polya.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.polyhedron.poly_add_module import PolyAdditionModule
from polya.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.main.congruence_closure_module import CongClosureModule
from polya.main.function_module import FunctionModule
from blackboard import Blackboard


def run(B, poly=True):
    """
    Given a blackboard B, iteratively runs arithmetical modules until either a contradiction is
    found or no new information is learned.
    If poly is True, tries to use geometric methods. Otherwise, uses FM.
    Returns True if a contradiction is found, False otherwise.
    """
    if not lrs.lrs_path:
        poly = False
    if poly:
        pa, pm = PolyAdditionModule(), PolyMultiplicationModule()
    else:
        pa, pm = FMAdditionModule(), FMMultiplicationModule()

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
        messages.announce(e.msg, messages.ASSERTION)
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
        messages.announce(e.msg, messages.ASSERTION)
        return True
    return run(B)


def solve_poly(*assertions):
    B = Blackboard()
    try:
        B.assert_comparisons(*assertions)
    except Contradiction as e:
        messages.announce(e.msg, messages.ASSERTION)
        return True
    return run(B, poly=True)


def solve_fm(*assertions):
    B = Blackboard()
    try:
        B.assert_comparisons(*assertions)
    except Contradiction as e:
        messages.announce(e.msg, messages.ASSERTION)
        return True
    return run(B, poly=False)


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
        if len(modules) == 0:
            modules.append(CongClosureModule())
            modules.append(PolyAdditionModule() if lrs.lrs_path else FMAdditionModule())
            modules.append(PolyMultiplicationModule() if lrs.lrs_path else FMMultiplicationModule())
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