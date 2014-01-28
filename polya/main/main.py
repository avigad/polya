####################################################################################################
#
# main.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Contains the main module for running the Polya inequality prover, with some prepackaged
# solving methods.
#
####################################################################################################

from __future__ import division
import polya.main.terms as terms
import polya.main.messages as messages
import polya.polyhedron.lrs as lrs
import copy

import polya.polyhedron.poly_add_module as poly_add_module
import polya.polyhedron.poly_mult_module as poly_mult_module
import polya.fourier_motzkin.fm_add_module as fm_add_module
import polya.fourier_motzkin.fm_mult_module as fm_mult_module

from terms import Var, Vars, UVar, Func, Contradiction
from formulas import Forall, Implies, And, Or, Not
from polya.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.polyhedron.poly_add_module import PolyAdditionModule
from polya.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.main.congruence_closure_module import CongClosureModule
from polya.main.function_module import FunctionModule
from blackboard import Blackboard


####################################################################################################
#
# System configuration
#
####################################################################################################

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


def show_configuration():
    """
    Tell the user what components are present.
    """
    messages.announce('', messages.INFO)
    messages.announce('Welcome to the Polya inequality prover.', messages.INFO)
    messages.announce('Looking for components...', messages.INFO)
    if lrs.lrs_path is None:
        messages.announce('lrs not found.', messages.INFO)
    else:
        messages.announce('lrs found (path: {0!s}).'.format(lrs.lrs_path), messages.INFO)
    if lrs.redund_path is None:
        messages.announce('redund not found.', messages.INFO)
    else:
        messages.announce('redund found (path: {0!s}).'.format(lrs.redund_path), messages.INFO)
    if have_cdd:
        messages.announce('cdd found.', messages.INFO)
    else:
        messages.announce('cdd not found.', messages.INFO)
    messages.announce('', messages.INFO)


def set_solver_type(s):
    """
    Set the solver to a given method, s, in solver_options.
    """
    if s in solver_options:
        messages.announce('Setting solver type: {0!s}'.format(s), messages.INFO)
        global default_solver
        default_solver = s
    else:
        messages.announce('Error: {0!s} is not in the list of possible arithmetic '
                               'solvers'.format(s), messages.INFO)
        messages.announce('solver options = {0!s}'.format(solver_options))


####################################################################################################
#
# Prepackaged solving methods
#
####################################################################################################

def run(B):
    """
    Given a blackboard B, runs the default modules  until either a contradiction is
    found or no new information is learned.
    Returns True if a contradiction is found, False otherwise.
    """
    if default_solver == 'poly':
        pa, pm = poly_add_module.PolyAdditionModule(), poly_mult_module.PolyMultiplicationModule()
    elif default_solver == 'fm':
        pa, pm = fm_add_module.FMAdditionModule(), fm_mult_module.FMMultiplicationModule()
    else:
        messages.announce('Unsupported option: {0}'.format(default_solver), messages.INFO)
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
        mid = B.identify()
        while len(B.get_new_info(mid)) > 0:
            for m in modules:
                messages.announce(B.info_dump(), messages.DEBUG)
                m.update_blackboard(B)
        return False
    except Contradiction as e:
        messages.announce(e.msg+'\n', messages.ASSERTION)
        return True


def solve(*assertions):
    """
    Given TermComparisons assertions, returns True if they are found to be inconsistent,
     false otherwise. Uses geometric methods if available, otherwise FM.
    """
    B = Blackboard()
    try:
        B.assume(*assertions)
    except Contradiction as e:
        messages.announce(e.msg+'\n', messages.ASSERTION)
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
            messages.announce('Error: assertions and axioms must be passed as lists.',
                              messages.INFO)
            messages.announce('Usage: Solver([assertions=list()[, axioms=list()[, poly=True]]])',
                              messages.INFO)
            raise Exception

        self.B = Blackboard()
        self.fm = None
        if len(modules) == 0:
            modules = [CongClosureModule()]
            if default_solver == 'poly':
                pa = poly_add_module.PolyAdditionModule()
                pm = poly_mult_module.PolyMultiplicationModule()
            elif default_solver == 'fm':
                pa = fm_add_module.FMAdditionModule()
                pm = fm_mult_module.FMMultiplicationModule()
            else:
                messages.announce('Unsupported option: {0}'.format(default_solver),
                                  messages.INFO)
                raise Exception

            modules.extend([pa, pm])

            if len(axioms) > 0:
                modules = [FunctionModule(axioms)] + modules
                self.fm = modules[0]
        self.assume(*assertions)
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

    def _assert_comparison(self, c):
        """
        Adds a single comparison to the Solver's blackboard.
        """
        try:
            self.B.assert_comparison(c)
        except Contradiction as e:
            messages.announce(e.msg, messages.ASSERTION)

    def add(self, *c):
        """
        Adds multiple comparisons to the Solver's blackboard.
        """
        # TODO: this is a hack!
        if len(c) > 0 and isinstance(c[0], Forall):
            for a in c:
                self.add_axiom(a)
        else:
            try:
                self.B.add(*c)
            except Contradiction as e:
                messages.announce(e.msg, messages.ASSERTION)

    def assume(self, *c):
        self.add(*c)

    def add_axiom(self, a):
        """
        Adds an axiom to the solver, and instantiates a FunctionModule if necessary.
        """
        if self.fm:
            self.fm.add_axiom(a)
        else:
            self.modules = [FunctionModule([a])] + self.modules
            self.fm = self.modules[0]
