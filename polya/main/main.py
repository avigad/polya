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

#import polya.main.terms as terms
import polya.main.messages as messages

import polya.modules.polyhedron.lrs as lrs
# import polya.modules.polyhedron.poly_add_module as poly_add_module
# import polya.modules.polyhedron.poly_mult_module as poly_mult_module
# import polya.modules.fourier_motzkin.fm_add_module as fm_add_module
# import polya.modules.fourier_motzkin.fm_mult_module as fm_mult_module
import polya.interface.solve_util as solve_util
import polya.interface.example as example

from terms import Var, Vars, UVar, Func, Contradiction, exp, log, minm, maxm, floor, ceil, root
from formulas import Forall, Implies, And, Or, Not
from polya.modules.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.modules.polyhedron.poly_add_module import PolyAdditionModule
from polya.modules.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.modules.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.modules.congruence_closure_module import CongClosureModule
from polya.modules.axiom_module import AxiomModule
from polya.modules.exponential_module import ExponentialModule
from polya.modules.absolute_value_module import AbsModule
from polya.modules.minimum_module import MinimumModule
from polya.modules.nth_root_module import NthRootModule
from polya.main.blackboard import Blackboard
from polya.interface.example import run_examples
from polya.main.messages import set_verbosity, quiet, modules, low, normal, debug


####################################################################################################
#
# System configuration
#
####################################################################################################

solver_options = ['fm', 'poly']
default_solver = 'none'
default_split_depth = 0
default_split_breadth = 0


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
    Prints information about the present components at verbosity level INFO.
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
    Sets the solver to a given method, s, in solver_options.
    """
    if s in solver_options:
        messages.announce('Setting solver type: {0!s}'.format(s), messages.INFO)
        global default_solver
        default_solver = s
    else:
        messages.announce('Error:{0!s} is not in the list of possible arithmetic solvers'.format(s),
                          messages.INFO)
        messages.announce('solver options = {0!s}'.format(solver_options), messages.INFO)

def set_split_defaults(split_depth, split_breadth):
    """
    Sets the default split depth and breadth.
    """
    global default_split_depth, default_split_breadth
    default_split_depth, default_split_breadth = split_depth, split_breadth


####################################################################################################
#
# Prepackaged solving methods
#
####################################################################################################


def solve(*assertions):
    """
    Runs the default modules on the given assertions, using default solver and split settings.
    Arguments:
     -- assertions: a list of TermComparisons, ie 5*x < 3*y

    Returns True if the assertions are contradictory, False otherwise.
    """
    return solve_util.solve(default_split_depth, default_split_breadth, default_solver, *assertions)


def run(B):
    """
    Runs the default modules on the given Blackboard object, using default solver and split
    settings.
    """
    return solve_util.run(B, default_split_depth, default_split_breadth, default_solver)


def Solver(assertions=list(), axioms=list(), modules=list(), split_depth=default_split_depth,
           split_breadth=default_split_breadth, solver_type=default_solver):
    """
    Instantiates a Solver object.
    Arguments:
     -- assertions: a list of TermComparisons to assert to the new Solver. Defaults to empty.
     -- axioms: a list of Axioms to assert to the Solver's axiom module. Defaults to empty.
     -- modules: a list of modules for the solver to use. Defaults to all available modules.
     -- split_depth: How many successive (cumulative) case splits to try.
     -- split_breadth: How many split options to consider.
     -- solver_type: 'fm' or 'poly' arithmetic.
    """
    return solve_util.Solver(split_depth, split_breadth, assertions, axioms, modules, solver_type)


def Example(hyps=None, conc=None, axioms=None, modules=None, omit=False, comment=None,
            split_depth=default_split_depth, split_breadth=default_split_breadth):
    """
    Instantiates an Example object. Used to create lists of test problems.
    Arguments:
     -- hyps: a list of TermComparisons, the hypotheses
     -- conclusion: a TermComparison, to try to derive. Defaults to False, ie, show hyps
       is contradictory.
     -- axioms: a list of extra axioms to use.
     -- modules: a list of modules to use. Defaults to all available modules.
     -- omit: the example will not run if omit=True. Defaults to False.
     -- comment: prints comment when the example is run.
     -- split_depth, split_depth: as in Solver.
    """
    return example.Example(hyps, conc, axioms, modules, omit, comment,
                           split_depth, split_breadth, default_solver)