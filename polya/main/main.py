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
import copy
import itertools

import polya.main.terms as terms
import polya.main.messages as messages

import polya.modules.polyhedron.lrs as lrs
import polya.modules.polyhedron.poly_add_module as poly_add_module
import polya.modules.polyhedron.poly_mult_module as poly_mult_module
import polya.modules.fourier_motzkin.fm_add_module as fm_add_module
import polya.modules.fourier_motzkin.fm_mult_module as fm_mult_module

from terms import Var, Vars, UVar, Func, Contradiction, exp, log, minm, maxm, floor, ceil, root
from formulas import Forall, Implies, And, Or, Not
from polya.modules.polyhedron.poly_mult_module import PolyMultiplicationModule
from polya.modules.polyhedron.poly_add_module import PolyAdditionModule
from polya.modules.fourier_motzkin.fm_add_module import FMAdditionModule
from polya.modules.fourier_motzkin.fm_mult_module import FMMultiplicationModule
from polya.modules.congruence_closure_module import CongClosureModule
from polya.modules.axiom_module import AxiomModule
from polya.modules.exponential_module import ExponentialModule
from polya.modules.abs_module import AbsModule
from polya.modules.minimum_module import MinimumModule
from polya.modules.nth_root_module import NthRootModule
from blackboard import Blackboard, set_default_seed


####################################################################################################
#
# System configuration
#
####################################################################################################

solver_options = ['fm', 'poly']
default_solver = 'none'
default_split_depth = 0
default_split_breadth = 0
default_seed = 7
set_default_seed(default_seed)


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
        messages.announce('solver options = {0!s}'.format(solver_options), messages.INFO)


####################################################################################################
#
# Prepackaged solving methods
#
####################################################################################################

def copy_and_add(B, *comps):
    """Create a copy of the blackboard B, and
    add comps to it, return this new blackboard if no inconsistency is
    immediately raised, return None otherwise.
    Arguments:
    - `B`: an instance of Blackboard
    - `a`: an instance of 
    """
    new_B = copy.deepcopy(B)
    new_B.add(*comps)
    return new_B


def run(B, split_depth, split_breadth):
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
    return run_modules(B, [cm, pa, pm], split_depth, split_breadth)


def saturate_modules(B, modules):
    """Run the modules in succession on B until saturation
    
    Arguments:
    - `B`: a blackboard
    - `modules`: a list of modules
    """
    mid = B.identify()
    while len(B.get_new_info(mid)) > 0:
        for m in modules:
            messages.announce(B.info_dump(), messages.DEBUG)
            m.update_blackboard(B)


def knows_split(B, i, j, comp, c):
    """
    Returns True if B knows either t_i = c*t_j, t_i > c*t_j, or t_i < c*t_j
    """
    return B.implies(i, comp, c, j) or B.implies(i, terms.comp_negate(comp), c, j)
    #return B.implies(i, terms.EQ, c, j) or B.implies(i, terms.GT, c, j) \
    #    or B.implies(i, terms.LT, c, j)


def get_splits(B, modules):
    """
    Asks each module for a list of comparisons it would like to see.
    Adds up this information and returns a list of tuples (i, j, c), ordered so that splitting
    on t_i <> c*t_j is most desirable for those that come earlier.
    """
    splits = {}
    for m in modules:
        l = m.get_split_weight(B)
        if l is not None:
            for (i, j, c, comp, w) in l:
                splits[i, j, comp, c] = splits.get((i, j, comp, c), 0) + w

    slist = [q for q in sorted(splits.keys(), key=lambda p: (-splits[p], p[0]))
             if splits[q] > 0 and not knows_split(B, q[0], q[1], q[2], q[3])]

    return slist


def split_modules(B, modules, depth, breadth, saturate=True):
    """
    B is a blackboard.
    modules is a list of modules.
    depth restricts how many subsequent splits will be performed: ie, if depth=2, will assume x>0
     and y>0, but won't assume z>0 on top of that.
    breadth restricts how many splits will be considered at each depth. ie, if depth=1, breadth=3,
     will try the three most promising splits separately. If depth=2, breadth=3, will try the three
     most promising splits determined after each of the three most promising preliminary splits.
    """
    #print 'SPLITTING: depth=', depth
    if saturate:
        saturate_modules(B, modules)
    if depth <= 0:
        return B
    else:
        backup_bbds = {}
        backup_modules = {}
        candidates = get_splits(B, modules)[:breadth]
        for i in range(len(candidates)):
            can = candidates[i]
            print 'Assuming:t{0} {1} {2}*{3}'.format(can[0], terms.comp_str[can[2]], can[3], can[1])
            ti, tj = terms.IVar(can[0]), can[3]*terms.IVar(can[1])
            comp = can[2]

            backup_bbds[i, comp] = copy.deepcopy(B)
            backup_modules[i, comp] = copy.deepcopy(modules)
            gtsplit = False
            try:
                #print 'ASSUMING {0} > {1}, where {0} is {2}'.format(ti, tj, B.term_defs[ti.index])
                backup_bbds[i, comp].assert_comparison(terms.comp_eval[comp](ti, tj))
                gtsplit = run_modules(backup_bbds[i, comp], backup_modules[i, comp], 0, 0)
            except Contradiction:
                gtsplit = True

            if gtsplit:
                #print 'DETERMINED {0} <= {1}'.format(ti, tj)
                B.assert_comparison(terms.comp_eval[terms.comp_negate(comp)](ti, tj))
                return split_modules(B, modules, depth, breadth)

            # # no contradiction was found assuming >.
            # backup_bbds[i, terms.LT] = copy.deepcopy(B)
            # backup_modules[i, terms.LT] = copy.deepcopy(modules)
            # ltsplit = False
            # try:
            #     #print 'ASSUMING {0} < {1}, where {0} is {2}'.format(ti, tj, B.term_defs[ti.index])
            #     backup_bbds[i, terms.LT].assert_comparison(ti < tj)
            #     ltsplit = run_modules(backup_bbds[i, terms.LT], backup_modules[i, terms.LT], 0, 0)
            # except Contradiction:
            #     ltsplit = True
            #
            # if ltsplit:
            #     #print 'DETERMINED {0} >= {1}'.format(ti, tj)
            #     B.assert_comparison(ti >= tj)
            #     return split_modules(B, modules, depth, breadth)

        # at this point, none of the depth-1 splits have returned any useful information.
        for (i, c) in backup_bbds.keys():
            #itertools.product(range(len(candidates)), [terms.GT, terms.LT]):
            # print i, c
            # print backup_bbds[i, c]
            # print backup_modules[i, c]
            split_modules(backup_bbds[i, c], backup_modules[i, c], depth-1, breadth, saturate=False)


def run_modules(B, modules, depth, breadth):
    """
    Given a blackboard B, iteratively runs the modules in modules until either a contradiction is
    found or no new information is learned.
    Returns True if a contradiction is found, False otherwise.
    """
    try:
        split_modules(B, modules, depth, breadth)
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
    return run(B, default_split_depth, default_split_breadth)


class Solver:

    def __init__(self, assertions=list(), axioms=list(), modules=list(),
                 split_depth=default_split_depth, split_breadth=default_split_breadth):
        """
        assertions: a list of TermComparisons to be asserted to the blackboard.
        axioms: a list of Axioms
        poly: True if the Solver should try to use the polyhedron modules
        """
        if not isinstance(assertions, list) or not isinstance(axioms, list):
            messages.announce(
                'Error: assertions and axioms must be passed as lists.',
                messages.INFO)
            messages.announce(
                'Usage: Solver([assertions=list()[, axioms=list()[, poly=True]]])',
                messages.INFO)
            raise Exception

        self.B = Blackboard()
        self.fm = None
        if len(modules) == 0:
            self.fm = AxiomModule(axioms)
            modules = [CongClosureModule(), ExponentialModule(self.fm)]
            modules.extend([AbsModule(self.fm), MinimumModule(), NthRootModule(self.fm), self.fm])
            if default_solver == 'poly':
                pa = poly_add_module.PolyAdditionModule()
                pm = poly_mult_module.PolyMultiplicationModule()
            elif default_solver == 'fm':
                pa = fm_add_module.FMAdditionModule()
                pm = fm_mult_module.FMMultiplicationModule()
            else:
                messages.announce(
                    'Unsupported option: {0}'.format(default_solver),
                    messages.INFO)
                raise Exception

            modules.extend([pa, pm])

        self.contradiction = False
        self.assume(*assertions)
        self.modules = modules
        self.split_depth, self.split_breadth = split_depth, split_breadth

    def set_modules(self, modules):
        self.modules = modules

    def append_module(self, m):
        self.modules.append(m)

    def check(self):
        """
        Searches for a contradiction in what has been asserted to the solver.
        Returns True if a contradiction is found, false otherwise.
        """
        if self.contradiction:
            return True
        self.contradiction = run_modules(self.B, self.modules, self.split_depth, self.split_breadth)
        return self.contradiction

    def prove(self, claim):
        """
        Tries to establish the truth of TermComparison claim from what is already known.
        Returns true if claim follows from the current blackboard, false otherwise.
        """
        if self.contradiction:
            return True

        a = terms.TermComparison(claim.term1, terms.comp_negate(claim.comp), claim.term2)
        try:
            B = copy_and_add(self.B, a)
        except Contradiction as e:
            messages.announce(e.msg+'\n', messages.ASSERTION)
        else:
            return run_modules(B, self.modules, self.split_depth, self.split_breadth)

    def _assert_comparison(self, c):
        """
        Adds a single comparison to the Solver's blackboard.
        """
        try:
            self.B.assert_comparison(c)
        except Contradiction as e:
            self.contradiction = True
            messages.announce(e.msg, messages.ASSERTION)

    def add(self, *c):
        """
        Adds multiple comparisons to the Solver's blackboard.
        """
        for item in c:
            if isinstance(item, Forall):
                self.add_axiom(item)
            else:
                try:
                    self.B.add(item)
                except Contradiction as e:
                    self.contradiction = True
                    messages.announce(e.msg, messages.ASSERTION)

    def assume(self, *c):
        self.add(*c)

    def add_axiom(self, a):
        """
        Adds an axiom to the solver, and instantiates a AxiomModule if necessary.
        """
        if self.fm:
            self.fm.add_axiom(a)
        else:
            self.modules = [AxiomModule([a])] + self.modules
            self.fm = self.modules[0]
