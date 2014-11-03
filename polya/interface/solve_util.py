####################################################################################################
#
# solve_util.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Contains prepackaged solving methods for Polya.
#
####################################################################################################

import polya.modules.polyhedron.poly_add_module as poly_add_module
import polya.modules.polyhedron.poly_mult_module as poly_mult_module
import polya.modules.fourier_motzkin.fm_add_module as fm_add_module
import polya.modules.fourier_motzkin.fm_mult_module as fm_mult_module
import polya.modules.congruence_closure_module as cc_module
import polya.modules.axiom_module as axiom_module
import polya.modules.absolute_value_module as abs_module
import polya.modules.nth_root_module as nth_root_module
import polya.modules.exponential_module as exp_module
import polya.modules.minimum_module as min_module
import polya.modules.builtins_module as builtins_module
import polya.main.formulas as formulas
import polya.main.messages as messages
import polya.main.blackboard as blackboard
import polya.main.terms as terms
import run_util


def run(B, split_depth, split_breadth, solver_type):
    """
    Given a blackboard B, runs the default modules  until either a contradiction is
    found or no new information is learned.
    Returns True if a contradiction is found, False otherwise.
    """
    s = Solver(split_depth, split_breadth, [], [], [], solver_type)
    s.B = B
    return s.check()


def solve(split_depth, split_breadth, solver_type, *assertions):
    """
    Given TermComparisons assertions, returns True if they are found to be inconsistent,
     false otherwise. Uses geometric methods if available, otherwise FM.
    """
    B = blackboard.Blackboard()
    try:
        B.assume(*assertions)
    except terms.Contradiction as e:
        messages.announce(e.msg+'\n', messages.ASSERTION)
        return True
    return run(B, split_depth, split_breadth, solver_type)


class Solver:

    def __init__(self, split_depth, split_breadth, assertions, axioms, modules, default_solver):
        """
        Instantiates a Solver object.
        Arguments:
         -- split_depth: How many successive (cumulative) case splits to try.
         -- split_breadth: How many split options to consider.
         -- assertions: a list of TermComparisons to assert to the new Solver. Defaults to empty.
         -- axioms: a list of Axioms to assert to the Solver's axiom module. Defaults to empty.
         -- modules: a list of modules for the solver to use. Defaults to all available modules.
         -- default_solver: 'fm' or 'poly' arithmetic.
        """
        if not isinstance(assertions, list) or not isinstance(axioms, list):
            messages.announce(
                'Error: assertions and axioms must be passed as lists.',
                messages.INFO)
            messages.announce(
                'Usage: Solver([assertions=list()[, axioms=list()[, poly=True]]])',
                messages.INFO)
            raise Exception

        self.B = blackboard.Blackboard()
        self.fm = None
        if len(modules) == 0:
            self.fm = axiom_module.AxiomModule(axioms)
            modules = [cc_module.CongClosureModule(), exp_module.ExponentialModule(self.fm)]
            modules.extend([abs_module.AbsModule(self.fm), min_module.MinimumModule(),
                            nth_root_module.NthRootModule(self.fm),
                            builtins_module.BuiltinsModule(self.fm), self.fm])
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
        else:
            self.fm = next([m for m in modules if isinstance(m, axiom_module.AxiomModule)], None)

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
        self.contradiction = run_util.run_modules(
            self.B, self.modules, self.split_depth, self.split_breadth
        )
        return self.contradiction

    def prove(self, claim):
        """
        Tries to establish the truth of TermComparison claim from what is already known.
        Returns true if claim follows from the current blackboard, false otherwise.
        Argument:
         -- claim: a TermComparison, ie 3*x > 2*y**2
        """
        if self.contradiction:
            return True

        a = terms.TermComparison(claim.term1, terms.comp_negate(claim.comp), claim.term2)
        try:
            B = run_util.copy_and_add(self.B, a)
        except terms.Contradiction as e:
            messages.announce(e.msg+'\n', messages.ASSERTION)
        else:
            return run_util.run_modules(B, self.modules, self.split_depth, self.split_breadth)

    def _assert_comparison(self, c):
        """
        Adds a single comparison to the Solver's blackboard.
        """
        try:
            self.B.assert_comparison(c)
        except terms.Contradiction as e:
            self.contradiction = True
            messages.announce(e.msg, messages.ASSERTION)

    def add(self, *c):
        """
        Adds multiple comparisons to the Solver's blackboard.
        """
        for item in c:
            if isinstance(item, formulas.Forall):
                self.add_axiom(item)
            else:
                try:
                    self.B.add(item)
                except terms.Contradiction as e:
                    self.contradiction = True
                    messages.announce(e.msg, messages.ASSERTION)

    def assume(self, *c):
        """
        Alias for add
        """
        self.add(*c)

    def add_axiom(self, a):
        """
        Adds an axiom to the solver, and instantiates a AxiomModule if necessary.
        """
        if self.fm:
            self.fm.add_axiom(a)
        else:
            self.modules = [axiom_module.AxiomModule([a])] + self.modules
            self.fm = self.modules[0]