####################################################################################################
#
# nth_root_module.py
#
# Author:
# Jeremy Avigad
#
# The module for learning facts about the nth root. Note that for each n, "NthRoot(n)" is a
#   different function
#
#
####################################################################################################

import polya.main.terms as terms
import polya.main.formulas as formulas
import polya.main.blackboard as blackboard
import polya.modules.axiom_module as function_module
import polya.main.messages as messages

from polya.main.main import Solver    # TODO: delete this after testing
import fractions


class NthRootModule:


    def __init__(self, am):
        """
        The nth_root module must be instantiated with a function module to add axioms to.
        """
        self.am = am

    def update_blackboard(self, B):
        """
        Adds axioms corresponding to each nth root function present.
        """
        messages.announce_module('nth root value module')

        nth_roots = []

        def is_nth_root_term(i):
            """
            Returns True if t_i is of the form abs(t_j).
            """
            return (isinstance(B.term_defs[i], terms.FuncTerm)
                        and isinstance(B.term_defs[i].func, terms.NthRoot))

        def root_degree(i):
            """
            If t_i is of the form NthRoot(n, t_j), returns n.
            """
            return B.term_defs[i].func.n

        nth_roots = set([root_degree(i) for i in range(B.num_terms) if is_nth_root_term(i)])
        x = terms.Var('x')
        for n in nth_roots:
            if n % 2 == 0:
                self.am.add_axiom(formulas.Forall([x], formulas.Implies(x >= 0,
                                                        terms.root(n, x) ** n == x)))
                self.am.add_axiom(formulas.Forall([x], formulas.Implies(x >= 0,
                                                        terms.root(n, x) >= 0)))
            else:
                self.am.add_axiom(formulas.Forall([x], terms.root(n, x) ** n == x))

if __name__ == '__main__':

    S = Solver()
    am = function_module.AxiomModule()
    m = NthRootModule(am)
    S.append_module(am)
    S.append_module(m)

    x, y, z, w, u = terms.Vars('x y z w u')

    # S.assume(y > 0)
    S.assume(x > y)
    S.assume((w * z) ** fractions.Fraction(2, 3) < u)
    S.prove(terms.root(3, x) > terms.root(3, y))



