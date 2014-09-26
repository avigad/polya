####################################################################################################
#
# exponential_module.py
#
# Author:
# Rob Lewis
#
# The routine for learning facts about exponential functions
#
#
####################################################################################################

import polya.main.terms as terms
import polya.main.formulas as formulas
import polya.main.blackboard as blackboard
import polya.modules.function_module as function_module


class ExponentialModule:


    def __init__(self, fm):
        """
        The exponential module must be instantiated with a function module to add axioms to.
        """
        self.fm = fm
        x, y = terms.Vars('x y')
        self.fm.add_axiom(formulas.Forall([x], terms.exp(x) > 0))
        self.fm.add_axiom(formulas.Forall([x, y],
                                          formulas.Implies(x < y, terms.exp(x) < terms.exp(y))))
        self.fm.add_axiom(formulas.Forall([x, y],
                                          formulas.Implies(x != y, terms.exp(x) != terms.exp(y))))

    def update_blackboard(self, B):
        exp_inds = [i for i in range(B.num_terms) if (isinstance(B.term_defs[i], terms.FuncTerm)
                                                      and B.term_defs[i].func_name=='exp')]
        for i in exp_inds:
            exponent = B.term_defs[i].args[0]
            if exponent.coeff != 1:
                term2 = (terms.exp(exponent.term)**exponent.coeff).canonize()
                n = B.term_name(term2.term)
                B.assert_comparison(terms.IVar(i) == term2.coeff * n)

if __name__ == '__main__':
    B = blackboard.Blackboard()
    x, y = terms.Vars('x y')
    B.assert_comparison(terms.exp(3*x)<5*y)
    fm = function_module.FunctionModule()
    ExponentialModule(fm).update_blackboard(B)