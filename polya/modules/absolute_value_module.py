####################################################################################################
#
# absolute_value_module.py
#
# Author:
# Jeremy Avigad
#
# The module for learning facts about absolute values.
#
#
####################################################################################################

import polya.main.terms as terms
import polya.main.formulas as formulas
import polya.main.blackboard as blackboard
import polya.modules.axiom_module as function_module
import polya.main.messages as messages
import polya.util.timer as timer



class AbsModule:


    def __init__(self, am):
        """
        The abs module must be instantiated with a function module to add axioms to.
        """
        self.am = am
        x = terms.Var('x')
        self.am.add_axiom(formulas.Forall([x], terms.abs_val(x) >= 0))
        self.am.add_axiom(formulas.Forall([x], terms.abs_val(x) >= x))
        self.am.add_axiom(formulas.Forall([x], terms.abs_val(x) >= -x))
        self.am.add_axiom(formulas.Forall([x], formulas.Implies(x >= 0, terms.abs_val(x) == x)))
        self.am.add_axiom(formulas.Forall([x], formulas.Implies(x <= 0, terms.abs_val(x) == -x)))

    def update_blackboard(self, B):
        """
        Adds variations on the triangle inequality.
        Looks for expressions abs(c1 * t1 + ... + ck * tk) for which each ti either
        occurs in an abs term, or has a known sign. In that case, adds inequalities corresponding
        to

            abs(c1 * t1 + ... + ck * tk) <= abs(c1 * t1) + ... + abs(ck * tk)
            abs(c1 * t1 + ... + ck * tk) >= abs(cj * tj) - (abs(c1 * t1) + ... + abs(ck * tk))

        """
        messages.announce_module('absolute value module')
        timer.start(timer.ABS)

        def is_abs_term(i):
            """
            Returns True if t_i is of the form abs(t_j).
            """
            return (isinstance(B.term_defs[i], terms.FuncTerm)
                                                      and B.term_defs[i].func_name == 'abs')

        def abs_arg_index(i):
            """
            If t_i is of the form abs(t_j), returns j.
            """
            return B.term_defs[i].args[0].term.index

        def is_sum_term(i):
            """
            Return True if t_i is a sum.
            """
            return isinstance(B.term_defs[i], terms.AddTerm)

        def sum_args(i):
            """
            Assuming t_i is a sum, returns the arguments.
            """
            return B.term_defs[i].args

        # indices i of terms t_i of the form abs(t_j)
        abs_indices = [i for i in range(B.num_terms) if is_abs_term(i)]
        # indices j of terms occurring in the context abs(t_j)
        abs_wrapped_indices = [abs_arg_index(i) for i in abs_indices]
        # indices of terms of the form abs(c1 * t1 + ... + ck * tk)
        abs_sum_indices = [i for i in abs_indices if is_sum_term(abs_arg_index(i))]

        def abs_present(i):
            """
            Returns True if t_i occurs in the context abs(t_i) or has known sign, which is to say,
            something equivalent to abs(t_i) is already a problem term.
            """
            return i in abs_wrapped_indices or B.weak_sign(i) == 1 or B.weak_sign(i) == -1

        def abs_of(i):
            """
            Assuming abs_present(i), returns an expression equal to abs(t_i).
            """
            if B.weak_sign(i) == 1:
                return terms.IVar(i)
            elif B.weak_sign(i) == -1:
                return terms.IVar(i) * -1
            else:
                return terms.IVar(next(j for j in abs_indices if abs_arg_index(j) == i))

        for i in abs_sum_indices:
            args = sum_args(abs_arg_index(i))
            if all(abs_present(a.term.index) for a in args):
                abs_of_args = [a.coeff * abs_of(a.term.index) for a in args]
                sum_of_abs_of_args = reduce(lambda x, y: x + y, abs_of_args, 0)
                B.assert_comparison(terms.IVar(i) <= sum_of_abs_of_args)
                for a in abs_of_args:
                    B.assert_comparison(terms.IVar(i) >= a * 2 - sum_of_abs_of_args)

        timer.stop(timer.ABS)

    def get_split_weight(self, B):
        return None


if __name__ == '__main__':
    pass
#     S = Solver()
#     am = function_module.AxiomModule()
#     m = AbsModule(am)
#     S.append_module(am)
#     S.append_module(m)
#
#     x, y, z, w = terms.Vars('x y z w')
# #    S.prove(abs(3 * x + 2 * y) <= 3 * abs(x) + 4 * abs(y))
#
#     S.assume(y > 0)
#     S.prove(abs(3 * x + 2 * y + 5) < 4 * abs(x) + 3 * y + 4)

#    S.prove(abs(x - y) >= abs(y) - abs(x))



