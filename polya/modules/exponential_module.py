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
import polya.main.messages as messages
import polya.main.formulas as formulas
import polya.util.timer as timer
#import polya.util.num_util as num_util
import fractions
#import copy
#from polya import *


def find_logs_with_arg(B, i):
    """
    B is a blackboard, i is an IVar index.
    Returns a list of pairs [(j, c)] such that t_j = log(c*t_i) in B.
    """
    return [(i, B.term_defs[i].args[0].coeff) for i in range(B.num_terms)
            if (isinstance(B.term_defs[i], terms.FuncTerm)
                and B.term_defs[i].func_name == 'log'
                and B.term_defs[i].args[0].term.index == i)]


def find_exps_with_arg(B, i):
    """
    B is a blackboard, i is an IVar index.
    Returns a list of pairs [(j, c)] such that t_j = exp(c*t_i) in B.
    """
    return [(i, B.term_defs[i].args[0].coeff) for i in range(B.num_terms)
            if (isinstance(B.term_defs[i], terms.FuncTerm)
                and B.term_defs[i].func_name == 'exp'
                and B.term_defs[i].args[0].term.index == i)]


def exp_factor_constant(B):
    """
    Takes a Blackboard B. For each i,
    If B.term_defs[i] is of the form exp(c*t), will declare that it is equal to exp(t)**c
    """
    exp_inds = [i for i in range(B.num_terms) if (isinstance(B.term_defs[i], terms.FuncTerm)
                                                  and B.term_defs[i].func == terms.exp)]
    for i in exp_inds:
        exponent = B.term_defs[i].args[0]
        if exponent.coeff != 1:
            # if exponent.coeff % 1 == 0:
            term2 = (terms.exp(exponent.term)**exponent.coeff).canonize()
            n = B.term_name(term2.term)
            B.assert_comparison(terms.IVar(i) == term2.coeff * n)
            # elif isinstance(exponent.coeff, fractions.Fraction):
            #     term2 = (terms.exp(
            #         fractions.Fraction(1, exponent.coeff.denominator)*exponent.term
            #     )**exponent.coeff.numerator).canonize()
            #     n = B.term_name(term2.term)
            #     B.assert_comparison(terms.IVar(i) == term2.coeff * n)
            # else:
            #     #todo: handle this case:
            #     raise Exception('Exponential module has tried to take a non-integer power')


def log_factor_exponent(B):
    """
    Takes a Blackboard B. Looks for terms of the form log(t**e), and asserts that they are equal to
    e*log(t).
    """
    log_inds = [i for i in range(B.num_terms) if (isinstance(B.term_defs[i], terms.FuncTerm)
                                                  and B.term_defs[i].func == terms.log)]

    for i in log_inds:
        coeff, t = B.term_defs[i].args[0].coeff, B.term_defs[B.term_defs[i].args[0].term.index]
        if (coeff == 1 and isinstance(t, terms.MulTerm)
             and len(t.args) == 1 and t.args[0].exponent != 1 and t.args[0].exponent != 0):
            B.assert_comparison(terms.IVar(i) == t.args[0].exponent * terms.log(t.args[0].term))


def exp_factor_sum(B):
    """
    Takes a Blackboard and a list of IVar indices, s.t. i in exp_inds implies B.term_defs[i] is an
    exponential function.
    Asserts a number of comparisons to B.
    If B.term_defs[i] is of the form exp(t_1 + ct_2 + ...), will declare that it is equal to
    exp(t_1)*exp(ct_2)*...
    """
    exp_inds = [i for i in range(B.num_terms) if (isinstance(B.term_defs[i], terms.FuncTerm)
                                                  and B.term_defs[i].func == terms.exp)]
    for i in exp_inds:
        coeff, t = B.term_defs[i].args[0].coeff, B.term_defs[B.term_defs[i].args[0].term.index]
        if isinstance(t, terms.AddTerm) and coeff == 1:
            margs = [B.term_name(terms.exp(a).canonize().term) for a in t.args]
            t2 = reduce(lambda x, y: x*y, margs, 1).canonize()
            n = B.term_name(t2.term)
            B.assert_comparison(terms.IVar(i) == t2.coeff * n)


# This was necessary before nth roots were added
# def exp_factor_sum(B):
#     """
#     Takes a Blackboard and a list of IVar indices, s.t. i in exp_inds implies B.term_defs[i] is an
#     exponential function.
#     Asserts a number of comparisons to B.
#     If B.term_defs[i] is of the form exp(t_1 + ct_2 + ...), will declare that it is equal to
#     exp(t_1)*exp(ct_2)*...
#     """
#     exp_inds = [i for i in range(B.num_terms) if (isinstance(B.term_defs[i], terms.FuncTerm)
#                                                   and B.term_defs[i].func_name == 'exp')]
#     for i in exp_inds:
#         coeff, t = B.term_defs[i].args[0].coeff, B.term_defs[B.term_defs[i].args[0].term.index]
#         if isinstance(t, terms.AddTerm):
#             cset = {coeff}
#             for a in t.args:
#                 cset.update([fractions.Fraction(c, a.term.index)
#                              for (i, c) in find_exps_with_arg(B, a.term.index)])
#
#             for c in cset:
#                 margs = [terms.exp(c*a) for a in t.args]
#                 t2 = reduce(lambda x, y: x*y, margs, 1).canonize()
#                 exp = fractions.Fraction(coeff, c)
#                 if exp.denominator == 1:
#                     B.assert_comparison(terms.IVar(i) == t2**exp)
#                 else:
#                     v = t2**exp.numerator
#                     B.assert_comparison(terms.IVar(i)**exp.denominator == v)

def log_factor_product(B):
    """
    Takes a Blackboard and looks for terms of the form log(a*b*...).
    Asserts that they are equal to log(a)+log(b)+...
    """
    log_inds = [i for i in range(B.num_terms) if (isinstance(B.term_defs[i], terms.FuncTerm)
                                                  and B.term_defs[i].func == terms.log)]
    for i in log_inds:
        coeff, t = B.term_defs[i].args[0].coeff, B.term_defs[B.term_defs[i].args[0].term.index]
        if coeff == 1 and isinstance(t, terms.MulTerm):
            margs = [terms.log(p.term**p.exponent) for p in t.args]
            t2 = reduce(lambda x, y: x+y, margs, 0).canonize()
            B.assert_comparison(terms.IVar(i) == t2)

class ExponentialModule:

    def __init__(self, am):
        """
        The exponential module must be instantiated with an axiom module to add axioms to.
        """
        self.am = am
        x, y = terms.Vars('x y')
        self.am.add_axiom(formulas.Forall([x], terms.exp(x) > 0))
        self.am.add_axiom(formulas.Forall([x], formulas.Implies(x >= 0, terms.exp(x) >= 1)))
        self.am.add_axiom(formulas.Forall([x], formulas.Implies(x > 0, terms.exp(x) > 1)))
        self.am.add_axiom(formulas.Forall([x, y],
                                          formulas.Implies(x < y, terms.exp(x) < terms.exp(y))))
        self.am.add_axiom(formulas.Forall([x, y],
                                          formulas.Implies(x <= y, terms.exp(x) <= terms.exp(y))))
        self.am.add_axiom(formulas.Forall([x, y],
                                          formulas.Implies(x != y, terms.exp(x) != terms.exp(y))))
        self.am.add_axiom(formulas.Forall([x], formulas.Implies(x >= 1, terms.log(x) >= 0)))
        self.am.add_axiom(formulas.Forall([x], formulas.Implies(x > 1, terms.log(x) > 0)))

    def update_blackboard(self, B):
        timer.start(timer.EXP)
        messages.announce_module('exponential module')
        exp_factor_constant(B)
        exp_factor_sum(B)
        log_factor_exponent(B)
        log_factor_product(B)
        timer.stop(timer.EXP)

    def get_split_weight(self, B):
        return None

if __name__ == '__main__':
    # B = blackboard.Blackboard()
    x, y, z, w, u, v = terms.Vars('x y z w u v')
    # B.assert_comparison(terms.exp(3*x) < 5*y)
    # B.assert_comparison(terms.exp(4*x + 3*y) < 0)
    # fm = function_module.AxiomModule()
    # ExponentialModule(fm).update_blackboard(B)
    # ExponentialModule(fm).update_blackboard(B)

    #s = Solver()
    #s.add(z > exp(x), w > exp(y))
    #s.prove(z**3 * w**2 > exp(3 * x + 2 * y))

    # s.add(0<x, x<y, u<v)
    # s.prove(2 * u + exp(1 + x + x**4) <= 2 * v + exp(1 + y + y**4))

