####################################################################################################
#
# fourier_motzkin/fm_mult_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The Fourier-Motzkin based routine to learn multiplicative comparisons.
#
# Uses general methods for handling multiplication and learning signs in poly_mult_module.py.

# TODO: reorganize the code into separate files, combine directories?
#
####################################################################################################


import polya.main.terms as terms
import polya.main.messages as messages
import polya.polyhedron.poly_mult_module as poly_mult_module
import fractions


class Error(Exception):
    pass


class Multiplicand():
    """
    Represents a term of the form IVar(index) ^ exp.
    """

    def __init__(self, index, exp):
        self.index = index
        self.exp = exp

    def __pow__(self, exp):
        return Multiplicand(self.index, exp * self.exp)

    def __str__(self):
        return 't{0!s}^{1!s}'.format(self.index, self.exp)

    def __repr__(self):
        return self.__str__()


class Product():
    """
    Represents a constant coefficient times a product of Multiplicands, possibly empty or with
    only one argument. Here and throughout the coefficient is assumed to be positive.
    """

    def __init__(self, coeff, args):
        self.coeff = coeff
        self.args = args

    def __pow__(self, exp):
        return Product(self.coeff ** exp, [m ** exp for m in self.args])

    def __mul__(self, other):
        result = []
        for a in self.args:
            try:
                s = next(s for s in other.args if s.index == a.index)
                if s.exp != -a.exp:
                    result.append(Multiplicand(a.index, a.exp + s.exp))
            except StopIteration:
                result.append(a)
        for b in other.args:
            if not b.index in (a.index for a in self.args):
                result.append(b)
        return Product(self.coeff * other.coeff, result)

    def __str__(self):
        if self.coeff == 1:
            if len(self.args) == 1:
                return '1'
            else:
                return '*'.join([str(a) for a in self.args])
        else:
            if len(self.args) == 1:
                return '1'
            else:
                return '{0!s}*{1}'.format(self.coeff,'*'.join([str(a) for a in self.args]))

    def __repr__(self):
        return self.__str__()

    def contains(self, v):
        """
        Determines whether index v occurs in the sum.
        """
        print self, v
        return v in (a.index for a in self.args)


class OneComparison():
    """
    Stores a comparison s > 1 (strong) or s >= 1 (weak).
    """

    def __init__(self, term, strong):
        self.term = term
        self.strong = strong

    def __str__(self):
        if self.strong:
            return '{0!s} > 1'.format(self.term)
        else:
            return '{0!s} >= 1'.format(self.term)

    def __repr__(self):
        return self.__str__()


def cast_to_product(term):
    """
    Represents any multiplicative term built up from IVars as a Sum.
    """
    if isinstance(term, terms.STerm):
        coeff = term.coeff
        term = term.term
    else:
        coeff = 1
    if isinstance(term, terms.IVar):
        if term.index == 0:
            args = []
        else:
            args = Multiplicand(term.index, 1)
    elif isinstance(term, terms.MulTerm):
        args = [(Multiplicand(a.index, a.exp) for a in term.args)]
    else:
        Error('Cannot cast {0!s} to a product'.format(term))
    return Product(coeff, args)


def multiplicand_to_mulpair(m):
    return terms.MulPair(terms.IVar(m.index), m.exp)


def trivial_eq(e):
    """
    Assumes e is a Product.
    Determine whether e == 1 is the trivial equality 1 == 1
    """
    return e.coeff == 1 and len(e.args) == 0


def trivial_ineq(c):
    """
    Assumes c is a OneComparison.
    Determines whether c is the trivial inequality 1 >= 1
    """
    return c.term.coeff == 0 and len(c.term.args) == 0 and not c.strong


def elim_eq_eq(t1, t2, v):
    """
    Takes Products t1 and t2 and an index v, where v occurs in t2.
    Uses t2 = 1 to eliminate v from t1 = 1, raising t1 to a positive power.
    """
    try:
        m1 = next(m for m in t1.args if m.index == v)
    except StopIteration:
        return t1
    try:
        m2 = next(m for m in t2.args if m.index == v)
    except StopIteration:
        raise Error('elim_eq_eq: IVar t{0!s} does not occur in {1!s}'.format(v, t2))
    exp1, exp2 = m1.exp, m2.exp
    scale1 = abs(exp2 / fractions.gcd(exp1, exp2))
    scale2 = -(exp1 * scale1) / exp2
    return t1 ** scale1 * t2 ** scale2


def elim_ineq_eq(c, t, v):
    """
    Takes a OneComparison c, a Product t, and a variable, v.
    Uses t = 1 to eliminate v from c.
    """
    t1 = elim_eq_eq(c.term, t, v)
    return OneComparison(t1, c.strong)


def elim_ineq_ineq(c1, c2, v):
    """
    Takes two OneComparisons, c1, and c2, and a variable, v,
    Assumes v occurs in both with exponents with opposite signs.
    Returns the result of eliminating v.
    """
    t1, t2 = c1.term, c2.term
    try:
        m1 = next(m for m in t1.args if m.index == v)
        m2 = next(m for m in t2.args if m.index == v)
    except StopIteration:
        raise Error('ineq_ineq_elim: variable {0!s} does not occur'.format(v))
    exp1, exp2 = m1.exp, m2.exp
    scale1 = abs(exp2 / fractions.gcd(exp1, exp2))
    scale2 = -(exp1 * scale1) / exp2
    if scale2 < 0:
        raise Error('ineq_ineq_elim: exponents of {0!s} have the same sign'.format(v))
    return OneComparison(t1 ** scale1 * t2 ** scale2, c1.strong or c2.strong)


def elim(one_equations, one_comparisons, v):
    """
    The main additive elimination routine.
    Takes a list of zero equations, a list of zero comparisons, and a variable v.
    Returns a new list of zero equations and a new list of zero comparisons in which v has
    been eliminated.
    """

    # If one of the equations contains v, take the shortest such one and use that to eliminate v
    short = None
    for e in one_equations:
        if e.contains(v) and (not short or len(e.args) < len(short.args)):
            short = e
    if short:
        new_equations, new_comparisons = [], []
        for e in one_equations:
            if e != short:
                e1 = elim_eq_eq(e, short, v)
                if not trivial_eq(e1):
                    new_equations.append(e1)
        for c in one_comparisons:
            c1 = elim_ineq_eq(c, short, v)
            if not trivial_ineq(c1):
                new_comparisons.append(c1)
        return new_equations, new_comparisons

    # Otherwise, do elimination on the inequalities
    pos_comparisons = []  # v occurs with positive exponent
    neg_comparisons = []  # v occurs with negative exponent
    new_comparisons = []
    for c in one_comparisons:
        try:
            m = next(m for m in c.term.args if m.index == v)
            if m.exp > 0:
                pos_comparisons.append(c)
            else:
                neg_comparisons.append(c)
        except StopIteration:  # v does not occur in c
            new_comparisons.append(c)
    for c1 in pos_comparisons:
        for c2 in neg_comparisons:
            c = elim_ineq_ineq(c1, c2, v)
            if not trivial_ineq(c):
                new_comparisons.append(c)
    return one_equations, one_comparisons


def equality_to_one_equality(c):
    """
    Converts an equality to an equation t = 0, with t a Product.
    """
    return cast_to_product(c.term1 / c.term2)


def inequality_to_one_comparison(c):
    """
    Converts an inequality to a ZeroComparison t > 0 or t >= 0, with t an AddTerm.
    """
    if (c.comp == terms.GE) or (c.comp == terms.GT):
        term = c.term1 / c.term2
    else:
        term = c.term2 / c.term1
    strong = (c.comp == terms.GT) or (c.comp == terms.LT)
    return OneComparison(cast_to_product(term), strong)


def get_multiplicative_information(B):
    """
    Retrieves known multiplicative equalities and inequalities from the blackboard B.
    """
    m_comparisons = poly_mult_module.get_multiplicative_information(B)
    # Each ti in m_comparisons really represents |t_i|.
    one_equalities = [equality_to_one_equality(c) for c in m_comparisons if c.comp == terms.EQ]
    one_comparisons = [inequality_to_one_comparison(c) for c in m_comparisons if
                       c.comp in (terms.GT, terms.GE, terms.LT, terms.LE)]
    return one_equalities, one_comparisons


mulpair_one = terms.MulPair(terms.IVar(0), 1)


def one_equality_to_comparison(e, B):
    """
    Converts an equation e == 0 to a blackboard comparison between IVars, or None if
    the equation is not of that form. Restores sign information from the Blackboard.
    """
    l = len(e.args)
    if l == 1:
        m = multiplicand_to_mulpair(e.args[0])
        return poly_mult_module.process_mul_comp(m, mulpair_one, e.coeff, terms.EQ, B)
    elif l == 2:
        m1 = multiplicand_to_mulpair(e.args[0])
        m2 = multiplicand_to_mulpair(e.args[1])
        return poly_mult_module.process_mul_comp(m1, m2, e.coeff, terms.EQ, B)
    else:
        return None


def one_comparison_to_comparison(c, B):
    """
    Converts a one comparison to a blackboard comparison between IVars, or None if
    the comparison is not of that form.
    """
    p = c.term
    l = len(p.args)
    comp = terms.GT if c.strong else terms.GE
    if l == 0:
        assert c.strong  # comparisons 1 >= 1 should have been eliminated
        return terms.IVar(0) < 0   # TODO: is the a better way of returning a contradiction?
    if l == 1:
        m = multiplicand_to_mulpair(p.args[0])
        return poly_mult_module.process_mul_comp(m, mulpair_one, c.coeff, comp, B)
    elif l == 2:
        m1 = multiplicand_to_mulpair(p.args[0])
        m2 = multiplicand_to_mulpair(p.args[1])
        return poly_mult_module.process_mul_comp(m1, m2, c.coeff, comp, B)
    else:
        return None


def assert_comparisons_to_blackboard(one_equalities, one_comparisons, B):
    """
    Asserts all the comparisons to zero_equalities and zero_comparisons to B.
    """
    for oe in one_equalities:
        c = one_equality_to_comparison(oe, B)
        if c:
            B.assert_comparison(c)
    for oc in one_comparisons:
        c = one_comparison_to_comparison(oc, B)
        if c:
            B.assert_comparison(c)


class FMMultiplicationModule:

    def __init__(self):
        pass

    def update_blackboard(self, B):
        """
        Learns sign information and equalities and inequalities from multiplicative information in
        B, and asserts them to B.
        """
        messages.announce_module('polyhedron multiplicative module')
        poly_mult_module.derive_info_from_definitions(B)
        eqs, comps = get_multiplicative_information(B)
        for i in range(B.num_terms):
            # at this point, eqs and comps have all comparisons with indices >= i
            i_eqs, i_comps = eqs, comps
            # determine all comparisons with IVar(i) and IVar(j) with j >= i
            for j in range(i + 1, B.num_terms):
                # at this point, i_eqs and i_comps have all comparisons with i and indices >= j
                ij_eqs, ij_comps = i_eqs, i_comps
                # determine all comparisons between IVar(i) and IVar(j)
                for k in range(j + 1, B.num_terms):
                     ij_eqs, ij_comps = elim(ij_eqs, ij_comps, k)
                assert_comparisons_to_blackboard(ij_eqs, ij_comps, B)
                # done with IVar(j)
                i_eqs, i_comps = elim(i_eqs, i_comps, j)
            # add this point, i_eqs and i_comps contain only comparisons with IVar(i) alone
            assert_comparisons_to_blackboard(i_eqs, i_comps, B)
            # done with IVar(i)
            eqs, comps = elim(eqs, comps, i)





# from classes import *
# from heuristic import *
# from itertools import combinations
# from math import floor, ceil
#
# ###############################################################################
# #
# # FRACTION ROUNDING
# #
# ###############################################################################
#
#
# # These are used for rounding square roots properly.
# # Take fractions,  return fractions
# precision = 100000
# def round_down(f):
#     if f.denominator > precision:
#         return Fraction(int(floor(float(f.numerator * precision) / f.denominator)), precision)
#     else:
#         return f
#
# def round_up(f):
#     if f.denominator > precision:
#         return Fraction(int(ceil(float(f.numerator * precision) / f.denominator)), precision)
#     else:
#         return f
#
# # If we have x comp coeff * y, then we also have x comp round_coeff * y
# def round_coeff(coeff, comp):
#     if comp in [LE, LT]:
#         return round_up(Fraction(coeff))
#     else:
#         return round_down(Fraction(coeff))
#
# def round_float_coeff(coeff,comp):
#     if comp in [LE, LT]:
#         return Fraction(int(ceil(coeff * precision)),precision)
#     else:
#         return Fraction(int(floor(coeff * precision)),precision)
#
#
# ###############################################################################
# #
# # MULTIPLICATIVE ELIMINATION
# #
# ###############################################################################
#
# # def lcm(args):
# #     if len(args)==0:
# #         return 1
# #     elif len(args)==1:
# #         return args[0]
# #     if len(args)==2:
# #         return args[0]*args[1]/gcd(args[0],args[1])
# #     else:
# #         return lcm([args[0],lcm(args[1:])])
#
#
# #
# # The next routine takes multiplicative terms t1 and t2, and another term
# #   v (usually a variable), which appears t.
# #
# # It raises t1 to a *positive power*, and t2 to a different power so that
# # the exponent of v is the same in both. It then returns t2 / t1.
# #
# # If t1 appears in a comparison t1 > 1 or t1 >= 1, and t2 appears in the
# # equation t2 = 1, what we get is the result of using the second equation
# # to eliminate v in the first.
# #
# # If t1 appears in a comparison t1 > 1 or t1 >= 1 in which v appears with
# # *positive* exponent, and t2 appears in a comparison t2 > 1 or t2 >= 1 in
# # which v occurs with a negative exponent, the result is again a consequence
# # of the two which eliminates v.
# #
# # v is not assumed to appear in t1.
# #
# def mul_subst(t1, t2, v):
# #     denoms = []
# #     for m in t1.mulpairs:
# #         if isinstance(m.exp,Fraction) and m.exp.denominator!=0:
# #             denoms.append(m.exp.denominator)
# #     scaled_t1 = pow(t1,lcm(denoms))
# #
# #     denoms = []
# #     for m in t2.mulpairs:
# #         if isinstance(m.exp,Fraction) and m.exp.denominator!=0:
# #             denoms.append(m.exp.denominator)
# #     scaled_t2 = pow(t2,lcm(denoms))
#
#     m1 = next((m for m in t1.mulpairs if m.term == v), None)
#     if m1 is None:
#         return t1
#     m2 = next((m for m in t2.mulpairs if m.term == v))
#     exp1, exp2 = m1.exp, m2.exp
#
#     # GCD will not work properly for floats.
#     if isinstance(exp1, float):
#         exp1 = Fraction(exp1)
#     if isinstance(exp2, float):
#         exp2 = Fraction(exp2)
#
#     scale1 = abs(exp2 / gcd(exp1, exp2))
#     scaled_t1 = pow(t1, scale1)
#     scaled_t2 = pow(t2, exp1 * scale1 / exp2)
#     return scaled_t1 / scaled_t2
#
# def mul_elim(equations, one_comparisons, v):
#     def occurs_in(v, t):
#         return v in (m.term for m in t.mulpairs)
#
#     for e in equations:
#         if occurs_in(v, e):
#             new_equations = [mul_subst(e2, e, v) for e2 in equations if e != e2]
#             new_comparisons = [One_comparison(mul_subst(c.term, e, v), c.comp)
#                                for c in one_comparisons]
#             return new_equations, new_comparisons
#
#     pos_comparisons = []  # v occurs with positive exponent
#     neg_comparisons = []  # v occurs with negative exponent
#     new_comparisons = []
#     for c in one_comparisons:
#         m = next((m for m in c.term.mulpairs if m.term == v), None)
#         if m is None:
#             new_comparisons.append(c)  # v does not occur at all
#         elif m.exp > 0:
#             pos_comparisons.append(c)
#         else:
#             neg_comparisons.append(c)
#     for c1 in pos_comparisons:
#         for c2 in neg_comparisons:
#             if c1.comp == GE and c2.comp == GE:
#                 new_comp = GE
#             else:
#                 new_comp = GT
#             new_comparisons.append(One_comparison(
#                     mul_subst(c1.term, c2.term, v), new_comp))
#     return equations, new_comparisons
#
#
#
#
# ###############################################################################
# #
# # MULTIPLICATIVE HEURISTIC
# #
# ###############################################################################
#
# # The main method has a number of subroutines that depend on the heuristic H.
# def learn_mul_comparisons(H):
#
#     ##############################
#     #
#     #  IVar size info
#     #
#     ##############################
#
#     def ge_one(i):
#         if (0, i) in H.term_comparisons.keys():
#             if [c for c in H.term_comparisons[0, i] if c.comp in [LT, LE] and
#                 c.coeff > 0 and c.coeff <= 1]:
#                 return True
#         return False
#
#     def le_one(i):
#         if (0, i) in H.term_comparisons.keys():
#             if [c for c in H.term_comparisons[0, i] if (c.comp in [GT, GE] and
#                 c.coeff >= 1) or (c.comp in [LT, LE] and c.coeff < 0)]:
#                 return True
#         return False
#
#     def le_neg_one(i):
#         if (0, i) in H.term_comparisons.keys():
#             if [c for c in H.term_comparisons[0, i] if c.comp in [LT, LE] and
#                 c.coeff < 0 and c.coeff >= -1]:
#                 return True
#         return False
#
#     def ge_neg_one(i):
#         if (0, i) in H.term_comparisons.keys():
#             if [c for c in H.term_comparisons[0, i] if (c.comp in [GT, GE] and
#                 c.coeff <= -1) or (c.comp in [LE, LT] and c.coeff > 0)]:
#                 return True
#         return False
#
#     def abs_ge_one(i):
#         return ge_one(i) or le_neg_one(i)
#
#     def abs_le_one(i):
#         return le_one(i) and ge_neg_one(i)
#
#     ################################################
#     #
#     # Handle absolute values for elimination routine
#     #
#     #################################################
#
#     # this first routine takes i, j, comp, C representing
#     #    ai comp C aj
#     # and returns a new pair comp', C', so that
#     #    abs(ai) comp' C' abs(aj)
#     # is equivalent to the original comparison.
#     # assume signs are nonzero
#
#     def make_term_comparison_abs(i, j, comp, C):
#         C1 = C * H.sign(i) * H.sign(j)
#         if H.sign(i) == 1:
#             comp1 = comp
#         else:
#             comp1 = comp_reverse(comp)
#         return comp1, C1
#
#     # this routine takes i, j, ei, ej, comp1, C1 representing
#     #    |ai|^{ei} comp1 C1 |aj|^{ej}
#     # and returns a new pair comp, C, so that
#     #    ai^{ei} comp C aj^{aj}
#     # is equivalent to the original comparison.
#     # assume signs are nonzero
#
#     def make_term_comparison_unabs(i, j, ei, ej, comp1, C1):
#         correction = (H.sign(i) ** ei) * (H.sign(j) ** ej)
#         correction = 1 if correction > 0 else -1  # Make correction an int instead of a float
#         C = C1 * correction
#         if H.sign(i) ** ei == 1:
#             comp = comp1
#         else:
#             comp = comp_reverse(comp1)
#         return comp, C
#
#     # Assumes ai, aj > 0 and j is not 0
#     def one_comparison_from_term_comparison(i, j, comp, C):
#         if C <= 0:
#             if comp in [LE, LT]:  # pos < neg. contradiction
#                 H.raise_contradiction(MUL)
#             else:  # pos > neg. useless
#                 return None
#
#         if comp == GT or comp == GE:
#             new_comp = comp
#             if i == 0:
#                 t = Mul_term([(IVar(j), -1)], Fraction(1, C))
#             else:
#                 t = Mul_term([(IVar(i), 1), (IVar(j), -1)], Fraction(1, C))
#         else:
#             new_comp = comp_reverse(comp)
#             if i == 0:
#                 t = Mul_term([(IVar(j), 1)], C)
#             else:
#                 t = Mul_term([(IVar(i), -1), (IVar(j), 1)], C)
#         return One_comparison(t, new_comp)
#
#
#     ###################################
#     #
#     # Sign inference helper functions
#     #
#     ###################################
#
#     def ivar_zero_comparison(i):
#         if i in H.zero_comparisons.keys():
#             return H.zero_comparisons[i].comp
#         return None
#
#     def mulpair_zero_comparison(m):
#         if m.term.index in H.zero_comparisons.keys():
#             comp = H.zero_comparisons[m.term.index].comp
#             if m.exp % 2 == 0 or (isinstance(m.exp, Fraction) and m.exp.numerator % 2 == 0):
#                 if comp in [GT, LT]:
#                     return GT
#                 else:
#                     return GE
#             else:
#                 return comp
#         elif m.exp % 2 == 0:
#             return GE
#         else:
#             return None
#
#     def prod_zero_comparisons(comps):
#         if None in comps:
#             return None
#         else:
#             notstrict = LE in comps or GE in comps
#             if len([m for m in comps if m in [LT, LE]]) % 2 == 0:
#                 if not notstrict:
#                     return GT
#                 else:
#                     return GE
#             else:
#                 if not notstrict:
#                     return LT
#                 else:
#                     return LE
#
#     def sign_pow(s, n):
#         if s == 1 or (s == -1 and n % 2 == 0):
#             return 1
#         elif s == -1:
#             return -1
#         else:
#             raise Error("sign should be 1 or -1")
#
#
#     def multerm_zero_comparison(t):
#         comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
#         return prod_zero_comparisons(comps)
#
#     # This method looks at term definitions and tries to infer signs of subterms.
#     # For instance, if a_i = a_j * a_k, a_i > 0, a_j < 0, then it will learn a_k < 0.
#     # Provenance is HYP, so this info is available to mul routine
#     def infer_signs_from_definitions():
#         for i in (j for j in range(H.num_terms) if isinstance(H.name_defs[j], Mul_term)):
#             t = H.name_defs[i]
#             # have the equation a_i = t.
#             leftsign = ivar_zero_comparison(i)
#             comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
#             rightsign = prod_zero_comparisons(comps)
#
#             if ((leftsign in [GE, GT] and rightsign == LT) or (leftsign in [LT, LE] and rightsign == GT)
#                 or (leftsign == GT and rightsign in [LE, LT]) or (leftsign == LT and rightsign in [GE, GT])):
#                 H.raise_contradiction(MUL)
#
#             if leftsign in [GT, LT]:  # strict info on left implies strict info for all on right.
#                 for j in range(len(comps)):
#                     if comps[j] in [GE, LE]:
#                         newcomp = (GT if comps[j] == GE else LT)
#                         H.learn_zero_comparison(t.mulpairs[j].term.index, newcomp, HYP)
#
#             elif rightsign in [GT, LT] and leftsign not in [GT, LT]:  # strict info on right implies strict info on left
#                 H.learn_zero_comparison(i, rightsign, HYP)
#
#             elif (rightsign == GE and leftsign == LE) or (rightsign == LE and leftsign == GE):  # we have zero equality.
#                 H.learn_zero_equality(i, MUL)
#                 if comps.count(GE) == 1 and comps.count(LE) == 0:
#                     index = comps.index(GE)
#                     H.learn_zero_equality(t.mulpairs[index].term.index, HYP)
#                 elif comps.count(LE) == 1 and comps.count(GE) == 0:
#                     index = comps.index(LE)
#                     H.learn_zero_equality(t.mulpairs[index].term.index, HYP)
#
#             # Reset these with potentially new info
#             leftsign = ivar_zero_comparison(i)
#             comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
#             rightsign = prod_zero_comparisons(comps)
#
#             # Two possibilities here.
#             # Case 1: lhs is strong, rhs is missing one. All others on rhs must be strong by above. Missing one must be strong too, and we can figure out what it is.
#             # Case 2: lhs is weak, rhs is missing one, all others on rhs are strong. Missing one must be weak.
#             if rightsign == None and comps.count(None) == 1 and (leftsign in [GT, LT] or (leftsign in [GE, LE] and comps.count(GE) + comps.count(LE) == 0)):
#                 index = comps.index(None)
#                 m = t.mulpairs[index]
#                 comps.pop(index)
#                 comps.append(leftsign)
#                 new_comp = prod_zero_comparisons(comps)
#                 index2 = m.term.index
#                 H.learn_zero_comparison(index2, new_comp, HYP)
#
#
#     def infer_signs_from_learned_equalities():
#         for t in (d for d in H.zero_equations if isinstance(d, Mul_term)):
#             # we have t=0.
#             comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
#
#             # If there are more than two unknowns, we can't do anything.
#             if comps.count(None) > 1:
#                 return
#
#             # If there is one unknown and every other is strict, that unknown must be equal to 0.
#             if comps.count(None) == 1 and comps.count(LE) + comps.count(GE) == 0:
#                 index = comps.index(None)
#                 i = t.mulpairs[index].term.index
#                 H.learn_zero_equality(i, MUL)
#
#             elif comps.count(None) == 0:
#                 ges, les = comps.count(GE), comps.count(LE)
#                 # If there are no unknowns and only one is weak, that weak one must be equal to 0.
#                 if ges == 1 and les == 0:
#                     index = comps.index(GE)
#                     H.learn_zero_equality(t.mulpairs[index].term.index, MUL)
#                 elif les == 1 and ges == 0:
#                     index = comps.index(LE)
#                     H.learn_zero_equality(t.mulpairs[index].term.index, MUL)
#
#                 # If there are no weak inequalities, we have a contradiction.
#                 elif ges == 0 and les == 0:
#                     H.raise_contradiction(MUL)
#
#
#     #############################
#     #
#     # Helper function for learn_mul_comparison
#     #
#     #############################
#
#     # Takes comparison of the form |a_i|^{e0} comp coeff * |a_j|^{e1}
#     # Assumes coeff > 0
#     # Assumes that setting e1=e0 preserves the truth of the inequality.
#     # Takes e0th root of each side and learns the comparison
#     def take_roots_and_learn(i, j, e0, e1, comp, coeff):
#         if e0 < 0:
#             comp = comp_reverse(comp)
#         e0, e1, coeff = 1, 1, coeff ** Fraction(1, Fraction(e0))
#         coeff = round_coeff(coeff, comp)
#         comp, coeff = make_term_comparison_unabs(i, j, 1, 1, comp, coeff)
#         H.learn_term_comparison(i, j, comp, coeff, MUL)
#
#     ##############################
#     #
#     # Main routines
#     #
#     ##############################
#
#
#     # Takes a one_comparison of the form a_i^{e_i} * a_j^{e_j} * const >(=) 1,
#     #  where a_i really represents |a_i|.
#     def learn_mul_comparison(c):
#
#         length = len(c.term.mulpairs)
#         if length == 0:
#             if c.term.const < 1:
#                 H.raise_contradiction(MUL)
#             return
#
#         elif length == 1:
#             comp, coeff = c.comp, Fraction(1, Fraction(c.term.const))
#             m = c.term.mulpairs[0]
#             i, j = 0, m.term.index
#             exp = -m.exp
#             comp, coeff = make_term_comparison_unabs(0, j, 1, exp, comp, coeff)
#
#             if (H.sign(j) ** exp) * coeff < 0:
#                 if comp in [LE, LT]:  # 1 < neg
#                     H.raise_contradiction(MUL)
#                 return  # 1 > neg. not useful
#
#             # now have:
#             #   1 comp coeff * a_j^exp
#
#             if exp < 0 and H.sign(j) * coeff > 0:
#                 exp, comp, coeff = -exp, comp_reverse(comp), Fraction(1, Fraction(coeff))
#             elif exp < 0:  # 1 is being compared to a negative number. Comparison should not change.
#                 exp, coeff = -exp, Fraction(1, Fraction(coeff))
#
#             coeff = (-1 if coeff<0 else 1)*round_float_coeff(pow(abs(coeff),1/Fraction(exp)), comp)
#
#             H.learn_term_comparison(0, j, comp, coeff, MUL)
#
#         elif length == 2:
#             m0, m1 = c.term.mulpairs[0], c.term.mulpairs[1]
#             i, j = m0.term.index, m1.term.index
#             e0, e1 = m0.exp, -m1.exp
#             coeff = Fraction(1, Fraction(c.term.const))
#             comp = c.comp
#
#             # now have:
#             #    |a_i|^e0 comp coeff * |a_j|^e1
#
#             if coeff < 0:
#                 if comp in [LT, LE]:  # pos < neg
#                     H.raise_contradiction(MUL)
#                 return  # pos > neg. not useful.
#
#             # Otherwise, both sides of the inequality are positive
#             # a_i and a_j are still abs values, coeff is positive
#
#             if e0 == e1:  # we have |a_i|^p comp coeff * |a_j|^p
#                 take_roots_and_learn(i, j, e0, e1, comp, coeff)
#
#             elif e0 < e1 and comp in [LE, LT] and abs_le_one(j):
#                 # making e1 smaller makes rhs bigger, which doesn't mess up comparison.
#                 # so pretend e1=e0 and take e0th root
#                 take_roots_and_learn(i, j, e0, e1, comp, coeff)
#
#             elif e0 > e1 and comp in [GE, GT] and abs_le_one(j):
#                 # making e1 bigger makes rhs smaller, which doesn't mess up comparison.
#                 # so pretend e1 = e0 and take e0th root
#                 take_roots_and_learn(i, j, e0, e1, comp, coeff)
#
#             elif e0 < e1 and comp in [GE, GT] and abs_ge_one(j):
#                 # making e1 smaller makes RHS smaller, which doesn't mess up comparison.
#                 take_roots_and_learn(i, j, e0, e1, comp, coeff)
#
#             elif e0 > e1 and comp in [LE, LT] and abs_ge_one(j):
#                 # making e1 bigger makes RHS bigger, which doesn't mess up comparison.
#                 take_roots_and_learn(i, j, e0, e1, comp, coeff)
#
#
#     ############################
#     #
#     # MAIN ROUTINE OF learn_mul_comparisons(H)
#     #
#     ############################
#
#     #H.info_dump()
#
#     if H.verbose:
#         print "Learning multiplicative facts..."
#         print
#
#     # infer signs from equations
#     infer_signs_from_definitions()
#     infer_signs_from_learned_equalities()
#
#
#     # make multiplicative equations (e's, where e = 1)
#     mul_eqs = []
#     for i in range(H.num_terms):
#         if isinstance(H.name_defs[i], Mul_term):
#             mul_eqs.append(H.name_defs[i] * Mul_term([Mul_pair(IVar(i), -1)]))
#
#     for eq in H.zero_equations:
#         if isinstance(eq, Add_term) and len(eq.addpairs) == 2:
#             equation = eq.addpairs[1].term * pow(eq.addpairs[0].term, -1) * Fraction(eq.addpairs[1].coeff, -eq.addpairs[0].coeff)
#             mul_eqs.append(equation)
#
#
#     # collect equations where signs are all known
#     # note that an equation e = 1 remains valid if each a_i is replace
#     # by abs(a_i)
#     # (to do: should really take absolute value of mult coefficient;
#     # in the implementation so far, it is always 1)
#     mul_eqs = [e for e in mul_eqs if
#                all(H.sign(m.term.index) != 0 for m in e.mulpairs)]
#
#
#     if H.verbose:
#         print 'Multiplicative equations:'
#         for e in mul_eqs:
#             print e, '= 1'
#         print
#
#
#
#     # make multiplicative comparisons
#     # if a_i is less than zero, replace by -a_i
#     # similarly for a_j
#     mul_comps = []
#     if H.verbose:
#         print 'Multiplicative comparisons:'
#     for i in [n for n in range(H.num_terms) if H.sign(n) != 0]:
#         for j in [m for m in range(i + 1, H.num_terms) if H.sign(m) != 0]:
#             if (i, j) in H.term_comparisons:
#                 for c in (p for p in H.term_comparisons[i, j] if p.provenance!=MUL):
#                     if H.verbose:
#                         print c.to_string(IVar(i), IVar(j))
#                     comp1, C1 = make_term_comparison_abs(i, j, c.comp, c.coeff)
#                     onecomp = one_comparison_from_term_comparison(i, j, comp1, C1)
#                     if onecomp:
#                         mul_comps.append(onecomp)
#
#
#
#     if H.verbose:
#         print
#
#     for i in range(0, H.num_terms):
#         # get all comparisons with i
#         i_mul_eqs = mul_eqs
#         i_mul_comps = mul_comps
#         for j in range(i + 1, H.num_terms):
#             # get all comparisons with i and j
#             ij_mul_eqs = i_mul_eqs
#             ij_mul_comps = i_mul_comps
#             for k in range(j + 1, H.num_terms):
#                 #if (i,j)==(0,2): print ij_mul_comps
#                 ij_mul_eqs, ij_mul_comps = (
#                     mul_elim(ij_mul_eqs, ij_mul_comps, IVar(k)))
#             # add any new information
#             for c in ij_mul_comps:
#                 #if (i,j)==(0,2): print 'learning from',c
#                 learn_mul_comparison(c)
#             # eliminate j
#             i_mul_eqs, i_mul_comps = mul_elim(i_mul_eqs, i_mul_comps, IVar(j))
#         mul_eqs, mul_comps = mul_elim(mul_eqs, mul_comps, IVar(i))
#
#     if H.verbose:
#         print
#
#
