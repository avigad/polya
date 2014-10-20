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
#import polya.polyhedron.poly_mult_module as poly_mult_module
import polya.util.mul_util as mul_util
import polya.util.timer as timer
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
        self.coeff = fractions.Fraction(coeff)
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
            if len(self.args) == 0:
                return '1'
            else:
                return '*'.join([str(a) for a in self.args])
        else:
            if len(self.args) == 0:
                return str(self.coeff)
            else:
                return '{0!s}*{1}'.format(self.coeff, '*'.join([str(a) for a in self.args]))

    def __repr__(self):
        return self.__str__()

    def contains(self, v):
        """
        Determines whether index v occurs in the sum.
        """
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
        args = [Multiplicand(a.term.index, a.exponent) for a in term.args if a.term.index != 0]
    else:
        raise Error('Cannot cast {0!s} to a product'.format(term))
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
    return c.term.coeff == 1 and len(c.term.args) == 0 and not c.strong


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
    # TODO: for debugging, remove
    # result = OneComparison(t1, c.strong)
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
    return one_equations, new_comparisons


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
    m_comparisons = mul_util.get_multiplicative_information(B)
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
        return mul_util.process_mul_comp(m, mulpair_one, e.coeff, terms.EQ, B)
    elif l == 2:
        m1 = multiplicand_to_mulpair(e.args[0])
        m2 = multiplicand_to_mulpair(e.args[1])
        return mul_util.process_mul_comp(m1, m2, e.coeff, terms.EQ, B)
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
        #print c
        #return mul_util.process_mul_comp(mulpair_one, mulpair_one, p.coeff, comp, B)
        return terms.comp_eval[comp](
            terms.IVar(0),
            mul_util.round_coeff(fractions.Fraction(1, p.coeff), comp) * terms.IVar(0)
        )

        #assert c.strong  # comparisons 1 >= 1 should have been eliminated
        #return p.coeff*terms.IVar(0) > 0
#        return None
    if l == 1:
        m = multiplicand_to_mulpair(p.args[0])
        return mul_util.process_mul_comp(m, mulpair_one, p.coeff, comp, B)
#        return None
    elif l == 2:
        m1 = multiplicand_to_mulpair(p.args[0])
        m2 = multiplicand_to_mulpair(p.args[1])
        return mul_util.process_mul_comp(m1, m2, p.coeff, comp, B)
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
        timer.start(timer.FMMUL)
        messages.announce_module('Fourier-Motzkin multiplicative module')
        mul_util.derive_info_from_definitions(B)
        mul_util.preprocess_cancellations(B)
        eqs, comps = get_multiplicative_information(B)
        # t0 = 1; ignore
        for i in range(1, B.num_terms):
            # at this point, eqs and comps have all comparisons with indices >= i
            i_eqs, i_comps = eqs, comps
            # determine all comparisons with IVar(i) and IVar(j) with j >= i
            for j in range(i + 1, B.num_terms):
                # at this point, i_eqs and i_comps have all comparisons with i and indices >= j
                ij_eqs, ij_comps = i_eqs, i_comps
                # determine all comparisons between IVar(i) and IVar(j)
                for k in range(j + 1, B.num_terms):
                    ij_eqs, ij_comps = elim(ij_eqs, ij_comps, k)
                #print 'comps:', ij_comps
                assert_comparisons_to_blackboard(ij_eqs, ij_comps, B)
                # done with IVar(j)
                i_eqs, i_comps = elim(i_eqs, i_comps, j)
            # add this point, i_eqs and i_comps contain only comparisons with IVar(i) alone
            assert_comparisons_to_blackboard(i_eqs, i_comps, B)
            # done with IVar(i)
            eqs, comps = elim(eqs, comps, i)
        timer.stop(timer.FMMUL)

    def get_split_weight(self, B):
        return mul_util.get_split_weight(B)