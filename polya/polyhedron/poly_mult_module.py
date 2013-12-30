####################################################################################################
#
# poly_mult_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The routine for learning facts about multiplicative terms using polytope projections.
# Much of the work is done in lrs_polyhedron_util.py, as it is shared with the additive
# module.
#
# TODO:
#
####################################################################################################


import terms
import messages
#import geometry as geo
import itertools
import lrs_polyhedron_util as lrs_util
import cdd
import blackboard
import fractions
import math
import primes
import poly_add_module


####################################################################################################
#
# Fraction rounding
#
####################################################################################################


precision = 1000


def round_down(f):
    """
    Takes a fraction f.
    Returns the closest fractional approximation to f from below with denominator <= precision.
    """
    if f.denominator > precision:
        return fractions.Fraction(int(math.floor(float(f.numerator * precision) / f.denominator)),
                                  precision)
    else:
        return f


def round_up(f):
    """
    Takes a fraction f.
    Returns the closest fractional approximation to f from above with denominator <= precision.
    """
    if f.denominator > precision:
        return fractions.Fraction(int(math.ceil(float(f.numerator * precision) / f.denominator)),
                                  precision)
    else:
        return f


def round_coeff(coeff, comp):
    """
    Preserves if we have x comp coeff * y, then we also have x comp round_coeff * y
    Returns a fraction.
    """
    if comp in [terms.LE, terms.LT]:
        return round_up(fractions.Fraction(coeff))
    else:
        return round_down(fractions.Fraction(coeff))


def ge_one(B, i):
    if i == 0:
        return True
    return B.implies(i, terms.GE, 1, 0)


def le_one(B, i):
    if i == 0:
        return True
    return B.implies(i, terms.LE, 1, 0)


def le_neg_one(B, i):
    if i == 0:
        return False
    return B.implies(i, terms.LE, -1, 0)


def ge_neg_one(B, i):
    if i == 0:
        return True
    return B.implies(i, terms.GE, -1, 0)


def abs_ge_one(B, i):
    return ge_one(B, i) or le_neg_one(B, i)


def abs_le_one(B, i):
    return le_one(B, i) and ge_neg_one(B, i)


def process_mul_comp(m1, m2, coeff1, comp1, B):
    """
    Returns an IVar TermComparison implied by m1 * m2 * coeff comp 1, where m1 and m2 are mulpairs.
    m1 and m2 are still absolute values
    """
    if coeff1 == 0:
        return terms.comp_eval[terms.comp_reverse(comp1)](terms.one, 0)

    i, j, ei, ej = m1.term.index, m2.term.index, m1.exponent, -m2.exponent
    comp = comp1 if coeff1 > 0 else terms.comp_reverse(comp1)
    coeff = 1/fractions.Fraction(coeff1)

    if coeff < 0:
        if comp in [terms.LT, terms.LE]:  # pos < neg
            return terms.one < 0
        return None  # pos > neg. not useful.
    
    if ei == 0:
        i, ei = 0, 1
    if ej == 0:
        j, ej = 0, 1

    # we have ti^ei comp coeff * tj^ej
    if i == 0:  # a_i = 1, so we can set ei to whatever we want.
        ei = ej
        
    # Otherwise, both sides of the inequality are positive
    # a_i and a_j are still abs values, coeff is positive
    
    if (
        (ei == ej)  # we have |a_i|^p comp coeff * |a_j|^p
        or (ei < ej and comp in [terms.LE, terms.LT] and abs_le_one(B, j))
        # making ej smaller makes rhs bigger, which doesn't mess up comparison.
        or (ei > ej and comp in [terms.GE, terms.GT] and abs_le_one(B, j))
        # making ej bigger makes rhs smaller
        or (ei < ej and comp in [terms.GE, terms.GT] and abs_ge_one(B, j))
        # making ej smaller makes RHS smaller
        or (ei > ej and comp in [terms.LE, terms.LT] and abs_ge_one(B, j))
        # making ej bigger makes RHS bigger
    ):
        # we can set ej = ei and preserve the comparison.
        if ei < 0:
            comp = terms.comp_reverse(comp)
        ei, ej, coeff = 1, 1, coeff ** fractions.Fraction(1, ei)
        coeff = round_coeff(coeff, comp)
        comp, coeff = make_term_comparison_unabs(i, j, ei, ej, comp, coeff, B)
        return terms.comp_eval[comp](terms.IVar(i), coeff * terms.IVar(j))

####################################################################################################
#
# Absolute value conversions
#
####################################################################################################


def make_term_comparison_abs(c, B):
    """
    c.term1 can be term or sterm, c.term2 must be sterm
    if c is a * ti comp b * tj, returns a comparison |ti| comp p * |tj|
    B is a blackboard
    """
    if c.term2.coeff == 0:
        if isinstance(c.term1, terms.STerm):
            comp = c.comp if c.term1.coeff > 0 else terms.comp_reverse(c.comp)
            return terms.comp_eval[comp](c.term1.term, 0)
        else:
            return terms.comp_eval[c.comp](c.term1, 0)

    if isinstance(c.term1, terms.Term):
        term1, comp, coeff, term2 = c.term1, c.comp, c.term2.coeff, c.term2.term
    else:
        term1, term2 = c.term1.term, c.term2.term
        if term1.coeff < 0:
            comp = terms.comp_reverse(c.comp)
            coeff = fractions.Fraction(c.term2.coeff, c.term1.coeff)
        else:
            comp, coeff = c.comp, fractions.Fraction(c.term2.coeff, c.term1.coeff)
    i, j = term1.index, term2.index

    # we have term1 comp coeff * term2
    coeff1 = coeff * B.sign(i) * B.sign(j)
    if B.sign(i) == 1:
        return terms.comp_eval[comp](term1, coeff1 * term2)
    else:
        return terms.comp_eval[terms.comp_reverse(comp)](term1, coeff1 * term2)


def make_term_comparison_unabs(i, j, ei, ej, comp1, coeff1, B):
    """
    this routine takes i, j, ei, ej, comp1, coeff1 representing
       |ai|^{ei} comp1 coeff1 |aj|^{ej}
    and returns a new pair comp, coeff, so that
       ai^{ei} comp coeff aj^{aj}
    is equivalent to the original comparison.
    assume signs are nonzero
    """
    correction = (B.sign(i) ** ei) * (B.sign(j) ** ej)
    correction = 1 if correction > 0 else -1  # Make correction an int instead of a float
    coeff = coeff1 * correction
    if B.sign(i) ** ei == 1:
        comp = comp1
    else:
        comp = terms.comp_reverse(comp1)
    return comp, coeff


####################################################################################################
#
# Main functions
#
####################################################################################################


def derive_info_from_definitions(B):
    #todo: this could do more (weak sign info)
    for key in (k for k in B.term_defs if isinstance(B.term_defs[k], terms.MulTerm)):
        unsigned = [p.term.index for p in B.term_defs[key].args if B.sign(p.term.index) == 0]
        if len(unsigned) == 0 and B.sign(key) == 0:
            s = reduce(lambda x, y: x*y, [B.sign(p.term.index) for p in B.term_defs[key].args])
            if s > 0:
                B.assert_comparison(terms.IVar(key) > 0)
            else:
                B.assert_comparison(terms.IVar(key) < 0)
        elif len(unsigned) == 1 and B.sign(key) != 0:
            s = reduce(lambda x, y: x*y, [B.sign(p.term.index) for p in B.term_defs[key].args
                                          if B.sign(p.term.index) != 0])
            if s == B.sign(key):
                B.assert_comparison(unsigned[0] > 0)
            else:
                B.assert_comparison(unsigned[0] < 0)



def get_mul_comparisons(vertices, lin_set, num_vars, prime_of_index):
    """
    Returns a list of objects of the form (m1, m2, const, comp),
    where m1 and m2 are mulpairs, const is an int, comp is terms.GE/GT/LE/LT,
    and const * m1 * m2 comp 1
    """
    new_comparisons = []
    for (i, j) in itertools.combinations(range(num_vars), 2):
        base_matrix = [[vertices[k][0], vertices[k][i+2], vertices[k][j+2]]
                       + vertices[k][num_vars+2:] for k in range(len(vertices)) if k not in lin_set]
        matrix = cdd.Matrix(base_matrix, number_type='fraction')
        matrix.rep_type = cdd.RepType.GENERATOR
        for k in lin_set:
            matrix.extend([[vertices[k][0], vertices[k][i+2], vertices[k][j+2]]
                           + vertices[k][num_vars+2:]], linear=True)

        ineqs = cdd.Polyhedron(matrix).get_inequalities()
        for c in ineqs:
            if c[2] == c[1] == 0:  # no comp
                continue
            strong = not any(
                v[1] != 0 and
                v[i+2]*c[1]+v[j+2]*c[2]+sum(c[k]*v[num_vars+k-1] for k in range(3, len(c))) == 0
                for v in vertices)

            const = 1
            #Don't want constant to a non-int power
            scale = int(primes.lcmm(fractions.Fraction(c[k]).denominator for k in range(3, len(c))))
            if scale != 1:
                c = [c[0]]+[scale*v for v in c[1:]]

            skip = False
            for k in range(3, len(c)):
                if c[k] != 0:
                    if c[k] >= 1000000 or c[k] <= -1000000:
                        # Not going to get much here. Causes arithmetic errors.
                        skip = True
                        break
                    else:
                        const*=(prime_of_index[k + num_vars - 3]**c[k])
            if skip:
                continue

            new_comparisons.append((terms.MulPair(terms.IVar(i), c[1]),
                                   terms.MulPair(terms.IVar(j), c[2]),
                                   const, terms.GT if strong else terms.GE))
    return new_comparisons


def add_of_mul_comps(m_comparisons, num_terms):
    """
    Takes a list of multiplicative comparisons.
    Returns [(t, comp)], poi, iop, new_num_terms
    Where each t is a sum of IVars with t comp 0, poi is primes of index
    And new_num_terms is the number of IVars 0 ... n-1
    """
    class indstore:
        i = num_terms

    index_of_prime = {}  # maps a prime factor to the index of its IVar
    prime_of_index = {}  # inverse of the above

    def index_of(p):
        if p in index_of_prime:
            return index_of_prime[p]
        index_of_prime[p] = indstore.i
        prime_of_index[indstore.i] = p
        indstore.i += 1
        return indstore.i - 1

    a_comparisons = []

    for c in m_comparisons:
        #if isinstance(c.term1, terms.MulTerm):
        if c.comp == terms.EQ:
            t = -c.term2
            for mp in c.term1.args:
                t += mp.term * mp.exponent
            a_comparisons.append((t, terms.EQ))
        else:
            # c is ivar comp coeff * ivar
            if c.term2.coeff < 0:
                if c.comp in [terms.GE, terms.GT]:
                    # pos > neg. irrelevant.
                    continue
                elif c.comp in [terms.LE, terms.LT]:
                    # pos < neg. contradiction. This shouldn't happen
                    raise Exception("Problem in log conversion.")
            t = c.term1 - c.term2
            const = fractions.Fraction(c.term2.coeff)
            if const.numerator != 1:
                fac = primes.factorization(const.numerator)
                for i in fac:
                    t -= fac[i] * terms.IVar(index_of(fac[i]))
            if const.denominator != 1:
                fac = primes.factorization(const.denominator)
                for i in fac:
                    t += fac[i] * terms.IVar(index_of(fac[i]))
            a_comparisons.append((t, c.comp))

    plist = sorted(index_of_prime.keys())
    for i in range(len(plist)-1):
        a_comparisons.append((terms.IVar(index_of_prime[plist[i+1]])
                              - terms.IVar(index_of_prime[plist[i]]), terms.GT))
    return a_comparisons, prime_of_index, index_of_prime, indstore.i


def update_blackboard(blackboard):
    messages.announce_module('polyhedron multiplicative module')

#    learn_additive_sign_info(blackboard)

    m_comparisons = get_multiplicative_information(blackboard)
    # Each ti in m_comparisons really represents |t_i|.

    p = add_of_mul_comps(m_comparisons, blackboard.num_terms)
    a_comparisons, prime_of_index, index_of_prime, num_terms = p
    a_comparisons = [terms.comp_eval[c[1]](c[0], 0) for c in a_comparisons]

    h_matrix = lrs_util.create_h_format_matrix(a_comparisons, num_terms)
    messages.announce('Halfplane matrix:', messages.DEBUG)
    messages.announce(h_matrix, messages.DEBUG)
    v_matrix, v_lin_set = lrs_util.get_vertices(h_matrix)
    messages.announce('Vertex matrix:', messages.DEBUG)
    messages.announce(str(v_matrix), messages.DEBUG)
    messages.announce('Linear set:', messages.DEBUG)
    messages.announce(str(v_lin_set), messages.DEBUG)

    new_comparisons = get_mul_comparisons(v_matrix, v_lin_set,
                                          blackboard.num_terms, prime_of_index)

    for m1, m2, coeff, comp in new_comparisons:
        # coeff * m1 * m2 comp
        #print coeff, '*', m1, '*', m2, terms.comp_str[comp], '1'
        c = process_mul_comp(m1, m2, coeff, comp, blackboard)
        if c is not None:
            blackboard.assert_comparison(c)


def get_multiplicative_information(blackboard):
    """
    Retrieves the relevant information from the blackboard.
    Filters to only comparisons and equations where sign information is known, and converts to
    absolute value form.
    Note: in the returned comparisons, t_j represents |t_j|
    """
    derive_info_from_definitions(blackboard)

    comparisons = []
    for c in (c for c in blackboard.get_inequalities() + blackboard.get_equalities()
              if c.term2.coeff != 0):
        ind1 = c.term1.index
        ind2 = c.term2.term.index
        if blackboard.sign(ind1) != 0 and blackboard.sign(ind2) != 0:
            comparisons.append(make_term_comparison_abs(c, blackboard))

    for key in blackboard.term_defs:
        if (isinstance(blackboard.term_defs[key], terms.MulTerm) and blackboard.sign(key) != 0 and
                all(blackboard.sign(p.term.index) != 0 for p in blackboard.term_defs[key].args)):
            comparisons.append(
                terms.TermComparison(blackboard.term_defs[key], terms.EQ, terms.IVar(key))
            )

    return comparisons

####################################################################################################
#
# Tests
#
####################################################################################################


if __name__ == '__main__':

    # can change 'normal' to 'quiet' or 'low'
    messages.set_verbosity(messages.normal)

    u, v, w, x, y, z = terms.Vars('u, v, w, x, y, z')
    f = terms.Func('f')
    g = terms.Func('g')

    B = blackboard.Blackboard()

    B.assert_comparison(u > 0)
    B.assert_comparison(u < 1)
    B.assert_comparison(v > 0)
    B.assert_comparison(v < 1)
    B.assert_comparison(u + v < u * v)

    poly_add_module.update_blackboard(B)
    update_blackboard(B)