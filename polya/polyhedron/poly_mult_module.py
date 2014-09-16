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

import polya.main.terms as terms
#import polya.main.blackboard as blackboard
import polya.main.messages as messages
import polya.polyhedron.lrs_polyhedron_util as lrs_util
import polya.polyhedron.lrs as lrs
#import polya.polyhedron.poly_add_module as poly_add_module
import polya.util.num_util as num_util
import polya.util.timer as timer
import polya.util.mul_util as mul_util

try:
    import cdd
except ImportError:
    cdd = None

import fractions
#import math
import itertools

####################################################################################################
#
# Main functions
#
####################################################################################################


def get_mul_comparisons(vertices, lin_set, num_vars, prime_of_index):
    """
    Returns a list of objects of the form (m1, m2, const, comp),
    where m1 and m2 are mulpairs, const is an int, comp is terms.GE/GT/LE/LT,
    and const * m1 * m2 comp 1
    """
    if all(v[1] == 0 for v in vertices):
        p = terms.MulPair(terms.IVar(0), 1)
        return [(p, p, 1, terms.LT)]
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

        for ind in range(len(ineqs)):
            c = ineqs[ind]
            if c[2] == c[1] == 0:  # no comp
                continue
            strong = not any(
                v[1] != 0 and
                v[i+2]*c[1]+v[j+2]*c[2]+sum(c[k]*v[num_vars+k-1] for k in range(3, len(c))) == 0
                for v in vertices)

            const = 1
            #Don't want constant to a non-int power
            scale = int(num_util.lcmm(fractions.Fraction(c[k]).denominator
                                      for k in range(3, len(c))))
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
                        if c[k] > 0:
                            const *= (prime_of_index[k + num_vars - 3]**c[k])
                        else:
                            const *= fractions.Fraction(1, prime_of_index[k+num_vars-3]**(-c[k]))
            if skip:
                continue

            if ind in ineqs.lin_set:
                new_comp = terms.EQ
            else:
                new_comp = terms.GT if strong else terms.GE

            new_comparisons.append((terms.MulPair(terms.IVar(i), c[1]),
                                   terms.MulPair(terms.IVar(j), c[2]),
                                   const, new_comp))
    return new_comparisons


def add_of_mul_comps(m_comparisons, num_terms):
    """
    Takes a list of multiplicative comparisons.
    Returns [(t, comp)], poi, iop, new_num_terms
    Where each t is a sum of IVars with t comp 0, poi is primes of index
    And new_num_terms is the number of IVars 0 ... n-1
    """
    # todo: is there a more elegant way to do this?
    class indstore:
        i = num_terms

    index_of_prime = {}  # maps a prime factor to the index of its IVar

    def index_of(p):
        if p in index_of_prime:
            return index_of_prime[p]
        index_of_prime[p] = indstore.i
        indstore.i += 1
        return indstore.i - 1

    a_comparisons = []

    for c in m_comparisons:
        (c2, sc2) = (c.term2.term, c.term2.coeff) if isinstance(c.term2, terms.STerm) \
            else (c.term2, None)
        if c.comp == terms.EQ:
            if isinstance(c2, terms.IVar):
                t = -c2
            elif isinstance(c2, terms.MulTerm):
                for mp in [m for m in c2.args if m.term.index != 0]:
                    t += mp.term * mp.exponent
            else:
                raise Exception

            if sc2 is not None:
                const = fractions.Fraction(sc2)
                if const.numerator != 1:
                    fac = num_util.factorization(const.numerator)
                    for i in fac:
                        t -= fac[i] * terms.IVar(index_of(i))
                if const.denominator != 1:
                    fac = num_util.factorization(const.denominator)
                    for i in fac:
                        t += fac[i] * terms.IVar(index_of(i))

            if isinstance(c.term1, terms.MulTerm):
                for mp in [m for m in c.term1.args if m.term.index != 0]:
                    t += mp.term * mp.exponent
            elif isinstance(c.term1, terms.IVar):
                t += c.term1
            else:
                raise Exception
            a_comparisons.append((t, terms.EQ))
        else:
            # c is ivar comp coeff * ivar
            if c.term2.coeff < 0:
                if c.comp in [terms.GE, terms.GT]:
                    # pos > neg. irrelevant.
                    continue
                elif c.comp in [terms.LE, terms.LT]:
                    # pos < neg. contradiction. This shouldn't happen
                    raise Exception("Problem in log conversion." + str(c))
            t = -c.term2.term if c.term1.index == 0 else c.term1 - c.term2.term
            const = fractions.Fraction(c.term2.coeff)
            if const.numerator != 1:
                fac = num_util.factorization(const.numerator)
                for i in fac:
                    t -= fac[i] * terms.IVar(index_of(i))
            if const.denominator != 1:
                fac = num_util.factorization(const.denominator)
                for i in fac:
                    t += fac[i] * terms.IVar(index_of(i))
            a_comparisons.append((t, c.comp))

    plist = sorted(index_of_prime.keys())
    for i in range(len(plist)-1):
        a_comparisons.append((terms.IVar(index_of_prime[plist[i+1]])
                              - terms.IVar(index_of_prime[plist[i]]), terms.GT))
    prime_of_index = dict((value, key) for key, value in index_of_prime.iteritems())
    return a_comparisons, prime_of_index, indstore.i


class PolyMultiplicationModule:
    def __init__(self):
        if not lrs.lrs_path:
            raise Exception('lrs is needed to instantiate a polyhedron module.')

    def update_blackboard(self, B):
        timer.start(timer.PMUL)
        messages.announce_module('polyhedron multiplicative module')

        mul_util.derive_info_from_definitions(B)

        print 'preprocessing'

        #mul_util.preprocess_cancellations(B)

        m_comparisons = mul_util.get_multiplicative_information(B)
        # Each ti in m_comparisons really represents |t_i|.

        p = add_of_mul_comps(m_comparisons, B.num_terms)
        a_comparisons, prime_of_index, num_terms = p
        a_comparisons = [terms.comp_eval[c[1]](c[0], 0) for c in a_comparisons]

        h_matrix = lrs_util.create_h_format_matrix(a_comparisons, num_terms)
        messages.announce('Halfplane matrix:', messages.DEBUG)
        messages.announce(h_matrix, messages.DEBUG)
        v_matrix, v_lin_set = lrs_util.get_vertices(h_matrix)
        messages.announce('Vertex matrix:', messages.DEBUG)
        for l in v_matrix:
            messages.announce(str(l), messages.DEBUG)
        messages.announce('Linear set:', messages.DEBUG)
        messages.announce(str(v_lin_set), messages.DEBUG)

        new_comparisons = get_mul_comparisons(v_matrix, v_lin_set,
                                              B.num_terms, prime_of_index)


        for m1, m2, coeff, comp in new_comparisons:
            c = mul_util.process_mul_comp(m1, m2, coeff, comp, B)
            if c is not None:
                B.assert_comparison(c)
        timer.stop(timer.PMUL)


####################################################################################################
#
# Tests
#
####################################################################################################

# if __name__ == '__main__':
#
#     # can change 'normal' to 'quiet' or 'low'
#     messages.set_verbosity(messages.normal)
#
#     u, v, w, x, y, z = terms.Vars('u, v, w, x, y, z')
#     f = terms.Func('f')
#     g = terms.Func('g')
#
#     B = blackboard.Blackboard()
#
#     B.assert_comparison(u > 0)
#     B.assert_comparison(u < 1)
#     B.assert_comparison(v > 0)
#     B.assert_comparison(v < 1)
#     B.assert_comparison(u + v < u * v)
#
#     pa = poly_add_module.PolyAdditionModule()
#     pm = PolyMultiplicationModule()
#
#     pa.update_blackboard(B)
#     pm.update_blackboard(B)
