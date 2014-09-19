####################################################################################################
#
# test_minimum_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Examples for Polya.
#
# TODO: improve command line interface
#
####################################################################################################


from polya import *
from polya.main.terms import minm, maxm, floor, ceil
import polya.main.minimum_module as mm
from sample_problems import Example
import sys
import timeit



####################################################################################################
#
# The list of examples
#
####################################################################################################


a, b, c, d, e, i, K, m, n = Vars('a, b, c, d, e, i, K, m, n')
r, s, t, u, v, w, x, y, z = Vars('r, s, t, u, v, w, x, y, z')
eps = Var('eps')

f = Func('f')
# exp = Func('exp')
# ceil = Func('ceil')

examples = list()

#
# examples from the paper
#

examples.append(Example(
    hyps=[0 < u, u < v, v < 1, 2 <= x, x <= y],
    conc=(2 * u**2 * x < v * y**2),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))


####################################################################################################
#
# To run from the command line
#
####################################################################################################


if __name__ == '__main__':

    # set_solver_type('fm')
    S = Solver()
    m = mm.MinimumModule()
    S.append_module(m)

    # works
    # S.assume(x < y)
    # S.prove(minm(x, y) == x)

    # works
    # S.assume(x <= y)
    # S.prove(maxm(x, y) == y)

    # #works
    # S.assume(0 < x)
    # S.assume(x <= y)
    # S.prove(2 * x + minm(w, z) < 3 * y + w)

    # set_solver_type('fm')
    # messages.set_verbosity(messages.debug)
    # S = Solver()
    # S.assume(x==z, y==w, x>0, y>0)
    # S.prove(x*y == z*w)

    # set_solver_type('fm')
    # messages.set_verbosity(messages.debug)
    # S = Solver()
    # S.assume(x==z, y==w, x>0, y>0)
    # S.prove(x*y == z*w)

    # works
    # S.assume(x < y, u <= v)
    # S.prove(u + minm(x + 2 * u, y + 2 * v) <= x + 3 * v)

    # works, but not without the assumption
    # S.assume(x >= y)
    # S.prove(minm(x, y) + maxm(x, y) == x + y)

    # # works
    # S.assume(x < u, y < u, z < u, x < v, y < v, z < v)
    # S.prove(maxm(x, y, z) < minm(u, v))

    # S.assume(x > 2 * y)
    # S.assume(x == 3 * y)
    # S.prove(y > 0)

    # a = mm.Extended(5)
    # b = mm.infty
    # c = mm.neg_infty
    # d = mm.Extended(8)
    # I1 = mm.ComparisonRange(a, b, False, False, False)
    # I2 = mm.ComparisonRange(c, d, True, True, True)
    # print 'I1 = ', I1
    # print 'I2 = ', I2
    # print 'I1 & I2 = ', I1 & I2

    B = Blackboard()
    B.add(x >= -2 * y)
    B.add(x < 3 * y)
    print B.get_le_range(1, 2)
