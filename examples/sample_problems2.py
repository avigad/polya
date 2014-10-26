####################################################################################################
#
# sample_problems2.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# Examples for Polya.
#
#
####################################################################################################

from polya import *
import sys


####################################################################################################
#
# The list of examples
#
####################################################################################################


a, b, c, d, e, i, K, m, n = Vars('a, b, c, d, e, i, K, m, n')
r, s, t, u, v, w, x, y, z = Vars('r, s, t, u, v, w, x, y, z')
eps = Var('eps')
f = Func('f')

examples = list()

#
# needed axioms before
#

examples.append(Example(
    hyps=[i >= 0, abs(f(y) - f(x)) < 1 / (2 * (i + 1)), abs(f(z) - f(y)) < 1 / (2 * (i + 1))],
    conc=(abs(f(z) - f(x)) < 1 / (i + 1)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))


#
# removed hypothesis 0 <= n
# fails -- do we get this with splits?
#

examples.append(Example(
    hyps=[n < (K / 2) * x, 0 < c, 0 < eps, eps < 1],
    conc=((1 + eps / (3 * (c + 3))) * n < K * x),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))



#
# exponents
#

examples.append(Example(
    hyps=[exp(x)>5, exp(y)>6, exp(z)>4],
    conc=(exp(x + y + z) > 20)
))


#
# min and max
#

examples.append(Example(
    hyps=[x <= y],
    conc=(minm(x, y) == x)))

examples.append(Example(
    hyps=[0 < x, x <= y],
    conc=(2 * x + minm(w, z) < 3 * y + w)))

examples.append(Example(
    hyps=[x < y, u <= v],
    conc=(u + minm(x + 2 * u, y + 2 * v) <= x + 3 * v)))

examples.append(Example(
    hyps=[x >= y],
    conc=(minm(x, y) + maxm(x, y) == x + y)))

examples.append(Example(
    hyps=[x < u, y < u, z < u, x < v, y < v, z < v],
    conc=(maxm(x, y, z) < minm(u, v))))


#
# abs
#

examples.append(Example(
    conc=(abs(3 * x + 2 * y) <= 3 * abs(x) + 4 * abs(y))))

examples.append(Example(
    hyps=[y > 0],
    conc=(abs(3 * x + 2 * y + 5) < 4 * abs(x) + 3 * y + 6)))

examples.append(Example(
    conc=(abs(x - y) >= abs(y) - abs(x))))


#
# varia
#

examples.append(Example(
    hyps=[x==z, y==w, x>0, y>0],
    conc=(x * y == z * w)))

examples.append(Example(
    hyps=[x > 2 * y, x == 3 * y],
    conc=(y > 0)))


# Follows by x > log(x) >= minm(...) > 1
examples.append(Example(
    hyps=[minm(exp(3*x), exp(9*x**2-2), log(x))>1, x>0],
    conc=(x>1)
))

examples.append(Example(
    hyps=[y>maxm(2, 3*x), x>0],
    conc=(exp(4*y-3*x)>exp(6))
))

examples.append(Example(
    hyps=[x!=0, y!=0, log(abs(x)+2*abs(y)) > 5, log(abs(y)) < root(2, 2)],
    conc=(log(exp(x)) > exp(-2))
))

# The Pythagorean Theorem. We shouldn't be able to prove this, just checking.
a1, a2, a3, b1, b2, b3 = Vars('a1 a2 a3 b1 b2 b3')
examples.append(Example(
    hyps=[(b2-b1)/(a2-a1) == -(a3-a2)/(b3-b2)],
    conc=(root(2, (b3-b1)**2 + (a3-a1)**2) == root(2, (b2-b1)**2 + (a2 - a1)**2) + root(2, (b3-b2)**2 - (a3-a2)**2)),
    split_depth=6, split_breadth=10,
    omit=True
))


####################################################################################################
#
# To run from the command line
#
####################################################################################################


if __name__ == '__main__':
    run_examples(examples, sys.argv)
