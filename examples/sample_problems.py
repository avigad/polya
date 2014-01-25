####################################################################################################
#
# sample_problems.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Examples for Polya.
#
# TODO: improve command line interface, or example, to set verbosity, include a range, omit
# examples, print timing, etc.
#
####################################################################################################


from polya import *
import sys
import timeit


class Example:

    def __init__(self, name = 'Polya sample problem', hyps = [], conc = None, ax = [],
                 modules = [], omit = False):
        self.name = name
        self.hyps = hyps
        self.conc = conc
        self.ax = ax
        self.modules = modules
        self.omit = omit    # flag to omit from 'test_all'

    def show(self):
        print 'Problem: {0}'.format(self.name)
        for a in self.ax:
            print 'Axiom: {0!s}'.format(a)
        for h in self.hyps:
            print 'Hypothesis: {0!s}'.format(h)
        if self.conc:
            print 'Conclusion: {0!s}'.format(self.conc)
        else:
            print 'Conclusion: False'
        if self.omit:
            print "(Omitted from 'test_all')"
        print

    def test(self):
        self.show()
        S = Solver(assertions=self.hyps, axioms=self.ax, modules=self.modules)
        t = timeit.default_timer()
        if self.conc:
            if S.prove(self.conc):
                print 'Conclusion is valid.'
            else:
                print 'Failed.'
        else:
            if S.check():
                print 'Refuted hypotheses.'
            else:
                print 'Failed.'
        print 'Ran in', round(timeit.default_timer()-t, 3), 'seconds'
        print


####################################################################################################
#
# The list of examples
#
####################################################################################################


a, b, c, d, e, i, m = Vars('a, b, c, d, e, i, m')
r, s, t, u, v, w, x, y, z = Vars('r, s, t, u, v, w, x, y, z')

f = Func('f')
exp = Func('exp')
abs2 = Func('abs')
ceil = Func('ceil')

examples = []

examples.append(Example(
    hyps = [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x],
    conc = u*(3*y)**2 + 1 < x**2 * v + x
))

examples.append(Example(
    hyps = [0 < x, x < y, 0 < u, u < v, 0 < w + z, w + z < r - 1],
    conc = u + (1+x)**2 * (2*w + 2*z + 3) < 2*v + (1+y)**2 * (2*r + 1)
))

examples.append(Example(
    hyps = [x+1 / y < 2, y < 0, y / x > 1, -2 <= x, x <= 2, -2 <= y, y <= 2],
    conc = x**2*y**(-1) <= 1-x
))

examples.append(Example(
    ax = [Forall([x, y], Implies(x<y, f(x)<f(y)))],
    hyps = [a < b],
    conc = f(a) < f(b)
))

examples.append(Example(
    ax = [Forall([x, y], Implies(x<y, f(x)<f(y)))],
    hyps = [0 < r, s > 1, 0 < x, x < y, w > z, z + f(x) > w + f(s * (y + r))]
))

examples.append(Example(
    ax = [Forall([x, y], (f(x) + f(y)) / 2 >= f((x + y) / 2))],
    hyps = [f(x) + f(y) < z, f((x + y) / 2) > 4 * z, z > 0]
))

examples.append(Example(
    ax = [Forall([x, y], (f(x) + f(y)) / 2 >= f((x + y) / 2))],
    hyps = [z > 0, f(x) + f(y) - z < 0, f((x + y)/2) - 4 * z > 0]
))

examples.append(Example(
    ax = [Forall([x, y], f(x * y) == f(x) * f(y)), Forall([x], Implies(x > 2, f(x) < 0))],
    hyps = [x > 1, y > 2, f(x * y) > 0]
))

# Polya does not refute the hypotheses in the next example, although there is a contradiction.
# we get t6 = t1*t3*t5, t10=t3*t5, t1>0, t10>0, t6<0.
# but because the signs of t1 and t3 are unknown, the mul routine cannot find that contradiction
# if we add z>0,

examples.append(Example(
    ax = [Forall([x, y], f((x * y) / 2) <= (f(x) * f(y)) / 2)],
    hyps = [z > 0, z * f(x) * f(y) < 0, 4 * z * f(x * y / 2) > 0]
))

examples.append(Example(
    ax = [Forall([x, y], f(x, y, x*y)>0)],
    hyps = [f(a, b, c * d) < 0, a > 0, b > 0, a == c, b == d]
))

examples.append(Example(
    ax = [Forall([x, y], f(x, y, x + y) > 0)],
    hyps = [f(e, b, c + d) < 0, a > 0, b > 0, a == c, b == d, a == e]
))

examples.append(Example(
    hyps = [0 < u, u < v, 1 < x, x < y, 0 < w, w < z],
    conc = u + x * w < v + y**2 * z
))

# This example comes from Avigad and Friedman (2006)
examples.append(Example(
    ax = [Forall([x, y], And(Implies(x < y, exp(x) < exp(y)), exp(x) > 0))],
    hyps = [0 < x, x < y],
    conc = (1 + x**2) / (2 + exp(y)) < (2 + y**2) / (1 + exp(x))
))

# An interesting example: the method does not terminate.
examples.append(Example(
    hyps = [x ** 2 + 2 * x + 1 < 0],
    omit = True
))

examples.append(Example(
    ax = [Forall([x], f(x) > 0)],
    hyps = [f(x) < y, y < z, z < f(x)]
))

examples.append(Example(
    hyps = [[x == y, f(x) != f(y)]],
    omit = True
))

examples.append(Example(
    ax = [Forall([x], ceil(x) >= x)],
    hyps = [a < b, x > a, m >= ceil((b - a) / (x - a))],
    conc = a + (b - a) / (m + 1) < x
))

# in the paper
examples.append(Example(
    ax = [Forall([x], ceil(x) >= x), Forall([m], f(m) < a + (b - a) / (m + 1))],
    hyps = [a < b, x > a, m >= ceil((b - a) / (x - a))],
    conc = f(m) < x
))

# in the paper
examples.append(Example(
    ax = [i >= 0, Forall([x,y], abs2(x + y) <= abs2(x) + abs2(y))],
    hyps = [abs2(f(y) - f(x)) < 1 / (2 * (i + 1)), abs2(f(z) - f(y)) < 1 / (2 * (i + 1))],
    conc = abs2(f(z) - f(x)) < 1 / (i + 1)
))

#
# The next block were all in the "arithmetical tests"
#

examples.append(Example(
    hyps = [x + 1 / y < 2, y < 0, y / x > 1, -2 <= x, x <= 2, -2 <= y, y <= 2, x**2 / y > (1 - x)]
))

examples.append(Example(
    hyps = [0 < x, x < y, 0 < u, u < v, 0 < w + z, w + z < r - 1,
          u + (1 + x)**2 * (2*w + 2*z + 3) >= 2 * v + (1 + y)**2 * (2*r + 1)]
))

examples.append(Example(
    hyps = [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x, u * (3*y)**2 + 1 >= x**2 * v + x]
))

# not valid
examples.append(Example(
    hyps = [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x, u* (3*y)**2 + 1 < x**2 * v + x]
))

examples.append(Example(
    hyps = [1 < x, 1 < y, 1 < z, 1 >= x * (1+z * y)]
))

examples.append(Example(
    hyps = [a > 0, a < 1, b > 0, b < 1, a+b < a * b]
))

# not valid
examples.append(Example(
    hyps = [a <= b * x / 2, 0 < c, 0 < d, d < 1, (1+d / (3*(c + 3))) * a >= b * x]
))

examples.append(Example(
    hyps = [x < 1, 1 < y, x * y > 1, u + x >= y + 1, x**2 * y < 2 - u * x * y]
))

examples.append(Example(
    hyps = [x * (y + z) <= 0, y + z > 0, x >= 0, x * w > 0]
))

examples.append(Example(
    hyps = [a**21 > 0, a**3 < 1, b**55 > 0, b < 1, a + b < a * b]
))

examples.append(Example(
    hyps = [0 < x, x < 1, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150]
))


####################################################################################################
#
# To run from the command line
#
####################################################################################################


if __name__ == '__main__':
    if len(sys.argv) == 1:
        print "Use 'python sample_problems.py list' to list the examples."
        print "Use 'python sample_problems.py 6 9 10' to run those examples."
        print "Use 'python sample_problems.py test_all' to run them all."
    elif sys.argv[1] == 'list':
        for i in range(len(examples)):
            print 'Example #{0!s}'.format(i)
            examples[i].show()
    elif sys.argv[1] == 'test_all':
        for i in range(len(examples)):
            if not examples[i].omit:
                examples[i].test()
        # TODO: import this?
        # timer.announce_times()
    else:
        for i in range(1, len(sys.argv)):
            try:
                examples[int(sys.argv[i])].test()
            except ValueError:
                print 'No example {0}.'.format(sys.argv[i])
