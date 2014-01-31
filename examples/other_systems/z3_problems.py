import polya
import z3
import timeit
import polya.main.messages as messages
import sys

Forall, And, Implies = z3.ForAll, z3.And, z3.Implies

class Example:

    def __init__(self, hyps=None, conc=None, axioms=None, omit=False, comment=None):
        self.hyps = hyps if hyps else list()
        self.conc = conc
        self.axioms = axioms if axioms else list()
        self.comment=comment
        self.omit = omit    # flag to omit from 'test_all'

    def show(self):
        for a in self.axioms:
            print 'Axiom: {0!s}'.format(a)
        for h in self.hyps:
            print 'Hypothesis: {0!s}'.format(h)
        if self.conc:
            print 'Conclusion: {0!s}'.format(self.conc)
        else:
            print 'Conclusion: False'
        if self.comment:
            print 'Comment: {0}'.format(self.comment)
        if self.omit:
            print "(Omitted from 'test_all')"
        print

    def test(self):
        self.show()
        s = z3.Solver()
        s.add(*self.hyps)
        if self.axioms:
            s.add(*self.axioms)
        if self.conc:
            s.add(z3.Not(self.conc))
        t = timeit.default_timer()
        val = str(s.check())
        if val == 'unsat':
            if self.conc:
                print 'Conclusion true'
            else:
                print 'Hypotheses inconsistent'
        elif val == "sat":
            if self.conc:
                print 'Conclusion does not follow'
            else:
                print 'Hypotheses are consistent'
        else:
            print 'z3 failed:', val

        print 'Ran in', round(timeit.default_timer()-t, 3), 'seconds'
        print


####################################################################################################
#
# These are the examples discussed in section 6 of the paper.
#
####################################################################################################

a, b, c, d, e, i, K, m, n = z3.Reals('a b c d e i K m n')
r, s, t, u, v, w, x, y, z = z3.Reals('r s t u v w x y z')
eps = z3.Real('eps')

f = z3.Function('f', z3.RealSort(), z3.RealSort())
g = z3.Function('g', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort())
exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())
abs2 = z3.Function('abs', z3.RealSort(), z3.RealSort())

examples = list()

#
# examples from the paper
#

examples.append(Example(
    hyps=[0 < u, u < v, v < 1, 2 <= x, x <= y],
    conc=(2 * u**2 * x < v * y**2),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[x > 1],
    conc=((1 + y**2) * x >= 1 + y**2)
))

examples.append(Example(
    hyps=[0 < x, x < 1],
    conc=(1 / (1 - x) > 1 / (1 - x**2)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[0 < u, u < v, 0 < z, z + 1 < w],
    conc=((u + v + z)**3 < (u + v + w + 1)**5),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

# times out
examples.append(Example(
    hyps=[0 < u, u < v, 0 < z, z + 1 < w],
    conc=((u + v + z)**33 < (u + v + w + 1)**55),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit=True
))

examples.append(Example(
    hyps=[0 < u, u < (v**2 + 23)**3, 0 < z, z + 1 < w],
    conc=((u + (v**2 + 23)**3 + z)**3 < (u + (v**2 + 23)**3 + w + 1)**5),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, x <= y],
    conc=(u + f(x) < v + f(y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x], f(x) <= 1)],
    hyps=[u < v, 0 < w],
    conc=(u + w * f(x) < v + w),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x], f(x) <= 2)],
    hyps=[u < v, 0 < w],
    conc=(u + w * (f(x) - 1) < v + w),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, 1 < w, 2 < s, (w + s) / 3 < v, x <= y],
    conc=(f(x) + u < v + f(y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, 1 < v, x <= y],
    conc=(f(x) + u < v**2 + f(y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x < y, exp(x) < exp(y)))],
    hyps=[0 < x, x < y, u < v],
    conc=(2 * u + exp(1 + x + x**4) <= 2 * v + exp(1 + y + y**4)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x < y, exp(x) < exp(y)))],
    hyps=[0 < x, 3 < y, u < v],
    conc=(2 * u + exp(10) <= 2 * v + exp(1 + y**2))
))

# times out
examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a) > 2, f(b) > 2],
    conc=(f(a + b) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit=True
))

# times out
examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a + b) > 2, f(c + d) > 2],
    conc=(f(a + b + c + d) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit=True
))

examples.append(Example(
    hyps=[0 <= n, n < (K / 2) * x, 0 < c, 0 < eps, eps < 1],
    conc=((1 + eps / (3 * (c + 3))) * n < K * x),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[0 < x, x < y],
    conc=((1 + x**2) / (2 + y)**17 < (2 + y**2) / (2 + x)**10),
    comment='From Avigad and Friedman (2006).'
))

examples.append(Example(
    axioms=[Forall([x, y], And(Implies(x < y, exp(x) < exp(y)), exp(x) > 0))],
    hyps=[0 < x, x < y],
    conc=((1 + x**2) / (2 + exp(y)) < (2 + y**2) / (1 + exp(x))),
    comment='From Avigad and Friedman (2006).'
))

examples.append(Example(
    hyps=[0 < x, 0 < y, y < 1, x * y > x + y]
))

# times out
examples.append(Example(
    hyps=[0 < x, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150],
    omit=True
))

# times out
examples.append(Example(
    hyps=[0 < x, -1 < y, y < 0, x**150 * (y+1)**150 > x**150 + (y+1)**150],
    omit=True
))

# times out
examples.append(Example(
    axioms=[Forall([x, y], abs2(x + y) <= abs2(x) + abs2(y)), Forall(x, Implies(x >= 0, abs2(x) == x)),
	    Forall(x, Implies(x <= 0, abs2(x) == -x))],
    hyps=[i >= 0, abs2(f(y) - f(x)) < 1 / (2 * (i + 1)), abs2(f(z) - f(y)) < 1 / (2 * (i + 1))],
    conc=(abs2(f(z) - f(x)) < 1 / (i + 1)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit=True
))

examples.append(Example(
    axioms=[Forall([x], ceil(x) >= x)],
    hyps=[a < b, x > a, m >= ceil((b - a) / (x - a))],
    conc=(a + (b - a) / (m + 1) < x)
))

examples.append(Example(
    axioms=[Forall([x], ceil(x) >= x),
            Forall([m], Implies(m > 0, f(ceil(m)) < a + (b - a) / (ceil(m))))],
    hyps=[a < b, x > a, m >= ((b - a) / (x - a))],
    conc=(f(ceil(m)) < x),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'

))


####################################################################################################
#
# To run from the command line
#
####################################################################################################

if __name__ == '__main__':

    # perform command
    if len(sys.argv) == 1:
        print "Use 'python z3_problems.py list' to list the examples."
        print "Use 'python z3_problems.py 6 9 10' to run those examples."
        print "Use 'python z3_problems.py test_all' to run them all."
    else:
        if sys.argv[1] == 'list':
            for i in range(len(examples)):
                print '*** Example {0!s} ***'.format(i)
                examples[i].show()
        elif sys.argv[1] == 'test_all':
            t = timeit.default_timer()
            for i in range(len(examples)):
                if not examples[i].omit:
                    print '*** Example {0!s} ***'.format(i)
                    examples[i].test()
            print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
        # for a comparison of Fourier-Motzkin and polytope methods
        else:
            for i in range(1, len(sys.argv)):
                try:
                    examples[int(sys.argv[i])].test()
                except ValueError:
                    print 'No example {0}.'.format(sys.argv[i])
