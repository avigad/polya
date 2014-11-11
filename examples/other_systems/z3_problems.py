 
import polya
import z3
import timeit
import polya.main.messages as messages
import sys
import fractions

Forall, And, Implies = z3.ForAll, z3.And, z3.Implies




####################################################################################################
#
# These are the examples discussed in section 6 of the paper.
#
####################################################################################################

a, b, c, d, e, i, K, m, n = z3.Reals('a b c d e i K m n')
r, s, t, u, v, w, x, y, z = z3.Reals('r s t u v w x y z')
eps = z3.Real('eps')

f = z3.Function('f', z3.RealSort(), z3.RealSort())
h = z3.Function('h', z3.RealSort(), z3.RealSort(), z3.RealSort())
g = z3.Function('g', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort())
log = z3.Function('log', z3.RealSort(), z3.RealSort())
exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())
abs = z3.Function('abs', z3.RealSort(), z3.RealSort())

# #mins = [z3.Function('min2', z3.RealSort(), z3.RealSort(), z3.RealSort()),
#         z3.Function('min2', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort()),
#         z3.Function('min2', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort(),
#                     z3.RealSort()),
#         z3.Function('min2', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort(),
#                     z3.RealSort(), z3.RealSort())
#  #       ]

min = z3.Function('min', z3.RealSort(), z3.RealSort(), z3.RealSort())

def minm(*args):
    if len(args) == 2:
        return min(*args)
    else:
        return min(args[0], minm(*args[1:]))

def maxm(*args):
    return -minm(*[-a for a in args])

def root(n, t):
    if n==2:
        return z3.Sqrt(t)
    elif n==3:
        return z3.Cbrt(t)
    else:
        return t**fractions.Fraction(1, n)
    
abs_axioms = [
    Forall([x], abs(x) >= 0),
    Forall([x], abs(x) >= x),
    Forall([x], abs(x) >= -x),
    Forall([x], Implies(x >= 0, abs(x) == x)),
    Forall([x], Implies(x <= 0, abs(x) == -x)),
    Forall([x, y], abs(x + y) <= abs(x) + abs(y))
]

abspos, absin1, absin2, abseq1, abseq2, abstriineq = (a for a in abs_axioms)

exp_axioms = [
    Forall([x], exp(x) > 0),
    Forall([x], exp(x) > x),
    Forall([x], Implies(x >= 0, exp(x) >= 1)),
    Forall([x], Implies(x > 0, exp(x) > 1)),
    Forall([x, y],
                                      Implies(x < y, exp(x) < exp(y))),
    Forall([x, y],
                                      Implies(x <= y, exp(x) <= exp(y))),
    Forall([x, y],
                                      Implies(x != y, exp(x) != exp(y))),
    Forall([x, y], exp(x+y) == exp(x)*exp(y)),
    Forall([x, y], exp(x*y) == exp(x)**y)
]

exppos, expin, exp01, exp02, expmon1, expmon2, expinj, expsum, exppow = (a for a in exp_axioms)

log_axioms = [
    Forall([x], Implies(x >= 1, log(x) >= 0)),
    Forall([x], Implies(x > 1, log(x) > 0)),
    Forall([x], Implies(x > 0, log(x) < x)),
    Forall([x, y], Implies(And(x > 0, x < y),
                                                               log(x) < log(y))),
    Forall([x, y], Implies(And(x > 0, x <= y),
                                                               log(x) <= log(y))),
    Forall([x, y], Implies(And(x > 0, y > 0, x != y),
                                                               log(x) != log(y))),
    Forall([x], Implies(x > 0, exp(log(x)) == x)),
    Forall([x], log(exp(x)) == x),
    Forall([x, y], Implies(And(x>0, y>0), log(x*y) == log(x) + log(y))),
    Forall([x, y], Implies(x>0, log(x**y) == y*log(x)))
]

logpos1, logpos2, login1, logmon1, logmon2, loginj, logexpinv1, logexpinv2, logprod, logpow = \
    (a for a in log_axioms)

min_axioms = [
    Forall([x, y], Implies(x <= y, min(x, y) == x)),
    Forall([x, y], Implies(x >= y, min(x, y) == y)),
    Forall([x, y, z], Implies(And(z <= x, z <= y), min(x, y) >= z))
]

mineq1, mineq2, minmax = (a for a in min_axioms)

####################################################################################################


class Example:

    def __init__(self, hyps=None, terms=None, conc=None, axioms=None, omit=False, comment=None):
        self.hyps = hyps if hyps else list()
        self.conc = conc
        self.terms = terms if terms else list()
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
        s.add(*[t==t for t in self.terms])
        if self.axioms:
            s.add(*self.axioms)
        #s.add(*(exp_axioms+log_axioms+abs_axioms+min_axioms))
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
    conc=((1 + y**2) * x >= 1 + y**2),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
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

examples.append(Example(
    hyps=[0 < u, u < v, 0 < z, z + 1 < w],
    conc=((u + v + z)**33 < (u + v + w + 1)**55),
    comment='Discussed in Avigad, Lewis, and Roux (2014). Z3 times out.',
    omit=True
))

examples.append(Example(
    hyps=[0 < u, u < (v**2 + 23)**3, 0 < z, z + 1 < w],
    conc=((u + (v**2 + 23)**3 + z)**3 < (u + (v**2 + 23)**3 + w + 1)**5),
))

examples.append(Example(
    axioms=[Forall([x], f(x) <= 1)],
    hyps=[u < v, 0 < w],
    conc=(u + w * f(x) < v + w),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, x <= y],
    conc=(u + f(x) < v + f(y)),
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
    hyps=[u < v, 1 < v, x <= y],
    conc=(f(x) + u < v**2 + f(y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, 1 < w, 2 < s, (w + s) / 3 < v, x <= y],
    conc=(f(x) + u < v**2 + f(y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[z > exp(x), w > exp(y)],
    axioms=[expsum, exppow],
    conc=(z**3 * w**2 > exp(3 * x + 2 * y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out.',
    omit=True
))

examples.append(Example(
    axioms=[logprod, logpow],
    hyps=[a > 1, b != 0, c > 0, log(b**2) > 4, log(c) > 1],
    conc=(log(a * b**2 * c**3) > 7),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[logpos1, logmon1],
    hyps=[u > 0, v > 0, log(x) > 2 * u + v],
    conc=(x > 1),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[mineq1, mineq2],
    hyps=[x < y, u <= v],
    conc=(u + minm(x + 2 * u, y + 2 * v) <= x + 3 * v),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[u > 0, v > 1],
    conc=(root(3, (u**9 * v**4)) > u**3 * v),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[abseq1, abstriineq],
    hyps=[y > 0],
    conc=(abs(3 * x + 2 * y + 5) < 4 * abs(x) + 3 * y + 6),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[mineq1, mineq2, abspos, exp01],
    conc=(exp(maxm(abs(x), y)) >= 1),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[expmon1, exp01, exppos, mineq1, mineq2],
    hyps=[y>maxm(2, 3*x), x > 0],
    conc=(exp(4*y - 3*x) > exp(6)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[logpos2, abspos],
    hyps=[y > 0],
    conc=(log(1 + abs(x) + y) > 0),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[expmon1, abstriineq],
    hyps=[abs(x) < 3, abs(y) < 2, w <= 0, exp(0) == 1],
    conc=(abs(x + 2 * y + z)  * exp(w) < (7 + abs(z))),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out',
    omit=True
))

examples.append(Example(
    hyps=[0 < x, x < y, u < v],
    axioms=[expmon1],
    conc=(2 * u + exp(1 + x + x**4) <= 2 * v + exp(1 + y + y**4)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
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
    axioms=[exppos, expmon2],
    hyps=[0 < x, x < y],
    conc=((1 + x**2) / (2 + exp(y)) < (2 + y**2) / (1 + exp(x))),
    comment='From Avigad and Friedman (2006).'
))

examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a) > 2, f(b) > 2],
    conc=(f(a + b) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a + b) > 2, f(c + d) > 2],
    conc=(f(a + b + c + d) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out',
    omit=True
))

examples.append(Example(
    hyps=[0 < x, 0 < y, y < 1, x * y > x + y],
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[0 < x, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150],
    comment='z3 times out',
    omit=True
))

examples.append(Example(
    hyps=[0 < x, -1 < y, y < 0, x**150 * (y+1)**150 > x**150 + (y+1)**150],
    comment='z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[abstriineq],
    hyps=[i >= 0, abs(f(y) - f(x)) < 1 / (2 * (i + 1)), abs(f(z) - f(y)) < 1 / (2 * (i + 1))],
    conc=(abs(f(z) - f(x)) < 1 / (i + 1)),
    comment='Discussed in Avigad, Lewis, and Roux (2014). z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[Forall([x], ceil(x) >= x)],
    hyps=[a < b, x > a, m >= ceil((b - a) / (x - a))],
    conc=(a + (b - a) / (m + 1) < x)
))

examples.append(Example(
    axioms=[Forall([m], Implies(m > 0, f(ceil(m)) < a + (b - a) / (ceil(m))))],
    hyps=[a < b, x > a, m >= ((b - a) / (x - a))],
    conc=(f(ceil(m)) < x),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'

))

examples.append(Example(
    hyps=[0 < x, y < z],
    conc=(x * y < x * z),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
#    split_depth=1,
#    split_breadth=10
))

examples.append(Example(
    hyps=[0 < x, x * y * z < 0, x * w > 0],
    conc=(w > y * z),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[mineq1, mineq2],
    conc=(minm(x, y) + maxm(x, y) == x + y),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    hyps=[x ** 2 + 2 * x + 1 < 0],
    comment='Discussed in Avigad, Lewis, and Roux (2014). ' +
            'An example where Polya does not terminate.'
))


#
# arithmetic examples
#

examples.append(Example(
    hyps=[x * (y + z) <= 0, y + z > 0, x >= 0, x * w > 0]
))

examples.append(Example(
    hyps=[0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x],
    conc=(u*(3*y)**2 + 1 < x**2 * v + x)
))

examples.append(Example(
    hyps=[0 < x, x < y, 0 < u, u < v, 0 < w + z, w + z < r - 1],
    conc=(u + (1+x)**2 * (2*w + 2*z + 3) < 2*v + (1+y)**2 * (2*r + 1))
))

examples.append(Example(
    hyps=[x + 1 / y < 2, y < 0, y / x > 1, -2 <= x, x <= 2, -2 <= y, y <= 2],
    conc=(x**2*y**(-1) <= 1-x)
))

examples.append(Example(
    hyps=[0 < u, u < v, 1 < x, x < y, 0 < w, w < z],
    conc=(u + x * w < v + y**2 * z)
))

examples.append(Example(
    hyps=[x + 1 / y < 2, y < 0, y / x > 1, -2 <= x, x <= 2, -2 <= y, y <= 2, x**2 / y > (1 - x)]
))

examples.append(Example(
    hyps=[0 < x, x < y, 0 < u, u < v, 0 < w + z, w + z < r - 1,
          u + (1 + x)**2 * (2 * w + 2 * z + 3) >= 2 * v + (1 + y)**2 * (2 * r + 1)]
))

examples.append(Example(
    hyps=[0 < x, x < 3 * y, u < v, v < 0, 1 < v**2, v**2 < x, u * (3 * y)**2 + 1 >= x**2 * v + x]
))

examples.append(Example(
    hyps=[0 < x, x < 3 * y, u < v, v < 0, 1 < v**2, v**2 < x, u * (3 * y)**2 + 1 < x**2 * v + x],
    comment='The hypotheses are consistent.'
))

examples.append(Example(
    hyps=[1 < x, 1 < y, 1 < z, 1 >= x * (1 + z * y)]
))

examples.append(Example(
    hyps=[a <= b * x / 2, 0 < c, 0 < d, d < 1, (1 + d / (3 * (c + 3))) * a >= b * x],
    comment='The hypotheses are consistent.'
))

examples.append(Example(
    hyps=[x < 1, 1 < y, x * y > 1, u + x >= y + 1, x**2 * y < 2 - u * x * y]
))

examples.append(Example(
    hyps=[a**21 > 0, a**3 < 1, b**55 > 0, b < 1, a + b < a * b]
))

examples.append(Example(
    hyps=[0 < x, y < z, y < 0, z > 0],
    conc=(x * y < x * z)
))

examples.append(Example(
    hyps=[0 < x, y < z, y == 0, z > 0],
    conc=(x * y < x * z)
))

examples.append(Example(
    hyps=[x > 1],
    conc=(1 + y**2 * x >= 1 + y**2)
))

examples.append(Example(
    hyps=[x > 1, z == y**2],
    conc=(1 + z * x >= 1 + z)
))

examples.append(Example(
    hyps=[x > 0, x * y * z < 0, x * w > 0],
    conc=(w > y * z),
    comment="Polya needs a case split on y to solve this."
))

examples.append(Example(
    hyps=[x == z, y == w, x > 0, y > 0],
    conc=(x * y == z * w)
))

examples.append(Example(
    hyps=[x > 2 * y, x == 3 * y],
    conc=(y > 0)
))


#
# examples involving function symbols
#

examples.append(Example(
    hyps=[x == y, f(x) != f(y)]
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x < y, f(x) < f(y)))],
    hyps=[a < b],
    conc=(f(a) < f(b))
))

examples.append(Example(
    axioms=[Forall([x], f(x) > 0)],
    hyps=[f(x) < y, y < z, z < f(x)]
))

examples.append(Example(
    axioms=[Forall([x, y], f(x * y) == f(x) * f(y)), Forall([x], Implies(x > 2, f(x) < 0))],
    hyps=[x > 1, y > 2, f(x * y) > 0],
    comment='z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[Forall([x, y], g(x, y, x * y) > 0)],
    hyps=[g(a, b, c * d) < 0, a > 0, b > 0, a == c, b == d]
))

examples.append(Example(
    axioms=[Forall([x, y], g(x, y, x + y) > 0)],
    hyps=[g(e, b, c + d) < 0, a > 0, b > 0, a == c, b == d, a == e]
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x < y, f(x) < f(y)))],
    hyps=[0 < r, s > 1, 0 < x, x < y, w > z, z + f(x) > w + f(s * (y + r))]
))

examples.append(Example(
    axioms=[Forall([x, y], (f(x) + f(y)) / 2 >= f((x + y) / 2))],
    hyps=[f(x) + f(y) < z, f((x + y) / 2) > 4 * z, z > 0]
))

examples.append(Example(
    axioms=[Forall([x, y], (f(x) + f(y)) / 2 >= f((x + y) / 2))],
    hyps=[z > 0, f(x) + f(y) - z < 0, f((x + y)/2) - 4 * z > 0]
))

examples.append(Example(
    axioms=[Forall([x, y], f((x * y) / 2) <= (f(x) * f(y)) / 2)],
    hyps=[z > 0, z * f(x) * f(y) < 0, 4 * z * f(x * y / 2) > 0],
    comment='Polya needs a split on f(x). z3 times out',
    omit=True
))


#
# min and max
#

examples.append(Example(
    axioms=[mineq1, mineq2],
    hyps=[x <= y],
    conc=(minm(x, y) == x)
))

examples.append(Example(
    axioms=[mineq1, mineq2],
    hyps=[0 < x, x <= y],
    conc=(2 * x + minm(w, z) < 3 * y + w)
))

examples.append(Example(
    axioms=[mineq1, mineq2, minmax],
    hyps=[x < u, y < u, z < u, x < v, y < v, z < v],
    conc=(maxm(x, y, z) < minm(u, v))
))

examples.append(Example(
    axioms=[mineq1, mineq2, minmax],
    hyps=[x < y, u < v],
    conc=(maxm(x + u, 2 * x + u) < maxm(y + v, 2 * y + v))
))


#
# abs
#

examples.append(Example(
    axioms=[abstriineq],
    conc=(abs(3 * x + 2 * y) <= 3 * abs(x) + 4 * abs(y)),
    comment='z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[abstriineq, abspos],
    conc=(abs(x - y) >= abs(y) - abs(x)),
    comment='z3 times out',
    omit=True
))

examples.append(Example(
    axioms=[abstriineq],
    conc=(abs(x - z) <= abs(x - y) + abs(y - z))
))

examples.append(Example(
    axioms=[abstriineq],
    conc=(abs(2 * x - z) <= abs(2 * x - y) + abs(y - z)),
))

examples.append(Example(
    axioms=[abstriineq, exp01, expmon1],
    hyps=[abs(x) < 3, abs(y) < 2, w >= 0],
    conc=(abs(x + 2 * y + z) < (7 + abs(z)) * exp(w)),
    comment='z3 times out',
    omit=True
))


#
# exp and log
#

examples.append(Example(
    conc=(exp(x + y) == exp(x) * exp(y))
))

examples.append(Example(
    terms=[log(exp(x))],
    conc=(log(1 + x**2 + exp(x)) > x)
))

examples.append(Example(
    hyps=[0 < x, 3 < y, u < v],
    conc=(2 * u + exp(10) <= 2 * v + exp(1 + y**2))
))


#
# combinations of built-in functions
#

# Follows from x > log(x) >= minm(...) > 1
examples.append(Example(
    axioms=[login1, mineq2, mineq1],
    hyps=[minm(exp(3 * x), exp(9 * x**2 - 2), log(x)) > 1, x > 0],
    conc=(x>1)
))

examples.append(Example(
    axioms=[logexpinv1, logexpinv2, mineq1, mineq2],
    terms=[log(exp(3 * x))],
    conc=(log(maxm(exp(2 * x), exp(3 * x))) >= 3 * x),
    comment='z3 times out',
    omit=True
))


#
# problems Polya does not get
#

# The Pythagorean Theorem.
a1, a2, a3, b1, b2, b3 = z3.Reals('a1 a2 a3 b1 b2 b3')
examples.append(Example(
    hyps=[(b2-  b1) / (a2 - a1) == -(a3 - a2) / (b3 - b2)],
    conc=(root(2, (b3 - b1)**2 + (a3 - a1)**2) == root(2, (b2 - b1)**2 + (a2 - a1)**2) +
          root(2, (b3 - b2)**2 - (a3 - a2)**2))
))

examples.append(Example(
    hyps=[-1 <= x, x <= 1],
    conc=(-1 <= 4*x**3 - 3*x),
    comment="Along with the following, is equivalent to an example from McLaughlin and Harrison"
))

examples.append(Example(
    hyps=[-1 <= x, x <= 1],
    conc=(1 >= 4*x**3 - 3*x),
    comment="Along with the previous, is equivalent to an example from McLaughlin and Harrison"
))

# These came from http://web.mit.edu/~holden1/www/math/high_school/awesome_math/Inequalities.pdf

examples.append(Example(
    hyps=[x>0, y>0, z>0],
    conc=(x**2/y**2 + y**2/z**2 + z**2/x**2 >= x/z + y/x + z/y),
    comment="We should not solve this even with case splits. But it's a good stress test for split."
))

examples.append(Example(
    hyps=[a>0, b>0, c>0],
    conc=(a*b/(a+b) + b*c/(b+c) + a*c/(a+c) <= 3*(a*b + b*c + c*a)/(2*(a+b+c)))
))

examples.append(Example(
    hyps=[a>0, b>0, c>0],
    conc=(a/(b+c) + b/(c+a) + c/(a+b) >= fractions.Fraction(3, 2))
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
