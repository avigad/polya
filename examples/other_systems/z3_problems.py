import polya
import z3
import timeit
import polya.main.messages as messages
import sys

#m, u, v, w, x, y, z = z3.Reals('m u v w x y z')
#a, b, c, d, e, i = z3.Reals('a b c d e i')
#f = polya.Func('f')
#f = z3.Function('f', z3.RealSort(), z3.RealSort())
#g = z3.Function('g', z3.RealSort(), z3.RealSort())
#ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())
abs2 = z3.Function('abs', z3.RealSort(), z3.RealSort())
abs = z3.Function('abs', z3.RealSort(), z3.RealSort())


a, b, c, d, e, i, K, m, n = z3.Reals('a b c d e i K m n')
r, s, t, u, v, w, x, y, z = z3.Reals('r s t u v w x y z')
eps = z3.Real('eps')

f = z3.Function('f', z3.RealSort(), z3.RealSort())
g = z3.Function('g', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort())
exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())

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
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, x <= y],
    conc=(u + f(x) < v + f(y)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, 1 < v, x <= y],
    conc=(f(x) + u < v**2 + f(y))
))

examples.append(Example(
    axioms=[Forall([x, y], Implies(x >= y, f(x) >= f(y)))],
    hyps=[u < v, 1 < w, 2 < s, (w + s) / 3 < v, x <= y],
    conc=(f(x) + u < v**2 + f(y)),
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
    axioms=[Forall([x, y], Implies(x < y, exp(x) < exp(y)))],
    hyps=[0 < x, x < y, u < v],
    conc=(2 * u + exp(1 + x + x**4) <= 2 * v + exp(1 + y + y**4)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a) > 2, f(b) > 2],
    conc=(f(a + b) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit = True
))

examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a + b) > 2, f(c + d) > 2],
    conc=(f(a + b + c + d) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit = True
))

examples.append(Example(
    hyps=[n < (K / 2) * x, 0 < c, 0 <= n, 0 < eps, eps < 1],
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
    hyps=[0 < x, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150],
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit = True
))

examples.append(Example(
    hyps=[0 < x, -1 < y, y < 0, x**150 * (y+1)**150 > x**150 + (y+1)**150],
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit = True
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

examples.append(Example(
    axioms=[Forall([x, y], abs2(x + y) <= abs2(x) + abs2(y))],
    hyps=[i >= 0, abs(f(y) - f(x)) < 1 / (2 * (i + 1)), abs2(f(z) - f(y)) < 1 / (2 * (i + 1))],
    conc=(abs2(f(z) - f(x)) < 1 / (i + 1)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)',
    omit = True
))

#
# cases where Polya fails
#

examples.append(Example(
    hyps=[0 < x, y < z],
    conc=(x * y < x * z),
    comment='Polya fails here. Splitting on y and z will solve this.'
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
    conc=(1 + y**2 * x >= 1 + y**2),
    comment='Polya fails here. Splitting on y will solve this. See also the next example.'
))

examples.append(Example(
    hyps=[x > 1, z == y**2],
    conc=(1 + z * x >= 1 + z)
))

# Polya does not refute the hypotheses in the next example, although there is a contradiction.
# we get t6 = t1*t3*t5, t10=t3*t5, t1>0, t10>0, t6<0.
# but because the signs of t1 and t3 are unknown, the mul routine cannot find that contradiction.
examples.append(Example(
    axioms=[Forall([x, y], f((x * y) / 2) <= (f(x) * f(y)) / 2)],
    hyps=[z > 0, z * f(x) * f(y) < 0, 4 * z * f(x * y / 2) > 0],
    comment='Polya fails here. Need a split on f(x).',
    omit = True
))

examples.append(Example(
    hyps=[x ** 2 + 2 * x + 1 < 0],
    comment='An example where the method does not terminate.',
    omit=True
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
    omit = True
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

# def z3example1():
#     # solved
#     s = z3.Solver()
#     s.add(0 < u, u < v, v < 1, 2 <= x, x <= y, 2 * u**2 * x >= v * y**2)
#     print s.check()
#
#
# def z3example1a():
#     # solved
#     s = z3.Solver()
#     u = w**100 + 7*w**40 + 1
#     s.add(0 < u, u < v, v < 1, 2 <= x, x <= y, 2 * u**2 * x >= v * y**2)
#     print s.check()
#
#
# def z3example2():
#     # solved
#     s = z3.Solver()
#     s.add(x > 1, (1 + y**2) * x < 1 + y**2)
#     print s.check()
#
#
# def z3example2a():
#     # solved
#     s = z3.Solver()
#     y = z**100 + 7*z**40 + 1
#     s.add(x > 1, (1 + y**2) * x < 1 + y**2)
#     print s.check()
#
#
# def z3example3():
#     # solved
#     s = z3.Solver()
#     s.add(x > 1, z == y**2, 1 + z * x < 1 + z)
#     print s.check()
#
#
# def z3example4():
#     # solved
#     s = z3.Solver()
#     s.add(0 < x, x < 1, 1/(1 - x) <= 1/(1 - x**2))
#     print s.check()
#
# def z3example4a():
#     # solved
#     s = z3.Solver()
#     x = y**100 + 7*y**40 + 1
#     s.add(0 < x, x < 1, 1/(1 - x) <= 1/(1 - x**2))
#     print s.check()
#
#
# def z3example5():
#     # solved
#     s = z3.Solver()
#     s.add(u < v, x <= y, u + f(x) >= v + f(y))
#     s.add(z3.ForAll([x, y], z3.Implies(x <= y, f(x) <= f(y))))
#     print s.check()
#
#
# def z3example6():
#     # not solved
#     s = z3.Solver()
#     s.add(u < v, 1 < v, x <= y, f(x) + u >= v**2 + f(y))
#     s.add(z3.ForAll([x, y], z3.Implies(x <= y, f(x) <= f(y))))
#     print s.check()
#
#
# def z3example7():
#     # not solved
#     s = z3.Solver()
#     s.add(u < v, 1 < w, 2 < z, (w + z) / 3 < v, x <= y, f(x) + u >= v**2 + f(y))
#     s.add(z3.ForAll([x, y], z3.Implies(x <= y, f(x) <= f(y))))
#     print s.check()
#
# def z3example8():
#     # solved
#     s = z3.Solver()
#     s.add(u < v, 0 < w, u + w*f(x) >= v + w)
#     s.add(z3.ForAll([x], f(x) <= 1))
#     print s.check()
#
#
# def z3example9():
#     # solved
#     s = z3.Solver()
#     s.add(u < v, 0 < w, u + w * (f(x) - 1) >= v + w)
#     s.add(z3.ForAll([x], f(x) <= 2))
#     print s.check()
#
#
# def z3example10():
#     # not solved
#     exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
#     s = z3.Solver()
#     s.add(0 < x, x < y, u < v, 2*u + exp(1 + x + x**4) >= 2*v + exp(1 + y + y**4))
#     s.add(z3.ForAll([x, y], z3.Implies(x<y, exp(x) < exp(y))))
#     print s.check()
#
#
# def z3example10a():
#     # not solved
#     exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
#     s = z3.Solver()
#     s.add(0 < x, x < y, u < v, 2*u + exp(1 + x + x**4) >= 2*v + exp(1 + y + y**4))
#     s.add(z3.ForAll([x, y], z3.Implies(x<y, exp(x) < exp(y))))
#     s.add(z3.ForAll([x, y], z3.Implies(exp(x) < exp(y), x<y)))
#     s.add(z3.ForAll([x, y], z3.Implies(z3.And(x**4 < y**4, 0 <= y), x < y)))
#     print s.check()
#
#
# def z3example11():
#     # z3 times out here.
#     print 'TIMES OUT- SKIPPED'
#     return
#     s = z3.Solver()
#     s.add(f(a) > 2, f(b) > 2, f(a+b) <= 4)
#     s.add(z3.ForAll([x, y], f(x+y) == f(x)*f(y)))
#     print s.check()
#
#
# def z3example12():
#     # z3 times out here.
#     print 'TIMES OUT- SKIPPED'
#     return
#     s = z3.Solver()
#     s.add(f(a + b) > 2, f(c + d) > 2, f(a + b + c + d) <= 4)
#     s.add(z3.ForAll([x, y], f(x+y) == f(x)*f(y)))
#     print s.check()
#
#
# def z3example13():
#     # solved
#     s = z3.Solver()
#     n, K, e, C, x = z3.Reals('n K e C x')
#     s.add(n < (K/2)*x, 0 < C, 0 < e, e < 1, 0 <= n, (1 + e/(3*(C + 3)))*n >= K*x)
#     print s.check()
#
#
# def z3example14():
#     # solved
#     s = z3.Solver()
#     s.add(0 < x, x < y, (1 + x**2)/(2 + y)**17 >= (1 + y**2)/(2 + x)**10)
#     print s.check()
#
#
# def z3example14a():
#     # solved
#     s = z3.Solver()
#     s.add(0 < x, x < y, (1 + x**2)/(2 + y)**100 >= (1 + y**2)/(2 + x)**10)
#     print s.check()
#
#
# def z3example15():
#     # DOES NOT SOLVE
#     exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
#     s = z3.Solver()
#     s.add(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))
#
#     s.add(z3.ForAll([x, y], z3.And(z3.Implies(x<y, exp(x)<exp(y)),
#                                                             exp(x)>0)))
#     print s.check()
#
#
# def z3example15a():
#     # DOES NOT SOLVE
#     exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
#     s = z3.Solver()
#     s.add(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))
#
#     s.add(z3.ForAll([x, y], z3.And(z3.Implies(x<y, exp(x)<exp(y)),
#                                                             exp(x)>0)))
#     s.add(z3.ForAll([x, y], z3.Implies( z3.And(x**2 < y**2, 0 <= y), x < y)))
#     print s.check()
#
#
# def z3example16():
#     # z3 times out (on my laptop)
#     print 'TIMES OUT- SKIPPED'
#     return
#     s = z3.Solver()
#     s.add(0 < x, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150)
#     print s.check()
#
#
# def z3example17():
#     # z3 times out (on my laptop)
#     print 'TIMES OUT- SKIPPED'
#     return
#     s = z3.Solver()
#     s.add(0 < x, -1 < y, y < 0, x**150 * (y+1)**150 > x**150 + (y+1)**150)
#     print s.check()
#
#
# def z3example18():
#     # not solved
#     s = z3.Solver()
#     s.add(a < b, x > a, m >= ceil((b - a) / (x - a)), (a + (b - a) / (m + 1) >= x))
#     s.add(z3.ForAll([x], ceil(x) >= x))
#     print s.check()
#
#
# def z3example19():
#     # not solved
#     s = z3.Solver()
#     s.add(a < b, x > a, m >= ((b - a) / (x - a)), f(ceil(m)) >= x)
#     s.add(z3.ForAll([m], z3.Implies(m > 0, f(ceil(m)) < a + (b - a) / (ceil(m)))))
#     s.add(z3.ForAll([x], ceil(x) >= x))
#     print s.check()
#
#
# def z3example20():
#     # solved
#     s = z3.Solver()
#     s.add(i >= 0, abs2(f(y) - f(x)) < 1 / (2 * (i + 1)), abs2(f(z) - f(y)) < 1 / (2 * (i + 1)))
#     s.add(abs2(f(z) - f(x)) >= 1 / (i + 1))
#     s.add(z3.ForAll([x, y], abs2(x+y) <= abs2(x) + abs2(y)))
#     print s.check()
#
#
# def z3example20a():
#     # solved (using z3's abs instead of a "fake" one)
#     s = z3.Solver()
#     s.add(i >= 0, abs(f(y) - f(x)) < 1 / (2 * (i + 1)), abs(f(z) - f(y)) < 1 / (2 * (i + 1)))
#     s.add(abs(f(z) - f(x)) >= 1 / (i + 1))
#
#
# def z3example21():
#     # solved
#     s = z3.Solver()
#     s.add(x**2 + 2*x + 1 < 0)
#     print s.check()
#
#
# def z3example22():
#     # does not solve
#     s = z3.Solver()
#     exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
#     s.add(0 < x, 3 < y, u < v, 2*u + exp(10) >= 2*v + exp(1 + y**2))
#     s.add(z3.ForAll([x, y], z3.And(z3.Implies(x<y, exp(x)<exp(y)), exp(x)>0)))
#     print s.check()
#
#
# def z3example23():
#     # solves with exponent 10, not with exponent 100
#     s = z3.Solver()
#     s.add((u**6+1)**100 >= (u**6+2)**100)
#     print s.check()
#
#
# def z3example24():
#     s = z3.Solver()
#     s.add(u>0, v>0, (u**5+v**5+1)**19 >= (u**5+v**5+2)**19)
#     print s.check()
#
#
# def z3example25():
#     s = z3.Solver()
#     s.add( 0 < u, 0 < v, 1 < z, (u + v + z)**19 >= (u + v + z + 1)**19)
#     print s
#     print s.check()
#
#
# def z3example26():
#     s = z3.Solver()
#     s.add(0 < u, u < v,  0 < z, z + 1 < w, (u + v + z)**9 >= (u + v + w)**19)
#     print s.check()
#
#
# def test_time(example):
#     t = timeit.default_timer()
#     rounds = 10
#     for i in range(rounds):
#         eval(example)
#     tot = timeit.default_timer() - t
#     return round(float(tot)/rounds, 3)


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

# if __name__ == '__main__':
#
#     t = timeit.default_timer()
#
#     # perform command
#     if len(sys.argv) == 1:
#         print "Use 'python z3_problems.py list' to list the examples."
#         print "Use 'python z3_problems.py 6 9 10' to run those examples."
#         print "Use 'python z3_problems.py test_all' to run them all."
#     else:
#         if sys.argv[1] == 'list':
#             for i in range(1, 22):
#                 print 'Example #{0!s}'.format(i)
#                 #examples[i].show()
#                 eval("z3example{}()".format(i))
#                 print
#         elif sys.argv[1] == 'test_all':
#             for i in range(1, 22):
#                 print 'Example #{0!s}'.format(i)
#                 #examples[i].show()
#                 eval("z3example{}()".format(i))
#                 print
#             print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
#         else:
#             for i in sys.argv[1:]:#range(1, len(sys.argv)):
#                 print 'Example #{0!s}'.format(i)
#                 #examples[i].show()
#                 eval("z3example{}()".format(i))
#                 print