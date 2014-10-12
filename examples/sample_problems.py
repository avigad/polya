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
# TODO: improve command line interface
#
####################################################################################################


from polya import *
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
exp = Func('exp')
ceil = Func('ceil')

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

examples.append(Example(
    hyps=[0 < u, u < v, 0 < z, z + 1 < w],
    conc=((u + v + z)**33 < (u + v + w + 1)**55),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
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

examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a) > 2, f(b) > 2],
    conc=(f(a + b) > 4),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
))

examples.append(Example(
    axioms=[Forall([x, y], f(x + y) == f(x) * f(y))],
    hyps=[f(a + b) > 2, f(c + d) > 2],
    conc=(f(a + b + c + d) > 4),
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
    axioms=[Forall([x, y], And(Implies(x < y, exp(x) < exp(y)), exp(x) > 0))],
    hyps=[0 < x, x < y],
    conc=((1 + x**2) / (2 + exp(y)) < (2 + y**2) / (1 + exp(x))),
    comment='From Avigad and Friedman (2006).'
))

examples.append(Example(
    hyps=[0 < x, 0 < y, y < 1, x * y > x + y]
))

examples.append(Example(
    hyps=[0 < x, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150]
))

examples.append(Example(
    hyps=[0 < x, -1 < y, y < 0, x**150 * (y+1)**150 > x**150 + (y+1)**150]
))

examples.append(Example(
    axioms=[Forall([x, y], abs(x + y) <= abs(x) + abs(y))],
    hyps=[i >= 0, abs(f(y) - f(x)) < 1 / (2 * (i + 1)), abs(f(z) - f(y)) < 1 / (2 * (i + 1))],
    conc=(abs(f(z) - f(x)) < 1 / (i + 1)),
    comment='Discussed in Avigad, Lewis, and Roux (2014)'
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
    comment='Polya fails here. Need a split on f(x).'
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
    hyps=[x > 1, y > 2, f(x * y) > 0]
))

examples.append(Example(
    axioms=[Forall([x, y], f(x, y, x * y) > 0)],
    hyps=[f(a, b, c * d) < 0, a > 0, b > 0, a == c, b == d]
))

examples.append(Example(
    axioms=[Forall([x, y], f(x, y, x + y) > 0)],
    hyps=[f(e, b, c + d) < 0, a > 0, b > 0, a == c, b == d, a == e]
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
    hyps=[x > 0, x*y*z < 0, x*w > 0],
    conc=(w > y*z),
    comment="Need a case split on y to solve this."
))

examples.append(Example(
    hyps=[-1 <= x, x <= 1],
    conc=(-1 <= 4*x**3 -3*x),
    comment="Need a case split on x. Along with the following, is equivalent to an example from" +
    "McLaughlin and Harrison"
))

examples.append(Example(
    hyps=[-1 <= x, x <= 1],
    conc=(1 >= 4*x**3 -3*x),
    comment="Need a case split on x. Along with the previous, is equivalent to an example from" +
    "McLaughlin and Harrison"
))

####################################################################################################
#
# To run from the command line
#
####################################################################################################


if __name__ == '__main__':
    run_examples(examples, sys.argv)
    # # handle switches
    # if '-v' in sys.argv:
    #     messages.set_verbosity(messages.normal)
    #     sys.argv.remove('-v')
    # else:
    #     messages.set_verbosity(messages.quiet)
    # if '-fm' in sys.argv:
    #     set_solver_type('fm')
    #     sys.argv.remove('-fm')
    #
    # # perform command
    # if len(sys.argv) == 1:
    #     print "Use 'python sample_problems.py list' to list the examples."
    #     print "Use 'python sample_problems.py 6 9 10' to run those examples."
    #     print "Use 'python sample_problems.py test_all' to run them all."
    # else:
    #     show_configuration()
    #     if sys.argv[1] == 'list':
    #         for i in range(len(examples)):
    #             print '*** Example {0!s} ***'.format(i)
    #             examples[i].show()
    #     elif sys.argv[1] == 'test_all':
    #         t = timeit.default_timer()
    #         for i in range(len(examples)):
    #             if not examples[i].omit:
    #                 print '*** Example {0!s} ***'.format(i)
    #                 examples[i].test()
    #         print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
    #     # for a comparison of Fourier-Motzkin and polytope methods
    #     elif sys.argv[1] == 'test_all_comp':
    #         t = timeit.default_timer()
    #         for i in range(len(examples)):
    #             if not examples[i].omit:
    #                 print '*** Example {0!s} ***'.format(i)
    #                 set_solver_type('fm')
    #                 print '[Fourier-Motzkin]'
    #                 examples[i].test()
    #                 set_solver_type('poly')
    #                 print '[Poly]'
    #                 examples[i].test()
    #         print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
    #     else:
    #         for i in range(1, len(sys.argv)):
    #             try:
    #                 examples[int(sys.argv[i])].test()
    #             except ValueError:
    #                 print 'No example {0}.'.format(sys.argv[i])
