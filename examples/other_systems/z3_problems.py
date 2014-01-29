import polya
import z3
import timeit
import polya.main.messages as messages
import sys

m, u, v, w, x, y, z = z3.Reals('m u v w x y z')
a, b, c, d, e, i = z3.Reals('a b c d e i')
#f = polya.Func('f')
f = z3.Function('f', z3.RealSort(), z3.RealSort())
g = z3.Function('g', z3.RealSort(), z3.RealSort())
ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())
abs2 = z3.Function('abs', z3.RealSort(), z3.RealSort())

####################################################################################################
#
# These are the examples discussed in section 6 of the paper.
#
####################################################################################################


def z3example1():
    # solved
    s = z3.Solver()
    s.add(0 < u, u < v, v < 1, 2 <= x, x <= y, 2 * u**2 * x >= v * y**2)
    print s.check()


def z3example2():
    # solved
    s = z3.Solver()
    s.add(x > 1, (1 + y**2) * x < 1 + y**2)
    print s.check()


def z3example3():
    # solved
    s = z3.Solver()
    s.add(x > 1, z == y**2, 1 + z * x < 1 + z)
    print s.check()


def z3example4():
    # solved
    s = z3.Solver()
    s.add(0 < x, x < 1, 1/(1 - x) <= 1/(1 - x**2))
    print s.check()


def z3example5():
    # solved
    s = z3.Solver()
    s.add(u < v, x <= y, u + f(x) >= v + f(y))
    s.add(z3.ForAll([x, y], z3.Implies(x <= y, f(x) <= f(y))))
    print s.check()


def z3example6():
    # not solved
    s = z3.Solver()
    s.add(u < v, 1 < v, x <= y, f(x) + u >= v**2 + f(y))
    s.add(z3.ForAll([x, y], z3.Implies(x <= y, f(x) <= f(y))))
    print s.check()


def z3example7():
    # not solved
    s = z3.Solver()
    s.add(u < v, 1 < w, 2 < z, (w + z) / 3 < v, x <= y, f(x) + u >= v**2 + f(y))
    s.add(z3.ForAll([x, y], z3.Implies(x <= y, f(x) <= f(y))))
    print s.check()

def z3example8():
    # solved
    s = z3.Solver()
    s.add(u < v, 0 < w, u + w*f(x) >= v + w)
    s.add(z3.ForAll([x], f(x) <= 1))
    print s.check()


def z3example9():
    # solved
    s = z3.Solver()
    s.add(u < v, 0 < w, u + w * (f(x) - 1) >= v + w)
    s.add(z3.ForAll([x], f(x) <= 2))
    print s.check()


def z3example10():
    # not solved
    exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(0 < x, x < y, u < v, 2*u + exp(1 + x + x**4) >= 2*v + exp(1 + y + y**4))
    s.add(z3.ForAll([x, y], z3.Implies(x<y, exp(x) < exp(y))))
    print s.check()


def z3example11():
    # z3 times out here.
    print 'TIMES OUT- SKIPPED'
    return
    s = z3.Solver()
    s.add(f(a) > 2, f(b) > 2, f(a+b) <= 4)
    s.add(z3.ForAll([x, y], f(x+y) == f(x)*f(y)))
    print s.check()


def z3example12():
    # z3 times out here.
    print 'TIMES OUT- SKIPPED'
    return
    s = z3.Solver()
    s.add(f(a + b) > 2, f(c + d) > 2, f(a + b + c + d) <= 4)
    s.add(z3.ForAll([x, y], f(x+y) == f(x)*f(y)))
    print s.check()


def z3example13():
    # solved
    s = z3.Solver()
    n, K, e, C, x = z3.Reals('n K e C x')
    s.add(n < (K/2)*x, 0 < C, 0 < e, e < 1, 0 <= n, (1 + e/(3*(C + 3)))*n >= K*x)
    print s.check()


def z3example14():
    # solved
    s = z3.Solver()
    s.add(0 < x, x < y, (1 + x**2)/(2 + y)**17 >= (1 + y**2)/(2 + x)**10)
    print s.check()


def z3example15():
    # DOES NOT SOLVE
    exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))

    s.add(z3.ForAll([x, y], z3.And(z3.Implies(x<y, exp(x)<exp(y)),
                                                            exp(x)>0)))
    print s.check()


def z3example16():
    # z3 times out (on my laptop)
    print 'TIMES OUT- SKIPPED'
    return
    s = z3.Solver()
    s.add(0 < x, 0 < y, y < 1, x**150 * y**150 > x**150 + y**150)
    print s.check()


def z3example17():
    # z3 times out (on my laptop)
    print 'TIMES OUT- SKIPPED'
    return
    s = z3.Solver()
    s.add(0 < x, -1 < y, y < 0, x**150 * (y+1)**150 > x**150 + (y+1)**150)
    print s.check()


def z3example18():
    # not solved
    s = z3.Solver()
    s.add(a < b, x > a, m >= ceil((b - a) / (x - a)), (a + (b - a) / (m + 1) >= x))
    s.add(z3.ForAll([x], ceil(x) >= x))
    print s.check()


def z3example19():
    # not solved
    s = z3.Solver()
    s.add(a < b, x > a, m >= ((b - a) / (x - a)), f(ceil(m)) >= x)
    s.add(z3.ForAll([m], z3.Implies(m > 0, f(ceil(m)) < a + (b - a) / (ceil(m)))))
    s.add(z3.ForAll([x], ceil(x) >= x))
    print s.check()


def z3example20():
    # solved
    s = z3.Solver()
    s.add(i >= 0, abs2(f(y) - f(x)) < 1 / (2 * (i + 1)), abs2(f(z) - f(y)) < 1 / (2 * (i + 1)))
    s.add(abs2(f(z) - f(x)) >= 1 / (i + 1))
    s.add(z3.ForAll([x, y], abs2(x+y) <= abs2(x) + abs2(y)))
    print s.check()


def z3example20a():
    # solved (using z3's abs instead of a "fake" one)
    s = z3.Solver()
    s.add(i >= 0, abs(f(y) - f(x)) < 1 / (2 * (i + 1)), abs(f(z) - f(y)) < 1 / (2 * (i + 1)))
    s.add(abs(f(z) - f(x)) >= 1 / (i + 1))


def z3example21():
    # solved
    s = z3.Solver()
    s.add(x**2 + 2*x + 1 < 0)
    print s.check()





def test_time(example):
    t = timeit.default_timer()
    rounds = 10
    for i in range(rounds):
        eval(example)
    tot = timeit.default_timer() - t
    return round(float(tot)/rounds, 3)


####################################################################################################
#
# To run from the command line
#
####################################################################################################


if __name__ == '__main__':

    t = timeit.default_timer()

    # perform command
    if len(sys.argv) == 1:
        print "Use 'python z3_problems.py list' to list the examples."
        print "Use 'python z3_problems.py 6 9 10' to run those examples."
        print "Use 'python z3_problems.py test_all' to run them all."
    else:
        if sys.argv[1] == 'list':
            for i in range(1, 22):
                print 'Example #{0!s}'.format(i)
                #examples[i].show()
                eval("z3example{}()".format(i))
                print
        elif sys.argv[1] == 'test_all':
            for i in range(1, 22):
                print 'Example #{0!s}'.format(i)
                #examples[i].show()
                eval("z3example{}()".format(i))
                print
            print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
        else:
            for i in range(1, len(sys.argv)):
                print 'Example #{0!s}'.format(i)
                #examples[i].show()
                eval("z3example{}()".format(i))
                print