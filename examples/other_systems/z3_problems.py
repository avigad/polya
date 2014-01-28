import polya
import z3
import timeit

u, v, w, x, y, z = polya.Vars('u v w x y z')
a, b, c, d, e = z3.Reals('a b c d e')
f = polya.Func('f')
g = z3.Function('g', z3.RealSort(), z3.RealSort())


####################################################################################################
#
# Examples from the paper
#
####################################################################################################

def example1():
    polya.solve(0 < u, u < v, v < 1, 2 <= x, x <= y, 2 * u**2 * x >= v * y**2)


def z3example1():
    u, v, x, y = z3.Reals('u v x y')
    z3.solve(0 < u, u < v, v < 1, 2 <= x, x <= y, 2 * u**2 * x >= v * y**2)


def example2():
    polya.solve(x > 1, (1 + y**2) * x <= 1 + y**2)


def z3example2():
    x, y = z3.Reals('x y')
    z3.solve(x > 1, (1 + y**2) * x <= 1 + y**2)


def example3():
    polya.solve(0 < x, x < 1, 1/(1 - x) >= 1/(1 - x**2))


def z3example3():
    x = z3.Real('x')
    z3.solve(0 < x, x < 1, 1/(1 - x) >= 1/(1 - x**2))

def example4():
    s = polya.Solver()
    s.add(u < v, x <= y, u + f(x) > v + f(y))
    s.add(polya.Forall([x, y], polya.Implies(x <= y, f(x) <= f(y))))
    s.check()

def z3example4():
    u, v, x, y = z3.Reals('u v x y')
    s = z3.Solver()
    s.add(u < v, x <= y, u + g(x) > v + g(y))
    s.add(z3.ForAll([x, y], z3.Implies(x <= y, g(x) <= g(y))))
    s.check()


def example5():
    s = polya.Solver()
    s.add(u < v, 0 < w, u + w*f(x) >= v + w)
    s.add(polya.Forall([x], f(x) <= 1))
    s.check()


def z3example5():
    u, v, w, x, y = z3.Reals('u v w x y')
    s = z3.Solver()
    s.add(u < v, 0 < w, u + w*g(x) >= v + w)
    s.add(z3.ForAll([x], g(x) <= 1))
    s.check()

def example6():
    exp = polya.Func('exp')
    s = polya.Solver()
    s.add(0 < x, x < y, u < v, 2*u + exp(1 + x + x**4) >= 2*v + exp(1 + y + y**4))
    s.add(polya.Forall([x, y], polya.Implies(x<y, exp(x) < exp(y))))
    s.check()

def z3example6():
    u, v, w, x, y = z3.Reals('u v w x y')
    exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(0 < x, x < y, u < v, 2*u + exp(1 + x + x**4) >= 2*v + exp(1 + y + y**4))
    s.add(z3.ForAll([x, y], z3.Implies(x<y, exp(x) < exp(y))))
    s.check()

def example7():
    n, K, e, C = polya.Vars('n K e C')
    polya.solve(n <= (K/2)*x, 0 < C, 0 < e < 1, (1 + e/(3*(C + 3)))*n >= K*x)


def z3example7():
    n, K, e, C, x = z3.Reals('n K e C x')
    z3.solve(n <= (K/2)*x, 0 < C, 0 < e < 1, (1 + e/(3*(C + 3)))*n >= K*x)


def example8():
    # = test1()
    polya.solve(0 < x, x < y, (1 + x**2)/(2 + y)**17 >= (1 + y**2)/(2 + x)**10)


def z3example8():
    u, v, w, x, y = z3.Reals('u v w x y')
    z3.solve(0 < x, x < y, (1 + x**2)/(2 + y)**17 >= (1 + y**2)/(2 + x)**10)


def example9():
    # = test2()
    exp = polya.Func('exp')

    s = polya.Solver()
    s.add(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))

    s.add(polya.Forall([x, y], polya.And(polya.Implies(x<y, exp(x)<exp(y)),
                                                            exp(x)>0)))

    s.check()


def z3example9():
    x, y = z3.Reals('x y')
    exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))

    s.add(z3.ForAll([x, y], z3.And(z3.Implies(x<y, exp(x)<exp(y)),
                                                            exp(x)>0)))
    s.check()


def example10():
    polya.solve(x>0, x<1, y>0, y<1, (x+y)-(x*y) <= 0)


def z3example10():
    x, y = z3.Reals('x y')
    z3.solve(x>0, x<1, y>0, y<1, (x+y)-(x*y) <= 0)


def example11():
    polya.solve(x>0, x<1, y>0, y<1, x**1000 + y**1000 - x**1000*y**1000 <= 0)


def z3example11():
    x, y = z3.Reals('x y')
    z3.solve(x>0, x<1, y>0, y<1, x**1000 + y**1000 - x**1000*y**1000 <= 0)

def example12():
    polya.solve(x**2 + 2*x + 1 < 0)


def z3example12():
    x = z3.Real('x')
    z3.solve(x**2 + 2*x + 1 < 0)


####################################################################################################


# This example comes from Agigad and Friedman (2006)
# Solved in ~.08 seconds
def test1():
    polya.solve(0 < x, x < y, (1 + x**2)/(2 + y)**17 >= (1 + y**2)/(2 + x)**10)


# solved in ~.5 seconds
def z3test1():
    s = z3.Solver()
    s.add(0<a, a<b, (1+a**2)/(2+b)**17 >= (1+b**2)/(2+a)**10)
    print s.check()

# This example comes from Avigad and Friedman (2006)
# solved in ~.1 seconds
def test2():
    exp = polya.Func('exp')

    B = polya.Blackboard()
    B.assert_comparisons(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))

    fm = polya.FunctionModule([polya.Forall([x, y], polya.And(polya.Implies(x<y, exp(x)<exp(y)),
                                                            exp(x)>0))])

    fm.update_blackboard(B)
    polya.run(B)

# Not solved.
def z3test2():
    s = z3.Solver()
    exp = z3.Function('exp', z3.RealSort(), z3.RealSort())
    s.add(0<a, a<b, (1+a**2)/(2+exp(b))>=(2+b**2)/(1+exp(a)))
    s.add(z3.ForAll([a, b], z3.And(z3.Implies(a<b, exp(a)<exp(b)), exp(a)>0)))
    print s.check()

# From the Isabelle mailing list- Isabelle will not solve automatically.
# solved in ~.02 seconds.
def test3():
    polya.solve(x>0, x<1, y>0, y<1, (x+y)-(x*y) <= 0)

# Solves this one in. 0.004 sec
def z3test3():
    s = z3.Solver()
    s.add(a>0, a<1, b>0, b<1, (a+b)-(a*b) <= 0)
    print s.check()

# A variant on the above.
# Solved in ~.03 seconds.
def test4():
    polya.solve(0 < x, x < 1, 0 < y, y < 1, x**150*y**150 > x**150+y**150)

# Does not finish.
def z3test4():
    s = z3.Solver()
    s.add(a>0, a<1, b>0, b<1, (a**150 +b) < (a**150*b**150))
    print s.check()

# solved in .005 sec
def test5():
    S = polya.Solver()
    f = polya.Func('f')
    S.add(x<y, f(x)>f(y))
    S.add_axiom(polya.Forall([x, y], polya.Implies(x<y, f(x)<f(y))))
    S.check()

# solved in .005 sec, but sometimes much longer??
def z3test5():
    s = z3.Solver()
    f = z3.Function('exp', z3.RealSort(), z3.RealSort())
    s.add(a<b)
    s.add(f(a)>f(b))
    s.add(z3.ForAll([a, b], z3.Implies(a<b, f(a)<f(b))))
    print s.check()

# solved in .04 sec
def test6():
    f = polya.Func('f')
    fm = polya.FunctionModule(
        [polya.Forall([x, y], (f(x)+f(y))/2 >= f((x+y)/2))]
    )

    B = polya.Blackboard()
    B.assert_comparisons(z>0, f(x)+f(y)-z<0, f((x+y)/2)-4*z>0)
    fm.update_blackboard(B)

    polya.run(B)

# solved in .007 sec
def z3test6():
    f = z3.Function('f', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(z3.ForAll([a, b], (f(a)+f(b))/2 >= f((a+b)/2)))
    s.add(c>0, f(a)+f(b)-c<0, f((a+b)/2)-4*c>0)

    print s.check()

# solved in .02 sec
def test7():
    f = polya.Func('f')
    fm = polya.FunctionModule(
        [polya.Forall([x, y], f(x*y)==f(x)*f(y)),
         polya.Forall([x], polya.Implies(x>2, f(x)<0))]
    )

    C = polya.Blackboard()
    C.assert_comparisons(x>1, y>2, f(x*y)>0)
    fm.update_blackboard(C)

    polya.run(C)

#times out
def z3test7():
    f = z3.Function('f', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(z3.ForAll([a, b], f(a*b) == f(a)*f(b)))
    s.add(z3.ForAll([a], z3.Implies(a>2, f(a)<0)))
    s.add(a>1, b>2, f(a*b)>0)

    print s.check()

# a b c d e
# u v w x y
def test8():
    f = polya.Func('f')
    S = polya.Solver()
    S.add(f(y, v, w+x)<0, u>0, v>0, u==w, v==x, u==y)

    S.add_axiom(polya.Forall([x, y], f(x, y, x+y)>0))
    S.check()


def z3test8():
    f = z3.Function('f', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    s.add(z3.ForAll([a, b], f(a, b, a+b) > 0))
    s.add(f(e, b, c + d)<0, a>0, b>0, a == c, b == d, a == e)

    print s.check()


# solved in .08 sec
def test9a():
    ceil = polya.Func('ceil')
    x, a, b, m = polya.Vars('x, a, b, m')
    S = polya.Solver()
    S.add_axiom(polya.Forall([x], ceil(x) >= x))
    S.add(a < b, x > a, m >= ceil((b - a) / (x - a)))
    S.add(a + (b - a) / (m + 1) >= x)
    S.check()

# not solved
def z3test9a():
    ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    x = z3.Real('x')
    s.add(z3.ForAll([x], ceil(x) >= x))
    m = z3.Real('m')
    s.add(a<b, x>a, m>=ceil((b-a)/x-a))
    s.add(a+(b-a)/(m+1)>= x)
    print s.check()


# solved in .08 sec
def test9():
    ceil = polya.Func('ceil')
    f = polya.Func('f')
    x, a, b, m = polya.Vars('x, a, b, m')
    S = polya.Solver()
    S.add_axiom(polya.Forall([x], ceil(x) >= x))
    S.add_axiom(polya.Forall([m], f(m) < a + (b - a) / (m + 1)))
    S.add(a < b, x > a, m >= ceil((b - a) / (x - a)))
    S.add(f(m) >= x)
    S.check()

# not solved
def z3test9():
    ceil = z3.Function('ceil', z3.RealSort(), z3.RealSort())
    f = z3.Function('f', z3.RealSort(), z3.RealSort())
    s = z3.Solver()
    x = z3.Real('x')
    m = z3.Real('m')
    s.add(z3.ForAll([x], ceil(x) >= x))
    s.add(z3.ForAll([m], f(m) < a+ (b-a)/(m+1)))
    s.add(a<b, x>a, m>=ceil((b-a)/x-a))
    s.add(f(m)>=x)
    print s.check()


def test10():
    abs2 = polya.Func('abs')
    f = polya.Func('f')
    x, y, z, i = polya.Vars('x, y, z, i')
    S = polya.Solver()
    S.add_axiom(polya.Forall([x,y], abs2(x + y) <= abs2(x) + abs2(y)))
    S.add_axiom(polya.Forall([x], abs2(x) == abs2(-1*x)))
    S.add(i >= 0)
    S.add(abs2(f(x) - f(y)) < 1 / (2 * (i + 1)))
    S.add(abs2(f(y) - f(z)) < 1 / (2 * (i + 1)))
    S.add(abs2(f(x) - f(z)) >= 1 / (i + 1))
    S.check()

def z3test10():
    abs2 = z3.Function('abs', z3.RealSort(), z3.RealSort())
    f = z3.Function('f', z3.RealSort(), z3.RealSort())
    x, y, z, i = z3.Reals('x y z i')
    S = z3.Solver()
    S.add(z3.ForAll([x,y], abs2(x + y) <= abs2(x) + abs2(y)))
    S.add(i >= 0, abs2(f(y) - f(x)) < 1 / (2 * (i + 1)), abs2(f(z) - f(x)) < 1 / (2 * (i + 1)))
    S.add(abs2(f(z) - f(x)) >= 1 / (i + 1))
    print S.check()

t = timeit.default_timer()

test10()
#z3test10()




print round(timeit.default_timer() - t, 3)
