####################################################################################################
#
# examples.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Examples that illustrate how to use Polya.
#
####################################################################################################

from polya import *
import timeit
import polya.util.timer as timer

t = timeit.default_timer()

x, y, u, v, w, z, r = Vars('x, y, u, v, w, z, r')
a, b, c, d, e = Vars('a, b, c, d, e')
n, k, p = Vars('n, k, p')


def test1():
    B = Blackboard()
    B.assume(0 < x)
    B.assume(x < 3*y)
    B.assume(u < v)
    B.assume(v < 0)
    B.assume(1 < v**2)
    B.assume(v**2 < x)
    B.assume(u*(3*y)**2 + 1 >= x**2 * v + x)
    # This example has a model if the last inequality is <. FM blows up here, poly doesn't
    # It does not have a model if the last inequality is >=. Contradiction is found.
    # "0<x<3*y", "u<v<0", "1<v^2<x", "u*(3*y)^2+1 >= x^2*v+x"
    run(B)


def test2():
    messages.set_verbosity(messages.normal)
    B = Blackboard()

    B.assume(0 < x)
    B.assume(x < y)
    B.assume(0 < u)
    B.assume(u < v)
    B.assume(0 < w + z)
    B.assume(w + z < r - 1)
    B.assume(u + (1+x)**2 * (2*w + 2*z + 3) >= 2*v + (1+y)**2 * (2*r + 1))
    run(B)


def test3():
    messages.set_verbosity(messages.normal)
    B = Blackboard()

    # "x+1/y<2", "y<0", "y/x>1", "-2<=x<=2", "-2<=y<=2", "x^2*y^(-1)>1-x"
    B.assume(x+1/y<2, y<0, y/x>1, -2<=x, x<=2, -2<=y, y<=2, x**2*y**(-1)>1-x)
    run(B)

def test4():
    f = Func('f')
    a, b, c = Vars('a, b, c')

    B = Blackboard()

    fm = FunctionModule([Forall([x, y], Implies(x<y, f(x)<f(y)))])

    B.assume(a<b)
    B.assume(f(a) > f(b))
    try:
        fm.update_blackboard(B)
    except Contradiction:
        print 'Contradiction found from axiom module'

def test5():

    f = Func('f')
    x, y, z, w, r, s = Vars('x, y, z, w, r, s')

    B = Blackboard()

    fm = FunctionModule([Forall([x, y], Implies(x<y, f(x)<f(y)))])

    B.assume(0<r, s>1, 0<x, x<y, w>z, z+f(x)>w+f(s*(y+r)))

    try:
        fm.update_blackboard(B)
    except Contradiction:
        print 'Contradiction found from axiom module'

    run(B)
    # run(B)

def test6():
    f = Func('f')
    x, y, z, w, r, s = Vars('x, y, z, w, r, s')
    u, v = UVar(1), UVar(2)

    B = Blackboard()

    fm = FunctionModule(
        [Forall([x, y], (f(x)+f(y))/2 >= f((x+y)/2))]
    )

    B.assume(f(x)+f(y)<z, f((x+y)/2)>4*z, z>0)
    fm.update_blackboard(B)

    run(B)
    # run(B)

def test7():
    x, y, z = Vars('x, y, z')
    f = Func('f')
    fm = FunctionModule(
        [Forall([x, y], (f(x)+f(y))/2 >= f((x+y)/2))]
    )

    B = Blackboard()
    B.assume(z>0, f(x)+f(y)-z<0, f((x+y)/2)-4*z>0)
    fm.update_blackboard(B)

    run(B)
    # run(B)


def test8():
    x, y, z = Vars('x, y, z')
    f = Func('f')
    fm = FunctionModule(
        [Forall([x, y], f(x*y)==f(x)*f(y)),
         Forall([x], Implies(x>2, f(x)<0))]
    )

    C = Blackboard()
    C.assume(x>1, y>2, f(x*y)>0)
    fm.update_blackboard(C)

    run(C)

def test9():
    x, y, z = Vars('x, y, z')
    f = Func('f')
    fm = FunctionModule(
        [
            Forall([x, y], f((x*y)/2)<=(f(x)*f(y))/2)
        ]
    )

    C = Blackboard()
    C.assume(z>0, z*f(x)*f(y)<0, 4*z*f(x*y/2)>0)
    fm.update_blackboard(C)
    run(C)

    # This example does not run successfully, despite there being a contradiction.
    # we get t6 = t1*t3*t5, t10=t3*t5, t1>0, t10>0, t6<0.
    # but because the signs of t1 and t3 are unknown, the mul routine cannot find that contradiction
    # if we add z>0,

def test10():
    a, b = Vars('a, b')
    f, g, h = Func('f'), Func('g'), Func('h')
    B = Blackboard()
    B.assume(f(a, b, c*d)<0, a>0, b>0, a==c, b==d)

    fm = FunctionModule([Forall([x, y], f(x, y, x*y)>0)])
    PolyAdditionModule().update_blackboard(B)
    PolyMultiplicationModule().update_blackboard(B)
    fm.update_blackboard(B)

    run(B)

def test10a():
    a, b = Vars('a, b')
    f, g, h = Func('f'), Func('g'), Func('h')
    S = Solver()
    #B = Blackboard()
    S.assume(f(e, b, c+d)<0, a>0, b>0, a==c, b==d, a==e)

    S.add_axiom(Forall([x, y], f(x, y, x+y)>0))
    S.check()


def test11():
    u, v, w, x, y, z = Vars('u v w x y z')
    # B = Blackboard()
    # B.assume(0 < u, u < v, 1 < x, x < y, 0 < w, w < z)
    # B.assume(u + x * w >= v + y**2 * z)
    # run(B)
    # print
    # print "**********"
    print
    # messages.set_verbosity(messages.debug)
    B = Blackboard()
    B.assume(0 < u, u < v, 1 < x, x < y, 0 < w, w < z)
    B.assume(u + x * w >= v + y**2 * z)
    run(B)

def test12():
    exp = Func('exp')

    B = Blackboard()
    B.assume(0<x, x<y, (1+x**2)/(2+exp(y))>=(2+y**2)/(1+exp(x)))

    fm = FunctionModule([Forall([x, y], And(Implies(x<y, exp(x)<exp(y)),
                                                            exp(x)>0))])

    fm.update_blackboard(B)
    run(B)

    # This example comes from Avigad and Friedman (2006)


def test13():
    x = Var('x')
    B = Blackboard()
    B.assume(x ** 2 + 2 * x + 1 < 0)
    run(B)
    # This test loops!

def test14():
    f = Func('f')
    S = Solver([f(x)<y, y<z, z<f(x)], [Forall([x], f(x)>0)])
    print S.check()

def test15():
    f = Func('f')
    S = Solver([x==y, f(x)!=f(y)])
    S.check()


def test16a():
    ceil = Func('ceil')
    x, a, b, m = Vars('x, a, b, m')
    S = Solver()
    S.add_axiom(Forall([x], ceil(x) >= x))
    S.assume(a < b, x > a, m >= ceil((b - a) / (x - a)))
    S.assume(a + (b - a) / (m + 1) >= x)
    S.check()


def test16():
    ceil = Func('ceil')
    f = Func('f')
    x, a, b, m = Vars('x, a, b, m')
    S = Solver()
    S.add_axiom(Forall([x], ceil(x) >= x))
    S.add_axiom(Forall([m], f(m) < a + (b - a) / (m + 1)))
    S.assume(a < b, x > a, m >= ceil((b - a) / (x - a)))
    S.assume(f(m) >= x)
    S.check()


def test17():
    abs2 = Func('abs')
    f = Func('f')
    x, y, z, i = Vars('x, y, z, i')
    S = Solver()
    S.add_axiom(Forall([x,y], abs2(x + y) <= abs2(x) + abs2(y)))
    S.assume(i >= 0)
    S.assume(abs2(f(y) - f(x)) < 1 / (2 * (i + 1)))
    S.assume(abs2(f(z) - f(y)) < 1 / (2 * (i + 1)))
    S.assume(abs2(f(z) - f(x)) >= 1 / (i + 1))
    S.check()


def arithmetical_tests():
    x, y, u, v, w, z, r = Vars('x, y, u, v, w, z, r')
    a, b, c, d, e = Vars('a, b, c, d, e')

    messages.set_verbosity(messages.quiet)

    problems = [
        [x+1/y < 2, y < 0, y/x > 1, -2 <= x, x <= 2, -2 <= y, y <= 2, x**2/y > (1-x)],

        [0 < x, x < y, 0 < u, u < v, 0 < w+z, w+z < r-1,
          u + (1+x)**2 * (2*w + 2*z + 3) >= 2*v + (1+y)**2 * (2*r + 1)],

        [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x, u*(3*y)**2+1 >= x**2*v + x],

        [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x, u*(3*y)**2+1 < x**2*v + x],

        [1 < x, 1 < y, 1 < z, 1 >= x*(1+z*y)],

        [a > 0, a < 1, b > 0, b < 1, a+b < a*b],

        #Crashes v.4.2c
        #[x+y >= 2, z+w >= 2, u*x**2 < u*x, u*y**2 < u*y, u*w**2 > u*w, u*z**2 > u*z],

        [a <= b*x/2, 0 < c, 0 < d, d < 1, (1+d/(3*(c+3)))*a >= b*x],

        [x < 1, 1 < y, x*y > 1, u+x >= y+1, x**2*y < 2-u*x*y],

       # [x < 1, 1 < y, x*y > 1, u+x >= y+1, x**2*y >= 2-u*x*y],

        [x*(y+z) <= 0, y+z > 0, x >= 0, x*w > 0],

        [a**21 > 0, a**3 < 1, b**55 > 0, b < 1, a+b < a*b],

        [0 < x, x < 1, 0 < y, y < 1, x**150*y**150 > x**150+y**150]
    ]
    expected = [True, True, True, False, True, True,
                #True,
                False, True,
                #False,
                True, True, True ]

    for i in range(len(problems)):
        val = solve(*problems[i])  # solve_poly to use polyhedrons
        if val == expected[i]:
            print 'Test {} correct.'.format(i+1)
        else:
            print 'Test {} incorrect.'.format(i+1)

#messages.set_verbosity(messages.debug)

# polya_set_solver_type('fm')

# test4()
# test5()
# test6()
# test7()
# test8()
# test9()
test10a()
# test12()
# # test13()
# test14()
# test16()
# test17()
# arithmetical_tests()

#messages.set_verbosity(messages.debug)

# print '\n*****\n'
#print solve_poly(x*(y+z) <= 0, y+z > 0, x >= 0, x*w > 0)


print 'Ran in', round(timeit.default_timer()-t, 3), 'seconds'

timer.announce_times()
