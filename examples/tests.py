####################################################################################################
#
# tests.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# Contains tests for Polya.
#
# TODO:
#
####################################################################################################

from polya import *
import timeit

t = timeit.default_timer()

x, y, u, v, w, z, r = Vars('x, y, u, v, w, z, r')
a, b, c, d, e = Vars('a, b, c, d, e')
n, k, p = Vars('n, k, p')


def test1():
    B = Blackboard()
    B.assert_comparison(0 < x)
    B.assert_comparison(x < 3*y)
    B.assert_comparison(u < v)
    B.assert_comparison(v < 0)
    B.assert_comparison(1 < v**2)
    B.assert_comparison(v**2 < x)
    B.assert_comparison(u*(3*y)**2 + 1 >= x**2 * v + x)
    # This example has a model if the last inequality is <. FM blows up here, poly doesn't
    # It does not have a model if the last inequality is >=. Contradiction is found.
    # "0<x<3*y", "u<v<0", "1<v^2<x", "u*(3*y)^2+1 >= x^2*v+x"
    run(B, poly=True)


def test2():
    messages.set_verbosity(messages.normal)
    B = Blackboard()

    B.assert_comparison(0 < x)
    B.assert_comparison(x < y)
    B.assert_comparison(0 < u)
    B.assert_comparison(u < v)
    B.assert_comparison(0 < w + z)
    B.assert_comparison(w + z < r - 1)
    B.assert_comparison(u + (1+x)**2 * (2*w + 2*z + 3) >= 2*v + (1+y)**2 * (2*r + 1))
    run(B, poly=True)


def test3():
    messages.set_verbosity(messages.normal)
    B = Blackboard()

    # "x+1/y<2", "y<0", "y/x>1", "-2<=x<=2", "-2<=y<=2", "x^2*y^(-1)>1-x"
    B.assert_comparisons(x+1/y<2, y<0, y/x>1, -2<=x, x<=2, -2<=y, y<=2, x**2*y**(-1)>1-x)
    run(B, poly=False)

def test4():
    f = Func('f')
    a, b, c = Vars('a, b, c')

    B = Blackboard()

    fm = function_module.FunctionModule([ForAll([x, y], Implies(x<y, f(x)<f(y)))])

    B.assert_comparison(a<b)
    B.assert_comparison(f(a) > f(b))
    try:
        fm.update_blackboard(B)
    except Contradiction:
        print 'Contradiction found from axiom module'

def test5():

    f = Func('f')
    x, y, z, w, r, s = Vars('x, y, z, w, r, s')

    B = Blackboard()

    fm = function_module.FunctionModule([ForAll([x, y], Implies(x<y, f(x)<f(y)))])

    B.assert_comparisons(0<r, s>1, 0<x, x<y, w>z, z+f(x)>w+f(s*(y+r)))

    try:
        fm.update_blackboard(B)
    except Contradiction:
        print 'Contradiction found from axiom module'

    run(B, poly=True)
    # run(B)

def test6():
    f = Func('f')
    x, y, z, w, r, s = Vars('x, y, z, w, r, s')
    u, v = UVar(1), UVar(2)

    B = Blackboard()

    fm = function_module.FunctionModule(
        [ForAll([x, y], (f(x)+f(y))/2 >= f((x+y)/2))]
    )

    B.assert_comparisons(f(x)+f(y)<z, f((x+y)/2)>4*z, z>0)
    fm.update_blackboard(B)

    run(B, poly=True)
    # run(B)

def test7():
    x, y, z = Vars('x, y, z')
    f = Func('f')
    fm = function_module.FunctionModule(
        [ForAll([x, y], (f(x)+f(y))/2 >= f((x+y)/2))]
    )

    B = Blackboard()
    B.assert_comparisons(z>0, f(x)+f(y)-z<0, f((x+y)/2)-4*z>0)
    fm.update_blackboard(B)

    run(B, poly=True)
    # run(B)


def test8():
    x, y, z = terms.Vars('x, y, z')
    f = terms.Func('f')
    fm = function_module.FunctionModule(
        [formulas.ForAll([x, y], f(x*y)==f(x)*f(y)),
         formulas.ForAll([x], formulas.Implies(x>2, f(x)<0))]
    )

    C = blackboard.Blackboard()
    C.assert_comparisons(x>1, y>2, f(x*y)>0)
    fm.update_blackboard(C)

    run(C)

def test9():
    x, y, z = terms.Vars('x, y, z')
    f = terms.Func('f')
    fm = function_module.FunctionModule(
        [
            formulas.ForAll([x, y], f((x*y)/2)<=(f(x)*f(y))/2)
        ]
    )

    C = blackboard.Blackboard()
    C.assert_comparisons(z>0, z*f(x)*f(y)<0, 4*z*f(x*y/2)>0)
    fm.update_blackboard(C)
    run(C)

    # This example does not run successfully, despite there being a contradiction.
    # we get t6 = t1*t3*t5, t10=t3*t5, t1>0, t10>0, t6<0.
    # but because the signs of t1 and t3 are unknown, the mul routine cannot find that contradiction

def test10():
    a, b = Vars('a, b')
    f, g = Func('f'), Func('g')
    B = Blackboard()
    B.assert_comparisons(b==g(a), f(b)>0)

    fm = function_module.FunctionModule([ForAll([x], f(g(x))<0)])
    fm.update_blackboard(B)

    run(B)


def test11():
    u, v, w, x, y, z = Vars('u v w x y z')
    B = Blackboard()
    B.assert_comparisons(0 < u, u < v, 1 < x, x < y, 0 < w, w < z)
    B.assert_comparison(u + x * w >= v + y**2 * z)
    run(B, False)


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

        [x+y >= 2, z+w >= 2, u*x**2 < u*x, u*y**2 < u*y, u*w**2 > u*w, u*z**2 > u*z],

        [a <= b*x/2, 0 < c, 0 < d, d < 1, (1+d/(3*(c+3)))*a >= b*x],

        [x < 1, 1 < y, x*y > 1, u+x >= y+1, x**2*y < 2-u*x*y],

        [x < 1, 1 < y, x*y > 1, u+x >= y+1, x**2*y >= 2-u*x*y],

        [x*(y+z) <= 0, y+z > 0, x >= 0, x*w > 0],

        [a**21 > 0, a**3 < 1, b**55 > 0, b < 1, a+b < a*b],

        [0 < x, x < 1, 0 < y, y < 1, x**150*y**150 > x**150+y**150]
    ]
    expected = [True, True, True, False, True, True, True, False, True, False, True, True, True]

    for i in range(len(problems)):
        val = solve_poly(*problems[i])
        if val == expected[i]:
            print 'Test {} correct.'.format(i+1)
        else:
            print 'Test {} incorrect.'.format(i+1)

#messages.set_verbosity(messages.debug)
test11()
# test4()
# test5()
# test6()
# test7()
# test8()
# test9()
#arithmetical_tests()
#print solve(x < 1, 1 < y, x*y > 1, u+x >= y+1, x**2*y < 2-u*x*y)
#print solve(x*(y+z) <= 0, y+z > 0, x >= 0, x*w > 0)


print 'Ran in', round(timeit.default_timer()-t, 3), 'seconds'
