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


from __future__ import division
from polya.main import terms
from polya.main import blackboard
from polya.polyhedron import poly_add_module
from polya.polyhedron import poly_mult_module
from polya.main import messages
import timeit
#import fractions
import z3

x, y, u, v, w, z, r = terms.Vars('x, y, u, v, w, z, r')
a, b, c, d, e = terms.Vars('a, b, c, d, e')
n, k, p = terms.Vars('n, k, p')

def run(B):
    pa, pm = poly_add_module.PolyAdditionModule(), poly_mult_module.PolyMultiplicationModule()
    try:
        s, s2 = '', '1'
        while s != s2:
            s = s2
            #B.info_dump()
            pa.update_blackboard(B)
            #B.info_dump()
            pm.update_blackboard(B)
            s2 = str(B.get_equalities()) + str(B.get_disequalities()) + str(B.get_inequalities())
        #print 'No contradiction found.'
        #print
        return False
    except terms.Contradiction as e:
        #print e.msg
        #print
        return True

def solve(*assertions):
    #print 'Beginning heuristic.\n'
    B = blackboard.Blackboard()
    B.assert_comparisons(*assertions)
    return run(B)

def test1():
    B = blackboard.Blackboard()
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


    run(B)

def test2():
    messages.set_verbosity(messages.normal)
    B = blackboard.Blackboard()

    B.assert_comparison(0 < x)
    B.assert_comparison(x < y)
    B.assert_comparison(0 < u)
    B.assert_comparison(u < v)
    B.assert_comparison(0 < w + z)
    B.assert_comparison(w + z < r - 1)
    B.assert_comparison(u + (1+x)**2 * (2*w + 2*z + 3) >= 2*v + (1+y)**2 * (2*r + 1))
    #     print("  0 < x < y")
    # print("  0 < u < v")
    # print("  0 < w + z < r - 1")
    #"  u + (1 + x)^2 (2 w + 2 z + 3) < 2 v + (1 + y)^2 (2 r + 1)"
    # x y u v w z r
    # a b c d e f g
    run(B)

t = timeit.default_timer()

def test3():
    messages.set_verbosity(messages.normal)
    B = blackboard.Blackboard()

    # "x+1/y<2", "y<0", "y/x>1", "-2<=x<=2", "-2<=y<=2", "x^2*y^(-1)>1-x"
    B.assert_comparisons(x+1/y<2, y<0, y/x>1, -2<=x, x<=2, -2<=y, y<=2, x**2*y**(-1)>1-x)
    run(B)

def tests():
    messages.set_verbosity(messages.quiet)

    problems = [
        [x+1/y<2, y<0, y/x>1, -2<=x, x<=2, -2<=y, y<=2, x**2*y**(-1)>1-x],

        [0<x, x<y, 0<u, u<v, 0<w+z, w+z < r-1,
          u + (1+x)**2 * (2*w + 2*z + 3) >= 2*v + (1+y)**2 * (2*r + 1)],

        [0<x, x<3*y, u<v, v<0, 1<v**2, v**2<x, u*(3*y)**2+1 >= x**2*v + x],

        [0<x, x<3*y, u<v, v<0, 1<v**2, v**2<x, u*(3*y)**2+1 < x**2*v + x],

        [1<x, 1<y, 1<z, 1>=x*(1+z*y)],

        [a>0, a<1, b>0, b<1, a+b<a*b],

        [x+y>=2, z+w>=2, u*x**2<u*x, u*y**2<u*y, u*w**2>u*w, u*z**2>u*z],

        [a<=b*x/2, 0<c, 0<d, d<1, (1+d/(3*(c+3)))*a>=b*x],

        [x<1, 1<y, x*y>1, u+x>=y+1, x**2*y<2-u*x*y],

        [x<1, 1<y, x*y>1, u+x>=y+1, x**2*y>=2-u*x*y],

        [x*(y+z)<=0, y+z>0, x>=0, x*w>0],

        [a**21>0, a**3<1, b**55>0, b<1, a+b<a*b],

        [0<x, x<1, 0<y, y<1, x**150*y**150>x**150+y**150]
    ]
    expected = [True, True, True, False, True, True, True, False, True, False, True, True, True]

    for i in range(len(problems)):
        val = solve(*problems[i])
        if val == expected[i]:
            print 'Test {} correct.'.format(i+1)
        else:
            print 'Test {} incorrect.'.format(i+1)

def z3test():
    print 'new version:'
    t0, t1, t2, t3, t4, t5, t6, t7, t8, t9 = z3.Reals('t0 t1 t2 t3 t4 t5 t6 t7 t8 t9')
    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11 = \
        z3.Reals('a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11')
    bools = [z3.Bool('b'+str(i)) for i in range(100)]
    s = z3.Solver()
    #s.add(t4==t0+t2, t6==t5+t1, t8==t0-.5*t7)
    eqs = [t3==t1*t2, t7==t5*t1*t2, t9==t2*t1**2]
    ineqs = [
        t0 > 0,
        t1 > 0,
        t2 > 0,
        t3 > 0,
        t4 > 0,
        t5 > 0,
        t6 > 0,
        t7 > 0,
        t8 > 0,
        t9 > 0,
        t0 > t1,
        t0 < t2,
        t0 < t3,
        t0 < (1/2)*t4,
        t0 < t5,
        t0 < (1/2)*t6,
        t1 < t2,
        t1 < t3,
        t1 < (1/2)*t4,
        t1 < t5,
        t1 > -1*t5,
        t1 < (1/2)*t6,
        t2 < t4,
        t2 > (1/2)*t4,
        t2 < t5,
        t2 < t6,
        t4 < 2*t5,
        t4 <= t6,
        t5 > (1/2)*t6,
        t7 > -2*t8,
        t8 > (1/2)*t9,

        t1 >= t9
    ]

    i = 0
    for e in eqs:
        s.add(z3.Implies(bools[i], e))
        i+=1

    for e in ineqs:
        s.add(z3.Implies(bools[i], e))
        i+=1

    for b in bools:
        s.add(b)

    print s
    print s.check()
    print s.model()
    print
    print


    i = 0

    print 'old version:'
    s = z3.Solver()
    eqs = [a2 == (a0 + -1*a1),a4 == (a0 + -1*a3),a6 == (a0 + -1*a5),a8 == (a0 + -1*a7 + -1*a1 + a3),
           a11 == (a0 + -1/2*a9 + -1/2*a10)]
    for e in eqs:
        s.add(z3.Implies(bools[i], e))
        i+=1

    ineqs = [
        a0 > 0,
        a1 > 0,
        a2 > 0,
        a3 > 0,
        a4 < 0,
        a5 > 0,
        a6 < 0,
        a7 > 0,
        a8 <= 0,
        a9 > 0,
        a10 > 0,
        a11 > 0,

        a5 < 1 * a9,
        a4 > -1 * a7,
        a1 < 1 * a3,
        a5 > -1 * a6,
        a6 > -1 * a9,
        a0 < 1 * a7,
        a3 < 1 * a7,
        a0 < 1 * a3,
        a1 > -1 * a2,
        a4 > -1 * a9,
        a2 < 1 * a9,
        a3 > 1 * a10,
        a1 < 1 * a5,
        a3 > -1 * a6,
        a1 < 1 * a10,
        a7 < 1 * a9,
        a2 < 1 * a7,
        a7 > 1 * a10,
        a3 < 1 * a9,
        a0 < 1 * a5,
        a6 > -1 * a7,
        a3 > 1 * a5,
        a0 > 1 * a1,
        a5 > 1 * a10,
        a3 > -1 * a4,
        a5 < 1 * a7,
        a1 > -1 * a7,
        a1 < 1 * a7,
        a0 < 1 * a9,
        a7 > -1 * a8
    ]

    for e in ineqs:
        s.add(z3.Implies(bools[i], e))
        i+=1

    print s.check(*[b for b in bools])
    #print s.model()
    print s.unsat_core()
    print s
    #print s.model()

tests()
#messages.set_verbosity(messages.debug)
#print solve(x<1, 1<y, x*y>1, u+x>=y+1, x**2*y<2-u*x*y)
#print solve(x*(y+z)<=0, y+z>0, x>=0, x*w>0)
#z3test()

print 'Ran in', round(timeit.default_timer()-t, 3), 'seconds'