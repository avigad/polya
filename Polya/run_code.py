from __future__ import division  # This makes Python interpret / as float division.
from classes import *
from heuristic import *
#from addition_module import *
#from multiplication_module import *
#from function_module import *
import poly_add_module as add #change this to polyhedron_module_cdd, polyhedron_module_lrs or polyhedron_module (which doesn't handle > vs >=)
import poly_mult_module as mul
#from random import randint
#from math import floor, ceil
import timeit
#import comparisons
start = timeit.default_timer()

#Ignore this, benchmarking code
class timecount:
    time = 0
    runs = 0
            
# Runs the heuristic procedure on an initialized Heuristic_data object.
# If split_cases is true, will look at all unsigned variables and split on them being > or < 0.    
def run_heuristic_on_heuristic_data(H, split_cases):
    while H.changed:
        try:
            H.changed = False
            #H.info_dump()
            #t = timeit.default_timer()
            add.learn_add_comparisons_poly(H)
            #timecount.time += timeit.default_timer()-t
            #timecount.runs+=1
            mul.learn_mul_comparisons_poly(H)
            #learn_func_comparisons(H)
            #comparisons.compare_matrix_methods(H.num_terms,H.term_comparisons,H.zero_comparisons,[H.name_defs[i]-IVar(i) for i in range(H.num_terms) if isinstance(H.name_defs[i],Add_term)])
        except Contradiction:
            print "Contradiction found!"
            return True
        except KeyboardInterrupt:
            print "Stopped."
            quit()
            
    if split_cases:
        if H.verbose:
            print 'We\'ve run out of new information. Let\'s try splitting cases.'
        unsigned_vars = [t for t in range(H.num_terms) if H.weak_sign(t) == 0]
        if unsigned_vars:
            if H.verbose:
                print 'We don\'t know sign information for:'
                for t in unsigned_vars:
                    print ' ', IVar(t), '=', H.terms[t]
                
        else:
            if H.verbose:
                print 'Signs of all variables are known; nothing to split on.'
                
        for v in unsigned_vars:
            if H.verbose:
                print 'Assuming', IVar(v), '>= 0. That is,', H.terms[v], '>= 0.'
            Hposv = H.duplicate()
            contr = False
            try:
                Hposv.learn_zero_comparison(v, GE, HYP)
            except Contradiction:
                contr = True
            if contr or run_heuristic_on_heuristic_data(Hposv, False):  # v>=0 is a contradiction. learn v<0
                if H.verbose:
                    print 'From the case split, we learned', H.terms[v], '< 0'
                H.learn_zero_comparison(v, LT, HYP)
                return run_heuristic_on_heuristic_data(H, True)
            
            # otherwise, no contradiction from v>=0. try v<=0
            if H.verbose:
                print 'Assuming', H.terms[v], '<= 0'
            Hnegv = H.duplicate()
            contr = False
            try:
                Hnegv.learn_zero_comparison(v, LE, HYP)
            except Contradiction:
                contr = True
            if contr or run_heuristic_on_heuristic_data(Hnegv, False):  # v<=0 is a contradiction. learn v>0
                if H.verbose:
                    print 'From the case split, we learned', H.terms[v], '> 0'
                H.learn_zero_comparison(v, GT, HYP)
                return run_heuristic_on_heuristic_data(H, True)
            
            # otherwise, v could be pos or neg. try splitting on the next case.
    
    return False

# Takes a list of (uncanonized) Zero_comparisons and runs the heuristic.
# If split_cases is true, it will try assuming variables of unknown sign are pos or neg
# if it doesn't find a contradiction before.
# Will not chain case splits.
def run_heuristic_on_hypotheses(hyps, func_data=[], split_cases=True,verbose=True):
    hypotheses = [canonize_zero_comparison(h) for h in hyps]
    # print "Canonized hypotheses:"
    # for h in hypotheses:
    #     print h
    # print

    try:
        H = Heuristic_data(hypotheses, func_data, verbose)
    except Contradiction:
        print "Contradiction found!"
        return True
    H.changed = True
    
    if run_heuristic_on_heuristic_data(H, split_cases):
        return True
        
    print "Nothing more learned. No contradiction has been found."
    return False

###############################################################################
#
# HARD-CODED TESTS
#
###############################################################################
         
def test_heuristic():

    print
    print("From these hypotheses:")
    print
    print("  0 < x < y")
    print("  0 < u < v")
    print("  0 < w + z < r - 1") 
    print
    print("It follows that:")
    print
    print("  u + (1 + x)^2 (2 w + 2 z + 3) < 2 v + (1 + y)^2 (2 r + 1)")
    print
    print("This test proves this by showing that the hypotheses together")
    print("with the negation of the conclusion are inconsistent")
    print

    r = Var("r")
    u = Var("u")
    v = Var("v")
    w = Var("w")
    x = Var("x")
    y = Var("y")
    z = Var("z")

    # hypotheses
    gt_zero_hyps = [
        x,
        Add_term([(1, y), (-1, x)]),
        u,
        Add_term([(1, v), (-1, u)]),
        Add_term([(1, w), (1, z)]),
        Add_term([(1, r), (-1, one), (-1, w), (-1, z)])]
    ge_zero_hyps = [
        Add_term([(1, u),
                  (1, Mul_term([(Add_term([(1, one), (1, x)]), 2),
                                (Add_term([(2, w), (2, z), (3, one)]), 1)])),
                  (-2, v),
                  (-1, Mul_term([(Add_term([(1, one), (1, y)]), 2),
                                (Add_term([(2, r), (1, one)]), 1)]))])]

    hypotheses = ([Zero_comparison(t, GT) for t in gt_zero_hyps] + 
                  [Zero_comparison(t, GE) for t in ge_zero_hyps])

    run_heuristic_on_hypotheses(hypotheses,split_cases=False)


def test_heuristic_2():

    print
    print("From these hypotheses:")
    print
    print("  (x^2-8)/(x^2+3x-1) < 0")
    print("  0 < x < 1")
    print
    print("There should be no contradiction. Both are true at x=.5")
    print
    print

    x = Var("x")

    # hypotheses
    # x^2-8
    a = Add_term([Add_pair(1, Mul_term([Mul_pair(x, 2)])), Add_pair(-8, one)])
    
    # x^2+3x-1
    b = Add_term([Add_pair(1, Mul_term([Mul_pair(x, 2)])), Add_pair(3, x), Add_pair(-1, one)])
    
    lt_zero_hyps = [
       Mul_term([Mul_pair(a, 1), Mul_pair(b, -1)])
       ]
    gt_zero_hyps = [
        x,
        Add_term([Add_pair(1, one), Add_pair(-1, x)])
        ]


    hypotheses = ([Zero_comparison(t, LT) for t in lt_zero_hyps]
                   + [Zero_comparison(t, GT) for t in gt_zero_hyps])

    run_heuristic_on_hypotheses(hypotheses, split_cases=False)
        
def test_heuristic_3():

    print
    print("From these hypotheses:")
    print
    print("  -x^2 > -10")
    print("  x > 5")
    print
    print("There should be a contradiction.")
    print
    print

    x = Var("x")

    # hypotheses
    # -x^2>-10
    a = Add_term([Add_pair(-1, Mul_term([Mul_pair(x, 2)])), Add_pair(10, one)])
    
    # x>5
    b = Add_term([Add_pair(1, x), Add_pair(-5, one)])
    lt_zero_hyps = [
       
       ]
    gt_zero_hyps = [
        a, b
        ]


    hypotheses = ([Zero_comparison(t, LT) for t in lt_zero_hyps]
                   + [Zero_comparison(t, GT) for t in gt_zero_hyps])

    run_heuristic_on_hypotheses(hypotheses)
    
def test_heuristic_4():

    print
    print("From these hypotheses:")
    print
    print("  x < 0")
    print("  x - y < 0")
    print("  x + y >= 5")
    print
    print("There should be no contradiction. All are true at x=-1, y=10.")
    print
    print

    x = Var("x")
    y = Var("y")

    
    lt_zero_hyps = [
       x, Add_term([Add_pair(1, x), Add_pair(-1, y)])
       ]

    hypotheses = ([Zero_comparison(t, LT) for t in lt_zero_hyps]
                   + [Zero_comparison(Add_term([Add_pair(1, x), Add_pair(1, y), Add_pair(-5, one)]), GE)])

    run_heuristic_on_hypotheses(hypotheses)
    
def test_heuristic_on_functions():
    # we know x < y => exp(x) < exp(y)
    # Assume x < y, exp(x) > exp(y).
    
    x = Var("x")
    y = Var("y")
    hypotheses = [Zero_comparison(Add_term([Add_pair(1, x), Add_pair(-1, y)]), LT), Zero_comparison(Add_term([Add_pair(1, Func_term('exp', [y])), Add_pair(-1, Func_term('exp', [x]))]), LT)]
    co = Function_conclusion((lambda H, a, b:Func_term("exp", [a])), (lambda H, a, b:Func_term("exp", [b])), GT)
    fr = Function_restriction('exp', lambda H, a, b:a.gt_rel(b, H), co)
    

    co2 = Function_conclusion(lambda H, a:Func_term("exp", [a]), lambda H, a:0, GT)
    fr2 = Function_restriction('exp2', lambda H, a:True, co2)
    # fr2 = Function_restriction('exp',free_vars2,[h2],co2)
    
    run_heuristic_on_hypotheses(hypotheses, [fr2])

def test_heuristic_on_functions2():
    # we know x < y => exp(x) < exp(y)
    # Assume x < y, exp(x) > exp(y).
    
    x = Var("x")
    y = Var("y")
    hypotheses = [Zero_comparison(Add_term([Add_pair(1, x), Add_pair(-1, y)]), LT), Zero_comparison(Add_term([Add_pair(1, Func_term('exp', [y])), Add_pair(-1, Func_term('exp', [x]))]), LE),
                  Zero_comparison(Add_term([Add_pair(1, Func_term('exp', [y])), Add_pair(-1, Func_term('exp', [x]))]), GE)]
    co = Function_conclusion((lambda H, a, b:Func_term("exp", [a])), (lambda H, a, b:Func_term("exp", [b])), GT)
    fr = Function_restriction('exp', lambda H, a, b:a.neq_rel(b, H), co)
    

    co2 = Function_conclusion(lambda H, a:Func_term("exp", [a]), lambda H, a:0, GT)
    fr2 = Function_restriction('exp2', lambda H, a:True, co2)
    # fr2 = Function_restriction('exp',free_vars2,[h2],co2)
    
    run_heuristic_on_hypotheses(hypotheses, [fr])

###################################################
#
#  INPUT CODE
#
####################################################

digit = '1234567890'
alpha = 'abcdefghijklmnopqrstuvwxyz_'
alphanum = alpha + digit
comp = '><='
punct = '()'
operators = '+-/*^'

# Helper function for lex.
# Takes a "property" string and an input string.
# Returns: the initial substring of input whose chars are in prop, the remainder of input
def splitoff(prop, inp):
    index = 0
    while index < len(inp) and inp[index] in prop: index += 1
    # if prop==punct and index>1: raise Exception
    return inp[:index], inp[index:]

# takes string with no whitespace
# returns list of strings where each string is a token of type digit,alpha,comp,punct,operators
# TODO: handle whitespace, multi-character names
def lex(inp):
    if len(inp) == 0: return []
    if len(inp) == 1: return [inp]
    
    
    type = ""
    # print inp[0]
    if inp[0] in alphanum: type = alphanum
    elif inp[0] in operators: type = operators
    elif inp[0] in comp: type = comp
    elif inp[0] in punct: type = punct
    if type == "": raise Exception("Bad input!")
    
    token, remainder = splitoff(type, inp)
    return [token] + lex(remainder)

# kinds of inequalities
# GT, GE, LE, LT = range(4)
# comp_str = { GT : '>', GE : '>=', LT : '<', LE : '<=' }

comp_str_rev = {'>': GT, '>=': GE, '<': LT, '<=': LE}


# dir is an int: GT, GE, LE, LT
# Temporary data structure for parsing.
# left and right are strings representing terms.
# ineq is the comparison between those terms: left ineq right
class StringCompData:
    def __init__(self, string1, string2, dir):
        self.left = string1
        self.right = string2
        self.ineq = dir
        
    def __str__(self):
        return self.left + comp_str[self.ineq] + self.right
        
    def __repr__(self):
        return self.__str__()


# inputs string
# returns list of one or two StringCompDatas
def splitup(s):
    # s should have one or two inequality signs of the same direction.
    t = "".join(s.split())
    if find(t, ">") > -1 and find(t, "<") > -1:
        raise Exception
    ineqs = count(t, ">") + count(t, "<")
    if ineqs < 1 or ineqs > 2: raise Exception
    
    if ineqs == 2:  # This is a chain of inequalities. Split and parse each one separately.
        dir = ">" if (find(t, ">") > -1) else "<"
        dirs = []
        i1 = find(t, dir)
        dirs.append(dir + "=" if t[i1 + 1] == "=" else dir)
        i2 = i1 + 1 + find(t[i1 + 1:], dir)
        dirs.append(dir + "=" if t[i2 + 1] == "=" else dir)
        
        substr1 = t[:i1]
        substr2 = t[i1 + len(dirs[0]):i2]
        substr3 = t[i2 + len(dirs[1]):]
        
        str1 = substr1 + dirs[0] + substr2
        str2 = substr2 + dirs[1] + substr3
        
        return splitup(str1) + splitup(str2)
        
    else:  # Only one inequality.
        iseq = "=" if (find(t, "=") > -1) else ""
        dir = ">" if (find(t, ">") > -1) else "<"
        substrs = split(t, dir + iseq)
        return [StringCompData(substrs[0], substrs[1], comp_str_rev[dir + iseq])]
        
        
# takes a string like "x^5+2*y".
# Returns "Var('x')**5+2*Var('y')"
def fixvars(input):

    lexed = lex(input)
    for i in range(0, len(lexed)):
        token = lexed[i]
        isvar = False
        for c in token:
            if c in alpha:
                isvar = True
                break
        if isvar:
            lexed[i] = "Var('" + lexed[i] + "')"
        elif lexed[i] == '^':
            lexed[i] = '**'
    output = ""
    for token in lexed: output += token
    return output
        

# takes string as input. Returns array of ZeroComparisons
# TODO: should be 2 functions
def make_zero_comp(input):
    string_comp_data = splitup(fixvars(input))
    zero_comps = []
    for scd in string_comp_data:
        if not ("Var" in scd.left + scd.right):
            if not eval(scd.left + comp_str[scd.ineq] + scd.right):
                print "Contradiction found while parsing!", scd.left, comp_str[scd.ineq], scd.right
                exit()
            continue
        terml = eval(scd.left)
        termr = eval(scd.right)
        term = terml + (-1) * termr
        zero_comps.append(Zero_comparison(term, scd.ineq))
    return zero_comps


def run_heuristic_on_input():
    print "Enter inequalities to run."
    print "Type \"done\" or a blank line when finished."
    args = []
    v = "".join(raw_input("inequality: ").split())  # clear whitespace
    while (v != "" and v != "done"):
        try:
            args.extend(make_zero_comp(v))  # args.append(parse(v))
        except KeyError as inst:
            print "Invalid input: ", inst
        v = "".join(raw_input("inequality: ").split())
    
    print args    
    run_heuristic_on_hypotheses(args)
    
# Uncomment one and only one line of inequalities.    
def run_heuristic_on_list():
    ineqs = [
        # This example is similar to one from S. McLaughlin and J. Harrison (2005),
        # which their algorithm solves in 23.5 seconds
         #"1<x", "1<y", "1<z", "1>=x*(1+z*y)"
        
        # This is not provable by Isabelle, from a post to the Isabelle mailing list.
        # "a>0", "a<1", "b>0", "b<1", "a+b<a*b"
    
        # This example takes a while and fails. No large constants. It does not have a model.
        # The contradiction is NOT found, by FM or either polyhedron method
         #"x+y>=2", "z+w>=2", "u*x^2<u*x", "u*y^2<u*y", "u*w^2>u*w", "u*z^2>u*z"
        
        # This example takes a few seconds, fails. There is a model.
         "n<=(1/2)*k*x", "0<c", "0<p<1", "(1+p/(3*(c+3)))*n>=k*x"
        
        # If the last inequality is >=, this one has a model. Blowup in FM
        # if the last inequality is changed to <, it does not have a model. Contradiction is found.
        #"x<1<y", "x*y>1", "u+x>=y+1", "x^2*y<2-u*x*y"
        
        # This example has a model if the last inequality is <. FM blows up here, poly doesn't
        # It does not have a model if the last inequality is >=. Contradiction is found.
        # "0<x<3*y", "u<v<0", "1<v^2<x", "u*(3*y)^2+1 < x^2*v+x" 
        
        # This is a simple example with extraneous info,
        # where the contradiction is found very quickly.
        # "x*(y+z)<=0", "y+z>0", "x>=0", "x*w>0"
        
        # This example performs splitting, fails
        # "x+y+z<=0", "x+y>=-z"
        
        # This set of constraints has a model: x = 0, found by the procedure
        # "x>=0", "x^3<=0"
        
        # warning: the next example blows up!
        #When using the polyhedron add, it blows up in the mult routine, which is a good sign
        #When using polyhedron add and mul, it does not blow up.
        #There is a model.
        #"x^(1/2)+y^(1/2) < 30", "x^(7/2)-1<y", "y^(1/5)>4"
        
        # The contradiction here is found relatively quickly.
        # "x+1/y<2", "y<0", "y/x>1", "-2<=x<=2", "-2<=y<=2", "x^2*y^(-1)>1-x"
        
        # This example case splits and fails.
        # "((x+y)^2)^(1/2)>(x^2)^(1/2)+(y^2)^(1/2)"
        
        # warning: the next example blows up!
        # "(a+b)*(1/2)<(a*b)^(1/2)"
        
        #"x<y","x>-y","y<5"
        #"0<x<a+b","a<5","b<3"
        #"x>=0","y>=0"#,"2*(x+y)<10"
      ]
    args = []
    try:
        for ineq in ineqs:
            args.extend(make_zero_comp("".join(ineq.split())))
    except KeyError as inst:
        print "Invalid input: ", inst
        return
    
    return run_heuristic_on_hypotheses(args,split_cases = False)

#run_heuristic_on_input()
#run_heuristic_on_list()
#test_heuristic()
#test_heuristic_2()
#test_heuristic_3()
#test_heuristic_4()
#test_heuristic_on_functions()
#test_heuristic_on_functions2()

def multirun():
    for k in range(10):
        run_heuristic_on_list()
        #test_heuristic()
        #test_heuristic_2()
        #test_heuristic_3()
        #test_heuristic_4()
    print 'average time finding vertices:',round(timecount_p.time/timecount_p.runs,4)

#multirun()

#stop = timeit.default_timer()
#print round(stop - start, 3)
#print round(timecount.time/timecount.runs,3)