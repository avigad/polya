import run_code, timeit, z3#, timecount

# This class runs through a number of examples to see if the given method gets the right answer.
# It will run the procedure in test_code.run_heuristic_on_heuristic_data, without splitting cases.
# Make sure no examples are set to run in test_code.

def run_example(ineqs):
    args = []
    try:
        for ineq in ineqs:
            args.extend(run_code.make_zero_comp("".join(ineq.split())))
    except KeyError as inst:
        print "Invalid input: ", inst
        return
    
    return run_code.run_heuristic_on_hypotheses(args,split_cases = False,verbose=False)



        # This example is similar to one from S. McLaughlin and J. Harrison (2005),
        # which their algorithm solves in 23.5 seconds
         #"1<x", "1<y", "1<z", "1>=x*(1+z*y)"
        
        # This is not provable by Isabelle, from a post to the Isabelle mailing list.
        # "a>0", "a<1", "b>0", "b<1", "a+b<a*b"
    
        # This example takes a while and fails. No large constants. It does not have a model.
        # Weird behavior: nothing learns anything at all?
        # "x+y>=2", "z+w>=2", "u*x^2<u*x", "u*y^2<u*y", "u*w^2>u*w", "u*z^2>u*z"
        
        # This example takes a few seconds, fails. There is a model.
         #"n<=(1/2)*k*x", "0<c", "0<p<1", "(1+p/(3*(c+3)))*n>=k*x"
        
        # If the last inequality is >=, this one has a model. Blowup in FM
        # if the last inequality is changed to <, it does not have a model. FM finds contr. WEIRD BEHAVIOR IN POLY ON THIS ONE
        # "x<1<y", "x*y>1", "u+x>=y+1", "x^2*y<2-u*x*y"
        
        # This example has a model if the last inequality is <. FM blows up here, poly doesn't
        # It does not have a model if the last inequality is >=. Contradiction is found.
        # "0<x<3*y", "u<v<0", "1<v^2<x", "u*(3*y)^2+1 >= x^2*v+x" 
        
        # This is a simple example with extraneous info,
        # where the contradiction is found very quickly.
         #"x*(y+z)<=0", "y+z>0", "x>=0", "x*w>0"
        
        # This example performs splitting, fails
        # "x+y+z<=0", "x+y>=-z"
        
        # This set of constraints has a model: x = 0, found by the procedure
        # "x>=0", "x^3<=0"
        
        # warning: the next example blows up!
        #When using the polyhedron version, it blows up in the mult routine, which is a good sign
        # "x^(1/2)+y^(1/2) < 30", "x^(7/2)-1<y", "y^(1/5)>4"
        
        # The contradiction here is found relatively quickly.
        # "x+1/y<2", "y<0", "y/x>1", "-2<=x<=2", "-2<=y<=2", "x^2*y^(-1)>1-x"
        
        # This example case splits and fails.
        # "((x+y)^2)^(1/2)>(x^2)^(1/2)+(y^2)^(1/2)"
        
        # warning: the next example blows up!
        # "(a+b)*(1/2)<(a*b)^(1/2)"

def run_all_tests():
    start = timeit.default_timer()
    tests = [
             ["1<x", "1<y", "1<z", "1>=x*(1+z*y)"],
             ["a>0", "a<1", "b>0", "b<1", "a+b<a*b"],
             ["x+y>=2", "z+w>=2", "u*x^2<u*x", "u*y^2<u*y", "u*w^2>u*w", "u*z^2>u*z"],
             ["n<=(1/2)*k*x", "0<c", "0<p<1", "(1+p/(3*(c+3)))*n>=k*x"],
             ["x<1<y", "x*y>1", "u+x>=y+1", "x^2*y>=2-u*x*y"],
             ["x<1<y", "x*y>1", "u+x>=y+1", "x^2*y<2-u*x*y"],
             ["0<x<3*y", "u<v<0", "1<v^2<x", "u*(3*y)^2+1 >= x^2*v+x"],
             ["0<x<3*y", "u<v<0", "1<v^2<x", "u*(3*y)^2+1 < x^2*v+x" ],
             ["x*(y+z)<=0", "y+z>0", "x>=0", "x*w>0"],
             ["x+1/y<2", "y<0", "y/x>1", "-2<=x<=2", "-2<=y<=2", "x^2*y^(-1)>1-x"],
             ["x^(1/2)+y^(1/2) < 30", "x^(7/2)-1<y", "y^(1/5)>4"],
             ["a^21>0","a^3<1","b^55>0","b<1","a+b<a*b"],
             ["0<x<1","0<y<1","x^150*y^150>x^150+y^150"] #Z3 cannot do this example, but we can!
             
             ]
    expected = [True,True,True,False,False,True,True,False,True,True,False,True,True]
    for i in range(len(tests)):
        print (i+1),': running on',tests[i]
        if run_example(tests[i])!=expected[i]:
            print 'WRONG RESULT'
        else:
            print 'CORRECT RESULT'
            
    time = timeit.default_timer()-start
    print round(time,3)
    print
    print 'z3 results:'
    start = timeit.default_timer()
    
    v,x,y,z,a,b,w,u,n,k,c,p = z3.Reals('v x y z a b w u n k c p')
    z3tests = [
             [1<x,1<y,1<z,1>=x*(1+z*y)],
             [a>0,a<1,b>0,b<1,a+b<a*b],
             [x+y>=2,z+w>=2,u*(x**2)<u*x,u*(y**2)<u*y,u*(w**2)>u*w,u*(z**2)>u*z],
             [n<=.5*k*x,0<c,0<p<1,(1+p/(3*(c+3)))*n>=k*x],
             [x<1,1<y,x*y>1,u+x>=y+1,(x**2)*y>=2-u*x*y],
             [x<1,1<y,x*y>1,u+x>=y+1,(x**2)*y<2-u*x*y],
             [0<x,x<(3*y),u<v,v<0,1<(v**2),(v**2)<x,(u*((3*y)**2)+1)>=((x**2)*v+x)],
             [0<x,x<3*y,u<v,v<0,1<(v**2),(v**2)<x,u*((3*y)**2)+1<(x**2)*v+x],
             [x*(y+z)<=0,y+z>0,x>=0,x*w>0],
             [x+1/y<2,y<0,y/x>1,-2<=x<=2,-2<=y<=2,(x**2)*(y**(-1))>1-x],
             [(x**.5)+(y**.5)<30,(x**3.5)-1<y,(y**.2)>4],
             [a**21>0,a**2<1,b**55>0,b<1,a+b<a*b],
 #            [0<x,0<y,x<1,y<1,(x**150)*(y**150)>(x**150)+(y**150)]
             ]
    for i in range(len(z3tests)):
        print (i+1),': running z3 on',z3tests[i]
    time = timeit.default_timer()-start
    print round(time,3)

run_all_tests()
#timecount.write()

#print run_code.timecount.time
#for i in range(10):            
#    run_all_tests()
#print round(run_code.timecount.time/run_code.timecount.runs,3)