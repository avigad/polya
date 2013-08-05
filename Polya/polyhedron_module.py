from classes import *
from heuristic import *
from itertools import combinations
from math import sqrt
import cdd
  
                  
# Try to mine sign data from additive definitions. 
# provenance is HYP, so this info is available to the additive routine  
def learn_additive_sign_info(H):
    for j in (i for i in range(H.num_terms) if (isinstance(H.name_defs[i], Add_term))):
        if H.sign(j) == 0:
            addpairs = H.name_defs[j].addpairs
            sign = addpairs[0].coeff * H.weak_sign(addpairs[0].term.index)
            if sign != 0 and all(addpairs[i].coeff * H.weak_sign(addpairs[i].term.index) == sign for i in range(len(addpairs))):
                if any(H.sign(addpairs[i].term.index) != 0 for i in range(len(addpairs))):
                    H.learn_zero_comparison(j, (GT if sign > 0 else LT), HYP)
                else:
                    H.learn_zero_comparison(j, (GE if sign > 0 else LE), HYP)
        if H.weak_sign(j) != 0 and len(H.name_defs[j].addpairs) == 2:
            pairi, pairk = H.name_defs[j].addpairs[0], H.name_defs[j].addpairs[1]
            i, k = pairi.term.index, pairk.term.index
            ci, ck = pairi.coeff, pairk.coeff
            comp = H.zero_comparisons[j].comp     
            if i > k:
                i, k, pairi, pairk, ci, ck = k, i, pairk, pairi, ck, ci
                
            c = -ck / ci
            if ci < 0:
                comp = comp_reverse(comp)
            H.learn_term_comparison(i, k, comp, c, HYP)
            
# Takes a heuristic H
# Accumulates additive comparisons and creates a polyhedron model of them
# To use the cdd matrix representation, we need to make a matrix of the form
#   (b | -A)
# where b-Ax >= 0.
# Since our situation is homogenous, b = 0.
# So, Ax <= 0
def create_H_format_matrix(H,add_eqs):
    d = H.num_terms
    base_matrix = []
    
    if H.verbose:
        print
        print 'Additive comparisons:'
    
    for (a,b) in H.term_comparisons.keys():
        for c in (p for p in H.term_comparisons[a,b] if p.provenance!=ADD):
        #for c in H.term_comparisons[a,b]:
            i,j = a,b
            comp,coeff_i,coeff_j = c.comp,1,-c.coeff #coeff_i * a_i + coeff_j * c_j comp 0
            if comp in [GE,GT]:
                coeff_i,coeff_j = -coeff_i,-coeff_j
                comp = comp_reverse(comp)
                
                
            row = [0]*(d+1) #row will be one row of the matrix (b | -A), where b = 0
            row[i+1]=-coeff_i
            row[j+1]=-coeff_j
            base_matrix.append(row)
            if H.verbose:
                print IVar(i),'+',str(-c.coeff)+'*'+str(IVar(j)),comp_str[c.comp],'0'
            
    for i in H.zero_comparisons.keys():
        row = [0]*(d+1)
        if H.zero_comparisons[i].comp in [LE,LT]:
            row[i+1] = -1
        else:
            row[i+1] = 1
        base_matrix.append(row)
        if H.verbose:
            print IVar(i),comp_str[H.zero_comparisons[i].comp],'0'
            
    matrix = cdd.Matrix(base_matrix,number_type='fraction')
    matrix.rep_type = cdd.RepType.INEQUALITY
    
    eq_rows = []
    for e in add_eqs:
        row = [0]*(d+1)
        for pair in e.addpairs:
            row[pair.term.index+1] = pair.coeff #don't need to make this negative, since it's = 0
        eq_rows.append(row)
    matrix.extend(eq_rows,linear=True)
    
    return matrix

# Runs the convex hull algorithm to turn a list of vertices in two variables into inequalities
# Vertices is a list of 3tuples: [ (0, c_i, c_j) ]
def get_2d_inequalities(i, j, vertices):
    proj_cdd_matrix = vertices #cdd.Matrix(vertices,number_type = 'fraction')
    proj_cdd_matrix.rep_type = cdd.RepType.GENERATOR
    ineqs = cdd.Polyhedron(proj_cdd_matrix).get_inequalities()
    return ineqs


#Computes the square of the Euclidean distance between two ordered pairs.
def distance_squared(p1,p2):
    return (p2[0]-p1[0])**2+(p2[1]-p1[1])**2

class VertexSetException(Exception):
    def __init__(self,s=''):
        self.message = s 
    pass


#Vertices is a list of 3-tuples (x,y).
#Normalize all (x,y) to the unit circle. By hypothesis, they all fall on the same semicircle.
#Returns the pair of original vertices (0,x1,y1),(0,x2,y2) that are at the extremes:
#The angle between these two vertices is greater than between any other pair.
#IT WOULD BE NICE TO DO THIS WITHOUT SQRT
def get_boundary_vertices(vertices):
    #print 'VERTICES: ',vertices
    if len(vertices)<2:
        raise VertexSetException('fewer than two vertices')
    normalized_vertices = []
    for v in vertices:
        scale = 1.0/sqrt(v[0]**2+v[1]**2)
        normalized_vertices.append((scale*v[0],scale*v[1]))
    max_i,max_j,max_d = 0,1,0
    for (i,j) in combinations(range(len(normalized_vertices)),2):
        d = distance_squared(normalized_vertices[i],normalized_vertices[j])
        if d>max_d:
            max_i,max_j,max_d = i,j,d 
            
            
    #max_i, max_j are the indices of the vertices with the largest separating angle.
    #All the other points should fall on one side or the other of the line between these two vertices.
    #If not, we're in a degenerate situation.
    if normalized_vertices[max_j][0]-normalized_vertices[max_i][0] != 0:
        nvi,nvj = normalized_vertices[max_j],normalized_vertices[max_i]
        m = Fraction(nvj[1]-nvi[1])/Fraction(nvj[0]-nvi[0])
        try:
            p = next(v for v in normalized_vertices if v!=nvi and v!=nvj)
        
        except StopIteration: #There are no other vertices, so all vertices fall in one semicircle
            return vertices[max_i],vertices[max_j]
        
        if p[1]>=nvi[1]+m*(p[0]-nvi[0]):
            dir = GE
        else:
            dir = LE
        
        #Check each vertex to make sure it falls on the same side of the chord as p
        for v in (n for n in normalized_vertices if n!=nvi and n!=nvj):
            if dir == GE:
                if v[1]<nvi[1]+m*(v[0]-nvi[0]):
                    raise VertexSetException('not in a semicircle GE max i,j'+str(i)+' '+str(j)+' '+str(normalized_vertices))
            elif dir == LE:
                if v[1]>nvi[1]+m*(v[0]-nvi[0]):
                    raise VertexSetException('not in a semicircle LE max i,j'+str(i)+' '+str(j)+' m='+str(m)+' '+str(normalized_vertices))
        
        return vertices[max_i],vertices[max_j]
    
    else: #Our normalized max and min points have the same x coordinate.
        x = normalized_vertices[max_i][0]
        try:
            p = next(v for v in normalized_vertices if (v[0]!=x))
        except StopIteration:
            return vertices[max_i],vertices[max_j]
        
        if any((p[0]-x)*(v[0]-x)<0 for v in normalized_vertices):
            raise VertexSetException('= x coords, not in a semicircle')
        
        return vertices[max_i],vertices[max_j]


#The main routine
# - get vertices of polyhedron
# - for each xy-pair, find the extreme bounds in the xy-plane if they exist.
# - learn these inequalities
def learn_add_comparisons_poly(H):
    learn_add_comparisons_poly_2(H) #Uncomment these two lines to run the alternative algorithm
    return
    
    #Sends a potentially new term comparison to the heuristic
    def learn_term_comparison(i,j,comp,coeff):
        if coeff == None:
            return
        if coeff == 0:
            H.learn_zero_comparison(i,comp,ADD)
        else:
            H.learn_term_comparison(i,j,comp,coeff,ADD)

    #Given a line through the origin in the i-j plane and a noncollinear point,
    #learn either y >= slope * x or y <= slope * x
    #line is a_j = slope * a_i
    def learn_comp_from_line_and_point(i,j,slope,point):
        if point[1] >= slope * point[0]:
            learn_term_comparison(j,i,GE,slope)
        else:
            learn_term_comparison(j,i,LE,slope)
            
    #Main routine
       
    if H.verbose:
        print 'Learning additive facts (polyhedron style...)'
        print
        
    # make additive equations
    add_eqs = [H.name_defs[i] + Add_term([(-1, IVar(i))])
        for i in range(H.num_terms) if isinstance(H.name_defs[i], Add_term)]
    
    add_eqs.extend([c for c in H.zero_equations if isinstance(c, Add_term)])
    
    if H.verbose:
        print "Additive equations:"
        for t in add_eqs:
            print t, "= 0"
        print
    
    #Check for new sign info    
    learn_additive_sign_info(H)
    
    #Create the polytope in H-representation
    matrix = create_H_format_matrix(H,add_eqs)
    
    #Convert to V-representation
    vertices = cdd.Polyhedron(matrix).get_generators()
    
    if H.verbose:
        print
        print 'Polyhedron vertices:'
        for l in vertices:
            print l[1:]#,("(point)" if l[0]==1 else "(ray)")
        print
        print 'Linear set:',vertices.lin_set
        print
        
    #Look comparisons between a_i and a_j by checking each vertex
    for (i,j) in combinations(range(H.num_terms),2):
        
        #For any ray marked as linear, adds it in both directions to proj_verts
        proj_verts = [(vertices[k][i+1],vertices[k][j+1]) for k in range(len(vertices)) if ((vertices[k][i+1]!=0 or vertices[k][j+1]!=0) and k not in vertices.lin_set)]
        for k in vertices.lin_set:
            v = vertices[k]
            if v[i+1]!=0 or v[j+1]!=0:
                proj_verts.extend([(v[i+1],v[j+1]),(-v[i+1],-v[j+1])])
                
        
        #Find the extreme ones. If there are none, try the next pair.
        try:
            bound1,bound2 = get_boundary_vertices(proj_verts)
        except VertexSetException: #Nothing we can learn for this pair
            continue
        
        #all vertices lie in the same halfplane, between the rays bound1 and bound2.
        
        if bound1[0]==0 and bound2[0]==0: #Both rays point along y axis. We'll learn x>0 or x<0
            if bound1[1]*bound2[1]>0: #Our rays point in the same direction. The hull is degenerate
                continue
            try:
                third_point = next((v for v in proj_verts if v[0]!=0))
            except StopIteration: #All vertices are collinear
                continue
            
            if third_point[0] > 0:
                H.learn_zero_comparison(i,GE,ADD)
            else:
                H.learn_zero_comparison(i,LE,ADD)
                
        elif bound1[0]==0: #One ray points along y axis. Learn x>0 or x<0 and something else
            if bound2[0]>0:
                H.learn_zero_comparison(i,GE,ADD)
            else:
                H.learn_zero_comparison(i,LE,ADD)
                
            m = Fraction(bound2[1],bound2[0])
            learn_comp_from_line_and_point(i,j,m,bound1)
            
        elif bound2[0]==0: #One ray points along y axis. Learn x>0 or x<0 and something else
            if bound1[0]>0:
                H.learn_zero_comparison(i,GE,ADD)
            else:
                H.learn_zero_comparison(i,LE,ADD)
            
            m = Fraction(bound1[1],bound1[0])
            learn_comp_from_line_and_point(i,j,m,bound2)
                
        
        else: #Neither ray points along the y axis.
            m1,m2 = Fraction(bound1[1],bound1[0]), Fraction(bound2[1],bound2[0])
            if m1==m2: #points are collinear
                if bound1[0]*bound2[0] >= 0: #point in the same direction. Hull is degenerate
                    continue
                try:
                    third_point = next((v for v in proj_verts if (v[0]==0) or (v[0]!=0 and Fraction(v[1],v[0])!=m1)))
                except StopIteration: #All vertices are collinear
                    continue
                
                learn_comp_from_line_and_point(i,j,m1,third_point)
                
            else:
                #bound1 and bound2 are points (a,b),(c,d) defining inequalities
                #1: y <> b/a * x 
                #2: y <> d/c * x
                learn_comp_from_line_and_point(i,j,m1,bound2)
                learn_comp_from_line_and_point(i,j,m2,bound1)
                
    if H.verbose:
        print

    
#An alternative to the above method.
#This one goes:
# - convert inequalities to a polyhedron in n dimensions
# - project this polyhedron to the a_i-a_j plane for each (i,j)
# - convert back to H format in 2 dimensions and read off inequalities    
def learn_add_comparisons_poly_2(H):
    
    #Note that the coefficients that come in here are reversed due to the format of the matrix.
    #We are learning :
    #  -c_i*a_i + -c_j*a_j <= 0
    def learn_term_comparison(i,j,c_i,c_j):
        if c_i!=0 and c_j!=0:
            #-c_i*a_i + -c_j*a_j <= 0
            coeff = -Fraction(c_j,c_i)
            comp = (GE if c_i>0 else LE)
            #print IVar(i),comp_str[comp],coeff*IVar(j)
            H.learn_term_comparison(i,j,comp,coeff,ADD)
            
        #-c_i*a_i <= c_j * a_j
        elif c_i==0 and c_j!=0:
            H.learn_zero_comparison(j,(GE if c_j>0 else LE),MUL)
        elif c_i!=0 and c_j==0:
            H.learn_zero_comparison(i,(LE if c_i<0 else GE),MUL)
    
    if H.verbose:
        print 'Learning additive facts (polyhedron style...)'
        print
        
    # make additive equations
    add_eqs = [H.name_defs[i] + Add_term([(-1, IVar(i))])
        for i in range(H.num_terms) if isinstance(H.name_defs[i], Add_term)]
    
    add_eqs.extend([c for c in H.zero_equations if isinstance(c, Add_term)])
    
    if H.verbose:
        print "Additive equations:"
        for t in add_eqs:
            print t, "= 0"
        print
        
    learn_additive_sign_info(H)
    
    matrix = create_H_format_matrix(H,add_eqs)
    
    #Convert polyhedron to V-representation
    vertices = cdd.Polyhedron(matrix).get_generators()
    if len(vertices)==0: #Fail gracefully.
        return
    
    if H.verbose:
        print
        print 'Polyhedron vertices:'
        for l in vertices:
            print l[1:]
        print
        print 'Linear set:', vertices.lin_set
        print
        
        
    #Track which vertices correspond to equalities
    v_lin_set = vertices.lin_set
        
    #For every combination a_i,a_j, project to that plane and get inequalities
    for (i,j) in combinations(range(H.num_terms),2):
        proj_vertices = cdd.Matrix([[vertices[0][0],vertices[0][i+1],vertices[0][j+1]]],
                                   linear=(True if 0 in v_lin_set else False), #0 in ...
                                   number_type='fraction')
        proj_vertices.rep_type=cdd.RepType.GENERATOR
        
        for k in range(1,len(vertices)):
            if k in v_lin_set:
                proj_vertices.extend([[vertices[k][0],vertices[k][i+1],vertices[k][j+1]]],linear=True)
            else:
                proj_vertices.extend([[vertices[k][0],vertices[k][i+1],vertices[k][j+1]]],linear=False)
                

        ineqs_i_j = get_2d_inequalities(i,j,proj_vertices)

        
        for n in range(len(ineqs_i_j)):
            k = ineqs_i_j[n]
            if k[0]!=0:
                H.raise_exception("Not homogeneous")
            if n not in ineqs_i_j.lin_set:
                learn_term_comparison(i,j,k[1],k[2])

    if H.verbose:
        print