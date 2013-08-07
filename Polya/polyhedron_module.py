from classes import *
from heuristic import *
from itertools import combinations
import cdd
  
# Used in a number of routines below
cdict = {LE:(lambda x,y: x<=y),LT:(lambda x,y:x<y),GE:(lambda x,y:x>=y),GT:(lambda x,y: x>y)}
           
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


#The following functions are helpers for get_boundary_vertices,
#which itself is a helper for the main routine.
def point_satisfies_comparison(comp,x,y):
    return cdict[comp.comp](x,comp.coeff * y)
    
def slope(point):
    if point[0]!=0:
        return Fraction(point[1],point[0])
    else:
        return float('inf')

#Line, given by coordinates (x,y)
#Points is an array of pairs
#Returns true if all points are on the same side (weak) of line
def fall_on_same_side(line,points):
    if line[1]!=0:
        m = Fraction(line[0],line[1])
        le_comp = Comparison_data(LE,m,ADD)
        ge_comp = Comparison_data(GE,m,ADD)
        return (all(point_satisfies_comparison(le_comp,*point) for point in points)
            or (all(point_satisfies_comparison(ge_comp,*point) for point in points)))
    else:
        sign = next((point[1] for point in points if point[1]!=0),None)
        if sign==None:
            return True
        return all(point[1]*sign>=0 for point in points)
    

class VertexSetException(Exception):
    def __init__(self,s=''):
        self.message = s 

#Vertices is a list of pairs (x,y) != (0,0).
#If the vertices fall within the same semicircle,
#returns the pair of original vertices (0,x1,y1),(0,x2,y2) that are at the extremes:
#The angle between these two vertices is greater than between any other pair.
#Otherwise, raises a VertexSetException
def get_boundary_vertices(vertices):
    if len(vertices)<2:
        raise VertexSetException('fewer than two vertices')
    
    b1,b2 = vertices[0], next((v for v in vertices if 
                               (slope(v)!=slope(vertices[0]) or v[0]*vertices[0][0]<0 or v[1]*vertices[0][1]<0))
                              ,None)
    if b2==None: #all vertices point in the same direction.
        #raise VertexSetException('all vertices point in same direction')
        return b1,vertices[1]
    
    for v in vertices:
        if fall_on_same_side(v,[b1,b2]):
            if not fall_on_same_side(b1,[v,b2]): #replace b1 with v
                b1 = v
            elif not fall_on_same_side(b2,[v,b1]):
                b2 = v
                
    for v in vertices:
        if (not fall_on_same_side(b1,vertices)) or (not fall_on_same_side(b2,vertices)):
            #This can happen when vertices have been added from the linear set.
            raise VertexSetException('points not in semicircle.')
        
    return b1,b2


#The main routine
# - get vertices of polyhedron
# - for each xy-pair, find the extreme bounds in the xy-plane if they exist.
# - learn these inequalities
def learn_add_comparisons_poly(H):
    #learn_add_comparisons_poly_2(H) #Uncomment these two lines to run the alternative algorithm
    #return
    
    #H.info_dump()

    
    #Sends a potentially new term comparison to the heuristic
    def learn_term_comparison(i,j,comp,coeff):
        if coeff == None:
            return
        if coeff == 0:
            H.learn_zero_comparison(i,comp,ADD)
        else:
            H.learn_term_comparison(i,j,comp,coeff,ADD)

    #Given a line through the origin in the i-j plane and a noncollinear point,
    #learn either a_i > slope * a_j or a_i < slope * aj
    #line is a_i = slope * aj
    def learn_comp_from_line_and_point(i,j,slope,point,strong):
        if point[0] >= slope * point[1]:
            learn_term_comparison(i,j,(GT if strong else GE),slope)
        else:
            learn_term_comparison(i,j,(LT if strong else LE),slope)

    def vert_satisfies_comp(vertex,comp):
        ls,rs = vertex[0],vertex[1]*comp.coeff
        return cdict[comp.comp](ls,rs)

    def vert_satisfies_zero_comp(vertex,i,comp):
        return cdict[comp.comp](vertex[i],0)
            
    #Returns true if vertex satisfies all strict comparisons between a_i,a_j
    def reachable(i,j,vertex):
        for c in H.term_comparisons.get((i,j),[]):
            if not vert_satisfies_comp(vertex,c):
                return False
        
        c = H.zero_comparisons.get(i,None)    
        if c!=None and not vert_satisfies_zero_comp(vertex,0,c):
            return False
        
        c = H.zero_comparisons.get(j,None)
        if c!=None and not vert_satisfies_zero_comp(vertex,1,c):
            return False
        
        return True
            
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
        proj_verts = [(vertices[k][i+1],vertices[k][j+1]) for k in range(len(vertices))
                       if ((vertices[k][i+1]!=0 or vertices[k][j+1]!=0) and k not in vertices.lin_set)]
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
        
        strong1,strong2 = not reachable(i,j,bound1), not reachable(i,j,bound2)
#         if (i,j)==(7,11):
#             print (i,j)
#             print proj_verts
#             print bound1,bound2
#             print strong1,strong2
            
        
        if bound1[1]==0 and bound2[1]==0: #both rays point along x axis. Learn y>0 or y<0
            if bound1[0]*bound2[0]>0: #rays point in the same direction. The cone is degenerate
                #Or, do we learn y = 0?
#                 print 'both bounds are 0'
#                 print i,j
#                 print proj_verts
#                 print bound1,bound2
                H.learn_zero_comparison(j,GE,ADD)
                H.learn_zero_comparison(j,LE,ADD)
                continue
            
            try:
                third_point = next((v for v in proj_verts if v[1]!=0))
            except StopIteration: #All vertices are collinear
                continue
            
            if third_point[1]>0:
                H.learn_zero_comparison(j,(GT if (strong1 and strong2) else GE),ADD)
            else:
                H.learn_zero_comparison(j,(LT if (strong1 and strong2) else LE),ADD)
                
        elif bound1[1]==0: #One ray points along x axis. Learn y>0 or y<0 and something else
            if bound2[1]>0:
                H.learn_zero_comparison(j,(GT if strong1 else GE),ADD)
            else:
                H.learn_zero_comparison(j,(LT if strong1 else LE),ADD)
            
            m = Fraction(bound2[0],bound2[1])
            learn_comp_from_line_and_point(i,j,m,bound1,strong2)  
            
        elif bound2[1]==0: #One ray points along x axis. Learn y>0 or y<0 and something else
            if bound1[1]>0:
                H.learn_zero_comparison(j,(GT if strong2 else GE),ADD)
            else:
                H.learn_zero_comparison(j,(LT if strong2 else LE),ADD)
            
            m = Fraction(bound1[0],bound1[1])
            learn_comp_from_line_and_point(i,j,m,bound2,strong1)
            
        else: #Neither ray points along the x axis.
            m1,m2 = Fraction(bound1[0],bound1[1]),Fraction(bound2[0],bound2[1])
            if m1==m2: # points are collinear
                if bound1[0]*bound2[0]>=0 and bound1[1]*bound2[1]>=0: #point in same direction. Hull is degenerate
                    #Or, do we learn equality?
#                     print 'both bounds are same dir nonzero'
#                     print i,j, m
#                     print proj_verts
#                     print bound1,bound2
                    H.learn_term_comparison(i,j,GE,m1,ADD)
                    H.learn_term_comparison(i,j,LE,m1,ADD)
                    continue
                
                try:
                    third_point = next((v for v in proj_verts if (v[1]==0) or (v[1]!=0 and Fraction(v[0],v[1])!=m1)))
                except StopIteration: #All vertices are collinear
                    continue
                
                learn_comp_from_line_and_point(i,j,m1,third_point,(strong1 and strong2))
                
            else: #Not collinear, not along y axis
                learn_comp_from_line_and_point(i,j,m1,bound2,strong1)
                learn_comp_from_line_and_point(i,j,m2,bound1,strong2)
                  
            
        #########OLD##########
                    
#         if bound1[0]==0 and bound2[0]==0: #Both rays point along y axis. We'll learn x>0 or x<0
#             if bound1[1]*bound2[1]>0: #Our rays point in the same direction. The hull is degenerate
#                 continue
#             try:
#                 third_point = next((v for v in proj_verts if v[0]!=0))
#             except StopIteration: #All vertices are collinear
#                 continue
#             
#             if third_point[0] > 0:
#                 H.learn_zero_comparison(i,(GT if strong1 and strong2 else GE),ADD)
#             else:
#                 H.learn_zero_comparison(i,(LT if strong1 and strong2 else LE),ADD)
#                 
#         elif bound1[0]==0: #One ray points along y axis. Learn x>0 or x<0 and something else
#             if bound2[0]>0:
#                 H.learn_zero_comparison(i,(GT if strong1 else GE),ADD)
#             else:
#                 H.learn_zero_comparison(i,(LT if strong1 else LE),ADD)
#                 
#             m = Fraction(bound2[1],bound2[0])
#             learn_comp_from_line_and_point(i,j,m,bound1,strong2)
#             
#         elif bound2[0]==0: #One ray points along y axis. Learn x>0 or x<0 and something else
#             if bound1[0]>0:
#                 H.learn_zero_comparison(i,(GT if strong2 else GE),ADD)
#             else:
#                 H.learn_zero_comparison(i,(LT if strong2 else LE),ADD)
#             
#             m = Fraction(bound1[1],bound1[0])
#             learn_comp_from_line_and_point(i,j,m,bound2,strong1)
#                 
#         
#         else: #Neither ray points along the y axis.
#             m1,m2 = Fraction(bound1[1],bound1[0]), Fraction(bound2[1],bound2[0])
#             if m1==m2: #points are collinear
#                 if bound1[0]*bound2[0] >= 0: #point in the same direction. Hull is degenerate
#                     continue
#                 try:
#                     third_point = next((v for v in proj_verts if (v[0]==0) or (v[0]!=0 and Fraction(v[1],v[0])!=m1)))
#                 except StopIteration: #All vertices are collinear
#                     continue
#                 
#                 learn_comp_from_line_and_point(i,j,m1,third_point,(strong1 and strong2))
#                 
#             else:
#                 #bound1 and bound2 are points (a,b),(c,d) defining inequalities
#                 #1: y <> b/a * x 
#                 #2: y <> d/c * x
#                 learn_comp_from_line_and_point(i,j,m1,bound2,strong1)
#                 learn_comp_from_line_and_point(i,j,m2,bound1,strong2)
                
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