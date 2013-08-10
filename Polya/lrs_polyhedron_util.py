from classes import *
from itertools import combinations
import cdd
import lrs
from timeit import default_timer

#Contains a number of functions for interpreting information sent to and from lrs.
#Nearly all of the machinery for the additive routine is here.
#The multiplicative routine uses some of this as well, but since inferring inequalities
#from projected vertices is more difficult there, much of its code is isolated.
  
# Used in a number of routines below
cdict = {LE:(lambda x,y: x<=y),LT:(lambda x,y:x<y),GE:(lambda x,y:x>=y),GT:(lambda x,y: x>y)}
           

            
# zero_equations is a list of terms == 0.
# zero_comparisons is a list of Zero_comparisons.
# d is the number of variables.
# To use the cdd matrix representation, we need to make a matrix of the form
#   (b | -A)
# where b-Ax >= 0.
# Since our situation is homogenous, b = 0.
# So, Ax <= 0
# And since we store -A, the matrix rows are >= 0.
# The 0th column of the matrix is b. Should always be 0.
# The 1st column of the matrix is delta, strict vs. non-strict inequality info:
# row[1] = -1 iff it is > 0
def create_H_format_matrix(zero_equations,zero_comparisons,d):
    
    base_matrix = []
    
    for c in zero_comparisons:
        term,comp = c.term,c.comp
        if comp in [LE,LT]:
            term,comp = term*(-1),comp_reverse(comp)
            
        row = [0]*(d+2)
        row[1] = (-1 if comp==GT else 0)
        if isinstance(term,Add_term):
            for p in term.addpairs:
                row[p.term.index+2] = p.coeff
        elif isinstance(term,IVar):
            row[term.index+2]=1
            
        base_matrix.append(row)
        
    row = [0]*(d+2)
    row[1] = 1
    base_matrix.append(row)
        
    matrix = cdd.Matrix(base_matrix,number_type='fraction')
    matrix.rep_type = cdd.RepType.INEQUALITY    
    
    eq_rows = []
    for e in zero_equations:
        row = [0]*(d+2)
        for p in e.addpairs:
            row[p.term.index+2] = p.coeff
        eq_rows.append(row)
    
    if eq_rows:
        matrix.extend(eq_rows,linear=True)

    return matrix

#The following functions are helpers for get_boundary_vertices,
#which itself is a helper for the main routine.
def point_satisfies_comparison(comp,x,y):
    return cdict[comp.comp](x,comp.coeff * y)
    
#Point is a triple (d,x,y). Ignore d.
def slope(point):
    if point[2]!=0:
        return Fraction(point[1],point[2])
    else:
        return float('inf')

#Line, given by coordinates (d,x,y) (ignore d)
#Points is an array of triples (ignore first coord)
#Returns true if all points are on the same side (weak) of line
def fall_on_same_side(line,points):
    if line[2]!=0:
        m = Fraction(line[1],line[2])
        le_comp = Comparison_data(LE,m,ADD)
        ge_comp = Comparison_data(GE,m,ADD)
        return (all(point_satisfies_comparison(le_comp,point[1],point[2]) for point in points)
            or (all(point_satisfies_comparison(ge_comp,point[1],point[2]) for point in points)))
    else:
        sign = next((point[2] for point in points if point[2]!=0),None)
        if sign==None:
            return True
        return all(point[2]*sign>=0 for point in points)
    

class VertexSetException(Exception):
    def __init__(self,s=''):
        self.message = s 

#Triples is a list of triples (d,x,y) != (d,0,0). Treat as a pair (x,y)
#If the vertices fall within the same semicircle,
#returns the pair of original vertices (0,x1,y1),(0,x2,y2) that are at the extremes:
#The angle between these two vertices is greater than between any other pair.
#Otherwise, raises a VertexSetException
#If any vertex on boundary has nonzero delta coord, return that one, so weak inequality.
def get_boundary_vertices(vertices):
    if len(vertices)<2:
        raise VertexSetException('fewer than two vertices')
    
    b1,b2 = vertices[0], next((v for v in vertices if 
                               (slope(v)!=slope(vertices[0]) or v[1]*vertices[0][1]<0 or v[2]*vertices[0][2]<0))
                              ,None)
    if b2==None: #all vertices point in the same direction.
        #raise VertexSetException('all vertices point in same direction')
        if any(v[0]!=0 for v in vertices):
            s = (1,b1[1],b1[2])
        else:
            s = (0,b1[1],b1[2])
        
        return s,s 
    
    else:
        for v in vertices:
            if fall_on_same_side(v,[b1,b2]):
                if not fall_on_same_side(b1,[v,b2]): #replace b1 with v
                    b1 = v
                elif not fall_on_same_side(b2,[v,b1]):
                    b2 = v
                elif v[0]!=0:
                    if slope(v)==slope(b1) and b1[0]==0 and (b1[1]*v[1]>=0 and b1[2]*v[2]>=0):
                        b1 = v
                    elif slope(v)==slope(b2) and b2[0]==0 and (b2[1]*v[1]>=0 and b2[2]*v[2]>=0):
                        b2 = v
                        
        for v in vertices:
            if (not fall_on_same_side(b1,vertices)) or (not fall_on_same_side(b2,vertices)):
                #This can happen when vertices have been added from the linear set.
                raise VertexSetException('points not in semicircle.')
            

    return b1,b2

class timecount_p:
    time = 0
    runs = 0

def get_generators(zero_equations,zero_comparisons,num_terms):
    matrix = create_H_format_matrix(zero_equations,zero_comparisons,num_terms)
    vertices,lin_set = lrs.get_generators(matrix)
    return vertices,lin_set

def get_2d_comparisons(vertices,lin_set):
    
    #Learned_comps is a list of 4-tuples (i,j,comp,coeff)
    learned_term_comps = []
    #learned_zero_comps is a list of pairs (i,comp)
    learned_zero_comps = []
    
    num_terms = len(vertices[0])-2
    
    #Sends a potentially new term comparison to the heuristic
    def learn_term_comparison(i,j,comp,coeff):
        if coeff == None:
            return
        if coeff == 0:
            learned_zero_comps.append((i,comp))
        else:
            learned_term_comps.append((i,j,comp,coeff))

    #Given a line through the origin in the i-j plane and a noncollinear point,
    #learn either a_i > slope * a_j or a_i < slope * aj
    #line is a_i = slope * aj
    def learn_comp_from_line_and_point(i,j,slope,point,strong):
        if point[0] >= slope * point[1]:
            learn_term_comparison(i,j,(GT if strong else GE),slope)
        else:
            learn_term_comparison(i,j,(LT if strong else LE),slope)
            
    
    if all(v[1]==0 for v in vertices): #We have a degenerate system where all terms = 0. Since 1!=0, contradiction
        raise Contradiction
        
    #Look for comparisons between a_i and a_j by checking each vertex
    for (i,j) in combinations(range(num_terms),2):
        
                
        proj_verts = []
        weak = False
        for k in range(len(vertices)):
            v = vertices[k]
            if v[i+2]!=0 or v[j+2]!=0:
                proj_verts.append((v[1],v[i+2],v[j+2]))
            elif v[1]!=0: #(c,0,0) is a vertex, so (c-epsilon,0,0) is reachable. Cannot have strict comp between i and j
                weak = True
        for k in lin_set:#vertices.lin_set:
            v = vertices[k]
            if v[1]!=0: print 'SOMETHING STRANGE, LINEAR VERTEX WITH NONZERO DELTA'
            if v[i+2]!=0 or v[j+2]!=0:
                proj_verts.append((v[1],-v[i+2],-v[j+2]))
                
        #Find the extreme ones. If there are none, try the next pair.
        try:
            bound1,bound2 = get_boundary_vertices(proj_verts)
        except VertexSetException: #Nothing we can learn for this pair
            continue
        
        #all vertices lie in the same halfplane, between the rays bound1 and bound2.
        
        strong1,strong2 = (not weak) and (bound1[0]==0), (not weak) and (bound2[0]==0)
        bound1,bound2 = bound1[1:],bound2[1:]
            
        
        if bound1[1]==0 and bound2[1]==0: #both rays point along x axis. Learn y>0 or y<0
            if bound1[0]*bound2[0]>0: #rays point in the same direction. Learn equality
                if strong1 or strong2:
                    raise Contradiction
                learned_zero_comps.append((j,GE))
                learned_zero_comps.append((j,LE))
                continue
            
            try:
                third_point = next((v[1:] for v in proj_verts if v[2]!=0))
            except StopIteration: #All vertices are collinear
                continue
            
            if third_point[1]>0:
                learned_zero_comps.append((j,(GT if (strong1 and strong2) else GE)))
            else:
                learned_zero_comps.append((j,(LT if (strong1 and strong2) else LE)))
                
        elif bound1[1]==0: #One ray points along x axis. Learn y>0 or y<0 and something else
            if bound2[1]>0:
                learned_zero_comps.append((j,(GT if strong1 else GE)))
            else:
                learned_zero_comps.append((j,(LT if strong1 else LE)))
            
            m = Fraction(bound2[0],bound2[1])
            learn_comp_from_line_and_point(i,j,m,bound1,strong2)  
            
        elif bound2[1]==0: #One ray points along x axis. Learn y>0 or y<0 and something else
            if bound1[1]>0:
                learned_zero_comps.append((j,(GT if strong2 else GE)))
            else:
                learned_zero_comps.append((j,(LT if strong2 else LE)))
            
            m = Fraction(bound1[0],bound1[1])
            learn_comp_from_line_and_point(i,j,m,bound2,strong1)
            
        else: #Neither ray points along the x axis.
            m1,m2 = Fraction(bound1[0],bound1[1]),Fraction(bound2[0],bound2[1])
            if m1==m2: # points are collinear
                if bound1[0]*bound2[0]>=0 and bound1[1]*bound2[1]>=0: #point in same direction. Learn equality
                    learn_term_comparison(i,j,GE,m1)
                    learn_term_comparison(i,j,LE,m1)
                    continue
                
                try:
                    third_point = next((v[1:] for v in proj_verts if (v[2]==0 and v[1]!=0) or (v[2]!=0 and Fraction(v[1],v[2])!=m1)))
                except StopIteration: #All vertices are collinear
                    continue
                
                learn_comp_from_line_and_point(i,j,m1,third_point,(strong1 and strong2))
                
            else: #Not collinear, not along y axis
                learn_comp_from_line_and_point(i,j,m1,bound2,strong1)
                learn_comp_from_line_and_point(i,j,m2,bound1,strong2)
                
    return learned_term_comps,learned_zero_comps

#zero_equations is a list of terms that are equal to 0
#zero_comparisons is a list of zero_comparison objects
#num_terms is the number of variables
def get_comparison_list(zero_equations,zero_comparisons,num_terms,verbose):            
    
    #Convert to V-representation
    vertices,lin_set = get_generators(zero_equations,zero_comparisons,num_terms)
    
    if verbose:
        print 'Polyhedron vertices: (first coord is delta)'
        for v in vertices:
            print v[1:]
        print
    
        
    if all(v[1]==0 for v in vertices): #We have a degenerate system where all terms = 0. Since 1!=0, contradiction
        raise Contradiction
        
    return get_2d_comparisons(vertices,lin_set)
