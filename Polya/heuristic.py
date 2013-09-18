from classes import *
from copy import deepcopy 


###############################################################################
#
# DATA STRUCTURE FOR THE HEURISTIC PROCEDURE
#
###############################################################################

#
# The procedure keeps track of the following data:
#   o the original list of terms
#   o a name of the form "a_i" for each term
#   o the total number of terms
#   o for each i, any known comparison of a_i with 0
#   o for each i < j, any known comparisons between a_i and c * a_j for some c
#   o a flag, 'verbose', for printing
#   o a flag, 'changed', to indicate whether anything has been learned in
#     since the flag was last set to False

def psc(c,x,y):
    return cdict[c.comp](x,c.coeff*y)

def psc_weak(c,x,y):
    return psc(Comparison_data((LE if c.comp in [LE,LT] else GE),c.coeff,c.provenance),x,y)   

class Heuristic_data:

    # Each Heuristic_data has:
    #  terms[i]: ith subterm of hypotheses (in original variables)
    #  name_defs[i]: definition of a_i (using Vars and other a_js)
    #  num_terms = len(terms)
    #  zero_comparisons[i]: Zero_comparison_data corresponding to a_i COMP 0
    #  term_comparisons[i,j]: List of Comparison_data's between a_i, a_j

    # __init__ takes a list of hypotheses, each assumed to be Zero_comparison 
    # like t > 0, where t is assumed to be in canonical form.
    #
    # It stores a list of all the subterms and creates names for them,
    # and then stores the relationship between the names.
    
    # takes a list of terms, stores a list of all subterms and 
    # creats names for them
    # TODO: don't have the init function do all the work.
    def __init__(self, hypotheses, function_information=[], verbose=True):
        self.verbose = False
        
        self.function_information = function_information
        
        # initialize term comparisons
        self.term_comparisons = {}
        
        # Stores terms that are equal to 0, that contain information beyond variable definitions.
        self.zero_equations = []
        

        # make the names
        hterms = [h.term for h in hypotheses]
        self.terms, self.name_defs = make_term_names(hterms)
        self.num_terms = len(self.terms)

        # store hypotheses as zero comparisons
        self.zero_comparisons = {0 : Zero_comparison_data(GT, HYP)}
        #equals_0 = []
        for h in hypotheses:
            self.learn_zero_comparison(self.terms.index(h.term), h.comp, HYP)
#             i = self.terms.index(h.term)
#             if i in self.zero_comparisons.keys():
#                 icomp = self.zero_comparisons[i].comp
#                 if ((icomp == LT and h.comp in [GE, GT]) or (icomp == GT and h.comp in [LE, LT])
#                       or (icomp == LE and h.comp == GT) or (icomp == GE and h.comp == LT)):
#                     self.raise_contradiction(HYP)
#                     return
#                 elif (icomp == LE and h.comp == GE) or (icomp == GE and h.comp == LE):  # learn equality. Not handled yet.
#                     equals_0.append(i)
#                 elif (icomp in [LE, GE] and h.comp in [LT, GT]):
#                     self.learn_zero_comparison(i,h.comp,HYP)
#             else:
#                 self.learn_zero_comparison(i, h.comp, HYP)
            # This should be redundant; leaving it here just in case. 
            # if isinstance(self.name_defs[i],Mul_term) and len(self.name_defs[i].mulpairs)==1 and Fraction(self.name_defs[i].mulpairs[0].exp).numerator%2==0:
            #     self.learn_zero_comparison(i,GE,HYP)


        #for i in equals_0:
        #    self.learn_zero_equality(i, HYP)
            
        self.verbose = verbose

        # print information
        if self.verbose:
            print
            print "Definitions:"
            for i in range(self.num_terms):
                print IVar(i), '=', self.name_defs[i]
                print '  In other words:', IVar(i), '=', self.terms[i]
            print
            print("Hypotheses:")
            for i in range(self.num_terms):
                if i in self.zero_comparisons.keys():
                    print self.zero_comparisons[i].to_string(IVar(i))
                    print '  In other words:', \
                        self.zero_comparisons[i].to_string(self.terms[i])

            print
        
        # If the input had anything of the form  a^(p/q) where q is even,
        # We can assume a is positive.
        verbose_switch = self.verbose
        self.verbose = False
        for t in self.name_defs.keys():
            s = self.name_defs[t]
            if isinstance(s, Mul_term):
                for m in s.mulpairs:
                    if ((isinstance(m.exp, Fraction) and m.exp.denominator % 2 == 0) or
                      (isinstance(m.exp, float) and Fraction(m.exp).denominator % 2 == 0)):
                        self.learn_zero_comparison(m.term.index, GE, HYP)
        self.verbose = verbose_switch
        
    def info_dump(self):
        print '**********'
        for i in self.zero_comparisons.keys():
            print IVar(i),comp_str[self.zero_comparisons[i].comp],'0'
        print
        
        for (i,j) in self.term_comparisons.keys():
            for c in self.term_comparisons[i,j]:
                print IVar(i), comp_str[c.comp], c.coeff,'*',IVar(j)
        print '**********'
            
    
    def get_index_of_name_def(self, term):
        for k in self.name_defs.keys():
            if self.name_defs[k] == term:
                return k
        return None
    
    # Returns a new instance of an identical Heuristic_data  
    def duplicate(self):
        return deepcopy(self)
    

    # If there is data on whether a_i is > 0 or < 0, returns the sign. Otherwise, returns 0
    def sign(self, i):
        if i in self.zero_comparisons.keys():
            comp = self.zero_comparisons[i].comp
            if comp == GT:
                return 1
            elif comp == LT:
                return -1
            else:
                return 0
        else:
            return 0
    
    # If there is data on whether a_i is >= 0 or <=0, returns the sign. Otherwise, returns 0    
    def weak_sign(self, i):
        if i in self.zero_comparisons.keys():
            comp = self.zero_comparisons[i].comp
            if comp == GT or comp == GE:
                return 1
            elif comp == LT or comp == LE:
                return -1
            else:
                return 0
        else:
            return 0
            

    def raise_contradiction(self, provenance):
        raise Contradiction('Contradiction!')
    
    def match_points(self,comps,i_zc,j_zc):
 
        
        
        points = [(c.coeff,1,c.comp,c.provenance) for c in comps]+[(-c.coeff,-1,c.comp,c.provenance) for c in comps]
        if len(i_zc)>0:
            points.extend([(0,1,i_zc[0].comp,i_zc[0].provenance),(0,-1,i_zc[0].comp,i_zc[0].provenance)])
            
        if len(j_zc)>0:
            points.extend([(1,0,j_zc[0].comp,j_zc[0].provenance),(-1,0,j_zc[0].comp,j_zc[0].provenance)])    
        
        for c in comps:
            points = [p for p in points if psc_weak(c,p[0],p[1])]
                    
        for c in i_zc:
            points = [p for p in points if cdict[(GE if c.comp in [GE,GT] else LE)](p[0],0)]

        for c in j_zc:
            points = [p for p in points if cdict[(GE if c.comp in [GE,GT] else LE)](p[1],0)]
        
        return points
    
    #Returns true if the known data implies a_i comp coeff * a_j, false otherwise.
    def implies(self,i,j,comp,coeff):
        #CHECK FOR EQUALITY. NOT IMPLEMENTED YET        
        
        if coeff == 0:
            try: 
                c = self.zero_comparisons[i]
                if c.comp == comp:
                    return True
                elif c.comp == GT and comp == GE:
                    return True
                elif c.comp == LT and comp == LE:
                    return True
                else:
                    return False
            except KeyError:
                return False
            

        comps = self.term_comparisons.get((i,j),[])
        if len(comps)==2 and comps[0].coeff==comps[1].coeff:
            print 'equality',i,j,comp_str[comp],coeff,comps
            return True
        for c in comps:
            if (c.coeff == coeff):
                if ((c.comp == comp) or (c.comp==GT and comp==GE) or (c.comp==LT and comp==LE)):
                    return True
                return False
        #We know coeff!=0, comps is populated, and the comparison being checked is not collinear
        #with any known comparison in comps.
        
        #Find the two points representing the strongest known comparison rays, including sign info.
        try:
            i_zc = [self.zero_comparisons[i]]
        except KeyError:
            i_zc = []
        try:
            j_zc = [self.zero_comparisons[j]]
        except KeyError:
            j_zc = []
            
        points = self.match_points(comps,i_zc,j_zc)
                    
        if len(points) == 0:
            return False
        
        if len(points)!=2:
            print "Problem in implies! there are",len(points),"points left."
            print points
            print " ",IVar(i),comp_str[comp],coeff,IVar(j)
            print comps, self.sign(i),self.sign(j)
            
        for p in points:
            if not psc(Comparison_data(comp,coeff,HYP),p[0],p[1]):
                return False
        return True
                 
        #FINISH WRITING THIS
    
    # Learn a_i = 0.
    # Eliminates a_i from all stored data
    def learn_zero_equality(self, i, provenance):
        if self.name_defs[i] in self.zero_equations or IVar(i) in self.zero_equations:
            return
        if self.verbose:
            print "Learning equality:", IVar(i), "= 0"
        # self.name_defs[i] = zero
        # turn all comparisons with a_i to zero_comparisons
        for j in range(0, i):
            if (j, i) in self.term_comparisons.keys():
                comps = self.term_comparisons[j, i]
                for c in comps:
                    self.learn_zero_comparison(j, c.comp, provenance)
        for j in range(i + 1, self.num_terms):
            if (i, j) in self.term_comparisons.keys():
                comps = self.term_comparisons[i, j]
                for c in comps:
                    self.learn_zero_comparison(j, comp_reverse(c.comp), provenance)
                    
                    
        for k in self.name_defs.keys():
            if k == i:
                continue
            ak = self.name_defs[k]
            if isinstance(ak, Mul_term):
                for c in ak.mulpairs:
                    if c.term.index == i:  # ak = 0
                        if c.exp < 0:
                            raise Exception("Trying to divide by 0!")
                        self.learn_zero_equality(k, provenance)
            elif isinstance(ak, Add_term):
                for c in ak.addpairs:
                    if c.term.index == i:
                        ak.addpairs.remove(c)
                if len(ak.addpairs) == 0:
                    self.learn_zero_equality(ak.index, provenance)
        
        t = self.name_defs[i]            
        if isinstance(t, Add_term):  # 0 = c*a_1+d*a_2+...
            if len(t.addpairs) == 1:
                self.learn_zero_equality(t.addpairs[0].term.index, provenance)
        
        if not isinstance(t, Var):
            self.zero_equations.append(t)
        self.zero_equations.append(IVar(i))
                
    # Adds information about how a_i compares to 0.
    # If the new information contradicts old, raises contradiction.
    def learn_zero_comparison(self, i, comp, provenance):
        if i in self.zero_comparisons.keys():
            old_comp = self.zero_comparisons[i].comp
            if ((old_comp == GE and comp == LE) or 
                (old_comp == LE and comp == GE)):
                self.learn_zero_equality(i, provenance)
                return
                # raise Error('Learn equality - not handled yet')
            elif ((old_comp in [GE, GT] and comp in [LE, LT]) or
                  (old_comp in [LT, LE] and comp in [GE, GT])):
                if self.verbose:
                    c = Zero_comparison_data(comp, provenance)
                    print 'Learned:', c.to_string(IVar(i))
                    print '  In other words:', c.to_string(self.terms[i])
                self.raise_contradiction(provenance)
            elif ((old_comp == GE and comp == GT) or 
                  (old_comp == LE and comp == LT)):
                # new fact is stronger; drop old
                del self.zero_comparisons[i]
            else:  # new fact is weaker
                return

        # add new comparison
        self.zero_comparisons[i] = Zero_comparison_data(comp, provenance)
        self.changed = True
        if self.verbose:
            print 'Learned:', self.zero_comparisons[i].to_string(IVar(i))
            print '  In other words:', \
                   self.zero_comparisons[i].to_string(self.terms[i])
    
    # Learns a_i = coeff * a_j
    def learn_term_equality(self, i, j, coeff, provenance):
        if i == j:
            if coeff != 1:
                self.learn_zero_equality(i, provenance)
            return
        
        if self.verbose:
            print 'Learned:', IVar(i),'=',coeff,'*',IVar(j)
        
        self.zero_equations.append(IVar(i) - IVar(j) * coeff)
        

    # new_comp is Comparison_data to potentially be added. a_i comp coeff a_j,
    #     but this method does not need to know i or j.
    # old_comps is list of comparisons of the same direction as new_comp
    # sign is +1 if a_j positive, -1 if a_j negative, 0 if a_j unknown
    # changes old_comps. returns True if changes are made, False otherwise               
    def make_new_comps(self, new_comp, old_comps, sign):
        # print 'make new comps fed:',new_comp,old_comps,sign
        if not old_comps:  # no comparisons in this direction.
            old_comps.append(new_comp)
            return True
        
        # If new_comp is already in there, no changes needed.    
        if any(new_comp.coeff==o.coeff and (new_comp.comp==o.comp or (new_comp.comp==LE and o.comp==LT) or (new_comp.comp==GE and o.comp==GT)) for o in old_comps):#if new_comp in old_comps:
            return False
            
        if sign == 0:  # We do not know the sign of a_j
            if len(old_comps) == 1:  # Only one element in old_comps, so new_comp has new info
                old_comps.append(new_comp)
                return True
                
            # Otherwise, there are two comps in old_comps.
            # See if new_comp is stronger or weaker than both.
            
            lt_all, gt_all = all(new_comp.le(c) for c in old_comps), all(new_comp.ge(c) for c in old_comps)
            if lt_all:
                for i in range(2):
                    if old_comps[i].le(old_comps[1 - i]):
                        old_comps.pop(i)
                        old_comps.append(new_comp)
                        return True
                        
            elif gt_all:
                for i in range(2):
                    if old_comps[i].ge(old_comps[1 - i]):
                        old_comps.pop(i)
                        old_comps.append(new_comp)
                        return True
                        
            return False
        
        # Otherwise, we do know the sign of a_j. There will only be one element in old_comps now.
        # new_comp should be that element if it is stronger than the alternatives in the proper direction.
        p1 = (new_comp.comp in [LE, LT] and ((sign == 1 and all(new_comp.le(c) for c in old_comps)) or (sign == -1 and all(new_comp.ge(c) for c in old_comps))))
        p2 = (new_comp.comp in [GE, GT] and ((sign == 1 and all(new_comp.ge(c) for c in old_comps)) or (sign == -1 and all(new_comp.le(c) for c in old_comps))))
        if p1 or p2:
            # print 'only one comp. sign = ',sign,'new comp = ',new_comp, 'old_comps = ',old_comps
            while len(old_comps) > 0:
                old_comps.pop()
            old_comps.append(new_comp)
            return True
            
        return False
    
    def learn_term_comparison(self,i,j,comp,coeff,provenance):
        # swap i and j if necessary, so i < j
        if i >= j:
            i, j, coeff = j, i, Fraction(1, Fraction(coeff))
            if coeff > 0:
                comp = comp_reverse(comp)
                
                
        if self.implies(i,j,comp,coeff):
            return
        
        elif self.implies(i,j,comp_negate(comp),coeff):
            if self.verbose:
                print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
                print '  In other words:', \
                       new_comp.to_string(self.terms[i], self.terms[j])
            self.raise_contradiction(provenance)
            return
        
        #Otherwise, we know we have new information.
        
        if coeff == 0:
            self.learn_zero_comparison(i, comp, provenance)
            return
        
#         # See if we can get any zero_comparisons from 1 comp c*a_j.
#         if i == 0:
#             if coeff > 0 and comp in [LE, LT]:  # a_j >= 1/c > 0
#                 self.learn_zero_comparison(j, GT, provenance)
#             elif coeff < 0 and comp in [LE, LT]:  # a_j <= 1/c < 0
#                 self.learn_zero_comparison(j, LT, provenance)
        new_comp=Comparison_data(comp,coeff,provenance)
        comps = self.term_comparisons.get((i,j),[])+[new_comp]
        try:
            i_zc = [self.zero_comparisons[i]]
        except KeyError:
            i_zc = []
            
        try:
            j_zc = [self.zero_comparisons[j]]
        except KeyError:
            j_zc = []
            
        points = self.match_points(comps,i_zc,j_zc)
        if len(points)!=2:
            print 'Not enough points in learn_term_comparison'
            
        if points[0][0]*points[0][1]==points[1][0]*points[1][1]:
            points = [points[0]]
            
        self.term_comparisons[i,j] = [Comparison_data(p[2],p[0]*p[1],p[3]) for p in points if (p[0]!=0 and p[1]!=0)]
        
        if self.verbose:
            print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
            print '  In other words:', \
                   new_comp.to_string(self.terms[i], self.terms[j])
            

    def learn_term_comparison2(self,i,j,comp,coeff,provenance):
        
        if self.implies(i,j,comp,coeff):
            imp = True
            print 'nothing happens'
        elif self.implies(i,j,comp_reverse(comp),coeff):
            imp = False
            print 'contradiction'
        else:
            imp = False
            print 'new info'
        
        ##################
        #
        # Helper functions
        #
        ##################
      
        
        #Comp is a comparison data xRcoeff*y
        #Assumes x,y is not on the line comp
        def point_satisfies_comparison(comp,x,y):
            if comp.comp in [LE,LT]:
                return x < comp.coeff * y
            else:
                return x > comp.coeff * y
        
        #Given comparisons c1 = xR1coeff1*y, c2 = xR2coeff2*y,
        #Finds a point on the line x = coeff2 * y that satisfies c1
        #Assumes the lines are not collinear
        def get_point_from_comparisons(c1,c2):
            x,y = c2.coeff,1
            if point_satisfies_comparison(c1,x,y):
                return (x,y)
            else:
                return (-x,-y)
        
        #Because of problems with infinite slope, zero comparisons are not taken into account in the routine.
        #Once something new has been learned, this subroutine makes sure the resulting state does not
        #contradict the known sign info.
        #It also could check to see if there is new sign info to be found, but this is not implemented yet.
        #Since we do not have coefficients of 0 in term_comparisons, no line will lie along an axis.   
        def check_against_zero_comparisons():
            comps = self.term_comparisons.get((i,j),[])
            if len(comps)==0: #Nothing we can do with no comparisons. This shouldn't happen.
                pass
            elif len(comps)==1: #Possible contradiction if signs of i and j are both known.
                strong = comps[0].comp in [LT,GT]
                si, sj = self.weak_sign(i),self.weak_sign(j)
                
                if not (si==0 or sj==0): #both signs are known. Look for contradiction
                    pi,pj = (si,0),(0,sj)
                    if not point_satisfies_comparison(comps[0],*pi) and not point_satisfies_comparison(comps[0],*pj):
                        if not (self.sign(i)==self.sign(j)==0 and not strong): #If this is false, we have x_i=x_j=0. Can we do something here?
                            print 'from 1'
                            self.raise_contradiction(provenance)
                
                elif si!=0: #sign of xi is known. learn sign of xj
                    #Make sure the known sign of xi is strong if the new comparison is strong.
                    if strong and self.sign(i)==0:
                        self.learn_zero_comparison(i, (GT if si>0 else LT), provenance)
                    
                    # 0 r1 x
                    # x r2 m * y
                    # if r1 and r2 point in the same direction,
                    # learn comparison between y and 0
                    r1 = ((GE if si<0 else LE) if self.sign(i)==0 else (GT if si<0 else LT))
                    r2 = comps[0].comp
                    
                    if (r1 in [LE,LT] and r2 in [LE,LT]) or (r1 in [GE,GT] and r2 in [GE,GT]):
                        if comps[0].coeff > 0:
                            #learn 0 r1 y
                            self.learn_zero_comparison(j, (comp_reverse(r1) if r1==r2 else (LT if r1 in [GE,GT] else GT)), provenance)
                        else:
                            self.learn_zero_comparison(j, (r1 if r1==r2 else (GT if r1 in [GE,GT] else LT)), provenance)
                    
                elif sj!=0: #sign of xj is known. learn sign of xi
                    if strong and self.sign(j)==0:
                        self.learn_zero_comparison(j, (GT if sj>0 else LT), provenance)        
                    
                    # 0 r1 y
                    # x r2 m * y
                    r1 = ((GE if sj<0 else LE) if self.sign(j)==0 else (GT if sj<0 else LT))
                    r2 = comps[0].comp
                    
                    if comps[0].coeff > 0 and ((r1 in [LE,LT] and r2 in [GE,GT]) or (r1 in [GE,GT] and r2 in [LE,LT])):
                        #learn 0 r1 x
                        self.learn_zero_comparison(i,(comp_reverse(r1) if comp_reverse(r1)==r2 else (LT if r1 in [GE,GT] else GT)),provenance)
                    elif comps[0].coeff < 0 and ((r1 in [LE,LT] and r2 in [LE,LT]) or (r1 in [GE,GT] and r2 in [GE,GT])):
                        #learn 0 r2 x == x r1 0
                        self.learn_zero_comparison(i,(comp_reverse(r1) if r1==r2 else (LT if r1 in [GE,GT] else LT)),provenance)
                        

                #Otherwise, no sign info is known. No contradiction and nothing to learn.
                    
            else: #two comparisons.
                si,sj = self.weak_sign(i),self.weak_sign(j)
                p1,p2 = get_point_from_comparisons(comps[0],comps[1]),get_point_from_comparisons(comps[1],comps[0])
                
                #Learning sign information could bring about a contradiction, if it exists
                if p1[0]*p2[0]>0:
                    self.learn_zero_comparison(i, (GT if p1[0]>0 else LT), provenance)
                if p1[1]*p2[1]>0:
                    self.learn_zero_comparison(j, (GT if p1[1]>0 else LT), provenance)
                
                #Check for cases like x>-2y,x>-1/2y, x<0,y<0. Can only happen if we know both sign info
                #These cases occur only if the vertices are in opposite quadrants,
                #where the non-contained quadrant is the one determined by the sign info    
                if (si!=0 and sj!=0): 
                    p = (-si,-sj)
                    if (point_satisfies_comparison(comps[0],*p) and point_satisfies_comparison(comps[1],*p)
                        and
                        (p1[0]*si<0 or p1[1]*sj<0) and (p2[0]*si<0 or p2[1]*sj<0)):
                        self.raise_contradiction(provenance)
                    
                # Otherwise, no contradiction, and no more sign info to learn.
                    
        ###################################### 
        

        if coeff == 0:
            self.learn_zero_comparison(i, comp, provenance)
            return
        # swap i and j if necessary, so i < j
        if i >= j:
            i, j, coeff = j, i, Fraction(1, Fraction(coeff))
            if coeff > 0:
                comp = comp_reverse(comp)
                

        # See if we can get any zero_comparisons from 1 comp c*a_j.
        if i == 0:
            if coeff > 0 and comp in [LE, LT]:  # a_j >= 1/c > 0
                self.learn_zero_comparison(j, GT, provenance)
            elif coeff < 0 and comp in [LE, LT]:  # a_j <= 1/c < 0
                self.learn_zero_comparison(j, LT, provenance)
            
        
        comp_list = self.term_comparisons.get((i,j),[])
        
        new_comp = Comparison_data(comp,coeff,provenance)
        
        #If there are no old comparisons, learn the new one. No sign info to find.
        if len(comp_list)==0:
            self.term_comparisons[i,j]=[new_comp]
            self.changed = True
            if self.verbose:
                print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
                print '  In other words:', \
                       new_comp.to_string(self.terms[i], self.terms[j])   
            if imp: print 'shouldnt be new *',i,j,new_comp 
            check_against_zero_comparisons()
            return
        
        for c in (c for c in comp_list if c.coeff == coeff):
            if c.comp==comp: #new comparison is already there
                return
            elif (c.comp==LT and comp==LE) or (c.comp==GT and comp==GE): #new comparison is weaker
                return
            elif (c.comp==LE and comp==LT) or (c.comp==GE and comp==GT): #new comparison is stronger
                comp_list.remove(c)
            elif (c.comp in [LE,GE] and comp in [LE,GE]): #We have equality.
                self.term_comparisons[i,j]=[c,new_comp]
                self.learn_term_equality(i,j,coeff,provenance)
                self.changed = True
                check_against_zero_comparisons()
                return
            else: #Contradiction
                if self.verbose:
                    print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
                    print '  In other words:', \
                           new_comp.to_string(self.terms[i], self.terms[j])
                self.raise_contradiction(provenance)
                
        #Now there are no comparisons in comp_list with the same coefficient as new_comp.
        
        if len(comp_list)<2:
            comp_list.append(new_comp)
            self.term_comparisons[i,j]=comp_list
            self.changed = True
            if self.verbose:
                print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
                print '  In other words:', \
                       new_comp.to_string(self.terms[i], self.terms[j])
            if imp: print 'shouldnt be new **',i,j,new_comp 
            check_against_zero_comparisons()
            return
        
        #Otherwise, we have two old comparisons and one potentially new one.
        c1,c2 = comp_list[0],comp_list[1]
        
        #First, make sure there's no equality.
        if c1.coeff == c2.coeff:
            if self.verbose:
                print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
                print '  In other words:', \
                       new_comp.to_string(self.terms[i], self.terms[j])
            self.raise_contradiction(provenance)
        
        p1,p2 = get_point_from_comparisons(c2,c1),get_point_from_comparisons(c1,c2) #p1 lies on line c1. p2 lies on c2
        
        satp1,satp2 = point_satisfies_comparison(new_comp,*p1),point_satisfies_comparison(new_comp,*p2)
        
        if satp1 and satp2:
            #new_comp has no new information
            return
        
        elif not (satp1 or satp2):
            #Contradiction
            if self.verbose:
                print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
                print '  In other words:', \
                       new_comp.to_string(self.terms[i], self.terms[j])
            self.raise_contradiction(provenance) 
            
        elif satp1: #new_comp is stronger than c2
            comp_list[1]=new_comp
            
        elif satp2: #new_comp is stronger than c1
            comp_list[0]=new_comp
           
        self.changed = True
        self.term_comparisons[i,j]=comp_list
        if self.verbose:
            print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
            print '  In other words:', \
                   new_comp.to_string(self.terms[i], self.terms[j])
            if imp: print 'shouldnt be new ***',i,j,new_comp 
        check_against_zero_comparisons()