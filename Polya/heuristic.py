from classes import *
from copy import deepcopy 
from itertools import product


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

class Equiv_class:
    # rep is an int, representing the index of the class representative
    # equivs is a list of pairs (c, i) representing a_rep = c*a_i
    def __init__(self,rep,equivalences):
        self.rep = rep
        self.coeffs = {rep:1}
        for (c,i) in equivalences:
            self.coeffs[i]=c
            
    def coeff(self,k):
        return self.coeffs[k]
    
    def learn_equiv(self,i,coeff):
        if i in self.coeffs:
            if self.coeffs[i]!=coeff: #Something is wrong here. Everything is zero.
                pass
        self.coeffs[i] = coeff
        
# Allows modules to query the heuristic for incremental changes.
# Stores a dict mapping module identifier to set of pairs {(i,j)},
# representing that new info has been learned about a_i and a_j since the last time n asked.
# If (i, -1) is in the list, there was information learned about the sign of a_i.
class Change_tracker:
    
    def __init__(self, H):
        self.database = {}
        self.heuristic = H
    
    # Called when the heuristic learns a new comparison.
    # Adds the pair (i,j) to each list.
    def set_changed(self,i,j):
        if (j<i):
            self.set_changed(j, i)
            return
        
        for key in self.database:
            self.database[key].add((i,j))
    
    # Returns the set of pairs that have changed since the last time module called get_changes.
    # If this is the first time, returns the current state of the heuristic.
    def get_changes(self,module):
        try:
            changes = self.database[module]
            self.database[module]=set()
            return changes
        except KeyError:
            self.database[module]=set()
            return set(self.heuristic.term_comparisons.keys()+[(c,-1) for c in self.heuristic.zero_comparisons.keys()])

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
    def __init__(self, hypotheses, axioms=[], verbose=True):
        self.verbose = False
        
        self.axioms = axioms
        
        # initialize term comparisons
        self.term_comparisons = {}
        
        # Stores terms that are equal to 0, that contain information beyond variable definitions.
        self.zero_equations = []
        
        self.equiv_classes = {}
        self.get_class = {}
        
        self.change_tracker = Change_tracker(self)

        # make the names
        hterms = [h.term for h in hypotheses]
        self.terms, self.name_defs = make_term_names(hterms, None, None)
        self.num_terms = len(self.terms)

        # store hypotheses as zero comparisons
        self.zero_comparisons = {0 : Zero_comparison_data(GT, HYP)}
        #equals_0 = []
        for h in hypotheses:
            self.learn_zero_comparison(self.terms.index(h.term), h.comp, HYP)

            
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
        for i in self.name_defs:
            print IVar(i),'=', self.name_defs[i]
        print

        for i in self.zero_comparisons.keys():
            print IVar(i),comp_str[self.zero_comparisons[i].comp],'0'
        print
        
        for (i,j) in self.term_comparisons.keys():
            for c in self.term_comparisons[i,j]:
                print IVar(i), comp_str[c.comp], c.coeff,'*',IVar(j)
        print '**********'
            
    # Returns a list of pairs (c,j), representing a_i = c*a_j
    # I don't think this is right! Fix it.
    def get_equivalences(self,i,include_self=False):
        if i not in self.get_class:
            return ((1,i) if include_self else [])
        eqc = self.equiv_classes[self.get_class[i]]
        if include_self:
            return [(pair[1],pair[0]) for pair in eqc.items()]
        else:
            return [(pair[1],pair[0]) for pair in eqc.items() if pair[0]!=i]
        
    #returns a list of triples (i,j,c) representing a_i = c * a_j 
    #does not return every equation, but every equation can be deduced from what is returned.
    def get_all_equivalences(self):
        l = []
        for k in self.equiv_classes:
            for i in self.equiv_classes[k].coeffs:
                l.append((k,i,self.equiv_classes[k].coeffs[i]))
        return l
        
    def get_changes(self,module):
        return self.change_tracker.get_changes(module)
    

    # Assumes that each item of term is a Var.
    # ie, if term is an Add_term, it is a sum of constants times vars.
    # Returns a list of Arg_assns mapping each variable name to an IVar, and the overall term identity.
    # Essentially, given a structure, this returns every term that has that structure, along with what
    # you must plug into the structure to get that term.
    def get_terms_of_struct(self,term):
        def generate_environments(map,identity):
            new_maps = []
            iter = product(*[map[k] for k in map])
            inds = [k for k in map]
            for item in iter:
               # new_maps.append(Arg_assn({inds[i]:item[i] for i in range(len(inds))},identity))
               raise Exception("is this used?")
            return new_maps
        
        arg_assns = []
        if isinstance(term,Add_term):
            l = len(term.addpairs)
            candidates = [(i, self.name_defs[i]) for i in range(self.num_terms) 
                          if (isinstance(self.name_defs[i],Add_term)
                          and len(self.name_defs[i].addpairs)==l)]
            
            for (i,t) in candidates:
                map = {}
                pairs = t.addpairs
                for i in range(l):
                    c = Fraction(pairs[i].coeff,term.addpairs[i].coeff)
                    equivs = set(p[1] for p in self.get_equivalences(pairs[i].term.index,True) if p[0]==c)
                    if term.addpairs[i].term in map:
                        map[term.addpairs[i].term].intersection_update(equivs)
                    else:
                        map[term.addpairs[i].term] = equivs
                        
                    if len(map[term.addpairs[i].term])==0:
                        empty = True
                        break
                
                if empty:
                     continue
                #At this point, map is a complete map from variables of term x to lists of ints i,
                #where each i is the index of a term that we can map x to to turn term into t.
                #We turn this into a list of all possible assignments that turn x into t.
                arg_assns.extend(generate_environments(map))
        
        elif isinstance(term,Mul_term):
            pass
        
        elif isinstance(term, Var):
            pass
        
        elif isinstance(term,Func_term):
            pass
        
        return arg_assns
    
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
        self.change_tracker.set_changed(i, -1)
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
        
        if i in self.get_class and j in self.get_class: 
            #There are equivalence classes for both a_i and a_j
            #Merge the one for a_j into the one for a_i
            ind_i, ind_j = self.get_class[i],self.get_class[j]
            coeff_i,coeff_j = self.equiv_classes[ind_i].coeff(i),self.equiv_classes[ind_j].coeff(j)
            conv = Fraction(coeff_i * coeff , coeff_j)
            for k in self.equiv_classes[ind_j].coeffs:
                self.equiv_classes[ind_i].learn_equiv(k,conv*self.equiv_classes[ind_j].coeff(k))
                self.get_class[k] = ind_i
                
            self.equiv_classes.pop(ind_j)
            
        
        elif i in self.get_class:
            ind_i = self.get_class[i]
            coeff_i = self.equiv_classes[ind_i].coeff(i)
            coeff_j = coeff_i * coeff
            self.equiv_classes[ind_i].learn_equiv(j,coeff_j)
            self.get_class[j] = ind_i
            
        elif j in self.get_class:
            ind_j = self.get_class[j]
            coeff_j = self.equiv_classes[ind_j].coeff(j)
            coeff_i = Fraction(coeff,coeff_j)
            self.equiv_classes[ind_j].learn_equiv(i,coeff_i)
            self.get_class[i] = ind_j
        
        else:
            #Make a new equiv class with representative a_i
            new_equiv_class = Equiv_class(i,[(coeff,j)])
            self.equiv_classes[i] = new_equiv_class
            self.get_class[i] = i
            self.get_class[j] = i
        
    
    def learn_term_comparison(self,i,j,comp,coeff,provenance):
        if coeff == 0:
            self.learn_zero_comparison(i, comp, provenance)
            return
                
        # swap i and j if necessary, so i < j
        if i >= j:
            i, j, coeff = j, i, Fraction(1, Fraction(coeff))
            if coeff > 0:
                comp = comp_reverse(comp)
                
        new_comp=Comparison_data(comp,coeff,provenance)
        
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

#         # See if we can get any zero_comparisons from 1 comp c*a_j.
#         if i == 0:
#             if coeff > 0 and comp in [LE, LT]:  # a_j >= 1/c > 0
#                 self.learn_zero_comparison(j, GT, provenance)
#             elif coeff < 0 and comp in [LE, LT]:  # a_j <= 1/c < 0
#                 self.learn_zero_comparison(j, LT, provenance)
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
        self.changed = True
        self.change_tracker.set_changed(i, j)
        if self.verbose:
            print 'Learned:', new_comp.to_string(IVar(i), IVar(j))
            print '  In other words:', \
                   new_comp.to_string(self.terms[i], self.terms[j])
            