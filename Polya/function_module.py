from classes import *
from heuristic import *
from itertools import product, ifilter
from inspect import getargspec
from copy import copy

init = True

# Takes preterms u1...un involving uvars v1...vm
# arg_uvars is a subset of uvars representing those that occur as arguments
# to a Func_term in preterms.
# Returns a list of assignments {vi <- ci*t_{ji}} such that
# each ui becomes equal to a problem term.
def unify(H, preterms, uvars, arg_uvars):
    
    def occurs_as_arg(term,var):
        if not isinstance(term,Func_term):
            return False
        for a in term.args:
            if a.term == var:
                return True
        return False
    
    # Replaces all instances of uvar in preterm with coeff*IVar(iind)
    # Returns a new Term, and a flag True/False representing whether all
    # UVars have been replaced.
    def substitute(preterm, uvar, coeff, iind):
        if isinstance(preterm, IVar):
            return (preterm, True)
            
        elif isinstance(preterm, UVar):
            if preterm.index == uvar.index:
                return (coeff * IVar(iind), True)
            else:
                return (preterm, False)
        
        elif isinstance(preterm, Add_term):
            s, flag = substitute(preterm.addpairs[0].term,uvar,coeff,iind)
            t = preterm.addpairs[0].coeff * s
            for ap in preterm.addpairs[1:]:
                s, flag2 = substitute(ap.term,uvar,coeff,iind)
                flag = flag and flag2
                t += ap.coeff * s
            return (t, flag)
        
        elif isinstance(preterm, Mul_term):
            s, flag = substitute(preterm.mulpairs[0].term,uvar,coeff,iind)
            t = s**preterm.mulpairs[0].exp
            for mp in preterm.mulpairs[1:]:
                s, flag2 = substitute(mp.term,uvar,coeff,iind)
                flag = flag and flag2
                t *= s**mp.exp
            return (t, flag)
        
        elif isinstance(preterm, Func_term):
            flag = True
            nargs = []
            for a in preterm.args:
                s, flag2 = substitute(a.term,uvar,coeff,ind)
                nargs.append((a.coeff, s))
                flag = flag and flag2
            return (Func_term(preterm.name, nargs, preterm.const), flag)
    ####
    
    if len(uvars) == 0:
        return []
    
    if len(arg_uvars) == 0:
        #We are in the unfortunate position where no variables occur alone in function terms.
        #Pass for now.
        return []
    
    v = arg_uvars[0]
    t = next(term for term in preterms if occurs_as_arg(term,v))
    ind = next(j for j in len(term.args) if term.args[j].term==v)
    c = t.args[ind].coeff
    
    prob_f_terms = [i for i in range(H.num_terms) if 
                  (isinstance(H.name_defs[i],Func_term) 
                   and len(H.name_defs[i].args)==len(t.args))]
    
    S = [(Fraction(H.name_defs[i].args[ind].coeff,c),i) for i in prob_f_terms]
    # S is a list of pairs (coeff, j) such that c*coeff*a_j occurs as an argument
    # in a problem term.
    
    for (coeff, j) in S:
        new_preterms = [substitute(p, v, coeff, j) for p in preterms]
        closed_terms, open_terms = [a for (a,b) in new_preterms if b], [a for (a,b) in new_preterms if not b]
        prob_terms, imp = [], False
        for ct in closed_terms:
            try:
                prob_terms.append(find_problem_term(ct))
            except No_Term_Exception:
                imp = True
                break
        if imp:
            continue
        
        map = unify(H, open_terms, [v0 for v0 in uvars if v0!=v], arg_uvars[1:])
        # add v <- coeff*a_j to map and return that
        
class No_Term_Exception(Exception):
    pass

# u is a preterm such that all variable occurences are IVars
# returns (c, i) such that u = c*a_i, or raises No_Term_Exception
def find_problem_term(H, u):
    if isinstance(u, IVar):
        return (1, u.index)
    
    elif isinstance(u, Func_term):
        nargs = [(lambda x,y:(x[0]*y,x[1]))(find_problem_term(H,p.term),p.coeff) for p in u.args]
        for i in [i for i in range(H.num_terms) if 
          (isinstance(H.name_defs[i],Func_term) 
          and H.name_defs[i].name == u.name
          and len(H.name_defs[i].args)==len(nargs))]:
            t = H.name_defs[i]
            good = True
            for k in range(len(t.args)):
                targ, uarg = (t.args[k].coeff, t.args[k].term.index), nargs[k]
                if not (targ[0]==uarg[0] and targ[1]==uarg[1]):
                    eqs = H.get_equivalences(targ.term)
                    if not any(uarg[0]==targ[0]*e[0] and uarg[1]==e[1] for e in eqs):
                        good = False
                        break
                        #Move on to the next i
            if good:
                #a_i is a func_term whose arguments match u
                return (1, i)
        # No i has been found that matches.
        raise No_Term_Exception
    
    elif isinstance(u, Add_term):
        #temporary
            
        npairs = [(lambda x,y:(x[0]*y,x[1]))(find_problem_term(H,p.term),p.coeff) for p in u.addpairs]
        t = npairs[0][0]*IVar(npairs[0][1])
        for p in npairs[1:]:
            t+=p[0]*IVar(p[1])
            
        for i in range(len(H.num_terms)):
            if str(u)==str(H.name_defs[i]) or str(p)==str(H.name_defs[i]):
                return (1, i) 
        raise No_Term_Exception
    
    elif isinstance(u, Mul_term):
        #temporary- copy above
        raise No_Term_Exception
    

# Represents the conclusion of a Function_restriction.    
class Function_conclusion:
    
    # lterm, rterm are lambda functions with the same arguments that are expected to return Terms.
    # their first arguments must be a Heuristic_data
    # comp is GE,GT,LE,LT
    def __init__(self, lterm, rterm, comp):
        self.lterm = lterm
        self.rterm = rterm
        self.comp = comp
        
    def __str__(self):
        return str(self.lterm) + " " + comp_str[self.comp] + " " + str(self.rterm)
        
    # ivars is a tuple of IVars with len(ivars) equal to the number of free variables in lterm and rterm
    # H is a Heuristic_data
    # This function computes the term_ or zero_comparison generated by plugging in ivars to lterm and rterm
    # and sends it to H.
    def learn_term_comparison(self, ivars, H):
        left = self.lterm(H, *ivars)
        right = self.rterm(H, *ivars)
        comp = self.comp
        
        if isinstance(left, IVar):
            i = left.index
        elif left == 0:
            self.learn_zero_comparison(right, comp_reverse(comp), H)
            return
        else:
            i = H.get_index_of_name_def(left)
            if not i:
                return 
            
        if isinstance(right, IVar):
            j = right.index
        elif right == 0:
            self.learn_zero_comparison(left, comp, H)
            return
        else:
            j = H.get_index_of_name_def(right)
            if not j:
                return
            
        H.learn_term_comparison(i, j, comp, 1, FUN)
        
        
    def learn_zero_comparison(self, term, comp, H):
        if isinstance(term, IVar):
            H.learn_zero_comparison(term.index, comp, FUN)
        else:
            i = H.get_index_of_name_def(term)
            if i:
                H.learn_zero_comparison(i, comp, FUN)

# This is the main class used to pass information about a function.
class Function_restriction:
    # name is a string, only used to identify this piece of info: ie, "monotonicity of exp"
    # hypotheses is a lambda predicate whose first argument is a Heuristic_data
    # conclusion is a Function_conclusion whose lterm and rterm have the same arguments as hypotheses
    # For all {free_vars} in {a0,a1,...,an}, [hypotheses({freevars})] => conclusion({freevars})
    def __init__(self, name, hypotheses, conclusion):
        self.name = name
        hargs, clargs, crargs = getargspec(hypotheses).args, getargspec(conclusion.lterm).args, getargspec(conclusion.rterm).args
        if hargs != clargs or hargs != crargs:
            raise Exception("Bad conclusion arguments!")
        self.hypotheses = hypotheses
        self.conclusion = conclusion
        
    def __str__(self):
        # return 'Function name: '+self.name+'. For all '+str(self.free_vars)+'('+str(self.hypotheses)+'=>'+str(self.conclusion)+')'
        return self.name
    
class Environment:
    def __init__(self,map={}):
        self.map = map
        
    def assign(self,x,y):
        self.map[x]=y
        
    def val(self,x):
        return self.map[x]
    
# Takes a list of maps from variable names to lists of IVar indices.
# Generates the intersection of all the maps:
#  a list of Environments such that each environment maps each variable name
#  to something in its range in each initial map.
def generate_environments(map):
    new_maps = []
    iter = product(*[map[k] for k in map])
    inds = [k for k in map]
    for item in iter:
        new_maps.append({inds[i]:item[i] for i in range(len(inds))})
        
    return new_maps
        
        
# Represents one clause of an axiom: S(x_1...x_n) comp T(x_1...x_n),
# where S and T are lambda terms that reduce to Terms.
# lterm and rterm must have the same arguments.
class Axiom_clause:
    def __init__(self,lterm,comp,rterm):
        if getargspec(lterm).args != getargspec(rterm).args:
            raise Exception('Bad axiom clause arguments!')
        self.lterm,self.comp,self.rterm = lterm,comp,rterm
        

        
# Represents an uninstantiated axiom.
# Clauses is a list of Axiom_clauses.
# The content of the axiom is that at least one element of clauses is true.
class Axiom:
    def __init__(self, clauses):
        for c in clauses:
            if getargspec(c.lterm).args!=getargspec(clauses[0].lterm).args:
                raise Exception('Bad axiom arguments!')
        self.clauses = clauses
        self.args = getargspec(clauses[0].lterm).args
        
        
        

# This class represents an instantiated axiom.
# Satisfied Axiom_insts cannot produce any new information and can be deleted.
# clauses is a dictionary, mapping (i,j) to a list of Comparison_datas.
# clauses represents a disjunction: at least one Comparison_data must be true.
class Axiom_inst:
    def __init__(self,clauses):
        self.clauses = clauses
        self.satisfied = False
        
    # Checks to see if any clauses can be eliminated based on info in Heuristic_data H.
    # If there is only one disjunction left in the list, sends it to be learned by H.
    def update_on_info(self,H):
        for (i,j) in self.clauses.keys():
            comps = [c for c in self.clauses[i,j] if not H.implies(i,j,comp_negate(c.comp),c.coeff)]
            if len(comps)==0:
                del self.clauses[(i,j)] #self.clauses.pop(i,j)?
                
            for comp in comps:
                if H.implies(i,j,comp.comp,comp.coeff):
                    #This disjunction is satisfied. Nothing new to be learned.
                    self.satisfied = True
                    return
        if len(self.clauses.keys())==1 and len(self.clauses[self.clauses.keys()[0]])==1:
            #There is one statement left in the disjunction. It must be true.
            i,j = self.clauses.keys()[0]
            comp = self.clauses[i,j]
            H.learn_term_comparison(i,j,comp.comp,comp.coeff,FUN)
            self.satisfied = True

# Called the first time learn_func_comparisons is run.
# Takes the function information from H, and generates a list of all possible instantiations.                    
def set_up_axioms():
    pass


    
    
    
def learn_func_comparisons(H):
            
    # Iterates through all tuples of IVars that satisfy the hypotheses of restr
    # and learns of them the conclusion of restr
    # restr is a Function_restriction
    def learn_from_function_restriction(restr):
        hyp = restr.hypotheses
        num_vars = len(getargspec(hyp).args) - 1
        num_defs = H.num_terms
        iterator = generate_tuples(num_defs, num_vars)
        conclusion = restr.conclusion
        
        for c in ifilter(lambda t: hyp(H, *t), iterator):  # c is an ordered tuple of IVars that satisfies hyp
            conclusion.learn_term_comparison(c, H)
            
    if init:
        set_up_axioms()
        
    if H.verbose:   
        print 'Learning functional facts...'
    restrictions = H.function_information
    for r in restrictions:
        if H.verbose:
            print 
            print 'From the restriction', r, 'we can learn:'
        learn_from_function_restriction(r)
    if H.verbose:
        print
