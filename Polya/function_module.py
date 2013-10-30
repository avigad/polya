from classes import *
from heuristic import *
from itertools import product, ifilter
from inspect import getargspec
from copy import copy

init = True
instantiated_axioms = []

# Replaces all instances of uvar in preterm with coeff*IVar(iind)
# Returns a new Term, and a flag True/False representing whether all
# UVars have been replaced.
def substitute(preterm, uvar, coeff, iind):
    return reduce(preterm, Environment({uvar:(coeff,iind)}))
    
# Replaces all UVars in preterm that are assigned by env with their designated values.
# Returns a new Term, and a flag True/False representing whether all
# UVars have been replaced.
def reduce(preterm,env):
    if isinstance(preterm, IVar):
        return (preterm, True)
        
    elif isinstance(preterm, UVar):
        if preterm.index in env:
            (c,j) = env[preterm.index]
            return (c * IVar(j), True)
        else:
            return (preterm, False)
    
    elif isinstance(preterm, Add_term):
        s, flag = reduce(preterm.addpairs[0].term, env)
        t = preterm.addpairs[0].coeff * s
        for ap in preterm.addpairs[1:]:
            s, flag2 = reduce(ap.term,env)
            flag = flag and flag2
            t += ap.coeff * s
        return (t, flag)
    
    elif isinstance(preterm, Mul_term):
        s, flag = reduce(preterm.mulpairs[0].term,env)
        t = s**preterm.mulpairs[0].exp
        for mp in preterm.mulpairs[1:]:
            s, flag2 = reduce(mp.term,env)
            flag = flag and flag2
            t *= s**mp.exp
        return (t, flag)
    
    elif isinstance(preterm, Func_term):
        flag = True
        nargs = []
        for a in preterm.args:
            s, flag2 = reduce(a.term,env)
            nargs.append((a.coeff, s))
            flag = flag and flag2
        return (Func_term(preterm.name, nargs, preterm.const), flag)
    

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
    
    ####
    
    if len(uvars) == 0:
        return [Environment()]
    
    if len(arg_uvars) == 0:
        #We are in the unfortunate position where no variables occur alone in function terms.
        #Pass for now.
        return [Environment()]
    
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
    
    envs = []
    
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
        
        #Right now, we do nothing with prob_terms
        
        maps = unify(H, open_terms, [v0 for v0 in uvars if v0!=v], arg_uvars[1:])
        for map in maps:
            map.assign(v,(coeff,j))
        envs.extend(maps)
        # add v <- coeff*a_j to map and return that
    return envs
        
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
        
        
# Represents one clause of an axiom: S(v_1...v_n) comp T(v_1...v_n),
# where S and T are Terms.
class Axiom_clause:
    def __init__(self,lterm,comp,coeff, rterm):
        self.lterm,self.comp,self.coeff,self.rterm = lterm,comp,coeff,rterm
        

        
# Represents an uninstantiated axiom.
# Clauses is a list of Axiom_clauses.
# The content of the axiom is that at least one element of clauses is true.
class Axiom:
    def __init__(self, clauses):
        
        #takes a term
        #returns two Sets. The first is all uvars that occur in the term.
        #The second is all uvars that occur alone as function arguments in the term.
        def find_uvars(term):
            if isinstance(term, UVar):
                return set([term]),set()
            elif isinstance(term, Var):
                return set(),set()
            else:
                vars = set()
                arg_vars = set()
                if isinstance(term, Add_term):
                    pairs = term.addpairs
                elif isinstance(term, Mul_term):
                    pairs = term.mulpairs
                elif isinstance(term, Func_term):
                    pairs = term.args
                    arg_vars = Set([p.term for p in pairs if isinstance(p.term, UVar)])
                for p in pairs:
                    nvars, narg_vars = find_uvars(p.term)
                    vars.update(nvars)
                    arg_vars.update(narg_vars)
                    
                return vars, arg_vars

        self.clauses = clauses
        uvars = set()
        arg_uvars = set()
        for c in clauses:
            nvars, narg_vars = find_uvars(c.lterm)
            uvars.update(nvars)
            arg_uvars.update(narg_vars)
            nvars, narg_vars = find_uvars(c.rterm)
            uvars.update(nvars)
            arg_uvars.update(narg_vars)
        
        self.vars, self.arg_vars = uvars, arg_uvars
        
    # Returns all possible Axiom_insts from this axiom scheme and heuristic H.
    # TODO: handle equalities correctly
    # TODO: learn if len=1
    def instantiate(self,H):
        preterms = Set(c.lterm for c in self.clauses).union(Set(c.rterm for c in self.clauses))
        envs = unify(H, preterms, self.uvars, self.arg_vars)
        axiom_insts = []
        for env in envs:
            nclauses = {}
            for c in self.clauses:
                comp,coeff = c.comp,c.coeff
                lterm = find_problem_term(H,reduce(c.lterm,env)[0])
                rterm = find_problem_term(H,reduce(c.rterm,env)[0])
                rterm[0]*=coeff
                if lterm[1]==rterm[1]: 
                    #handle this correctly. Not done yet.
                    pass
                if lterm[1]>rterm[1]:
                    comp,lterm,rterm = comp_reverse(comp), rterm,lterm
                nclauses[lterm[1],rterm[1]] = nclauses.get((lterm[1],rterm[1]),set()).add(Comparison_data(comp,Fraction(rterm[0],lterm[0])))
            if len(nclauses)==1 and len(nclauses[nclauses.keys()[0]])==1:
                #learn the info here. Not done yet
                pass
            
            elif len(nclauses)>0:
                axiom_insts.append(Axiom_inst(nclauses))
        
        return axiom_insts
                
        

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
# Takes a list of Axioms from H, and generates a list of all possible instantiations.                    
def set_up_axioms(H):
    axioms = H.axioms
    for a in axioms:
        instantiated_axioms.extend(a.instantiate(H))
    init = False


    
    
    
def learn_func_comparisons(H):
            
            
    if init:
        instantiated_axioms = set_up_axioms(H)
        
    if H.verbose:   
        print 'Learning functional facts...'
        
    for inst in instantiated_axioms:
        inst.update_on_info(H)
        
    if H.verbose:
        print
