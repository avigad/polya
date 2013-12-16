from classes import *
from heuristic import *
from itertools import product, ifilter
from inspect import getargspec
from copy import copy
#from scipy.linalg import lu
#from numpy import array
import sympy



init = True
instantiated_axioms = []

from fractions import Fraction
def add_list(l1,l2):
    return [l1[i]+l2[i] for i in range(len(l1))]

def scale_list(c,l):
    return [c*li for li in l]


def elim_var(i,pivot,rows):
    if pivot[i]==0:
        raise Exception
    new_rows = [add_list(r, scale_list(-Fraction(r[i],pivot[i]),pivot)) for r in rows]
    return new_rows



# Returns all possible Axiom_insts from this axiom scheme and heuristic H.
# TODO: handle equalities correctly
# TODO: learn if len=1
def instantiate(axiom,H):
    
    # Replaces all instances of uvar in preterm with coeff*IVar(iind)
    # Returns a new Term, and a flag True/False representing whether all
    # UVars have been replaced.
    def substitute(preterm, uvar, coeff, iind):
        return reduce(preterm, Environment({uvar.index:(coeff,iind)}))
        
    # Replaces all UVars in preterm that are assigned by env with their designated values.
    # Returns a new Term, and a flag True/False representing whether all
    # UVars have been replaced.
    def reduce(preterm,env):
        #print '   REDUCING'
        #print '   preterm:',preterm
        #print '   env:',env
        if isinstance(preterm, IVar):
            return (preterm, True)
            
        elif isinstance(preterm, UVar):
            if preterm.index in env.keys():
                (c,j) = env.val(preterm.index)
                #print '   returning',(c * IVar(j), True)
                return (c * IVar(j), True)
            else:
                #print '   returning', (preterm,False)
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
                nargs.append(Add_pair(a.coeff, s))
                flag = flag and flag2
            return (Func_term(preterm.name, nargs, preterm.const), flag)
    
    # u is a preterm such that all variable occurences are IVars
    # returns (c, i) such that u = c*a_i, or raises No_Term_Exception
    # TODO: linear arithmetic for add/mul matching
    def find_problem_term(u):
        if isinstance(u, IVar):
            return (1, u.index)
        
        
        elif isinstance(u, Func_term):
            nargs = [(lambda x,y:(x[0]*y,x[1]))(find_problem_term(p.term),p.coeff) for p in u.args]
            for i in [i for i in range(H.num_terms) if 
              (isinstance(H.name_defs[i],Func_term) 
              and H.name_defs[i].name == u.name
              and len(H.name_defs[i].args)==len(nargs))]:
                t = H.name_defs[i]
                good = True
                for k in range(len(t.args)):
                    targ, uarg = (t.args[k].coeff, t.args[k].term.index), nargs[k]
                    if not (targ[0]==uarg[0] and targ[1]==uarg[1]):
                        eqs = H.get_equivalences(targ[1])
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
            if len(u.addpairs)==1:
                return (u.addpairs[0].coeff,u.addpairs[0].term.index)
            
            npairs = [(lambda x,y:(x[0]*y,x[1]))(find_problem_term(p.term),p.coeff) for p in u.addpairs]

            #print '*** we have an add_term. u:',u
            # make a matrix out of u and all additive equalities/definitions and try to diagonalize it.
            urow = [0]*(H.num_terms)+[-1]
            for (c,i) in npairs:
                urow[i]=c

            mat = []
            for (i,j,c) in H.get_all_equivalences():
                row = [0]*(H.num_terms+1)
                row[i]=-1
                row[j]=c
                mat.append(row[:])

            for i in (i for i in range(H.num_terms) if isinstance(H.name_defs[i],Add_term)):
                row = [0]*(H.num_terms+1)
                row[i]=-1
                for p in H.name_defs[i].addpairs:
                    row[p.term.index]=p.coeff
                mat.append(row[:])

            mat.append(urow)

            #begin FM elimination
            rows_i = copy(mat)
            for i in range(H.num_terms): #check if u = c*i
                rows_j = copy(rows_i)
                for j in range(i+1,H.num_terms):
                    try:
                        r = next(r for r in rows_j if r[j]!=0 and r[-1]==0)
                    except StopIteration:
                        continue
                    rows = elim_var(j,r,[row for row in rows_j if row is not r])

                row = next(r for r in rows_j if r[-1]!=0)
                l = len([k for k in row if k!=0])
                if l==1:
                    #we have u = 0. What to do?
                    return (1,zero)
                elif l==2:
                    #we've found a match for u
                    ind = next(k for k in row if k!=0)
                    coeff = -Fraction(row[ind],row[-1])
                    return (coeff, ind)
                else:
                    try:
                        r = next(r for r in rows_i if r[i]!=0 and r[-1]==0)
                        rows_i = elim_var(i,r,[row for row in rows_i if row is not r])
                    except StopIteration:
                        if rows_i[-1][i]!=0: #there is a t_i in u, and nowhere else. Can't elim.
                            raise No_Term_Exception

            raise No_Term_Exception


            #try:
            #    p,l,d,ut = m.LUdecompositionFF()
            #    print 'matrix was:'
            #    print ut
            #    r = next(i for i in range(ut.shape[0]) if ut.row(i)[-1]!=0) #find the row in ut with nonzero u coeff
            #    nzs = [k for k in range(len(ut.row(r))) if ut.row(r)[k]!=0]
            #    if len(nzs)!=2:
            #        print 'no matrix match found'
            #        #print ut
            #        raise No_Term_Exception
            #
            #    else:
            #        #u is equal to something times a_nzs[0]
            #        cfa, cfu = ut.row(r)[nzs[0]], ut.row(r)[nzs[1]]
            #        cf = -Fraction(cfa,cfu)
            #        print 'found solution to matrix: u = ',cf,'* a',nzs[0]
            #        return (cf,nzs[0])
            #
            #except Exception as e:
            #    print 'Got an exception in matrix search:',e
            #    raise No_Term_Exception


            #pl, solved = lu(array(mat),permute_l=True)
            ##print 'solved:'
            ##print solved
            #nurow = solved[-1]
            #if nurow[-1]==0 or len([i for i in nurow if i!=0])!=2:
            #    #print 'didnt solve the mat!'
            #    raise No_Term_Exception
            #else:
            #    #print 'solved the mat!'
            #    k = next(i for i in range(len(nurow)) if nurow[i]!=0)
            #    c = nurow[k]
            #    #we have u = c*a_k
            #    return (c,k)
            #
                
            
            #temporary
            
                
#             npairs = [(lambda x,y:(x[0]*y,x[1]))(find_problem_term(p.term),p.coeff) for p in u.addpairs]
#             t = npairs[0][0]*IVar(npairs[0][1])
#             for p in npairs[1:]:
#                 t+=p[0]*IVar(p[1])
#                 
#             for i in range(H.num_terms):
#                 if str(u)==str(H.name_defs[i]) or str(t)==str(H.name_defs[i]):
#                     return (1, i) 
#             raise No_Term_Exception
        
        elif isinstance(u, Mul_term):
            #temporary- copy above
            npairs = [(lambda x,y:(x[0]*y,x[1]))(find_problem_term(p.term),p.coeff) for p in u.mulpairs]
            t = npairs[0][0]*IVar(npairs[0][1])
            for p in npairs[1:]:
                t+=p[0]*IVar(p[1])
                
            for i in range(len(H.num_terms)):
                if str(u)==str(H.name_defs[i]) or str(p)==str(H.name_defs[i]):
                    return (1, i) 
            raise No_Term_Exception
        
        else:
            print 'something weird in fpt:', u, 'should not have uvars'
            raise No_Term_Exception
            
    # Takes preterms u1...un involving uvars v1...vm
    # arg_uvars is a subset of uvars representing those that occur as arguments
    # to a Func_term in preterms.
    # Returns a list of assignments {vi <- ci*t_{ji}} such that
    # each ui becomes equal to a problem term.
    def unify(preterms, uvars, arg_uvars,envs=[Environment()]):
        
        print 'UNIFYING:'
        print '  preterms:',preterms
        print '  uvars:',uvars
        print '  arg_uvars:',arg_uvars
        
        def occurs_as_arg(term,var):
            if not isinstance(term,Func_term):
                return False
            for a in term.args:
                if a.term == var:
                    return True
            return False
        
        ####
        
        if len(uvars) == 0:
            return envs
        
        if len(arg_uvars) == 0:
            #We are in the unfortunate position where no variables occur alone in function terms.
            #Pass for now.
            return envs
        
        v = arg_uvars[0]
        #print ''
        #print '  searching for a value for',v
        try:
            t = next(term for term in preterms if occurs_as_arg(term,v))
        except StopIteration:
            print 'error: arg_uvars not set up right.',preterms, uvars, arg_uvars
            raise Exception
        ind = next(j for j in range(len(t.args)) if t.args[j].term==v)
        c = t.args[ind].coeff
        print '  v occurs in',t
        
        prob_f_terms = [i for i in range(H.num_terms) if 
                      (isinstance(H.name_defs[i],Func_term) 
                       and len(H.name_defs[i].args)==len(t.args))]
        
        print '  the relevant problem terms are:',prob_f_terms
        
        S = [(Fraction(H.name_defs[i].args[ind].coeff,c),H.name_defs[i].args[ind].term.index) for i in prob_f_terms]
        # S is a list of pairs (coeff, j) such that c*coeff*a_j occurs as an argument
        # in a problem term.
        
        #print '  S is:',S
        
        nenvs = []
        for (coeff, j) in S:
            print '  envs is:',envs
            print '  assign',v,'to be',coeff,'*',IVar(j)
            print '  preterms is:',preterms
            new_preterms = [substitute(p, v, coeff, j) for p in preterms]
            print '  new_preterms:', new_preterms
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
            print '  okay, everything has matches!'
            cenvs = deepcopy(envs)
            #print '  cenvs:',cenvs,'envs:',envs
            for c in cenvs:
                c.assign(v.index,(coeff,j))
            maps = unify(open_terms, [v0 for v0 in uvars if v0!=v], arg_uvars[1:],cenvs)
            #print '  maps:',maps
            #print '  nenvs was:',nenvs
            nenvs.extend(maps)
            #print '  nenvs is now:',nenvs
            #print '  now, envs:',envs
            # add v <- coeff*a_j to map and return that
        #print '  we have found environments:',envs
        #print '  ___'
        return nenvs
        
    #takes a preterm
    #returns set of function terms that occur as subterms
    def find_func_subterms(preterm):
        f_subterms = set()
        if isinstance(preterm,(Var,Const)):
            return f_subterms
        elif isinstance(preterm,Add_term):
            for pair in preterm.addpairs:
                f_subterms.update(find_func_subterms(pair.term))
            return f_subterms
        elif isinstance(preterm,Mul_term):
            for pair in preterm.mulpairs:
                f_subterms.update(find_func_subterms(pair.term))
            return f_subterms
        elif isinstance(preterm,Func_term):
            f_subterms.add(preterm)
            for pair in preterm.args:
                f_subterms.update(find_func_subterms(pair.term))
            return f_subterms
    ###################################################        
    
    print 'instantiate running.'
    print 'clauses:', axiom.clauses
    preterms = set(c.lterm for c in axiom.clauses if c.lterm!=zero).union(set(c.rterm for c in axiom.clauses if c.rterm!=zero))
    #print 'preterms:',preterms
    func_subterms = set()
    for pt in preterms:
        func_subterms.update(find_func_subterms(pt))
    preterms.update(func_subterms)
    envs = unify(preterms, list(axiom.vars), list(axiom.arg_vars))
    #print 'envs:',envs
    axiom_insts = []
    for env in envs:
        print 'env:',env
        nclauses = {}
        for c in axiom.clauses:
            comp,coeff = c.comp,c.coeff
            try:
                # H.num_terms + 1 is code for 0, since this is handled differently.
                lterm = (find_problem_term(reduce(c.lterm,env)[0]) if c.lterm!=zero else (0,H.num_terms+1))
                rterm = (find_problem_term(reduce(c.rterm,env)[0]) if c.rterm!=zero else (0,H.num_terms+1))
            except No_Term_Exception: #this shouldn't happen
                #print 'problem!'
                continue
            
            if lterm[0]==rterm[0]==0:
                pass
            else:
                
                rterm=(coeff*rterm[0],rterm[1])
                if lterm[1]==rterm[1]: 
                    #handle this correctly. Not done yet.
                    continue
                if lterm[1]>rterm[1]:
                    comp,lterm,rterm = comp_reverse(comp), rterm,lterm
                cd = Comparison_data(comp,Fraction(rterm[0],lterm[0]))
                if rterm[1]==H.num_terms+1:
                    rterm = (rterm[0],0)
                #print 'cd=',cd
                nclauses[lterm[1],rterm[1]] = nclauses.get((lterm[1],rterm[1]),set()).union(set([cd]))
        if len(nclauses)==1 and len(nclauses[nclauses.keys()[0]])==1:
            #learn the info here. Not done yet
            i,j = nclauses.keys()[0]
            clause = list(nclauses[i,j])[0]
            H.learn_term_comparison(i,j,clause.comp,clause.coeff,FUN)
        
        elif len(nclauses)>0:
            axiom_insts.append(Axiom_inst(nclauses,str(axiom)))
    
    #print 'instantiate returning:',axiom_insts
    return axiom_insts

# Called the first time learn_func_comparisons is run.
# Takes a list of Axioms from H, and generates a list of all possible instantiations.                    
def set_up_axioms(H):
    axioms = H.axioms
    for a in axioms:
        instantiated_axioms.extend(instantiate(a,H))
    init = False


    
    
    
def learn_func_comparisons(H):
    if H.verbose:   
        print 'Learning functional facts...'            
            
    if init:
        set_up_axioms(H)
        
    if H.verbose:   
        print 'Instantiated axioms:',instantiated_axioms
        
    #H.info_dump()
    new_info = H.get_changes(FUN)
        
    for inst in [ax for ax in instantiated_axioms if not ax.satisfied]:
        inst.update_on_info(H,new_info)
        
    if H.verbose:
        print
        
