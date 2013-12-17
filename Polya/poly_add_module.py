from classes import *
#from heuristic import *
import lrs_polyhedron_util as lrs_util
  

           
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


#The main routine
# - get vertices of polyhedron
# - for each xy-pair, find the extreme bounds in the xy-plane if they exist.
# - learn these inequalities
def learn_add_comparisons(H):
    
    #Sends a potentially new term comparison to the heuristic
    def learn_term_comparison(i,j,comp,coeff):
        if coeff == None:
            return
        if coeff == 0:
            H.learn_zero_comparison(i,comp,ADD)
        else:
            H.learn_term_comparison(i,j,comp,coeff,ADD)
            
            
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
    
    #Convert to V-representation
    
    #t = default_timer()
    #vertices = cdd.Polyhedron(matrix).get_generators()
    zero_comparisons = []
    for (i,j) in H.term_comparisons.keys():
        for c in (c for c in H.term_comparisons[i,j] if c.provenance!=ADD):
            zero_comparisons.append(Zero_comparison(IVar(i)-c.coeff*IVar(j),c.comp))
    for i in H.zero_comparisons.keys():
        if H.zero_comparisons[i].provenance!=ADD:
            zero_comparisons.append(Zero_comparison(IVar(i),H.zero_comparisons[i].comp))

    #H.info_dump()
            
    term_comps,zero_comps = lrs_util.get_comparison_list(add_eqs,zero_comparisons,H.num_terms,H.verbose)

    
    for (i,j,comp,coeff) in term_comps:
        learn_term_comparison(i,j,comp,coeff)
        
    for (i,comp) in zero_comps:
        learn_term_comparison(i,i,comp,0)