from classes import *
from itertools import combinations
import primes
import lrs_polyhedron_util as lrs_util
import cdd
import operator
from math import floor,ceil
from copy import deepcopy

###############################################################################
#
# FRACTION ROUNDING
#
###############################################################################


# These are used for rounding square roots properly.
# Take fractions,  return fractions
precision = 100000
def round_down(f):
    if f.denominator > precision:
        return Fraction(int(floor(float(f.numerator * precision) / f.denominator)), precision)
    else:
        return f

def round_up(f):
    if f.denominator > precision:
        return Fraction(int(ceil(float(f.numerator * precision) / f.denominator)), precision)
    else:
        return f
    
# If we have x comp coeff * y, then we also have x comp round_coeff * y    
def round_coeff(coeff, comp):
    if comp in [LE, LT]:
        return round_up(Fraction(coeff))
    else:
        return round_down(Fraction(coeff))

def learn_mul_comparisons_poly(H):
    
    ##############################
    #
    #  IVar size info
    #
    ##############################

    def ge_one(i):
        if i==0: return True
        if (0, i) in H.term_comparisons.keys():
            if [c for c in H.term_comparisons[0, i] if c.comp in [LT, LE] and
                c.coeff > 0 and c.coeff <= 1]:
                return True
        return False

    def le_one(i):
        if i==0: return True
        if (0, i) in H.term_comparisons.keys():
            if [c for c in H.term_comparisons[0, i] if (c.comp in [GT, GE] and
                c.coeff >= 1) or (c.comp in [LT, LE] and c.coeff < 0)]:
                return True
        return False
    
    def le_neg_one(i):
        if (0, i) in H.term_comparisons.keys():
            if [c for c in H.term_comparisons[0, i] if c.comp in [LT, LE] and
                c.coeff < 0 and c.coeff >= -1]:
                return True
        return False
        
    def ge_neg_one(i):
        if i==0: return True
        if (0, i) in H.term_comparisons.keys():
            if [c for c in H.term_comparisons[0, i] if (c.comp in [GT, GE] and
                c.coeff <= -1) or (c.comp in [LE, LT] and c.coeff > 0)]:
                return True
        return False
        
    def abs_ge_one(i):
        return ge_one(i) or le_neg_one(i)
    
    def abs_le_one(i):
        return le_one(i) and ge_neg_one(i)
    
    #############################
    #
    # Processing learned comparisons
    #
    #############################
    
    # Takes comparison of the form |a_i|^{e0} comp coeff * |a_j|^{e1}
    # Assumes coeff > 0
    # Assumes that setting e1=e0 preserves the truth of the inequality.
    # Takes e0th root of each side and learns the comparison
    def take_roots_and_learn(i, j, e0, e1, comp, coeff):
        if e0 < 0:
            comp = comp_reverse(comp)
        e0, e1, coeff = 1, 1, coeff ** Fraction(1, Fraction(e0))
        coeff = round_coeff(coeff, comp)
        comp, coeff = make_term_comparison_unabs(i, j, 1, 1, comp, coeff)
        H.learn_term_comparison(i, j, comp, coeff, MUL)
    


    # Takes a one_comparison of the form a_i^{e_i} * a_j^{e_j} * const >(=) 1,
    #  where a_i really represents |a_i|.

    def learn_mul_comparison(i,j,comp,coeff,e0,e1):
        if j<i:
            i,j,e0,e1 = j,i,e1,e0    
        coeff = 1/Fraction(coeff)
        if coeff<0:
            comp = comp_reverse(comp)
            
        e1 = -e1
        
        if coeff < 0:
            if comp in [LT, LE]:  # pos < neg
                H.raise_contradiction(MUL)
            return  # pos > neg. not useful.
        
        if i==0: #a_i = 1, so we can set e0 to whatever we want.
            e0 = e1
            
        # Otherwise, both sides of the inequality are positive
        # a_i and a_j are still abs values, coeff is positive
        
        if e0 == e1:  # we have |a_i|^p comp coeff * |a_j|^p
            take_roots_and_learn(i, j, e0, e1, comp, coeff)
            
        elif e0 < e1 and comp in [LE, LT] and abs_le_one(j):
            # making e1 smaller makes rhs bigger, which doesn't mess up comparison.
            # so pretend e1=e0 and take e0th root
            take_roots_and_learn(i, j, e0, e1, comp, coeff)
            
        elif e0 > e1 and comp in [GE, GT] and abs_le_one(j):
            # making e1 bigger makes rhs smaller, which doesn't mess up comparison.
            # so pretend e1 = e0 and take e0th root
            take_roots_and_learn(i, j, e0, e1, comp, coeff)
            
        elif e0 < e1 and comp in [GE, GT] and abs_ge_one(j):
            # making e1 smaller makes RHS smaller, which doesn't mess up comparison.
            take_roots_and_learn(i, j, e0, e1, comp, coeff)
            
        elif e0 > e1 and comp in [LE, LT] and abs_ge_one(j):
            # making e1 bigger makes RHS bigger, which doesn't mess up comparison.
            take_roots_and_learn(i, j, e0, e1, comp, coeff)
    

                
    ###################################
    #
    # Sign inference helper functions
    #
    ###################################
    
    def ivar_zero_comparison(i):
        if i in H.zero_comparisons.keys():
            return H.zero_comparisons[i].comp
        return None
    
    def mulpair_zero_comparison(m):
        if m.term.index in H.zero_comparisons.keys():
            comp = H.zero_comparisons[m.term.index].comp
            if m.exp % 2 == 0 or (isinstance(m.exp, Fraction) and m.exp.numerator % 2 == 0):
                if comp in [GT, LT]:
                    return GT
                else:
                    return GE
            else:
                return comp
        elif m.exp % 2 == 0:
            return GE
        else:
            return None

    def prod_zero_comparisons(comps):
        if None in comps:
            return None
        else:
            notstrict = LE in comps or GE in comps
            if len([m for m in comps if m in [LT, LE]]) % 2 == 0:
                if not notstrict: 
                    return GT
                else:
                    return GE
            else:
                if not notstrict:
                    return LT
                else:
                    return LE

    def sign_pow(s, n):
        if s == 1 or (s == -1 and n % 2 == 0):
            return 1
        elif s == -1:
            return -1
        else:
            raise Error("sign should be 1 or -1")


    def multerm_zero_comparison(t):
        comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
        return prod_zero_comparisons(comps)
    
                
    def infer_signs_from_learned_equalities():
        for t in (d for d in H.zero_equations if isinstance(d, Mul_term)):
            # we have t=0.
            comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
            
            # If there are more than two unknowns, we can't do anything.
            if comps.count(None) > 1:
                return
            
            # If there is one unknown and every other is strict, that unknown must be equal to 0.
            if comps.count(None) == 1 and comps.count(LE) + comps.count(GE) == 0:
                index = comps.index(None)
                i = t.mulpairs[index].term.index
                H.learn_zero_equality(i, MUL)
            
            elif comps.count(None) == 0:
                ges, les = comps.count(GE), comps.count(LE)
                # If there are no unknowns and only one is weak, that weak one must be equal to 0.
                if ges == 1 and les == 0:
                    index = comps.index(GE)
                    H.learn_zero_equality(t.mulpairs[index].term.index, MUL)
                elif les == 1 and ges == 0:
                    index = comps.index(LE)
                    H.learn_zero_equality(t.mulpairs[index].term.index, MUL)
                    
                # If there are no weak inequalities, we have a contradiction.
                elif ges == 0 and les == 0:
                    H.raise_contradiction(MUL)    
                    
    
    # This method looks at term definitions and tries to infer signs of subterms.
    # For instance, if a_i = a_j * a_k, a_i > 0, a_j < 0, then it will learn a_k < 0.
    # Provenance is HYP, so this info is available to mul routine
    def infer_signs_from_definitions():
        for i in (j for j in range(H.num_terms) if isinstance(H.name_defs[j], Mul_term)):
            t = H.name_defs[i]
            # have the equation a_i = t.
            leftsign = ivar_zero_comparison(i)
            comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
            rightsign = prod_zero_comparisons(comps)
            
            if ((leftsign in [GE, GT] and rightsign == LT) or (leftsign in [LT, LE] and rightsign == GT)
                or (leftsign == GT and rightsign in [LE, LT]) or (leftsign == LT and rightsign in [GE, GT])):
                H.raise_contradiction(MUL)
                
            if leftsign in [GT, LT]:  # strict info on left implies strict info for all on right.
                for j in range(len(comps)):
                    if comps[j] in [GE, LE]:
                        newcomp = (GT if comps[j] == GE else LT)
                        H.learn_zero_comparison(t.mulpairs[j].term.index, newcomp, HYP)
                        
            elif rightsign in [GT, LT] and leftsign not in [GT, LT]:  # strict info on right implies strict info on left
                H.learn_zero_comparison(i, rightsign, HYP)
                
            elif (rightsign == GE and leftsign == LE) or (rightsign == LE and leftsign == GE):  # we have zero equality.
                H.learn_zero_equality(i, MUL)
                if comps.count(GE) == 1 and comps.count(LE) == 0:
                    index = comps.index(GE)
                    H.learn_zero_equality(t.mulpairs[index].term.index, HYP)
                elif comps.count(LE) == 1 and comps.count(GE) == 0:
                    index = comps.index(LE)
                    H.learn_zero_equality(t.mulpairs[index].term.index, HYP)

            # Reset these with potentially new info
            leftsign = ivar_zero_comparison(i)
            comps = [mulpair_zero_comparison(m) for m in t.mulpairs]
            rightsign = prod_zero_comparisons(comps)
            
            # Two possibilities here.
            # Case 1: lhs is strong, rhs is missing one. All others on rhs must be strong by above. Missing one must be strong too, and we can figure out what it is.
            # Case 2: lhs is weak, rhs is missing one, all others on rhs are strong. Missing one must be weak.
            if rightsign == None and comps.count(None) == 1 and (leftsign in [GT, LT] or (leftsign in [GE, LE] and comps.count(GE) + comps.count(LE) == 0)):
                index = comps.index(None)
                m = t.mulpairs[index]
                comps.pop(index)
                comps.append(leftsign)
                new_comp = prod_zero_comparisons(comps)
                index2 = m.term.index
                H.learn_zero_comparison(index2, new_comp, HYP)

    ################################################
    #
    # Handle absolute values for elimination routine
    #
    #################################################
    
    # this first routine takes i, j, comp, C representing
    #    ai comp C aj
    # and returns a new pair comp', C', so that
    #    abs(ai) comp' C' abs(aj)
    # is equivalent to the original comparison.
    # assume signs are nonzero
    
    def make_term_comparison_abs(i, j, comp, C):
        C1 = C * H.sign(i) * H.sign(j)
        if H.sign(i) == 1:
            comp1 = comp
        else: 
            comp1 = comp_reverse(comp)
        return comp1, C1
        
    # this routine takes i, j, ei, ej, comp1, C1 representing
    #    |ai|^{ei} comp1 C1 |aj|^{ej}
    # and returns a new pair comp, C, so that
    #    ai^{ei} comp C aj^{aj}
    # is equivalent to the original comparison.
    # assume signs are nonzero
    
    def make_term_comparison_unabs(i, j, ei, ej, comp1, C1):
        correction = (H.sign(i) ** ei) * (H.sign(j) ** ej)
        correction = 1 if correction > 0 else -1  # Make correction an int instead of a float
        C = C1 * correction
        if H.sign(i) ** ei == 1:
            comp = comp1
        else:
            comp = comp_reverse(comp1)
        return comp, C
    
    # Assumes ai, aj > 0 and j is not 0
    def one_comparison_from_term_comparison(i, j, comp, C):
        if C <= 0: 
            if comp in [LE, LT]:  # pos < neg. contradiction
                H.raise_contradiction(MUL)
            else:  # pos > neg. useless
                return None
            
        if comp == GT or comp == GE:
            new_comp = comp
            if i == 0:
                t = Mul_term([(IVar(j), -1)], Fraction(1, C))
            else:
                t = Mul_term([(IVar(i), 1), (IVar(j), -1)], Fraction(1, C))
        else:
            new_comp = comp_reverse(comp)
            if i == 0:
                t = Mul_term([(IVar(j), 1)], C)
            else:
                t = Mul_term([(IVar(i), -1), (IVar(j), 1)], C)
        return One_comparison(t, new_comp)
    
    ########################
    #
    # MAIN ROUTINE
    #
    #######################
    
    if H.verbose:
        print 'Learning multiplicative facts (polyhedron style...)'
        print
    
    infer_signs_from_definitions()
    infer_signs_from_learned_equalities()
    
    
    mul_eqs = [H.name_defs[i]*IVar(i)**(-1) for i in range(H.num_terms) if
            (isinstance(H.name_defs[i],Mul_term) and
              all(H.sign(p.term.index)!=0 for p in H.name_defs[i].mulpairs))]
    
    if H.verbose:
        print 'Multiplicative equations:'
        for e in mul_eqs:
            print e,'= 1'
        print
        
    mul_comps = []
    for (i,j) in H.term_comparisons.keys():
        if H.sign(i)!=0 and H.sign(j)!=0:
            for c in (c for c in H.term_comparisons[i,j] if c.provenance!=MUL):
                comp1, C1 = make_term_comparison_abs(i, j, c.comp, c.coeff)
                onecomp = one_comparison_from_term_comparison(i, j, comp1, C1)
                if onecomp:
                    mul_comps.append(onecomp)
                    
    if H.verbose:
        print 'Multiplicative comparisons:'
        print '(Note: here, a_i represents |a_i|)'
        for c in mul_comps:
            print c.term,comp_str[c.comp],'1'
        print

    
    #mul_eqs is a list of terms that are equal to 1
    #mul_cops is a list of one_comparisons.
    #turn these into zero_comps by taking logs,
    #and store this info in a matrix to pass to lrs.
    
    #Maps a prime number to the index of its ivar
    index_of_prime = {}
    class ind_store:
        i = H.num_terms
    
    #Inverse of above
    prime_of_index = {}
    
    #p is a prime
    #returns the index of the ivar corresponding to p, or creates one
    def get_index_of(p):
        try:
            return index_of_prime[p]
        except KeyError:
            index_of_prime[p] = ind_store.i
            prime_of_index[ind_store.i] = p
            ind_store.i+=1
            return ind_store.i-1
    
    add_eqs = []
    for e in mul_eqs:
        #take the log of each piece
        p = e.mulpairs[0]
        term = p.term*p.exp
        for p in e.mulpairs[1:]:
            term += p.term*p.exp
            
        if e.const != 1:
            if e.const < 0: #since we have taken absolute value, this should never happen
                raise Exception
            c_fract = Fraction(e.const)
            fac = primes.factorization(c_fract.numerator)
            for i in fac.keys():
                term += fac[i]*IVar(get_index_of(i))
            fac = primes.factorization(c_fract.denominator)
            for i in fac.keys():
                term -= fac[i]*IVar(get_index_of(i))
        add_eqs.append(term)
        
    add_comps = []
    for c in mul_comps:
        e = c.term
        p = e.mulpairs[0]
        term = p.term*p.exp
        for p in e.mulpairs[1:]:
            term += p.term*p.exp
            
        if e.const != 1:
            if e.const < 0:
                raise Exception
            c_fract = Fraction(e.const)
            fac = primes.factorization(c_fract.numerator)
            for i in fac.keys():
                term += fac[i]*IVar(get_index_of(i))
            fac = primes.factorization(c_fract.denominator)
            for i in fac.keys():
                term -= fac[i]*IVar(get_index_of(i))
        #print c,'became:',term
        add_comps.append(Zero_comparison(term,c.comp))
        
    plist = sorted(index_of_prime.keys())
    for i in range(len(plist)-1):
        add_comps.append(Zero_comparison(IVar(index_of_prime[plist[i+1]])-IVar(index_of_prime[plist[i]]),GT))
    
    vertices,lin_set = lrs_util.get_generators(add_eqs,add_comps,H.num_terms+len(plist))
    
    if H.verbose:
        print 'Polyhedron vertices:',['Column 1 = delta.']+['Column '+str(j+1)+' = '+str(prime_of_index[j]) for j in sorted(prime_of_index.keys())]      
        for r in vertices:
            print r[1:],('(ray)' if r[0]==0 else '(point)')
        print
        print 'Linear set:'
        print lin_set
    
    
    for (i,j) in combinations(range(H.num_terms),2):
        base_matrix = [vertices[k][:2]+[vertices[k][i+2],vertices[k][j+2]]+vertices[k][H.num_terms+2:] for k in range(len(vertices)) if k not in lin_set]
        matrix = cdd.Matrix(base_matrix,number_type = 'fraction')
        matrix.rep_type = cdd.RepType.GENERATOR
        for k in lin_set:
            matrix.extend([vertices[k][:2]+[vertices[k][i+2],vertices[k][j+2]]+vertices[k][H.num_terms+2:]],linear=True)
            
        
        ineqs = cdd.Polyhedron(matrix).get_inequalities()
        #ineqs,lin_set2 = lrs.get_inequalities(matrix) #This will have the same effect, but right now it is slower. Need to import lrs to use
        
        for c in ineqs:
            if c[2]==c[3]==0: #no comp
                continue 
                
            strong = (c[1]<0)
                
            const = 1
            #Don't want constant to a non-int power
            scale = int(reduce(operator.mul,(Fraction(c[k]).denominator for k in range(4,len(c))),1))
            if scale!=1:
                c = [c[0],c[1]]+[scale*v for v in c[2:]]
                
            skip = False
            for k in range(4,len(c)):
                if c[k]!=0:
                    if c[k]>=10000000 or c[k]<=-10000000:
                        #Not going to get much here. Causes arithmetic errors.
                        skip = True
                    else:
                        const*=(prime_of_index[k+H.num_terms-4]**c[k])

            if skip:
                continue        
  
            if c[2]==0: #const*a_j^c[3] comp 1
                learn_mul_comparison(0,j,(GT if strong else GE),const,1,c[3])
            elif c[3]==0:
                if i!=0:
                    learn_mul_comparison(0,i,(GT if strong else GE),const,1,c[2])
            else: 
                learn_mul_comparison(i,j,(GT if strong else GE),const,c[2],c[3])
    
    if H.verbose:
        print    