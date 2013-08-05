from classes import *
from heuristic import *
from itertools import combinations
from math import floor, ceil

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


###############################################################################
#
# MULTIPLICATIVE ELIMINATION
#
###############################################################################



#
# The next routine takes multiplicative terms t1 and t2, and another term
#   v (usually a variable), which appears t.
#
# It raises t1 to a *positive power*, and t2 to a different power so that
# the exponent of v is the same in both. It then returns t2 / t1.
#
# If t1 appears in a comparison t1 > 1 or t1 >= 1, and t2 appears in the
# equation t2 = 1, what we get is the result of using the second equation
# to eliminate v in the first.
#
# If t1 appears in a comparison t1 > 1 or t1 >= 1 in which v appears with 
# *positive* exponent, and t2 appears in a comparison t2 > 1 or t2 >= 1 in
# which v occurs with a negative exponent, the result is again a consequence
# of the two which eliminates v. 
#
# v is not assumed to appear in t1.
#
def mul_subst(t1, t2, v):

    m1 = next((m for m in t1.mulpairs if m.term == v), None)
    if m1 is None:
        return t1
    m2 = next((m for m in t2.mulpairs if m.term == v))
    exp1, exp2 = m1.exp, m2.exp
    
    # GCD will not work properly for floats.
    if isinstance(exp1, float):
        exp1 = Fraction(exp1)
    if isinstance(exp2, float):
        exp2 = Fraction(exp2)
    
    scale1 = abs(exp2 / gcd(exp1, exp2))
    scaled_t1 = pow(t1, scale1)
    scaled_t2 = pow(t2, exp1 * scale1 / exp2)
    return scaled_t1 / scaled_t2
 
def mul_elim(equations, one_comparisons, v):
    def occurs_in(v, t):
        return v in (m.term for m in t.mulpairs)

    for e in equations:
        if occurs_in(v, e):
            new_equations = [mul_subst(e2, e, v) for e2 in equations if e != e2]
            new_comparisons = [One_comparison(mul_subst(c.term, e, v), c.comp)
                               for c in one_comparisons]
            return new_equations, new_comparisons
    
    pos_comparisons = []  # v occurs with positive exponent
    neg_comparisons = []  # v occurs with negative exponent
    new_comparisons = []
    for c in one_comparisons:
        m = next((m for m in c.term.mulpairs if m.term == v), None)
        if m is None:
            new_comparisons.append(c)  # v does not occur at all
        elif m.exp > 0:
            pos_comparisons.append(c)
        else:
            neg_comparisons.append(c)
    for c1 in pos_comparisons:
        for c2 in neg_comparisons:
            if c1.comp == GE and c2.comp == GE:
                new_comp = GE
            else:
                new_comp = GT
            new_comparisons.append(One_comparison(
                    mul_subst(c1.term, c2.term, v), new_comp))
    return equations, new_comparisons




###############################################################################
#
# MULTIPLICATIVE HEURISTIC
#
###############################################################################

# The main method has a number of subroutines that depend on the heuristic H.
def learn_mul_comparisons(H):
    
    ##############################
    #
    #  IVar size info
    #
    ##############################

    def ge_one(i):
        if (0, i) in H.term_comparisons.keys():
            if [c for c in H.term_comparisons[0, i] if c.comp in [LT, LE] and
                c.coeff > 0 and c.coeff <= 1]:
                return True
        return False

    def le_one(i):
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
        if (0, i) in H.term_comparisons.keys():
            if [c for c in H.term_comparisons[0, i] if (c.comp in [GT, GE] and
                c.coeff <= -1) or (c.comp in [LE, LT] and c.coeff > 0)]:
                return True
        return False
        
    def abs_ge_one(i):
        return ge_one(i) or le_neg_one(i)
    
    def abs_le_one(i):
        return le_one(i) and ge_neg_one(i)
    
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
            
    
    #############################
    #
    # Helper function for learn_mul_comparison
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
    
    ##############################
    #
    # Main routines
    #
    ##############################


    # Takes a one_comparison of the form a_i^{e_i} * a_j^{e_j} * const >(=) 1,
    #  where a_i really represents |a_i|.
    def learn_mul_comparison(c):
        
        length = len(c.term.mulpairs)
        if length == 0:
            if c.term.const < 1: 
                H.raise_contradiction(MUL)
            return
        
        elif length == 1:
            comp, coeff = c.comp, Fraction(1, Fraction(c.term.const))
            m = c.term.mulpairs[0]
            i, j = 0, m.term.index
            exp = -m.exp
            comp, coeff = make_term_comparison_unabs(0, j, 1, exp, comp, coeff)
            
            if (H.sign(j) ** exp) * coeff < 0:
                if comp in [LE, LT]:  # 1 < neg
                    H.raise_contradiction(MUL)
                return  # 1 > neg. not useful
           
            # now have:
            #   1 comp coeff * a_j^exp 
            
            if exp < 0 and H.sign(j) * coeff > 0:
                exp, comp, coeff = -exp, comp_reverse(comp), Fraction(1, Fraction(coeff))
            elif exp < 0:  # 1 is being compared to a negative number. Comparison should not change.
                exp, coeff = -exp, Fraction(1, Fraction(coeff))
                
            coeff = round_coeff(coeff, comp)
            
            H.learn_term_comparison(0, j, comp, coeff, MUL)
            
        elif length == 2:
            m0, m1 = c.term.mulpairs[0], c.term.mulpairs[1]
            i, j = m0.term.index, m1.term.index
            e0, e1 = m0.exp, -m1.exp
            coeff = Fraction(1, Fraction(c.term.const))
            comp = c.comp
                
            # now have:
            #    |a_i|^e0 comp coeff * |a_j|^e1
            
            if coeff < 0:
                if comp in [LT, LE]:  # pos < neg
                    H.raise_contradiction(MUL)
                return  # pos > neg. not useful.
                
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
            

    ############################
    #
    # MAIN ROUTINE OF learn_mul_comparisons(H)
    #
    ############################

    if H.verbose:
        print "Learning multiplicative facts..."
        print

    # infer signs from equations
    infer_signs_from_definitions()
    infer_signs_from_learned_equalities()
    

    # make multiplicative equations (e's, where e = 1)
    mul_eqs = []
    for i in range(H.num_terms):
        if isinstance(H.name_defs[i], Mul_term):
            mul_eqs.append(H.name_defs[i] * Mul_term([Mul_pair(IVar(i), -1)]))
            
    for eq in H.zero_equations:
        if isinstance(eq, Add_term) and len(eq.addpairs) == 2:
            equation = eq.addpairs[1].term * pow(eq.addpairs[0].term, -1) * Fraction(eq.addpairs[1].coeff, -eq.addpairs[0].coeff)
            mul_eqs.append(equation)


    # collect equations where signs are all known
    # note that an equation e = 1 remains valid if each a_i is replace
    # by abs(a_i)
    # (to do: should really take absolute value of mult coefficient;
    # in the implementation so far, it is always 1)
    mul_eqs = [e for e in mul_eqs if 
               all(H.sign(m.term.index) != 0 for m in e.mulpairs)]
    
    
    if H.verbose:
        print 'Multiplicative equations:'
        for e in mul_eqs:
            print e, '= 1'
        print


    
    # make multiplicative comparisons
    # if a_i is less than zero, replace by -a_i
    # similarly for a_j
    mul_comps = []
    if H.verbose:
        print 'Multiplicative comparisons:'
    for i in [n for n in range(H.num_terms) if H.sign(n) != 0]:
        for j in [m for m in range(i + 1, H.num_terms) if H.sign(m) != 0]:
            if (i, j) in H.term_comparisons:
                for c in (p for p in H.term_comparisons[i, j] if p.provenance!=MUL): 
                    if H.verbose:
                        print c.to_string(IVar(i), IVar(j))
                    comp1, C1 = make_term_comparison_abs(i, j, c.comp, c.coeff)
                    onecomp = one_comparison_from_term_comparison(i, j, comp1, C1)
                    if onecomp:
                        mul_comps.append(onecomp)
                        


    if H.verbose:
        print

    for i in range(0, H.num_terms):
        # get all comparisons with i
        i_mul_eqs = mul_eqs
        i_mul_comps = mul_comps
        for j in range(i + 1, H.num_terms):
            # get all comparisons with i and j
            ij_mul_eqs = i_mul_eqs
            ij_mul_comps = i_mul_comps
            for k in range(j + 1, H.num_terms):
                ij_mul_eqs, ij_mul_comps = (
                    mul_elim(ij_mul_eqs, ij_mul_comps, IVar(k)))
            # add any new information
            for c in ij_mul_comps:
                learn_mul_comparison(c)
            # eliminate j
            i_mul_eqs, i_mul_comps = mul_elim(i_mul_eqs, i_mul_comps, IVar(j))
        mul_eqs, mul_comps = mul_elim(mul_eqs, mul_comps, IVar(i))

    if H.verbose:
        print
        
        
