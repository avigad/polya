import polya.main.terms as terms
import polya.util.num_util as num_util
import fractions
import math

####################################################################################################
#
# Fraction rounding
#
####################################################################################################


precision = 10000
max_coeff = 1000000


def round_down(f):
    """
    Takes a fraction f.
    Returns the closest fractional approximation to f from below with denominator <= precision.
    """
    if f.denominator > precision:
        return fractions.Fraction((f.numerator * precision) // f.denominator, precision)
        # it is hard to tell which is faster
        # return fractions.Fraction(int(math.floor(f * precision)), precision)
    else:
        return f


def round_up(f):
    """
    Takes a fraction f.
    Returns the closest fractional approximation to f from above with denominator <= precision.
    """
    if f.denominator > precision:
        return fractions.Fraction(((f.numerator * precision) // f.denominator) + 1, precision)
        # return fractions.Fraction(int(math.ceil(f * precision)), precision)
    else:
        return f


def round_coeff(coeff, comp):
    """
    Preserves if we have x comp coeff * y, then we also have x comp round_coeff * y
    Returns a fraction.
    """
    if comp in [terms.LE, terms.LT]:
        return round_up(fractions.Fraction(coeff))
    elif comp in [terms.GE, terms.GT]:
        return round_down(fractions.Fraction(coeff))
    else:
        return coeff


def ge_one(B, i):
    if i == 0:
        return True
    return B.implies(i, terms.GE, 1, 0)


def le_one(B, i):
    if i == 0:
        return True
    return B.implies(i, terms.LE, 1, 0)


def le_neg_one(B, i):
    if i == 0:
        return False
    return B.implies(i, terms.LE, -1, 0)


def ge_neg_one(B, i):
    if i == 0:
        return True
    return B.implies(i, terms.GE, -1, 0)


def abs_ge_one(B, i):
    return ge_one(B, i) or le_neg_one(B, i)


def abs_le_one(B, i):
    return le_one(B, i) and ge_neg_one(B, i)


def reduce_mul_term(t):
    """
    Takes a MulTerm t in which variables t_j could appear multiple times: t_j^3 * t_j^-2 * t_j^-1
    Since t_j is assumed to be positive, combines these so that each t_j appears once
    """
    inds = set(a.term.index for a in t.args)
    ind_lists = [[i for i in range(len(t.args)) if t.args[i].term.index == j] for j in inds]
    rt = terms.One()
    for l in ind_lists:
        exp = sum(t.args[k].exponent for k in l)
        if exp != 0:
            rt *= t.args[l[0]].term ** exp
    if isinstance(rt, terms.One):
        return terms.IVar(0)
    return rt


def process_mul_comp(m1, m2, coeff1, comp1, B):
    """
    Returns an IVar TermComparison implied by m1 * m2 * coeff comp 1, where m1 and m2 are mulpairs.
    m1 and m2 are still absolute values
    """
    if coeff1 == 0:
        return terms.comp_eval[terms.comp_reverse(comp1)](terms.one, 0)

    i, j, ei, ej = m1.term.index, m2.term.index, m1.exponent, -m2.exponent
    if i > j:
        i, j, ei, ej = j, i, -ej, -ei
    comp = comp1 if coeff1 > 0 else terms.comp_reverse(comp1)
    coeff = 1/fractions.Fraction(coeff1)

    if coeff < 0:
        if comp in [terms.LT, terms.LE]:  # pos < neg
            return terms.one < 0
        return None  # pos > neg. not useful.

    if ei == 0:
        i, ei = 0, 1
    if ej == 0:
        j, ej = 0, 1

    # we have ti^ei comp coeff * tj^ej
    if i == 0:  # a_i = 1, so we can set ei to whatever we want.
        ei = ej

    # Otherwise, both sides of the inequality are positive
    # a_i and a_j are still abs values, coeff is positive

    if (
        (ei == ej)  # we have |a_i|^p comp coeff * |a_j|^p
        or (ei < ej and comp in [terms.LE, terms.LT] and abs_le_one(B, j))
        # making ej smaller makes rhs bigger, which doesn't mess up comparison.
        or (ei > ej and comp in [terms.GE, terms.GT] and abs_le_one(B, j))
        # making ej bigger makes rhs smaller
        or (ei < ej and comp in [terms.GE, terms.GT] and abs_ge_one(B, j))
        # making ej smaller makes RHS smaller
        or (ei > ej and comp in [terms.LE, terms.LT] and abs_ge_one(B, j))
        # making ej bigger makes RHS bigger
    ):
        # we can set ej = ei and preserve the comparison.
        if ei < 0:
            comp = terms.comp_reverse(comp)
        cexp = fractions.Fraction(1, ei)

        # take both sides to the cexp power
        p = (num_util.perfect_root(coeff, cexp) if cexp > 0
             else num_util.perfect_root(coeff, -cexp))
        if p and cexp < 0:
            p = fractions.Fraction(1, p)
        if p:
            ei, ej, coeff = 1, 1, p
        elif comp in [terms.EQ, terms.NE]:
            return terms.IVar(0) == terms.IVar(0)
        else:
            ei, ej, coeff = 1, 1, fractions.Fraction(coeff ** cexp)
        # ei, ej, coeff = 1, 1, coeff ** fractions.Fraction(1, ei)
        if coeff > max_coeff:
            if comp in [terms.GE, terms.GT]:
                coeff = max_coeff
            else:
                return terms.IVar(0) == terms.IVar(0)
        else:
            coeff = round_coeff(coeff, comp)
        comp, coeff = make_term_comparison_unabs(i, j, ei, ej, comp, coeff, B)
        if isinstance(coeff, fractions.Fraction) and coeff.denominator > precision:
            print i, terms.comp_str[comp], coeff, j
        return terms.comp_eval[comp](terms.IVar(i), coeff * terms.IVar(j))

####################################################################################################
#
# Absolute value conversions
#
####################################################################################################


def make_term_comparison_abs(c, B):
    """
    c.term1 can be term or sterm, c.term2 must be sterm
    if c is a * ti comp b * tj, returns a comparison |ti| comp p * |tj|
    B is a blackboard
    """
    if c.term2.coeff == 0:
        if isinstance(c.term1, terms.STerm):
            comp = c.comp if c.term1.coeff > 0 else terms.comp_reverse(c.comp)
            return terms.comp_eval[comp](c.term1.term, 0)
        else:
            return terms.comp_eval[c.comp](c.term1, 0)

    if isinstance(c.term1, terms.Term):
        term1, comp, coeff, term2 = c.term1, c.comp, c.term2.coeff, c.term2.term
    else:
        term1, term2 = c.term1.term, c.term2.term
        if term1.coeff < 0:
            comp = terms.comp_reverse(c.comp)
            coeff = fractions.Fraction(c.term2.coeff, c.term1.coeff)
        else:
            comp, coeff = c.comp, fractions.Fraction(c.term2.coeff, c.term1.coeff)
    i, j = term1.index, term2.index

    # we have term1 comp coeff * term2
    coeff1 = coeff * B.sign(i) * B.sign(j)
    if B.sign(i) == 1:
        return terms.comp_eval[comp](term1, coeff1 * term2)
    else:
        return terms.comp_eval[terms.comp_reverse(comp)](term1, coeff1 * term2)


def make_term_comparison_unabs(i, j, ei, ej, comp1, coeff1, B):
    """
    this routine takes i, j, ei, ej, comp1, coeff1 representing
       |ai|^{ei} comp1 coeff1 |aj|^{ej}
    and returns a new pair comp, coeff, so that
       ai^{ei} comp coeff aj^{aj}
    is equivalent to the original comparison.
    assume signs are nonzero
    """
    correction = (B.sign(i) ** ei) * (B.sign(j) ** ej)
    correction = 1 if correction > 0 else -1  # Make correction an int instead of a float
    coeff = coeff1 * correction
    if B.sign(i) ** ei == 1:
        comp = comp1
    else:
        comp = terms.comp_reverse(comp1)
    return comp, coeff

def get_multiplicative_information(B):
    """
    Retrieves the relevant information from the blackboard.
    Filters to only comparisons and equations where sign information is known, and converts to
    absolute value form.
    Note: in the returned comparisons, t_j represents |t_j|
    """

    comparisons = []
    for c in (c for c in B.get_inequalities() + B.get_equalities()
              if c.term2.coeff != 0):
        ind1 = c.term1.index
        ind2 = c.term2.term.index
        if B.sign(ind1) != 0 and B.sign(ind2) != 0:
            comparisons.append(make_term_comparison_abs(c, B))

    for key in B.term_defs:
        if (isinstance(B.term_defs[key], terms.MulTerm) and B.sign(key) != 0 and
                all(B.sign(p.term.index) != 0 for p in B.term_defs[key].args)):
            comparisons.append(
                terms.TermComparison(reduce_mul_term(B.term_defs[key]), terms.EQ, terms.IVar(key))
            )

    return comparisons

####################################################################################################
#
# Sign info functions
#
####################################################################################################

class Sign:
    def __init__(self, dir, strong):
        self.dir, self.strong = dir, strong

    def __mul__(self, other):
        if other is 0:
            return 0
        return Sign(self.dir * other.dir, self.strong and other.strong)

    def __rmul__(self, other):
        return self*other

    def __hash__(self):
        return hash((self.dir, self.strong))

    def __repr__(self):
        return "dir: {0!s}, strong: {1!s}".format(self.dir, self.strong)


LE, LT, GE, GT = Sign(-1, False), Sign(-1, True), Sign(1, False), Sign(1, True)
comp_to_sign = {terms.LE: LE, terms.LT: LT, terms.GE: GE, terms.GT: GT}
sign_to_comp = {(-1, False): terms.LE, (-1, True): terms.LT, (1, False): terms.GE,
                (1, True): terms.GT}


def derive_info_from_definitions(B):
    def mulpair_sign(p):
        if p.exponent % 2 == 0:
            return GT if B.implies(p.term.index, terms.NE, 0, 0) else GE
            # return 1 if B.sign(p.term.index) != 0 else 0
        else:
            s = B.zero_inequalities.get(p.term.index, None)
            return comp_to_sign[s] if s is not None else 0
            # return B.sign(p.term.index)

    # def weak_mulpair_sign(p):
    #     if p.exponent % 2 == 0:
    #         return 1
    #     else:
    #         return B.weak_sign(p.term.index)


    for key in (k for k in B.term_defs if isinstance(B.term_defs[k], terms.MulTerm)):
        #signs = [mulpair_sign(p) for p in B.term_defs[key].args]
        #s = reduce(lambda x, y: x*y, signs)

        if any((B.implies(p.term.index, terms.EQ, 0, 0) and p.exponent >= 0)
               for p in B.term_defs[key].args):  # This term is 0 * something else.
            B.assert_comparison(terms.IVar(key) == 0)

        if B.implies(key, terms.NE, 0, 0) and all((p.exponent > 0 or B.sign(p.term.index) > 0)
                                                  for p in B.term_defs[key].args):
            # we have strict information about key already. So everything must have a strict sign.
            for p in B.term_defs[key].args:
                #print 'from {0} != 0, we get {1} != 0'.format(B.term_defs[key], p.term)
                B.assert_comparison(p.term != 0)

        signs = [mulpair_sign(p) for p in B.term_defs[key].args]
        unsigned = [i for i in range(len(signs)) if signs[i] == 0]
        if B.weak_sign(key) != 0:
            if len(unsigned) == 0:
                s = reduce(lambda x, y: x*y, signs)
                B.assert_comparison(terms.comp_eval[sign_to_comp[s.dir, s.strong]](terms.IVar(key),
                                                                                   0))

            if len(unsigned) == 1:
                ind = unsigned[0]
                s = reduce(lambda x, y: x*y, [signs[i] for i in range(len(signs)) if i is not ind],
                           GT)
                if s.dir == B.sign(key):
                    # remaining arg is pos
                    dir = terms.GT if B.sign(key) != 0 else terms.GE
                else:
                    dir = terms.LT if B.sign(key) != 0 else terms.LE
                B.assert_comparison(terms.comp_eval[dir](B.term_defs[key].args[ind].term, 0))

        elif len(unsigned) == 0:
            # we don't know any information about the sign of key.
            s = reduce(lambda x, y: x*y, signs)
            B.assert_comparison(terms.comp_eval[sign_to_comp[s.dir, s.strong]](terms.IVar(key), 0))

def preprocess_cancellations(B):
    """
    This routine tries to overcome some of the limitations of the elimination routine by looking
    for comparisons where there is not full sign information.

    Given a comparison t_1^k_1 * ... * t_n^k^n <> s_1^l_1 * ... * s_n ^ l_n, we cancel out as many
    pieces as we can that have sign info and check what remains for a valid comparison.
    """

    mul_inds = {i:B.term_defs[i]
                for i in range(len(B.term_defs)) if isinstance(B.term_defs[i],terms.MulTerm)}
    comps = []

    for c in (c for c in B.get_inequalities() + B.get_equalities() if
            (c.term2.coeff != 0 and (c.term1.index in mul_inds or c.term2.term.index in mul_inds))):
        lterm = mul_inds[c.term1.index] if c.term1.index in mul_inds else c.term1
        rterm = mul_inds[c.term2.term.index] if c.term2.term.index in mul_inds else c.term2.term
        coeff = c.term2.coeff
        comp = c.comp
        if isinstance(lterm, terms.IVar):
            lterm = terms.MulTerm([terms.MulPair(lterm, 1)])
        if isinstance(rterm, terms.IVar):
            rterm = terms.MulTerm([terms.MulPair(rterm, 1)])
        args_to_cancel = []
        for j in range(len(rterm.args)):
            p = rterm.args[j]
            s = B.sign(p.term.index)
            if s != 0 or (B.implies_zero_comparison(p.term.index, terms.NE) and p.exponent%2 == 0):
                #cancel = terms.MulTerm([terms.MulPair(p.term,-p.exponent)])
                #rterm, lterm = (rterm * cancel).canonize().term, (lterm * cancel).canonize().term
                args_to_cancel.append(j)
                try:
                    k = next(i for i in range(len(lterm.args)) if lterm.args[i].term.index ==
                                                                  p.term.index)
                    if lterm.args[k].exponent == p.exponent:
                        lterm.args.pop(k)
                    else:
                        lterm.args[k].exponent -= p.exponent
                except StopIteration:
                    lterm *= terms.MulTerm([terms.MulPair(p.term,-p.exponent)])
                comp = terms.comp_reverse(comp) if (s < 0 and p.exponent % 2 == 1) else comp

        rterm = terms.MulTerm([rterm.args[k] for k in range(len(rterm.args)) if
                               k not in args_to_cancel])
        if len(rterm.args) == 0:
            rterm = terms.One()
        if len(lterm.args) == 0:
            lterm = terms.One()

        lterm, rterm = lterm.canonize().term, rterm.canonize().term

        if B.has_name(lterm)[0] and B.has_name(rterm)[0]:
            B.assert_comparison(terms.comp_eval[comp](lterm, coeff * rterm))

def get_split_weight(B):
    """
    returns a list of tuples (i, j, c, <>. w). A tuple represents that this module would like
    interested to assume the comparison t_i <> c*t_j, with weight w.
    """
    def occurs_in_mul_term(i):
        for k in [j for j in range(B.num_terms) if isinstance(B.term_defs[j], terms.MulTerm)]:
            if i in [t.term.index for t in B.term_defs[k].args]:
                return True
        return False

    def no_sign_info(i):
        if not (B.implies_zero_comparison(i, terms.GT)) and \
                not (B.implies_zero_comparison(i, terms.LT)) and \
                not (B.implies_zero_comparison(i, terms.EQ)):
            return True
        else:
            return False

    return [(i, 0, 0, comp, 1) for i in range(B.num_terms) if (occurs_in_mul_term(i)
                                                               and no_sign_info(i))
            for comp in [terms.GT, terms.LT]]



