####################################################################################################
#
# fourier_motzkin/addition_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The Fourier-Motzkin based routine to learn additive comparisons.
#
# AddTerms are too elaborate for the calculations here, since all our sums are based on IVars,
#   and we want to allow empty sums or sums with only one term.
#
# The classes Sum and Summand are better suited to the purposes here.
#
# TODO: for now, we use fractions. This can probably be optimized by using integers and reducing
#   by gcd's.
# TODO: another optimization: use Z3 to filter redundant inequalities
# TODO: perhaps canonize and at least filter syntactic duplication (but this may not be a problem)
#
####################################################################################################


import polya.main.terms as terms
import polya.main.messages as messages
import fractions


class Error(Exception):
    pass


class Summand():
    """
    Represents a term of the form coeff * IVar(index)
    """

    def __init__(self, coeff, index):
        self.coeff = fractions.Fraction(coeff)
        self.index = index

    def __rmul__(self, coeff):
        return Summand(coeff * self.coeff, self.index)

    def __str__(self):
        return '{0!s}*t{1!s}'.format(self.coeff, self.index)

    def __repr__(self):
        return self.__str__()


class Sum():
    """
    Represents a sum of Summands, possibly empty or with only one argument.
    """
    def __init__(self, args):
        self.args = args

    def __rmul__(self, coeff):
        return Sum([coeff * s for s in self.args])

    def __add__(self, other):
        result = []
        for a in self.args:
            try:
                s = next(s for s in other.args if s.index == a.index)
                if s.coeff != -a.coeff:
                    result.append(Summand(a.coeff + s.coeff, a.index))
            except StopIteration:
                result.append(a)
        for b in other.args:
            if not b.index in (a.index for a in self.args):
                result.append(b)
        return Sum(result)

    def __str__(self):
        if len(self.args) == 0:
            return '0'
        else:
            return ' + '.join([str(a) for a in self.args])

    def __repr__(self):
        return self.__str__()

    def contains(self, v):
        """
        Determines whether index v occurs in the sum.
        """
        return v in (a.index for a in self.args)


class ZeroComparison():
    """
    Stores a comparison s > 0 (strong) or s >= 0 (weak).
    """

    def __init__(self, term, strong):
        self.term = term
        self.strong = strong

    def __str__(self):
        if self.strong:
            return '{0!s} > 0'.format(self.term)
        else:
            return '{0!s} >= 0'.format(self.term)

    def __repr__(self):
        return self.__str__()


def cast_to_summand(term):
    """
    Represents any IVar or coeff * IVar as a Summand.
    """
    if isinstance(term, terms.IVar):
        return Summand(1, term.index)
    elif isinstance(term, terms.STerm) and isinstance(term.term, terms.IVar):
        return Summand(term.coeff, term.term.index)
    else:
        Error('{0!s} is not a summand'.format(term))


def cast_to_sum(term):
    """
    Represents any additive term built up from IVars as a Sum.
    """
    if term.key == terms.zero.key:
        return terms.Sum([])
    elif isinstance(term, terms.AddTerm):
        return Sum([cast_to_summand(a) for a in term.args])
    else:
        return Sum([cast_to_summand(term)])


def summand_to_sterm(s):
    """
    Casts any Summand to an STerm.
    """
    return terms.STerm(s.coeff, terms.IVar(s.index))


def trivial_eq(e):
    """
    Assumes e is a Sum.
    Determine whether e == 0 is the trivial equality 0 == 0
    """
    return len(e.args) == 0


def trivial_ineq(c):
    """
    Assumes c is a ZeroComparison.
    Determines whether c is the trivial inequality 0 >= 0
    """
    return len(c.term.args) == 0 and not c.strong

        
def elim_eq_eq(t1, t2, v):
    """
    Takes sums t1 and t2 and an index v
    Solves for v in t2 = 0 and substitutes the result in t1.
    """
    try:
        s1 = next(s for s in t1.args if s.index == v)
    except StopIteration:
        return t1
    try:
        s2 = next(s for s in t2.args if s.index == v)
    except StopIteration:
        raise Error('elim_eq_eq: IVar t{0!s} does not occur in {1!s}'.format(v, t2))
    return t1 + (- s1.coeff / s2.coeff) * t2


def elim_ineq_eq(c, t, v):
    """
    Takes a zero comparison c, an additive term t, and a variable, v.
    Solves for v in t = 0 and substitutes the result in c.
    """
    t1 = elim_eq_eq(c.term, t, v)
    return ZeroComparison(t1, c.strong)


def elim_ineq_ineq(c1, c2, v):
    """
    Takes two zero_comparisons, c1, and c2, and a variable, v,
    Assumes v occurs in both with opposite signs.
    Returns the result of eliminating v.
    """
    t1, t2 = c1.term, c2.term
    try:
        s1 = next(s for s in t1.args if s.index == v)
        s2 = next(s for s in t2.args if s.index == v)
    except StopIteration:
        raise Error('ineq_ineq_elim: variable {0!s} does not occur'.format(v))
    r = - (s1.coeff / s2.coeff)
    if r < 0:
        raise Error('ineq_ineq_elim: coefficients of {0!s} have the same sign'.format(v))
    return ZeroComparison(t1 + r * t2, c1.strong or c2.strong)


def elim(zero_equations, zero_comparisons, v):
    """
    The main additive elimination routine.
    Takes a list of zero equations, a list of zero comparisons, and a variable v.
    Returns a new list of zero equations and a new list of zero comparisons in which v has
    been eliminated.
    """

    # If one of the equations contains v, take the shortest such one and use that to eliminate v
    short = None
    for e in zero_equations:
        if e.contains(v) and (not short or len(e.args) < len(short.args)):
            short = e
    if short:
        new_equations, new_comparisons = [], []
        for e in zero_equations:
            if e != short:
                e1 = elim_eq_eq(e, short, v)
                if not trivial_eq(e1):
                    new_equations.append(e1)
        for c in zero_comparisons:
            c1 = elim_ineq_eq(c, short, v)
            if not trivial_ineq(c1):
                new_comparisons.append(c1)
        return new_equations, new_comparisons

    # Otherwise, do elimination on the inequalities
    pos_comparisons = []  # v occurs positively
    neg_comparisons = []  # v occurs negatively
    new_comparisons = []
    for c in zero_comparisons:
        try:
            s = next(s for s in c.term.args if s.index == v)
            if s.coeff > 0:
                pos_comparisons.append(c)
            else:
                neg_comparisons.append(c)
        except StopIteration:  # v does not occur in c
            new_comparisons.append(c)
    for c1 in pos_comparisons:
        for c2 in neg_comparisons:
            c = elim_ineq_ineq(c1, c2, v)
            if not trivial_ineq(c):
                new_comparisons.append(c)
    return zero_equations, new_comparisons


def equality_to_zero_equality(c):
    """
    Converts an equality to an equation t = 0, with t a .
    """
    return cast_to_sum(c.term1 - c.term2)


def inequality_to_zero_comparison(c):
    """
    Converts an inequality to a ZeroComparison t > 0 or t >= 0, with t an AddTerm.
    """
    if (c.comp == terms.GE) or (c.comp == terms.GT):
        term = c.term1 - c.term2
    else:
        term = c.term2 - c.term1
    strong = (c.comp == terms.GT) or (c.comp == terms.LT)
    return ZeroComparison(cast_to_sum(term), strong)


def get_additive_information(B):
    """
    Retrieves known additive comparisons and inequalities from the blackboard B
    """
    zero_equalities = [equality_to_zero_equality(c) for c in B.get_equalities()]
    zero_comparisons = [inequality_to_zero_comparison(c) for c in B.get_inequalities()]
    # convert each definition ti = s0 + s1 + ... + sn to a zero equality
    for i in range(B.num_terms):
        if isinstance(B.term_defs[i], terms.AddTerm):
            zero_equalities.append(cast_to_sum(terms.IVar(i) - B.term_defs[i]))
    return zero_equalities, zero_comparisons


def zero_equality_to_comparison(e):
    """
    Converts an equation e == 0 to a blackboard comparison between IVars, or None if
    the equation is not of that form.
    """
    l = len(e.args)
    if l == 1:
        t = summand_to_sterm(e.args[0])
        return t == 0
    elif l == 2:
        t1 = summand_to_sterm(e.args[0])
        t2 = summand_to_sterm(e.args[1])
        return t1 == -t2
    else:
        return None


def zero_comparison_to_comparison(c):
    """
    Converts a zero comparison to a blackboard comparison between IVars, or None if
    the comparison is not of that form.
    """
    s = c.term
    l = len(s.args)
    if l == 0:
        assert c.strong  # comparisons 0 >= 0 should have been eliminated
        return terms.IVar(0) < 0   # TODO: is the a better way of returning a contradiction?
    if l == 1:
        t = summand_to_sterm(s.args[0])
        return t > 0 if c.strong else t >= 0
    elif l == 2:
        t1 = summand_to_sterm(s.args[0])
        t2 = summand_to_sterm(s.args[1])
        return t1 > - t2 if c.strong else t1 >= -t2
    else:
        return None


def assert_comparisons_to_blackboard(zero_equalities, zero_comparisons, B):
    """
    Asserts all the comparisons to zero_equalities and zero_comparisons to B.
    """
    for ze in zero_equalities:
        c = zero_equality_to_comparison(ze)
        if c:
            B.assert_comparison(c)
    for zc in zero_comparisons:
        c = zero_comparison_to_comparison(zc)
        if c:
            B.assert_comparison(c)


class FMAdditionModule:

    def __init__(self):
        pass

    def update_blackboard(self, B):
        """
        Learns equalities and inequalities from additive information in B, and asserts them
        to B.
        """
        messages.announce_module('Fourier-Motzkin additive module')
        eqs, comps = get_additive_information(B)
        for i in range(B.num_terms):
            # at this point, eqs and comps have all comparisons with indices >= i
            i_eqs, i_comps = eqs, comps
            # determine all comparisons with IVar(i) and IVar(j) with j >= i
            for j in range(i + 1, B.num_terms):
                # at this point, i_eqs and i_comps have all comparisons with i and indices >= j
                ij_eqs, ij_comps = i_eqs, i_comps
                # determine all comparisons between IVar(i) and IVar(j)
                for k in range(j + 1, B.num_terms):
                     ij_eqs, ij_comps = elim(ij_eqs, ij_comps, k)
                assert_comparisons_to_blackboard(ij_eqs, ij_comps, B)
                # done with IVar(j)
                i_eqs, i_comps = elim(i_eqs, i_comps, j)
            # add this stage, i_eqs and i_comps contain only comparisons with IVar(i) alone
            assert_comparisons_to_blackboard(i_eqs, i_comps, B)
            # done with IVar(i)
            eqs, comps = elim(eqs, comps, i)


####################################################################################################
#
# Tests
#
####################################################################################################

if __name__ == '__main__':

    x = terms.IVar(0)
    y = terms.IVar(1)
    z = terms.IVar(2)
    w = terms.IVar(3)

    t1 = 3 * x + 4 * y - 2 * z
    t2 = -2 * x - 2 * y + 5 * z

    print 't1 = ', t1
    print 't2 = ', t2
    print 't1 + t2 = ', t1 + t2
    print 't1 * 3 + t2 * -1 = ', t1 * 3 + t2 * -1
    print 't1 + x =', t1 + x
    print 't1 + w =', t1 + w
    s1 = cast_to_sum(t1)
    s2 = cast_to_sum(t2)
    print 's1:', s1
    print 's2:', s2
    print 's1 + s2:', s2
    print 'eliminate x:', elim_eq_eq(s1, s2, 0)
    print 'eliminate y:', elim_eq_eq(s1, s2, 1)
    print 'eliminate z:', elim_eq_eq(s1, s2, 2)
