####################################################################################################
#
# minumum_module.py
#
# Author:
# Jeremy Avigad
#
# The routine for learning facts about terms with min
#
#
####################################################################################################

import polya.main.terms as terms
import polya.main.messages as messages
# import polya.main.formulas as formulas
# import polya.util.timer as timer
# import polya.util.num_util as num_util
import polya.util.geometry as geometry
# import fractions
# import copy

VAL, INF, NEG_INF = range(3)

class Extended:
    """
    The extended reals: infinity, negative infinity, or a value
    """

    def __init__(self, val = None):
        self.type = VAL
        self.val = val if val else 0

    def __str__(self):
        if self.type == INF:
            return 'infinity'
        elif self.type == NEG_INF:
            return '-infinity'
        else:
            return str(self.val)

    def __repr__(self):
        return self.__str__()

    def __cmp__(self, other):
        if self.type == NEG_INF:
            return 0 if other.type == NEG_INF else -1
        elif self.type == VAL:
            if other.type == NEG_INF:
                return 1
            elif other.type == VAL:
                return cmp(self.val, other.val)
            else:
                return -1
        else:
            return 0 if other.type == INF else 1

    def scale(self, c):
        """
        Scale by a nonzero coefficient.
        """
        if self.type == INF:
            return self if c > 0 else neg_infty
        elif self.type == NEG_INF:
            return self if c > 0 else infty
        else:
            return Extended(self.val * c)

infty = Extended()
infty.type = INF

neg_infty = Extended()
neg_infty.type = NEG_INF


class ComparisonRange:
    """
    An interval (whose endpoints can be +-infinity) of values c such that a comparison like
    t1 <= c * t2 is entailed by information in the blackboard.
    Extra tags indicate whether the inequality is strict or weak at the endpoints and in the
    interior.

    """

    def __init__(self, lower, upper, lower_strict, interior_strict, upper_strict):
        self.lower = lower
        self.upper = upper
        self.lower_strict = lower_strict
        self.interior_strict = interior_strict
        self.upper_strict = upper_strict

    def __str__(self):
        lower_str = 'strict' if self.lower_strict else 'weak'
        interior_str = 'strict' if self.interior_strict else 'weak'
        upper_str = 'strict' if self.upper_strict else 'weak'
        return '[{0!s}, {1!s}], {2}, {3}, {4}'.format(self.lower, self.upper, lower_str,
                                                      interior_str, upper_str)

    def __repr__(self):
        return self.__str__()

    def __and__(self, other):

        if (self.upper < self.lower or other.upper < other.lower or self.upper < other.lower or
            other.upper < self.lower):
            return empty_range

        if self.lower < other.lower:
            lower = other.lower
            if lower < self.upper:
                lower_strict = other.lower_strict and self.interior_strict
            else:  # lower == self.upper:
                lower_strict = other.lower_strict and self.upper_strict
        elif self.lower == other.lower:
            lower = self.lower
            lower_strict = self.lower_strict and other.lower_strict
        else:  # other.lower < self.lower
            lower = self.lower
            if lower < other.upper:
                lower_strict = self.lower_strict and other.interior_strict
            else:  # lower == other.upper
                lower_strict = self.lower_strict and other.upper_strict

        if self.upper < other.upper:
            upper = self.upper
            if other.lower < upper:
                upper_strict = self.upper_strict and other.interior_strict
            else:  # other.lower == upper:
                upper_strict = self.upper_strict and other.lower_strict
        elif self.upper == other.upper:
            upper = self.upper
            upper_strict = self.upper_strict and other.upper_strict
        else:  # other.upper < self.upper
            upper = other.upper
            if self.lower < upper:
                upper_strict = other.upper_strict and self.interior_strict
            else:  #  self.lower == upper
                upper_strict = other.upper_strict and self.lower_strict

        if lower < upper:
            interior_strict = self.interior_strict and other.interior_strict
        else:
            interior_strict = lower_strict

        return ComparisonRange(lower, upper, lower_strict, interior_strict, upper_strict)

    def is_empty(self):
        return self.upper < self.lower

    def scale(self, c):
        """
        Scale by a nonzero coefficient.
        """
        if c > 0:
            return ComparisonRange(self.lower.scale(c), self.upper.scale(c), self.lower_strict,
                                   self.interior_strict, self.upper_strict)
        else:
            return ComparisonRange(self.upper.scale(c), self.lower.scale(c), self.upper_strict,
                                   self.interior_strict, self.lower_strict)

empty_range = ComparisonRange(Extended(0), Extended(-1), False, False, False)


def add_halfplane_comparison(hp, hp_list):
    """
    Takes a new half plane comparison, and return a list of 0, 1, or 2 half plane comparisons,
    assumed not to be equidirectional with the new one.
    Returns a list with the strongest comparisons, taking new one into account.
    """

    if len(hp_list) < 2:
        return hp_list + [hp]
    else:
        if hp.compare_hp(hp_list[0]) == -1:
            if hp.compare_hp(hp_list[1]) == -1:
                # hp is counterclockwise from both
                if hp_list[0].compare_hp(hp_list[1]) == -1:
                    return [hp, hp_list[1]]
                else:
                    return [hp, hp_list[0]]
            else:
                return hp_list
        else:
            if hp.compare_hp(hp_list[1]) == 1:
                # hp is clockwise from both
                if hp_list[0].compare_hp(hp_list[1]) == 1:
                    return [hp_list[1], hp]
                else:
                    return [hp_list[0], hp]
            else:
                return hp_list


def halfplane_flip(hp):
    """
    Converts a comparison between ti and tj into a comparison between tj and ti
    """
    return geometry.Halfplane(-hp.b, -hp.a, hp.strong)


def get_halfplane_comparisons(B, i, j):
    """
    Assumes i ~= j, no equalities between ti and tj are known, and neither ti == 0 nor tj == 0
    are known.
    Returns a list of the at most two strongest half plane comparisons between ti and tj.
    """

    if i < j:
        hp_comps = B.inequalities.get((i, j), [])
    else:
        hp_comps = [halfplane_flip(hp) for hp in B.inequalities.get((j, i), [])]

    if i in B.zero_inequalities:
        comp = B.zero_inequalities[i]
        if comp in [terms.GT, terms.GE]:
            new_hp = geometry.Halfplane(0, -1, (True if comp == terms.GT else False))
        else:
            new_hp = geometry.Halfplane(0, 1, (True if comp == terms.LT else False))
        hp_comps = add_halfplane_comparison(new_hp, hp_comps)

    if j in B.zero_inequalities:
        comp = B.zero_inequalities[j]
        if comp in [terms.GT, terms.GE]:
            new_hp = geometry.Halfplane(-1, 0, (True if comp == terms.GT else False))
        else:
            new_hp = geometry.Halfplane(1, 0, (True if comp == terms.LT else False))
        hp_comps = add_halfplane_comparison(new_hp, hp_comps)

    return hp_comps


def get_le_range(B, i, j):
    """
    Takes a blackboard B, and two indices, i, j < B,num_terms.
    Returns an ComparisonRange for the comparison t_i <= c * t_j.
    """

    si = B.sign(i)
    wsi = B.weak_sign(i)
    sj = B.sign(j)
    wsj = B.weak_sign(j)

    if i ==j or (i < j and (i, j) in B.equalities) or (j < i and (j, i) in B.equalities):
        if i == j:
            coeff = Extended(1)
        elif i < j:
            coeff = Extended(B.equalities[i, j])
        else:
            coeff = Extended(1 / B.equalities[j, i])
        if sj == 1:
            return ComparisonRange(coeff, infty, False, True, True)
        elif wsj == 1:
            return ComparisonRange(coeff, infty, False, False, False)
        elif sj == -1:
            return ComparisonRange(neg_infty, coeff, True, True, False)
        elif wsj == -1:
            return ComparisonRange(neg_infty, coeff, False, False, False)
        else:
            return ComparisonRange(coeff, coeff, False, False, False)

    if j in B.zero_equalities:
        if i in B.zero_equalities:
            return ComparisonRange(neg_infty, infty, False, False, False)
        elif i in B.zero_inequalities:
            if B.zero_inequalities[i] == terms.LT:
                return ComparisonRange(neg_infty, infty, True, True, True)
            elif B.zero_inequalities[i] == terms.LE:
                return ComparisonRange(neg_infty, infty, False, False, False)
            else:
                return empty_range
        else:
            return empty_range

    if i in B.zero_equalities:
        if j in B.zero_inequalities:
            comp = B.zero_inequalities[j]
            if comp == terms.GT:
                return ComparisonRange(Extended(0), infty, False, True, True)
            elif comp == terms.GE:
                return ComparisonRange(Extended(0), infty, False, False, False)
            elif comp == terms.LE:
                return ComparisonRange(neg_infty, Extended(0), False, False, False)
            else:
                return ComparisonRange(neg_infty, Extended(0), False, True, True)
        else:
            return empty_range

    hp_comps = get_halfplane_comparisons(B, i, j)
    if len(hp_comps) == 0:
        return empty_range
    if len(hp_comps) == 1:
        hp = hp_comps[0]
        if hp.a <= 0:
            return empty_range
        else:
            coeff = Extended(hp.a / hp.b)
            strict = hp.strong
            return ComparisonRange(coeff, coeff, strict, strict, strict)
    else:
        hp0, hp1 = hp_comps[0], hp_comps[1]
        if hp0.compare_hp(hp1) == 1:
            hp0, hp1 = hp1, hp0
        if hp0.b <= 0 and hp1.b <= 0:
            return empty_range
        elif hp0.b <= 0:
            lower = neg_infty
            upper = Extended(hp1.a / hp1.b)
            return ComparisonRange(lower, upper, True, True, hp1.strong)
        elif hp1.b <= 0:
            lower = Extended(hp0.a / hp0.b)
            upper = infty
            return ComparisonRange(lower, upper, hp0.strong, True, True)
        else:
            lower = Extended(hp0.a / hp0.b)
            upper = Extended(hp1.a / hp1.b)
            return ComparisonRange(lower, upper, hp0.strong, True, hp1.strong)


# TODO: this is similar to the previous one. Can they be combined?
def get_ge_range(B, i, j):
    """
    Takes a blackboard B, and two indices, i, j < B,num_terms.
    Returns an ComparisonRange for the comparison t_i >= c * t_j.
    """

    si = B.sign(i)
    wsi = B.weak_sign(i)
    sj = B.sign(j)
    wsj = B.weak_sign(j)

    if i ==j or (i < j and (i, j) in B.equalities) or (j < i and (j, i) in B.equalities):
        if i == j:
            coeff = Extended(1)
        elif i < j:
            coeff = Extended(B.equalities[i, j])
        else:
            coeff = Extended(1 / B.equalities[j, i])
        if sj == 1:
            return ComparisonRange(neg_infty, coeff, True, True, False)
        elif wsj == 1:
            return ComparisonRange(neg_infty, coeff, False, False, False)
        elif sj == -1:
            return ComparisonRange(coeff, infty, False, True, True)
        elif wsj == -1:
            return ComparisonRange(coeff, infty, False, False, False)
        else:
            return ComparisonRange(coeff, coeff, False, False, False)

    if j in B.zero_equalities:
        if i in B.zero_equalities:
            return ComparisonRange(neg_infty, infty, False, False, False)
        elif i in B.zero_inequalities:
            if B.zero_inequalities[i] == terms.GT:
                return ComparisonRange(neg_infty, infty, True, True, True)
            elif B.zero_inequalities[i] == terms.GE:
                return ComparisonRange(neg_infty, infty, False, False, False)
            else:
                return empty_range
        else:
            return empty_range

    if i in B.zero_equalities:
        if j in B.zero_inequalities:
            comp = B.zero_inequalities[j]
            if comp == terms.GT:
                return ComparisonRange(neg_infty, Extended(0), True, True, False)
            elif comp == terms.GE:
                return ComparisonRange(neg_infty, Extended(0), False, False, False)
            elif comp == terms.LE:
                return ComparisonRange(Extended(0), infty, False, False, False)
            else:
                return ComparisonRange(Extended(0), infty, True, True, False)
        else:
            return empty_range

    hp_comps = get_halfplane_comparisons(B, i, j)
    if len(hp_comps) == 0:
        return empty_range
    if len(hp_comps) == 1:
        hp = hp_comps[0]
        if hp.a <= 0:
            return empty_range
        else:
            coeff = Extended(hp.a / hp.b)
            strict = hp.strong
            return ComparisonRange(coeff, coeff, strict, strict, strict)
    else:
        hp0, hp1 = hp_comps[0], hp_comps[1]
        if hp0.compare_hp(hp1) == 1:
            hp0, hp1 = hp1, hp0
        if hp0.b >= 0 and hp1.b >= 0:
            return empty_range
        elif hp0.b >= 0:
            lower = neg_infty
            upper = Extended(hp1.a / hp1.b)
            return ComparisonRange(lower, upper, True, True, hp1.strong)
        elif hp1.b >= 0:
            lower = Extended(hp0.a / hp0.b)
            upper = infty
            return ComparisonRange(lower, upper, hp0.strong, True, True)
        else:
            lower = Extended(hp0.a / hp0.b)
            upper = Extended(hp1.a / hp1.b)
            return ComparisonRange(lower, upper, hp0.strong, True, hp1.strong)


def le_coeff_range(B, i, j, coeff):
    """
    Takes a blackboard, B, and i, j < B.num_terms.
    Returns a comparison range for the relation c * ti <= coeff * tj, i.e. a range of values for
    c for which the comparison is known to hold.
    """

    if coeff == 0:
        if i in B.zero_equalities:
            return ComparisonRange(neg_infty, infty, False, False, False)
        elif i in B.zero_inequalities:
            if B.zero_inequalities[i] == terms.GT:
                return ComparisonRange(neg_infty, infty, True, True, True)
            elif B.zero_inequalities[i] == terms.GE:
                return ComparisonRange(neg_infty, infty, False, False, False)
            else:
                return empty_range
        else:
            return empty_range
    elif coeff > 0:
        return get_ge_range(B, j, i).scale(coeff)
    else:  # coeff < 0
        return get_le_range(B, j, i).scale(coeff)


class MinimumModule:

    def __init__(self):
        pass

    def update_blackboard(self, B):
        messages.announce_module('minimum module')
        for i in range(B.num_terms):
            if isinstance(B.term_defs[i], terms.FuncTerm) and B.term_defs[i].func_name == 'minm':
                # t_i is of the form minm(...)
                args = B.term_defs[i].args
                # assert that t_i is le all of its arguments
                for a in args:
                    B.assert_comparison(terms.IVar(i) <= a)
                # see if we can infer the sign
                # TODO: optimize
                if all(B.implies_comparison(a > 0) for a in args):
                    B.assert_comparison(terms.IVar(i) > 0)
                elif all(B.implies_comparison(a >= 0) for a in args):
                    B.assert_comparison(terms.IVar(i) >= 0)
                if any(B.implies_comparison(a < 0) for a in args):
                    B.assert_comparison(terms.IVar(i) < 0)
                elif any(B.implies_comparison(a <= 0) for a in args):
                    B.assert_comparison(terms.IVar(i) <= 0)
                # see if any multiple of another problem term is known to be less than all the
                # arguments.
                for j in range(B.num_terms):
                    if  j != i:
                        comp_range = ComparisonRange(neg_infty, infty, True, True, True)
                        for a in args:
                            comp_range = comp_range & le_coeff_range(B, j, a.term.index, a.coeff)
                            if comp_range.is_empty():
                                break
                        if not comp_range.is_empty():
                            if comp_range.lower.type == VAL:
                                c = comp_range.lower.val
                                if comp_range.lower_strict:
                                    B.assert_comparison(c * terms.IVar(j) < terms.IVar(i))
                                else:
                                    B.assert_comparison(c * terms.IVar(j) <= terms.IVar(i))
                            if comp_range.upper.type == VAL:
                                c = comp_range.upper.val
                                if comp_range.upper_strict:
                                    B.assert_comparison(c * terms.IVar(j) < terms.IVar(i))
                                else:
                                    B.assert_comparison(c * terms.IVar(j) <= terms.IVar(i))


                # old code
                # # if any argument is the smallest, t_i is equal to that
                # if a in args:
                #     if all((a is a1) or B.implies_comparison(a <= a1) for a1 in args):
                #             B.assert_comparison(terms.IVar(i) == a)
                # # see if any problem term is known to be less than all the arguments
                # # TODO: note, we could also do this by adding clauses
                # for j in range(B.num_terms):
                #     if j != i:
                #         if all(B.implies_comparison(terms.IVar(j) < a) for a in args):
                #             B.assert_comparison(terms.IVar(j) < terms.IVar(i))
                #         elif all(B.implies_comparison(terms.IVar(j) <= a) for a in args):
                #             B.assert_comparison(terms.IVar(j) <= terms.IVar(i))
                #
                #         # if all(B.implies(j, terms.LT, a.coeff, a.term.index) for a in args):
                #         #     B.assert_comparison(terms.IVar(j) < terms.IVar(i))
                #         # elif all(B.implies(j, terms.LE, a.coeff, a.term.index) for a in args):
                #         #     B.assert_comparison(terms.IVar(j) <= terms.IVar(i))