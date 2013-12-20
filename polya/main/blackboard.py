####################################################################################################
#
# blackboard.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The common data structure for sharing data between modules. An instance of Blackboard() keeps
# track of (sub)terms t0, t1, t2, t3, ... of interest, where by convention t0 represents one.
#
# When needed, we use IVar(i) to represent ti.
#
# The Blackboard class also stores the following information regarding its terms:
#
#  term_inequalities: inequalities of the form "ti comp c * tj", where c is nonzero
#  term_zero_inequalities: inequalities of the form "ti comp 0"
#  term_equalities: equalities of the form "ti = c * tj"
#  term_zero_equalities: equalities of the form "ti = 0"
#  term_disequalities: disequalities of the form "ti != c * tj", where c is nonzero
#  term_zero_disequalities: disequalities of the form "ti != 0"
#
# These internal representations should be invisible to routines outside this module, which should
# only assert information and query information through class methods.
#
# TODO: General utility functions for substitution, etc. should be defined in terms.py.
# TODO: With these, we should define functions here that expand definitions.
#
####################################################################################################


import terms
import messages


class Error(Exception):
    pass


####################################################################################################
#
# Blackboard
#
####################################################################################################


class Blackboard():
    def __init__(self):

        # named subterms
        self.num_terms = 1
        self.term_defs = {0: terms.one}       # maps each index to its definition
        self.terms = {0: terms.one}           # maps each index to its fully expanded term
        self.term_names = {terms.one.key: 0}  # reverse lookup: maps a term to is defining index

        # comparisons between named subterms
        self.term_inequalities = {}
        self.term_zero_inequalities = {0: terms.GT}
        self.term_equalities = {}
        self.term_zero_equalities = set([])
        self.term_disequalities = {}
        self.term_zero_disequalities = {0}

    def term_name(self, t):
        """
        Assumes t is a canonized term without IVars. Returns an IVar that represents t, if
        there is one. If not, recursively creates indices representing t and all its subterms, as
        needed.
        """
        if t.key in self.term_names:
            return terms.IVar(self.term_names[t.key])
        else:
            if isinstance(t, terms.Var):
                new_def = t
            elif isinstance(t, terms.AddTerm):
                new_def = terms.AddTerm([terms.STerm(a.coeff, self.term_name(a.term))
                                         for a in t.args])
            elif isinstance(t, terms.MulTerm):
                new_def = terms.MulTerm([terms.MulPair(self.term_name(a.term), a.exponent)
                                         for a in t.args])
            elif isinstance(t, terms.AbsTerm):
                new_def = terms.AbsTerm(self.term_name(t.args[0]))
            elif isinstance(t, terms.MinTerm):
                new_def = terms.MinTerm([terms.STerm(a.coeff, self.term_name(a.term))
                                         for a in t.args])
            elif isinstance(t, terms.AppTerm):
                new_def = terms.FuncTerm(t.func_name, [terms.STerm(a.coeff, self.term_name(a.term))
                                                       for a in t.args])
            else:
                raise Error('cannot create name for {0!s}'.format(t))
            i = self.num_terms  # index of the new term
            self.term_defs[i] = new_def
            self.terms[i] = t
            self.term_names[t.key] = i
            self.num_terms += 1
            messages.announce('Defining t{0!s} := {1!s}'.format(i, new_def), messages.DEF)
            messages.announce('  := {1!s}'.format(i, t), messages.DEF_FULL)
            return terms.IVar(i)

    def assert_comparison(self, c):
        """
        Take an instance of terms.TermComparison, and adds the comparison to the blackboard.
        If the comparison terms are not both IVars, finds or creates indices for the terms.
        """
        c = c.canonize()  # c is now of the form "term comp sterm"
        term1, comp, coeff, term2 = c.term1, c.comp, c.term2.coeff, c.term2.term
        if coeff == 0:
            term2 = terms.IVar(0)
        if not isinstance(term1, terms.IVar) or not isinstance(term2, terms.IVar):
            ivar1 = term1 if isinstance(term1, terms.IVar) else self.term_name(term1)
            ivar2 = term1 if isinstance(term1, terms.IVar) else self.term_name(term2)
            c = terms.TermComparison(ivar1, comp, coeff * ivar2).canonize()
            term1, comp, coeff, term2 = c.term1, c.comp, c.term2.coeff, c.term2.term
        if comp in (terms.GE, terms.GT, terms.LE, terms.LT):
            if coeff == 0:
                self.assert_term_zero_inequality(term1.index, comp)
            else:
                self.assert_term_inequality(term1.index, comp, coeff, term2.index)
        elif comp == terms.EQ:
            if coeff == 0:
                self.assert_term_zero_equality(term1.index)
            else:
                self.assert_term_equality(term1.index, coeff, term2.index)
        elif comp == terms.NE:
            if coeff == 0:
                self.assert_term_zero_disequality(term1.index)
            else:
                self.assert_term_disequality(term1.index, coeff, term2.index)
        else:
            raise Error('Unrecognized comparison: {0!s}'.format())

    def assert_term_inequality(self, i, comp, coeff, j):
        """
        Adds the inequality "ti comp coeff * tj".
        """
        # TODO: implement this
        self.announce_term_comparison(i, comp, coeff, j)

    def assert_term_zero_inequality(self, i, comp):
        """
        Adds the inequality "ti comp 0".
        """
        # TODO: implement this
        self.announce_term_zero_comparison(i, comp)

    def assert_term_equality(self, i, coeff, j):
        """
        Adds the equality "ti = coeff * tj"
        """
        # TODO: implement this
        self.announce_term_comparison(i, terms.EQ, coeff, j)

    def assert_term_zero_equality(self, i):
        """
        Adds the equality "ti = 0"
        """
        # TODO: implement this
        self.announce_term_zero_comparison(i, terms.EQ)

    def assert_term_disequality(self, i, coeff, j):
        """
        Adds the equality "ti != coeff * tj"
        """
        # TODO: implement this
        self.announce_term_comparison(i, terms.NE, coeff, j)

    def assert_term_zero_disequality(self, i):
        """
        Adds the equality "ti != 0"
        """
        # TODO: implement this
        self.announce_term_zero_comparison(i, terms.NE)

    def announce_term_comparison(self, i, comp, coeff, j):
        """
        Reports a successful assertion to the user.
        """
        messages.announce(
            'Asserting {0!s}'.format(terms.TermComparison(terms.IVar(i), comp,
                                                          coeff * terms.IVar(j))),
            messages.ASSERTION)
        messages.announce(
            '  := {0!s}'.format(terms.TermComparison(self.terms[i], comp, coeff * self.terms[j])),
            messages.ASSERTION_FULL)

    def announce_term_zero_comparison(self, i, comp):
        """
        Reports a successful assertion to the user.
        """
        messages.announce(
            'Asserting {0!s}'.format(terms.TermComparison(terms.IVar(i), comp, terms.zero)),
            messages.ASSERTION)
        messages.announce(
            '  := {0!s}'.format(terms.TermComparison(self.terms[i], comp, terms.zero)),
            messages.ASSERTION_FULL)

    # Requested by Rob, 12/19:
    def sign(self, i):
        """
        Returns 1 if ti > 0, -1 if ti < 0, 0 otherwise
        """
        return 0

    def weak_sign(self, i):
        """
        Returns 1 if ti >= 0, -1 if ti <= 0, 0 otherwise
        """
        return 0


####################################################################################################
#
# Tests
#
####################################################################################################


if __name__ == '__main__':

    # can change 'normal' to 'quiet' or 'low'
    messages.set_verbosity(messages.normal)

    u, v, w, x, y, z = terms.Vars('u, v, w, x, y, z')
    f = terms.Func('f')
    g = terms.Func('g')

    B = Blackboard()

    B.assert_comparison(x < y)
    B.assert_comparison(x + 0 < f(x, y, z))
    B.assert_comparison((x + y) + (z + x) == 2 * (x + y) * w)
    B.assert_comparison(2 * ((x + y) ** 5) * g(x) * (3 * (x * y + f(x) + 2 + w) ** 2) >=
                        (u + 3 * v + u + v + x) ** 2)
    B.assert_comparison(u + 3 * v !=
                        (x + (y * z) ** 5 + (3 * u + 2 * v) ** 2) ** 4 * (
                            u + 3 * v + u + v + x) ** 2)
    B.assert_comparison(2 * f(x, y + z) ** 2 == 3 * u * v)
    B.assert_comparison(-2 * (x + y) * w >=
                        (x + (y * z) ** 5 + (3 * u + 2 * v) ** 2) ** 4 * (
                            u + 3 * v + u + v + x) ** 2)