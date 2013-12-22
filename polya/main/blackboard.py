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
#  term_equalities: equalities of the form "ti = c * tj", where c is nonzero
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
import geometry
import fractions


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
        self.term_names = {terms.one.key: 0}      # reverse lookup: maps a term to is defining index

        # comparisons between named subterms
        self.inequalities = {}  # Dictionary mapping (i, j) to a list of pairs (comp, coeff)
        self.zero_inequalities = {0: terms.GT}  # Dictionary mapping i to comp
        self.equalities = {}  # Dictionary mapping (i, j) to coeff
        self.zero_equalities = set([])  # Set of IVar indices equal to 0
        self.disequalities = {}  # Dictionary mapping (i, j) to a set of coeffs
        self.zero_disequalities = set([])  # Is this one necessary?

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

    def get_inequalities(self):
        inequalities = []
        for i in self.zero_inequalities:
            comp = self.zero_inequalities[i]
            inequalities.append(terms.comp_eval[comp](terms.IVar(i), 0))
        for (i, j) in self.inequalities:
            for comp, coeff in self.inequalities[i, j]:
                inequalities.append(terms.comp_eval[comp](terms.IVar(i), coeff * terms.IVar(j)))
        return inequalities

    def get_equalities(self):
        equalities = [terms.IVar(i) == 0 for i in self.zero_equalities]
        for p in self.equalities:
            coeff = self.equalities[p]
            equalities.append(terms.IVar(p[0]) == coeff * terms.IVar(p[1]))
        return equalities

    def get_disequalities(self):
        disequalities = [terms.IVar(i) != 0 for i in self.zero_disequalities]
        for p in self.disequalities:
            coeff_list = self.disequalities[p]
            for coeff in coeff_list:
                disequalities.append(terms.IVar(p[0]) != coeff * terms.IVar(p[1]))
        return disequalities

    def implies(self, i, comp, coeff, j):
        """
        Checks to see if the statement ti comp coeff * tj is known by the Blackboard.
        """
        #print 'checking if t{0} {1} {2} t{3}'.format(i, terms.comp_str[comp], coeff, j)
        if coeff == 0:
            return self.implies_zero_comparison(i, comp)

        elif i == j:
            coeff1 = 1 - coeff
            if coeff1 > 0:
                return self.implies_zero_comparison(i, comp)
            elif coeff1 < 0:
                return self.implies_zero_comparison(i, terms.comp_reverse(comp))
            elif comp in [terms.GE, terms.LE, terms.EQ]:
                return True
            else:
                return False

        if comp in [terms.LT, terms.LE, terms.GE, terms.GT]:
            # Gather all of the known information about ti and tj.
            new_line = geometry.Line(1, -coeff, 0, comp)
            known_lines = [geometry.Line(1, -coeff1, 0, comp1)
                           for (comp1, coeff1) in self.inequalities.get((i, j), [])]
            if i in self.zero_inequalities:
                known_lines.append(geometry.Line(1, 0, 0, self.zero_inequalities[i]))
            if j in self.zero_equalities:
                known_lines.append(geometry.Line(0, 1, 0, self.zero_inequalities[j]))

            # If we don't know anything, we don't know ti comp coeff * tj
            if len(known_lines) == 0:
                return False

            # If we only know one thing, then we only know the new info if it is the same.
            elif len(known_lines) == 1:
                if new_line.slope() == known_lines[0].slope():
                    if ((comp == known_lines[0].comp)
                       or (comp == terms.GE and known_lines[0].comp == terms.GT)
                       or (comp == terms.LE and known_lines[0].comp == terms.LT)):
                        return True
                return False

            # Otherwise, figure out the two strongest things we know, and see if they imply the new.
            else:
                # We know at least two facts about i and j.
                return not new_line.has_new_info(*geometry.find_two_strongest(known_lines))

        # All equality info is stored, so see if we know this equality.
        elif comp == terms.EQ:
            return coeff == self.equalities.get((i, j), None)

        # See if we know this disequality, or if the disequality is implied by an inequality.
        elif comp == terms.NE:
            if coeff in self.disequalities.get((i, j), []):
                return True
            return self.implies(i, terms.GT, coeff, j) or self.implies(i, terms.LT, coeff, j)

    def implies_zero_comparison(self, i, comp):
        """
        Checks to see if the statement ti comp 0 is known by the Blackboard.
        """
        if comp in [terms.LT, terms.GT]:
            return self.zero_inequalities.get(i, terms.EQ) == comp

        elif comp == terms.LE:
            return self.zero_inequalities.get(i, terms.EQ) in [terms.LE, terms.LT]

        elif comp == terms.GE:
            return self.zero_inequalities.get(i, terms.EQ) in [terms.GE, terms.GT]

        elif comp == terms.EQ:
            return i in self.zero_equalities

        elif comp == terms.NE:
            return i in self.zero_disequalities

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

        if self.implies(term1.index, comp, coeff, term2.index):
            return
        elif self.implies(term1.index, terms.comp_negate(comp), coeff, term2.index):
            self.raise_contradiction(term1.index, comp, coeff, term2.index)

        if comp in (terms.GE, terms.GT, terms.LE, terms.LT):
            if coeff == 0:
                self.assert_zero_inequality(term1.index, comp)
            else:
                self.assert_inequality(term1.index, comp, coeff, term2.index)
        elif comp == terms.EQ:
            if coeff == 0:
                self.assert_zero_equality(term1.index)
            else:
                self.assert_equality(term1.index, coeff, term2.index)
        elif comp == terms.NE:
            if coeff == 0:
                self.assert_zero_disequality(term1.index)
            else:
                self.assert_disequality(term1.index, coeff, term2.index)
        else:
            raise Error('Unrecognized comparison: {0!s}'.format())

    def assert_inequality(self, i, comp, coeff, j):
        """
        Adds the inequality "ti comp coeff * tj".
        """
        new_line = geometry.Line(1, -coeff, 0, comp)
        lines = [geometry.Line(1, -coeff1, 0, comp1)
                 for (comp1, coeff1) in self.inequalities.get((i, j), [])]
        if len(lines) == 0:
            self.inequalities[i, j] = [(comp, coeff)]
        else:
            if i in self.zero_inequalities:
                lines.append(geometry.Line(1, 0, 0, self.zero_inequalities[i]))
            if j in self.zero_equalities:
                lines.append(geometry.Line(0, 1, 0, self.zero_inequalities[j]))
            lines.append(new_line)
            l1, l2 = geometry.find_two_strongest(lines)
            ineqs = [((l.comp if l.a > 0 else terms.comp_reverse(l.comp)),
                      fractions.Fraction(-l.b, l.a))
                     for l in [l1, l2] if l.a != 0 and l.b != 0]
            self.inequalities[i, j] = ineqs
        self.announce_comparison(i, comp, coeff, j)

    def assert_zero_inequality(self, i, comp):
        """
        Adds the inequality "ti comp 0".
        """
        # TODO: implement this
        self.announce_zero_comparison(i, comp)

    def assert_equality(self, i, coeff, j):
        """
        Adds the equality "ti = coeff * tj"
        """
        # TODO: implement this
        self.announce_comparison(i, terms.EQ, coeff, j)

    def assert_zero_equality(self, i):
        """
        Adds the equality "ti = 0"
        """
        if i not in self.zero_equalities:
            self.zero_equalities.add(i)
            self.announce_zero_comparison(i, terms.EQ)

    def assert_disequality(self, i, coeff, j):
        """
        Adds the equality "ti != coeff * tj"
        """
        if (i, j) in self.disequalities:
            if coeff not in self.disequalities[i, j]:
                self.disequalities[i, j].add(coeff)
                self.announce_comparison(i, terms.NE, coeff, j)
        else:
            self.disequalities[i, j] = set([coeff])
            self.announce_comparison(i, terms.NE, coeff, j)

    def assert_zero_disequality(self, i):
        """
        Adds the equality "ti != 0"
        """
        # TODO: implement this
        self.announce_zero_comparison(i, terms.NE)

    def announce_comparison(self, i, comp, coeff, j):
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

    def announce_zero_comparison(self, i, comp):
        """
        Reports a successful assertion to the user.
        """
        messages.announce(
            'Asserting {0!s}'.format(terms.TermComparison(terms.IVar(i), comp, terms.zero)),
            messages.ASSERTION)
        messages.announce(
            '  := {0!s}'.format(terms.TermComparison(self.terms[i], comp, terms.zero)),
            messages.ASSERTION_FULL)

    def raise_contradiction(self, i, comp, coeff, j):
        """
        Called when the given information contradicts something already known.
        """
        # TODO: implement this
        pass

    def sign(self, i):
        """
        Returns 1 if ti > 0, -1 if ti < 0, 0 otherwise
        """
        if i in self.zero_inequalities:
            comp = self.zero_inequalities[i]
            if comp == terms.GT:
                return 1
            elif comp == terms.LT:
                return -1
        return 0

    def weak_sign(self, i):
        """
        Returns 1 if ti >= 0, -1 if ti <= 0, 0 otherwise
        """
        if i in self.zero_inequalities:
            comp = self.zero_inequalities[i]
            if comp in (terms.GT, terms.GE):
                return 1
            elif comp in (terms.LT, terms.LE):
                return -1
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
    B.assert_comparison(y > 4 * x)
    B.assert_comparison(y < -x)
    B.assert_comparison(x < 0)
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

    print B.get_equalities()
    print B.get_inequalities()
    print B.get_disequalities()

    print B.implies(0, terms.GT, 2, 0)
    print B.implies(18, terms.NE, 9, 23)

    print
    print B.inequalities