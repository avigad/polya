####################################################################################################
#
# formulas.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# Formulas are used for constructing Axioms for the function module.
#
# A formula can be one of these types:
#  - A TermComparison
#  - And(Formula, ..., Formula)
#  - Or(Formula, ..., Formula)
#  - Implies(Formula, Formula)
#  - Not(Formula)
#
# Formulas can be canonized into conjunctive normal form (an and of ors),
# and can be constructed using Not or Implies.
#
####################################################################################################

import polya.main.terms as terms
import numbers


class AxiomException(Exception):
    def __init__(self, msg):
        self.msg = msg

class Axiom:
    """
    literals is a list of term_comparisons. The axiom represents their disjunction.
    """
    def __init__(self, literals):
        #todo: make triggers a set

        def find_uvars(term):
            """
            Takes a Term and returns two sets.
            The first is the set of all indices UVars that return in that term.
            The second is the subset of the first that occur alone as function arguments.
            """
            if isinstance(term, terms.UVar):
                return {term.index}, set()
            elif isinstance(term, (terms.Atom, numbers.Rational)):
                return set(), set()
            else:
                vars = set()
                if isinstance(term, terms.FuncTerm):
                    arg_vars = set([p.term.index for p in term.args
                                    if isinstance(p.term, terms.UVar)])
                else:
                    arg_vars = set()
                for p in term.args:
                    nvars, narg_vars = find_uvars(p.term)
                    vars.update(nvars)
                    arg_vars.update(narg_vars)
                return vars, arg_vars

        def find_func_subterms(term):
            f_subterms = []
            if isinstance(term, terms.Atom):
                return f_subterms
            if isinstance(term, terms.FuncTerm):
                f_subterms.append(term)
            for pair in term.args:
                f_subterms.extend(find_func_subterms(pair.term))
            return f_subterms

        self.literals = [l.canonize() for l in literals]

        # todo: user should be able to specify triggers if they would like to.
        triggers=list()
        if len(triggers) == 0:
            for c in self.literals:
                triggers.extend(find_func_subterms(c.term1))
                triggers.extend(find_func_subterms(c.term2.term))
        self.triggers = triggers

        uvars, arg_uvars, trig_uvars, trig_arg_uvars = set(), set(), set(), set()
        for c in self.literals:
            nvars, narg_vars = find_uvars(c.term1)
            uvars.update(nvars)
            arg_uvars.update(narg_vars)
            nvars, narg_vars = find_uvars(c.term2.term)
            uvars.update(nvars)
            arg_uvars.update(narg_vars)

        for c in self.triggers:
            trig_nvars, trig_narg_vars = find_uvars(c)
            trig_uvars.update(trig_nvars)
            trig_arg_uvars.update(trig_narg_vars)

        if trig_uvars != uvars:
            raise Exception('All UVars must be in the trigger set.')
        else:
            self.vars, self.arg_vars, self.trig_arg_vars = uvars, arg_uvars, trig_arg_uvars

    def __str__(self):
        str1 = "{For all " + ", ".join(str(terms.UVar(u)) for u in self.vars) + ": "
        str1 += " or ".join(str(l) for l in self.literals) + "}"
        return str1

    def __repr__(self):
        return str(self)


class Formula:
    def __init__(self):
        pass


class And(Formula):
    """
    Represents a conjunction of formulas.
    """

    def __init__(self, f1, f2):
        """
        conjuncts is a list of Formulas
        """
        if any(not (isinstance(c, (Formula, terms.TermComparison))) for c in [f1, f2]):
            raise AxiomException('Badly formed And')
        self.f1, self.f2 = f1, f2
        Formula.__init__(self)

    def __str__(self):
        return "And({0!s}, {1!s})".format(self.f1, self.f2)

    def __repr__(self):
        return str(self)


class Or(Formula):
    """
    Represents a disjunction of formulas.
    """

    def __init__(self, f1, f2):
        """
        disjuncts is a list of Formulas
        """
        if any(not (isinstance(c, (Formula, terms.TermComparison))) for c in [f1, f2]):
            raise AxiomException('Badly formed Or')
        self.f1, self.f2 = f1, f2
        Formula.__init__(self)

    def __str__(self):
        return "Or({0!s}, {1!s})".format(self.f1, self.f2)

    def __repr__(self):
        return str(self)


class Not(Formula):
    """
    Represents the negation of a formula
    """

    def __init__(self, formula):
        if not isinstance(formula, (Formula, terms.TermComparison)):
            raise AxiomException('Badly formed Not')
        self.formula = formula
        Formula.__init__(self)

    def negate(self):
        """
        Pushes the negation through self.formula to remove the not.
        """
        if isinstance(self.formula, terms.TermComparison):
            return terms.TermComparison(self.formula.term1,
                                        terms.comp_negate(self.formula.comp),
                                        self.formula.term2)

        elif isinstance(self.formula, And):
            return Or(Not(self.formula.f1), Not(self.formula.f2))

        elif isinstance(self.formula, Or):
            return And(Not(self.formula.f1), Not(self.formula.f2))

        elif isinstance(self.formula, Not):
            return self.formula

        elif isinstance(self.formula, Implies):
            return And(self.formula.hyp, Not(self.formula.con))

    def __str__(self):
        return "Not({0!s})".format(self.formula)

    def __repr__(self):
        return str(self)


class Implies(Formula):
    """
    Represents the formula a->b
    """

    def __init__(self, hyp, con):
        if any(not isinstance(c, (Formula, terms.TermComparison)) for c in [hyp, con]):
            raise AxiomException('Badly formed Not')
        self.hyp, self.con = hyp, con
        Formula.__init__(self)

    def __str__(self):
        return "Implies({0!s}, {1!s})".format(self.hyp, self.con)

    def __repr__(self):
        return str(self)

class ForAll:
    """
    Represents a universal quantifier over vars
    Vars are terms.Vars
    """
    def __init__(self, vars, formula):
        self.vars = set(v.key for v in vars)
        self.formula = cnf(formula)

    def to_cnf(self):
        map = dict(zip(list(self.vars), range(len(self.vars))))

        def replace_vars(t):
            if isinstance(t, terms.STerm):
                return terms.STerm(t.coeff, replace_vars(t.term))
            if isinstance(t, terms.Var):
                return terms.UVar(map[t.key]) if t.key in map else t
            elif isinstance(t, terms.AddTerm):
                return terms.AddTerm([terms.STerm(s.coeff, replace_vars(s.term)) for s in t.args])
            elif isinstance(t, terms.MulTerm):
                return terms.MulTerm([terms.MulPair(replace_vars(s.term), s.exponent)
                                      for s in t.args])
            elif isinstance(t, terms.FuncTerm):
                return terms.FuncTerm(t.func_name, [terms.STerm(s.coeff, replace_vars(s.term))
                                                    for s in t.args])
            else:
                return t

        def process_tc(tc):
            return terms.TermComparison(replace_vars(tc.term1), tc.comp, replace_vars(tc.term2))

        return [[process_tc(c) for c in clause] for clause in self.formula]



def cnf(formula):
    """
    Returns an equivalent formula in clausal normal form.
    Specifically, returns a list of lists of TermComparisons.
    Each list denotes the disjunction of its contents; the overall list represents the conjunction.
    """
    if isinstance(formula, ForAll):
        return formula.to_cnf()
    elif isinstance(formula, terms.TermComparison):
        return [[formula.canonize()]]
    elif isinstance(formula, Not):
        return cnf(formula.negate())
    elif isinstance(formula, Implies):
        return cnf(Or(Not(formula.hyp), formula.con))
    elif isinstance(formula, And):
        return cnf(formula.f1) + cnf(formula.f2)
    elif isinstance(formula, Or):
        c1, c2 = cnf(formula.f1), cnf(formula.f2)
        rlist = []
        for c in c1:
            for d in c2:
                rlist.append(c + d)
        return rlist


####################################################################################################
#
# Tests
#
####################################################################################################


if __name__ == '__main__':

    u, v, w, x = terms.Vars('u, v, w, x')

    ax = Or(Implies(u<v, w==x),And(u!=v, x>3*w))

    print ax
    print cnf(ax)