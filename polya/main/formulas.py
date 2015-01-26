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
import copy


class AxiomException(Exception):
    def __init__(self, msg):
        self.msg = msg


class Axiom:
    """
    literals is a list of term_comparisons. The axiom represents their disjunction.
    """
    def __init__(self, literals, triggers=list()):
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
        triggers = list()
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

    def __eq__(self, other):
        if not isinstance(other, Axiom):
            return False
        return str(self) == str(other)

    def __hash__(self):
        return hash(str(self))


class Formula:
    def __init__(self):
        pass


class And(Formula):
    """
    Represents a conjunction of formulas.
    """

    def __init__(self, *conjuncts):
        """
        conjuncts is a list of Formulas
        """
        if any(not (isinstance(c, (Formula, terms.TermComparison))) for c in conjuncts):
            raise AxiomException('Badly formed And')
        self.conjuncts = conjuncts
        Formula.__init__(self)

    def __str__(self):
        return "And({0!s})".format(', '.join(str(s) for s in self.conjuncts))

    def __repr__(self):
        return str(self)
        
    def substitute(self, map):
    	return And(*[c.substitute(map) for c in self.conjuncts])


class Or(Formula):
    """
    Represents a disjunction of formulas.
    """

    def __init__(self, *disjuncts):
        """
        disjuncts is a list of Formulas
        """
        if any(not (isinstance(c, (Formula, terms.TermComparison))) for c in disjuncts):
            print disjuncts
            raise AxiomException('Badly formed Or')
        self.disjuncts = disjuncts
        Formula.__init__(self)

    def __str__(self):
        return "Or({0!s})".format(', '.join(str(s) for s in self.disjuncts))

    def __repr__(self):
        return str(self)
        
    def substitute(self, map):
    	return Or(*[d.substitute(map) for d in self.disjuncts])


class Not(Formula):
    """
    Represents the negation of a formula
    """

    def __init__(self, formula):
        if not isinstance(formula, (Formula, terms.TermComparison)):
            print "BAD:", formula
            raise AxiomException('Badly formed Not:' + str(formula))
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
            return Or(*[Not(a) for a in self.formula.conjuncts])

        elif isinstance(self.formula, Or):
            return And(*[Not(a) for a in self.formula.disjuncts])

        elif isinstance(self.formula, Not):
            return self.formula

        elif isinstance(self.formula, Implies):
            return And(self.formula.hyp, Not(self.formula.con))

        elif isinstance(self.formula, Univ):
            return Exist(self.formula.vars, Not(self.formula.formula))

        elif isinstance(self.formula, Exist):
            return Univ(self.formula.vars, Not(self.formula.formula))

    def __str__(self):
        return "Not({0!s})".format(self.formula)

    def __repr__(self):
        return str(self)
        
    def substitute(self, map):
    	return Not(self.formula.substitute(map))


class Implies(Formula):
    """
    Represents the formula a->b
    """

    def __init__(self, hyp, con):
        if any(not isinstance(c, (Formula, terms.TermComparison)) for c in [hyp, con]):
            raise AxiomException('Badly formed Implies')
        self.hyp, self.con = hyp, con
        Formula.__init__(self)

    def __str__(self):
        return "Implies({0!s}, {1!s})".format(self.hyp, self.con)

    def __repr__(self):
        return str(self)
        
    def substitute(self, map):
    	return Implies(self.hyp.substitute(map), self.con.substitute(map))


class Univ(Formula):
    """
    Not used directly by Polya, but makes the Formula class complete.
    vars is a list of Vars. formula is a formula.
    """
    def __init__(self, vars, formula):
        if any(not isinstance(v, terms.Var) for v in vars) or not isinstance(formula, (Formula, terms.TermComparison)):
            raise AxiomException('Badly formed Univ')
        self.vars, self.formula = set(vars), formula
        Formula.__init__(self)

    def __str__(self):
        return "Forall({0!s}: {1!s})".format(", ".join(str(v) for v in self.vars), self.formula)

    def __repr__(self):
        return str(self)
        
    def substitute(self, map):
    	return Univ(self.vars, self.formula.substitute(map))


class Exist(Formula):
    """
    Not used directly by Polya, but makes the Formula class complete.
    vars is a list of Vars. formula is a formula.
    """
    def __init__(self, vars, formula):
        if any(not isinstance(v, terms.Var) for v in vars) or not isinstance(formula, (Formula, terms.TermComparison)):
            raise AxiomException('Badly formed Exist')
        self.vars, self.formula = set(vars), formula
        Formula.__init__(self)

    def __str__(self):
        return "Exist({0!s}: {1!s})".format(", ".join(str(v) for v in self.vars), self.formula)

    def __repr__(self):
        return str(self)
        
    def substitute(self, map):
    	return Exist(self.vars, self.formula.substitute(map))



class Forall:
    """
    Represents a universal quantifier over vars. Should not be mixed with Univ and Exist formulas.
    """
    def __init__(self, vars, formula):
        """
        vars is a list of terms.Vars. formula is a Formula
        """
        self.vars = vars
        #self.vars = set(v.key for v in vars) if isinstance(vars, list) else set(vars.key)
        self.formula = formula

    def to_cnf(self):
        vars = set(v.key for v in self.vars) if isinstance(self.vars, list) else set(self.vars.key)
        map = dict(zip(list(vars), range(len(vars))))

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
                return t.func(*[terms.STerm(s.coeff, replace_vars(s.term)) for s in t.args])
                #return terms.FuncTerm(t.func_name, [terms.STerm(s.coeff, replace_vars(s.term))
                                                    #for s in t.args])
            else:
                return t

        def process_tc(tc):
            return terms.TermComparison(replace_vars(tc.term1), tc.comp, replace_vars(tc.term2))

        return [[process_tc(c) for c in clause] for clause in cnf(self.formula)]

    def __str__(self):
        return "Forall({0!s}, {1!s})".format(self.vars, self.formula)

    def __repr__(self):
        return str(self)

    # def __getitem__(self, item):
    #     if isinstance(item, terms.Var):
    #         return lambda f: Forall([item], f)
    #     else:
    #         return lambda f: Forall(item, f)
    #
    # def __call__(self, *args, **kwargs):
    #     return Forall(*args)


def kill_arrows(fmla):
    """
    puts fmla in nnf with no implies
    """
    if isinstance(fmla, Univ):
        return Univ(fmla.vars, kill_arrows(fmla.formula))
    elif isinstance(fmla, Exist):
        return Exist(fmla.vars, kill_arrows(fmla.formula))
    elif isinstance(fmla, And):
        return And(*[kill_arrows(c) for c in fmla.conjuncts])
    elif isinstance(fmla, Or):
        return Or(*[kill_arrows(d) for d in fmla.disjuncts])
    elif isinstance(fmla, Implies):
        return kill_arrows(Or(Not(fmla.hyp), fmla.con))
    elif isinstance(fmla, Not):
        return kill_arrows(fmla.negate())
    elif isinstance(fmla, terms.TermComparison):
    	return fmla
    else:
    	print "Bad:", fmla
        raise Exception('Expected formula to be put in nnf')

class Count(object):
	def __init__(self):
		self.i = 1
		
	def next(self):
		self.i += 1
		return self.i - 1

cntr = Count()

def fix_scopes(fmla1):
    """
    Takes a fmla in nnf.
    Makes sure all quantifiers use different variable names.
    """
    def helper(fmla):
        if isinstance(fmla, Univ):
            fmla2 = helper(copy.deepcopy(fmla.formula))
            map = {v.key:terms.Var("qvar"+str(cntr.next())) for v in fmla.vars}    
            return Univ(set(map.values()), fmla2.substitute(map))
        elif isinstance(fmla, Exist):
            fmla2 = helper(copy.deepcopy(fmla.formula))
            map = {v.key:terms.Var("qvar"+str(cntr.next())) for v in fmla.vars}
            return Exist(set(map.values()), fmla2.substitute(map))
        elif isinstance(fmla, And):
            return And(*[helper(c) for c in fmla.conjuncts])
        elif isinstance(fmla, Or):
            return Or(*[helper(c) for c in fmla.disjuncts])
        elif isinstance(fmla, Implies):
            return Implies(helper(fmla.hyp), helper(fmla.conc))
        elif isinstance(fmla, Not):
            return Not(helper(fmla.formula))
        elif isinstance(fmla, terms.TermComparison):
        	return fmla
    return helper(fmla1)

# def kill_arrows(fmla):
#     if isinstance(fmla, Univ):
#         pass
#     elif isinstance(fmla, Exist):
#         pass
#     elif isinstance(fmla, And):
#         pass
#     elif isinstance(fmla, Or):
#         pass
#     elif isinstance(fmla, Implies):
#         pass
#     elif isinstance(fmla, Not):
#         pass

def init_q_finder(term):
	"""
	Takes a term that is an initial sequence of quantifiers Q1...Qn.
	Returns a function that maps term t to Q1...Qn t.
	"""
	if isinstance(term, Univ):
		qs, t2 = init_q_finder(term.formula)
		return lambda t: Univ(term.vars, qs(t)), t2
	elif isinstance(term, Exist):
		qs, t2 = init_q_finder(term.formula)
		return lambda t: Exist(term.vars, qs(t)), t2
	else:
		return lambda t: t, term


def pnf_helper(fmla1):
    """
    Puts a formula (with Unif and Exist quantifiers, not Forall) in prenex normal form.
    """
    
    #fmla1 = fix_scopes(kill_arrows(formula))
    # fmla1 is ands, ors, and quantifiers, and quantifier scopes don't overlap
    #print 'pnf_helper called on', fmla1
    
    if isinstance(fmla1, Univ):
        fmla2 = pnf_helper(fmla1.formula)
        if not isinstance(fmla2, Univ):
     #       print 'return', fmla1.vars, fmla2
            return Univ(fmla1.vars, fmla2)
        else:
            return Univ(fmla1.vars.union(fmla2.vars), fmla2.formula)
    elif isinstance(fmla1, Exist):
        fmla2 = pnf_helper(fmla1.formula)
        if not isinstance(fmla2, Exist):
            return Exist(fmla1.vars, fmla2)
        else:
            return Exist(fmla1.vars.union(fmla2.vars), fmla2.formula)
    elif isinstance(fmla1, And):
        pnfcnjs = [init_q_finder(pnf_helper(c)) for c in fmla1.conjuncts]
      #  print 'in and. pnfcnjs is:', pnfcnjs
        qstring = reduce(lambda f, g: lambda z: f(g(z)), [p[0] for p in pnfcnjs], lambda x: x)
        return qstring(And(*[p[1] for p in pnfcnjs]))
    elif isinstance(fmla1, Or):
        pnfcnjs = [init_q_finder(pnf_helper(c)) for c in fmla1.disjuncts]
       # print 'in or. pnfcnjs is:', pnfcnjs
       # print pnfcnjs
        qstring = reduce(lambda f, g: lambda z: f(g(z)), [p[0] for p in pnfcnjs], lambda x: x)
        return qstring(Or(*[p[1] for p in pnfcnjs]))
    elif isinstance(fmla1, terms.TermComparison):
    	return fmla1
        
def pnf(fmla):
	return pnf_helper(fix_scopes(kill_arrows(fmla)))

def cnf(formula):
    """
    Returns an equivalent formula in clausal normal form.
    Specifically, returns a list of lists of TermComparisons.
    Each list denotes the disjunction of its contents; the overall list represents the conjunction.
    """
    def distribute_or(c1, c2):
        rlist = []
        for c in c1:
            for d in c2:
                rlist.append(c + d)
        return rlist

    if isinstance(formula, Forall):
        return formula.to_cnf()
    elif isinstance(formula, terms.TermComparison):
        return [[formula.canonize()]]
    elif isinstance(formula, Not):
        return cnf(formula.negate())
    elif isinstance(formula, Implies):
        return cnf(Or(Not(formula.hyp), formula.con))
    elif isinstance(formula, And):
        return reduce(lambda a, b: a+b, (cnf(a) for a in formula.conjuncts))
    elif isinstance(formula, Or):
        disjuncts = [cnf(d) for d in formula.disjuncts]
        return reduce(distribute_or, disjuncts)

####################################################################################################
#
# Tests
#
####################################################################################################


if __name__ == '__main__':

    u, v, w, x = terms.Vars('u, v, w, x')

    ax = Or(Implies(u < v, w == x), And(u != v, x > 3*w))

    print ax
    print cnf(ax)

    ax = Or(And(u < v, v < w, w >= x), Implies(u > 3*x, w+v < 2), u < 5*v)
    print ax
    print cnf(ax)

    print Forall([u, v, w], ax)
    print Forall([u, v, w], ax).to_cnf()