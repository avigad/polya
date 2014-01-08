####################################################################################################
#
# function_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The routine for learning facts using axioms.
# FunctionModule is initialized with a list of axioms.
# Each time update_blackboard is called, the module will check to see if any new clauses can be
# instantiated from its known axioms, and if so, will add them to the blackboard.
#
# TODO:
#
####################################################################################################

import terms
import blackboard
import messages
import fractions
import numbers
import copy
# from itertools import product, ifilter
# from inspect import getargspec
# from copy import copy
# from scipy.linalg import lu
# from numpy import array

class Axiom:
    """
    literals is a list of term_comparisons
    triggers is
    """
    def __init__(self, literals, triggers=list()):

        def find_uvars(term):
            """
            Takes a Term and returns two sets.
            The first is the set of all indices UVars that return in that term.
            The second is the subset of the first that occur alone as function arguments.
            """
            if isinstance(term, terms.UVar):
                return {term.index}, set()
            elif isinstance(term, (terms.Var, numbers.Rational)):
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

        self.literals = literals
        if len(triggers) > 0:
            self.triggers = triggers
        else:
            pass

class Environment:
    def __init__(self):
        pass

def substitute(term, u_index, coeff, i_index):
    """
    Replaces all instances of u_{u_index} in term with coeff * t_{i_index}.
    """
    return reduce_term(term, {u_index:(coeff, i_index)})

def reduce_term(term, env):
    """
    env maps UVar indices to (coeff, IVar index) pairs.
    Replaces all defined UVars in term with their designated values.
    Returns a pair of a new Term and a flag whether all UVars have been replaced.
    """
    if isinstance(term, terms.IVar):
        return term, True

    elif isinstance(term, terms.UVar):
        if term.index in env:
            c, j = env[term.index]
            return c*terms.IVar(j), True

    elif isinstance(term, terms.AddTerm):
        rfunc = lambda (s1, flag1), (s2, flag2): (s1+s2, flag1 and flag2)
        return reduce(rfunc, [(lambda a: (ap.coeff*a[0], a[1]))(reduce_term(ap.term, env))
                              for ap in term.args])
    elif isinstance(term, terms.MulTerm):
        rfunc = lambda (s1, flag1), (s2, flag2): (s1*s2, flag1 and flag2)
        return reduce(rfunc, [(lambda a:(a[0]**mp.exponent, a[1]))(reduce_term(mp.term, env))
                              for mp in term.args])
    elif isinstance(term, terms.FuncTerm):
        flag1 = True
        nargs = []
        for a in term.args:
            s, flag2 = reduce_term(a.term, env)
            nargs.append(a.coeff * s)
            flag1 = flag1 and flag2
        return terms.FuncTerm(term.func_name, nargs), flag1

    else:
        raise Exception("Unknown term type encountered in reduce_term")


class NoTermException(Exception):
    pass


def add_list(l1, l2):
    return [l1[i]+l2[i] for i in range(len(l1))]


def scale_list(c, l):
    return [c*li for li in l]


def elim_var(i, pivot, rows):
    if pivot[i] == 0:
        raise Exception
    new_rows = [add_list(r, scale_list(-fractions.Fraction(r[i], pivot[i]), pivot)) for r in rows]
    return new_rows


def find_problem_term(B, term):
    """
    term is a Term such that all variable occurrences are IVars.
    returns (c, i) such that term = c*ti, or raises NoTermException
    """
    if isinstance(term, terms.IVar):
        return 1, term.index

    elif isinstance(term, terms.FuncTerm):
        nargs = [find_problem_term(B, p.term) for p in term.args]
        for i in range(len(nargs)):
            nargs[i] = (term.args[i].coeff*nargs[i][0], nargs[i][1])

        for i in range(len(B.num_terms)):
            t = B.term_defs[i]
            if (isinstance(t, terms.FuncTerm) and t.func_name == term.func_name
                                                                and len(t.args) == len(nargs)):
                match = True
                for k in range(len(t.args)):
                    targ, uarg = (t.args[k].coeff, t.args[k].term.index), nargs[k]
                    if not targ == uarg:
                        match = False  # todo: add matching modulo equality here
                        break

                if match:
                    return 1, i
        raise NoTermException

    elif isinstance(term, terms.AddTerm):
        if len(term.args) == 1:
            return term.args[0].coeff, term.args[0].term.index
        elif term.key in B.term_names:
            return B.term_names[term.key]

        nargs = [find_problem_term(B, p.term) for p in term.args]
        for i in range(len(nargs)):
            nargs[i] = (term.args[i].coeff*nargs[i][0], nargs[i][1])

        # Do some linear algebra
        urow = [0]*B.num_terms + [-1]
        for (c, i) in nargs:
            urow[i] = c

        mat = []
        for tc in B.get_equalities():
            i, c = tc.term1.index, tc.coeff
            j = (B.num_terms if tc.coeff == 0 else tc.term2.term.index)
            row = [0]*(B.num_terms+1)
            row[i] = -1
            row[j] = c
            mat.append(row[:])

        for i in (i for i in range(B.num_terms) if isinstance(B.term_defs[i], terms.AddTerm)):
            row = [0]*(B.num_terms+1)
            row[i] = -1
            for p in B.name_defs[i].addpairs:
                row[p.term.index] = p.coeff
            mat.append(row[:])

        mat.append(urow)

        #begin FM elimination
        rows_i = copy.copy(mat)
        for i in range(B.num_terms): #check if u = c*i
            rows_j = copy.copy(rows_i)
            for j in range(i+1,B.num_terms):
                try:
                    r = next(r for r in rows_j if r[j]!=0 and r[-1]==0)
                except StopIteration:
                    continue
                rows = elim_var(j,r,[row for row in rows_j if row is not r])

            row = next(r for r in rows_j if r[-1]!=0)
            l = len([k for k in row if k != 0])
            if l == 1:
                #we have u = 0. What to do?
                return 0, 0
            elif l == 2:
                #we've found a match for u
                ind = next(k for k in range(len(row)) if row[k] != 0)
                coeff = -fractions.Fraction(row[ind],row[-1])
                return coeff, ind
            else:
                try:
                    r = next(r for r in rows_i if r[i] != 0 and r[-1] == 0)
                    rows_i = elim_var(i,r,[row for row in rows_i if row is not r])
                except StopIteration:
                    if rows_i[-1][i]!=0: #there is a t_i in u, and nowhere else. Can't elim.
                        raise NoTermException

        raise NoTermException



    elif isinstance(term, terms.MulTerm):
        pass


def unify(B, terms, uvars, arg_uvars, envs=[{}]):
    """
    Takes Terms s1...sn involving uvars u1...um
    arg_uvars is a subset of uvars: those that occur alone as function arguments in s1...sn.
    Optional envs is a list of maps from UVar indices to (const, IVar index) pairs.
    Returns a list of assignments under which each si is equal to a problem term in B.
    """

    def occurs_as_arg(term, varkey):
        """
        Returns true if term is a FuncTerm and var occurs alone as an argument.
        """
        if not isinstance(term, terms.FuncTerm):
            return False
        return any(a.term.key == varkey for a in term.args)

    if len(uvars) == 0:
        return envs

    if len(arg_uvars) == 0:
        #todo: we should find a way to handle the case where no variables occur alone in func terms.
        return envs

    v = arg_uvars[0]
    vkey = terms.UVar(v).key
    try:
        t = next(term for term in terms if occurs_as_arg(term, vkey))
    except StopIteration:
        raise Exception('arg_uvars not set up right.'+str(terms)+str(uvars)+str(arg_uvars))
    ind = next(j for j in range(len(t.args)) if t.args[j].term.key == vkey)
    c = t.args[ind].coeff

    # we have: t = f(..., c*u_v, ...)

    prob_f_terms = [i for i in range(B.num_terms) if
                    (isinstance(B.term_defs[i], terms.FuncTerm)
                     and B.term_defs[i].func_name == t.func_name
                     and len(B.term_defs[i].args) == len(t.args))]

    s = [(fractions.Fraction(B.term_defs[i].args[ind].coeff, c),
          B.term_defs[i].args[ind].term.index) for i in prob_f_terms]

    # s is a list of pairs (coeff, j) such that c*coeff*tj occurs as an argument to f in a pr. term

    nenvs = []
    for (coeff, j) in s:
        new_terms = [substitute(p, v, coeff, j) for p in terms]
        closed_terms, open_terms = list(), list()

        for (a, b) in new_terms:
            if b:
                closed_terms.append(a)
            else:
                open_terms.append(a)

        try:
            prob_terms = [find_problem_term(B, ct) for ct in closed_terms]
        except NoTermException:
            continue

        #todo: prob_terms isn't actually used in what follows. Could it be?

        # At this point, every closed term matches something in the problem.
        cenvs = copy.deepcopy(envs)
        for c in cenvs:
            c[v] = (coeff, j)
            maps = unify(B, open_terms, [v0 for v0 in uvars if v0 != v], arg_uvars[1:], cenvs)
            nenvs.extend(maps)
    return nenvs


def instantiate(axiom, B):
    # Get a list of assignments that work for all of axiom's triggers.
    envs = unify(B, axiom.triggers, axiom.vars, axiom.trig_arg_vars)

    # For each assignment, use it to instantiate a Clause from axiom and assert it in B.


class FunctionModule:

    def __init__(self, axioms=list()):
        """
        axioms is a list of Axiom objects.
        """
        self.axioms = axioms

    def add_axiom(self, axiom):
        self.axioms.append(axiom)

    def update_blackboard(B):
        messages.announce_module('polyhedron additive module')