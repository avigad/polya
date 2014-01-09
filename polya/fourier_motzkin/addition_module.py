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
# TODO: for now, we use fractions. This can probably be optimized by using integers and reducing
#   by gcd's.
# TODO: another optimization: use Z3 to filter redundant inequalities
#
####################################################################################################

from polya.main import terms
from polya.main import blackboard

# from itertools import combinations

####################################################################################################
#
# ADDITIVE ELIMINATION
#
####################################################################################################

        
def add_subst(t1, t2, v):
    """
    Takes additive terms t1 and t2, and a term v (usually a variable), which is assumed to occur in
    t1. Returns the result of solving for v in the equation t1 = 0 and substituting in t2.
    """
    s1 = next(s for s in t1.args if s.term.key == v.key)
    try:
        s2 = next(s for s in t2.args if s.term.key == v.key)
    except ValueError:
        return t2
    return t2 - (s2.coeff / s1.coeff * t1)

# def add_elim(equations, zero_comparisons, v):
#     # print 'running add_elim to eliminate',v,'. eqns len=',len(equations),'comps len=',len(zero_comparisons)
#
#     def occurs_in(v, t):
#         return v in (a.term for a in t.addpairs)
#
#     # Find the shortest equation that contains v, if it exists. solve it for v and substitute into others
#     shortest_eqn = None
#     for e in equations:
#         if occurs_in(v, e) and ((not shortest_eqn) or len(e.addpairs) < len(shortest_eqn.addpairs)):
#             shortest_eqn = e
#
#     if shortest_eqn:
#         e = shortest_eqn
#         new_equations = [add_subst(e, e2, v) for e2 in equations if e != e2]
#         new_comparisons = [Zero_comparison(add_subst(e, c.term, v), c.comp) for c in zero_comparisons]
#
#         # Filters new_equations and new_comparisons for repeats. Not currently used.
#         # new_equations = []
#         # for e2 in equations:
#         #    if e!=e2:
#         #        ne = add_subst(e,e2,v)
#         #        #if ne not in new_equations:
#         #        new_equations.append(ne)
#         #
#         # new_comparisons = []
#         # for c in zero_comparisons:
#         #    nc = Zero_comparison(add_subst(e,c.term,v),c.comp)
#         #    #if str(nc) not in [str(t) for t in new_comparisons]:
#         #        new_comparisons.append(nc)
#
#         return new_equations, new_comparisons
#
#     # Otherwise, there is no equation that contains v.
#
#     pos_comparisons = []  # v occurs positively
#     neg_comparisons = []  # v occurs negatively
#     new_comparisons = []
#
#     # If we are filtering for repeats, it is much more efficient to store comparisons in a hashmap.
#     # new_comparisons = {}
#     # def add_to_new_comps(zerocomp):
#     #    try:
#     #        s = new_comparisons[str(zerocomp)]
#     #    except KeyError:
#     #        new_comparisons[str(zerocomp)]=zerocomp
#
#     for c in zero_comparisons:
#         try:
#             a = next((a for a in c.term.addpairs if a.term == v))
#             if a.coeff > 0:
#                 pos_comparisons.append(c)
#             else:
#                 neg_comparisons.append(c)
#         except StopIteration:  # v does not occur at all
#             # if c not in new_comparisons:
#             new_comparisons.append(c)
#             # add_to_new_comps(c)
#
#     for c1 in pos_comparisons:
#         for c2 in neg_comparisons:
#             # print c1,c2
#             if c1.comp == GE and c2.comp == GE:
#                 new_comp = GE
#             else:
#                 new_comp = GT
#             new_zc = Zero_comparison(add_subst(c1.term, c2.term, v), new_comp)
#             # if new_zc not in new_comparisons:
#             new_comparisons.append(new_zc)
#             # add_to_new_comps(new_zc)
#
#     return equations, new_comparisons  # [new_comparisons[c] for c in new_comparisons.keys()]
#
# # Try to mine sign data from additive definitions.
# # provenance is HYP, so this info is available to the additive routine
# def learn_additive_sign_info(H):
#     for j in (i for i in range(H.num_terms) if (isinstance(H.name_defs[i], Add_term))):
#         if H.sign(j) == 0:
#             addpairs = H.name_defs[j].addpairs
#             sign = addpairs[0].coeff * H.weak_sign(addpairs[0].term.index)
#             if (sign != 0 and
#                 all(addpairs[i].coeff * H.weak_sign(addpairs[i].term.index) == sign for i in range(len(addpairs)))):
#                 if any(H.sign(addpairs[i].term.index) != 0 for i in range(len(addpairs))):
#                     H.learn_zero_comparison(j, (GT if sign > 0 else LT), HYP)
#                 else:
#                     H.learn_zero_comparison(j, (GE if sign > 0 else LE), HYP)
#         if H.weak_sign(j) != 0 and len(H.name_defs[j].addpairs) == 2:
#             pairi, pairk = H.name_defs[j].addpairs[0], H.name_defs[j].addpairs[1]
#             i, k = pairi.term.index, pairk.term.index
#             ci, ck = pairi.coeff, pairk.coeff
#             comp = H.zero_comparisons[j].comp
#             if i > k:
#                 i, k, pairi, pairk, ci, ck = k, i, pairk, pairi, ck, ci
#
#             c = -ck / ci
#             if ci < 0:
#                 comp = comp_reverse(comp)
#             H.learn_term_comparison(i, k, comp, c, HYP)
#
# def learn_add_comparisons(H):
#
#     #H.info_dump()
#
#     def learn_add_comparison(c):
#         length = len(c.term.addpairs)
#         if length == 0:
#             if c.comp == GT:
#                 H.raise_contradiction(ADD)
#                 #pass
#         elif length == 1:
#             a = c.term.addpairs[0]
#             i = a.term.index
#             if a.coeff > 0:
#                 comp = c.comp
#             else:
#                 comp = comp_reverse(c.comp)
#             H.learn_zero_comparison(i, comp, ADD)
#         elif length == 2:
#             a0 = c.term.addpairs[0]
#             i0 = a0.term.index
#             c0 = a0.coeff
#             a1 = c.term.addpairs[1]
#             i1 = a1.term.index
#             c1 = a1.coeff
#             coeff = -Fraction(c1, c0)
#             if c0 < 0:
#                 comp = comp_reverse(c.comp)
#             else:
#                 comp = c.comp
#             H.learn_term_comparison(i0, i1, comp, coeff, ADD)
#
#     if H.verbose:
#         print "Learning additive facts..."
#         print
#
#
#     # make additive equations
#     add_eqs = [H.name_defs[i] + Add_term([(-1, IVar(i))])
#         for i in range(H.num_terms) if isinstance(H.name_defs[i], Add_term)]
#
#     add_eqs.extend([c for c in H.zero_equations if isinstance(c, Add_term)])
#
#     if H.verbose:
#         print "Additive equations:"
#         for t in add_eqs:
#             print t, "= 0"
#         print
#
#     # Try to mine sign data from additive definitions.
#     learn_additive_sign_info(H)
#
#     # make additive comparisons
#     add_comps = []
#     for i in H.zero_comparisons.keys():
#         if H.zero_comparisons[i].provenance != ADD:
#             # otherise, additive routine can already see this fact
#             comp = H.zero_comparisons[i].comp
#             if comp in [GT, GE]:
#                 add_comps.append(Zero_comparison(Add_term([(1, IVar(i))]),
#                                                  comp))
#             else:
#                 add_comps.append(Zero_comparison(Add_term([(-1, IVar(i))]),
#                                                  comp_reverse(comp)))
#     for (i, j) in H.term_comparisons.keys():
#         for c in H.term_comparisons[i, j]:
#             if c.provenance != ADD:
#                 if c.comp in [GT, GE]:
#                     add_comps.append(Zero_comparison(
#                         Add_term([(1, IVar(i)), (-1 * c.coeff, IVar(j))]), c.comp))
#                 else:
#                     add_comps.append(Zero_comparison(
#                         Add_term([(-1, IVar(i)), (c.coeff, IVar(j))]),
#                                  comp_reverse(c.comp)))
#
#     if H.verbose:
#         print "Additive comparisons:"
#         for c in add_comps:
#             print c
#         print
#
#
#     for i in range(H.num_terms):
#         # get all comparisons with i
#         i_add_eqs = add_eqs
#         i_add_comps = add_comps
#         for j in range(i + 1, H.num_terms):
#             # get all comparisons with i and j
#             ij_add_eqs = i_add_eqs
#             ij_add_comps = i_add_comps
#             for k in range(j + 1, H.num_terms):
#
#                 ij_add_eqs, ij_add_comps = (
#                     add_elim(ij_add_eqs, ij_add_comps, IVar(k)))
#
#             # add any new information
#             for c in ij_add_comps:
#                 learn_add_comparison(c)
#             # eliminate j
#             i_add_eqs, i_add_comps = add_elim(i_add_eqs, i_add_comps, IVar(j))
#         add_eqs, add_comps = add_elim(add_eqs, add_comps, IVar(i))
#     if H.verbose:
#         print


####################################################################################################
#
# Tests
#
####################################################################################################

if __name__ == '__main__':

    x, y, z, w = terms.Vars('x, y, z, w')
    t1 = 3 * x + 4 * y - 2 * z
    t2 = -2 * x - 2 * y + 5 * z

    print 't1 = ', t1
    print 't2 = ', t2
    print 't1 + t2 = ', t1 + t2
    print 't1 * 3 + t2 * -1 = ', t1 * 3 + t2 * -1
    print 't1 + x =', t1 + x
    print 't1 + w =', t1 + w
    print 'eliminate x:', add_subst(t1, t2, x)
    print 'eliminate y:', add_subst(t1, t2, y)
    print 'eliminate z:', add_subst(t1, t2, z)
