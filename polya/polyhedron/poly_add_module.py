####################################################################################################
#
# poly_add_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The routine for learning facts about additive terms using polytope projections.
# Much of the work is done in lrs_polyhedron_util.py, as it is shared with the multiplicative
# module.
#
# TODO:
#
####################################################################################################

import terms
import messages
import lrs_polyhedron_util as lrs_util


def learn_additive_sign_info(blackboard):
    """
    Looks at additive definitions and tries to mine sign information.
    """
    for j in (
        i for i in range(blackboard.num_terms) if isinstance(blackboard.term_defs[i], terms.AddTerm)
    ):
        if blackboard.sign(j) == 0:
            args = blackboard.term_defs[j].args
            sign = args[0].coeff * blackboard.weak_sign(args[0].term.index)
            if (sign != 0 and all(args[i].coeff * blackboard.weak_sign(args[i].term.index) == sign
                for i in range(len(args)))):
                if any(blackboard.sign(args[i].term.index) != 0 for i in range(len(args))):
                    blackboard.assert_comparison(
                        terms.comp_eval[(terms.GT if sign > 0 else terms.LT)](terms.IVar(j), 0)
                    )
                else:
                    blackboard.assert_comparison(
                        terms.comp_eval[(terms.GE if sign > 0 else terms.LE)](terms.IVar(j), 0)
                    )

        # There's more in the old version here. Is it really necessary?


def update_blackboard(blackboard):
    messages.announce_module('polyhedron additive module')

    learn_additive_sign_info(blackboard)

    comparisons = get_additive_information(blackboard)
    h_matrix = lrs_util.create_h_format_matrix(comparisons, blackboard.num_terms)
    v_matrix, v_lin_set = lrs_util.get_vertices(h_matrix)
    messages.announce('Vertex matrix:', messages.DEBUG)
    messages.announce(str(v_matrix), messages.DEBUG)
    messages.announce('Linear set:', messages.DEBUG)
    messages.announce(str(v_lin_set), messages.DEBUG)

    new_comparisons = lrs_util.get_2d_comparisons(v_matrix, v_lin_set)

    for c in new_comparisons:
        blackboard.assert_comparison(c)


# This method is a placeholder for when proper accessors are defined in blackboard.
def get_additive_information(blackboard):
    comparisons = []

    for key in blackboard.term_defs:
        if isinstance(blackboard.term_defs[key], terms.AddTerm):
            comparisons.append(
                terms.TermComparison(blackboard.term_defs[key], terms.EQ, terms.IVar(key))
            )
        #TODO: include term equality and zero equality information here

    #This will depend on the structure of term_inequalities
    for key in blackboard.term_inequalities:
        comparisons.append(blackboard.term_inequalities[key])

    for key in blackboard.term_zero_inequalities:
        comparisons.append(blackboard.term_zero_inequalities[key])

    return comparisons