####################################################################################################
#
# lrs_polyhedron_util.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# Contains many methods for manipulating polytopes using lrs.
# Nearly all of the machinery for the additive polyhedron module lives here, and much is shared with
# the multiplicative routine.
#
# TODO:
#
####################################################################################################

import polya.main.terms as terms
import polya.modules.polyhedron.lrs as lrs

# where should this go?
try:
    import cdd  # This is needed for matrix formatting. Can we get around this?
except ImportError:
    cdd = None
    #pass


def get_vertices(comparison_matrix):
    """
    To use the cdd/lrs matrix representation, we need to make a matrix of the form
       (b | -A)
    where b-Ax >= 0.
    Since our situation is homogenous, b = 0.
    So, Ax <= 0
    And since we store -A, the matrix rows are >= 0.
    The 0th column of the matrix is b. Should always be 0.
    The 1st column of the matrix is delta, strict vs. non-strict inequality info:
    row[1] = -1 iff it is > 0

    So each row of the input should be of the form [0, (-1|0), c_0, ..., c_n],
    where c_0 * t_0 + ... + c_n * t_n >= 0.

    Equality rows should be added with linear=True.
    The matrix must contain the row [0, 1, 0, 0, ..., 0] for proper strength information.
    """
    return lrs.get_generators(comparison_matrix)


def create_h_format_matrix(comparisons, num_vars):
    """
    comparisons is a list of TermComparisons.
    num_vars is the number of IVars defined.
    """

    inequalities, equalities = [], []

    for c in comparisons:
        term = c.term1 - c.term2
        comp = c.comp
        if isinstance(term, terms.STerm):
            if term.coeff < 0:
                comp = terms.comp_reverse(comp)
            term = term.term

        if isinstance(term, terms.IVar):
            term = terms.AddTerm([terms.STerm(1, term)])

        if comp in [terms.LE, terms.LT]:
            comp = terms.comp_reverse(comp)
            for st in term.args:
                st.coeff *= -1
        elif comp not in [terms.GE, terms.GT, terms.EQ]:
            # Add routine does not handle disequality
            continue


        row = [0] * (num_vars + 2)
        row[1] = (-1 if comp == terms.GT else 0)

        if isinstance(term, terms.AddTerm):
            for p in term.args:
                row[p.term.index + 2] = p.coeff
        elif isinstance(term, terms.IVar):
            row[term.index+2] = 1

        if comp == terms.EQ:
            equalities.append(row)
        else:
            inequalities.append(row)

    row = [0]*(num_vars + 2)
    row[1] = 1
    inequalities.append(row)

    matrix = cdd.Matrix(inequalities, number_type='fraction')
    matrix.rep_type = cdd.RepType.INEQUALITY

    if equalities:
        matrix.extend(equalities, linear=True)

    return matrix