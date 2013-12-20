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

import terms
import itertools
import fractions
import lrs
import cdd  # This is needed for matrix formatting. Can we get around this?


####################################################################################################
#
# Internal classes
#
####################################################################################################


class Line:
    """
    Represents the line a*x + b*y [] c, where [] can be any comparison or equality.
    """
    def __init__(self, a, b, c, comp=terms.EQ):
        self.a, self.b, self.c, self.comp = a, b, c, comp

    def satisfies_point(self, point):
        return terms.comp_eval[self.comp](self.a * point[0] + self.b * point[1], self.c)

    def slope(self):
        if self.b == 0:
            return float('inf')
        else:
            return fractions.Fraction(self.b, self.a)

    def get_direction(self, point):
        """
        Returns GT, EQ, or LT based on how point compares to the line, ignoring self.comp
        """
        val = self.a * point[0] + self.b * point[1]
        if val > self.c:
            return terms.GT
        elif val < self.c:
            return terms.LT
        else:
            return terms.EQ

    def __eq__(self, other):
        if isinstance(other, Line):
            return self.slope() == other.slope() and self.c == other.c
        return False


class VertexSetException(Exception):
    def __init__(self, s=''):
        self.message = s

####################################################################################################
#
# Helper functions for manipulating vertices
#
####################################################################################################


def line_of_point(point, comp=terms.EQ):
    return Line(point[0], point[1], 0, comp)


def fall_on_same_side(line, points):
    """
    line is a Line
    points is a list of pairs
    returns true if all points are (weakly) on the same side of line.
    """
    eq_line = Line(line.a, line.b, line.c, terms.EQ)
    try:
        test_point = next(p for p in points if not eq_line.satisfies_point(p))
    except StopIteration:  # All points lie on line.
        return True

    direction = Line(line.a, line.b, line.c, terms.GE)
    if not direction.satisfies_point(test_point):
        direction = Line(line.a, line.b, line.c, terms.LE)

    return all(direction.satisfies_point(p) for p in points)


def are_collinear_rays(p1, p2):
    return line_of_point(p1) == line_of_point(p2) and p1[0]*p2[0] >= 0 and p1[1]*p2[1] >= 0


def get_boundary_vertices(vertices):
    """
    Takes a list of triples where the first two entries are (x,y) coordinates, and the third is
    delta.
    If all the vertices fall within the same semicircle, returns the pair that are at the extremes:
    the angle between these two vertices is greater than between any other pair.
    Otherwise, raises a VertexSetException.
    If any vertex on the boundary has nonzero delta coordinate, will return one of those.
    """

    if len(vertices) < 2:
        raise VertexSetException('Fewer than two vertices')

    b1, l_b1 = vertices[0], line_of_point(vertices[0])

    try:
        b2 = next(v for v in vertices if not are_collinear_rays(b1, v))
    except StopIteration:
        # All vertices point in the same direction.
        if any(v[2] != 0 for v in vertices):
            s = (b1[0], b1[1], 1)
        else:
            s = (b1[0], b1[1], 0)
        return s, s

    l_b2 = line_of_point(b2)
    for v in vertices:
        l_v = line_of_point(v)
        if fall_on_same_side(l_v, [b1, b2]):
            if not fall_on_same_side(l_b1, [v, b2]):
                b1, l_b1 = v, l_v
            elif not fall_on_same_side(l_b2, [v, b1]):
                b2, l_b2 = v, l_v
            elif v[2] != 0:
                if are_collinear_rays(b1, v):
                    b1, l_b1 = v, l_v
                elif are_collinear_rays(b2, v):
                    b2, l_b2 = v, l_v

    if (not fall_on_same_side(l_b1, vertices)) or (not fall_on_same_side(l_b2, vertices)):
        raise VertexSetException('Points not in semicircle.')

    return b1, b2


####################################################################################################
#
# Main functions
#
####################################################################################################


def get_2d_comparisons(vertices, lin_set):
    """
    Takes a matrix of vertices. Each row is of the form
     [0, delta, c_0, ..., c_n]

    lin_set tracks the linear set for lrs.
    Returns all possible TermComparisons from the given vertices.
    """

    def adjust_strength(strong, comp):
        if strong:
            if comp == terms.GE:
                return terms.GT
            elif comp == terms.LE:
                return terms.LT
        else:
            if comp == terms.GT:
                return terms.GE
            elif comp == terms.LT:
                return terms.LE
        return comp

    if all(v[1] == 0 for v in vertices):  # We have a degenerate system.
        return [terms.IVar(0) == 0]

    learned_comparisons = []

    # Look for comparisons between t_i and t_j by checking each vertex.
    for (i, j) in itertools.combinations(range(len(vertices[0])), 2):

        i_j_vertices = set()
        weak = False
        for v in vertices:
            if v[i+2] != 0 or v[j+2] != 0:
                i_j_vertices.add((v[i+2], v[j+2], v[1]))
            elif v[1] != 0:
                #(c,0,0) is a vertex, so (c-epsilon,0,0) is reachable.
                weak = True

        for k in lin_set:
            v = vertices[k]
            if v[i+2] != 0 or v[j+2] != 0:
                i_j_vertices.add((v[i+2], v[j+2], v[1]))

        # Find the extremal vertices.
        try:
            bound1, bound2 = get_boundary_vertices(i_j_vertices)
        except VertexSetException:  # Nothing we can learn for this i, j pair.
            continue

        # Now, all vertices lie in the same halfplane between bound1 and bound2.
        strong1, strong2 = (not weak) and (bound1[2] == 0), (not weak) and (bound2[2] == 0)
        l_b1, l_b2 = line_of_point(bound1), line_of_point(bound2)

        if l_b1 == l_b2:
            if bound1[0]*bound2[0] >= 0 and bound1[1]*bound2[1] >= 0:
                # the rays are collinear. Learn equality.
                learned_comparisons.append(bound1[0] * terms.IVar(i) == bound2[0] * terms.IVar(j))
                if strong1 or strong2:
                    learned_comparisons.append(
                        bound1[0] * terms.IVar(i) < bound2[0] * terms.IVar(j)
                    )

            else:
                #the rays are opposite. Figure out the comparison direction another way.
                try:
                    pt = next(v for v in vertices if l_b1 != line_of_point(v))
                except StopIteration:
                    # There is no direction information to be found: all vertices are collinear.
                    continue
                dir1 = adjust_strength(strong1 and strong2, l_b1.get_direction(pt))
                learned_comparisons.append(
                    terms.comp_eval[dir1](bound1[0] * terms.IVar(i), bound1[1] * terms.IVar(j))
                )

        else:
            # Otherwise, the points do not lie on the same line through the origin.
            dir1 = adjust_strength(strong1, l_b1.get_direction(bound2))
            dir2 = adjust_strength(strong2, l_b2.get_direction(bound1))
            learned_comparisons.append(
                terms.comp_eval[dir1](bound1[0] * terms.IVar(i), bound1[1] * terms.IVar(j))
            )
            learned_comparisons.append(
                terms.comp_eval[dir2](bound2[0] * terms.IVar(i), bound2[1] * terms.IVar(j))
            )

    return learned_comparisons


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