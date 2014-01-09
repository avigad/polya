#from ..main import terms
from polya.main import terms
import fractions


class Line:
    """
    Represents the line a*x + b*y [] c, where [] can be any comparison or equality.
    """
    def __init__(self, a, b, c, comp=terms.EQ):
        self.a, self.b, self.c, self.comp = a, b, c, comp

    def satisfies_point(self, point):
        return terms.comp_eval[self.comp](self.a * point[0] + self.b * point[1], self.c)

    def slope(self):
        if self.a == 0:
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

    def unit_points(self):
        if self.b != 0:
            return (1, self.slope()), (-1, -self.slope())
        else:
            return (0, 1), (0, -1)

    def has_new_info(self, line1, line2):
        """
        Returns false if all points satisfying line1 and line2 also satisfy self.
        Returns true otherwise.
        Assumes all three lines go through the origin and are inequalities;
         raises Exception otherwise.
        """
        if self.c != 0 or line1.c != 0 or line2.c != 0:
            raise Exception
        
        slope_s, slope_1, slope_2 = self.slope(), line1.slope(), line2.slope()
        
        if slope_s == slope_1:
            if self.comp == line1.comp:
                return False
            elif ((self.comp == terms.GE and line1.comp == terms.GT) or 
                    (self.comp == terms.LE and line1.comp == terms.LT)):
                return False

        if slope_s == slope_2:
            if self.comp == line2.comp:
                return False
            elif ((self.comp == terms.GE and line2.comp == terms.GT) or 
                    (self.comp == terms.LE and line2.comp == terms.LT)):
                return False
            
        if slope_s == slope_1 or slope_s == slope_2:
            # self is collinear with at least one of the others, and not subsumed by either.
            return True
        
        if slope_1 == slope_2:
            up1, up2 = line1.unit_points()
        else:
            up11, up12 = line1.unit_points()
            up21, up22 = line2.unit_points()
            up1 = up11 if line2.satisfies_point(up11) else up12
            up2 = up21 if line1.satisfies_point(up21) else up22

        return not (self.satisfies_point(up1) and self.satisfies_point(up2))

    def __eq__(self, other):
        if isinstance(other, Line):
            return self.slope() == other.slope() and self.c == other.c
        return False

    def __str__(self):
        return "{0}x + {1}y {3} {2}".format(self.a, self.b, self.c, terms.comp_str[self.comp])


def line_of_point(point, comp=terms.EQ):
    return Line(point[1], -point[0], 0, comp)


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


def find_two_strongest(lines):
    l1, l2 = lines[0], lines[1]
    for l in lines[2:]:
        if not l1.has_new_info(l, l2):
            l1 = l
        elif not l2.has_new_info(l, l1):
            l2 = l
    return l1, l2

class Halfplane:
    """
    Defines the halfplane counterclockwise of the vector (a, b).
    If strong is true, the line bx - ay = 0 is not included in the halfplane.
    """

    def __init__(self, a, b, strong):
        self.a, self.b, self.strong = a, b, strong

    def __str__(self):
        return "({0}, {1}), {2}".format(self.a, self.b, "strong" if self.strong else "weak")

    def __repr__(self):
        return str(self)

    def cross(self, x, y):
        return self.a * y - self.b * x

    def contains_point(self, x, y):
        """
        Returns true if (x, y) lies in the halfplane counterclockwise of (a, b), false otherwise.
        Respects strength: if self.strong, returns false if the points are collinear.
        """
        v = self.cross(x, y)
        if v == 0:
            # The vectors are collinear.
            return not self.strong
        else:
            return self.cross(x, y) > 0
            #same_dir = True if (self.a * x >= 0 and self.b * y >= 0) else False

    def compare_hp(self, hp):
        """
        Compares two halfplanes.
        Returns 1 if hp is counterclockwise of self.
        Returns -1 if self is counterclockwise of hp.
        Returns 0 if the two are collinear: note that there is more information to find here
        (wrt strength, direction)
        """
        v = self.cross(hp.a, hp.b)
        if v > 0:
            return 1
        elif v < 0:
            return -1
        else:
            return 0

    def eq_dir(self, hp):
        """
        Returns true if self and hp point in the same direction, false otherwise.
        """
        return self.cross(hp.a, hp.b) == 0 and self.a * hp.a >= 0 and self.b * hp.b >= 0

    def to_comp(self, t1, t2):
        if self.a == 0:  # vertical
            if self.contains_point(1, 0):
                return t1 > 0 if self.strong else t1 >= 0
            else:
                return t1 < 0 if self.strong else t1 <= 0

        elif self.b == 0:  # horizontal
            if self.contains_point(0, 1):
                return t2 > 0 if self.strong else t2 >= 0
            else:
                return t2 < 0 if self.strong else t2 <= 0
        else:
            # p = (-self.b, self.a)  # p is pi/2 ccw of self
            if -self.b > fractions.Fraction(self.a * self.a, self.b):
                comp = terms.GT if self.strong else terms.GE
            else:
                comp = terms.LT if self.strong else terms.LE
            return terms.comp_eval[comp](t1, fractions.Fraction(self.a, self.b) * t2)


def halfplane_of_comp(comp, coeff):
    """
    Returns a halfplane object representing the inequality x comp coeff * y
    Assumes comp is LT, LE, GE, or GT
    """
    if coeff == 0:
        if comp in [terms.GT, terms.GE]:
            return Halfplane(0, -1, (True if comp == terms.GT else False))
        else:
            return Halfplane(0, 1, (True if comp == terms.LT else False))

    normal = (1, -coeff) if terms.comp_eval[comp](1, -coeff * coeff) else (-1, coeff)
    hp = Halfplane(coeff, 1, (True if comp in [terms.GT, terms.LT] else False))
    if hp.contains_point(*normal):
        return hp
    else:
        return Halfplane(-coeff, -1, (True if comp in [terms.GT, terms.LT] else False))