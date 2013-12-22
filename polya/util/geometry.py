import terms
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