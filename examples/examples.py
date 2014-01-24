####################################################################################################
#
# examples.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Examples for Polya.
#
# TODO: add timing
# TODO: add names to the examples?
#
####################################################################################################


from polya import *
import polya.main.terms as terms
import sys


def negate_comparison(c):
    return terms.TermComparison(c.term1, terms.comp_negate(c.comp), c.term2)


class Example:

    def __init__(self, hyps = [], conc = None, ax = [], modules = None):
        self.hyps = hyps
        self.conc = conc
        self.ax = ax
        self.modules = modules

    def test(self):
        S = Solver()
        for a in self.ax:
            print 'Axiom: {0!s}'.format(h)
            S.add_axiom(a)
        for h in self.hyps:
            print 'Hypothesis: {0!s}'.format(h)
            S.assert_comparison(h)
        if self.conc:
            S.assert_comparison(negate_comparison(self.conc))
            print 'Conclusion: {0!s}'.format(self.conc)
        else:
            print 'Conclusion: False'
        # TODO: handle modules
        print
        S.check()
        print


####################################################################################################
#
# The list of examples
#
####################################################################################################


r, s, t, u, v, w, x, y, z = Vars('r, s, t, u, v, w, x, y, z')

examples = {}

examples[0] = Example(
    hyps = [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x],
    conc = u*(3*y)**2 + 1 < x**2 * v + x
)

examples[1] = Example(
    hyps = [0 < x, x < y, 0 < u, u < v, 0 < w + z, w + z < r - 1],
    conc = u + (1+x)**2 * (2*w + 2*z + 3) < 2*v + (1+y)**2 * (2*r + 1)
)


####################################################################################################
#
# To run from the command line, use
#
#   python examples 6 9 10
#
# e.g. to run examples 6 9 10, or
#
#   python examples all
#
# to run all.
#
####################################################################################################


if __name__ == '__main__':
    if len(sys.argv) == 0:
        print "Use 'python examples 6 9 10' to run those examples."
        print "Use 'python examples all' to run them all."
    elif sys.argv[1] == 'all':
        for i in examples:
            examples[i].test()
    else:
        for i in range(1, len(sys.argv)):
            try:
                examples[int(sys.argv[i])].test()
            except ValueError:
                print 'No example {0}.'.format(sys.argv[i])
