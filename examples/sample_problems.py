####################################################################################################
#
# sample_problems.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Examples for Polya.
#
#
####################################################################################################


from polya import *
import sys
import timeit


class Example:

    def __init__(self, name = 'Polya sample problem', hyps = [], conc = None, ax = [],
                 modules = []):
        self.name = name
        self.hyps = hyps
        self.conc = conc
        self.ax = ax
        self.modules = modules

    def show(self):
        print 'Problem: {0}'.format(self.name)
        for a in self.ax:
            print 'Axiom: {0!s}'.format(a)
        for h in self.hyps:
            print 'Hypothesis: {0!s}'.format(h)
        if self.conc:
            print 'Conclusion: {0!s}'.format(self.conc)
        else:
            print 'Conclusion: False'
        print

    def test(self):
        self.show()
        S = Solver(assertions=self.hyps, axioms=self.ax, modules=self.modules)
        t = timeit.default_timer()
        if self.conc:
            if S.prove(self.conc):
                print 'Conclusion is valid.'
            else:
                print 'Failed.'
        else:
            if S.check():
                print 'Refuted hypotheses.'
            else:
                print 'Failed.'
        print 'Ran in', round(timeit.default_timer()-t, 3), 'seconds'
        print




####################################################################################################
#
# The list of examples
#
####################################################################################################


i = 0  # temporary counter

r, s, t, u, v, w, x, y, z = Vars('r, s, t, u, v, w, x, y, z')

examples = []

examples.append(Example(
    hyps = [0 < x, x < 3*y, u < v, v < 0, 1 < v**2, v**2 < x],
    conc = u*(3*y)**2 + 1 < x**2 * v + x
))

examples.append(Example(
    hyps = [0 < x, x < y, 0 < u, u < v, 0 < w + z, w + z < r - 1],
    conc = u + (1+x)**2 * (2*w + 2*z + 3) < 2*v + (1+y)**2 * (2*r + 1)
))


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
    if len(sys.argv) == 1:
        print "Use 'python examples.py list' to list the examples."
        print "Use 'python examples.py 6 9 10' to run those examples."
        print "Use 'python examples.py test_all' to run them all."
    elif sys.argv[1] == 'list':
        for i in range(len(examples)):
            examples[i].show()
    elif sys.argv[1] == 'test_all':
        for i in range(len(examples)):
            examples[i].test()
    else:
        for i in range(1, len(sys.argv)):
            try:
                examples[int(sys.argv[i])].test()
            except ValueError:
                print 'No example {0}.'.format(sys.argv[i])
