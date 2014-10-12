####################################################################################################
#
# example.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Class to easily construct examples.
#
# TODO: improve command line interface
#
####################################################################################################

import polya.interface.solve_util as solve_util
import timeit


class Example:

    def __init__(self, hyps, conc, axioms, modules, omit, comment,
                 split_depth, split_breadth, solver):
        self.hyps = hyps if hyps else list()
        self.conc = conc
        self.axioms = axioms if axioms else list()
        self.modules = modules if modules else list()
        self.comment=comment
        self.omit = omit    # flag to omit from 'test_all'
        self.split_depth = split_depth
        self.split_breadth = split_breadth
        self.solver = solver

    def show(self):
        for a in self.axioms:
            print 'Axiom: {0!s}'.format(a)
        for h in self.hyps:
            print 'Hypothesis: {0!s}'.format(h)
        if self.conc:
            print 'Conclusion: {0!s}'.format(self.conc)
        else:
            print 'Conclusion: False'
        if self.comment:
            print 'Comment: {0}'.format(self.comment)
        if self.omit:
            print "(Omitted from 'test_all')"
        print

    def test(self):
        self.show()
        S = solve_util.Solver(self.split_depth, self.split_breadth, self.hyps, self.axioms,
                              self.modules, self.solver)
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