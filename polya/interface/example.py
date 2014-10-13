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
#
####################################################################################################

import polya.interface.solve_util as solve_util
import timeit
import polya.main.messages as messages
import polya.util.timer as timer


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

    def set_solver_type(self, s):
        self.solver = s

    def set_split(self, depth, breadth):
        self.split_depth, self.split_breadth = depth, breadth

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
        
def run_examples(examples, switches):
    # handle switches
    if '-v' in switches:
        messages.set_verbosity(messages.normal)
        switches.remove('-v')
    else:
        messages.set_verbosity(messages.quiet)
    if '-fm' in switches:
        for e in examples:
            e.set_solver_type('fm')
        switches.remove('-fm')


    # perform command
    if len(switches) == 1:
        print "Use 'python sample_problems.py list' to list the examples."
        print "Use 'python sample_problems.py 6 9 10' to run those examples."
        print "Use 'python sample_problems.py test_all' to run them all."
    else:
        #show_configuration()
        if switches[1] == 'list':
            for i in range(len(examples)):
                print '*** Example {0!s} ***'.format(i)
                examples[i].show()
        elif switches[1] == 'test_all':
            t = timeit.default_timer()
            for i in range(len(examples)):
                if not examples[i].omit:
                    print '*** Example {0!s} ***'.format(i)
                    examples[i].test()
            print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
        # for a comparison of Fourier-Motzkin and polytope methods
        elif switches[1] == 'test_all_comp':
            t = timeit.default_timer()
            for i in range(len(examples)):
                if not examples[i].omit:
                    print '*** Example {0!s} ***'.format(i)
                    examples[i].set_solver_type('fm')
                    print '[Fourier-Motzkin]'
                    examples[i].test()
                    examples[i].set_solver_type('poly')
                    print '[Poly]'
                    examples[i].test()
            print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
        else:
            for i in range(1, len(switches)):
                try:
                    examples[int(switches[i])].test()
                except ValueError:
                    print 'No example {0}.'.format(switches[i])
        messages.set_verbosity(messages.debug)

        timer.announce_times()