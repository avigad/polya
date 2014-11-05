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
        """
        Instantiates an Example object. Used to create lists of test problems.
        Arguments:
         -- hyps: a list of TermComparisons, the hypotheses
         -- conclusion: a TermComparison, to try to derive. Defaults to False, ie, show hyps
           is contradictory.
         -- axioms: a list of extra axioms to use.
         -- modules: a list of modules to use. Defaults to all available modules.
         -- omit: the example will not run if omit=True. Defaults to False.
         -- comment: prints comment when the example is run.
         -- split_depth, split_depth: as in Solver.
         -- solver: 'fm' or 'poly' arithmetic
        """
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
        """
        Prints the example.
        """
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
        """
        Creates a Solver object with the stored values, and runs check().
        """
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
        
def run_examples(examples, args):
    """
    Takes a list of Example objects, tests each one in succession, and prints data.
    Used from the command line, as in sample_problems.py
    """
    # handle switches
    if '-v' in args:
        messages.set_verbosity(messages.normal)
        args.remove('-v')
    else:
        messages.set_verbosity(messages.quiet)
    if '-fm' in args:
        for e in examples:
            e.set_solver_type('fm')
        args.remove('-fm')


    # perform command
    if len(args) == 1 or '-h' in args:
        script_name = args[0]
        print "Use 'python {0} list' to list the examples.".format(script_name)
        print "Use 'python {0} 6 9 10' to run those examples.".format(script_name)
        print "Use 'python {0} test_all' to run them all.".format(script_name)
        print "Use switch -v to produce verbose output."
        print "Use switch -fm to use Fourier Motzkin"
    else:
        #show_configuration()
        if args[1] == 'list':
            for i in range(len(examples)):
                print '*** Example {0!s} ***'.format(i)
                examples[i].show()
        elif args[1] == 'test_all':
            t = timeit.default_timer()
            for i in range(len(examples)):
                if not examples[i].omit:
                    print '*** Example {0!s} ***'.format(i)
                    examples[i].test()
            print 'Total:', round(timeit.default_timer()-t, 3), 'seconds'
        # for a comparison of Fourier-Motzkin and polytope methods
        elif args[1] == 'test_all_comp':
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
            for i in range(1, len(args)):
                try:
                    examples[int(args[i])].test()
                except ValueError:
                    print 'No example {0}.'.format(args[i])
        messages.set_verbosity(messages.debug)

        if args[1] != 'list':
            timer.announce_times()