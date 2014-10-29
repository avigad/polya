The Polya Inequality Prover
===========================

Authors: Jeremy Avigad, Robert Y. Lewis, Cody Roux

Polya is a system designed to support interactive theorem proving by verifying the kinds of inequalities that arise in ordinary mathematical arguments. The method is described in the paper "A heuristic prover for real inequalities," available [online](http://www.andrew.cmu.edu/user/avigad/Papers/polya.pdf). The version of the system described in the paper is tagged "v0.2".

The system is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0.html). It is still an experimental prototype, and feedback is very welcome.

For instructions on setting up and using Polya, see the file 'INSTALL.md'.

Once Polya is installed, you can use it directly in the Python 2.7 interactive mode. Start Python:

    python
    
and at the prompt type

    from polya import *
    
at which point you can enter the command

    show_configuration()
    
to see which external packages are present.

There are a tutorial and sample problems in the folder 'examples'. See the 'README.md' in that folder for more information.

For benchmark comparisons, see 'examples/results.md' and the data in the folder 'examples/other_systems'.






    