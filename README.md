The Polya Inequality Prover
===========================

Authors: Jeremy Avigad, Robert Y. Lewis, Cody Roux

Polya is a system designed to support interactive theorem proving by verifying the kinds of inequalities that arise in ordinary mathematical arguments. The method is described in the paper "A heuristic prover for real inequalities," available [online](http://www.andrew.cmu.edu/user/avigad/Papers/polya.pdf). The system is still an experimental prototype, and feedback is very welcome.

The system is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0.html).

For instructions on setting up and using Polya, see INSTALL.md. There are tutorial examples in

    examples/examples.py
    
and additional information in the folder "doc". 


Using Polya
-----------

Once Polya is installed, you can use it directly in the Python 2.7 interactive mode. Start Python:

    python
    
and at the prompt type

    from polya import *
    
at which point you can try entering some of the examples described in the file

    examples/examples.py
    
From the examples folder, you can also try some sample problems directly from the system prompt. Type

    python sample_problems.py list
    
for a list of problems,

    python sample_problems.py 2 5 7
    
to run Polya on problems 2, 5, and 7 sequentially, and 

    python sample_problems.py test_all
    
to run Polya on all of the sample problems. You can use the flag "-v" for a more verbose output that shows each module's assertions:

    python sample_problems.py -v 2 5 7
    python sample_problems.py -v test_all
    
If the geometric packages are installed, these are used by default. You can force the use of the Fourier-Motzkin modules instead by adding the switch "-fm" anywhere on the command line.
    