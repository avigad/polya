Getting Started
===============

Using Polya
-----------

Once Polya is installed, you can use it directly in the Python 2.7 interactive mode. Start Python:

    python
    
and at the prompt type

    from polya import *
    
at which point you can try entering some of the examples described in the [tutorial].(tutorial.html).


Trying the sample problems
--------------------------
    
From the examples folder, you can also try some sample problems directly from the system prompt. Type

    python sample_problems.py list
    
for a list of problems,

    python sample_problems.py 2
    
to try sample problem 2, 

    python sample_problems.py 2 5 7
    
to run Polya on problems 2, 5, and 7 sequentially, and 

    python sample_problems.py test_all
    
to run Polya on all of the sample problems. 

You can use the flag "-v" for a more verbose output that shows each module's assertions:

    python sample_problems.py -v 2 5 7
    python sample_problems.py -v test_all
    
If the geometric packages are installed, these are used by default. You can force the use of the Fourier-Motzkin modules instead by adding the switch "-fm" anywhere on the command line. Type

    python sample_problems.py test_all_comp
    
to run all the examples with both the Fourier-Motzkin modules and the geometric polytope modules.
    