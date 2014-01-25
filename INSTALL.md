Installation instructions
=========================

Setting your Python path
------------------------

To run Polya, the Polya module needs to be in your Python path. For example, in a Unix bash shell, use

    export PYTHONPATH=PYTHONPATH:path/to/directory

where "directory" contains the contents of the distribution, including the folder named "polya". If you will be using Polya regularly, it is convenient to add this line to your .bashrc.

Polya is more efficient when it can use certain external packages; see below.


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

    python sample_problems 2 5 7
    
to run Polya on problems 2, 5, and 7 sequentially, and 

    python sample_problems.py all
    
to run Polya on all of them.


Installing the geometry packages
--------------------------------

Polya can make use of more efficient geometric methods to handle additive and multiplicative information. To to take advantage of these capabilities, you need to have the following software installed:

1. GMP

2. CDD

3. LRS and Redund

