Reference
=========================

The following methods are available in the Polya package. We assume

    from polya import *


Introducing terms
------------------------

    Var(name)

Constructs a Polya variable represented by name. Variables can be added, subtracted, multiplied,
divided, and taken to integer powers to create new terms.

    Vars(names)

Constructs a tuple of variables. names is a string, with names delineated by whitespace.

    Func(name)

Constructs a function symbol represented by name. Called on a term, will return a function
application term.

    term1 [] term2

When [] is replaced with <, <=, >=, >, =, !=, constructs a TermComparison object.

Blackboard
------------------------

    Blackboard()

Constructs a Blackboard object. A Blackboard has the following methods available:

    assume(*term_comparisons)

Adds the information in each term_comparison to the Blackboard. Throws a Contradiction if the
information is inconsistent with the current state of the Blackboard.

    get_inequalities(), get_disequalities(), get_equalities()

Returns a list of TermComparisons representing all known inequalities (resp. disequalities,
equalities).


