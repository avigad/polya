In order to run Polya, import polya, and then:
    x, y, z = polya.main.terms.Vars('x, y, z')
    B = polya.main.blackboard.Blackboard()
    B.assert_comparisons(x<y, y<z, z<x)

    pa = polya.polyhedron.poly_add_module.PolyAddModule()
    pa.update_blackboard(B)

    f = polya.main.terms.Func('f')
    B.assert_comparison(f(x)>=f(y))

    import polya.main.formulas as a
    fm = polya.main.function_module.FunctionModule()
    fm.add_axiom(a.ForAll([x, y], a.Implies(x<y, f(x)<f(y))))
    fm.update_blackboard(B)

There are currently five modules that can be instantiated.

- fm_addition_module
This is the original Fourier-Motzkin additive elimination routine. It learns facts about additive
terms in the problem. It is susceptible to high runtimes.

- poly_add_module
This is a replacement for the above. It works by using lrs to construct a vertex representation of
the given inequalities, then projects these vertices to the i-j plane for each pair i,j. From there
it infers the appropriate comparisons. It depends on cdd to format the information passed to lrs.

- multiplication_module
This is the original Fourier-Motzkin multiplicative elimination routine. The same caveats of the FM
additive module apply.

- poly_mult_module
This is a replacement for the above. It is currently slower than the FM version. The constant term c
in c*t > 1 is converted via prime factorization to a number of additional variables p1...pn. Since
in order to find the correct comparisons between a_i and a_j, these variables must be present, we
cannot use the 2d algorithm in lrs_polyhedron_util, but instead use cdd to obtain an
h-representation from the vertices projected to the i-j-p1-...-pn plane. cdd accomplishes this
faster than lrs at the moment. lrs is used for the initial h-to-v conversion.

- function_module
This module takes universal axioms and instantiates them as clauses.


In order to use any of the polyhedron modules, cdd and pycddlib must be installed and accessible
from the install folder. See: https://pycddlib.readthedocs.org/en/1.0.4/index.html. In order to use
any module dependent on lrs, lrs must be executable from the run directory, or lrs.py must be
modified to point to the lrs binary.