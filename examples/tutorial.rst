=======================
A Quick Start for Polya
=======================

Overview
---------

This document outlines basic usage of the Polya Proof Assistant
Python package.

Polya is a Python library that allows the user to express and solve complex inequalities expressed over the real numbers. In particular the aim is to provide a tool that proves *intuitively true* statements of mathematics, something which many automated tools fail to do.

A basic example
----------------

We will need to import the polya python package, which
should be in your python path

.. code-block::

   from polya import *

Then declare the variables which you wish to use to express your
inequality:

.. code-block::

   x = Vars('x')

You can also declare several variables at once, by separating the
names with a space:

.. code-block::

   y, z = Vars('y z')

Then, to prove inequalities, create a ``Solver`` object, and add
inequalities using the variables and the usual Python operations.

.. code-block::

   s = Solver()
   s.assume(x > 0)
   s.assume(y > x, y <= 0)


We can check that the inequalities assumed up to this point are
inconsistent:

.. code-block::

   s.check()

The output should look something like this:

>>> lrs found! (/home/croux/prog/python/polya/polya/polyhedron/lrs)
redund found! (/home/croux/prog/python/polya/polya/polyhedron/redund)
Defining t1 := x
  := x
Asserting t1 > 0
  := x > 0
Defining t2 := y
  := y
Asserting t1 < t2
  := x < y
Asserting t2 > 0
  := y > 0
Contradiction: t1 >= t2
  := x >= y
>>> Entering congruence closure module
>>> Entering polyhedron additive module
>>> Entering polyhedron multiplicative module
False

You can also add hypotheses to the solver, and ask it to attempt to
prove a new assume.

.. code-block::

   s = Solver()
   s.assume(x > 0, y > x)
   s.prove(y >= 0)

Which should produce a similar result (though prove returns ``True``
if the proposition is provable).

Arithmetic
----------

Of course, Polya is capable of proving inequalities involving sums and
products:

.. code-block::

   s = Solver()
   s.assume(x > 0, x < 1, y > 0, z > 0, y + z <= x)
   s.prove(z**2 <= 1)
   

Function symbols and axioms
---------------------------


More generally, it is possible to declare function symbols, and add
axioms involving them to the set of assumptions.


.. code-block::

   f = Func('f')

   s = Solver()
   
   s.add_axiom(Forall(x, f(x) > 0))

   s.prove(f(3) >= 0)

Axioms take the form of a universal statement, followed a
formula built using the usual propositional connectives.

.. code-block::


   s = Solver()

   s.add_axiom(Forall([x, y], Implies(x > y, f(x) > f(y))))

   s.assume(x > 1)

   s.prove(f(x**2) > f(x))


The Blackboard
--------------

Polya works by maintaining inequality information using a central
structure, the **Blackboard**. It is possible to work directly with
blackboards:

.. code-block::

   b = Blackboard()
   b.assume(0 < x)
   b.assume(x < 3*y)
   b.assume(u < v)
   b.assume(v < 0)
   b.assume(1 < v**2)
   b.assume(v**2 < x)
   b.assume(u*(3*y)**2 + 1 >= x**2 * v + x)

   run(b)

Running a blackboard calls the additive and the multiplicative
solvers, respectively and the axiom instantiation, if necessary.
