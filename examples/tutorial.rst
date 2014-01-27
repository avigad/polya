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

.. code-block:: python

   from polya import *

Then declare the variables which you wish to use to express your
inequality:

.. code-block:: python

   x = Vars('x')

You can also declare several variables at once, by separating the
names with a space:

.. code-block:: python

   y, z = Vars('y z')

Then, to prove inequalities, create a ``Solver`` object, and add
inequalities using the variables and the usual Python operations.

.. code-block:: python

   s = Solver()
   s.assume(x > 0)
   s.assume(y > x, y <= 0)


We can check that the inequalities assumed up to this point are
inconsistent:

.. code-block:: python

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

.. code-block:: python

   s = Solver()
   s.assume(x > 0, y > x)
   s.prove(y >= 0)

Which should produce a similar result (though prove returns ``True``
if the proposition is provable).

Arithmetic
----------

Of course, Polya is capable of proving inequalities involving sums and
products:

.. code-block:: python

   s = Solver()
   s.assume(x > 0, x < 1, y > 0, z > 0, y + z <= x)
   s.prove(z**2 <= 1)
   

Function symbols and axioms
---------------------------


More generally, it is possible to declare function symbols, and add
axioms involving them to the set of assumptions.


.. code-block:: python

   f = Func('f')

   s = Solver()
   
   s.add_axiom(Forall(x, f(x) > 0))

   s.prove(f(3) >= 0)

Axioms take the form of a universal statement, followed a
formula built using the usual propositional connectives.

.. code-block:: python


   s = Solver()

   s.add_axiom(Forall([x, y], Implies(x > y, f(x) > f(y))))

   s.assume(x > 1)

   s.prove(f(x**2) > f(x))


The Blackboard
--------------

Polya works by maintaining inequality information using a central
structure, the **Blackboard**. It is possible to work directly with
blackboards:

.. code-block:: python

   b = Blackboard()
   b.assume(0 < x)
   b.assume(x < 3*y)
   b.assume(u < v)
   b.assume(v < 0)
   b.assume(1 < v**2)
   b.assume(v**2 < x)
   b.assume(u*(3*y)**2 + 1 >= x**2 * v + x)

   run(b)

Running a blackboard calls a number of **update modules**, which each
successively add inequality information to the blackboard in turn until
no more facts are learned.

In this case the **default modules** are called, which are the
additive, multiplicative and congruence modules respectively.

There are several types of **module interfaces**, which can be
instantiated by concrete modules and called on a given blackboard. The
different types of modules are as follows:

A) The **additive module interface** learns all possible facts which
   are only expressible in terms of the additive properties of the
   known facts, i.e. inequalities of the form a1*x1+...+an*xn < t,
   where < may also be <=, >, >=, or =.
   
   There are two possible implementations of this module. The first,
   simpler one is based on Fourier-Motzkin elimination and can be
   instantiated by

   .. code-block:: python
        
                   ma = FMAdditionModule()

   The second is based on a geometric method, and can only be used if
   CDD and LRS are correctly configured on your machine.

   .. code-block:: python
        
                   ma = PolyAdditionModule()

   Either module can then be explicitly used to learn new facts about
   a given blackboard ``b``

   .. code-block:: python

                   ma.update_blackboard(b)

B) The **multiplicative module interface** works in a similar way to
   the additive module interface, but on the purely multiplicative
   fragment of the problem. Essentially, the concrete implementations
   work in a very similar manner to the additive modules by taking
   logarithms of the known facts. Again there are two flavors

   .. code-block:: python

                   mm1 = FMMultiplicationModule()
                   mm2 = PolyMultiplicationModule()

C) The **congruence module interface**. This module simply learns all
   possible equalities using the usual rules for equality
   (reflexivity, symmetry, transitivity and the congruence rules). At
   the moment it has a single possible instance

   .. code-block:: python

                   mc = CongClosureModule()

D) The **axiom instantiation interface**. This module takes as
   arguments the set of universally quantified formulas which serve as
   axioms, and performs instantiations of the axioms according to a
   certain heuristic for a given blackboard.

   .. code-block:: python

                   fm = FunctionModule([Forall([x, y], Implies(x<y,
                   f(x) < f(y)))])
                   fm.update_blackboard(b)
