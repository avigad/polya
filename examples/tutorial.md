Polya: A Quick Start
====================

Overview
--------

This document outlines basic usage of the Polya Inequality Prover.

Polya is a Python library that allows the user to verify inequalities between 
real-valued expressions. It aims, in particular, to capture the common 
inferences that arise in interactive theorem proving.


A basic example
---------------

Run Python 2.7 and import the Polya Python package, which should be in your 
Python path:

```python
from polya import *
```

You can check to see what external tools have been found:

```python
show_configuration()
```

The output should look something like this:

```
Welcome to the Polya inequality prover.
Looking for components...
lrs found (path: lrs).
redund found (path: redund).
cdd found.
```

Then declare the variables which you wish to use to express your inequality:

```python
x = Vars('x')
```

You can also declare several variables at once, by separating the names with a 
space or a comma:

```python
y, z = Vars('y z')
```

Then, to prove inequalities, create a ``Solver`` object, and add inequalities 
using the variables and the usual Python operations.

```python
s = Solver()
s.assume(x > 0)
s.assume(y > x, y <= 0)
```

The system reports that these declarations have been asserted to a central 
blackboard. You can ask Polya to check whether they are consistent:


```python
s.check()
```

In this case, Polya reports that a contradiction has been found.

You can alternatively ask Polya to prove that a claim follows from the 
hypotheses:

```python
s = Solver()
s.assume(x > 0, y > x)
s.prove(y > 0)
```

The net effect is the same: Polya attempts to prove the conclusion by
assuming the negation and deriving a contradiction.


Arithmetic
----------

Polya is capable of proving inequalities involving sums and products.

```python
s = Solver()
s.assume(x > 0, x < 1, y > 0, z > 0, y + z <= x)
s.prove(z**2 <= 1)
```


Function symbols and axioms
---------------------------

More generally, you can declare function symbols, and add axioms involving them 
to the set of assumptions.


```python
f = Func('f')
s = Solver()
s.add_axiom(Forall(x, f(x) > 0))
s.prove(f(3) >= 0)
```

Axioms take the form of a universal statement, followed a formula built using the 
usual propositional connectives.

```python
s = Solver()
s.add_axiom(Forall([x, y], Implies(x > y, f(x) > f(y))))
s.assume(x > 1)
s.prove(f(x**2) > f(x))
```


The blackboard
--------------

Polya works by maintaining inequality information using a central structure, the 
*blackboard*. It is possible to work with the blackboard directly:

```python
b = Blackboard()
b.assume(0 < x)
b.assume(x < 3*y)
b.assume(u < v)
b.assume(v < 0)
b.assume(1 < v**2)
b.assume(v**2 < x)
b.assume(u*(3*y)**2 + 1 >= x**2 * v + x)

run(b)
```

The modules
-----------

Running a blackboard calls a number of *modules*, each of which attempts to 
derive new information and add it to the blackboard. This continues until
no additional facts are learned.

In this case the *default modules* are called, which are the
additive, multiplicative and congruence modules respectively.

The *additive module* learns all possible facts which
are only expressible in terms of the additive properties of the
known facts, i.e. inequalities of the form a1*x1+...+an*xn < t,
where < may also be <=, >, >=, or =.
   
In fact, there are two versions of this module. The first,
simpler one is based on Fourier-Motzkin elimination and can be
instantiated by

```python        
ma = FMAdditionModule()
```

The second is based on a geometric method, and can only be used if
the computational geometry packages cdd and lrs are correctly configured on 
your machine.

```python     
ma = PolyAdditionModule()
```

Either module can then be explicitly used to learn new facts about
a given blackboard ``b``

```python
ma.update_blackboard(b)
```

The *multiplicative module* works is similar to the additive module interface, 
but works on the purely multiplicative fragment of the problem. Restricted to
the positive reals, the multiplicative module essentially emulates the additive
module under the map x -> log x. Again, there are two versions:

```python
mm1 = FMMultiplicationModule()
mm2 = PolyMultiplicationModule()
```

The *congruance closure module*. This module simply learns all possible equalities 
using the usual rules for equality (reflexivity, symmetry, transitivity and the 
congruence rules):
   
```python
mc = CongClosureModule()
```

The *function module*. This module takes as arguments a set of universally 
quantified formulas which serve as axioms, and performs instantiations of the 
axioms according to a certain heuristic for a given blackboard.

```python
fm = FunctionModule([Forall([x, y], Implies(x<y, f(x) < f(y)))])
fm.update_blackboard(b)
```

The information shared between all modules consists of one of the following 
forms:

* `t comp c*u`

* `t comp 0`

where `t` and `u` are terms appearing in the problem, `c` is a rational constant, and
comp is any of
 
```python
<. <=, >, >=, ==, or !=
``` 
