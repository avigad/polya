Test Problems
=============

This file provides data to support the discussion in the paper "A heuristic prover for real inequalities", by Avigad, Lewis, and Roux (2014).

All tests were performed on an Intel i7-3770 4 core CPU at 3.4 GHz. The data on Polya was obtained using

    sample_problems.py
    
The data on Z3 was obtained using

    z3_problems.py
    
The assessment of Isabelle's Sledgehammer is based on the file

    isabelle_problems.py
    
We also experimented with MetiTarski, which uses Z3 for problems in the language of real closed fields. MetiTarski did well on those problems, but it is not designed to handle axioms for uninterpreted function symbols, and did not solve the two problems with exponentiation below. Some tests are found in the file

    metitarski_problems.tptp

The results:

    *** Example 0 ***
    Hypothesis: u > 0
    Hypothesis: u < v
    Hypothesis: v < 1
    Hypothesis: x >= 2
    Hypothesis: x <= y
    Conclusion: 2 * u**2 * x < y**2 * v
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 16ms
    Polya (fm): valid, 15ms
    Z3: valid, 3ms
    Sledgehammer: fails
    
    
    *** Example 1 ***
    Hypothesis: x > 1
    Conclusion: (1 + y**2) * x >= 1 + y**2
    
    Polya (poly): valid, 23ms
    Polya (fm): valid, 16ms
    Z3: valid, 2ms
    Sledgehammer: succeeds (resolution, z3)
    
    
    *** Example 2 ***
    Hypothesis: x > 0
    Hypothesis: x < 1
    Conclusion: (-1*x + 1)**-1 > (-1*x**2 + 1)**-1
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 27ms
    Polya (fm): valid, 15ms
    Z3: valid, 2ms
    Sledgehammer: fails
    
    
    *** Example 3 ***
    Hypothesis: u > 0
    Hypothesis: u < v
    Hypothesis: z > 0
    Hypothesis: 1 + z < w
    Conclusion: (u + v + z)**3 < (u + v + w + 1)**5
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 44ms
    Polya (fm): valid, 39ms
    Z3: valid, 13ms
    Sledgehammer: fails
    
    
    *** Example 4 ***
    Hypothesis: u > 0
    Hypothesis: u < v
    Hypothesis: z > 0
    Hypothesis: 1 + z < w
    Conclusion: (u + v + z)**33 < (u + v + w + 1)**55
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 26ms
    Polya (fm): valid, 4ms
    Z3: timed out
    Sledgehammer: fails
    
    
    *** Example 5 ***
    Hypothesis: u > 0
    Hypothesis: u < (23 + v**2)**3
    Hypothesis: z > 0
    Hypothesis: 1 + z < w
    Conclusion: (u + (23 + v**2)**3 + z)**3 < (u + (23 + v**2)**3 + w + 1)**5
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 35ms
    Polya (fm): valid, 69ms
    Z3: valid, 194ms
    Sledgehammer: fails
    
    
    *** Example 6 ***
    Axiom: Forall([x, y], Implies(x >= y, f(x) >= f(y)))
    Hypothesis: u < v
    Hypothesis: x <= y
    Conclusion: u + f(x) < v + f(y)
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 9ms
    Polya (fm): valid, 7ms
    Z3: valid, 2ms
    Sledgehammer: succeeds (resolution, z3)
    
    
    *** Example 7 ***
    Axiom: Forall([x], f(x) <= 1)
    Hypothesis: u < v
    Hypothesis: w > 0
    Conclusion: u + w * f(x) < v + w
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 15ms
    Polya (fm): valid, 11ms
    Z3: valid, 2ms
    Sledgehammer: succeeds (resolution)
    
    
    *** Example 9 ***
    Axiom: Forall([x], f(x) <= 2)
    Hypothesis: u < v
    Hypothesis: w > 0
    Conclusion: u + w * (-1 + f(x)) < v + w
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 18ms
    Polya (fm): valid, 14ms
    Z3: valid, 2ms
    Sledgehammer: fails
    
    
    *** Example 8 ***
    Axiom: Forall([x, y], Implies(x >= y, f(x) >= f(y)))
    Hypothesis: u < v
    Hypothesis: w > 1
    Hypothesis: s > 2
    Hypothesis: (1/3)*(w + s) < v
    Hypothesis: x <= y
    Conclusion: f(x) + u < v + f(y)
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 11ms
    Polya (fm): valid, 9ms
    Z3: valid, 3ms
    Sledgehammer: fails
    
    
    *** Example 10 ***
    Axiom: Forall([x, y], Implies(x >= y, f(x) >= f(y)))
    Hypothesis: u < v
    Hypothesis: v > 1
    Hypothesis: x <= y
    Conclusion: f(x) + u < v**2 + f(y)
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 19ms
    Polya (fm): valid, 14ms
    Z3: unknown
    Sledgehammer: fails
    
    
    *** Example 11 ***
    Axiom: Forall([x, y], Implies(x < y, exp(x) < exp(y)))
    Hypothesis: x > 0
    Hypothesis: x < y
    Hypothesis: u < v
    Conclusion: 2*u + exp(1 + x + x**4) <= 2*v + exp(1 + y + y**4)
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 53ms
    Polya (fm): valid, 36ms
    Z3: unknown
    Sledgehammer: succeeds (resolution, z3)
    
    
    *** Example 12 ***
    Axiom: Forall([x, y], Implies(x < y, exp(x) < exp(y)))
    Hypothesis: x > 0
    Hypothesis: y > 3
    Hypothesis: u < v
    Conclusion: 2*u + exp(10) <= 2*v + exp(1 + y**2)
    
    Polya (poly): valid, 73ms
    Polya (fm): valid, 41ms
    Z3: unknown
    Sledgehammer: fails
    
    
    *** Example 13 ***
    Axiom: Forall([x, y], f(x + y) == f(x) * f(y))
    Hypothesis: f(a) > 2
    Hypothesis: f(b) > 2
    Conclusion: f(a + b) > 4
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 23ms
    Polya (fm): valid, 19ms
    Z3: timed out
    Sledgehammer:
    
    
    *** Example 14 ***
    Axiom: Forall([x, y], f(x + y) == f(x) * f(y))
    Hypothesis: f(a + b) > 2
    Hypothesis: f(c + d) > 2
    Conclusion: f(a + b + c + d) > 4
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 44ms
    Polya (fm): valid, 42ms
    Z3: timed out
    Sledgehammer: fails
    
    
    *** Example 15 ***
    Hypothesis: n >= 0
    Hypothesis: n < (1/2) * K * x
    Hypothesis: c > 0
    Hypothesis: eps > 0
    Hypothesis: eps < 1
    Conclusion: ((1/3) * (3 + c)**-1 * eps + 1) * n < K * x
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 61ms
    Polya (fm): valid, 45ms
    Z3: valid, 2ms
    Sledgehammer: fails
    
    
    *** Example 16 ***
    Hypothesis: x > 0
    Hypothesis: x < y
    Conclusion: (2 + y)**-17 * (1 + x**2) < (2 + x)**-10 * (2 + y**2)
    Comment: From Avigad and Friedman (2006).
    
    Polya (poly): valid, 57ms
    Polya (fm): valid, 62ms
    Z3: valid, 398ms
    Sledgehammer: fails
    
    
    *** Example 17 ***
    Axiom: Forall([x, y], And(Implies(x < y, exp(x) < exp(y)), exp(x) > 0))
    Hypothesis: x > 0
    Hypothesis: x < y
    Conclusion: (2 + exp(y))**-1 * (1 + x**2) < (1 + exp(x))**-1 * (2 + y**2)
    Comment: From Avigad and Friedman (2006).
    
    Polya (poly): valid, 79ms
    Polya (fm): valid, 76ms
    Z3: unknown
    Sledgehammer: fails
    
    
    *** Example 18 ***
    Hypothesis: x > 0
    Hypothesis: y > 0
    Hypothesis: y < 1
    Hypothesis: x * y > x + y
    Conclusion: False
    
    Polya (poly): valid, 10ms
    Polya (fm): valid, 7ms
    Z3: valid, 2ms
    Sledgehammer: succeeds (resolution)
    
    
    *** Example 19 ***
    Hypothesis: x > 0
    Hypothesis: y > 0
    Hypothesis: y < 1
    Hypothesis: x**150 * y**150 > x**150 + y**150
    Conclusion: False
    
    Polya (poly): valid, 19ms
    Polya (fm): valid, 9ms
    Z3: timed out
    Sledgehammer: fails
    
    
    *** Example 20 ***
    Hypothesis: x > 0
    Hypothesis: y > -1
    Hypothesis: y < 0
    Hypothesis: x**150 * (1 + y)**150 > x**150 + (1 + y)**150
    Conclusion: False
    
    Polya (poly): valid, 28ms
    Polya (fm): valid, 15ms
    Z3: timed out
    Sledgehammer: fails
    
    
    *** Example 21 ***
    Axiom: Forall([x, y], abs(x + y) <= abs(x) + abs(y))
    Hypothesis: i >= 0
    Hypothesis: abs(-1*f(x) + f(y)) < (1/2)*(1 + i)**-1
    Hypothesis: abs(-1*f(y) + f(z)) < (1/2)*(1 + i)**-1
    Conclusion: abs(-1*f(x) + f(z)) < (1 + i)**-1
    Comment: Discussed in Avigad, Lewis, and Roux (2014)
    
    Polya (poly): valid, 75ms
    Polya (fm): valid, 72ms
    Z3: timed out
    Sledgehammer: fails
    
    
    *** Example 22 ***
    Axiom: Forall([x], ceil(x) >= x)
    Hypothesis: a < b
    Hypothesis: x > a
    Hypothesis: m >= ceil((-1*a + x)**-1 * (-1*a + b))
    Conclusion: a + (1 + m)**-1 * (-1*a + b) < x
    
    Polya (poly): valid, 28ms
    Polya (fm): valid, 28ms
    Z3: unknown
    Sledgehammer: fails
    
    
    *** Example 23 ***
    Axiom: Forall([x], ceil(x) >= x)
    Axiom: Forall([m], Implies(m > 0, f(ceil(m)) < a + ceil(m)**-1 * (-1*a + b)))
    Hypothesis: a < b
    Hypothesis: x > a
    Hypothesis: m >= (-1*a + x)**-1 * (-1*a + b)
    Conclusion: f(ceil(m)) < x
    Comment: Discussed in Avigad, Lewis, and Roux (2cd014)
    
    Polya (poly): valid, 94ms
    Polya (fm): valid, 64ms
    Z3: unknown
    Sledgehammer: fails
    
    