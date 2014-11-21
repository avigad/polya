####################################################################################################
#
# axiom_module.py
#
# Author:
# Rob Lewis
#
# Adds axioms for built-in functions: sin, cos, floor, ceiling, etc
#
####################################################################################################

import polya.main.terms as terms
import polya.main.formulas as formulas
import polya.util.timer as timer

Forall, And, Implies = formulas.Forall, formulas.And, formulas.Implies
sin, cos, tan, floor = terms.sin, terms.cos, terms.tan, terms.floor

x = terms.Var('x')
y = terms.Var('y')

sin_axioms = [Forall([x], And(sin(x) >= -1, sin(x) <= 1))]

cos_axioms = [Forall([x], And(cos(x) >= -1, cos(x) <= 1))]

tan_axioms = [Forall([x], tan(x) == sin(x) / cos(x))]

floor_axioms = [Forall([x], And(floor(x) <= x, floor(x) > x-1))]

abs_axioms=[
    Forall([x, y], And(abs(x + y) >= abs(x) + abs(y), abs(x - y) >= abs(x) - abs(y))),
    formulas.Forall([x], terms.abs_val(x) >= 0),
    formulas.Forall([x], terms.abs_val(x) >= x),
    formulas.Forall([x], terms.abs_val(x) >= -x),
    formulas.Forall([x], formulas.Implies(x >= 0, terms.abs_val(x) == x)),
    formulas.Forall([x], formulas.Implies(x <= 0, terms.abs_val(x) == -x))
]

exp_axioms = [
    formulas.Forall([x], terms.exp(x) > 0),
    #formulas.Forall([x], terms.exp(x) > x),
    formulas.Forall([x], formulas.Implies(x >= 0, terms.exp(x) >= 1)),
    formulas.Forall([x], formulas.Implies(x > 0, terms.exp(x) > 1)),
    formulas.Forall([x, y],
                                      formulas.Implies(x < y, terms.exp(x) < terms.exp(y))),
    formulas.Forall([x, y],
                                      formulas.Implies(x <= y, terms.exp(x) <= terms.exp(y))),
    formulas.Forall([x, y],
                                      formulas.Implies(x != y, terms.exp(x) != terms.exp(y)))
]

log_axioms = [
    formulas.Forall([x], formulas.Implies(x >= 1, terms.log(x) >= 0)),
    formulas.Forall([x], formulas.Implies(x > 1, terms.log(x) > 0)),
    formulas.Forall([x], formulas.Implies(x > 0, terms.log(x) < x)),
    formulas.Forall([x, y], formulas.Implies(formulas.And(x > 0, x < y),
                                                               terms.log(x) < terms.log(y))),
    formulas.Forall([x, y], formulas.Implies(formulas.And(x > 0, x <= y),
                                                               terms.log(x) <= terms.log(y))),
    formulas.Forall([x, y], formulas.Implies(formulas.And(x > 0, y > 0, x != y),
                                                               terms.log(x) != terms.log(y))),
    formulas.Forall([x], formulas.Implies(x > 0, terms.exp(terms.log(x)) == x)),
    formulas.Forall([x], terms.log(terms.exp(x)) == x)
]


class BuiltinsModule:
    def __init__(self, am):
        """
        Module must be initiated with an axiom module.
        """
        self.am = am
        self.added = {'sin': False, 'cos': False, 'tan': False, 'floor': False, 'abs': False,
                      'exp': False, 'log': False}

    def update_blackboard(self, B):
        """
        Adds axioms for sin, cos, tan, floor
        """
        timer.start(timer.BUILTIN)
        ts = [B.term_defs[i] for i in range(B.num_terms)]
        funcs = [t.func.name for t in ts if isinstance(t, terms.FuncTerm)]

        if (not self.added['sin'] and 'sin' in funcs):
            self.am.add_axioms(sin_axioms)
            self.added['sin'] = True

        if (not self.added['cos'] and 'cos' in funcs):
            self.am.add_axioms(cos_axioms)
            self.added['cos'] = True

        if (not self.added['tan'] and 'tan' in funcs):
            self.am.add_axioms(tan_axioms)
            self.added['tan'] = True

        if (not self.added['floor'] and 'floor' in funcs):
            self.am.add_axioms(floor_axioms)
            self.added['floor'] = True

        if (not self.added['abs'] and 'abs' in funcs):
            self.am.add_axioms(abs_axioms)
            self.added['abs'] = True

        if (not self.added['exp'] and 'exp' in funcs):
            self.am.add_axioms(exp_axioms)
            self.added['exp'] = True

        if (not self.added['log'] and 'log' in funcs):
            self.am.add_axioms(log_axioms)
            self.added['log'] = True

        timer.stop(timer.BUILTIN)

    def get_split_weight(self, B):
        return None