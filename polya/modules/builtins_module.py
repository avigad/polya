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
x = terms.Var('x')
sin, cos, tan, floor = terms.sin, terms.cos, terms.tan, terms.floor

sin_axioms = [Forall([x], And(sin(x) >= -1, sin(x) <= 1))]

cos_axioms = [Forall([x], And(cos(x) >= -1, cos(x) <= 1))]

tan_axioms = [Forall([x], tan(x) == sin(x) / cos(x))]

floor_axioms = [Forall([x], And(floor(x) <= x, floor(x) > x-1))]


class BuiltinsModule:
    def __init__(self, am):
        """
        Module must be initiated with an axiom module.
        """
        self.am = am
        self.added = {'sin': False, 'cos': False, 'tan': False, 'floor': False}

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
        timer.stop(timer.BUILTIN)

    def get_split_weight(self, B):
        return None