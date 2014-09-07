####################################################################################################
#
# exponential_module.py
#
# Author:
# Rob Lewis
#
# The routine for learning facts about exponential functions
#
#
####################################################################################################

import polya.main.terms as terms
import polya.main.messages as messages
import polya.main.formulas as formulas
import polya.util.timer as timer
import polya.util.num_util as num_util
import fractions
import copy


class ExponentialModule:


    def __init__(self, fm):
        """
        The exponential module must be instantiated with a function module to add axioms to.
        """
        self.fm = fm

    def update_blackboard(self, B):
        pass