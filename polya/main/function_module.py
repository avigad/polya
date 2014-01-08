####################################################################################################
#
# function_module.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# The routine for learning facts using axioms.
# FunctionModule is initialized with a list of axioms.
# Each time update_blackboard is called, the module will check to see if any new clauses can be
# instantiated from its known axioms, and if so, will add them to the blackboard.
#
# TODO:
#
####################################################################################################

import terms
import blackboard
import messages
# from itertools import product, ifilter
# from inspect import getargspec
# from copy import copy
# from scipy.linalg import lu
# from numpy import array

class Axiom:
    """
    literals is a list of term_comparisons
    triggers is
    """
    def __init__(self, literals, triggers=list()):
        pass

def instantiate(axiom, B):
    pass

class FunctionModule:

    def __init__(self, axioms=list()):
        """
        axioms is a list of Axiom objects.
        """
        self.axioms = axioms

    def add_axiom(self, axiom):
        self.axioms.append(axiom)

    def update_blackboard(B):
        messages.announce_module('polyhedron additive module')