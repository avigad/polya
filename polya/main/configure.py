####################################################################################################
#
# configure.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# System configuration, loaded by __init__.py when the polya module is imported.
#
####################################################################################################

import polya.main.messages as messages
import polya.polyhedron.lrs as lrs

####################################################################################################
#
# System configuration
#
####################################################################################################

messages.announce('', messages.INFO)
messages.announce('Welcome to Polya.', messages.INFO)

solver_options = ['fm', 'poly']
default_solver = 'none'

messages.announce('Looking for components...', messages.INFO
)
# look for cdd
try:
    import cdd
    have_cdd = True
    messages.announce('cdd found.', messages.INFO)
except Exception:
    have_cdd = False
    messages.announce('cdd not found.', messages.INFO)

# look for lrs
if lrs.lrs_path is None:
    messages.announce('lrs not found.', messages.INFO)
else:
    messages.announce('lrs found (path: {0!s}).'.format(lrs.lrs_path), messages.INFO)

# look for redund
if lrs.redund_path is None:
    messages.announce('redund not found.', messages.INFO)
else:
    messages.announce('redund found (path: {0!s}).'.format(lrs.redund_path), messages.INFO)

messages.announce('', messages.INFO
)
if lrs.lrs_path and lrs.redund_path and have_cdd:
    default_solver = 'poly'
else:
    default_solver = 'fm'


def polya_set_solver_type(s):
    """Set the solver to a given method in
    solver_options

    Arguments:
    - `s`:
    """
    if s in solver_options:
        messages.announce('Setting solver type: {0!s}'.format(s), messages.INFO)
        global default_solver
        default_solver = s
    else:
        messages.announce('Error: {0!s} is not in the list of possible arithmetic '
                               'solvers'.format(s), messages.INFO)
        messages.announce('solver options = {0!s}'.format(solver_options))



