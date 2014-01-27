####################################################################################################
#
# messages.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# User messages. Modules tag messages with a description of the type of information. The user
# sets the global variable 'verbosity' with a list of tags as to what should be printed out.
#
# The intended tags are as follows:
#
#   MODULE:         '>>> Entering additive module'
#   MODULE_PAD:     blank lines around module announcement
#   DEF:            'Defined t1 := t7 + t8'
#   DEF_FULL:       '  := 3 * (x + y) + z'
#   ASSERTION:      'Asserted t5 < 3 * t8'
#   ASSERTION_FULL: '  := x + y < 3 * (u + v) * (w + 2 * z)'
#   DEBUG:          anything else
#
####################################################################################################


# tags
INFO, MODULE, MODULE_PAD, DEF, DEF_FULL, ASSERTION, ASSERTION_FULL, MISC, DEBUG = range(9)

# predefined levels
quiet = ()
modules = (INFO, MODULE)
low = (INFO, MODULE, MODULE_PAD, DEF, ASSERTION)
normal = (INFO, MODULE, MODULE_PAD, DEF, DEF_FULL, ASSERTION, ASSERTION_FULL)
debug = (INFO, MODULE, MODULE_PAD, DEF, DEF_FULL, ASSERTION, ASSERTION_FULL, DEBUG)

# global verbosity level
verbosity = normal


def set_verbosity(level=normal):
    global verbosity
    verbosity = level


def announce_module(module):
    announce('', MODULE_PAD)
    announce('>>> Entering {0}'.format(module), MODULE)
    announce('', MODULE_PAD)


def announce(message, level):
    """
    Display message, if an appropriate level.
    """
    if level in verbosity:
        print message


def visible(level):
    """
    Determine whether messages at this level should be displayed.
    """
    return level in verbosity


def announce_strong(message):
    """
    Display message, no matter what the level is.
    """
    print message