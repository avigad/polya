####################################################################################################
#
# run_util.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
# Cody Roux
#
# Contains techniques for running the Polya inequality prover, with some prepackaged
# solving methods.
#
####################################################################################################

import polya.main.messages as messages
import polya.main.terms as terms
import copy


def copy_and_add(B, *comps):
    """Create a copy of the blackboard B, and
    add comps to it, return this new blackboard if no inconsistency is
    immediately raised, return None otherwise.
    Arguments:
    - `B`: an instance of Blackboard
    - `a`: an instance of
    """
    new_B = copy.deepcopy(B)
    new_B.add(*comps)
    return new_B


def saturate_modules(B, modules):
    """Run the modules in succession on B until saturation

    Arguments:
    -- B: a blackboard
    -- modules: a list of modules
    """
    mid = B.identify()
    while len(B.get_new_info(mid)) > 0:
        for m in modules:
            messages.announce(B.info_dump(), messages.DEBUG)
            m.update_blackboard(B)


def knows_split(B, i, j, comp, c):
    """
    Returns True if B knows either t_i comp c*t_j or its negation.
    """
    return B.implies(i, comp, c, j) or B.implies(i, terms.comp_negate(comp), c, j)
    #return B.implies(i, terms.EQ, c, j) or B.implies(i, terms.GT, c, j) \
    #    or B.implies(i, terms.LT, c, j)


def get_splits(B, modules):
    """
    Asks each module for a list of comparisons it would like to see.
    Adds up this information and returns a list of tuples (i, j, c), ordered so that splitting
    on t_i <> c*t_j is most desirable for those that come earlier.
    """
    splits = {}
    for m in modules:
        l = m.get_split_weight(B)
        if l is not None:
            for (i, j, c, comp, w) in l:
                splits[i, j, comp, c] = splits.get((i, j, comp, c), 0) + w

    slist = [q for q in sorted(splits.keys(), key=lambda p: (-splits[p], p[0]))
             if splits[q] > 0 and not knows_split(B, q[0], q[1], q[2], q[3])]

    return slist


def split_modules(B, modules, depth, breadth, saturate=True):
    """
    B is a blackboard.
    modules is a list of modules.
    depth restricts how many subsequent splits will be performed: ie, if depth=2, will assume x>0
     and y>0, but won't assume z>0 on top of that.
    breadth restricts how many splits will be considered at each depth. ie, if depth=1, breadth=3,
     will try the three most promising splits separately. If depth=2, breadth=3, will try the three
     most promising splits determined after each of the three most promising preliminary splits.
    """
    if saturate:
        saturate_modules(B, modules)
    if depth <= 0:
        return B
    else:
        backup_bbds = {}
        backup_modules = {}
        candidates = get_splits(B, modules)[:breadth]
        for i in range(len(candidates)):
            can = candidates[i]
            ti, tj = terms.IVar(can[0]), can[3]*terms.IVar(can[1])
            comp = can[2]

            backup_bbds[i, comp] = copy.deepcopy(B)
            backup_modules[i, comp] = copy.deepcopy(modules)
            gtsplit = False
            try:
                newcomp = terms.comp_eval[comp](ti, tj)
                messages.announce("Case split: assuming {0} at depth {1}".format(newcomp, depth),
                                  messages.ASSERTION)
                backup_bbds[i, comp].assert_comparison(newcomp)
                gtsplit = run_modules(backup_bbds[i, comp], backup_modules[i, comp], 0, 0)
            except terms.Contradiction:
                gtsplit = True

            if gtsplit:
                #print 'DETERMINED {0} <= {1}'.format(ti, tj)
                messages.announce("Split led to contradiction at depth {0}. Learned:".format(depth),
                                  messages.ASSERTION)
                B.assert_comparison(terms.comp_eval[terms.comp_negate(comp)](ti, tj))
                return split_modules(B, modules, depth, breadth)

        # at this point, none of the depth-1 splits have returned any useful information.
        for (i, c) in backup_bbds.keys():
            messages.announce("Working under depth {4} assumption: t{0} {1} {2} t{3}".format(
                candidates[i][0], terms.comp_str[candidates[i][2]],
                candidates[i][3], candidates[i][1], depth), messages.ASSERTION)
            try:
                split_modules(backup_bbds[i, c], backup_modules[i, c], depth-1, breadth, saturate=False)
            except terms.Contradiction:
                messages.announce("Split led to contradiction at depth {0}. Learned:".format(depth),
                                  messages.ASSERTION)

                can = candidates[i]
                ti, tj = terms.IVar(can[0]), can[3]*terms.IVar(can[1])
                comp = can[2]
                B.assert_comparison(terms.comp_eval[terms.comp_negate(comp)](ti, tj))
                return split_modules(B, modules, depth, breadth)

            messages.announce("Ending depth {4} assumption: t{0} {1} {2} t{3}".format(
                candidates[i][0], terms.comp_str[candidates[i][2]],
                candidates[i][3], candidates[i][1], depth), messages.ASSERTION)


def run_modules(B, modules, depth, breadth):
    """
    Given a blackboard B, iteratively runs the modules in modules until either a contradiction is
    found or no new information is learned.
    Returns True if a contradiction is found, False otherwise.
    """
    try:
        split_modules(B, modules, depth, breadth)
        return False
    except terms.Contradiction as e:
        messages.announce(e.msg+'\n', messages.ASSERTION)
        return True