####################################################################################################
#
# lrs.py
#
# Author:
# Rob Lewis
#
# Helper class for interacting with the external lrs geometry package.
#
####################################################################################################

from fractions import Fraction
import pipes
import tempfile
import os.path
#import polya.main.messages as messages


import subprocess

poly_dir = os.path.dirname(__file__)


def find_lrs_path():
    """
    look in some standard places for lrs and return the path
    """
    for s in ['lrs', './lrs', poly_dir + '/lrs', '/usr/bin/lrs']:
        try:
            subprocess.check_output([s, '_pretend_file'])
        except (OSError, subprocess.CalledProcessError), e:
            pass
        else:
            return s

lrs_path = find_lrs_path()


def find_redund_path():
    """
    look in some standard places for redund and return the path
    """
    for s in ['redund', './redund', poly_dir + '/redund', '/usr/bin/redund']:
        try:
            subprocess.check_output([s, '_pretend_file'])
        except OSError, e:
            pass
        else:
            return s

redund_path = find_redund_path()


def make_frac(string):
    """
    Turns a string "1234/3456" into a Fraction
    """
    i = string.find('/')
    if i < 0:
        return int(string)
    return Fraction(int(string[:i]), int(string[i+1:]))


def output_to_matrix(str_output):
    """
    Takes an lrs output string and parses it.
    Returns a pair (mat, lin_set), where mat is a list of lists (a matrix) and lin_set is the
    list of linear rows of that matrix.
    """
    arr = str(str_output).split('\n')

    try:
        l_ind = next(i for i in range(len(arr)) if arr[i][0:3] == 'lin')
        lin_set = [int(val)-1 for val in arr[l_ind].split()[2:]]
    except StopIteration:
        lin_set = []
        
    #print lin_set
    row = next(i for i in range(3, len(arr)) if arr[i][0:3] == 'beg')+2
    mat = []
    while row < len(arr) and arr[row] != 'end':
        mat.append([make_frac(val) for val in arr[row].split()])
        row += 1
    return mat, lin_set


def get_generators(matrix):
    """
    Given a matrix in H-rep, gets the v-rep
    Turns out, the code is the same as get_inequalities,
    since lrs determines the directions based on the input.
    Left like this for readability.
    """
    return get_inequalities(matrix)


def get_inequalities(matrix):
    """
    Given a matrix in v-rep, gets the h-rep
    """
    s = str(matrix)
    #timecount.start()
    p = pipes.Template()
    p.append(lrs_path, "--")
    p.debug(False)
    t = tempfile.NamedTemporaryFile(mode='r')
    f = p.open(t.name, 'w')
    try:
        f.write(s)
    finally:
        f.close()
    t.seek(0)
    out = t.read()
    t.close()
    #timecount.stop()
    
    try:
        return output_to_matrix(out)
    except StopIteration:
        print 'Error in LRS'
        print matrix
        print 'out:'
        print out
        raise


def redund_and_generate(matrix):
    """
    Uses lrs to remove redundancies before performing v-to-h conversion.
    """
    s = str(matrix)
    p = pipes.Template()
    p.append(redund_path, "--")
    p.debug(False)
    t = tempfile.NamedTemporaryFile(mode='r')
    f = p.open(t.name, 'w')
    try:
        f.write(s)
    finally:
        f.close()
    t.seek(0)
    out = t.read()
    t.close()
    #print matrix
    #print 'turned into'
    #print out

    return get_inequalities(out)
