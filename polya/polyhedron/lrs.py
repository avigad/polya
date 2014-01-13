#import subprocess
from fractions import Fraction
import pipes
import tempfile
#import timecount

#Depending on how you have installed lrs,
#you may have to change lines 48 and 71 to
# "./lrs" and "./redund"


lrs_path = '/usr/bin/lrs'

import subprocess as s

try:
    s.check_output([lrs_path, '_stupid_pretend_file'])
except OSError, e:
    print "call to", lrs_path, "failed with message:"
    print str(e)
    print
    print "Do you have lrs installed? See instructions for details."


def make_frac(string):
    i = string.find('/')
    if i < 0:
        return int(string)
    return Fraction(int(string[:i]), int(string[i+1:]))


def output_to_matrix(str_output):
    arr = str(str_output).split('\n')

    try:
        l_ind = next(i for i in range(len(arr)) if arr[i][0:3] == 'lin')
        lin_set = [int(val)-1 for val in arr[l_ind].split()[2:]]
    except StopIteration:
        lin_set = []
        
    #print lin_set
    row = next(i for i in range(3, len(arr)) if arr[i][0:3] == 'beg')+2
    mat = []
    while arr[row] != 'end':
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
        print matrix
        print out
        exit()


def redund_and_generate(matrix):
    s = str(matrix)
    p = pipes.Template()
    p.append("redund", "--")
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
