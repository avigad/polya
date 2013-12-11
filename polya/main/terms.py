####################################################################################################
#
# terms.py
#
# Authors:
# Jeremy Avigad
# Rob Lewis
#
# A Term is either an Atom or a AppTerm.
#
# An STerm is a scaled term, i.e. something of the form (c * t), where c is a Fraction and t
# is a Term. When terms are canonized, such a scalar is needed.
#
# Subclasses of Atom include:
#
#     One (the constant term 1)
#     Var
#     IVar (indexed variables, used to name subterms)
#     UVar (unification variables)
#
# An AppTerm consists of a function applied to a sequence of arguments. Subclasses of AppTerm
# include:
#
#     FuncTerm
#     AddTerm
#     MulTerm
#     AbsTerm
#     MinTerm
#     MaxTerm
#
# For all AppTerms other than MulTerm, the arguments are STerms. A MulTerm, on the other hand, is
# of the form
#
#  (t1^n1) * ... * (tk^nk)
#
# where each ti is a Term and each ni is an integer. When canonizing, scalars are collected and
# brought to the front, so each ti need only by a Term. Such a pair (t, n) is called a MulPair.
#
# This module defines Python syntax for entering Terms and STerms, and the methods for canonizing
# and printing them.
#
# This module also defines comparisons between STerms, which are always normalized
# to be of the form
#
#   term1 comp c * term2
#
####################################################################################################

# TODO: would it be better to have one AppTerm, and put all the information into the Function?

import fractions
import numbers

class Error(Exception):
    pass


####################################################################################################
#
# Casts
#
####################################################################################################


def Rational_to_STerm(rat):
    return STerm(rat, One())

def MulPair_to_Term(mulpair):
    return MulTerm([mulpair])

def Term_to_STerm(term):
    return STerm(1, term)


####################################################################################################
#
# Term
#
####################################################################################################


class Term:

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        raise NotImplementedError()

    def __add__(self, other):
        # case where self is an AddTerm is handled in that class
        if isinstance(other, numbers.Rational):
            return self + Rational_to_STerm(other)
        # elif isinstance(other, MulPair):
        #     return self + MulPair_to_Term(other)
        if isinstance(other, AddTerm):
            return other + self
        elif isinstance(other, Term):
            if self == other:
                return STerm(2, self)
            else:
                return AddTerm([STerm(1, self), STerm(1, other)])
        elif isinstance(other, STerm):
            return other + self
        else:
            raise Error('Cannot add term')

    def __truediv__(self, other):
        return self / other

    def __rtruediv__(self, other):
        return other * self ** (-1)

    def __rdiv__(self, other):
        return (self ** (-1)) * other

    def __neg__(self):
        return self * (-1)

    def __sub__(self, other):
        return self + other * (-1)

    def __rsub__(self, other):
        return (-1) * self + other

    def __rmul__(self, other):
        return self * other

    def __radd__(self, other):
        return self + other


class Atom(Term):

    def __init__(self, name, sort_key):
        self.name = name
        self.sort_key = sort_key

    def __str__(self):
        return self.name

    def __cmp__(self, other):
        if isinstance(other, Atom):
            return cmp(self.sort_key, other.sort_key)
        else:
            return -1


class AppTerm(Term):

    def __init__(self, func, args, sort_key):
        self.func = func
        self.args = args
        self.sort_key = sort_key

    def __str__(self):
        args = [str(a) for a in self.args]
        return str(self.func)+'('+', '.join(args)+')'

    def __cmp__(self, other):
        if isinstance(other, Atom):
            return 1
        else:
            j = cmp(self.sort_key, other.sort_key)
            if j == 0:
                return cmp(self.args, other.args)
            else:
                return j



####################################################################################################
#
# STerm
#
####################################################################################################


class STerm:

    def __init__(self, coeff, term):
        self.coeff = fractions.Fraction(coeff)
        self.term = term

    def __str__(self):
        if self.coeff == 1:
            return str(self.term)
        elif isinstance(self.term, One):
            return str(self.coeff)
        else:
            return str(self.coeff) + "*" + str(self.term)

    def __repr__(self):
        return self.__str__()

    def __cmp__(self, other):
        j = cmp(self.term, other.term)
        if j==0:
            return cmp(self.coeff,other.coeff)
        else:
            return j

    def __add__(self, other):
        if isinstance(self.term, AddTerm):
            return self.coeff * self.term + other    # first term is an AddTerm
        elif isinstance(other, numbers.Rational):
            return self + Rational_to_STerm(other)
#        elif isinstance(other, MulPair):
#            return self + MulPair_to_Term(other)
        elif isinstance(other, AddTerm):
            return other + self
        elif isinstance(other, Term):
            if self.term == other:
                return STerm(self.coeff + 1, self.term)
            else:
                return AddTerm([self, STerm(1, other)])
        elif isinstance(other, STerm):
            if isinstance(other.term, AddTerm):
                return other.coeff * other.term + self
            else:
                if self.term == other.term:
                    if self.coeff + other.coeff == 0:
                        return STerm(0, One())
                    else:
                        return STerm(self.coeff + other.coeff, self.term)
                else:
                    return AddTerm([self, other])
        else:
            raise Error('Cannot add STerm')

    def __mul__(self, other):
        if isinstance(other, numbers.Rational):
            return STerm(self.coeff * other, self.term)
        elif isinstance(other, Term):
            return STerm(self.coeff, self.term * other)
        elif isinstance(other, STerm):
            return STerm(self.coeff * other.coeff, self.term / other.term)

    def __div__(self, other):
        if isinstance(other, numbers.Rational):
            if other == 0:
                Error('Divide by 0')
            else:
                return STerm(self.coeff / other, self.term)
        elif isinstance(other, Term):
            return STerm(self.coeff, self.term / other)
        elif isinstance(other, STerm):
            if (other.coeff == 0):
                Error('Divide by 0')
            else:
                return STerm(self.coeff / other.coeff, self.term / other.term)

    def __pow__(self, n):
        if isinstance(n, (int, long)):
            Error('Non integer power')    # TODO: for now, we only handle integer powers
        else:
            return STerm(pow(self.coeff, n), MulPair(self.term, n))


####################################################################################################
#
# MulPair
#
####################################################################################################


class MulPair():

    def __init__(term, exponent):
        self.term = term
        self.power = exponent

    def __cmp__(self, other):
        return cmp((self.term, self.power), (other.term, other.power))

    def __add__(self, other):
        return MulPair_to_Term(self) + other

    def __radd__(self, other):
        return self + other

    def __mul__(self, other):
        return MulPair_to_Term(self) * other

    def __rmul__(self, other):
        return self * other


####################################################################################################
#
# Subclasses of Atom
#
####################################################################################################


class One(Atom):

    def __init__(self):
        Atom.__init__(self, '1', sort_key=(10, 0))


class Var(Atom):

    def __init__(self, name):
        Atom.__init__(self, name, sort_key=(20, name))


class IVar(Atom):

    def __init__(self, index):
        self.index = index
        Atom.__init__(self, 't' + str(index), sort_key=(30, index))


class UVar(Atom):

    def __init__(self, index):
        self.index = index
        Atom.__init__(self, 'u' + str(index), sort_key=(40, index))


def _str_to_list(s):
    if ',' in s:
        return [item.strip() for item in s.split(',')]
    elif ' ' in s:
        return [item.strip() for item in s.split()]
    else:
        return [s]


def Vars(name_str):
    """
    Create a list of variables

    Examples:
      x, y, z = Vars('x, y, z')
      a, b, c = Vars('a b c')
    """
    names = _str_to_list(name_str)
    if len(names) == 1:
        return Var(names[0])
    else:
        vars = ()
        for name in names:
            vars += (Var(name),)
        return vars


####################################################################################################
#
# Subclasses of FuncTerm
#
####################################################################################################


class AddTerm(AppTerm):

    def __init__(self, args):
        AppTerm.__init__(self, 'sum', args, sort_key=(10, 'sum'))

    def __add__(self, other):
        if isinstance(other, fractions.Rational):
            return self + STerm(other, One())
        elif isinstance(other, AddTerm):
            result = self
            for s in other.args:
                result += s
            return result
        elif isinstance(other, Term):
            return self + STerm(1, other)
        elif isinstance(other, STerm):
            newargs = []
            newargs.extend(self.args)
            matches = [s for s in newargs if s.term == other.term ]
            if matches:
                s = matches[0]
                newargs.remove(s)
                if s.coeff != -other.coeff:
                    newargs.append(STerm(s.coeff + other.coeff, s.term))
            else:
                newargs.append(other)
            return AddTerm(newargs)


class MulTerm(AppTerm):

    def __init__(self, args):
        AppTerm.__init__(self, 'prod', args, sort_key=(20, 'prod'))


class AbsTerm(AppTerm):

    def __init__(self, args):
        AppTerm.__init__(self, 'abs', args, sort_key=(30, 'abs'))


class MinTerm(AppTerm):

    def __init__(self, args):
        AppTerm.__init__(self, 'min', args, sort_key=(40, 'min'))


class MaxTerm(AppTerm):

    def __init__(self, args):
        AppTerm.__init__(self, 'max', args, sort_key=(50, 'max'))


class FuncTerm(AppTerm):

    def __init__(self, name, args):
        AppTerm.__init__(self, name, args, sort_key=(60, name))


class Func():
    """
    User defined functions.

    Example:
      x, y, z = Vars('x, y, z')
      f = Func('f')
      print f(x, y, z)
    """

    def __init__(self, name, arity = None):
        self.name = name
        self.arity = arity

    def __call__(self, *args):
        if self.arity != None and len(args) != self.arity:
            raise Error('Wrong number of arguments to {0!s}'.format(func.name))

        return FuncTerm(self.name, args)


####################################################################################################
#
# Tests
#
####################################################################################################

if __name__ == '__main__':
    x, y, z = Vars('x, y, z')
    f = Func('f')
    print f(x, y, z)
    print x + y
    print x + x
    print x + (x + y)

