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
#     MinTerm  (max(x1, ..., xn) is represented by -min(-x1, ..., -xn))
#
# For all AppTerms other than AbsTerm and MulTerm, the arguments are STerms. The argument to abs(t)
# need only be a term, because the scalar can be brought outside. Each MulTerm is of the form
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
# TODO: would it be better to have one AppTerm, and put all the information into the Function?
#
####################################################################################################


import fractions
import numbers


class Error(Exception):
    pass


####################################################################################################
#
# Term
#
####################################################################################################


class Term:

    def __init__(self):
        pass

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        raise NotImplementedError()

    def __add__(self, other):
        # case where self is an AddTerm is handled in that class
        if isinstance(other, numbers.Rational):
            return self + STerm(other, One())
        elif isinstance(other, STerm):
            return other + self
        elif isinstance(other, Term):
            if isinstance(other, AddTerm):
                return other + self
            elif self == other:
                return STerm(2, self)
            else:
                return AddTerm([STerm(1, self), STerm(1, other)])
        else:
            raise Error('Cannot add Term {0!s} to {1!s}'.format(self, other))

    def __radd__(self, other):
        return self + other

    def __mul__(self, other):
        # case where self is a MulTerm is handled in that class
        if isinstance(self, One):
            return other
        elif isinstance(other, numbers.Rational):
            return STerm(other, self)
        elif isinstance(other, Term):
            if isinstance(other, One):
                return self
            if isinstance(other, MulTerm):
                return other * self
            elif self == other:
                return MulPair(self, 2)
            else:
                return MulTerm([MulPair(self, 1), MulPair(other, 1)])
        else:
            raise Error('Cannot multiply Term {0!s} by {1!s}'.format(self, other))

    def __neg__(self):
        return self * -1

    def __sub__(self, other):
        return self + other * -1

    def __rsub__(self, other):
        return (-1) * self + other

    def __rmul__(self, other):
        return self * other

    def __div__(self, other):
        return self * (other ** -1)

    def __rdiv__(self, other):
        return (self ** -1) * other

    def __truediv__(self, other):
        return self / other

    def __rtruediv__(self, other):
        return other * self ** (-1)

    def __pow__(self, n):
        return MulTerm([MulPair(self, n)])

    def __abs__(self):
        return AbsTerm(self)


class Atom(Term):

    def __init__(self, name, sort_key):
        Term.__init__(self)
        self.name = name
        self.sort_key = sort_key

    def __str__(self):
        return self.name

        # def __cmp__(self, other):
        #     if isinstance(other, Atom):
        #         return cmp(self.sort_key, other.sort_key)
        #     else:
        #         return -1


class AppTerm(Term):

    def __init__(self, func, args, sort_key):
        Term.__init__(self)
        self.func = func
        self.args = args
        self.sort_key = (sort_key, (a.sort_key for a in args))

    def __str__(self):
        args = [str(a) for a in self.args]
        return str(self.func) + '(' + ', '.join(args) + ')'


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
        variables = ()
        for name in names:
            variables += (Var(name),)
        return variables


####################################################################################################
#
# Subclasses of FuncTerm
#
####################################################################################################


class AddTerm(AppTerm):
    def __init__(self, args):
        AppTerm.__init__(self, 'sum', args, sort_key=(50, 'sum'))

    def __add__(self, other):
        args = list(self.args)
        # determine the list of STerms to add
        if isinstance(other, fractions.Rational):
            args2 = [STerm(other, One())] if other != 0 else []
        elif isinstance(other, AddTerm):
            args2 = other.args
        elif isinstance(other, Term):
            args2 = [STerm(1, other)]
        elif isinstance(other, STerm):
            if other.coeff == 0:
                args2 = []
            elif isinstance(other.term, AddTerm):
                args2 = [a * other.coeff for a in other.term.args]
            else:
                args2 = [other]
        else:
            raise Error('Cannot add AddTerm {0!s} and {1!s}'.format(self, other))
            # add each argument in args2 to args
        for b in args2:
            for a in args:
                if b.term.sort_key == a.term.sort_key:
                    args.remove(a)
                    if a.coeff != -b.coeff:
                        args.append(STerm(a.coeff + b.coeff, a.term))
                    break
            else:
                args.append(b)
        return AddTerm(args) if args else STerm(0, One())


class MulTerm(AppTerm):
    def __init__(self, args):
        AppTerm.__init__(self, 'prod', args, sort_key=(60, 'prod'))

    def __mul__(self, other):
        args = list(self.args)
        scalar = 1
        # determine the list of MulPairs to multiply, and possibly a scalar
        if isinstance(other, fractions.Rational):
            scalar = other
            args2 = []
        elif isinstance(other, One):
            args2 = []
        elif isinstance(other, MulTerm):
            args2 = other.args
        elif isinstance(other, Term):
            args2 = [MulPair(other, 1)]
        elif isinstance(other, STerm):
            scalar = other.coeff
            if isinstance(other.term, MulTerm):
                args2 = other.term.args
            else:
                args2 = [MulPair(other.term, 1)]
        else:
            raise Error('Cannot multiply MulTerm {0!s} by {1!s}'.format(self, other))
            # multiply args by each argument in args2
        for b in args2:
            for a in args:
                if b.term.sort_key == a.term.sort_key:
                    args.remove(a)
                    if a.exponent != -b.exponent:
                        args.append(MulPair(a.term, a.exponent + b.exponent))
                    break
            else:
                args.append(b)
        if scalar == 0:
            return STerm(0, One())
        else:
            result = MulTerm(args) if args else One()
            return result if scalar == 1 else STerm(scalar, result)


class AbsTerm(AppTerm):
    def __init__(self, args):
        AppTerm.__init__(self, 'abs', args, sort_key=(70, 'abs'))


class MinTerm(AppTerm):
    def __init__(self, args):
        AppTerm.__init__(self, 'min', args, sort_key=(80, 'min'))


class FuncTerm(AppTerm):
    def __init__(self, name, args):
        AppTerm.__init__(self, name, args, sort_key=(90, name))


class Func():
    """
    User defined functions.

    Example:
      x, y, z = Vars('x, y, z')
      f = Func('f')
      print f(x, y, z)
    """

    def __init__(self, name, arity=None):
        self.name = name
        self.arity = arity

    def __call__(self, *args):
        if self.arity is not None and len(args) != self.arity:
            raise Error('Wrong number of arguments to {0!s}'.format(self.name))

        return FuncTerm(self.name, args)


####################################################################################################
#
# STerm
#
####################################################################################################


class STerm:
    def __init__(self, coeff, term):
        self.coeff = fractions.Fraction(coeff)
        if coeff != 0:
            self.term = term
        else:
            self.term = One()
            self.sort_key = (term.sort_key, coeff)

    def __str__(self):
        if self.coeff == 1:
            return str(self.term)
        elif isinstance(self.term, One):
            return str(self.coeff)
        else:
            return str(self.coeff) + "*" + str(self.term)

    def __repr__(self):
        return self.__str__()

    def __add__(self, other):
        if isinstance(self.term, AddTerm):
            return self.coeff * self.term + other    # make first term an AddTerm
        elif isinstance(other, numbers.Rational):
            return self + STerm(other, One())
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
                if self.term.sort_key == other.term.sort_key:
                    if self.coeff + other.coeff == 0:
                        return STerm(0, One())
                    else:
                        return STerm(self.coeff + other.coeff, self.term)
                else:
                    return AddTerm([self, other])
        else:
            raise Error('Cannot add STerm')

    def __radd__(self, other):
        return other + self

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
            if other.coeff == 0:
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


class MulPair:
    def __init__(self, term, exponent):
        self.term = term
        self.exponent = exponent
        self.sort_key = (term.sort_key, exponent)

    def __str__(self):
        return '({0!s} ^ {1!s})'.format(self.term, self.exponent)


####################################################################################################
#
# Tests
#
####################################################################################################

if __name__ == '__main__':
    u, v, w, x, y, z = Vars('w, v, w, x, y, z')
    f = Func('f')
    g = Func('g')

    print f(x, y, z)
    print x + y
    print x + x
    print x + (x + y)
    print x
    print (x + y) + (z + x)
    print x * y
    print 2 * x * y
    print 2 * (x + y) * w
    print 2 * ((x + y) ** 5) * g(x) * (3 * (x * y + f(x) + 2 + w) ** 2)
