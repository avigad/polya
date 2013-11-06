from fractions import Fraction, gcd
from string import find, count, split
from copy import deepcopy


# use this for errors in this module
class Error(Exception):
    pass


class Contradiction(Error):
    pass

    
# kinds of inequalities
GT, GE, LE, LT = range(4)
comp_str = {GT: '>', GE: '>=', LT: '<', LE: '<='}


# swaps GT and LT, GE and LE
def comp_reverse(i):
    return 3 - i

# swaps GT and LE, GE and LT
def comp_negate(i):
    return (i+2) % 4

# to record where each fact came from
ADD, MUL, HYP, FUN = range(4)

#Used in heuristic and polyhedron_util
cdict = {LE:(lambda x,y: x<=y),LT:(lambda x,y:x<y),GE:(lambda x,y:x>=y),GT:(lambda x,y: x>y)}

###############################################################################
#
# TERMS
#
# Add_pair(a1, t1) represents a1 * t1
#
# Add_term([(a1, t1), ..., (ak, tk)]) represents a1 * t1 + ... + ak * tk
#   stored internally as a list of Add_pair's
#
# Mul_pair((t1, n1)) represents t1 ^ n1
#
# Mul_term([(t1, n1), ..., (tk, nk)]) represents t1 ^ n1 * .... * tk ^ nk
#   stored internally as a list of Mul_pairs
#
# Func_term(f,[t1,...,tn]) represents f(t1,t2,...,tn)
#
# An ordering on expressions is defined recursively, using Python's
#   built-in lexicographic orderings on pairs and lists
#
# TODO: canonize should check for duplicates and combine them
# TODO: complete documentation
###############################################################################


class Term:

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        raise NotImplementedError()
        
    def __truediv__(self, other):
        return self / other
    
    def __rtruediv__(self, other):
        return other * self ** (-1)
    
    def __rdiv__(self, other):
        return (self ** (-1)) * other
    
    def __neg__(self):
        return self * (-1)
    
    def __sub__(self, other):
        return self +other * (-1)
    
    def __rsub__(self, other):
        return (-1) * self +other
    
    def __rmul__(self, other):
        return self * other

    def __radd__(self, other):
        return self +other
    
    def __lt__(self,other):
        if other==0:
            return Zero_comparison(self,LT)
        elif isinstance(other,Term):
            return Zero_comparison(self-other,LT)
        elif isinstance(other,(Fraction,int)):
            return Zero_comparison(self-one*other,LT)
        elif isinstsance(other,float):
            return Zero_comparison(self-one*Fraction(other),LT)
        else:
            raise Exception("Bad term comparison.")
        
    def __rlt__(self,other):
        raise Exception()

    def __le__(self,other):
        if other==0:
            return Zero_comparison(self,LE)
        elif isinstance(other,Term):
            return Zero_comparison(self-other,LE)
        elif isinstance(other,(Fraction,int)):
            return Zero_comparison(self-one*other,LE)
        elif isinstsance(other,float):
            return Zero_comparison(self-one*Fraction(other),LE)
        else:
            raise Exception("Bad term comparison.")
        
    def __rgt__(self,other):
        raise Exception()
        
    def __gt__(self,other):
        if other==0:
            return Zero_comparison(self,GT)
        elif isinstance(other,Term):
            return Zero_comparison(self-other,GT)
        elif isinstance(other,(Fraction,int)):
            return Zero_comparison(self-one*other,GT)
        elif isinstsance(other,float):
            return Zero_comparison(self-one*Fraction(other),GT)
        else:
            raise Exception("Bad term comparison.")
        
    def __ge__(self,other):
        if other==0:
            return Zero_comparison(self,GE)
        elif isinstance(other,Term):
            return Zero_comparison(self-other,GE)
        elif isinstance(other,(Fraction,int)):
            return Zero_comparison(self-one*other,GE)
        elif isinstsance(other,float):
            return Zero_comparison(self-one*Fraction(other),GE)
        else:
            raise Exception("Bad term comparison.")
        
    def __hash__(self):
        return hash(str(self))

class Const(Term):

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name
        #return "Const({0!s})".format(self.name)

    def __cmp__(self, other):
        if isinstance(other, Const):
            return cmp(self.name, other.name)
        else:
            return -1
            
    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return Const("0")
            elif other == 1:
                return self
            else:
                return Add_term(Add_pair(other,self))
#                num = Fraction(self.name)
#                return Const(str(num * other))
        return other * self

    def __add__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return self
            return Add_term([Add_pair(1, self), Add_pair(other, one)])
            
        if isinstance(other, Add_term):
            addpairs = other.addpairs
            coeff = 1
            pair = next((p for p in addpairs if p.term == self), None)
            if pair:
                addpairs.remove(pair)
                coeff = pair.coeff + 1
            
            addpairs.append(Add_pair(coeff, self))
            return Add_term(addpairs)
            
        return Add_term([Add_pair(1, self), Add_pair(1, other)])

    def __pow__(self, other):
        if not isinstance(other, (int, float, Fraction)):
            raise Exception("Cannot have variables in the exponent")
        if other == 0:
            return one
        if other == 1:
            return self
            
        return Mul_term(Mul_pair(self, other))
        
    def __div__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                raise Exception("Cannot divide by 0")
            if other == 1:
                return self
                
            coeff = (1 / Fraction(other) if isinstance(other, float)\
                     else Fraction(1, other))
            return Add_term([Add_pair(coeff, self)])
            
        return self * other ** (-1)

    def structure(self):
        return "Const"

class LogConst(Const):
    def __init__(self,val):
        self.name = 'log('+str(val)+')'
        self.val = val

one = Const("1")
zero = Const("0")


class Var(Term):

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __cmp__(self, other):
        if isinstance(other, Const):
            return 1
        elif isinstance(other, Var):
            return cmp(self.name, other.name)
        else:
            return -1
            
    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return zero
            if other == 1:
                return self
            return Add_term([Add_pair(other, self)])
            
        if isinstance(other, Mul_term):
            mulpairs = other.mulpairs
            mulpairs.append(Mul_pair(self, 1))
            return Mul_term(mulpairs)
            
        return Mul_term([Mul_pair(self, 1), Mul_pair(other, 1)])

    def __add__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return self
            return Add_term([Add_pair(1, self), Add_pair(other, one)])
            
        if isinstance(other, Add_term):
            addpairs = other.addpairs
            coeff = 1
            pair = next((p for p in addpairs if p.term == self), None)
            if pair:
                addpairs.remove(pair)
                coeff = pair.coeff + 1
            
            addpairs.append(Add_pair(coeff, self))
            return Add_term(addpairs)
            
        return Add_term([Add_pair(1, self), Add_pair(1, other)])

    def __pow__(self, other):
        if not isinstance(other, (int, float, Fraction)):
            raise Exception("Cannot have variables in the exponent "+str(other)+' '+str(type(other)))
        if other == 0:
            return one
        if other == 1:
            return self
            
        return Mul_term(Mul_pair(self, other))
        
    def __div__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                raise Exception("Cannot divide by 0")
            if other == 1:
                return self
                
            coeff = (1 / Fraction(other) if isinstance(other, float)\
                     else Fraction(1 / other))
            return Add_term([Add_pair(coeff, self)])
            
        return self * other ** (-1)

    def structure(self):
        return "Var"
        

class Add_pair:
    
    def __init__(self, coeff, term):
        self.coeff = coeff
        self.term = term

    def __str__(self):
        if self.coeff == 1:
            return str(self.term)
        elif self.term == one:
            return str(self.coeff)
        else:
            return str(self.coeff) + "*" + str(self.term)

    def __repr__(self):
        return self.__str__()

    def __cmp__(self, other):
        j = cmp(self.term,other.term)
        if j==0:
            return cmp(self.coeff,other.coeff)
        return j
        #return cmp((self.term, self.coeff), (other.term, other.coeff))

    # used only to scale an addpair by a constant
    def __div__(self, factor):
        num = (Fraction(self.coeff) if isinstance(self.coeff, float)\
               else self.coeff)
        denom = (Fraction(factor) if isinstance(factor, float) else factor)
        return Add_pair(Fraction(num, denom), self.term)

    def __mul__(self, factor):
        return Add_pair(self.coeff * factor, self.term)

    # this is useful for canonization
    def __pow__(self, n):
        return Add_pair(pow(Fraction(self.coeff), n), Mul_pair(self.term, n))


class Add_term(Term):

    def __init__(self, l):
        if isinstance(l, Term):
            self.addpairs = [Add_pair(1, l)]
        elif isinstance(l, Add_pair):
            self.addpairs = [l]
        elif isinstance(l, list):
            if not l:
                self.addpairs = l
            elif isinstance(l[0], Add_pair):
                self.addpairs = l
            else:
                self.addpairs = [Add_pair(p[0], p[1]) for p in l]
        else:
            raise Error("Add_term of:" + str(l))

    def __str__(self):
        return ("(" + " + ".join([str(a) for a in self.addpairs]) + ")")

    def __cmp__(self, other):
        if isinstance(other, (Const, Var)):
            return 1
        elif isinstance(other, Add_term):
            return cmp(self.addpairs, other.addpairs)
        else:
            return -1

    # used to scale by a constant
    def __div__(self, factor):
        if isinstance(factor, (int, float, Fraction)):
            return Add_term([s / (Fraction(factor)\
                                  if isinstance(factor, float) else factor)\
                             for s in self.addpairs])
        return self * factor ** (-1)

    def __mul__(self, factor):
        if isinstance(factor, (int, float, Fraction)):
            return Add_term([s * factor for s in self.addpairs])
        if isinstance(factor, Mul_term):
            mulpairs = factor.mulpairs
            mulpairs.append(Mul_pair(self, 1))
            return Mul_term(mulpairs)
        
        return self * Mul_term([Mul_pair(factor, 1)])

    def __add__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return self
            return self +Add_term([Add_pair(other, one)])
            
        if isinstance(other, Add_term):
            addpairs = []
            addpairs.extend(self.addpairs)
            for a in other.addpairs:
                for b in addpairs:
                    if b.term == a.term:
                        addpairs.remove(b)
                        if a.coeff != -b.coeff:
                            addpairs.append(Add_pair(a.coeff + b.coeff, a.term))
                        break
                else:
                    addpairs.append(a)
            # if not addpairs:
                # print self, other
                # raise Error("Add_term zero")
                # return zero
            return(Add_term(addpairs))
            
        return self +Add_term([Add_pair(1, other)])

    def __pow__(self, other):
        if not isinstance(other, (int, float, Fraction)):
            raise Exception("Cannot have variables in the exponent")
            
        if other == 0:
            return one
        if other == 1:
            return self
            
        return Mul_term(Mul_pair(self, other))

    def structure(self):
        s = "AddTerm("
        for t in self.addpairs:
            s += t.term.structure() + ","
        s = s[:-1] + ")"
        return s
        

class Mul_pair:
    
    def __init__(self, term, exp):
        self.term = term
        self.exp = exp

    def __str__(self):
        if self.exp == 1:
            return str(self.term)
        else:
            return str(self.term) + "^" + str(self.exp)
            
    def __repr__(self):
        return self.__str__()

    def __cmp__(self, other):
        if isinstance(other,Mul_pair):
            j = cmp(self.term,other.term)
            if j==0:
                return cmp(self.exp,other.exp)
            return j
#            return cmp((self.term, self.exp), (other.term, other.exp))
        return -1

    def __pow__(self, n):
        if isinstance(n, int) or \
               (isinstance(n, Fraction) and n.denominator % 2 == 1):
            return Mul_pair(self.term, self.exp * n)
        else:
            return Mul_pair(Mul_term([self]), n)


# allow a constant multiplier, for the multiplicative part
class Mul_term(Term):

    def __init__(self, l, const=1):
        self.const = const
        if isinstance(l, Term):
            self.mulpairs = [Mul_pair(l, 1)]
        elif isinstance(l, Mul_pair):
            self.mulpairs = [l]
        elif isinstance(l, list):
            if not l:
                self.mulpairs = l
            elif isinstance(l[0], Mul_pair):
                self.mulpairs = l
            else:
                self.mulpairs = [Mul_pair(p[0], p[1]) for p in l]
        else:
            raise Error("Mul_term of: " + str(l))
        for item in self.mulpairs:
            if not isinstance(item, Mul_pair):
                print item, 'is not a mul_pair!'
                raise Exception
 
    def __str__(self):
        if self.const == 1:
            factorlist = []
        else:
            factorlist = [str(self.const)]
        factorlist.extend([str(m) for m in self.mulpairs])
        return "(" + " * ".join(factorlist) + ")"

    def __cmp__(self, other):
        if isinstance(other, (Const, Var, Add_term, Func_term)):
            return 1
        else:
            return cmp(self.mulpairs, other.mulpairs)

    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return zero
            con = self.const * other
            return Mul_term(self.mulpairs, con)
        
        if isinstance(other, Mul_term):
            mulpairs = list(self.mulpairs)
            for a in other.mulpairs:
                for b in mulpairs:
                    if b.term == a.term:
                        mulpairs.remove(b)
                        if a.exp != -b.exp:
                            mulpairs.append(Mul_pair(a.term, a.exp + b.exp))
                        break
                else:
                    mulpairs.append(a)
            return Mul_term(mulpairs, self.const * other.const)
            
        return self * Mul_term([Mul_pair(other, 1)])

    def __add__(self, other):
        if isinstance(other, (int, float, Fraction)):
            if other == 0:
                return self
            return Add_term([Add_pair(other, one)]) + self
            
        if isinstance(other, Mul_term):
            return Add_term([Add_pair(1, self), Add_pair(1, other)])
                
        return other + self

    def __pow__(self, n):
        if not isinstance(n, (int, float, Fraction)):
            raise Exception("Cannot have variables in the exponent")
        mulpairs = [pow(m, n) for m in self.mulpairs]
        return Mul_term(mulpairs, pow(Fraction(self.const), n))

    def __div__(self, other):
        return self * pow(other, -1)

    def structure(self):
        s = "MulTerm("
        for t in self.mulpairs:
            s += t.term.structure() + ","
        s = s[:-1] + ")"
        return s

class Func():
    def __init__(self, name):
        self.name = name
        
    def __call__(self, *args):
        return Func_term(self.name, args)

class Func_term(Term):
    
    def __init__(self, name, args, const=1):
        self.name = name
        self.args = []
        for a in args:
            if isinstance(a, Term):
                self.args.append(Add_pair(1,a))
            elif isinstance(a, Add_pair):
                self.args.append(a)
            else:
                print 'a is not a term, but a... ?', type(a)
                print a
                self.args.append(eval(a))
        self.const = const
        
    def __add__(self, other):
        if isinstance(other, Add_term):
            return other + self
        if isinstance(other, Func_term) and\
               other.name == self.name and other.args == self.args:
            if other.const + self.const == 0:
                return zero
            return Func_term(self.name, self.args, other.const + self.const)
        return Add_term([Add_pair(1, other)]) + self
    
    def __mul__(self, other):
        if isinstance(other, (int, float, Fraction)):
            return Func_term(self.name, self.args, self.const * other)
        if isinstance(other, Mul_term):
            return other * self
        return Mul_term([Mul_pair(other, 1)]) * self
    
    def __div__(self, other):
        return self * pow(other, -1)

    def __pow__(self, n):
        if not isinstance(n, (int, float, Fraction)):
            raise Exception("Cannot have variables in the exponent")
        return Mul_term([Mul_pair(self, n)])

    def __cmp__(self, other):
        if isinstance(other, Func_term):
            if other.name != self.name:
                return cmp(self.name, other.name)
            return cmp(self.args, other.args)
        return 1
    
        
    def __str__(self):
        s = ('' if self.const == 1 else str(self.const) + '*') + self.name + '('
        for a in self.args:
            s += str(a) + ', '
        s = s[:-2] + ')'
        return s
    
    def structure(self):
        s = ('' if self.const == 1 else str(self.const)) + 'Func_term('
        for a in self.args:
            s += a.structure() + ','
        s = s[:-1] + ')'
        return s
        
###############################################################################
#
# AXIOM CLASSES
#
###############################################################################

# Maps UVar indices to (c, j) where c is a constant and j is an IVar index
class Environment:
    def __init__(self,map={}):
        self.map = map
        
    def assign(self,x,y):
        self.map[x]=y
        
    def val(self,x):
        return self.map[x]
    
    def keys(self):
        return self.map.keys()
    
    def __str__(self):
        return str(self.map)
    
    def __repr__(self):
        return self.__str__()    
    
    def __hash__(self):
        return hash(str(self))
    
    def __cmp__(self,other):
        return cmp(str(self),str(other))
    
        
class No_Term_Exception(Exception):
    pass
        
        
# Represents one clause of an axiom: S(v_1...v_n) comp T(v_1...v_n),
# where S and T are Terms.
class Axiom_clause:
    def __init__(self,lterm,comp,coeff, rterm):
        self.lterm,self.comp,self.coeff,self.rterm = lterm,comp,coeff,rterm
        
    def __str__(self):
        return str(self.lterm)+' '+comp_str[self.comp]+' '+str(self.coeff) + '*'+str(self.rterm)
    
    def __repr__(self):
        return self.__str__()
        

        
# Represents an uninstantiated axiom.
# Clauses is a list of Axiom_clauses.
# The content of the axiom is that at least one element of clauses is true.
class Axiom:
    def __init__(self, clauses):
        
        #takes a term
        #returns two Sets. The first is all uvars that occur in the term.
        #The second is all uvars that occur alone as function arguments in the term.
        def find_uvars(term):
            if isinstance(term, UVar):
                return set([term]),set()
            elif isinstance(term, (Var,Const)):
                return set(),set()
            else:
                vars = set()
                arg_vars = set()
                if isinstance(term, Add_term):
                    pairs = term.addpairs
                elif isinstance(term, Mul_term):
                    pairs = term.mulpairs
                elif isinstance(term, Func_term):
                    pairs = term.args
                    arg_vars = set([p.term for p in pairs if isinstance(p.term, UVar)])
                for p in pairs:
                    nvars, narg_vars = find_uvars(p.term)
                    vars.update(nvars)
                    arg_vars.update(narg_vars)
                    
                return vars, arg_vars

        self.clauses = clauses
        uvars = set()
        arg_uvars = set()
        for c in clauses:
            nvars, narg_vars = find_uvars(c.lterm)
            uvars.update(nvars)
            arg_uvars.update(narg_vars)
            nvars, narg_vars = find_uvars(c.rterm)
            uvars.update(nvars)
            arg_uvars.update(narg_vars)
        
        self.vars, self.arg_vars = uvars, arg_uvars
        
    def __str__(self):
        s = '{For all '
        for u in self.vars:
            s+=str(u)+', '
        s = s[:-2]+': '+str(self.clauses)+'}'
        return s
                
        

# This class represents an instantiated axiom.
# Satisfied Axiom_insts cannot produce any new information and can be deleted.
# clauses is a dictionary, mapping (i,j) to a list of Comparison_datas.
# clauses represents a disjunction: at least one Comparison_data must be true.
class Axiom_inst:
    def __init__(self,clauses, origin=''):
        self.clauses = clauses
        self.satisfied = False
        self.origin = origin
        
    def __str__(self):
        s = ''
        for (i,j) in self.clauses:
            for comp in self.clauses[i,j]:
                s+= '{'+comp.to_string(IVar(i),IVar(j))+'} or '
        s = s[:-4]
        return s 
    
    def __repr__(self):
        return str(self)
        
    # Checks to see if any clauses can be eliminated based on info.
    # Info is a set of pairs (i,j) representing new comparison info about (i,j) in H
    # If there is only one disjunction left in the list, sends it to be learned by H.
    def update_on_info(self,H,info):
        #print 'updating:',str(self)
        for (i,j) in info.intersection(self.clauses.keys()):
            #print ' looking at',[c.to_string(IVar(i),IVar(j)) for c in self.clauses[i,j]]
            comps = [c for c in self.clauses[i,j] if not H.implies(i,j,comp_negate(c.comp),c.coeff)]
            #print ' comps:',comps
            if len(comps)==0:
                del self.clauses[(i,j)] #self.clauses.pop(i,j)?
                #H.raise_contradiction(FUN)
            else:
                self.clauses[i,j] = comps
                
            for comp in comps:
                if H.implies(i,j,comp.comp,comp.coeff):
                    #This disjunction is satisfied. Nothing new to be learned.
                    self.satisfied = True
                    return
        if len(self.clauses.keys())==1 and len(self.clauses[self.clauses.keys()[0]])==1:
            #There is one statement left in the disjunction. It must be true.
            i,j = self.clauses.keys()[0]
            comp = list(self.clauses[i,j])[0]
            H.learn_term_comparison(i,j,comp.comp,comp.coeff,FUN)
            self.satisfied = True
        elif len(self.clauses.keys())==0:
            print 'Contradiction found from axiom:',self.origin
            H.raise_contradiction(FUN)

###############################################################################
#
# COMPARISON CLASSES
#
###############################################################################

# Comparison and its subclasses are used in the Boole interface.
# Not currently needed.


# class Comparison():
#     def __init__(self):
#         self.dir = None
#         self.left = None
#         self.right = None
#     
#     # Returns a canonized Zero_comparison
#     def canonize(self):
#         term = self.left - self.right
#         zero_comp = Zero_comparison(term, self.dir)
#         return canonize_zero_comparison(zero_comp)
# 
#     def __str__(self):
#         return "{0!s}{1!s}{2!s}"\
#                .format(self.left, comp_str[self.dir], self.right)
# 
#     def neg(self):
#         """Return the negated comparison
#         """
#         raise NotImplementedError()
# 
#     
# class CompGT(Comparison):
#     # Left and right are terms
#     def __init__(self, left, right):
#         Comparison.__init__(self)
#         self.dir = GT
#         self.left = left
#         self.right = right
# 
#     def neg(self):
#         return CompLE(self.left, self.right)
# 
# 
# class CompGE(Comparison):
#     # Left and right are terms
#     def __init__(self, left, right):
#         Comparison.__init__(self)
#         self.dir = GE
#         self.left = left
#         self.right = right
# 
#     def neg(self):
#         return CompLT(self.left, self.right)
# 
# 
# class CompLT(Comparison):
#     # Left and right are terms
#     def __init__(self, left, right):
#         Comparison.__init__(self)
#         self.dir = LT
#         self.left = left
#         self.right = right
# 
#     def neg(self):
#         return CompGE(self.left, self.right)
# 
# 
# class CompLE(Comparison):
#     # Left and right are terms
#     def __init__(self, left, right):
#         Comparison.__init__(self)
#         self.dir = LE
#         self.left = left
#         self.right = right
# 
#     def neg(self):
#         return CompGT(self.left, self.right)


# Comparison between one term a_i and 0
# a_i comp 0
class Equality_data:
    
    def __init__(self,coeff,provenance):
        self.coeff = coeff
        self.provenance = provenance

class Zero_comparison_data:

    def __init__(self, comp, provenance=None):
        self.comp = comp
        self.provenance = provenance

    def to_string(self, term):
        return str(term) + ' ' + comp_str[self.comp] + ' 0'
    


# comparison between two terms, a_i and a_j
# a_i comp coeff * a_j
class Comparison_data:

    def __init__(self, comp, coeff=1, provenance=None):
        self.comp = comp
        self.coeff = coeff
        self.provenance = provenance

    def to_string(self, term1, term2):
        if self.coeff == 1:
            return str(term1) + ' ' + comp_str[self.comp] + ' ' + str(term2)
        else:
            return (str(term1) + ' ' + comp_str[self.comp] + ' ' + \
                    str(self.coeff) + '*' + str(term2))

    def __str__(self):
        return 'comparison: ' + comp_str[self.comp] + ' ' + str(self.coeff)
        
    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(self.__str__())
    
    # used to figure out strength of inequalities
        
    def ge(self, other):
        if (self.comp in [LT, LE] and other.comp in [GT, GE]) \
               or (self.comp in [GT, GE] and other.comp in [LT, LE]):
            return True
        return self.coeff > other.coeff \
               or (self.coeff == other.coeff and self.comp in [LT, GT] \
                   and other.comp in [LE, GE])
        
    def le(self, other):
        if (self.comp in [LT, LE] and other.comp in [GT, GE]) \
               or (self.comp in [GT, GE] and other.comp in [LT, LE]):
            return True
        return self.coeff < other.coeff \
               or (self.coeff == other.coeff and self.comp in [LT, GT] \
                   and other.comp in [LE, GE])

    def __cmp__(self, other):
        if self.coeff == other.coeff and self.comp == other.comp:
            return 0
        return 1


# Stores term comp 0
# Used in the additive routine
class Zero_comparison:

    def __init__(self, term, comp):
        self.term = term
        self.comp = comp

    def __str__(self):
        return str(self.term) + ' ' + comp_str[self.comp] + ' 0'

    def __repr__(self):
        return self.__str__()
    
    def __eq__(self, other):
        if not isinstance(other, Zero_comparison):
            return False
        return self.comp == other.comp and self.term == other.term


# The multiplicative procedure makes use of inequalities like t > 1, where
# t is a Mul_term.
class One_comparison:

    def __init__(self, term, comp):
        self.term = term
        self.comp = comp

    def __str__(self):
        return str(self.term) + ' ' + comp_str[self.comp] + ' 1'

    def __repr__(self):
        return self.__str__()
    
    def __hash__(self):
        return hash(str(self))

###############################################################################
#
# CANONIZING TERMS
#
# A canonical term is one of the following
#   a variable or the constant 1
#   an additive term ((a1, t1), ..., (a1, tk)) where
#     each ti is a canonical term
#       (variable, the constant 1, or multiplicative)
#     t1 < t2 < ... < tk
#     a1 = 1 (so the term is normalized)
#   a multiplicative term ((t1, n1), ..., (tk, nk)) where
#     each ti is a canonical term (variable or additive)
#     n1 < n2 < ... < nk
#
# Add_pair(r, t) is said to be canonical if t is a canonical term.
#
# "canonize" converts any term to a canonical Add_pair
#
# The order for sorting is built into the term classes.
#
###############################################################################


def product(l):
    return reduce((lambda x, y: x * y), l, 1)


# returns an Add_pair
def canonize(t):
    if isinstance(t, Const) or isinstance(t, Var):
        return Add_pair(1, t)
    elif isinstance(t, Add_term):
        addpairs = [canonize(p.term) * p.coeff for p in t.addpairs]
        addpairs.sort()
        coeff = addpairs[0].coeff
        if coeff == 0:
            print 'problem in canonize:', t, addpairs
        term = Add_term([p / coeff for p in addpairs])
        if len(term.addpairs) == 1:
            coeff = coeff * term.addpairs[0].coeff
            term = term.addpairs[0].term
        return Add_pair(coeff, term)
    elif isinstance(t, Mul_term):
        mulpairs = [pow(canonize(p.term), p.exp) for p in t.mulpairs]
        mulpairs.sort()
        coeff = product([p.coeff for p in mulpairs]) * t.const
        term = Mul_term([p.term for p in mulpairs])
        return Add_pair(coeff, term)
    elif isinstance(t, Func_term):
        args = t.args
        nargs = []
        for p in args:
            cp = canonize(p.term)
            nargs.append(Add_pair(p.coeff*cp.coeff,cp.term))
        term = Func_term(t.name, nargs, 1)
        return Add_pair(t.const, term)


def test_canonize():
    x = Var("x")
    y = Var("y")
    z = Var("z")
    t1 = Mul_term([(Add_term([(2, x), (-3, y), (1, z)]), 3), (x, 2)])
    t2 = Mul_term([(Add_term([(2, x), (-5, y), (1, z)]), 3), (x, 2)])
    t3 = Mul_term([(x, 2), (Add_term([(-3, y), (1, z), (2, x)]), 3)])

    print "t1 =", t1
    print "t2 =", t2
    print "t3 =", t3
    print "t1 < t2:", t1 < t2
    print "t1 < x:", t1 < x
    print "t1 == t3:", t1 == t3

    print "Canonize t1:", canonize(t1)
    print "Canonize t2:", canonize(t2)
    print "Canonize t3:", canonize(t3)
    print "Canonize x:", canonize(x)
    print "canonize(t1) == canonize(t2):", canonize(t1) == canonize(t3)


# Takes an (uncanonized) Zero_comparison.
# Returns a canonized Zero_comparison with positive coefficient.
def canonize_zero_comparison(h):
    canon = canonize(h.term)
    if canon.coeff > 0:
        return Zero_comparison(canon.term, h.comp)
    elif canon.coeff < 0:
        return Zero_comparison(canon.term, comp_reverse(h.comp))
    else:
        raise Error("0 in hypothesis")
    

###############################################################################
#
# NAMING SUBTERMS
#
# The heuristic procedure starts by naming all subterms. We'll use
# "IVars" for the name, e.g. a0, a1, a2, ...
#
###############################################################################

class UVar(Term, Var):

    def __init__(self, index):
        Var.__init__(self, "v" + str(index))
        self.index = index

    def __str__(self):
        return self.name

    def __cmp__(self, other):
        if isinstance(other, Const):
            return 1
        elif isinstance(other, Var):
            return cmp(self.index, other.index)
        else:
            return -1
        
    def __eq__(self, other):
        if isinstance(other, UVar):
            return self.index == other.index
        return False

# internal variables -- just an index
class IVar(Term, Var):

    def __init__(self, index):
        Var.__init__(self, "a" + str(index))
        self.index = index

    def __str__(self):
        return self.name

    def __cmp__(self, other):
        if isinstance(other, Const):
            return 1
        elif isinstance(other, Var):
            return cmp(self.index, other.index)
        else:
            return -1
    
    def __eq__(self, other):
        # print "IVAR EQ CALLED"
        if isinstance(other, IVar):
            return self.index == other.index
        return False
    
    def __ne__(self, other):
        if isinstance(other, IVar):
            return self.index != other.index
        return True
    
    # Looks in Heuristic_data H to see if self < other is known.
    def lt_rel(self, other, H):
        i, j = self.index, other.index
        if i > j:
            return other.gt_rel(self, H)
        if i == j:
            return False
        
        if i == 0 and j in H.zero_comparisons.keys():
            if H.zero_comparisons[j].comp == GT:
                return True
            return False
        
        signi, signj = H.sign(i), H.sign(j)
        wsigni, wsignj = H.weak_sign(i), H.weak_sign(j)
        if wsignj != 0: 
            if signi == -1 and signj == 1:
                return True
            if signi == 1 and signj == -1:
                return False
            # both signs are the same.
            if (i, j) in H.term_comparisons.keys():
                comps = H.term_comparisons[i, j]
                for c in comps:
                    if ((wsignj == 1 and ((c.comp == LT and c.coeff <= 1)\
                                          or (c.comp == LE and c.coeff < 1))) or
                        (wsignj == -1 and ((c.comp == LT and (c.coeff < 0 or c.coeff >= 1))
                            or (c.comp == LE and (c.coeff < 0 or c.coeff > 1))))):
                        return True
            return False
        
        # sign info on right is unknown
        if (i, j) in H.term_comparisons.keys():
            comps = H.term_comparisons[i, j]
            if (any((c.comp == LT and c.coeff <= 1) or (c.comp == LE and c.coeff < 1)\
                    for c in comps) and \
                any(((c.comp == LT and (c.coeff < 0 or c.coeff >= 1))\
                     or (c.comp == LE and (c.coeff < 0 or c.coeff > 1)))\
                    for c in comps)):
                return True
        return False
    
    def gt_rel(self, other, H):
        i, j = self.index, other.index
        if i > j:
            return other.lt_rel(self, H)
        if i == j:
            return False
        
        if i == 0 and j in H.zero_comparisons.keys():
            if H.zero_comparisons[j].comp == LT:
                return True
            return False
        
        signi, signj = H.sign(i), H.sign(j)
        wsigni, wsignj = H.weak_sign(i), H.weak_sign(j)
        if wsignj != 0: 
            if signi == -1 and signj == 1:
                return False
            if signi == 1 and signj == -1:
                return True
            # both signs are the same.
            if (i, j) in H.term_comparisons.keys():
                comps = H.term_comparisons[i, j]
                for c in comps:
                    if ((wsignj == 1 and ((c.comp == GT and c.coeff >= 1)\
                                          or (c.comp == GE and c.coeff > 1))) or
                        (wsignj == -1 and ((c.comp == GT and c.coeff <= 1)\
                                           or (c.comp == GE and c.coeff < 1)))):
                        return True
            return False
        
        # sign info on right is unknown
        if (i, j) in H.term_comparisons.keys():
            comps = H.term_comparisons[i, j]
            if (any((c.comp == GT and c.coeff >= 1)\
                    or (c.comp == GE and c.coeff > 1) for c in comps) and
                any((c.comp == GT and c.coeff <= 1)\
                    or (c.comp == GE and c.coeff < 1) for c in comps)):
                return True
        return False
    
    def le_rel(self, other, H):
        i, j = self.index, other.index
        if i > j:
            return other.ge_rel(self, H)
        if i == j:
            return True
        
        if i == 0 and j in H.zero_comparisons.keys():
            if H.zero_comparisons[j].comp in [GT, GE]:
                return True
            return False
        
        # signi, signj = H.sign(i), H.sign(j)
        wsigni, wsignj = H.weak_sign(i), H.weak_sign(j)
        if wsignj != 0:
            if wsigni == -1 and wsignj == 1:
                return True
            if wsigni == 1 and wsignj == -1:
                return False
            # both signs are the same.
            if (i, j) in H.term_comparisons.keys():
                comps = H.term_comparisons[i, j]
                for c in comps:
                    if (c.comp in [LE, LT] and ((wsignj == 1 and c.coeff <= 1)  or
                        (wsignj == -1 and ((c.coeff < 0 or c.coeff >= 1))))):
                        return True
            return False
        
        # sign info on right is unknown
        if (i, j) in H.term_comparisons.keys():
            comps = H.term_comparisons[i, j]
            if (any((c.comp in [LT, LE] and c.coeff <= 1) for c in comps) and
                any((c.comp in [LT, LE] and (c.coeff < 0 or c.coeff >= 1)) for c in comps)):
                return True
        return False
    
    def ge_rel(self, other, H):
        i, j = self.index, other.index
        if i > j:
            return other.le_rel(self, H)
        if i == j:
            return True
        
        if i == 0 and j in H.zero_comparisons.keys():
            if H.zero_comparisons[j].comp in [LT, LE]:
                return True
            return False
        
        # signi, signj = H.sign(i), H.sign(j)
        wsigni, wsignj = H.weak_sign(i), H.weak_sign(j)
        if wsignj != 0:
            if wsigni == -1 and wsignj == 1:
                return False
            if wsigni == 1 and wsignj == -1:
                return True
            # both signs are the same.
            if (i, j) in H.term_comparisons.keys():
                comps = H.term_comparisons[i, j]
                for c in comps:
                    if c.comp in [GT, GE] and ((wsignj == 1 and c.coeff >= 1) or
                        (wsignj == -1 and  c.coeff <= 1)):
                        return True
            return False
        
        # sign info on right is unknown
        if (i, j) in H.term_comparisons.keys():
            comps = H.term_comparisons[i, j]
            if (any((c.comp in [GT, GE] and c.coeff >= 1)  for c in comps) and
                any((c.comp in [GT, GE] and c.coeff <= 1)  for c in comps)):
                return True
        return False
    
    def eq_rel(self, other, H):
        i, j = self.index, other.index
        if i == j:
            return True
        if self -other in H.zero_equations or other - self in H.zero_equations:
            return True
        return False
    
    def neq_rel(self, other, H):
        i, j = self.index, other.index
        if i > j:
            return other.neq_rel(self, H)
        if i == j:
            return False
        return self.gt_rel(other, H) or self.lt_rel(other, H)
            

# creates a name for every subterm in the list of terms args
# returns a list of all subterms (the ith name names the ith subterms)
#   and dictionaries with all the name definitions
def make_term_names(terms):

    name_defs = {}

    subterm_list = [one]
    name_defs[0] = one

    # makes this term and all subterms have names, defining new names
    # if necessary; and returns the name
    #
    # notes that subterm_list and name_defs are global to this procedure,
    # which augments them as it recurses through t
    def process_subterm(t):
        #print 'processing',t,'. structure:',t.structure()
        if t in subterm_list:
            return IVar(subterm_list.index(t))
        else:
            new_def = None
            if isinstance(t, Var):
                new_def = t
            elif isinstance(t, Add_term):
                addpairs = []
                for a in t.addpairs:
                    addpairs.append(Add_pair(a.coeff, process_subterm(a.term)))
                new_def = Add_term(addpairs)
            elif isinstance(t, Mul_term):
                mulpairs = []
                for m in t.mulpairs:
                    mulpairs.append(Mul_pair(process_subterm(m.term), m.exp))
                new_def = Mul_term(mulpairs)
            elif isinstance(t, Func_term):
                args = []
                for m in t.args:
                    args.append(Add_pair(m.coeff,process_subterm(m.term)))
                new_def = Func_term(t.name, args, t.const)
            l = len(subterm_list)  # index of new term
            subterm_list.append(t)
            name_defs[l] = new_def
            return IVar(l)

    for t in terms:
        process_subterm(t)

    return subterm_list, name_defs


def test_make_term_names():

    x = Var("x")
    y = Var("y")
    z = Var("z")
    t1 = Mul_term([(Add_term([(2, x), (-3, y), (1, z)]), 3), (x, 2)])
    t2 = Mul_term([(Add_term([(2, x), (-3, y), (1, z)]), 3), (x, 3)])
    t3 = Mul_term([(x, 2), (Add_term([(-3, y), (1, z), (2, x)]), 3)])
    t4 = Add_term([(2, t1), (3, t2), (1, x)])
    terms = [t1, t2, t3, t4]

    subterm_list, name_defs = make_term_names(terms)

    print
    print "Terms:", terms
    print
    print "Subterms:"
    for i in range(len(subterm_list)):
        print IVar(i), "=", subterm_list[i]
    print
    print "Definitions:"
    for i in range(len(subterm_list)):
        print IVar(i), "=", name_defs[i]
