import argparse
from copy import copy
from math import sqrt


class DegreeIsTooBigException(Exception):
    def __init__(self, message):
        self.message = message


class NotOddDegreeException(Exception):
    def __init__(self, message):
        self.message = message


class Polynomial:

    def __init__(self, *coefficients):
        if len(coefficients) == 1 and type(coefficients[0]) != int:
            coefficients = coefficients[0]
        else:
            coefficients = list(coefficients)
        if isinstance(coefficients,
                      list):  # construction of polynomial from list
            k = 0
            for i in range(len(coefficients) - 1, 0, -1):
                if coefficients[i] != 0:
                    break
                else:
                    k += 1
            if k != 0:
                self.coefficients = coefficients[:-k]
            else:
                self.coefficients = coefficients
        if isinstance(coefficients,
                      Polynomial):  # construction of polynomial from polynomial
            k = 0
            for i in range(len(coefficients.coefficients) - 1, 0, -1):
                if coefficients.coefficients[i] != 0:
                    break
                else:
                    k += 1
            if k != 0:
                self.coefficients = copy(coefficients.coefficients[:-k])
            else:
                self.coefficients = copy(coefficients.coefficients)
        if isinstance(coefficients,
                      dict):  # construction of polynomial from dict
            self.coefficients = [0 for _ in
                                 range(sorted(coefficients.keys())[-1] + 1)]
            for i in coefficients:
                if coefficients[i] != 0:
                    self.coefficients[i] = coefficients[i]

    def __repr__(self):  # polynomial representation
        string = "Polynomial {}"
        return string.format(self.coefficients)

    def __str__(self):   # cast to string
        string = ""
        for i in range(len(
                self.coefficients)):  # constructing the string with polynomial backwards
            if self.coefficients[i] != 0:
                if i > 1:  # case with given degree of a member above 1
                    string += str(i)[::-1] + "^x" + (
                        str(int(abs(self.coefficients[i])))[::-1]
                        if abs(self.coefficients[i]) != 1 or i == 0 else '') \
                              + (' -' if self.coefficients[
                                             i] < 0 else ' +') + ' '
                else:  # case with given degree of a member below or equal 1
                    string += ('x' if i == 1 else '') + \
                              (str(int(abs(self.coefficients[i])))[::-1]
                               if abs(
                                  self.coefficients[
                                      i]) != 1 or i == 0 else '') + (
                                  ' -' if self.coefficients[
                                              i] < 0 else ' +') + ' '

        if string != "":
            if string[:-1][-1] == '-':
                string = (string[:-3] + '-')[::-1]
            else:
                string = string[:-3][::-1]
        return string

    def __eq__(self, other):
        self = Polynomial(self)
        other = Polynomial(other)
        return self.coefficients == other.coefficients
        # comparing lists of coefficients of two polynomials

    def __add__(self, other):
        other = Polynomial(other)
        poly = Polynomial(self)
        # swaps polynomials if first is less then second
        if poly.degree() < other.degree():
            poly, other = other, poly
        # finds a sum of coefficients for two polynomials
        for i in range(len(other.coefficients)):
            poly.coefficients[i] += other.coefficients[i]
        return Polynomial(poly.coefficients)

    def __radd__(self, other):
        return self + other

    def __neg__(self):
        # inversion of signs of coefficients
        coefficients = [-i for i in self.coefficients]
        return Polynomial(coefficients)

    def __sub__(self, other):  # subtract implementation
        return self + -other

    def __rsub__(self, other):
        return -self + other

    def __call__(self, x):
        ans = 0
        # counting of the value of a given polynomial
        for i in range(len(self.coefficients)):
            ans += (x ** i) * self.coefficients[i]
        return ans

    def degree(self):
        # returns the maximum degree of a given polynomial
        if len(self.coefficients):
            return len(self.coefficients) - 1
        else:
            return 0

    def der(self, d=1):
        # recursive counting derivative of a given polynomial to a given degree
        if d == 0:
            return self
        coef_fin = [0 for _ in range(self.degree() + 1)]
        for i in range(len(self.coefficients) - 2, -1, -1):
            coef_fin[i] = self.coefficients[i + 1] * (i + 1)
        temp = Polynomial(coef_fin)
        return temp.der(d - 1)

    def __mul__(self, other):
        other = Polynomial(other)
        temp = [0 for _ in range(self.degree() + other.degree() + 1)]
        # multiply polynomial and other polynomial
        if isinstance(other, Polynomial):
            for i in range(self.degree() + 1):
                for l in range(other.degree() + 1):
                    temp[i + l] += self.coefficients[i] * other.coefficients[l]
        else:  # multiply polynomial and other number
            for i in self:
                i *= other
            temp = self

        return Polynomial(temp)

    def __rmul__(self, other):
        return self * other

    def __iter__(self):
        # basic iterator, iterates through non zero coefficients
        self.n = 0
        k = 0
        for i in self.coefficients:
            if i != 0:  # counting non-zero coefficients
                k += 1
        return iter(zip([i for i in range(k)],
                        [i for i in self.coefficients if i != 0]))

    def __next__(self):
        # gets next non zero coefficient in polynomial
        k = 0
        for i in self.coefficients:
            if i != 0:  # counting non-zero coefficients
                k += 1
        if self.n < k:
            while self.n < len(self.coefficients):
                if self.coefficients[self.n] != 0:
                    result = self.coefficients[self.n]
                    break
                else:
                    self.n += 1
            self.n += 1
            return result
        else:
            raise StopIteration

    def __mod__(self, other):
        return (self / other)[1]

    def gcd(self, other):
        # realisation of simple Euclidean algorithm
        poly = Polynomial(self)
        other = Polynomial(other)
        if poly.degree() < other.degree() or (
                poly.coefficients[-1] < other.coefficients[
            -1] and poly.degree() == other.degree()):
            poly, other = other, poly
        while other.degree() != 0:
            poly, other = other, poly % other
        return poly

    def __truediv__(self, other):
        # division for polynomials
        # only those where self > other are accepted!
        other = Polynomial(other)
        dother = other.degree()
        other = other.coefficients
        temp = self.coefficients
        dself = self.degree()
        n = max(dself, dother)
        temp += [0 for i in range(n - len(temp) - 1)]
        other += [0 for i in range(n - len(other) - 1)]
        if dother < 0: raise ZeroDivisionError
        if dself >= dother:
            q = [0] * dself
            while dself >= dother:
                d = [0] * (dself - dother) + other
                mult = q[dself - dother] = temp[-1] / float(d[-1])
                d = [coeff * mult for coeff in d]
                temp = [(coeffN - coeffd) for coeffN, coeffd in zip(temp, d)]
                dself = Polynomial(temp).degree()
            r = temp
        else:
            q = [0]
            r = temp
        return Polynomial(q), Polynomial(r)


class RealPolynomial(Polynomial):

    def __init__(self, *coefficients):
        super().__init__(*coefficients)
        if self.degree() % 2 == 0:
            raise NotOddDegreeException("not odd")

    def search(self, lo, hi, eps):
        # searching for root in given range with given eps
        while lo < hi:
            if abs(self(lo)) < eps:
                return lo
            if abs(self(hi)) < eps:
                return hi
            mid = (lo + hi) / 2
            if self(mid) * self(hi) <= 0:
                lo = mid
            else:
                hi = mid

    def find_root(self, eps=1e-6):
        # returns root with given eps
        a = 1
        while self(a) * self(-a) > 0:
            a *= 2
        ans = self.search(-a, a, eps)
        if ans is None:
            return self.find_root(eps)
        else:
            return ans


class QuadraticPolynomial(Polynomial):
    def __init__(self, *coefficients):
        super().__init__(*coefficients)
        if self.degree() > 2:
            raise DegreeIsTooBigException("too big")

    def solve(self):
        # solves quadratic polynomial
        ans = []
        temp = self.coefficients
        if len(temp) < 2:  # one element case
            if len(temp) == 1:
                try:
                    if self.coefficients[1] != 0:
                        ans.append(0)
                except:
                    pass
            return ans
        elif len(temp) == 2:  # two elements case
            if self.degree() == 1:
                ans.append(-temp[0] / temp[1])
            else:
                try:
                    ans.append(sqrt(-temp[0]))
                except:
                    pass
            return ans
        else:  # three elements case
            d = (temp[1] ** 2) - (4 * temp[2] * temp[0])
            if d < 0:  # case when discriminant is less than zero
                pass
            elif d == 0:  # case when discriminant equals zero
                ans.append(-temp[1] / (2 * temp[2]))
            else:  # case when discriminant is greater than zero
                ans.append((-temp[1] - sqrt(d)) / (2 * temp[2]))
                ans.append((-temp[1] + sqrt(d)) / (2 * temp[2]))
            return ans


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Polynomial')
    parser.add_argument('command',
                        choices=['multiply', 'derivative', 'solve-quadratic',
                                 'find-root'])
    parser.add_argument('coefficients', nargs='*', type=int)
    parser.add_argument('--lhs', nargs='+', type=int, help='lhs')
    parser.add_argument('--rhs', nargs='+', type=int, help='rhs')
    parser.add_argument('--degree', type=int, help='degree')
    parser.add_argument('--eps', type=float, help='eps')
    args = parser.parse_args()

    if args.command == 'multiply':
        lhs = Polynomial(args.lhs)
        rhs = Polynomial(args.rhs)
        print(lhs * rhs)
    elif args.command == 'derivative':
        poly = Polynomial(args.coefficients)
        print(poly.der(args.degree))
    elif args.command == 'solve-quadratic':
        poly = QuadraticPolynomial(args.coefficients)
        print(poly.solve())
    elif args.command == 'find-root':
        poly = RealPolynomial(args.coefficients)
        print(poly.find_root(args.eps))
