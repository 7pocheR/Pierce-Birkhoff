"""Finite exact certificate for a seven-dimensional nonsymmetric Gram graph.

No random generation, numerical rank tolerance, file writes, or assertions
disabled by Python optimization are used. Fraction arithmetic checks the
graph identity; bounded integer arithmetic computes rational-jet reductions.
"""

from fractions import Fraction
from itertools import combinations_with_replacement

import numpy as np


PRIME = 1009
ORDER = 22
POSITIVE = [0, 3, 6, 1, 4, 7, 11, 14]
NEGATIVE = [2, 5, 8, 9, 12, 10, 13]
BASE = np.array([0, 0, 0, 0, 0, 1, 0, 0, -1], dtype=np.int64)
UNKNOWN = [0, 1, 2, 3, 4, 6, 7]
PAIRS3 = list(combinations_with_replacement(range(3), 2))
PAIRS7 = list(combinations_with_replacement(range(7), 2))
L = np.array([
    [3, 0, 1, 0, 0, 1, 0, 0, 1, -2, 0, 0, -1, 1, 0],
    [0, 0, -326, 630, 0, 490, 0, 0, -59, -80, -3, 0, 185, -80, 0],
    [0, 0, 46, 0, 0, 35, 105, 0, -11, 45, 38, 0, 25, 45, 0],
    [0, 90, -38, 0, 0, 10, 0, 0, 13, 40, -9, 0, -55, 40, 0],
    [0, 0, 1, 0, 3, 1, 0, 0, 1, 1, 0, 0, -1, -2, 0],
    [0, 0, 23, 0, 0, 14, 0, 63, -37, 5, -30, 0, -5, 5, 0],
    [0, 0, -4, 0, 0, 0, 0, 0, -31, -10, -17, 70, -25, -10, 0],
    [0, 0, 4, 0, 0, 0, 0, 0, 31, 10, -53, 0, 25, 10, 70]], dtype=np.int64)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def rank_minor(matrix):
    a = np.asarray(matrix, dtype=np.int64).copy() % PRIME
    original = a.copy()
    row_ids = list(range(a.shape[0]))
    columns = []
    rank = 0
    for j in range(a.shape[1]):
        choices = np.flatnonzero(a[rank:, j])
        if not len(choices):
            continue
        i = rank+int(choices[0])
        a[[rank, i]] = a[[i, rank]]
        row_ids[rank], row_ids[i] = row_ids[i], row_ids[rank]
        a[rank] = a[rank]*pow(int(a[rank, j]), -1, PRIME) % PRIME
        a[rank+1:] = (a[rank+1:]-a[rank+1:, j, None]*a[rank]) % PRIME
        columns.append(j)
        rank += 1
        if rank == a.shape[0]:
            break
    rows = sorted(row_ids[:rank])
    minor = original[np.ix_(rows, columns)].copy()
    determinant = 1
    for j in range(rank):
        i = j+int(np.flatnonzero(minor[j:, j])[0])
        if i != j:
            minor[[i, j]] = minor[[j, i]]
            determinant = -determinant
        pivot = int(minor[j, j])
        determinant = determinant*pivot % PRIME
        minor[j] = minor[j]*pow(pivot, -1, PRIME) % PRIME
        minor[j+1:] = (minor[j+1:]-minor[j+1:, j, None]*minor[j]) % PRIME
    return rank, rows, columns, determinant % PRIME


def inverse(matrix):
    n = len(matrix)
    a = np.column_stack((matrix, np.eye(n, dtype=np.int64))) % PRIME
    for j in range(n):
        choices = np.flatnonzero(a[j:, j])
        require(len(choices), 'singular modular inverse')
        i = j+int(choices[0])
        a[[i, j]] = a[[j, i]]
        a[j] = a[j]*pow(int(a[j, j]), -1, PRIME) % PRIME
        for i in range(n):
            if i != j:
                a[i] = (a[i]-a[i, j]*a[j]) % PRIME
    return a[:, n:]


def integer_determinant(matrix):
    a = [[int(x) for x in row] for row in matrix]
    sign, previous = 1, 1
    for k in range(len(a)-1):
        i = next((i for i in range(k, len(a)) if a[i][k]), None)
        if i is None:
            return 0
        if i != k:
            a[k], a[i] = a[i], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                numerator = a[i][j]*pivot-a[i][k]*a[k][j]
                require(numerator % previous == 0, 'exact Bareiss division')
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def chart(parameters):
    count = parameters.shape[1]
    zero = np.zeros(count, dtype=np.int64)
    one = zero.copy()
    one[0] = 1
    mul = lambda a, b: np.convolve(a, b)[:count] % PRIME
    k = parameters[:3]
    norm = sum((mul(v, v) for v in k), zero.copy()) % PRIME
    denominator = (one+norm) % PRIME
    cross = [[zero, -k[2], k[1]], [k[2], zero, -k[0]], [-k[1], k[0], zero]]
    nr = [[((one-norm)*int(i == j)+2*mul(k[i], k[j])+2*cross[i][j]) % PRIME
           for j in range(3)] for i in range(3)]
    c = [[parameters[5], parameters[6]], [parameters[7], parameters[8]]]
    cv = [[c[i][0], c[i][1],
           (mul(c[i][0], parameters[3])+mul(c[i][1], parameters[4])) % PRIME]
          for i in range(2)]
    a = [[sum((mul(nr[i][r], cv[r][j]) for r in range(2)), zero.copy()) % PRIME
          for j in range(3)] for i in range(3)]
    b = [[mul(denominator, cv[i][j]) for j in range(3)] for i in range(2)]
    return np.array([a[i][j] for i in range(3) for j in range(3)]+
                    [b[i][j] for i in range(2) for j in range(3)])


def gram_coefficients(basis):
    a, b = basis[:9].reshape(3, 3, 7), basis[9:].reshape(2, 3, 7)
    result = []
    for i, j in PAIRS3:
        matrix = sum((np.outer(a[r, i], a[r, j]) for r in range(3)), np.zeros((7, 7), dtype=np.int64))
        matrix -= sum((np.outer(b[r, i], b[r, j]) for r in range(2)), np.zeros((7, 7), dtype=np.int64))
        result.append([matrix[i, j] if i == j else matrix[i, j]+matrix[j, i] for i, j in PAIRS7])
    return np.array(result) % PRIME


def main():
    require(ORDER == 22 and PRIME == 1009, 'fixed arithmetic bounds')
    graph = [[Fraction(-int(L[i, j]), int(L[i, POSITIVE[i]])) for j in NEGATIVE] for i in range(8)]
    for i in range(8):
        for j in range(8):
            require(L[i, POSITIVE[j]] == (L[i, POSITIVE[i]] if i == j else 0), 'graph pivot coordinates')
    for i in range(7):
        for j in range(7):
            require(sum(graph[k][i]*graph[k][j] for k in range(8)) == int(i == j), 'rational isometric graph')
    require(all((630*x).denominator == 1 for row in graph for x in row), 'integer basis scaling')
    basis = np.zeros((15, 7), dtype=np.int64)
    basis[NEGATIVE] = np.eye(7, dtype=np.int64)
    for i in range(8):
        for j in range(7):
            value = graph[i][j]
            basis[POSITIVE[i], j] = value.numerator % PRIME * pow(value.denominator % PRIME, -1, PRIME) % PRIME
    tangent = []
    for j in range(9):
        series = np.zeros((9, 2), dtype=np.int64)
        series[:, 0], series[j, 1] = BASE, 1
        column = chart(series)[:, 1]
        tangent.append(np.where(column > PRIME//2, column-PRIME, column))
    tangent = np.array(tangent).T
    exact_jacobian = L[1:] @ tangent[:, UNKNOWN]
    determinant = integer_determinant(exact_jacobian)
    require(determinant == 16383079440000 and determinant % PRIME != 0, 'exact implicit Jacobian determinant')
    active = L[1:] % PRIME
    jacobian_inverse = inverse(exact_jacobian % PRIME)
    series = np.zeros((9, ORDER+1), dtype=np.int64)
    series[:, 0], series[8, 1] = BASE, 1
    for degree in range(1, ORDER+1):
        ambient = chart(series[:, :degree+1])
        series[UNKNOWN, degree] = -jacobian_inverse @ (active @ ambient[:, degree] % PRIME) % PRIME
    ambient = chart(series)
    require(not np.any(L @ ambient % PRIME), 'all eight constraints through the certified order')
    coordinates = ambient[NEGATIVE]
    require(not np.any((basis @ coordinates-ambient) % PRIME), 'graph coordinate reconstruction')
    linear = rank_minor(coordinates.T)
    quadratic_matrix = np.array([np.convolve(coordinates[i], coordinates[j])[:ORDER+1] % PRIME
                                 for i, j in PAIRS7]).T
    quadratic = rank_minor(quadratic_matrix)
    grams = gram_coefficients(basis)
    gram_rank = rank_minor(grams)
    require(not np.any((grams[0]+grams[3]-grams[5]) % PRIME), 'traceless Gram relation')
    require(not np.any(quadratic_matrix @ grams.T % PRIME), 'Gram annihilation')
    require((linear[0], quadratic[0], gram_rank[0]) == (7, 23, 5), 'three certified ranks')
    require((linear[3], quadratic[3], gram_rank[3]) == (693, 349, 256), 'three nonzero minors')
    target = [[Fraction(1), Fraction(1, 4), Fraction(0)],
              [Fraction(1, 4), Fraction(1), Fraction(0)],
              [Fraction(0), Fraction(0), Fraction(2)]]
    simplex = [[4*int(i == j)-1 for j in range(3)] for i in range(3)]+[[-1, -1, -1]]
    labels = [-sum(simplex[i][a]*target[a][b]*simplex[j][b] for a in range(3) for b in range(3))
              for i in range(4) for j in range(i+1, 4)]
    require(labels == [Fraction(3, 2), Fraction(17, 2), Fraction(1, 2),
                       Fraction(17, 2), Fraction(1, 2), Fraction(7, 2)], 'positive common target labels')
    require(target[0][0]+target[1][1]-target[2][2] == 0, 'target preserves omitted graph constraint')
    print('exact graph identity T^T T = I7 and integer scaling 630: passed')
    print('exact implicit Jacobian determinant:', determinant)
    print('linear:', linear)
    print('quadratic:', quadratic)
    print('Gram:', gram_rank)
    print('common target labels:', [str(x) for x in labels])
    print('all finite certificate checks passed')


if __name__ == '__main__':
    main()
