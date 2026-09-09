#!/usr/bin/env python3
"""Exact certificates for the six-dimensional singular Gram construction.

This checker verifies the finite algebraic identities and rank certificates.
The accompanying manuscript proves continuity, the implicit-function argument,
the finite-family quantifiers, and exclusion of arbitrary polynomial leaves.
"""

if not __debug__:
    raise RuntimeError("Run this checker without -O or PYTHONOPTIMIZE; assertions are required.")

import hashlib
from pathlib import Path

import sympy as s


checks = 0


def zero(value, name):
    global checks
    entries = list(value) if isinstance(value, s.MatrixBase) else [value]
    assert all(s.cancel(s.expand(entry)) == 0 for entry in entries), name
    checks += 1


def equal(actual, expected, name):
    zero(actual - expected, name)


def check(condition, name):
    global checks
    assert condition, name
    checks += 1


x, y, z, u, v, r = variables = s.symbols("x y z u v r")
t, rho, delta, eps = s.symbols("t rho delta eps", real=True)
w = s.Matrix(variables)
beta = s.diag(1, 1, 3, -1, -1)
J = s.Matrix([[0, -1], [1, 0]])
K = s.diag(J, s.zeros(1), J / 2)
null_vector = s.Matrix([s.Rational(1, 2), 0, s.Rational(1, 2), 1, 0])
L = s.Matrix([
    [0, 0, 0, 0, -1],
    [0, 0, 1, 1, 0],
    [0, 0, 0, 0, 0],
    [0, 0, 0, 0, -s.Rational(1, 2)],
    [0, 0, 2, s.Rational(1, 2), 0],
])


def columns(point):
    first = point[:5, 0]
    middle = L * first + null_vector * point[5]
    return s.Matrix.hstack(first, middle, K * first)


def gram(point):
    C = columns(point)
    return (C.T * beta * C).applyfunc(s.factor)


C = columns(w)
Q = gram(w)
D = s.factor(C[:3, :].det())
qvec = s.Matrix([Q[0, 0], Q[0, 1], Q[2, 2]])
gram4 = s.Matrix([Q[0, 0], Q[0, 1], Q[1, 2], Q[2, 2]])
monomials = [variables[i] * variables[j]
             for i in range(6) for j in range(i, 6)]

zero(K.T * beta + beta * K, "K is beta-skew")
zero(null_vector.T * beta * null_vector, "u is null")
zero(null_vector.T * beta * L, "L has image perpendicular to u")
zero(L.T * beta * L + beta + beta * K * K, "signed Gram identity")
zero(Q[0, 2], "second Gram relation")
zero(Q[0, 0] + Q[1, 1] - Q[2, 2], "first Gram relation")
check(C.reshape(15, 1).jacobian(variables).rank() == 6,
      "the whole six-dimensional space is embedded injectively")

a, bq, d, e = s.symbols("a b d e")
R = s.Matrix([[a, bq, 0], [bq, d - a, e], [0, e, d]])
one = s.ones(3, 1)
simplex_a = [4 * s.eye(3)[:, i] - one for i in range(3)] + [-one]
simplex_u = [(s.eye(3)[:, i] + one) / 4 for i in range(3)] + [s.zeros(3, 1)]
edges = [(i, j) for i in range(4) for j in range(i + 1, 4)]
labels = {ij: s.expand(-(simplex_a[ij[0]].T * R * simplex_a[ij[1]])[0])
          for ij in edges}
reconstructed = s.zeros(3)
for (i, j), label in labels.items():
    difference = simplex_u[i] - simplex_u[j]
    reconstructed += label * difference * difference.T
zero(reconstructed - R, "simplex reconstruction")
zero(labels[0, 2] - 2 * labels[0, 1] - 6 * labels[0, 3]
     - 5 * labels[1, 3], "redundant label 02")
zero(labels[2, 3] - labels[0, 1] - 2 * labels[0, 3]
     - 2 * labels[1, 3], "redundant label 23")
selected_edges = [(0, 1), (0, 3), (1, 2), (1, 3)]
selected_labels = s.Matrix([labels[ij] for ij in selected_edges])
check(selected_labels.jacobian([a, bq, d, e]).det() != 0,
      "the four selected Gram labels are independent")

Rminus = s.Matrix([0, 1, -1]) * s.Matrix([0, 1, -1]).T
R0 = s.Matrix([[1, s.Rational(1, 4), 0],
               [s.Rational(1, 4), 1, 0], [0, 0, 2]])
check(all(R0[:i, :i].det() > 0 for i in range(1, 4)), "R0 is positive definite")
subs_minus = {a: 0, bq: 0, d: 1, e: -1}
subs_R0 = {a: 1, bq: s.Rational(1, 4), d: 2, e: 0}
equal(selected_labels.subs(subs_minus), s.Matrix([0, 0, 16, 0]), "rank-one target labels")
equal(selected_labels.subs(subs_R0), s.Matrix([
    s.Rational(3, 2), s.Rational(1, 2), s.Rational(17, 2), s.Rational(1, 2)
]), "positive target labels")
positive_point = s.Matrix([2, 8, 0, -1, -7, -9])
positive_gram = gram(positive_point)
positive_minors = [positive_gram[:i, :i].det() for i in range(1, 4)]
check(all(number > 0 for number in positive_minors), "a positive Gram value exists")

curve = s.Matrix([
    t**4 - 6*t**2 + 1,
    4*t**3 - 4*t,
    t**4 + 2*t**2 + 1,
    2*t**4 - 2,
    4*t**3 + 4*t,
    2*t**5 + 4*t**3 + 2*t,
])
first = curve.diff(t)
second = curve.diff(t, 2)
third = curve.diff(t, 3)
k = s.Matrix([-t, 1, 1])
dcurve = 12 * (1 + t*t)**2
zero(gram(curve), "the polynomial curve is Gram-zero")
zero(columns(curve) * k, "the column relation on the curve")
equal(gram(first), dcurve * Rminus, "the derivative has the rank-one Gram value")
equal(first[:5, 0], (4*t*curve[:5, 0] - 4*K*curve[:5, 0]) / (1+t*t),
      "the first derivative stays in span(v,Kv)")
equal(columns(second) * k, 2 * first[:5, 0], "second differentiated column relation")

linear_matrix = s.Matrix([[s.expand(curve[i]).coeff(t, degree)
                          for i in range(6)] for degree in range(6)])
equal(linear_matrix.det(), s.Integer(2048), "the six curve coordinates are independent")
curve_products = [curve[i] * curve[j] for i in range(6) for j in range(i, 6)]
first_products = [first[i] * first[j] for i in range(6) for j in range(i, 6)]
M = s.Matrix([[s.expand(poly).coeff(t, degree) for poly in curve_products]
              for degree in range(11)])
Mfirst = s.Matrix([[s.expand(poly).coeff(t, degree) for poly in first_products]
                   for degree in range(9)])
N = M.col_join(Mfirst)
quad_columns = list(M.rref()[1])
quad_minor = M[:, quad_columns].det()
joint_columns = list(N.rref()[1])
joint_rows = list(N[:, joint_columns].T.rref()[1])
joint_minor = N.extract(joint_rows, joint_columns).det()
check(len(quad_columns) == 11 and quad_minor != 0, "quadratic curve rank 11")
check(len(joint_columns) == 18 and joint_minor != 0, "combined quadratic rank 18")
equal(quad_minor, s.Integer(2)**35, "the stated quadratic minor value")
equal(joint_minor, s.Integer(2)**69, "the stated combined minor value")

Hforms = s.Matrix([Q[0, 0], Q[0, 1], Q[1, 2] + Q[2, 2]])
Hcoefficients = s.Matrix([[s.Poly(poly, *variables).coeff_monomial(monomial)
                          for monomial in monomials] for poly in Hforms])
check(Hcoefficients.rank() == 3, "three independent Gram forms annihilate both curves")
equal(Hcoefficients[:, [0, 2, 4]].det(), s.Integer(1), "the stated three-form independence minor")
zero(N * Hcoefficients.T, "the three Gram forms are in the combined kernel")
Gcoefficients = s.Matrix([[s.Poly(poly, *variables).coeff_monomial(monomial)
                          for monomial in monomials] for poly in gram4])
check(Gcoefficients.rank() == 4, "the Gram span has dimension four")

base = rho * curve
base_substitution = dict(zip(variables, base))
j0 = third - 6*t/(1+t*t) * second
n = -second / (2*rho*dcurve)
Jgram = gram4.jacobian(variables).subs(base_substitution)
Jpi = qvec.jacobian(variables).subs(base_substitution)
JD = s.Matrix([D]).jacobian(variables).subs(base_substitution)
equal(Jgram * n, s.Matrix([0, 0, -1, 1]), "n gives the rank-one first variation")
zero(Jgram * j0, "j0 lies in the derivative kernel")
zero(JD * n, "n has zero first determinant variation")
equal((JD * j0)[0], -48*rho*rho*(1+t*t)**4, "j0 has nonzero determinant variation")
jimage = columns(j0) * k
nimage = columns(n) * k
equal((jimage.T * beta * jimage)[0], s.Integer(1728), "positive normal norm")
zero((nimage.T * beta * nimage)[0], "the first rank-one variation has null residual")
zero((nimage.T * beta * jimage)[0], "orthogonality of the two residuals")
zero(curve[:5, 0].T * beta * jimage, "normal residual is perpendicular to v")
zero((K*curve[:5, 0]).T * beta * jimage, "normal residual is perpendicular to Kv")
J3 = Jpi[:, :3]
J3det = s.factor(J3.det())
equal(J3det, 12*rho**3*(1+t*t)**6, "the three Gram derivatives are independent at every base")
ell = lambda T: (k.T * T * k)[0]
sigma = s.factor(ell(R0))
equal(sigma, t*t-t/s.Integer(2)+3, "strictly positive normal target value")
equal(sigma, (t-s.Rational(1, 4))**2 + s.Rational(47, 16), "positive square decomposition")
zero(ell(Rminus), "the first target vanishes on the moving relation")
zero(s.Matrix([ell(Q)]).jacobian(variables).subs(base_substitution), "the missing Gram derivative is zero")

# Keep j0 unnormalized for the exact symbolic IFT check.  The variable eta
# represents its scalar coefficient; normalization is eta^2=sigma/1728.
eta = s.symbols("eta", real=True)
j = -eta * j0
normal_relations = {eta**2: sigma/s.Integer(1728)}
for sign in [1, -1]:
    direction = n + sign*delta*j
    residual_norm = s.factor(ell(gram(direction)))
    zero(s.expand(residual_norm - delta*delta*sigma).subs(normal_relations),
         f"rescaled fourth equation at zero, sign {sign}")
    fourth_derivative = 2 * ((columns(direction)*k).T * beta * (columns(j)*k))[0]
    zero(s.expand(fourth_derivative - sign*2*delta*sigma).subs(normal_relations),
         f"nonzero fourth IFT derivative, sign {sign}")
    # The first three rows vanish on j; hence the full four-by-four
    # determinant is det(J3) times the displayed fourth derivative.
    zero(Jpi*j, f"triangular IFT Jacobian, sign {sign}")

# Independently check the expansion used to recover the exact common Gram.
z0, z1, z2, z3, z4, z5 = zvariables = s.symbols("z0:6")
increment = s.Matrix(zvariables)
zero(gram(base+eps*increment) - eps*(
    C.subs(base_substitution).T*beta*columns(increment)
    + columns(increment).T*beta*C.subs(base_substitution))
    - eps*eps*gram(increment), "exact second-order Gram expansion")

print("SymPy", s.__version__)
print("Selected four-label matrix determinant:", selected_labels.jacobian([a,bq,d,e]).det())
print("Positive point Gram:", positive_gram.tolist())
print("Positive point leading principal minors:", positive_minors)
print("Linear coefficient determinant:", linear_matrix.det())
print("Quadratic minor columns (zero-based):", quad_columns)
print("Quadratic minor determinant:", quad_minor)
print("Combined minor rows (zero-based):", joint_rows)
print("Combined minor columns (zero-based):", joint_columns)
print("Combined minor determinant:", joint_minor)
print("Gram derivative 3x3 determinant:", J3det)
print("Normal squared norm:", s.factor((jimage.T*beta*jimage)[0]))
print("Determinant derivative on j0:", s.factor((JD*j0)[0]))
print("Exact assertions passed:", checks)
print("Checker SHA-256:", hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
