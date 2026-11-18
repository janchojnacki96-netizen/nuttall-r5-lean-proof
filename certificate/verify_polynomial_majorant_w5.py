#!/usr/bin/env python3
"""Exact rational-polynomial majorant verifier for all 25 B_ij, i,j<=4.

Proves 50 nonnegative coefficient expansions:
  5(1+d)^8(1+q)^4 +/- B_ij(d,q)
for d,q >= 0. No floating point, no CAS, no external packages.
This is a human-auditable finite algebraic test, not a Lean proof.
"""
from fractions import Fraction
from math import comb, factorial

base = {
    (a, b): Fraction(5 * comb(8, a) * comb(4, b))
    for a in range(9) for b in range(5)
}
verified = 0
for i in range(5):
    for j in range(5):
        bpoly = {}
        for k in range(min(i, j) + 1):
            monomial = (i + j - 2*k, k)
            coeff = Fraction((-1)**(i+j-k), factorial(k)*factorial(i-k)*factorial(j-k))
            bpoly[monomial] = bpoly.get(monomial, Fraction(0)) + coeff
        for sign in (-1, 1):
            poly = {
                key: value + sign*bpoly.get(key, Fraction(0))
                for key, value in base.items()
            }
            assert all(value >= 0 for value in poly.values()), (i, j, sign)
            verified += 1

assert verified == 50
print("PASS: 50 exact nonnegative-polynomial certificates")
