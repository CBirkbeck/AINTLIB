#!/usr/bin/env python3
"""
Sympy verification: in char 2, A·ψ₂ + B·cubic_x ∈ K[X²] = expand-range.

A = (X² + a₁²X + a₁a₃ + a₄)·Ψ₃ + (a₁X + a₃)⁴
B = a₁·Ψ₃ + (a₁X + a₃)³
ψ₂ = a₁X + a₃   (in char 2)
cubic_x = X³ + a₂X² + a₄X + a₆

Per-coefficient verification: every coefficient of LHS - witness_expand
is divisible by 2, hence vanishes in char 2.

The witness polynomial (defined in HasseWeil/Verschiebung/QthRoots.lean as
omega2_coupled_witness_char_two) has the per-coefficient form derived here.

Output: M(X) = (LHS - RHS) / 2, the multiplier needed by `linear_combination`.
"""

from sympy import symbols, expand, Poly, simplify

X, a1, a2, a3, a4, a6 = symbols('X a1 a2 a3 a4 a6')

# Char 2 specialisations
b2 = a1**2
b4 = a1*a3
b6 = a3**2
b8 = a1**2 * a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2  # raw unfolded

Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8

psi2 = a1*X + a3
cubic_x = X**3 + a2*X**2 + a4*X + a6

A = (X**2 + a1**2 * X + a1*a3 + a4) * Psi3 + (a1*X + a3)**4
B = a1*Psi3 + (a1*X + a3)**3

LHS = expand(A*psi2 + B*cubic_x)

# Witness coefficients (per omega2_coupled_witness_char_two):
c3 = a1*a2 + a3
c2 = a1**3 * a4 + a1*a3**2 + a1*a6 + a3*a4
c1 = a1**5 * a6 + a1**4 * a3 * a4 + a1**3 * a2 * a3**2 + a1**3 * a2 * a6 + \
     a1**3 * a4**2 + a1**2 * a2 * a3 * a4 + a1**2 * a3**3 + a1**2 * a3 * a6 + \
     a1 * a2**2 * a3**2 + a1 * a2 * a4**2 + a1 * a3**2 * a4 + a3 * a4**2
c0 = a1**3 * a3**2 * a6 + a1**3 * a6**2 + a1**2 * a3**3 * a4 + a1 * a2 * a3**4 + \
     a1 * a2 * a3**2 * a6 + a1 * a4**2 * a6 + a2 * a3**3 * a4 + a3**5 + \
     a3**3 * a6 + a3 * a4**3

RHS = expand(c3*X**6 + c2*X**4 + c1*X**2 + c0)

print("=== Coefficient-by-coefficient: LHS_n - RHS_n divisible by 2 ===")
poly_LHS = Poly(LHS, X)
poly_RHS = Poly(RHS, X)

max_deg = max(poly_LHS.degree(), poly_RHS.degree())
for n in range(max_deg + 1):
    cL = poly_LHS.nth(n)
    cR = poly_RHS.nth(n)
    diff = expand(cL - cR)
    if diff == 0:
        print(f"  X^{n}: identically 0")
        continue
    diff_poly = Poly(diff, a1, a2, a3, a4, a6)
    all_even = all(int(c) % 2 == 0 for c in diff_poly.coeffs())
    half = expand(diff / 2)
    print(f"  X^{n}: divisible by 2: {all_even}, M_{n} = {half}")

print("\n=== M(X) for linear_combination M * h_2P ===")
diff_total = expand(LHS - RHS)
M = expand(diff_total / 2)
print(f"M(X) =")
M_poly = Poly(M, X)
for n in range(M_poly.degree() + 1):
    c = M_poly.nth(n)
    if c != 0:
        print(f"  X^{n}: {c}")
