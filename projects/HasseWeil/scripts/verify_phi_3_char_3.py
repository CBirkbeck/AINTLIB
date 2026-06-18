"""
Verify whether Φ_3 ∈ F_3[X^3] for elliptic curves in characteristic 3.

Mathlib's Φ definition (from DivisionPolynomial/Basic.lean):
  Φ(n) = X · ΨSq(n) - preΨ(n+1) · preΨ(n-1) · (if Even n then 1 else Ψ₂Sq)

For n = 3 (odd): Φ(3) = X · ΨSq(3) - preΨ(4) · preΨ(2) · Ψ₂Sq
                       = X · Ψ_3² - preΨ_4 · 1 · Ψ_2²
                       = X · Ψ_3² - preΨ_4 · Ψ_2²

where:
  Ψ_2² = 4X³ + b₂X² + 2b₄X + b₆
  Ψ_3 = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈
  preΨ_4 = 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²)

In char 3: 3 = 0, 5 = 2, 10 = 1, 2 = 2.

We compute Φ_3 in char 3 with a SPECIFIC curve y² = x³ + x + 1 over F_3.
Short Weierstrass: a₁ = a₂ = a₃ = 0, a₄ = 1, a₆ = 1.
So b₂ = a₁² + 4a₂ = 0
   b₄ = 2a₄ + a₁a₃ = 2
   b₆ = a₃² + 4a₆ = 4 = 1 (in F_3)
   b₈ = a₁²a₆ + 4a₂a₆ - a₁a₃a₄ + a₂a₃² - a₄² = -1 = 2 (in F_3)

Compute Φ_3 modulo 3 using sympy.
"""

import sympy as sp
from sympy import GF

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

# Generic formulas (over Z, will reduce mod 3 below)
Psi_2_sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi_3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
preP4 = (2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
         + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

# Φ_3 = X · Ψ_3² - preΨ_4 · Ψ_2² (n=3 odd)
Phi_3 = X * Psi_3**2 - preP4 * Psi_2_sq
Phi_3_expanded = sp.expand(Phi_3)

print("=" * 70)
print("Φ_3 in generic Z[b2, b4, b6, b8, X]:")
print("=" * 70)
poly_X = sp.Poly(Phi_3_expanded, X)
for i, c in enumerate(poly_X.all_coeffs()[::-1]):
    if c != 0:
        print(f"  X^{i}: {c}")

print()
print("=" * 70)
print("Φ_3 mod 3 (substituting b2, b4, b6, b8 then reducing):")
print("=" * 70)

# For y² = x³ + x + 1 over F_3:
# a1 = a2 = a3 = 0, a4 = 1, a6 = 1
# b2 = 0, b4 = 2, b6 = 4 = 1, b8 = -1 = 2 (all mod 3)
b_vals = {b2: 0, b4: 2, b6: 1, b8: 2}

Phi_3_specific = Phi_3_expanded.subs(b_vals)
Phi_3_mod3 = sp.expand(Phi_3_specific) % 3  # may need manual reduction

# Reduce coefficients mod 3
poly_X_specific = sp.Poly(Phi_3_specific, X)
print(f"Φ_3 for y² = x³ + x + 1 over F_3 (coefficients before mod):")
for i, c in enumerate(poly_X_specific.all_coeffs()[::-1]):
    if c != 0:
        print(f"  X^{i}: {c}")

print()
print("Coefficients reduced mod 3:")
mod3_coeffs = []
for i, c in enumerate(poly_X_specific.all_coeffs()[::-1]):
    c_mod = int(c) % 3
    if c_mod != 0:
        mod3_coeffs.append((i, c_mod))
        print(f"  X^{i}: {c_mod}")

print()
print("=" * 70)
print("Question: are all nonzero monomials at exponents divisible by 3?")
print("=" * 70)
all_div_by_3 = all(i % 3 == 0 for i, _ in mod3_coeffs)
print(f"  all_div_by_3: {all_div_by_3}")
if all_div_by_3:
    print("  ✓ Φ_3 IS in F_3[X^3]: cube root extraction is straightforward.")
else:
    bad_exps = [i for i, _ in mod3_coeffs if i % 3 != 0]
    print(f"  ✗ Φ_3 has nonzero coeffs at non-3-divisible exponents: {bad_exps}")

print()
print("=" * 70)
print("Also computing Φ_3 / ΨSq_3 = (X^4 + ... ) / Ψ_3² in F_3(X)")
print("Numerator and denominator individually:")
print("=" * 70)
PsiSq_3_specific = sp.expand(Psi_3.subs(b_vals)**2)
print("ΨSq_3 = Ψ_3²:")
poly_PsiSq3 = sp.Poly(PsiSq_3_specific, X)
for i, c in enumerate(poly_PsiSq3.all_coeffs()[::-1]):
    c_mod = int(c) % 3
    if c_mod != 0:
        print(f"  X^{i}: {c_mod}")

print("\nIs ΨSq_3 mod 3 in F_3[X^3]?")
psisq_bad = []
for i, c in enumerate(poly_PsiSq3.all_coeffs()[::-1]):
    c_mod = int(c) % 3
    if c_mod != 0 and i % 3 != 0:
        psisq_bad.append(i)
print(f"  Non-3-divisible nonzero exponents in ΨSq_3: {psisq_bad}")
