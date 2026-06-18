#!/usr/bin/env python3
"""
ω_3 X/Y coefficient extraction in char 3 (Route 2).

Goal: Extract the explicit polynomial forms of the {1, Y} basis
coefficients of `W.ω 3` modulo Weierstrass in char 3, analogous to
`omega2_X_coeff_char_two` and `omega2_Y_coeff_char_two` (Sessions 8/18).

## Strategy

mathlib's `W.ω n` formula:
    `ω n = redInvarDenom_n · INNER - complEDSAux₂_n + negPolynomial · ψ_n^3`

where:
* `INNER = (a₁·polyY - polyX) · C·Ψ₃ + 4·polynomial · (2·polynomial + C·Ψ₂Sq)`
* `polyY = 2Y + a₁X + a₃`, `polyX = a₁Y - 3X² - 2a₂X - a₄`
* `negPolynomial = -Y - a₁X - a₃`
* `ψ_n = normEDS b c d n` for `b = ψ_2`, `c = C Ψ_3`, `d = C preΨ_4`

For n = 3:
* `redInvarDenom_3 = complEDS 3 1 · complEDS 2 1 · normEDS 4 = 1 · 1 · ψ_4 = ψ_4`
  where `ψ_4 = (preΨ_4) · ψ_2`.
* `complEDSAux₂_3 = preNormEDS (b^4) c d 1 · preNormEDS (b^4) c d 4^2 · b
                  = 1 · preΨ_4^2 · ψ_2 = preΨ_4^2 · ψ_2`.
* `ψ_3 = C Ψ_3` (constant in Y), so `ψ_3^3 = C(Ψ_3^3)`.

So in char 3:
    `W.ω 3 = ψ_4 · INNER - preΨ_4^2 · ψ_2 + negPolynomial · C(Ψ_3^3)`

This script computes the {1, Y} basis coefficients by reducing
modulo Weierstrass `Y² ≡ -a₁·X·Y - a₃·Y + cubic_x` (char 3).

## Output

Lean-ready forms for `omega_3_X_coeff_char_three` and
`omega_3_Y_coeff_char_three`, plus the multiplier candidates for the
coupled-residual identity.
"""

from sympy import symbols, expand, Poly, simplify

X, Y, a1, a2, a3, a4, a6 = symbols('X Y a1 a2 a3 a4 a6')

# --- Char-3 b-coefficients ---
# In char 3: 4 = 1, 2 = 2.
b2 = a1**2 + a2  # = a₁² + 4·a₂ ≡ a₁² + a₂ (4 = 1)
b4 = 2*a4 + a1*a3
b6 = a3**2 + a6  # = a₃² + 4·a₆ ≡ a₃² + a₆
b8 = a1**2 * a6 + a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2  # b₈ char 3

# --- Char-3 collapsed forms ---
# Ψ_3 in char 3 collapses to b₂·X³ + b₈
Psi3_char3 = b2*X**3 + b8

# Mathlib's full Ψ_3 (works in any char, but collapses in char 3)
Psi3_full = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8

# preΨ_4 in char 3 (5 = 2, 10 = 1, 2 = 2)
preP4_char3 = (2*X**6 + b2*X**5 + 2*b4*X**4 + b6*X**3 + b8*X**2
               + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

# Ψ_2² in char 3 (4 = 1, 2 = 2)
Psi2Sq_char3 = X**3 + b2*X**2 + 2*b4*X + b6

# --- Bivariate polynomials in K[X][Y] ---
# polynomialY = 2Y + a₁X + a₃
polyY = 2*Y + a1*X + a3

# polynomialX = a₁·Y - 3X² - 2a₂X - a₄
polyX = a1*Y - 3*X**2 - 2*a2*X - a4

# negPolynomial = -Y - a₁X - a₃
negPoly = -Y - a1*X - a3

# Weierstrass polynomial = Y² + a₁XY + a₃Y - cubic_x
cubic_x = X**3 + a2*X**2 + a4*X + a6
W_poly = Y**2 + a1*X*Y + a3*Y - cubic_x

# ψ_2 = polynomialY = 2Y + a₁X + a₃ (bivariate)
psi2 = polyY

# Char-3 Weierstrass: Y² = -a₁XY - a₃Y + cubic_x
weierstrass_y_sq = -a1*X*Y - a3*Y + cubic_x


def reduce_mod_weierstrass(expr, max_iter=10):
    """Reduce Y² → weierstrass_y_sq iteratively until no Y² remains."""
    e = expand(expr)
    for _ in range(max_iter):
        # Replace Y² → weierstrass_y_sq
        if Y**2 not in e.atoms() and not any(Y**k in e.atoms() for k in range(2, 10)):
            break
        # Use polynomial division by Y² - weierstrass_y_sq
        e = expand(e.subs(Y**2, weierstrass_y_sq))
    return expand(e)


def reduce_mod3(expr, gens):
    """Reduce coefficients mod 3."""
    e = expand(expr)
    if e == 0:
        return 0
    p = Poly(e, *gens)
    new_expr = 0
    for monom, coeff in p.terms():
        int_c = int(coeff) % 3
        if int_c:
            term = 1
            for v, e_pow in zip(gens, monom):
                term *= v ** e_pow
            new_expr += int_c * term
    return expand(new_expr)


print("=" * 70)
print("ω_3 in char 3: structural setup")
print("=" * 70)

# In char 3 with these collapsed forms, compute the components of W.ω 3:
# ψ_4 = preΨ_4 · ψ_2 (bivariate, since ψ_2 is bivariate)
psi4 = preP4_char3 * psi2

# INNER for n=3 in char 3:
# INNER = (a₁·polyY - polyX) · Ψ_3 + 4·polynomial·(2·polynomial + Ψ_2Sq)
INNER = ((a1 * polyY - polyX) * Psi3_char3 +
         4 * W_poly * (2 * W_poly + Psi2Sq_char3))

# redInvarDenom_3 · INNER
redInvar_INNER = expand(psi4 * INNER)

# complEDSAux₂_3 = preΨ_4^2 · ψ_2 (in char 3)
complEDSAux2_3 = expand(preP4_char3**2 * psi2)

# negPolynomial · ψ_3³ = (-Y - a₁X - a₃) · Ψ_3³  (Ψ_3 is constant in Y)
negPoly_psi3_cubed = expand(negPoly * Psi3_char3**3)

# Full ω_3 in char 3:
omega3_full = expand(redInvar_INNER - complEDSAux2_3 + negPoly_psi3_cubed)

print("\nω_3 raw form (before Weierstrass reduction): degree in Y =",
      Poly(omega3_full, Y).degree())

# Reduce Y² → -a₁XY - a₃Y + cubic_x (char 3)
omega3_reduced = reduce_mod_weierstrass(omega3_full)
omega3_reduced_mod3 = reduce_mod3(omega3_reduced, [X, Y, a1, a2, a3, a4, a6])

print(f"\nω_3 after Weierstrass reduction + mod 3: degree in Y =",
      Poly(omega3_reduced_mod3, Y).degree() if omega3_reduced_mod3 != 0 else 0)

# Extract Y⁰ and Y¹ coefficients (basis decomposition)
poly_Y = Poly(omega3_reduced_mod3, Y)
print("\n--- Y⁰ and Y¹ coefficients of ω_3 (char 3) ---")
y0_coeff = poly_Y.coeff_monomial((0,)) if poly_Y.degree() >= 0 else 0
y1_coeff = poly_Y.coeff_monomial((1,)) if poly_Y.degree() >= 1 else 0
print(f"Y⁰ coeff (1-component, omega_3_X_coeff): {y0_coeff}")
print(f"\nY¹ coeff (Y-component, omega_3_Y_coeff): {y1_coeff}")

print("\n" + "=" * 70)
print("Lean-ready emission")
print("=" * 70)
print("""
/-- **X-coefficient of ω_3 in char 3** (Y⁰ coefficient in {1, Y} basis). -/
noncomputable def omega_3_X_coeff_char_three (W : WeierstrassCurve K) :
    Polynomial K :=
  -- TODO: substitute the explicit Y⁰ form from sympy output above
  sorry

/-- **Y-coefficient of ω_3 in char 3** (Y¹ coefficient in {1, Y} basis). -/
noncomputable def omega_3_Y_coeff_char_three (W : WeierstrassCurve K) :
    Polynomial K :=
  -- TODO: substitute the explicit Y¹ form from sympy output above
  sorry
""")
print("=" * 70)
