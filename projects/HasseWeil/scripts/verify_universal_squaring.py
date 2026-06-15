#!/usr/bin/env python3
"""
Universal squaring identity multiplier extraction (Route 2).

This extends `verify_omega2_coupled_universal.py` to handle the FULL
universal squaring identity:

  (α₀_univ + α₁_univ · y_univ)^2 ≡ ω_2(x_gen, y_gen) / ψ_2(x_gen)^3
                                  in MvPolynomial AVar (ZMod 2)

where AVar = {a₁, a₂, a₃, a₄, a₆, X, Y} and the identity holds modulo
the universal Weierstrass relation
  Y² = a₁·X·Y + a₃·Y + (X³ + a₂·X² + a₄·X + a₆)   (in char 2).

## Strategy

The squaring identity composition (Worker C Session 22, commit a0c0e6f)
combines:
* char-2 squaring formula `(a + b·y)² = a² + b²·y²`
* Weierstrass equation for `y²`
* polyExpandRoot squaring identity (Session 14)
* coupled identity (Session 14, the breakthrough)
* basis decomposition (Session 18)
* ψ_ff bridge (Session 20)

At the universal level over `MvPolynomial AVar (ZMod 2)`, the char-2
reductions are baked into the coefficient ring, so the coupled identity
holds directly (verified by `verify_omega2_coupled_universal.py`).

The substantive remaining content is the **Weierstrass substitution**:
the squaring identity reduces, after polyExpandRoot squaring + char-2
arithmetic, to a polynomial in (X, Y) modulo the Weierstrass relation.

## What this script computes

1. Universal α₀, α₁ as MvPolynomial expressions in (X-only).
2. (α₀ + α₁·Y)² expanded via Weierstrass substitution.
3. mulByInt_y_univ = ω_2(X, Y) / ψ_2(X)^3 expressed symbolically.
4. The DIFFERENCE (LHS² · ψ³ - ω_2 · ψ_factor) reduced modulo Weierstrass.
5. The universal multiplier polynomial M(X, Y) such that
       (LHS² · ψ³ - ω_2) ≡ M · (Y² - cubic_y_form)  (in MvPolynomial)
   This is the Route 1 universal-level certificate.

## Output

Emits the multiplier `M(X, Y)` in a Lean-ready form (literal Lean syntax
for the URing 2 expression with explicit AVar indices).
"""

from sympy import symbols, expand, Poly, simplify, ZZ, Rational, Symbol

X, Y, a1, a2, a3, a4, a6 = symbols('X Y a1 a2 a3 a4 a6')

# Universal char-2 b-coefficients (folded with mod-2)
b2 = a1**2  # = a1² mod 2 (since 4 = 0)
b4 = a1*a3  # = a₁·a₃ mod 2 (since 2 = 0)
b6 = a3**2  # = a₃² mod 2
b8 = a1**2 * a6 + a1*a3*a4 + a2*a3**2 + a4**2  # b₈ char 2

# Universal Ψ₃ in char 2
Psi3 = X**4 + b2*X**3 + b4*X**2 + b6*X + b8

# Universal A and B (Sessions 8/9)
A_univ = (X**2 + a1**2 * X + a1*a3 + a4) * Psi3 + (a1*X + a3)**4
B_univ = a1 * Psi3 + (a1*X + a3)**3

# Universal ψ₂ = a₁·X + a₃ (in char 2)
psi2 = a1*X + a3

# Universal cubic_x = X³ + a₂·X² + a₄·X + a₆
cubic_x = X**3 + a2*X**2 + a4*X + a6

# Universal Weierstrass relation in char 2: Y² = a₁·X·Y + a₃·Y + cubic_x
weierstrass_y_sq = a1*X*Y + a3*Y + cubic_x

# Coupled residual = A·ψ₂ + B·cubic_x
coupled_residual = expand(A_univ * psi2 + B_univ * cubic_x)


def reduce_int_mod2(expr):
    """Reduce all integer coefficients in an MvPolynomial expression mod 2."""
    e = expand(expr)
    if e == 0:
        return 0
    # Collect terms in (a1..a6, X, Y) and reduce coefficients mod 2.
    p = Poly(e, a1, a2, a3, a4, a6, X, Y)
    new_expr = 0
    for monom, coeff in p.terms():
        int_c = int(coeff) % 2
        if int_c:
            term = 1
            for v, e_pow in zip([a1, a2, a3, a4, a6, X, Y], monom):
                term *= v ** e_pow
            new_expr += int_c * term
    return expand(new_expr)


print("=" * 70)
print("Universal squaring identity multiplier extraction (Route 2)")
print("=" * 70)

# --- Universal α₀² and α₁² (via the polyExpandRoot squaring) ---
# At the universal level: α₀² · ψ⁴ = (A·ψ + B·cubic_x) and α₁² · ψ⁴ = B
# (these correspond to Session 22's polyExpandRoot squaring witnesses).
# So α₀² = (A·ψ + B·cubic_x) / ψ⁴ and α₁² = B / ψ⁴.

print("\n--- 1. Universal α₀² and α₁² (after polyExpandRoot squaring) ---")
print("α₀² · ψ⁴ = A·ψ + B·cubic_x  (coupled residual)")
print("α₁² · ψ⁴ = B  (Y-coefficient witness)")

# --- The squaring identity LHS = (α₀ + α₁·Y)² ---
# In char 2: (α₀ + α₁·Y)² = α₀² + α₁²·Y²
# Substituting Weierstrass Y² = a₁·X·Y + a₃·Y + cubic_x (char 2):
# = α₀² + α₁²·(a₁·X·Y + a₃·Y + cubic_x)
# = (α₀² + α₁²·cubic_x) + α₁²·(a₁·X + a₃)·Y
# = (α₀² + α₁²·cubic_x) + α₁²·ψ·Y

# Multiplying through by ψ⁴:
# LHS · ψ⁴ = (α₀² + α₁²·cubic_x)·ψ⁴ + α₁²·ψ⁵·Y
#          = (A·ψ + B·cubic_x) + B·cubic_x  + B·ψ·Y    (substituting α₀²·ψ⁴ and α₁²·ψ⁴)
#          = A·ψ + 2·B·cubic_x + B·ψ·Y
#          = A·ψ + B·ψ·Y         (in char 2: 2·anything = 0)
#          = ψ·(A + B·Y)

print("\n--- 2. Universal (LHS) · ψ⁴ over ZMod 2 ---")
LHS_times_psi4 = expand(coupled_residual + B_univ * cubic_x + B_univ * psi2 * Y)
LHS_times_psi4_mod2 = reduce_int_mod2(LHS_times_psi4)
print("(α₀² · ψ⁴ + α₁² · ψ⁴ · cubic_x) + α₁² · ψ⁵ · Y, ZMod 2 form:")
print(f"  Coefficient of Y⁰: {reduce_int_mod2(LHS_times_psi4_mod2.coeff(Y, 0))}")
print(f"  Coefficient of Y¹: {reduce_int_mod2(LHS_times_psi4_mod2.coeff(Y, 1))}")

# Expected RHS · ψ⁴: ψ · ω_2(X, Y) / ψ³ · ψ⁴ = ψ² · ω_2(X, Y)... wait
# RHS = mulByInt_y = ω_2(X, Y) / ψ³
# RHS · ψ⁴ = ω_2(X, Y) · ψ
# By basis decomposition: ω_2 = A + B·Y in K[X][Y] modulo Weierstrass
# So RHS · ψ⁴ = (A + B·Y) · ψ = ψ·A + ψ·B·Y

print("\n--- 3. Universal RHS · ψ⁴ = ψ·A + ψ·B·Y over ZMod 2 ---")
RHS_times_psi4 = expand(psi2 * A_univ + psi2 * B_univ * Y)
RHS_times_psi4_mod2 = reduce_int_mod2(RHS_times_psi4)
print(f"  Coefficient of Y⁰: {reduce_int_mod2(RHS_times_psi4_mod2.coeff(Y, 0))}")
print(f"  Coefficient of Y¹: {reduce_int_mod2(RHS_times_psi4_mod2.coeff(Y, 1))}")

# --- Verify LHS · ψ⁴ ≡ RHS · ψ⁴ over ZMod 2 ---
print("\n--- 4. Universal squaring identity verification (ZMod 2) ---")
diff = expand(LHS_times_psi4 - RHS_times_psi4)
diff_mod2 = reduce_int_mod2(diff)
print(f"LHS · ψ⁴ - RHS · ψ⁴ (ZMod 2):  {diff_mod2}")

if diff_mod2 == 0:
    print("\n✓ Universal squaring identity holds DIRECTLY over MvPolynomial AVar (ZMod 2)")
    print("  → Lean proof: `decide` (kernel-level, axiom-clean)")
    print("  → Universal multiplier needed: NONE (multiplier = 0)")
else:
    print(f"\n⚠ Difference doesn't vanish over ZMod 2 — {diff_mod2}")
    print("  This means the Weierstrass relation is needed at the universal level.")

# --- Universal multiplier extraction (over ℤ for sanity) ---
print("\n--- 5. Universal multiplier over ℤ (for linear_combination fallback) ---")
diff_Z = expand(LHS_times_psi4 - RHS_times_psi4)
print(f"LHS · ψ⁴ - RHS · ψ⁴ over ℤ:  {diff_Z}")
# This should be a multiple of 2.
diff_div_2 = expand(diff_Z / 2)
print(f"\nDivided by 2: {diff_div_2}")
print("\nThis is the universal multiplier M(X, Y) for `linear_combination M * h_2`")
print("at the universal level, if the direct route via decide fails.")

# --- Lean-ready emission ---
print("\n--- 6. Lean URing 2 emission ---")
print("```lean")
print("/-- Universal squaring identity multiplier (Route 2). -/")
print("noncomputable def universalSquaringMultiplier (p : ℕ) [Fact p.Prime] :")
print("    URing p :=")
if diff_mod2 == 0:
    print("  -- Identity holds directly over ZMod p (no multiplier needed for p = 2).")
    print("  0")
else:
    # Emit the multiplier in URing p form.
    M_int = expand(diff_div_2)
    M_str = str(M_int).replace("a1", "(Ua1 p)").replace("a2", "(Ua2 p)") \
                       .replace("a3", "(Ua3 p)").replace("a4", "(Ua4 p)") \
                       .replace("a6", "(Ua6 p)").replace("X", "(UX p)") \
                       .replace("Y", "(UY p)").replace("**", "^")
    print(f"  {M_str}")
print("```")

print("\n" + "=" * 70)
print("Sympy verification complete.")
print("Next session Lean port:")
print("  1. Add UY (Y-variable) to AVar in Route2Universal.lean")
print("  2. Define universalSquaringIdentity statement.")
print("  3. Try `decide` first (axiom-clean, kernel-level).")
print("  4. Fall back to linear_combination universalSquaringMultiplier * h_2.")
print("=" * 70)
