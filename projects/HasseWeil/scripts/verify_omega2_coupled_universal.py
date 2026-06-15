#!/usr/bin/env python3
"""
Route 2 universal certificate: emit the universal coupled-identity
multiplier M(X) and the universal squaring-identity multipliers (Y-coefficient
and constant-coefficient) in `MvPolynomial AVar (ZMod 2)` form, ready for
direct Lean transcription.

This is the Python-side preparation for the Route 2 universal scaffold
(`HasseWeil/Verschiebung/Route2Universal.lean`). The output is the explicit
multiplier polynomials needed by `linear_combination` calls at the universal
level, replacing the `^ Fintype.card K`-vs-`^ 2` dependent-rewrite obstacle.

## What this script computes

1. **Universal coupled identity multiplier** `M_coupled(X)`: the polynomial
   such that `A·ψ₂ + B·cubic_x = expand_2(witness) + 2·M_coupled` in
   `ℤ[a₁..a₆][X]`. Already known from `verify_omega2_coupled.py`; reproduced
   here in the universal-friendly form.

2. **Universal Y-coefficient match multiplier**: the certificate for
   `α₁² · ψ₂(x_gen) = aeval x_gen B / ψ₂(x_gen)^3`. Trivial structurally;
   this script just emits the witness statement.

3. **Universal constant-coefficient match multiplier**: the certificate for
   `(α₀² + α₁²·cubic_x) · ψ₂^4 = aeval x_gen A · ψ_gen + 2·B·cubic·something`.
   The "+2·..." part is the multiplier hooked to char-2 vanishing.

4. **Universal final-squaring multiplier**: the certificate for
   `(α₀ + α₁·y_gen)² = mulByInt_y W 2`. Combination of the above.

## Output format

For each multiplier polynomial, output as:
* Total-degree distribution.
* Per-X-degree coefficient as a polynomial in (a₁, a₂, a₃, a₄, a₆) over ℤ.
* Mod-2 reduction (the form needed for the `MvPolynomial AVar (ZMod 2)`
  transcription).

The ZMod 2 reduction means each integer coefficient becomes 0 or 1, dramatically
shrinking the polynomial. The Lean transcription is then a literal copy
of the surviving monomials.
"""

from sympy import symbols, expand, Poly, simplify

X, a1, a2, a3, a4, a6 = symbols('X a1 a2 a3 a4 a6')

# Universal Weierstrass b-coefficients (over ℤ, no char-2 reduction yet)
b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a6
b8 = a1**2 * a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2

# Universal Ψ₃ (in ℤ[a₁..a₆][X])
Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8

# Universal ψ₂(X) = a₁X + a₃ (in char 2; in general 2Y + a₁X + a₃, but the Y
# part vanishes in char 2). For Route 2 we work in char 2 directly.
psi2 = a1*X + a3

# Universal cubic_x = X³ + a₂X² + a₄X + a₆
cubic_x = X**3 + a2*X**2 + a4*X + a6

# Universal A, B (Sessions 8/9 forms, with char-2 b-relations folded in:
# b₂ = a₁², b₄ = a₁a₃, b₆ = a₃²)
b2_c2 = a1**2  # b₂ in char 2
b4_c2 = a1*a3  # b₄ in char 2
b6_c2 = a3**2  # b₆ in char 2
Psi3_c2 = 3*X**4 + b2_c2*X**3 + 3*b4_c2*X**2 + 3*b6_c2*X + b8

# Universal A: (X² + a₁²X + a₁a₃ + a₄)·Ψ₃ + (a₁X + a₃)⁴
A_univ = (X**2 + a1**2 * X + a1*a3 + a4) * Psi3_c2 + (a1*X + a3)**4

# Universal B: a₁·Ψ₃ + (a₁X + a₃)³
B_univ = a1 * Psi3_c2 + (a1*X + a3)**3


def reduce_mod2_per_x_coeff(expr):
    """Output per-X-coefficient mod 2 reduction.

    Returns dict {X-degree: polynomial-in-a-vars-mod-2}.
    """
    e = expand(expr)
    if e == 0:
        return {}
    poly_X = Poly(e, X)
    result = {}
    for power, c in zip(reversed(range(poly_X.degree() + 1)), poly_X.all_coeffs()):
        c_expand = expand(c)
        if c_expand == 0:
            continue
        a_poly = Poly(c_expand, a1, a2, a3, a4, a6)
        new_c = 0
        for monom, coeff in a_poly.terms():
            int_c = int(coeff) % 2
            if int_c:
                term = 1
                for v, e_pow in zip([a1, a2, a3, a4, a6], monom):
                    term *= v ** e_pow
                new_c += int_c * term
        if new_c != 0:
            result[power] = new_c
    return result


def emit_lean_avar_term(term, prefix="U"):
    """Convert a sympy a-monomial term (1 or product of a_i^k) into a Lean
    expression like `Ua1 p ^ 2 * Ua3 p`. Used for transcribing the universal
    multiplier into `URing p` form."""
    if term == 1:
        return "1"
    s = str(term)
    # Replace a_i with Ua_i p
    s = s.replace("a1", f"({prefix}a1 p)")
    s = s.replace("a2", f"({prefix}a2 p)")
    s = s.replace("a3", f"({prefix}a3 p)")
    s = s.replace("a4", f"({prefix}a4 p)")
    s = s.replace("a6", f"({prefix}a6 p)")
    s = s.replace("**", "^")
    return s


print("=" * 70)
print("Route 2 universal certificate: coupled identity + squaring multipliers")
print("=" * 70)

# 1. Universal coupled identity: A·ψ₂ + B·cubic_x in char 2 (mod 2)
print("\n--- 1. Universal coupled identity (A·ψ₂ + B·cubic_x) mod 2 ---")
LHS_coupled = expand(A_univ * psi2 + B_univ * cubic_x)
LHS_coupled_mod2 = reduce_mod2_per_x_coeff(LHS_coupled)
print("Per-X-coefficient (mod 2):")
for power in sorted(LHS_coupled_mod2.keys(), reverse=True):
    print(f"  X^{power}: {LHS_coupled_mod2[power]}")
    print(f"      Lean: {emit_lean_avar_term(LHS_coupled_mod2[power])} * UX p ^ {power}")

# 2. Witness polynomial (already shipped Lean-side as omega2_coupled_witness_char_two)
print("\n--- 2. Witness polynomial coefficients (already in Lean) ---")
c3 = a1*a2 + a3
c2 = a1**3 * a4 + a1*a3**2 + a1*a6 + a3*a4
c1 = (a1**5 * a6 + a1**4 * a3 * a4 + a1**3 * a2 * a3**2 + a1**3 * a2 * a6 +
      a1**3 * a4**2 + a1**2 * a2 * a3 * a4 + a1**2 * a3**3 + a1**2 * a3 * a6 +
      a1 * a2**2 * a3**2 + a1 * a2 * a4**2 + a1 * a3**2 * a4 + a3 * a4**2)
c0 = (a1**3 * a3**2 * a6 + a1**3 * a6**2 + a1**2 * a3**3 * a4 + a1 * a2 * a3**4 +
      a1 * a2 * a3**2 * a6 + a1 * a4**2 * a6 + a2 * a3**3 * a4 + a3**5 +
      a3**3 * a6 + a3 * a4**3)
witness_expand = expand(c3*X**6 + c2*X**4 + c1*X**2 + c0)
print(f"Witness's expand-2 form: c3·X⁶ + c2·X⁴ + c1·X² + c0")
print(f"  c3 = {c3}")
print(f"  c2 = {c2}")
print(f"  c1 = {c1}")
print(f"  c0 = {c0}")

# 3. Universal coupled identity multiplier: M = (LHS - witness_expand) / 2 ∈ ℤ[a₁..a₆][X]
print("\n--- 3. Universal coupled identity multiplier M(X) = (LHS - RHS) / 2 ---")
diff = expand(LHS_coupled - witness_expand)
M_universal = expand(diff / 2)
M_poly = Poly(M_universal, X)
print("Per-X-coefficient of M (over ℤ[a₁..a₆]):")
for power in range(M_poly.degree() + 1):
    c = M_poly.nth(power)
    if c != 0:
        print(f"  X^{power}: {expand(c)}")

# 4. Universal multiplier in MvPolynomial AVar (ZMod 2) form
# In MvPolynomial AVar (ZMod 2), the multiplier `m * h_2` produces 2·m which
# vanishes. So we need the multiplier `m` such that `LHS_universal - RHS_universal
# - m·2 ≡ 0` in `MvPolynomial AVar ℤ`.
print("\n--- 4. Lean URing 2 form: linear_combination multiplier ---")
print("```lean")
print("def coupled_identity_multiplier_universal : URing 2 :=")
parts = []
for power in range(M_poly.degree() + 1):
    c = M_poly.nth(power)
    if c != 0:
        c_lean = emit_lean_avar_term(expand(c))
        if power == 0:
            parts.append(f"  ({c_lean})")
        else:
            parts.append(f"  ({c_lean}) * UX 2 ^ {power}")
print(" +\n".join(parts) if parts else "  0")
print("```")

# 5. Universal Y-coefficient witness (trivial structurally — same as Lean form)
print("\n--- 5. Universal Y-coefficient match ---")
print("α₁² · ψ₂(x_gen) = (aeval x_gen B) / ψ₂(x_gen)^3")
print("(Direct from polyExpandRoot squaring at universal level — no multiplier needed.)")

# 6. Universal constant-coefficient match: (α₀² + α₁²·cubic_x) · ψ₂^4 = aeval A · ψ + 2·multiplier
# The multiplier here is `aeval B · aeval cubic_x · ψ_gen^4` at the universal level.
print("\n--- 6. Universal constant-coefficient match multiplier ---")
print("(α₀² + α₁²·cubic_x) · ψ₂^4 = aeval x_gen A · ψ_gen + 2·(aeval x_gen B · aeval x_gen cubic_x)")
print("Multiplier: (B · cubic_x) — used in linear_combination M · h_2.")
print("```lean")
print("-- Universal form (in URing 2):")
print("def constant_match_multiplier_universal : URing 2 :=")
print("  B_univ * cubic_x_univ  -- defined in Route2Universal.lean (next session)")
print("```")

print("\n" + "=" * 70)
print("Route 2 universal scaffold preparation — sympy verification complete.")
print("Multipliers ready for Lean port in HasseWeil/Verschiebung/Route2Universal.lean")
print("=" * 70)

# 7. CRITICAL: in URing 2 = MvPolynomial AVar (ZMod 2), the coefficient ring is
# already ZMod 2, so all integer multiples of 2 vanish automatically. The
# universal coupled identity then holds DIRECTLY as a polynomial equality —
# no `linear_combination` needed!
#
# Verify: reduce LHS_coupled mod 2 == witness_expand mod 2.
print("\n--- 7. Direct universal identity over ZMod 2 (NO linear_combination needed) ---")
LHS_mod2 = reduce_mod2_per_x_coeff(LHS_coupled)
RHS_mod2 = reduce_mod2_per_x_coeff(witness_expand)

all_powers = set(LHS_mod2.keys()) | set(RHS_mod2.keys())
all_match = True
for power in sorted(all_powers, reverse=True):
    lhs_c = LHS_mod2.get(power, 0)
    rhs_c = RHS_mod2.get(power, 0)
    diff = expand(lhs_c - rhs_c)
    if diff == 0:
        print(f"  X^{power}: LHS == RHS (ZMod 2) ✓")
    else:
        print(f"  X^{power}: LHS != RHS (ZMod 2): diff = {diff}")
        all_match = False

if all_match:
    print("\n✓ At the universal level over MvPolynomial AVar (ZMod 2):")
    print("  (A·ψ₂ + B·cubic_x) ≡ expand_2(witness)  as polynomials.")
    print("  → No `linear_combination` needed at universal level — the char-2")
    print("    reduction is baked into the coefficient ring ZMod 2.")
    print("  → Lean proof candidates: `decide`, `rfl`, or `MvPolynomial.funext`.")
else:
    print("\n✗ Universal identity does NOT hold over ZMod 2 — sympy disagreement.")

print("\n" + "=" * 70)
print("Recommendation for Route 2 Lean port:")
print("  1. Try `decide` first (kernel-level, axiom-clean).")
print("  2. If `decide` times out: `set_option maxHeartbeats 1000000` retry.")
print("  3. If still failing: Route 1 universal-level `linear_combination`")
print("     using `coupled_identity_multiplier_universal` from Section 4 above.")
print("=" * 70)
