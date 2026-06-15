#!/usr/bin/env python3
"""
Universal Φ_3 ∈ K[X^3] verification (q=3 char=3, b-coefficient form).

Computes Φ_3 in char 3 with GENERIC a₁, a₂, a₃, a₄, a₆ coefficients
(reducing mod 3 throughout), checks which exponents have nonzero
coefficients, and extracts the witness polynomial g such that
Φ_3 = expand 3 (g) modulo char-3 b-relations.

## Strategy

In char 3:
* `Ψ_3 = b₂·X³ + b₈`  (the 3X⁴, 3b₄X², 3b₆X terms vanish)
* `ΨSq_3 = Ψ_3² = b₂²·X⁶ + 2·b₂·b₈·X³ + b₈²`
* `X·ΨSq_3 = b₂²·X⁷ + 2·b₂·b₈·X⁴ + b₈²·X`
* `Ψ_2² = X³ + b₂·X² + 2b₄·X + b₆`  (4=1, 2=2 in char 3)
* `preΨ_4 = 2X⁶ + b₂X⁵ + 2b₄X⁴ + b₆X³ + b₈X² + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²)`

Φ_3 = X·ΨSq_3 - preΨ_4·Ψ_2².

Sympy expands and reduces mod 3, then groups by powers of X.

## Output

Lean-ready `polyExpandRoot` witness for `Φ_3 ∈ Set.range (expand K 3)`.
"""

from sympy import symbols, expand, Poly

X, b2, b4, b6, b8 = symbols('X b2 b4 b6 b8')

# Char-3 forms (after reducing 3 = 0, 4 = 1, 5 = 2, 10 = 1)
Psi_3 = b2*X**3 + b8                                     # 3X⁴ etc. vanish
PsiSq_3 = expand(Psi_3**2)
Psi_2_sq = X**3 + b2*X**2 + 2*b4*X + b6                   # 4=1, 2=2
preP_4 = (2*X**6 + b2*X**5 + 2*b4*X**4 + b6*X**3 + b8*X**2
          + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

Phi_3_char3 = expand(X * PsiSq_3 - preP_4 * Psi_2_sq)


def reduce_mod3(poly_expr, gens):
    """Reduce coefficients of poly_expr (in symbol generators gens) mod 3."""
    p = Poly(poly_expr, *gens)
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
print("Φ_3 in char 3 (generic b₂, b₄, b₆, b₈)")
print("=" * 70)
Phi_3_char3_mod = reduce_mod3(Phi_3_char3, [X, b2, b4, b6, b8])
print(f"Φ_3 (char 3, generic): {Phi_3_char3_mod}")

# Group by powers of X
poly_X = Poly(Phi_3_char3_mod, X)
print("\n--- Coefficients of Φ_3 by X power (mod 3) ---")
nonzero_exps = []
for i, c in enumerate(poly_X.all_coeffs()[::-1]):
    c_mod = reduce_mod3(c, [b2, b4, b6, b8])
    if c_mod != 0:
        print(f"  X^{i}: {c_mod}")
        nonzero_exps.append((i, c_mod))

# Check which exponents are NOT divisible by 3
non_3_div = [i for i, _ in nonzero_exps if i % 3 != 0]
print(f"\nNon-3-divisible exponents: {non_3_div}")
if non_3_div:
    print("Φ_3 is NOT in K[X³] without using b-relations!")
    print("(Will need b_relation_of_char_three to cancel non-3-divisible terms.)")
else:
    print("✓ Φ_3 IS in K[X³] directly with char-3 b-coefficients.")

# Let's also verify the b-relation b₈ = b₂·b₆ - b₄² in char 3 by substitution.
# In char 3: b₂ = a₁² + a₂, b₄ = 2a₄ + a₁a₃, b₆ = a₃² + a₆,
# b₈ = a₁²a₆ + a₂a₆ - a₁a₃a₄ + a₂a₃² - a₄²
print("\n--- Char-3 b-relation: b₈ = b₂·b₆ - b₄² ---")
a1, a2, a3, a4, a6 = symbols('a1 a2 a3 a4 a6')
b2_g = a1**2 + a2  # 4 = 1
b4_g = 2*a4 + a1*a3
b6_g = a3**2 + a6  # 4 = 1
b8_g = a1**2*a6 + a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2
b8_predicted = expand(b2_g*b6_g - b4_g**2)
diff = expand(b8_g - b8_predicted)
diff_mod3 = reduce_mod3(diff, [a1, a2, a3, a4, a6])
print(f"b₈ - (b₂·b₆ - b₄²) (mod 3): {diff_mod3}")
if diff_mod3 == 0:
    print("✓ Confirmed: b₈ = b₂·b₆ - b₄² in char 3.")

# --- Substitute b₈ = b₂·b₆ - b₄² into Φ_3 and check K[X³] membership ---
print("\n--- Φ_3 with b₈ → b₂·b₆ - b₄² (char 3) ---")
Phi_3_subst = Phi_3_char3.subs(b8, b2*b6 - b4**2)
Phi_3_subst_mod = reduce_mod3(Phi_3_subst, [X, b2, b4, b6])
print(f"Φ_3 after substitution: {Phi_3_subst_mod}")

poly_X_subst = Poly(Phi_3_subst_mod, X)
print("\n--- Coefficients by X power (mod 3, b-relation applied) ---")
nonzero_exps_subst = []
for i, c in enumerate(poly_X_subst.all_coeffs()[::-1]):
    c_mod = reduce_mod3(c, [b2, b4, b6])
    if c_mod != 0:
        print(f"  X^{i}: {c_mod}")
        nonzero_exps_subst.append((i, c_mod))

non_3_div_subst = [i for i, _ in nonzero_exps_subst if i % 3 != 0]
print(f"\nNon-3-divisible exponents (after b-relation): {non_3_div_subst}")
if not non_3_div_subst:
    print("✓ Φ_3 ∈ K[X³] after applying b₈ = b₂·b₆ - b₄² in char 3.")

    # Extract the K[X³] witness g(X) such that Φ_3 = g(X^3)
    # Map X^(3k) → X^k
    print("\n--- Lean witness g such that Φ_3 = expand 3 g ---")
    g_expr = 0
    for i, c in enumerate(poly_X_subst.all_coeffs()[::-1]):
        c_mod = reduce_mod3(c, [b2, b4, b6])
        if c_mod != 0:
            assert i % 3 == 0
            g_expr += c_mod * X ** (i // 3)
    g_expr = expand(g_expr)
    print(f"g(X) = {g_expr}")

print("\n" + "=" * 70)
