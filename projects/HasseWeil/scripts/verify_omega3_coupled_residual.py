#!/usr/bin/env python3
"""
Sympy verification of the q=3 char=3 coupled residual.

Computes:
  R_3(X) = A_3 · (ψ_2² + cubic_x) + B_3 · ψ_2 · cubic_x

where A_3, B_3 are the {1, Y} basis coefficients of `W.ω 3` after
char-3 Weierstrass reduction (extracted in
`scripts/verify_omega_3_coefficients.py`).

The coupled identity comes from matching `(α₀ + α₁·y_gen)^3 = mulByInt_y W 3`:
* y-side: α₁³·(ψ_2² + cubic_x) = B_3/ψ_3³.
* 1-side: α₀³ - α₁³·ψ_2·cubic_x = A_3/ψ_3³.

Multiplying through by ψ_3³ and combining yields:
  α₀³·ψ_3³ = A_3 + α₁³·ψ_2·cubic_x·ψ_3³

Substituting α₁³·ψ_3³ = B_3/(ψ_2² + cubic_x):
  α₀³·ψ_3³·(ψ_2² + cubic_x) = A_3·(ψ_2² + cubic_x) + B_3·ψ_2·cubic_x
                            = R_3(X)

So R_3 must be a cube in K(E)^q (the function field's q-th power image).
Sympy verifies that after b-relation substitution `b₈ = b₂·b₆ - b₄²`
in char 3, R_3 lies in K[X³] = expand-3 range.

## Output

* Witness polynomial g(X) such that R_3 = expand 3 (g) (after b-relation).
* Multiplier M_3 for `linear_combination M_3 * h_3P`.
"""

from sympy import symbols, expand, Poly, div

X, Y, a1, a2, a3, a4, a6 = symbols('X Y a1 a2 a3 a4 a6')

# --- Char-3 b-coefficients ---
b2 = a1**2 + a2  # 4 = 1
b4 = 2*a4 + a1*a3
b6 = a3**2 + a6  # 4 = 1
b8 = a1**2 * a6 + a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2

# --- Char-3 collapsed forms ---
Psi3_char3 = b2*X**3 + b8  # 3X⁴, 3b₄X², 3b₆X vanish

preP4_char3 = (2*X**6 + b2*X**5 + 2*b4*X**4 + b6*X**3 + b8*X**2
               + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

Psi2Sq_char3 = X**3 + b2*X**2 + 2*b4*X + b6  # 4=1, 2=2 stays

# --- Weierstrass setup ---
polyY = 2*Y + a1*X + a3
polyX = a1*Y - 3*X**2 - 2*a2*X - a4
negPoly = -Y - a1*X - a3
cubic_x = X**3 + a2*X**2 + a4*X + a6
W_poly = Y**2 + a1*X*Y + a3*Y - cubic_x
psi2 = polyY  # ψ_2 in K[X][Y]
weierstrass_y_sq = -a1*X*Y - a3*Y + cubic_x  # char 3


def reduce_mod_weierstrass(expr, max_iter=30):
    """Reduce Y^k (k≥2) → Y^(k-2)·weierstrass_y_sq term-by-term until degree ≤ 1."""
    e = expand(expr)
    for _ in range(max_iter):
        p = Poly(e, Y)
        if p.degree() < 2:
            break
        new_terms = 0
        for power, coeff in zip(reversed(range(p.degree() + 1)), p.all_coeffs()):
            if power < 2:
                new_terms += coeff * Y**power
            else:
                # Y^power = Y^(power-2) · weierstrass_y_sq
                new_terms += coeff * Y**(power - 2) * weierstrass_y_sq
        e = expand(new_terms)
    return expand(e)


def reduce_mod3(expr, gens):
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


# --- Compute W.ω 3 components ---
psi4 = preP4_char3 * psi2  # ψ_4 = preΨ_4 · ψ_2
INNER = ((a1 * polyY - polyX) * Psi3_char3 +
         4 * W_poly * (2 * W_poly + Psi2Sq_char3))
redInvar_INNER = expand(psi4 * INNER)
complEDSAux2_3 = expand(preP4_char3**2 * psi2)
negPoly_psi3_cubed = expand(negPoly * Psi3_char3**3)
omega3_full = expand(redInvar_INNER - complEDSAux2_3 + negPoly_psi3_cubed)

# Reduce modulo Weierstrass
omega3_reduced = reduce_mod_weierstrass(omega3_full)
omega3_mod3 = reduce_mod3(omega3_reduced, [X, Y, a1, a2, a3, a4, a6])

# Extract A_3 (Y⁰ coeff) and B_3 (Y¹ coeff)
poly_Y_omega = Poly(omega3_mod3, Y)
A_3 = poly_Y_omega.coeff_monomial((0,)) if poly_Y_omega.degree() >= 0 else 0
B_3 = poly_Y_omega.coeff_monomial((1,)) if poly_Y_omega.degree() >= 1 else 0

# --- The K[X]-only ψ_2 (since ω_3 reduces with Y² substituted, the 1-side
# uses a₁X + a₃ for ψ_2 NOT the bivariate polyY) ---
psi_2_X = a1*X + a3  # K[X]-only
psi_2_sq_plus_cubic_x = expand(psi_2_X**2 + cubic_x)
psi_2_times_cubic_x = expand(psi_2_X * cubic_x)

# --- Compute R_3 = A_3·(ψ_2² + cubic_x) + B_3·ψ_2·cubic_x ---
R_3 = expand(A_3 * psi_2_sq_plus_cubic_x + B_3 * psi_2_times_cubic_x)
R_3_mod3 = reduce_mod3(R_3, [X, a1, a2, a3, a4, a6])

print("=" * 70)
print("ω_3 coupled residual R_3(X) in char 3")
print("=" * 70)
print(f"\nR_3 degree in X: {Poly(R_3_mod3, X).degree() if R_3_mod3 != 0 else 'zero'}")

# --- Substitute b₈ = b₂·b₆ - b₄² (char-3 b-relation) ---
# After b-relation, all non-3-divisible exponents should vanish.
R_3_after_brel = expand(R_3.subs(b8, b2*b6 - b4**2))
R_3_after_brel_mod3 = reduce_mod3(R_3_after_brel, [X, a1, a2, a3, a4, a6])

# Check which exponents have nonzero coefficients
print("\n--- R_3 (after b-relation, mod 3): non-3-divisible exponents ---")
poly_X_R3 = Poly(R_3_after_brel_mod3, X)
nonzero_exps_subst = []
non_3_div_subst = []
for i in range(poly_X_R3.degree() + 1):
    c = poly_X_R3.nth(i)
    c_red = reduce_mod3(c, [a1, a2, a3, a4, a6])
    if c_red != 0:
        nonzero_exps_subst.append((i, c_red))
        if i % 3 != 0:
            non_3_div_subst.append(i)

print(f"Total nonzero exponents: {len(nonzero_exps_subst)}")
print(f"Non-3-divisible exponents (should be empty): {non_3_div_subst}")

if not non_3_div_subst:
    print("\n✓ R_3 ∈ K[X³] after applying char-3 b-relation.")
else:
    print(f"\n⚠ R_3 has non-3-divisible exponents: {non_3_div_subst}")
    print("R_3 (as defined) NOT in expand-3 range.")
    print("Testing alternative: R_3 · (ψ_2² + cubic_x)² ∈ expand-3 range?")

    R3_alt = expand(R_3 * psi_2_sq_plus_cubic_x ** 2)
    R3_alt_after_brel = expand(R3_alt.subs(b8, b2*b6 - b4**2))
    R3_alt_mod3 = reduce_mod3(R3_alt_after_brel,
                              [X, a1, a2, a3, a4, a6])

    poly_X_alt = Poly(R3_alt_mod3, X)
    nonzero_alt = []
    non_3_div_alt = []
    for i in range(poly_X_alt.degree() + 1):
        c = poly_X_alt.nth(i)
        c_red = reduce_mod3(c, [a1, a2, a3, a4, a6])
        if c_red != 0:
            nonzero_alt.append((i, c_red))
            if i % 3 != 0:
                non_3_div_alt.append(i)
    print(f"  Total nonzero: {len(nonzero_alt)}")
    print(f"  Non-3-divisible exponents: {non_3_div_alt}")

    if not non_3_div_alt:
        print("\n✓ R_3 · (ψ_2²+cubic_x)² ∈ K[X³] after b-relation.")
        print("→ The cubing identity has α³·ψ_3³·(ψ_2²+cubic_x)³ form.")
    else:
        print("\n⚠ Alternative also has non-3-divisible exponents.")
        print("Need yet different normalization.")

    # Also try: just B_3 · (ψ_2² + cubic_x)² alone
    print("\n--- Testing: B_3 · (ψ_2²+cubic_x)² ∈ expand-3 range? ---")
    B3_alt = expand(B_3 * psi_2_sq_plus_cubic_x ** 2)
    B3_alt_after_brel = expand(B3_alt.subs(b8, b2*b6 - b4**2))
    B3_alt_mod3 = reduce_mod3(B3_alt_after_brel,
                              [X, a1, a2, a3, a4, a6])
    poly_X_B3 = Poly(B3_alt_mod3, X)
    non_3_div_B3 = []
    for i in range(poly_X_B3.degree() + 1):
        c = poly_X_B3.nth(i)
        c_red = reduce_mod3(c, [a1, a2, a3, a4, a6])
        if c_red != 0 and i % 3 != 0:
            non_3_div_B3.append(i)
    print(f"  Non-3-divisible exponents in B_3·(ψ_2²+cubic_x)²: {non_3_div_B3}")

# --- Corrected R_3 form: R_3_full = R_3 · (ψ_2²+cubic_x)² ---
print("\n" + "=" * 70)
print("Corrected R_3 form: R_3·(ψ_2²+cubic_x)² extraction")
print("=" * 70)

R_3_full = expand(R_3 * psi_2_sq_plus_cubic_x ** 2)
R_3_full_after_brel = expand(R_3_full.subs(b8, b2*b6 - b4**2))
R_3_full_mod3 = reduce_mod3(R_3_full_after_brel,
                            [X, a1, a2, a3, a4, a6])

poly_X_full = Poly(R_3_full_mod3, X)
nonzero_full = []
for i in range(poly_X_full.degree() + 1):
    c = poly_X_full.nth(i)
    c_red = reduce_mod3(c, [a1, a2, a3, a4, a6])
    if c_red != 0:
        nonzero_full.append((i, c_red))

print(f"R_3_full (after b-relation, mod 3): {len(nonzero_full)} nonzero terms")
print(f"All exponents: {[i for i, _ in nonzero_full]}")
all_3_div = all(i % 3 == 0 for i, _ in nonzero_full)
print(f"All 3-divisible: {all_3_div}")

if all_3_div:
    # Extract witness g(X) such that R_3_full = expand 3 (g)
    g_full = 0
    for i, c in nonzero_full:
        g_full += c * X ** (i // 3)
    g_full = expand(g_full)

    # --- Lean code generation ---
    print("\n" + "=" * 70)
    print("Lean def emission (omega3_witness_polynomial_char_three)")
    print("=" * 70)

    def coeff_to_lean(c):
        """Convert sympy poly in (a1..a6) to Lean expression with W.a₁ etc."""
        c = expand(c)
        if c == 0:
            return "0"
        s = str(c)
        s = s.replace("**", "^")
        s = s.replace("a1", "W.a₁")
        s = s.replace("a2", "W.a₂")
        s = s.replace("a3", "W.a₃")
        s = s.replace("a4", "W.a₄")
        s = s.replace("a6", "W.a₆")
        return s

    g_poly = Poly(g_full, X)
    print("noncomputable def omega3_witness_polynomial_char_three")
    print("    (W : WeierstrassCurve K) : Polynomial K :=")
    terms_lean = []
    for n in range(g_poly.degree() + 1):
        c = g_poly.nth(n)
        if c == 0:
            continue
        c_lean = coeff_to_lean(c)
        if n == 0:
            terms_lean.append(f"  Polynomial.C ({c_lean})")
        elif n == 1:
            terms_lean.append(f"  Polynomial.C ({c_lean}) * Polynomial.X")
        else:
            terms_lean.append(
                f"  Polynomial.C ({c_lean}) * Polynomial.X ^ {n}")
    print(" +\n".join(terms_lean))

    # --- Compute multiplier M_3 for linear_combination ---
    print("\n" + "=" * 70)
    print("M_3 multiplier (for linear_combination * h_3P)")
    print("=" * 70)

    # We need: R_3_full - expand3(g) (over Z) = M_b · brel + 3 · M_3
    # After b-relation substitution: R_3_full|brel - expand3(g) = 3 · M_3
    expand3_g_full = 0
    for i, c in nonzero_full:
        expand3_g_full += c * X ** i
    expand3_g_full = expand(expand3_g_full)

    R3_full_after_brel_int = expand(R_3_full.subs(b8, b2*b6 - b4**2))
    residual_after = expand(R3_full_after_brel_int - expand3_g_full)
    M_3_mult = expand(residual_after / 3)
    check_M3 = expand(3 * M_3_mult - residual_after)
    print(f"M_3 (R3_full - expand3 g)/3 check: {check_M3 == 0}")

    M_3_poly = Poly(M_3_mult, X)
    M_3_terms = sum(1 for c in M_3_poly.all_coeffs() if c != 0)
    print(f"M_3 nonzero X-degree terms: {M_3_terms}")
