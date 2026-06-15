"""
Verify Φ_q ∈ F_q[X^q] generically in char p with b-relation, using polynomial
quotient.
"""
import sympy as sp

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

Psi_2_sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi_3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
preP4 = (2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
         + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))
preP5 = preP4*Psi_2_sq**2 - Psi_3**3
preP6 = Psi_3 * (preP5 - preP4**2)
preP7 = preP5*Psi_3**3 - preP4**3*Psi_2_sq**2

def reduce_via_b_rel(c, p):
    """Reduce c (a polynomial in b2,b4,b6,b8) mod p via the b-relation
    4b8 = b2*b6 - b4²."""
    if p == 2:
        # In char 2: relation is b2*b6 - b4² = 0 (since 4 = 0).
        # b8 is unconstrained. Replace b2*b6 by b4².
        c2 = sp.expand(c)
        # Iteratively replace b2*b6 with b4²
        for _ in range(20):
            new = sp.expand(c2.subs(b2*b6, b4**2))
            if new == c2:
                break
            c2 = new
        return c2 % 2 if isinstance(c2, sp.Integer) else sp.expand(c2)
    else:
        # char p ≠ 2: substitute b8 = (b2*b6 - b4²) * inv(4) mod p
        inv4 = pow(4, -1, p)
        b8_repl = inv4 * (b2*b6 - b4**2)
        c_subst = sp.expand(c.subs(b8, b8_repl))
        # Reduce coefficients mod p
        return c_subst

def check(P_X, q, p, label):
    print(f"=== {label}: q={q} in char p={p} ===")
    poly = sp.Poly(P_X, X)
    n_total = 0
    n_bad = 0
    for i, c in enumerate(poly.all_coeffs()[::-1]):
        c_red = reduce_via_b_rel(c, p)
        # Now reduce coefficients mod p
        c_modp = sp.Poly(c_red, b2, b4, b6, b8) if c_red != 0 else 0
        if c_red == 0:
            continue
        # Check coeff-by-coeff mod p
        if isinstance(c_modp, sp.Poly):
            terms = c_modp.terms()
            nonzero_mod_p = [(m, int(coef) % p) for m, coef in terms if int(coef) % p != 0]
            if not nonzero_mod_p:
                continue
        n_total += 1
        if i % q != 0:
            n_bad += 1
            short = str(c_red)[:80]
            print(f"  X^{i}: nonzero coefficient (after b-rel + mod {p}): {short}")
    if n_bad == 0:
        print(f"  ✓ All nonzero monomials at multiples of q={q}.")
    else:
        print(f"  ✗ {n_bad}/{n_total} nonzero monomials at non-multiples of q.")
    print()

# Φ_3 in char 3
Phi_3 = X * Psi_3**2 - preP4 * Psi_2_sq
check(Phi_3, q=3, p=3, label="Φ_3")

# Φ_2 in char 2
Phi_2 = X**4 - b4*X**2 - 2*b6*X - b8
check(Phi_2, q=2, p=2, label="Φ_2")

# Φ_5 in char 5
PsiSq_5 = preP5**2
Phi_5 = X * PsiSq_5 - preP6 * preP4 * Psi_2_sq
check(Phi_5, q=5, p=5, label="Φ_5")

# Now check ΨSq_q in char p — does the denominator also lie in F_p[X^q]?
ΨSq_3 = Psi_3**2  # n=3 odd
ΨSq_2 = Psi_2_sq  # n=2 even, ΨSq(2) = preΨ(2)² · Ψ_2² = 1·Ψ_2² = Ψ_2²
ΨSq_5 = preP5**2  # n=5 odd
check(ΨSq_3, q=3, p=3, label="ΨSq_3")
check(ΨSq_2, q=2, p=2, label="ΨSq_2")
check(ΨSq_5, q=5, p=5, label="ΨSq_5")
