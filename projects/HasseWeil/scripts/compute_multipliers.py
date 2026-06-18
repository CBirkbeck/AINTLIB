"""
Compute polynomial multipliers M_i for the Wronskian auxiliary identities.

The m=3 and m=4 identities are TRUE as identities in R[X] when R is a Weierstrass
curve coefficient ring (where b_relation: 4b8 = b2*b6 - b4^2 holds), but NOT true
in the abstract polynomial ring Z[b2, b4, b6, b8, X].

For each coefficient of X^i in LHS - RHS, there is an explicit polynomial
M_i(b2, b4, b6, b8) such that:

    (LHS - RHS).coeff(X^i) = M_i * (4b8 - b2*b6 + b4^2)

This script computes all M_i using polynomial division (with b8 as the leading
variable in the divisor).
"""

import sympy as sp

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

# Weierstrass curve division polynomials
Psi_2_sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi_3    = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
preP4    = (2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
           + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

# Derivatives w.r.t. X
dPsi_2_sq = sp.diff(Psi_2_sq, X)
dPsi_3    = sp.diff(Psi_3,    X)
dpreP4    = sp.diff(preP4,    X)
dM        = sp.diff(preP4 * Psi_2_sq, X)

# m=3 identity
LHS_3 = 4*Psi_3**3 + 2*preP4*Psi_2_sq*dPsi_3 - dM*Psi_3
RHS_3 = 3*preP4*Psi_2_sq**2 - 3*preP4**2
diff_3 = sp.expand(LHS_3 - RHS_3)

b_rel = 4*b8 - b2*b6 + b4**2

def compute_multipliers(diff_poly, label, max_deg):
    print(f"=== Multipliers for {label} ===")
    total_ok = 0
    multipliers = {}
    for i in range(max_deg + 1):
        c = sp.expand(diff_poly.coeff(X, i))
        if c == 0:
            multipliers[i] = sp.Integer(0)
            print(f"  i={i:2d}: coeff is 0, M_{i} = 0")
            total_ok += 1
            continue
        c_poly = sp.Poly(c, b8)
        q = sp.Integer(0)
        remainder_expr = c
        while sp.Poly(remainder_expr, b8).degree() >= 1:
            rem_poly = sp.Poly(remainder_expr, b8)
            lc = rem_poly.LC()
            d = rem_poly.degree()
            term_coef = sp.nsimplify(lc / 4, rational=True)
            term = term_coef * b8**(d-1)
            q = q + term
            remainder_expr = sp.expand(remainder_expr - term * b_rel)
        rem_simplified = sp.simplify(remainder_expr)
        if rem_simplified != 0:
            print(f"  i={i:2d}: NOT DIVISIBLE, remainder = {rem_simplified}")
            multipliers[i] = None
        else:
            q_expr = sp.expand(q)
            check = sp.expand(q_expr * b_rel) - c
            if sp.simplify(check) != 0:
                print(f"  i={i:2d}: CHECK FAILED. q*b_rel - c = {sp.simplify(check)}")
                multipliers[i] = None
            else:
                multipliers[i] = q_expr
                total_ok += 1
                q_str = str(q_expr)
                print(f"  i={i:2d}: M_{i} = {q_str}")
    print(f"Total verified: {total_ok}/{max_deg+1}")
    return multipliers


m3 = compute_multipliers(diff_3, "m=3 (LHS - RHS)", max_deg=12)

# m=4 identity
LHS_4 = (preP4**2 * Psi_2_sq)**2 - (
    sp.diff(Psi_3 * (preP4 * Psi_2_sq**2 - Psi_3**3), X) * (preP4**2 * Psi_2_sq)
    - Psi_3 * (preP4 * Psi_2_sq**2 - Psi_3**3) * sp.diff(preP4**2 * Psi_2_sq, X)
)
RHS_4 = 4 * (
    Psi_3**2 * preP4 * (Psi_3 * ((preP4 * Psi_2_sq**2 - Psi_3**3) - preP4**2))
    - preP4 * (preP4 * Psi_2_sq**2 - Psi_3**3)**2
)
diff_4 = sp.expand(LHS_4 - RHS_4)

print()
print(f"m=4 diff polynomial: degree in X = {sp.Poly(diff_4, X).degree()}")

m4 = compute_multipliers(diff_4, "m=4 (LHS - RHS)", max_deg=30)
