"""
Verify ω₂ basis decomposition in char 2:
ω₂ = C(A) + C(B) · Y in K[X][Y] modulo W.polynomial.

Where:
- A(X) = (X² + a₁²X + a₁·a₃ + a₄)·Ψ₃ + (a₁X + a₃)⁴
- B(X) = a₁·Ψ₃ + (a₁X + a₃)³

mathlib's ω 2 def (after redInvarDenom_two = 1, complEDSAux₂_two = 0):
ω 2 = (CC a₁ · polynomialY - polynomialX) · CΨ₃
      + 4 · polynomial · (2 · polynomial + CΨ₂Sq)
      - 0
      + negPolynomial · ψ₂³

In char 2: 4=0, 2=0, so middle term vanishes.
ω 2 (char 2) = (a₁ · polynomialY - polynomialX) · CΨ₃ + negPolynomial · ψ₂³

polynomialY (char 2) = a₁X + a₃ (constant in Y, since 2Y=0)
polynomialX (char 2) = a₁Y - X² - a₄ (linear in Y)
negPolynomial (char 2) = Y + a₁X + a₃ (linear in Y)
ψ₂ (char 2) = a₁X + a₃ (constant in Y)

Compute: ω 2 = ?
"""

from sympy import symbols, expand, Poly, simplify

X, Y, a1, a2, a3, a4, a6 = symbols('X Y a1 a2 a3 a4 a6')

# Char 2 specialisations
b2 = a1**2  # b₂ = a₁²
b4 = a1*a3  # b₄ = a₁·a₃
b6 = a3**2  # b₆ = a₃²
b8 = a1**2 * a6 + a1*a3*a4 + a2*a3**2 + a4**2  # b₈ char-2 form (4·a₂·a₆ = 0, -=+)

# Ψ₃ (char 2): X⁴ + b₂X³ + b₄X² + b₆X + b₈
Psi3 = X**4 + b2*X**3 + b4*X**2 + b6*X + b8

# polynomial (char 2): Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)
W_poly = Y**2 + a1*X*Y + a3*Y - (X**3 + a2*X**2 + a4*X + a6)

# polynomialY (char 2) = 2Y + a₁X + a₃ → a₁X + a₃
polyY = a1*X + a3

# polynomialX (char 2) = a₁Y - 3X² - 2a₂X - a₄ → a₁Y - X² - a₄ (3=1, 2=0)
polyX_p = a1*Y - X**2 - a4

# negPolynomial (char 2) = -Y - a₁X - a₃ → Y + a₁X + a₃ (-=+)
negPoly = Y + a1*X + a3

# ψ₂ (char 2) = polynomialY = a₁X + a₃
psi2 = polyY

# Compute ω 2 (char 2)
omega2 = (a1 * polyY - polyX_p) * Psi3 + negPoly * psi2**3
omega2_exp = expand(omega2)
print("=== ω₂ in char 2 (expanded) ===")
poly_y = Poly(omega2_exp, Y)
for power, coeff in zip(reversed(range(poly_y.degree() + 1)), poly_y.all_coeffs()):
    if coeff != 0:
        print(f"  Y^{power}: {expand(coeff)}")

# Reduce mod 2 (treat all integer coefficients mod 2)
def reduce_char2(expr):
    e = expand(expr)
    if e == 0:
        return 0
    p = Poly(e, X)
    new_terms = 0
    for power, c in zip(reversed(range(p.degree() + 1)), p.all_coeffs()):
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
        new_terms += new_c * X**power
    return expand(new_terms)

# After mod 2:
print("\n=== ω₂ in char 2 — Y-coefficients reduced mod 2 ===")
for power, coeff in zip(reversed(range(poly_y.degree() + 1)), poly_y.all_coeffs()):
    c_red = reduce_char2(coeff)
    if c_red != 0:
        print(f"  Y^{power}: {c_red}")

# Compare to A and B from session 9
# A(X) = (X² + a₁²X + a₁·a₃ + a₄)·Ψ₃ + (a₁X + a₃)⁴
A = (X**2 + a1**2 * X + a1*a3 + a4) * Psi3 + (a1*X + a3)**4
A_red = reduce_char2(expand(A))

# B(X) = a₁·Ψ₃ + (a₁X + a₃)³
B = a1 * Psi3 + (a1*X + a3)**3
B_red = reduce_char2(expand(B))

print("\n=== Expected ===")
print(f"A_char_two (Y^0) = {A_red}")
print(f"B_char_two (Y^1) = {B_red}")

# Now verify: in char 2, after reducing mod W.polynomial (Y² → cubic_x - a₁xy - a₃y),
# ω₂'s Y² term should reduce away. But we may need to be careful — ω₂ might contain
# Y² terms that need substitution.

# Let me check ω₂'s degree in Y from the print above first.
