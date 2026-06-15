"""Just verify Φ_4 in char 2."""
import sympy as sp
X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

Psi_2_sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi_3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
preP4 = (2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
         + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

# preΨ(5) = preΨ_odd(m=2): preΨ(4)·preΨ(2)³·Ψ_2² - preΨ(1)·preΨ(3)³·1 (m=2 even)
preP5 = preP4 * 1 * Psi_2_sq**2 - 1 * Psi_3**3 * 1

# Φ_4 = X · preΨ(4)² · Ψ_2² - preΨ(5) · preΨ(3) · 1 (n=4 even, χ=1, χ̃=Ψ_2²)
ΨSq_4 = preP4**2 * Psi_2_sq
Phi_4 = X * ΨSq_4 - preP5 * Psi_3 * 1

# Reduce in char 2 with b2*b6 = b4²
def reduce_b2(c):
    c2 = sp.expand(c)
    for _ in range(15):
        new = sp.expand(c2.subs(b2*b6, b4**2))
        if new == c2: break
        c2 = new
    return c2

print("=== Φ_4: q=4 in char p=2 ===")
print(f"  Φ_4 has degree in X: {sp.Poly(Phi_4, X).degree()}")

bad = []
n = 0
for i, c in enumerate(sp.Poly(Phi_4, X).all_coeffs()[::-1]):
    c_red = reduce_b2(c)
    if c_red == 0: continue
    # Mod 2 by checking each monomial
    try:
        cp = sp.Poly(c_red, b2, b4, b6, b8)
        terms = [(m, int(co) % 2) for m, co in cp.terms() if int(co) % 2 != 0]
    except:
        terms = [((), int(c_red) % 2)] if int(c_red) % 2 != 0 else []
    if not terms: continue
    n += 1
    if i % 4 != 0:
        bad.append(i)
print(f"  Total nonzero (after b-rel + mod 2): {n}")
print(f"  Non-4-divisible exponents: {bad}")
if not bad:
    print("  ✓ Φ_4 IS in F_2[X^4] (after b-rel)")
else:
    print(f"  ✗ Φ_4 has NONZERO coeff at non-4-divisible exponents: {bad}")
