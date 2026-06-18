"""Generate the m=4 multiplier polynomial in Lean syntax."""
import sympy as sp
import re

X, b2, b4, b6, b8 = sp.symbols('X b2 b4 b6 b8')

Psi_2_sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
Psi_3    = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
preP4    = (2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
           + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2))

diff_4 = sp.expand((preP4**2 * Psi_2_sq)**2
                   - (sp.diff(Psi_3 * (preP4 * Psi_2_sq**2 - Psi_3**3), X) * (preP4**2 * Psi_2_sq)
                      - Psi_3 * (preP4 * Psi_2_sq**2 - Psi_3**3) * sp.diff(preP4**2 * Psi_2_sq, X))
                   - 4*(Psi_3**2 * preP4 * (Psi_3 * ((preP4 * Psi_2_sq**2 - Psi_3**3) - preP4**2))
                        - preP4 * (preP4 * Psi_2_sq**2 - Psi_3**3)**2))

b_rel = 4*b8 - b2*b6 + b4**2

def compute(diff_poly, max_deg):
    mults = {}
    for i in range(max_deg + 1):
        c = sp.expand(diff_poly.coeff(X, i))
        if c == 0:
            mults[i] = sp.Integer(0)
            continue
        q = sp.Integer(0)
        rem = c
        while sp.Poly(rem, b8).degree() >= 1:
            rp = sp.Poly(rem, b8)
            lc, d = rp.LC(), rp.degree()
            term = sp.nsimplify(lc / 4, rational=True) * b8**(d-1)
            q = q + term
            rem = sp.expand(rem - term * b_rel)
        assert sp.simplify(rem) == 0
        q_expr = sp.expand(q)
        assert sp.simplify(sp.expand(q_expr * b_rel) - c) == 0
        mults[i] = q_expr
    return mults


m4 = compute(diff_4, 30)


def to_lean(expr):
    if expr == 0:
        return "0"
    # Expand into a sum of monomials for easier Lean formatting.
    expr_expanded = sp.expand(expr)
    # Build Lean expression monomial by monomial.
    terms = sp.Add.make_args(expr_expanded)
    parts = []
    for t in terms:
        s = str(t)
        s = re.sub(r'b2\*\*([0-9]+)', lambda m: f'W.b₂ ^ {m.group(1)}', s)
        s = re.sub(r'b4\*\*([0-9]+)', lambda m: f'W.b₄ ^ {m.group(1)}', s)
        s = re.sub(r'b6\*\*([0-9]+)', lambda m: f'W.b₆ ^ {m.group(1)}', s)
        s = re.sub(r'b8\*\*([0-9]+)', lambda m: f'W.b₈ ^ {m.group(1)}', s)
        s = s.replace('b2', 'W.b₂').replace('b4', 'W.b₄').replace('b6', 'W.b₆').replace('b8', 'W.b₈')
        s = s.replace('**', '^')
        parts.append(s)
    # Combine with plus/minus
    result = parts[0]
    for p in parts[1:]:
        if p.startswith('-'):
            result += ' + (' + p + ')'
        else:
            result += ' + ' + p
    return result


# Print each M_i as a Lean Polynomial.C(...) * Polynomial.X^i term.
# Use Polynomial.C wrapping so the result is in R[X].
print("-- m=4 multiplier polynomial")
print("-- M(X) = sum_i (M_i * X^i) where each M_i is in R (the b's live in R)")
print()
print("-- As a Lean expression (to be multiplied by h_P: (4:R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄^2):")
print()
print("(")
nonzero_is = sorted(i for i, m in m4.items() if m != 0)
for idx, i in enumerate(nonzero_is):
    m = m4[i]
    lean_m = to_lean(m)
    # Wrap in Polynomial.C and multiply by X^i
    if i == 0:
        term = f"Polynomial.C ({lean_m})"
    elif i == 1:
        term = f"Polynomial.C ({lean_m}) * Polynomial.X"
    else:
        term = f"Polynomial.C ({lean_m}) * Polynomial.X ^ {i}"
    prefix = "    " if idx == 0 else "  + "
    print(f"{prefix}{term}")
print(")")

# Find all numeric constants in the multiplier to know which CNorm lemmas to include
import re as re2
all_nums = set()
for i, m in m4.items():
    if m != 0:
        # Find all integer literals
        nums = re2.findall(r'(\d+)', str(m))
        all_nums.update(int(n) for n in nums)
print()
print(f"-- Numeric constants appearing in m=4 multiplier: {sorted(all_nums)}")
