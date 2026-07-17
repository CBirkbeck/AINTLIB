# [hArb] hB-redundancy certificate (STREAM-OMEGA 2026-07-17, board v10.310).
# On a flex-NF chart (a2=a4=a6=0) with Q=(p,q) marked, modulo
#   R1 := q^2 + a1*p*q + a3*q - p^3          (curve at Q)
#   R2 := 3p^3 + a1^2 p^2 + 3 a1 a3 p + 3 a3^2   (the 3-torsion cubic)
# the B-locus quantity  B := a1^3 p + a1^2 a3 + a1^2 q + 6 a1 p^2 + 3 a3 p + 6 p q
# satisfies the INTEGRAL identity  B*C = 27*a3^8*(a1^3-27a3)^2 + lam1*R1 + lam2*R2
# with C, lam1, lam2 in ZZ[a1,a3,p,q]:
#   C = a3^4*(a1^3-27a3) * C0,
#   C0 = -a1^7 q - 3 a1^5 a3 p + 6 a1^5 p q + 45 a1^4 a3 q - 9 a1^3 a3 p^2
#        + 27 a1^3 p^2 q - 27 a1^2 a3 p q - 135 a1 a3^3 - 270 a1 a3^2 q
#        - 81 a3^2 p^2 - 162 a3 p^2 q.
# Since 27*a3^8*(a1^3-27a3)^2 = 27 * a3^2 * Delta^2 (Delta = a3^3(a1^3-27a3) on flex NF)
# is a UNIT whenever 3, a3, Delta are units, B is a unit on EVERY genuine chart:
# the hB hypothesis of isE3Form_of_threeTorsion / isE3Chart is REDUNDANT.
# Run this script to regenerate lam1, lam2 exactly (sympy, deterministic).
import sympy as sp
a1,a3,p,q = sp.symbols('a1 a3 p q')
def red(e):
    e = sp.expand(e)
    while True:
        if sp.degree(e, q) >= 2:
            e = sp.expand(e.subs(q**2, p**3 - a1*p*q - a3*q)); continue
        if sp.degree(e, p) >= 3:
            e = sp.expand(e.subs(p**5, p**2*(-(a1**2*p**2 + 3*a1*a3*p + 3*a3**2)/3)))
            e = sp.expand(e.subs(p**4, p*(-(a1**2*p**2 + 3*a1*a3*p + 3*a3**2)/3)))
            e = sp.expand(e.subs(p**3, -(a1**2*p**2 + 3*a1*a3*p + 3*a3**2)/3))
            continue
        return e
B  = a1**3*p + a1**2*a3 + a1**2*q + 6*a1*p**2 + 3*a3*p + 6*p*q
basis=[(0,0),(1,0),(2,0),(0,1),(1,1),(2,1)]
M=sp.zeros(6,6)
for j,(bp,bq) in enumerate(basis):
    pol = sp.Poly(red(B * p**bp * q**bq), p, q)
    for i,(ip,iq) in enumerate(basis):
        co = pol.coeff_monomial(p**ip * q**iq)
        M[i,j] = co if co is not None else 0
adjM = M.adjugate()
C = sp.expand(sum(adjM[j,0] * p**basis[j][0] * q**basis[j][1] for j in range(6)))
det = 27*a3**8*(a1**3-27*a3)**2
R1 = q**2 + a1*p*q + a3*q - p**3
R2 = 3*p**3 + a1**2*p**2 + 3*a1*a3*p + 3*a3**2
E = sp.expand(B*C - det)
lam1, rem1 = sp.div(E, R1, q)
lam2, rem2 = sp.div(sp.expand(rem1), R2, p)
assert sp.expand(E - lam1*R1 - lam2*R2) == 0 and sp.expand(rem2) == 0
print("lam1 =", sp.expand(lam1)); print("lam2 =", sp.expand(lam2))
