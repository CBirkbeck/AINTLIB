#!/usr/bin/env python3
# T-W7.0c (lane P1): Bosma–Lenstra second addition law — derivation + Lean certificates.
#
# Pipeline:
#   A. Extract mathlib's projective formulas (negY,addZ,addX,negAddY,dblZ,dblX,negDblY) verbatim
#      from Projective/Formula.lean; build addY,dblY composites.  Validate: addZ_eq' reduction,
#      numeric agreement with an independent affine chord–tangent implementation.
#   B. My page transcription of B–L law (1); check == -(mathlib addX,addY,addZ) exactly.
#   C. Validate the p.236 rational functions f,g (addition) and s*(X/Z),s*(Y/Z) (subtraction).
#   D. DERIVE law (2) from the paper's anchor  law2_i = s*(Y/Z) · law1_i  by exact mod-p linear
#      algebra over the weight-graded (2,2)-monomial basis (transcription-free), lift to ℤ,
#      then exact-verify symbolically:  d³Z₁Z₂·law2_i ≡ N_Y·law1_i  (mod F₁,F₂).
#   E. Certificates (exact cofactors over ℤ[a₁..a₆]):
#        I1: F(addXYZ)        = A1·F1 + B1·F2        (equation_addXYZ — new even for mathlib)
#        I2: F(law2)          = A2·F1 + B2·F2        (equation_dblAddXYZ)
#        M*: 2×2 minors law1×law2 ≡ 0 mod (F1,F2)    (the two laws agree projectively)
#        D*: law2(P,P) − σ·dblXYZ(P) ≡ 0 mod F1      (diagonal = mathlib doubling; fixes sign σ)
#        O*: law2((0,Y1,0),Q) structure              (zero-section columns)
#   F. Numeric re-validation of every exported identity on fresh samples; Lean-syntax export.

import re, random, sys, json, os
from itertools import product

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
os.makedirs(OUT, exist_ok=True)
ML = "/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean"

# ---------------- polynomial arithmetic: dict{exps: int}, vars (X1,Y1,Z1,X2,Y2,Z2,a1,a2,a3,a4,a6)
NV = 11
NAMES = ["X1","Y1","Z1","X2","Y2","Z2","a1","a2","a3","a4","a6"]
ZERO_E = (0,)*NV

class P:
    __slots__ = ("d",)
    def __init__(self, d=None):
        self.d = d if d is not None else {}
    @staticmethod
    def const(c):
        return P({ZERO_E: c}) if c else P()
    @staticmethod
    def var(i):
        e = [0]*NV; e[i] = 1
        return P({tuple(e): 1})
    def __add__(self, o):
        if isinstance(o, int): o = P.const(o)
        d = dict(self.d)
        for e, c in o.d.items():
            n = d.get(e, 0) + c
            if n: d[e] = n
            elif e in d: del d[e]
        return P(d)
    __radd__ = __add__
    def __neg__(self):
        return P({e: -c for e, c in self.d.items()})
    def __sub__(self, o):
        if isinstance(o, int): o = P.const(o)
        return self + (-o)
    def __rsub__(self, o):
        return (-self) + o
    def __mul__(self, o):
        if isinstance(o, int):
            return P({e: c*o for e, c in self.d.items()}) if o else P()
        d = {}
        sd, od = self.d, o.d
        if len(sd) > len(od): sd, od = od, sd
        for e1, c1 in sd.items():
            for e2, c2 in od.items():
                e = tuple(map(sum, zip(e1, e2)))
                n = d.get(e, 0) + c1*c2
                if n: d[e] = n
                elif e in d: del d[e]
        return P(d)
    __rmul__ = __mul__
    def __pow__(self, n):
        r = P.const(1); b = self
        while n:
            if n & 1: r = r * b
            b = b * b; n >>= 1
        return r
    def __eq__(self, o):
        if isinstance(o, int): o = P.const(o)
        return self.d == o.d
    def is_zero(self):
        return not self.d
    def subst_diag(self):
        """P2 := P1  (X2->X1, Y2->Y1, Z2->Z1)"""
        d = {}
        for e, c in self.d.items():
            ne = (e[0]+e[3], e[1]+e[4], e[2]+e[5], 0, 0, 0) + e[6:]
            n = d.get(ne, 0) + c
            if n: d[ne] = n
            elif ne in d: del d[ne]
        return P(d)
    def subst_P_infty(self):
        """P1 := (0, Y1, 0): kill terms with X1- or Z1-exponent > 0."""
        return P({e: c for e, c in self.d.items() if e[0] == 0 and e[2] == 0})
    def subst_Q_infty(self):
        return P({e: c for e, c in self.d.items() if e[3] == 0 and e[5] == 0})
    def divide_exact(self, o):
        """exact division by a MONOMIAL poly o (single term) or general trial division; None if fails."""
        if len(o.d) == 1:
            (oe, oc), = o.d.items()
            d = {}
            for e, c in self.d.items():
                ne = tuple(a-b for a, b in zip(e, oe))
                if min(ne) < 0 or c % oc: return None
                d[ne] = c // oc
            return P(d)
        return None
    def evalm(self, vals, p):
        s = 0
        for e, c in self.d.items():
            t = c % p
            for i, ex in enumerate(e):
                if ex: t = t * pow(vals[i], ex, p) % p
            s = (s + t) % p
        return s
    def nterms(self):
        return len(self.d)
    def maxcoef(self):
        return max((abs(c) for c in self.d.values()), default=0)

X1,Y1,Z1,X2,Y2,Z2,a1,a2,a3,a4,a6 = (P.var(i) for i in range(NV))
NSD = {n: v for n, v in zip(NAMES, (X1,Y1,Z1,X2,Y2,Z2,a1,a2,a3,a4,a6))}

def F_of(X, Y, Z):
    return Y**2*Z + a1*X*Y*Z + a3*Y*Z**2 - (X**3 + a2*X**2*Z + a4*X*Z**2 + a6*Z**3)

F1 = F_of(X1, Y1, Z1)
F2 = F_of(X2, Y2, Z2)

# ---------------- reduction: f = q1*F1 + q2*F2 + r   (LT(F1) = -X1^3, LT(F2) = -X2^3, lex X1>X2)
F1_TAIL = F1 + X1**3   # F1 = -X1^3 + tail1
F2_TAIL = F2 + X2**3

def reduce2(f):
    q1, q2 = P(), P()
    work = P(dict(f.d))
    while True:
        off = {e: c for e, c in work.d.items() if e[0] >= 3}
        if off:
            qc = P({(e[0]-3,)+e[1:]: -c for e, c in off.items()})
            q1 = q1 + qc
            work = work - qc*F1
            continue
        off = {e: c for e, c in work.d.items() if e[3] >= 3}
        if off:
            qc = P({e[:3]+(e[3]-3,)+e[4:]: -c for e, c in off.items()})
            q2 = q2 + qc
            work = work - qc*F2
            continue
        break
    assert (q1*F1 + q2*F2 + work) == f, "reduction reconstruction failed"
    return q1, q2, work

def reduce1(f):
    """reduce mod F1 only (unary identities in P-variables)."""
    q1 = P()
    work = P(dict(f.d))
    while True:
        off = {e: c for e, c in work.d.items() if e[0] >= 3}
        if not off: break
        qc = P({(e[0]-3,)+e[1:]: -c for e, c in off.items()})
        q1 = q1 + qc
        work = work - qc*F1
    assert (q1*F1 + work) == f
    return q1, work

# ---------------- A. extract mathlib polynomials
def extract_def(src, name):
    m = re.search(r"def %s .*?:=\n(.*?)\n(?:\n|lemma|@\[|variable|end|private)" % name, src, re.S)
    assert m, "def %s not found" % name
    body = m.group(1)
    body = body.replace("W'.negY P", "PLACEHOLDER_NEGY_P").replace("W'.negY Q", "PLACEHOLDER_NEGY_Q")
    for u, r in (("W'.a₁","a1"),("W'.a₂","a2"),("W'.a₃","a3"),("W'.a₄","a4"),("W'.a₆","a6")):
        body = body.replace(u, r)
    for u, r in (("P x","X1"),("P y","Y1"),("P z","Z1"),("Q x","X2"),("Q y","Y2"),("Q z","Z2")):
        body = body.replace(u, r)
    body = body.replace("^", "**").replace("\n", " ")
    return body

src = open(ML).read()
mlpoly = {}
for name in ("negY", "addZ", "addX", "negAddY", "dblZ", "dblX", "negDblY"):
    body = extract_def(src, name)
    ns = dict(NSD)
    if "PLACEHOLDER_NEGY_P" in body or "PLACEHOLDER_NEGY_Q" in body:
        negY_P = eval(extract_def(src, "negY"), {}, dict(NSD))
        negY_Q = eval(extract_def(src, "negY").replace("X1","X2").replace("Y1","Y2").replace("Z1","Z2"), {}, dict(NSD))
        ns["PLACEHOLDER_NEGY_P"] = negY_P
        ns["PLACEHOLDER_NEGY_Q"] = negY_Q
    mlpoly[name] = eval(body, {}, ns)

negY_ml   = mlpoly["negY"]
addZ_ml   = mlpoly["addZ"]
addX_ml   = mlpoly["addX"]
negAddY_ml= mlpoly["negAddY"]
dblZ_ml   = mlpoly["dblZ"]
dblX_ml   = mlpoly["dblX"]
negDblY_ml= mlpoly["negDblY"]
# addY = negY ![addX, negAddY, addZ]  = -negAddY - a1*addX - a3*addZ ; likewise dblY
addY_ml = -negAddY_ml - a1*addX_ml - a3*addZ_ml
dblY_ml = -negDblY_ml - a1*dblX_ml - a3*dblZ_ml

def bideg_ok(f, dP, dQ):
    return all(e[0]+e[1]+e[2] == dP and e[3]+e[4]+e[5] == dQ for e in f.d)

assert bideg_ok(addX_ml,2,2) and bideg_ok(addY_ml,2,2) and bideg_ok(addZ_ml,2,2)
assert all(e[3]+e[4]+e[5] == 0 and e[0]+e[1]+e[2] == 4 for f in (dblX_ml,dblY_ml,dblZ_ml) for e in f.d)
print("A1. extraction ok: addX/addY/addZ bidegree (2,2); dblX/dblY/dblZ degree 4.")
print("    term counts:", {k: v.nterms() for k, v in
      dict(addX=addX_ml, addY=addY_ml, addZ=addZ_ml, dblX=dblX_ml, dblY=dblY_ml, dblZ=dblZ_ml).items()})

# known mathlib identity addZ_eq' : addZ*(Z1*Z2) - (X1*Z2-X2*Z1)^3 ∈ (F1,F2)
_,_,r = reduce2(addZ_ml*(Z1*Z2) - (X1*Z2 - X2*Z1)**3)
assert r.is_zero(), "addZ_eq' reduction failed -> extraction/reducer bug"
print("A2. reducer validated against mathlib addZ_eq'.")

# ---------------- numeric layer (mod prime)
PRIME = (1 << 61) - 1

def inv(x, p=PRIME): return pow(x % p, p - 2, p)

def affine_add(av, P1, P2, p=PRIME):
    """chord-tangent addition, points (x,y) with z=1, None for vertical; independent of B-L."""
    A1,A2,A3,A4,A6 = av
    x1,y1 = P1; x2,y2 = P2
    if x1 != x2:
        lam = (y1 - y2) * inv(x1 - x2, p) % p
    else:
        if (y1 + y2 + A1*x1 + A3) % p == 0: return None
        lam = (3*x1*x1 + 2*A2*x1 + A4 - A1*y1) * inv(2*y1 + A1*x1 + A3, p) % p
    x3 = (lam*lam + A1*lam - A2 - x1 - x2) % p
    y3 = (-(lam*(x3 - x1) + y1) - A1*x3 - A3) % p
    return (x3, y3)

def affine_neg(av, PT, p=PRIME):
    A1,A2,A3,A4,A6 = av
    x, y = PT
    return (x, (-y - A1*x - A3) % p)

def rand_sample(rng, p=PRIME):
    """random curve + two affine points on it (z1=z2=1), x1 != x2."""
    while True:
        A1,A2,A3 = (rng.randint(-5,5) for _ in range(3))
        x1,y1,x2,y2 = (rng.randint(-9,9) for _ in range(4))
        if x1 == x2: continue
        r1 = y1*y1 + A1*x1*y1 + A3*y1 - x1**3 - A2*x1*x1
        r2 = y2*y2 + A1*x2*y2 + A3*y2 - x2**3 - A2*x2*x2
        A4 = (r1 - r2) * inv(x1 - x2, p) % p
        A6 = (r1 - A4*x1) % p
        vals = [x1 % p, y1 % p, 1, x2 % p, y2 % p, 1, A1 % p, A2 % p, A3 % p, A4, A6]
        return vals

def curve_ok(vals, p=PRIME):
    return F1.evalm(vals, p) == 0 and F2.evalm(vals, p) == 0

rng = random.Random(20260707)
samples = [rand_sample(rng) for _ in range(40)]
assert all(curve_ok(v) for v in samples)

# mathlib addXYZ vs affine law (validates affine impl + extraction, secant branch)
for v in samples:
    av = v[6:]
    exp = affine_add(av, (v[0], v[1]), (v[3], v[4]))
    aZ = addZ_ml.evalm(v, PRIME)
    assert aZ != 0
    got = (addX_ml.evalm(v, PRIME) * inv(aZ) % PRIME, addY_ml.evalm(v, PRIME) * inv(aZ) % PRIME)
    assert got == exp, "mathlib addXYZ mismatch with affine law"
print("A3. mathlib addXYZ == affine chord law on", len(samples), "samples.")

# ---------------- B. my transcription of B-L law (1)  (p.236-237) ; expect == -(mathlib)
X3_1 = ((X1*Y2 - X2*Y1)*(Y1*Z2 + Y2*Z1) + (X1*Z2 - X2*Z1)*Y1*Y2
  + a1*X1*X2*(Y1*Z2 - Y2*Z1) + a1*(X1*Y2 - X2*Y1)*(X1*Z2 + X2*Z1)
  - a2*X1*X2*(X1*Z2 - X2*Z1) + a3*(X1*Y2 - X2*Y1)*Z1*Z2
  + a3*(X1*Z2 - X2*Z1)*(Y1*Z2 + Y2*Z1) - a4*(X1*Z2 + X2*Z1)*(X1*Z2 - X2*Z1)
  - 3*a6*(X1*Z2 - X2*Z1)*Z1*Z2)
Y3_1 = (-3*X1*X2*(X1*Y2 - X2*Y1) - Y1*Y2*(Y1*Z2 - Y2*Z1) - 2*a1*(X1*Z2 - X2*Z1)*Y1*Y2
  + (a1**2 + 3*a2)*X1*X2*(Y1*Z2 - Y2*Z1) - (a1**2 + a2)*(X1*Y2 + X2*Y1)*(X1*Z2 - X2*Z1)
  + (a1*a2 - 3*a3)*X1*X2*(X1*Z2 - X2*Z1) - (2*a1*a3 + a4)*(X1*Y2 - X2*Y1)*Z1*Z2
  + a4*(X1*Z2 + X2*Z1)*(Y1*Z2 - Y2*Z1) + (a1*a4 - a2*a3)*(X1*Z2 + X2*Z1)*(X1*Z2 - X2*Z1)
  + (a3**2 + 3*a6)*(Y1*Z2 - Y2*Z1)*Z1*Z2 + (3*a1*a6 - a3*a4)*(X1*Z2 - X2*Z1)*Z1*Z2)
Z3_1 = (3*X1*X2*(X1*Z2 - X2*Z1) - (Y1*Z2 + Y2*Z1)*(Y1*Z2 - Y2*Z1)
  + a1*(X1*Y2 - X2*Y1)*Z1*Z2 - a1*(X1*Z2 - X2*Z1)*(Y1*Z2 + Y2*Z1)
  + a2*(X1*Z2 + X2*Z1)*(X1*Z2 - X2*Z1) - a3*(Y1*Z2 - Y2*Z1)*Z1*Z2 + a4*(X1*Z2 - X2*Z1)*Z1*Z2)
ok1 = (X3_1 == -addX_ml, Y3_1 == -addY_ml, Z3_1 == -addZ_ml)
print("B.  law(1) transcription == -(mathlib addX,addY,addZ):", ok1)

# ---------------- C. rational functions of p.236 (validated numerically)
def ratfun_checks():
    good_add, good_sub = 0, 0
    for v in samples:
        av = v[6:]
        x1,y1,x2,y2 = v[0],v[1],v[3],v[4]
        d = (x1 - x2) % PRIME
        lam = (y1 - y2)*inv(d) % PRIME
        nu  = -(y1*x2 - y2*x1)*inv(d) % PRIME
        f   = (lam*lam + av[0]*lam - (x1 + x2) - av[1]) % PRIME
        g   = (-(lam + av[0])*f - nu - av[2]) % PRIME
        exp = affine_add(av, (x1,y1), (x2,y2))
        good_add += (f, g) == exp
        kap = (y1 + y2 + av[0]*x2 + av[2])*inv(d) % PRIME
        mu  = -(y1*x2 + y2*x1 + av[0]*x1*x2 + av[2]*x1)*inv(d) % PRIME
        sX  = (kap*kap + av[0]*kap - (x1 + x2) - av[1]) % PRIME
        sY  = (-(kap + av[0])*sX - mu - av[2]) % PRIME
        expS = affine_add(av, (x1,y1), affine_neg(av,(x2,y2)))
        good_sub += (sX, sY) == expS
    return good_add, good_sub

ga, gs = ratfun_checks()
print("C.  f,g (addition) match: %d/%d ; s*(X/Z),s*(Y/Z) (subtraction) match: %d/%d"
      % (ga, len(samples), gs, len(samples)))
assert ga == len(samples) and gs == len(samples), "p.236 rational-function reading wrong - STOP"

# ---------------- D. derive law (2):  law2_i = s*(Y/Z) * law1_i   as (2,2)-forms
WEIGHTS = (2, 3, 0, 2, 3, 0, 1, 2, 3, 4, 6)   # X,Y,Z weights + a-weights
QUADS = [(2,0,0),(1,1,0),(0,2,0),(1,0,1),(0,1,1),(0,0,2)]  # X^2,XY,Y^2,XZ,YZ,Z^2

def a_monos(w):
    out = []
    for e6 in range(w//6 + 1):
        for e4 in range((w - 6*e6)//4 + 1):
            for e3 in range((w - 6*e6 - 4*e4)//3 + 1):
                for e2 in range((w - 6*e6 - 4*e4 - 3*e3)//2 + 1):
                    e1 = w - 6*e6 - 4*e4 - 3*e3 - 2*e2
                    out.append((e1, e2, e3, e4, e6))
    return out

def basis_for_weight(w):
    out = []
    for q1 in QUADS:
        for q2 in QUADS:
            wm = q1[0]*2 + q1[1]*3 + q2[0]*2 + q2[1]*3
            if wm > w: continue
            for am in a_monos(w - wm):
                out.append(q1 + q2 + am)
    return out

def solve_law2(coord_idx, weight, law1_polys, nsamp_extra=120):
    basis = basis_for_weight(weight)
    n = len(basis)
    rows, rhs = [], []
    srng = random.Random(991000 + coord_idx)
    needed = n + 60
    tries = 0
    mat = []   # eliminated rows: list of (pivot_col, row, r)
    piv = {}
    def add_row(row, r):
        for pc in sorted(piv):
            if row[pc]:
                f = row[pc] * inv(mat[piv[pc]][1][pc]) % PRIME
                prow = mat[piv[pc]][1]; pr = mat[piv[pc]][2]
                row = [(x - f*y) % PRIME for x, y in zip(row, prow)]
                r = (r - f*pr) % PRIME
        nz = next((i for i, x in enumerate(row) if x), None)
        if nz is None:
            assert r == 0, "inconsistent system - anchor identity violated"
            return False
        piv[nz] = len(mat)
        mat.append((nz, row, r))
        return True
    got = 0
    while got < n:
        tries += 1
        assert tries < 20*n, "cannot reach full rank"
        v = rand_sample(srng)
        d = (v[0]*v[5] - v[3]*v[2]) % PRIME
        if d == 0: continue
        kap = (v[1]*v[5] + v[4]*v[2] + v[6]*v[3]*v[2] + v[8]*v[2]*v[5]) * inv(d) % PRIME
        mu  = -(v[1]*v[3] + v[4]*v[0] + v[6]*v[0]*v[3] + v[8]*v[0]*v[5]) * inv(d) % PRIME
        sX  = (kap*kap + v[6]*kap - (v[0]*v[5] + v[3]*v[2])*inv(v[2]*v[5]) - v[7]) % PRIME
        sY  = (-(kap + v[6])*sX - mu - v[8]) % PRIME
        lhs = sY * law1_polys[coord_idx].evalm(v, PRIME) % PRIME
        mvals = []
        for b in basis:
            t = 1
            e = (b[0], b[1], 2-b[0]-b[1], b[2], b[3], 2-b[2]-b[3], b[4], b[5], b[6], b[7], b[8])
            for i, ex in enumerate(e):
                if ex: t = t * pow(v[i], ex, PRIME) % PRIME
            mvals.append(t)
        if add_row(mvals, lhs):
            got += 1
    # back-substitute
    sol = [0]*n
    for pc in sorted(piv, reverse=True):
        _, row, r = mat[piv[pc]]
        s = r
        for j in range(pc+1, n):
            if row[j]: s = (s - row[j]*sol[j]) % PRIME
        sol[pc] = s * inv(row[pc]) % PRIME
    # lift symmetric
    out = {}
    for b, c in zip(basis, sol):
        if c:
            cc = c if c <= PRIME//2 else c - PRIME
            e = (b[0], b[1], 2-b[0]-b[1], b[2], b[3], 2-b[2]-b[3], b[4], b[5], b[6], b[7], b[8])
            out[e] = cc
    return P(out)

# NOTE: basis entries b: (q1x,q1y, q2x,q2y, a1,a2,a3,a4,a6) -- 3+3 packed as pairs; fix packing:
def basis_for_weight(w):  # noqa: F811  (redefined cleanly)
    out = []
    for q1 in QUADS:
        for q2 in QUADS:
            wm = q1[0]*2 + q1[1]*3 + q2[0]*2 + q2[1]*3
            if wm > w: continue
            for am in a_monos(w - wm):
                out.append((q1[0], q1[1], q2[0], q2[1]) + am)
    return out

law1 = (X3_1, Y3_1, Z3_1)
law2 = []
for i, w in enumerate((11, 12, 9)):
    L = solve_law2(i, w, law1)
    law2.append(L)
    print("D%d. derived law2[%d]: %d terms, max |coeff| = %d" % (i, i, L.nterms(), L.maxcoef()))
L2X, L2Y, L2Z = law2
assert bideg_ok(L2X,2,2) and bideg_ok(L2Y,2,2) and bideg_ok(L2Z,2,2)

# exact symbolic verification of the anchor:  d^3*Z1*Z2*law2_i ≡ N_Y*law1_i (mod F1,F2)
d_ = X1*Z2 - X2*Z1
kapN = Y1*Z2 + Y2*Z1 + a1*X2*Z1 + a3*Z1*Z2
muN  = -(Y1*X2 + Y2*X1 + a1*X1*X2 + a3*X1*Z2)
NX = kapN**2*Z1*Z2 + a1*kapN*d_*Z1*Z2 - (X1*Z2 + X2*Z1)*d_**2 - a2*d_**2*Z1*Z2
NY = -(kapN + a1*d_)*NX - muN*d_**2*Z1*Z2 - a3*d_**3*Z1*Z2
for i, (L, nm) in enumerate(zip(law2, "XYZ")):
    _,_,r = reduce2(d_**3*(Z1*Z2)*L - NY*law1[i])
    assert r.is_zero(), "anchor identity FAILS for coordinate %s" % nm
print("D3. anchor  d³Z₁Z₂·law2 ≡ N_Y·law1  (mod F₁,F₂) verified exactly — law2 is certified.")

json.dump({nm: {" ".join(map(str,e)): c for e, c in L.d.items()} for nm, L in zip("XYZ", law2)},
          open(os.path.join(OUT, "law2_derived.json"), "w"))

# ---------------- my (uncertain) page transcription of law (2), for the fidelity report
X3_2t = (Y1*Y2*(X1*Y2 + X2*Y1) + a1*(2*X1*Y2 + X2*Y1)*X2*Y1 + a1**2*X1*X2**2*Y1
  - a2*X1*X2*(X1*Y2 + X2*Y1) - a1*a2*X1**2*X2**2 + a3*X2*Y1*(Y1*Z2 + 2*Y2*Z1)
  + a1*a3*X1*X2*(Y1*Z2 - Y2*Z1) - a1*a3*(X1*Y2 + X2*Y1)*(X1*Z2 - X2*Z1)
  - a4*X1*X2*(Y1*Z2 + Y2*Z1) - a4*(X1*Y2 + X2*Y1)*(X1*Z2 + X2*Z1)
  - a1**2*a3*X1**2*X2*Z2 - a1*a4*X1*X2*(2*X1*Z2 + X2*Z1)
  - a2*a3*X1*X2**2*Z1 - a3**2*X1*Z2*(2*Y2*Z1 + Y1*Z2)
  - 3*a6*(X1*Y2 + X2*Y1)*Z1*Z2
  - 3*a6*(X1*Z2 + X2*Z1)*(Y1*Z2 + Y2*Z1) - a1*a3**2*X1*Z2*(X1*Z2 + 2*X2*Z1)
  - 3*a1*a6*X1*Z2*(X1*Z2 + 2*X2*Z1) + a3*a4*(X1*Z2 - 2*X2*Z1)*X2*Z1
  - (a1**2*a6 - a1*a3*a4 + a2*a3**2 + 4*a2*a6 - a4**2)*(Y1*Z2 + Y2*Z1)*Z1*Z2
  - (a1**3*a6 - a1**2*a3*a4 + a1*a2*a3**2 + 4*a1*a2*a6 - a1*a4**2)*X1*Z1*Z2**2
  - a3**3*(X1*Z2 + X2*Z1)*Z1*Z2 - 3*a3*a6*(X1*Z2 + 2*X2*Z1)*Z1*Z2
  - (a1**2*a3*a6 - a1*a3**2*a4 + a2*a3**3 + 4*a2*a3*a6 - a3*a4**2)*Z1**2*Z2**2)
diffX = X3_2t - L2X
print("E0. transcription check X₃⁽²⁾: %s (%d differing monomials)"
      % ("EXACT" if diffX.is_zero() else "differs", diffX.nterms()))

# ---------------- E. certificates
def export_poly(f, fname):
    open(os.path.join(OUT, fname), "w").write(lean_poly(f) + "\n")

SUB = {"a1":"W'.a₁","a2":"W'.a₂","a3":"W'.a₃","a4":"W'.a₄","a6":"W'.a₆"}
VARN = ["P x","P y","P z","Q x","Q y","Q z"]

def lean_mono(e, c):
    parts = []
    for i in range(6, 11):
        if e[i]:
            nm = SUB[NAMES[i]]
            parts.append(nm if e[i] == 1 else "%s ^ %d" % (nm, e[i]))
    for i in range(6):
        if e[i]:
            nm = VARN[i]
            parts.append(nm if e[i] == 1 else "%s ^ %d" % (nm, e[i]))
    body = " * ".join(parts) if parts else "1"
    ac = abs(c)
    if ac != 1 or not parts:
        body = "%d * %s" % (ac, body) if parts else "%d" % ac
    return body

def lean_poly(f, width=94, indent="      "):
    if f.is_zero(): return indent + "0"
    items = sorted(f.d.items(), key=lambda kv: tuple(-x for x in kv[0]))
    s = ""
    first = True
    for e, c in items:
        t = lean_mono(e, c)
        s += (("-" if c < 0 else "") if first else (" - " if c < 0 else " + ")) + t
        first = False
    # wrap
    words = s.split(" ")
    lines, cur = [], indent
    for wd in words:
        if len(cur) + len(wd) + 1 > width and cur.strip():
            lines.append(cur); cur = indent + "  " + wd
        else:
            cur += ("" if cur.endswith(" ") or cur == indent else " ") + wd
    lines.append(cur)
    return "\n".join(lines)

certs = {}

# I1: F(addXYZ_ml) = A1*F1 + B1*F2
q1, q2, r = reduce2(F_of(addX_ml, addY_ml, addZ_ml))
assert r.is_zero(), "law1 on-curve FAILS"
certs["I1"] = (q1, q2)
print("E1. I1  F(addXYZ) ∈ (F₁,F₂): cofactors %d / %d terms, max|c| %d/%d"
      % (q1.nterms(), q2.nterms(), q1.maxcoef(), q2.maxcoef()))

# I2: F(law2) = A2*F1 + B2*F2
q1, q2, r = reduce2(F_of(L2X, L2Y, L2Z))
assert r.is_zero(), "law2 on-curve FAILS"
certs["I2"] = (q1, q2)
print("E2. I2  F(law2) ∈ (F₁,F₂): cofactors %d / %d terms, max|c| %d/%d"
      % (q1.nterms(), q2.nterms(), q1.maxcoef(), q2.maxcoef()))

# minors against mathlib law1 (use mathlib sign: addXYZ)
for nm, (u, v_) in {"MXY": (addX_ml*L2Y - addY_ml*L2X, None),
                    "MXZ": (addX_ml*L2Z - addZ_ml*L2X, None),
                    "MYZ": (addY_ml*L2Z - addZ_ml*L2Y, None)}.items():
    q1, q2, r = reduce2(u)
    assert r.is_zero(), "minor %s FAILS" % nm
    certs[nm] = (q1, q2)
    print("E3. %s ≡ 0 mod (F₁,F₂): cofactors %d / %d terms" % (nm, q1.nterms(), q2.nterms()))

# diagonal vs mathlib dblXYZ: find sign
for sgn in (1, -1):
    rs = []
    for L, D in ((L2X, dblX_ml), (L2Y, dblY_ml), (L2Z, dblZ_ml)):
        q, r = reduce1(L.subst_diag() - sgn*D)
        rs.append((q, r))
    if all(r.is_zero() for _, r in rs):
        DIAG_SIGN = sgn
        certs["DX"], certs["DY"], certs["DZ"] = ((q, None) for q, _ in rs)
        break
else:
    DIAG_SIGN = None
print("E4. diagonal: law2(P,P) ≡ %s·dblXYZ(P) mod F₁ ; cofactor terms: %s"
      % (DIAG_SIGN, [certs[k][0].nterms() for k in ("DX","DY","DZ")] if DIAG_SIGN else "NONE"))

# O-columns: law2((0,Y1,0), Q) and law2(P, (0,Y2,0))
for nm, L in (("X", L2X), ("Y", L2Y), ("Z", L2Z)):
    lft = L.subst_P_infty()
    rgt = L.subst_Q_infty()
    g1 = lft.divide_exact(Y1**2)
    g2 = rgt.divide_exact(Y2**2)
    print("E5. law2_%s((0,Y₁,0),Q) = Y₁² * [%d terms] ; law2_%s(P,(0,Y₂,0)) = Y₂² * [%d terms]"
          % (nm, g1.nterms() if g1 else -1, nm, g2.nterms() if g2 else -1))
    certs["OL"+nm] = (lft, rgt)

# is law2 symmetric?
print("E6. law2 symmetric in (P,Q)?",
      all(L == P({(e[3],e[4],e[5],e[0],e[1],e[2])+e[6:]: c for e, c in L.d.items()}) for L in law2))

# smul degrees (structural, for the record): each term (2,2) => (u v)^2 scaling. checked above.

# ---------------- F. numeric re-validation of every certificate on fresh samples
frng = random.Random(777)
fs = [rand_sample(frng) for _ in range(25)]
def val_zero(f):
    return all(f.evalm(v, PRIME) == 0 for v in fs)
okF = True
okF &= val_zero(F_of(addX_ml, addY_ml, addZ_ml) - (certs["I1"][0]*F1 + certs["I1"][1]*F2))
okF &= val_zero(F_of(L2X, L2Y, L2Z) - (certs["I2"][0]*F1 + certs["I2"][1]*F2))
print("F.  fresh-sample re-validation:", okF)

# law2 computes P+Q numerically including the diagonal (independent end-to-end check)
good = 0
for v in fs:
    av = v[6:]
    exp = affine_add(av, (v[0], v[1]), (v[3], v[4]))
    z = L2Z.evalm(v, PRIME)
    if z == 0: continue
    got = (L2X.evalm(v, PRIME)*inv(z) % PRIME, L2Y.evalm(v, PRIME)*inv(z) % PRIME)
    good += got == exp
print("F2. law2 == P+Q on generic samples:", good, "/", len(fs))
gooD = 0
for v in fs:
    av = v[6:]
    vd = v[:3] + v[:3] + av  # P2 := P1
    exp = affine_add(av, (v[0], v[1]), (v[0], v[1]))
    z = L2Z.evalm(vd, PRIME)
    if exp is None:
        gooD += z == 0
        continue
    if z == 0: continue
    got = (L2X.evalm(vd, PRIME)*inv(z) % PRIME, L2Y.evalm(vd, PRIME)*inv(z) % PRIME)
    gooD += got == exp
print("F3. law2 doubles correctly on the diagonal:", gooD, "/", len(fs))

# ---------------- exports
export_poly(L2X, "dblAddX.txt"); export_poly(L2Y, "dblAddY.txt"); export_poly(L2Z, "dblAddZ.txt")
for k, (q1, q2) in certs.items():
    if q1 is not None: export_poly(q1, "cof_%s_1.txt" % k)
    if q2 is not None: export_poly(q2, "cof_%s_2.txt" % k)
print("G.  exports written to", OUT)
