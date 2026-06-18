# T-PIC-A-002: `σ` vanishes on principal divisors

**Status**: DONE (`projectiveDivisorSum_eq_zero_of_principal` in
`HasseWeil/Curves/Miller.lean`, axiom-clean — direct corollary of
`afInputs_unconditional.h_van`)
**Silverman**: III.3.5 (Corollary): every principal divisor sums to O.
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~80
**Difficulty**: easy-medium
**Phase**: A

## Depends on
- T-PIC-A-001 (`projectiveDivisorSum`)
- T-II-3-005 (DONE) — `divisorOf : FunctionField → Divisor`
- T-II-3-006 (DONE) — `IsPrincipal` predicate

## Blocks
- T-PIC-A-003 (descent to Pic⁰)

## Statement

The sum-of-points map vanishes on principal divisors:

```lean
theorem projectiveDivisorSum_principal
    {f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} (hf : f ≠ 0) :
    projectiveDivisorSum W ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) = 0
```

This is **Silverman III.3.5**: `Σ nP·P = O` for any principal divisor on
an elliptic curve.

## Mathlib check
Not in mathlib.

## Naming
`projectiveDivisorSum_principal` (snake_case).

## Generality
Same as T-PIC-A-001 (`[W.IsElliptic]`, no `IsAlgClosed`).

## Proof approach

**Silverman's argument** (page 64): every principal divisor of degree 0
is `div(f)` for some `f ∈ K(E)*`. The corollary II.3.5 says this implies
`Σ nP · P = O` in `E`.

**Project's path** to this:
1. T-II-3-009 (worker-K, CHECKED-OUT) provides
   `deg(projectiveDivisorOf f) = 0` — needed to even talk about
   `principal ⊆ Div⁰`.
2. The actual sum-vanishing uses Silverman III.3.4(e): the geometric
   group law on E coincides with the Pic⁰-induced one. So the
   sum-of-zeros-and-poles equals `O` for any principal divisor.

This last step has a chicken-and-egg flavor with III.3.4. The clean proof
uses **lines/sections of E in P²**: for a function `f = h₁/h₂` with `h_i`
homogeneous polynomials, `div(h_i)` is the divisor of intersection of E
with the curve `h_i = 0`. By Bezout-type reasoning + collinearity (three
collinear points on E sum to O), the sum of zeros minus sum of poles is O.

**Recommended**: prove for `f` of the special form `f = (line through P,Q,R)/(line through O,O,O)`-style first (this is what Silverman uses in
the proof of III.3.4(e), "Then from the definition of addition on E").
Then extend to general principal divisors via factorization.

**Alternative**: take this AS the consequence of III.3.4(e) and only
prove it after we have III.3.4. Then T-PIC-A-002 becomes a corollary of
T-PIC-F-002.

**Decision**: keep this as A-002 with the direct lines-in-P² proof. The
proof needs ~80 lines and might leverage `HasseWeil/EC/GenericPoint*.lean`
(see existing file structure).

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.projectiveDivisorSum_principal
```
reports only standard axioms. No new sorries.

## Progress log

### 2026-04-27 — analysis session

Investigated tractability of this ticket in a single session. **Conclusion:
not closeable without substantial new geometric infrastructure.**

**Multiplicative reduction shipped (PicZero.lean):**
- `projectiveDivisorSum_projectiveDivisorOf_one` — σ(div 1) = 0 (trivial).
- `projectiveDivisorSum_projectiveDivisorOf_mul` — σ(div (f·g)) = σ(div f) + σ(div g).
- `projectiveDivisorSum_projectiveDivisorOf_inv` — σ(div f⁻¹) = -σ(div f).

These collectively show σ ∘ projectiveDivisorOf is an **AddMonoidHom-like
structure** on `K(E)*` (multiplicative-to-additive). Hence to prove the
universal vanishing, it suffices to prove it on a multiplicative
**generating set** for `K(E)*`.

**Per-line case (would close A-002 modulo factorization):**
For `f = aX + bY + cZ`-type linear forms (lines in P²), the divisor
`div(f) = (P) + (Q) + (R) - 3(O)` where P, Q, R are the 3 intersection
points of the line with E (Bezout). By the geometric group law, three
collinear points sum to O, so σ(div(line)) = O = 0. This case is
**provable in ~50–100 lines** given the Bezout-on-E and 3-collinear-sum-to-O
infrastructure (some of which lives in `HasseWeil/Curves/NormBezout.lean`).

**Conics and higher degrees (the real obstacle):**
For irreducible f of degree ≥ 2 (e.g., conics meeting E in 6 points),
the sum-of-intersection-points = 0 fact is the **Cayley–Bacharach
theorem** (or its specialization to E and a curve of degree d). This is
a substantial theorem requiring:
- Resultants and Bezout's theorem on the projective plane.
- The "9th point" extension argument.
- Or equivalently: Riemann-Roch (which the project has explicitly
  decided to avoid).

Without this, the universal vanishing **cannot be reduced to per-curve
checks at the function-field level** in a clean way.

**Recommended path forward** (multi-session, high effort):
1. Build the Bezout-on-E infrastructure (~150 lines): for any homogeneous
   polynomial p of degree d, the divisor of `p|_E` has total degree 3d,
   with multiplicities given by intersection multiplicities.
2. Build the line case (~80 lines): for linear p, the 3 intersection
   points sum to O via the explicit group law.
3. Build Cayley–Bacharach (~500–1000 lines, **research-level**): for
   higher-degree p, the intersection points sum to (deg p) · O.
4. Combine with multiplicativity to conclude T-PIC-A-002.

**Alternative**: provide T-PIC-A-002 as a witness in
`AddHomProperty_of_picZero_witnesses`. This is what the witness-parametric
framework already supports — B-4-003 closure is a 5-line corollary
once anyone provides the witness.

**Status**: this ticket remains OPEN. The witness-parametric form
(via `T-PIC-E-001 = AddHomProperty_of_picZero_witnesses`) makes this
ticket's content droppable-in once delivered.
