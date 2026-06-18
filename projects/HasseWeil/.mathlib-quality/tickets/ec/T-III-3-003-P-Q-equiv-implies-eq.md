# T-III-3-003: (P) ~ (Q) ⇒ P = Q

**Status**: CHECKED-OUT
**Silverman**: III.3.3
**Module**: `HasseWeil/EC/PicE.lean`
**Owner**: worker-K
**Checked out at**: 2026-04-20T17:09Z
**Estimated lines**: 60 → **revised 300–500** (see 2026-04-20 progress note)
**Difficulty**: medium → **hard** (see 2026-04-20 progress note)
**Stream**: B/C

## Depends on
- T-III-3-002 (degree 2 over K(x))
- T-II-3-006 (linear equivalence)

## Blocks
- T-III-3-004 (Pic⁰(E) ≅ E)

## Statement (Silverman III.3.3)
On an elliptic curve `E`, if `(P) ∼ (Q)` (linear equivalence of divisors of degree
1), then `P = Q`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- On an elliptic curve, two single-point divisors are linearly equivalent only
    if the points are equal. Reference: Silverman III.3.3. -/
theorem WeierstrassCurve.point_divisor_inj (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (P Q : E.toAffine.Point) :
    (Divisor.single P 1 : Divisor _) ~_div Divisor.single Q 1 → P = Q

end HasseWeil.EC
```

## Notes
- Proof outline: if `(P) - (Q) = div(f)` for some `f ≠ 0`, then `f` has a unique
  pole (at `Q`) of order 1 and a unique zero (at `P`) of order 1. So `f` defines
  a degree-1 morphism `E → ℙ¹`, which would be an isomorphism (T-II-2-006). But
  `E` has genus 1, so cannot be isomorphic to `ℙ¹` (genus 0). The genus argument
  here is the only place we'd want RR; we can avoid it by directly observing that
  `K(E)` is a quadratic extension of `K(x)` (T-III-3-002), so cannot equal `K(t)`.

## Progress log

- **2026-04-20T17:09Z** [worker-K] checkout. Audit of ticket scope revealed two
  issues:
  1. **Signature/framework mismatch**: the ticket's acceptance-criteria uses
     `P, Q : E.toAffine.Point` (mathlib's inductive Point = `.zero | .some`),
     but the project's `Divisor C` (`HasseWeil/Curves/Divisors.lean`) is
     `C.SmoothPoint →₀ ℤ` — affine smooth points only, no ∞ support. There is
     no bridge from `E.toAffine.Point` to `C.SmoothPoint`, and `Divisor.single`
     for a `Point.zero` wouldn't typecheck.
  2. **Proof-strategy gap**: the ticket claims the proof avoids Riemann–Roch
     via "K(E) is a quadratic extension of K(x), so cannot equal K(t)". This
     reasoning is incorrect as stated — `K(T)/K(T²)` is itself quadratic, so
     `[K(E):K(x)] = 2` alone does NOT force `K(E) ≠ K(T)`. A rigorous RR-free
     proof requires:
     - Bridge `div(f) = (P) - (Q)` (projective, deg 0) ⇒ `[F(E):F(f)] = 1`.
     - Apply Lüroth (mathlib `RatFunc.finrank_eq_max_natDegree`) to get
       `F(E) ≅ F(T)`.
     - Ramification contradiction: any rational parametrization of
       `y² = x³+ax+b` with `Δ ≠ 0` would require 3 distinct finite critical
       values from a degree-2 `x : ℙ¹ → ℙ¹`, which has exactly 1.
     - Uses `ordAtInfty_coordX = -2`, `ordAtInfty_coordY = -3` from
       `Curves/Infinity.lean`.

  Revised estimate: **300–500 lines** for the full proof, plus **~150 lines**
  for ∞-aware divisor infrastructure (see sub-ticket
  `T-II-3-001b-projective-divisor`). Difficulty revised `medium → hard`.

  Plan per `/develop` Principle 5 (escalate, don't shortcut):
  1. Create sub-ticket **T-II-3-001b** for extending `Divisor` to include the
     point at infinity as a support place.
  2. Implement the extension + prove `deg(projectiveDivisorOf f) = 0`
     (Silverman II.3.1(b), overlaps T-II-3-009).
  3. Return to T-III-3-003 with the infrastructure in hand.
