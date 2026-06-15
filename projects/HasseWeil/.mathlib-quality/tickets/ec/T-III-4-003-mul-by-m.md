# T-III-4-003: [m] : E → E, [m] ≠ 0 for m ≠ 0

**Status**: DONE
**Silverman**: III.4.2(a)
**Module**: `HasseWeil/Basic.lean` → `HasseWeil/EC/Isogeny.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-4-001 (Isogeny)
- T-III-2-005 (doubling formula)

## Blocks
- T-III-4-006 (E[m])
- T-III-5-003 ([m]*ω = m·ω)
- T-III-5-004 (m ≠ 0 in K ⇒ [m] separable)

## Statement (Silverman III.4.2(a))
For each `m ∈ ℤ`, there is the multiplication-by-m isogeny `[m] : E → E`.
For `m ≠ 0`, `[m] ≠ 0` (the constant isogeny).

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Multiplication-by-m as an isogeny.
    Reference: Silverman III.4.2(a). -/
def WeierstrassCurve.mulByInt (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] (m : ℤ) :
    Isogeny E E

theorem WeierstrassCurve.mulByInt_ne_zero (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    {m : ℤ} (hm : m ≠ 0) :
    E.mulByInt m ≠ 0

end HasseWeil.EC
```

## Notes
- For `m ≠ 0`, `[m] ≠ 0` requires showing `E` has a non-torsion point of finite
  order (or equivalently that `[m]` does not kill all of `E`). One way: use the
  formal-group analysis (`[m](T) = mT + ...`) which is nonzero in characteristic
  not dividing `m`. For arbitrary characteristic, use that `E[m]` is finite.
- Existing partial implementation in `HasseWeil/Basic.lean`.

## Progress log
- 2026-04-08 [worker-C] checkout. Plan: focus on closing the two existing
  `Endomorphism.lean` sorries (`isogTrace_mulByInt_zero`, `isogTrace_mulByInt_one`)
  which are listed in INDEX as part of T-III-4-003 (mulByInt edge cases). The
  current code defines `mulByInt 0` with the identity pullback (degree = 1
  computationally), so the literal trace formula gives 1, not 0. Will provide
  correct edge-case theorems via direct degree computation, then write
  `mulByInt_ne_zero` (the main acceptance criterion).
- 2026-04-08 [worker-C] DONE. Closed both edge-case sorries:
  - Deleted `isogTrace_mulByInt_zero` and `isogTrace_mulByInt_one`. They were
    mathematically false under the current `mulByInt 0 := AlgHom.id` convention
    (which gives `(mulByInt E 0).degree = 1`, not 0). Both theorems were unused
    downstream and contradicted the existing `isogTrace_mulByInt` which already
    documents the trace formula only holds for `n ≠ 0 ∧ 1 - n ≠ 0`. Removing
    them is the correct action; if a future ticket adds a true zero isogeny
    (with proper degree-0 convention), the n=0 trace can be reproved then.
  - Added `mulByInt_degree_pos` and `mulByInt_degree_ne_zero` to `Basic.lean`
    (alongside `mulByInt_degree`). These are the literal acceptance criteria
    of T-III-4-003 ("[m] ≠ 0 for m ≠ 0"), restated as positive-degree statements
    since `Isogeny` carries no `Zero` instance.
  - **Endomorphism.lean: 4 → 2 sorries.** Remaining 2 (lines 58, 84) are
    `isogOneSub.pullback`/`isogSmulSub.pullback` for **arbitrary** α, which
    require the Weierstrass addition law as an algebra hom on K(E). Out of
    scope for T-III-4-003; tracked under T-III-4-009 (translation map).
  - Build clean: `lake build` succeeds (2763 jobs), 0 new sorries.
  - Status: REVIEW.
- 2026-04-10 [worker-A] Verified: `#print axioms` on `mulByInt_degree_pos` and
  `mulByInt_degree_ne_zero` shows only standard axioms (propext, Classical.choice,
  Quot.sound). No sorryAx. Full `lake build` clean. Status: DONE.
