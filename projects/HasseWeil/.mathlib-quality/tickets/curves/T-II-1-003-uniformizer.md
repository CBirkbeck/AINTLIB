# T-II-1-003: Uniformizer

**Status**: DONE (verified axiom-clean 2026-04-22: `exists_uniformizer` depends only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.1 (definition after II.1.1)
**Module**: `HasseWeil/Curves/Valuation.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-17T10:45Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-1-001 (DVR)
- T-II-1-002 (ord_P)

## Blocks
- T-II-2-007 (ramification index uses uniformizer)
- T-II-4-005 (ω = g·dt)

## Statement
A **uniformizer** at a smooth point `P` is any function `t ∈ K̄(C)` with
`ord_P(t) = 1`. Equivalently, `t` is a generator for the maximal ideal of `K̄[C]_P`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A uniformizer at a smooth point `P` of a smooth curve. -/
def Uniformizer (C : SmoothPlaneCurve F) (P : C.SmoothPoint) (t : C.FunctionField) : Prop :=
  ord_P C P t = 1

/-- Existence of a uniformizer (from DVR structure). -/
theorem exists_uniformizer (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    ∃ t : C.FunctionField, Uniformizer C P t

/-- Two uniformizers differ by a unit. -/
theorem Uniformizer.unit_quotient (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    {t s : C.FunctionField} (ht : Uniformizer C P t) (hs : Uniformizer C P s) :
    ord_P C P (t / s) = 0

end HasseWeil.Curves
```

## Notes
- The mathlib equivalent is `IsDiscreteValuationRing.exists_uniformizer` or similar.
- We use `Uniformizer` (not `Mathlib.RingTheory.DiscreteValuationRing.uniformizer`)
  to keep our notation consistent with Silverman.

## Progress log

- 2026-04-17T10:45Z [worker-A] checkout. Deps T-II-1-001 (DVR) and
  T-II-1-002 (ord_P) both in REVIEW; plan to land the uniformizer API
  on top of `HasseWeil/Curves/Valuation.lean`. Strategy: use
  `HeightOneSpectrum.valuation_exists_uniformizer` from mathlib to
  extract a `π` with multiplicative valuation `exp(-1)`, then unfold
  to `ord_P = 1`.
- 2026-04-17T11:00Z [worker-A] Complete.
  - **Deviation from ticket Module field**: the ticket specified
    `Curves/Basic.lean`; the uniformizer API is placed in
    `Curves/Valuation.lean` since it logically sits next to `ord_P`
    and reuses its helper `ord_P_of_ne`.
  - Added to `HasseWeil/Curves/Valuation.lean`:
    * New helper `ord_P_inv : f ≠ 0 → ord_P P f⁻¹ = -(ord_P P f)`
      (needed to prove the unit-quotient lemma).
    * `Uniformizer C P t := ord_P C P t = 1`.
    * `exists_uniformizer C P : ∃ t, Uniformizer C P t` — proved by
      calling `HeightOneSpectrum.valuation_exists_uniformizer` on the
      DVR's maximal ideal and converting the multiplicative output
      `exp(-1) = ↑(ofAdd(-1))` to the additive `ord_P t = 1` via
      `WithZero.coe_inj` + `rfl` on `(ofAdd (-1)).toAdd = -1`.
    * `Uniformizer.unit_quotient : ord_P (t/s) = 0` — expands `t/s`
      as `t * s⁻¹`, applies `ord_P_mul`, `ord_P_inv`, then computes
      `1 + (-1) = 0` in `WithTop ℤ`.
  - `lake build HasseWeil.Curves.Valuation` passes with 0 errors,
    full `lake build HasseWeil` passes, 0 sorries. `#print axioms`
    reports only standard mathlib axioms on
    `exists_uniformizer`, `Uniformizer.unit_quotient`, `ord_P_inv`.
  - Status → REVIEW.
