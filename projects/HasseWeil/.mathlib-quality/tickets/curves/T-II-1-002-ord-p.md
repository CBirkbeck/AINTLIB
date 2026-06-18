# T-II-1-002: `ord_P : K(C) → ℤ ∪ ∞`

**Status**: DONE (verified axiom-clean 2026-04-22: `ord_P`, `ord_P_zero`, `ord_P_mul`, `ord_P_add_le` all depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.1 (definition after II.1.1)
**Module**: `HasseWeil/Curves/Valuation.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-17T09:15Z
**Estimated lines**: 40
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-1-001 (DVR at smooth point)

## Blocks
- T-II-1-003 (uniformizer)
- T-II-2-007 (ramification index)
- T-II-3-005 (div(f))
- T-II-4-007 (ord_P(ω))

## Statement
For a smooth curve `C` and smooth point `P ∈ C`, define the order function
`ord_P : K̄(C)* → ℤ` extending to `ord_P : K̄(C) → ℤ ∪ {∞}` with `ord_P(0) = ∞`.

This is the discrete valuation associated to the DVR `K̄[C]_P` from T-II-1-001.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The order of a function at a smooth point of a curve.
    Returns ℤ for nonzero functions, ⊤ for zero.
    Reference: Silverman II.1 (definition). -/
noncomputable def ord_P (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    C.FunctionField → ℤ ∪ ⊤ := sorry  -- via DVR

theorem ord_P_zero (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    ord_P C P 0 = ⊤

theorem ord_P_mul (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    (f g : C.FunctionField) :
    ord_P C P (f * g) = ord_P C P f + ord_P C P g

theorem ord_P_add_le (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    (f g : C.FunctionField) :
    min (ord_P C P f) (ord_P C P g) ≤ ord_P C P (f + g)

end HasseWeil.Curves
```

## Notes
- Use mathlib's `Multiplicative` / `WithTop ℤ` structure or just `ℤ ∪ ⊤`.
- The DVR structure from T-II-1-001 gives this directly via `IsDiscreteValuationRing.maxPowDivides`
  or similar.
- Make `ord_P` decidable where possible.

## Progress log

- 2026-04-17T09:15Z [worker-A] checkout. Strategy: build on the
  `localRing_isDVR_of_smooth` theorem from T-II-1-001. Use mathlib's
  adic-valuation machinery: `IsDiscreteValuationRing.maximalIdeal` gives a
  `HeightOneSpectrum` element on the local ring, whose `.valuation K` lands
  in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`. Convert to `WithTop ℤ` via
  `WithZero.unzero` + `Multiplicative.toAdd` with a sign flip (uniformizer
  has `v = ofAdd(-1)` multiplicatively, so `ord = 1` additively).
- 2026-04-17T10:30Z [worker-A] Complete.
  - Created `HasseWeil/Curves/Valuation.lean`:
    * `SmoothPlaneCurve.localRingAt P := Localization.AtPrime (C.maximalIdealAt P)`
      as a noncomputable abbrev.
    * `SmoothPlaneCurve.maximalIdealAt_isPrime` as an instance (derived
      from `maximalIdealAt_isMaximal.isPrime`) — needed so
      `Localization.AtPrime` elaborates.
    * `localRingAt.instIsDVR` delegates to `localRing_isDVR_of_smooth`.
    * `localRingAt.instIsFractionRing` obtains
      `IsFractionRing (localRingAt P) FunctionField` from mathlib's
      `IsFractionRing (Localization.AtPrime p) (FractionRing R)` instance.
    * `SmoothPlaneCurve.pointValuation C P : Valuation FunctionField ℤᵐ⁰`
      is the adic valuation on the fraction field induced by the DVR.
    * `SmoothPlaneCurve.ord_P C P : FunctionField → WithTop ℤ` is the
      additive version: `⊤` on zero, otherwise `-(unzero hne).toAdd : ℤ`.
  - Proved the three ticket lemmas:
    * `ord_P_zero : ord_P C P 0 = ⊤` (trivial from `map_zero`).
    * `ord_P_mul : ord_P (f*g) = ord_P f + ord_P g` via case split on
      f = 0 / g = 0, then `map_mul` + `toAdd_mul` + `WithTop.coe_add`.
    * `ord_P_add_le : min (ord_P f) (ord_P g) ≤ ord_P (f+g)` via case
      split on f = 0 / g = 0 / (f+g) = 0, then flip sign on
      `(pointValuation P).map_add_le_max`.
  - Also added helper lemma `pointValuation_eq_zero_iff` and
    `ord_P_eq_top_iff`.
  - `HasseWeil.lean` root updated to import the new module.
  - `lake build HasseWeil.Curves.Valuation` passes with 0 errors; full
    `lake build HasseWeil` passes. `sorry_analyzer.py` reports 0 sorries.
    `#print axioms` on `ord_P`, `ord_P_zero`, `ord_P_mul`, `ord_P_add_le`
    reports only `propext, Classical.choice, Quot.sound` (standard
    mathlib axioms).
  - **Deviation from ticket signature**: the ticket shows the body as
    `sorry  -- via DVR` with no `Module` instance or other structure. The
    implementation defines `ord_P` as a direct function returning
    `WithTop ℤ`, not as an `AddValuation` bundle. Mathlib doesn't have an
    ergonomic `AddValuation ... (WithTop ℤ)` for DVR → fraction field in
    one step, so the additive formulation is unpacked manually from the
    multiplicative `pointValuation : Valuation _ ℤᵐ⁰`. The three required
    lemmas are still provided exactly as specified.
  - Status → REVIEW.
