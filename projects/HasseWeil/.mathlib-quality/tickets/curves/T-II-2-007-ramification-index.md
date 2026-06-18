# T-II-2-007: Ramification index e_φ(P)

**Status**: PARTIAL (worker-I, 2026-04-20) — witness-parametric form delivered;
fully-intrinsic `e_φ(P)` without test-function argument blocked on image-point
correspondence (T-II-2-001 at point-map level, requires integral closure).
**Silverman**: II.2 (definition before II.2.6)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: worker-I (partial)
**Estimated lines**: 30 (delivered ~60 of API)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-1-002 (ord_P), T-II-1-003 (uniformizer)
- T-II-2-001 (morphism)

## Blocks
- T-II-2-008 (sum formula)
- T-II-2-009 (#fibers = deg_s)
- T-III-4-013 (e_φ = deg_i)

## Statement
For a nonconstant map `φ : C₁ → C₂` and a point `P ∈ C₁`, the **ramification
index** of `φ` at `P` is

```
e_φ(P) := ord_P(φ*(t_{φ(P)}))
```

where `t_{φ(P)}` is a uniformizer at `φ(P) ∈ C₂`. We say `φ` is **unramified at
P** if `e_φ(P) = 1`, and **unramified** if it's unramified at every point.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The ramification index of a morphism at a point.
    Reference: Silverman II.2 (definition). -/
noncomputable def Morphism.ramificationIndex (φ : Morphism C₁ C₂)
    (P : C₁.SmoothPoint) : ℤ :=
  -- e_φ(P) = ord_P(φ*(t)) for any uniformizer t at φ(P)
  sorry

theorem Morphism.ramificationIndex_pos (φ : Morphism C₁ C₂) (hφ : ¬ IsConst φ)
    (P : C₁.SmoothPoint) :
    1 ≤ φ.ramificationIndex P

/-- φ is unramified at P. -/
def Morphism.IsUnramifiedAt (φ : Morphism C₁ C₂) (P : C₁.SmoothPoint) : Prop :=
  φ.ramificationIndex P = 1

/-- φ is unramified everywhere. -/
def Morphism.IsUnramified (φ : Morphism C₁ C₂) : Prop :=
  ∀ P, φ.IsUnramifiedAt P

end HasseWeil.Curves
```

## Notes
- Independence of choice of uniformizer: any two uniformizers at φ(P) differ by
  a unit, so the ord doesn't change.
- mathlib has `Ideal.ramificationIdx` in `Mathlib.RingTheory.DedekindDomain.Ideal`.

## Progress log

- **2026-04-20** (worker-I): delivered witness-parametric API in
  `HasseWeil/Curves/CurveMap.lean`:
  - `CurveMap.ramificationIndex φ P t := C₁.ord_P P (φ.pullback t)` as
    `WithTop ℤ` (explicit test function `t`).
  - `CurveMap.ramificationIndexℤ` — `ℤ`-valued form via `.untopD 0`.
  - `CurveMap.ramificationIndex_id` / `ramificationIndex_comp` (chain rule
    at pullback level), plus `ℤ`-analogues.
  - `CurveMap.ramificationIndex_ne_top` (for `t ≠ 0`).
  - `CurveMap.pullback_ne_zero` (pullback of nonzero is nonzero).
  - `CurveMap.IsUnramifiedAt φ P t := ramificationIndex P t = 1`, with
    `isUnramifiedAt_iff_uniformizer_pullback` and `id_isUnramifiedAt`.
  - `CurveMap.one_le_ramificationIndex_of_pullback_pointValuation_lt_one`
    — the positivity result, in the "P over zero of t" form.
  Also delivered the public bridge
  `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one` in
  `HasseWeil/Curves/Valuation.lean`. All axiom-clean.

  **Blocker for full version**: intrinsic `e_φ(P) : ℤ` without test function
  needs the image-point map `φ# : SmoothPoint C₁ → SmoothPoint C₂`, which
  requires the pullback `φ*(F[C₂]) ⊂ F[C₁]` (morphism-everywhere property)
  plus the maximal-ideal-↔-smooth-point correspondence. Both depend on
  T-II-1-004 Part 2 (`F[C]` is integrally closed in `F(C)`).
