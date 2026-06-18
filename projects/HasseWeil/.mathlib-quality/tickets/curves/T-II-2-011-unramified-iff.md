# T-II-2-011: Unramified ⇔ #φ⁻¹(Q) = deg(φ) everywhere

**Status**: PARTIAL (witness-parametric, 2026-04-20, worker-A)
**Silverman**: II.2.7 (Corollary)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: worker-A
**Estimated lines**: 25
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-2-008 (sum formula — supplied as a witness hypothesis `hsum`)

## Blocks
- T-III-4-015 (separable ⇒ #ker = deg) [already witness-closed via
  `HasseWeil/EC/IsogenyKernel.lean`]

## Statement (Silverman II.2.7)
A nonconstant map `φ : C₁ → C₂` is unramified if and only if

```
#φ⁻¹(Q) = deg(φ)   for all Q ∈ C₂.
```

## Framework adaptation

Our project uses `HasseWeil.Curves.CurveMap` (pullback-only; no intrinsic
`fiber` type or global `IsUnramified`). T-II-2-011 is therefore recorded in
**witness-parametric form**: the caller supplies
* `S : Finset C₁.SmoothPoint` — the fiber over a chosen image point,
* `hle` — each ramification index in `S` is ≥ 1 (automatic for a
  uniformizer witness, see
  `one_le_ramificationIndex_of_pullback_pointValuation_lt_one`),
* `hsum` — the II.2.6(a) sum formula `Σ e_φ(P) = deg(φ)` (witness).

The conclusion is the combinatorial Silverman II.2.7:
`#S = deg(φ) ↔ ∀ P ∈ S, e_φ(P) = 1`.

## Acceptance criteria (delivered)

```lean
namespace HasseWeil.Curves
namespace CurveMap

/-- Pure combinatorial content: if terms are ≥ 1, sum = card iff all = 1. -/
theorem _root_.Finset.sum_eq_card_iff_forall_eq_one_of_one_le
    {α : Type*} {S : Finset α} {e : α → ℤ}
    (hle : ∀ P ∈ S, 1 ≤ e P) :
    ∑ P ∈ S, e P = (S.card : ℤ) ↔ ∀ P ∈ S, e P = 1

/-- Silverman II.2.7 (witness-parametric): a fiber has size = deg iff every
    ramification index is 1. -/
theorem fiber_card_eq_degree_iff_all_ramificationIndexℤ_one
    (φ : CurveMap C₁ C₂) (t : C₂.FunctionField)
    (S : Finset C₁.SmoothPoint)
    (hle : ∀ P ∈ S, 1 ≤ φ.ramificationIndexℤ P t)
    (hsum : ∑ P ∈ S, φ.ramificationIndexℤ P t = (φ.degree : ℤ)) :
    (S.card : ℤ) = (φ.degree : ℤ) ↔
      ∀ P ∈ S, φ.ramificationIndexℤ P t = 1

end CurveMap
end HasseWeil.Curves
```

## Notes
- Direct from II.2.6(a): Σ_{P ∈ fiber} e_φ(P) = deg(φ). If every e_φ(P) = 1
  (unramified) then the count is just #fiber.
- The witness form is immediately usable once II.2.6(a) (T-II-2-008) is
  formalized; no further work at the T-II-2-011 site is required.

## Progress log
- 2026-04-20 (worker-A): witness-parametric form added in
  `HasseWeil/Curves/CurveMap.lean` + combinatorial helper
  `Finset.sum_eq_card_iff_forall_eq_one_of_one_le`. Compiles clean.
