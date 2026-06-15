# T-III-4-013: e_φ(P) = deg_i φ for all P (isogeny version)

**Status**: PARTIAL (witness-parametric, 2026-04-20, worker-A)
**Silverman**: III.4.10(a)(ii)
**Module**: `HasseWeil/EC/IsogenyKernel.lean`
**Owner**: worker-A (partial)
**Estimated lines**: 40 (delivered ~50 with Q-ratio form)
**Difficulty**: medium (CRITICAL)
**Stream**: C

## Depends on
- T-II-2-008 (Σ e = deg)
- T-III-4-012 (fiber card = deg_s)

## Blocks
- T-III-4-015 (separable ⇒ unramified)

## Statement (Silverman III.4.10(a) second half)
For every nonzero isogeny `φ : E₁ → E₂` and every `P ∈ E₁(K̄)`,
`e_φ(P) = deg_i φ` (the inseparable degree).

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- For an isogeny, every point has the same ramification index = deg_i.
    Reference: Silverman III.4.10(a) second part. -/
theorem Isogeny.ramification_eq_inSepDegree (α : Isogeny E₁ E₂) (hα : α ≠ 0)
    (P : E₁.toAffine.Point) :
    α.ramificationIndex P = α.degree / α.sepDegree

end HasseWeil.EC
```

## Notes
- From `Σ_{P in fiber} e(P) = deg φ` (T-II-2-008) and the fact that all `e(P)`
  are equal (by translation symmetry, similar to the fiber card result), we get
  `deg_s · e = deg`, so `e = deg / deg_s = deg_i`.

## Witness-parametric form (delivered)

```lean
namespace HasseWeil.Isogeny

/-- Combinatorial helper: uniform function sums to card × constant. -/
theorem _root_.Finset.sum_eq_card_mul_of_constant
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (heq : ∀ P ∈ S, e P = c) :
    ∑ P ∈ S, e P = (S.card : ℤ) * c

/-- Witness-parametric III.4.10(a) second half (product form):
    deg_s × c = deg. -/
theorem ramificationIndex_mul_sepDegree_eq_degree_of_witnesses
    (φ : Isogeny W₁ W₂)
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (h_uniform : ∀ P ∈ S, e P = c)
    (h_sum : ∑ P ∈ S, e P = (φ.degree : ℤ))
    (h_card : S.card = φ.sepDegree) :
    (φ.sepDegree : ℤ) * c = (φ.degree : ℤ)

/-- Witness-parametric III.4.10(a) second half (ratio form, over ℚ):
    c = deg / deg_s = deg_i. -/
theorem ramificationIndex_eq_insepDegree_of_witnesses
    (φ : Isogeny W₁ W₂) (hs : φ.sepDegree ≠ 0)
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (h_uniform : ∀ P ∈ S, e P = c)
    (h_sum : ∑ P ∈ S, e P = (φ.degree : ℤ))
    (h_card : S.card = φ.sepDegree) :
    (c : ℚ) = (φ.degree : ℚ) / (φ.sepDegree : ℚ)

end HasseWeil.Isogeny
```

Witness inputs:
* `h_uniform` — translation symmetry (Silverman III.4.10(a) setup)
* `h_sum` — T-II-2-008 (Σ e = deg)
* `h_card` — T-III-4-012 (#fiber = deg_s)

The combinatorial closure is axiom-clean; once the three witnesses are
available from their respective tickets, T-III-4-013 is immediate.

## Progress log

- **2026-04-20** (worker-A): delivered combinatorial witness-parametric form
  in `HasseWeil/EC/IsogenyKernel.lean`:
  - `Finset.sum_eq_card_mul_of_constant` — uniform sum helper (ℤ).
  - `Isogeny.ramificationIndex_mul_sepDegree_eq_degree_of_witnesses` — product
    form of the statement.
  - `Isogeny.ramificationIndex_eq_insepDegree_of_witnesses` — ratio form
    (over ℚ), expressing `c = deg / deg_s = deg_i`.
  Build clean, no new axioms beyond the standard (`propext`,
  `Classical.choice`, `Quot.sound`).
