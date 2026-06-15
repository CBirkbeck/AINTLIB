/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Verschiebung.FieldTower

/-!
# Verschiebung pullback construction (Session 4)

Given the Silverman III.6.2 inclusion `Im([q]*) ⊆ Im(π*) = K(E)^q` (Session 3
witness), the Verschiebung's pullback `V* : K(E) →ₐ[K] K(E)` is constructed
via the composition

```
       (mulByInt W q).pullback              π*⁻¹
K(E) ───────────────────────────► Im(π*) ───────► K(E)
            (factors through                ≃ₐ
              the inclusion)
```

where `π*⁻¹` is the inverse of the Frobenius pullback restricted to its
range (which is a `K(E) ≃ₐ[K] Im(π*)` via `AlgEquiv.ofInjective`).

The factoring identity `[q]* = π* ∘ V*` is then automatic from this
construction.

## Main definitions

* `frobeniusIsog_rangeEquiv` — `K(E) ≃ₐ[K] (frobeniusIsog W).pullback.range`
  (the canonical Frobenius restricted to its image, via injectivity).
* `verschiebungPullback_of_witness` — the V* algebra hom, parametric on
  the inclusion witness.
* `mulByInt_q_factor_via_witness` — the factoring identity
  `[q]* = π* ∘ V*` derived from V*'s construction.

## Status

Witness-parametric on the Session 3 inclusion. Once Session 3's
unconditional discharge lands, this file's outputs become axiom-clean.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### Frobenius as AlgEquiv onto its range

`(frobeniusIsog W).pullback : K(E) →ₐ[K] K(E)` is injective (as any AlgHom
between fields). Its range is a Subalgebra of `K(E)`. By
`AlgEquiv.ofInjective`, this gives a canonical `K(E) ≃ₐ[K]
(frobeniusIsog W).pullback.range`. -/

/-- The Frobenius pullback as an `AlgEquiv` onto its range. -/
noncomputable def frobeniusIsog_rangeEquiv :
    W.toAffine.FunctionField ≃ₐ[K]
      (frobeniusIsog W).pullback.range :=
  AlgEquiv.ofInjective (frobeniusIsog W).pullback
    (frobeniusIsog W).pullback.toRingHom.injective

/-- Applying `frobeniusIsog_rangeEquiv` produces the Frobenius image
    (as an element of the range Subalgebra). -/
@[simp] theorem frobeniusIsog_rangeEquiv_apply (z : W.toAffine.FunctionField) :
    ((frobeniusIsog_rangeEquiv W) z : W.toAffine.FunctionField) =
      (frobeniusIsog W).pullback z := by
  simp [frobeniusIsog_rangeEquiv]

/-! ### `[q]*` restricted to land in the Frobenius image

The Session 3 inclusion `Im([q]*) ⊆ Im(π*)` — given as a witness here
(`h_subset`) — lets us *restrict* the codomain of `(mulByInt W q).pullback`
to land in `(frobeniusIsog W).pullback.range`. This is the natural
intermediate step before composing with `π*⁻¹`. -/

/-- Codomain restriction of `(mulByInt W q).pullback` to land in the
    Frobenius range, given the inclusion witness. -/
noncomputable def mulByInt_q_pullback_restricted
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    W.toAffine.FunctionField →ₐ[K] (frobeniusIsog W).pullback.range :=
  (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.codRestrict
    (frobeniusIsog W).pullback.range
    (fun z => h_subset ⟨z, rfl⟩)

/-- Coercion of `mulByInt_q_pullback_restricted` back to `K(E)` via the
    range subalgebra inclusion gives `(mulByInt W q).pullback`. -/
@[simp] theorem mulByInt_q_pullback_restricted_coe
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (z : W.toAffine.FunctionField) :
    ((mulByInt_q_pullback_restricted W h_subset z) :
        W.toAffine.FunctionField) =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z :=
  rfl

/-! ### The Verschiebung pullback `V*`

V* := frobenius_rangeEquiv.symm ∘ mulByInt_q_pullback_restricted.

By construction:
* `π* (V* z) = frobenius_rangeEquiv (frobenius_rangeEquiv.symm (mulByInt_q_restricted z))
            = (mulByInt_q_restricted z : K(E))
            = (mulByInt W q).pullback z`

So `π* ∘ V* = (mulByInt W q).pullback`, the desired factoring. -/

/-- **The Verschiebung pullback** `V* : K(E) →ₐ[K] K(E)`, witness-parametric
    on the Session 3 inclusion. Constructed as the composition
    `π*⁻¹ ∘ ([q]* restricted to Im(π*))`. -/
noncomputable def verschiebungPullback_of_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField :=
  ((frobeniusIsog_rangeEquiv W).symm.toAlgHom).comp
    (mulByInt_q_pullback_restricted W h_subset)

/-- **Factoring identity**: `(mulByInt W q).pullback = π*.comp V*`,
    derived from V*'s construction. -/
theorem mulByInt_q_factor_via_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
      (frobeniusIsog W).pullback.comp
        (verschiebungPullback_of_witness W h_subset) := by
  apply AlgHom.ext
  intro z
  -- LHS: (mulByInt W q).pullback z
  -- RHS: π* (V* z) = π* ((frobenius_rangeEquiv).symm (mulByInt_q_restricted z))
  --    = ((frobenius_rangeEquiv) ((frobenius_rangeEquiv).symm (mulByInt_q_restricted z)) : K(E))
  --    = ((mulByInt_q_restricted z) : K(E))
  --    = (mulByInt W q).pullback z
  show (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z =
    (frobeniusIsog W).pullback
      ((frobeniusIsog_rangeEquiv W).symm
        (mulByInt_q_pullback_restricted W h_subset z))
  -- Apply π* to (frobenius_rangeEquiv).symm result
  have h_apply_pi :
      (frobeniusIsog W).pullback
        ((frobeniusIsog_rangeEquiv W).symm
          (mulByInt_q_pullback_restricted W h_subset z)) =
      ((frobeniusIsog_rangeEquiv W) ((frobeniusIsog_rangeEquiv W).symm
        (mulByInt_q_pullback_restricted W h_subset z)) :
          W.toAffine.FunctionField) := by
    rw [← frobeniusIsog_rangeEquiv_apply W ((frobeniusIsog_rangeEquiv W).symm
      (mulByInt_q_pullback_restricted W h_subset z))]
  rw [h_apply_pi, AlgEquiv.apply_symm_apply]
  rw [mulByInt_q_pullback_restricted_coe]

end HasseWeil
