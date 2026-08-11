/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».CornerSquareDatum
import «Adic spaces».Presheaf

/-!
# The 𝒪-valued Čech complex of a rational covering, all degrees (T632)

[Wedhorn] Appendix A (l.5245–5270) verbatim, at the structure presheaf of a
`RationalCoveringData`: the group of `q`-cochains is the product of the
completed rational localizations at all `(q+1)`-tuple intersections
(`interList` of cover pieces, unnormalized — repetitions included), the
differential is the alternating sum of the face restrictions
`(dq f)_{i₀…i_{q+1}} = Σ (−1)^j f_{i₀…î_j…i_{q+1}}`, and the augmentation is
the product restriction from the base.

`IsCechAcyclicFull` is Definition A.1 verbatim: exactness of the augmented
complex `0 → 𝒪(X) → Č⁰ → Č¹ → ⋯` at every degree.
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTateRing A]
  [DecidableEq A] [PlusSubring A] [HasLocLiftPowerBounded A]

variable (C : RationalCoveringData A) (hC : C.IsRational)

/-- The `(q+1)`-tuple intersection datum of cover pieces
([Wedhorn] `U_{i₀…i_q}`). -/
noncomputable def tupleDatum {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    RationalLocData A :=
  interList (fun i => (σ i).1) (fun i => hC.piece (σ i).2)

omit [HasLocLiftPowerBounded A] in
theorem tupleDatum_isRational {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    (tupleDatum C hC σ).IsRational :=
  interList_isRational _ _

omit [HasLocLiftPowerBounded A] in
theorem rationalOpen_tupleDatum {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s =
      ⋂ i, rationalOpen (σ i).1.T (σ i).1.s :=
  rationalOpen_interList _ _

omit [HasLocLiftPowerBounded A] in
/-- The tuple intersection is contained in each face's intersection. -/
theorem tupleDatum_subset_face {q : ℕ} (σ : Fin (q + 2) → ↥C.covers)
    (j : Fin (q + 2)) :
    rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s ⊆
      rationalOpen (tupleDatum C hC (σ ∘ j.succAbove)).T
        (tupleDatum C hC (σ ∘ j.succAbove)).s := by
  rw [rationalOpen_tupleDatum, rationalOpen_tupleDatum]
  exact Set.subset_iInter fun i => Set.iInter_subset _ (j.succAbove i)

omit [HasLocLiftPowerBounded A] in
/-- The tuple intersection is contained in the base. -/
theorem tupleDatum_subset_base {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s ⊆
      rationalOpen C.base.T C.base.s := by
  rw [rationalOpen_tupleDatum]
  exact le_trans (Set.iInter_subset _ 0) (C.hsubset _ (σ 0).2)

/-- The group of unnormalized `q`-cochains with values in the structure
presheaf. -/
abbrev cechO (q : ℕ) : Type _ :=
  ∀ σ : Fin (q + 1) → ↥C.covers, presheafValue (tupleDatum C hC σ)

/-- The Čech differential ([Wedhorn] l.5262's `dq` formula). -/
noncomputable def cechD (q : ℕ) : cechO C hC q →+ cechO C hC (q + 1) where
  toFun f := fun σ => ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
    restrictionMapHom (tupleDatum C hC (σ ∘ j.succAbove)) (tupleDatum C hC σ)
      (tupleDatum_subset_face C hC σ j) (f (σ ∘ j.succAbove))
  map_zero' := by
    funext σ
    simp only [Pi.zero_apply, map_zero, smul_zero, Finset.sum_const_zero]
  map_add' f g := by
    funext σ
    show (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        restrictionMapHom _ _ (tupleDatum_subset_face C hC σ j)
          ((f + g) (σ ∘ j.succAbove))) = _
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The augmentation `𝒪(X) → Č⁰` ([Wedhorn] l.5273's `ε`). -/
noncomputable def cechAug : presheafValue C.base →+ cechO C hC 0 where
  toFun s := fun σ => restrictionMapHom C.base (tupleDatum C hC σ)
    (tupleDatum_subset_base C hC σ) s
  map_zero' := by
    funext σ
    simp only [map_zero, Pi.zero_apply]
  map_add' s t := by
    funext σ
    simp only [map_add, Pi.add_apply]

/-- **All-degree Čech acyclicity** ([Wedhorn] Definition A.1 verbatim):
the augmented unnormalized Čech complex
`0 → 𝒪(X) → Č⁰ → Č¹ → ⋯` is exact. -/
structure IsCechAcyclicFull : Prop where
  /-- Exactness at `𝒪(X)`: the augmentation is injective. -/
  aug_injective : Function.Injective (cechAug C hC)
  /-- Exactness at `Č⁰`: cocycles are restrictions of global sections. -/
  exact_zero : ∀ f : cechO C hC 0, cechD C hC 0 f = 0 →
    ∃ s : presheafValue C.base, cechAug C hC s = f
  /-- Exactness at `Č^{q+1}`: cocycles are coboundaries. -/
  exact_succ : ∀ (q : ℕ) (f : cechO C hC (q + 1)), cechD C hC (q + 1) f = 0 →
    ∃ g : cechO C hC q, cechD C hC q g = f

end ValuationSpectrum
