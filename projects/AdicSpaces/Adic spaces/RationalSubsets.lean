/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicSpectrum
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Rational Subsets and Finite Intersection Stability

Rational subsets and their stability under finite intersection (Remark 7.30, Theorem 7.35(2)).

## Main definitions

* `IsRationalSubset U` : `U = R(T/s)` for some finite `T` and `s ∈ A`.

## Main results

* `rationalOpen_inter` : `R(T₁/s₁) ∩ R(T₂/s₂) = R(T₁·T₂/s₁·s₂)`
  (Remark 7.30(5)).
* `IsRationalSubset.inter` : Intersection of two rational subsets is rational.
* `IsRationalSubset.isOpen` : Rational subsets are open in `Spa(A, A⁺)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Remark 7.30, Theorem 7.35(2)
-/

open scoped Pointwise

namespace ValuationSpectrum

section Helpers

variable {A : Type*} [CommRing A]

/-- `v(s₁ * s₂) ≠ 0` implies `v(s₁) ≠ 0`. -/
lemma not_vle_zero_left_of_mul {v : Spv A} {s₁ s₂ : A}
    (h : ¬ v.vle (s₁ * s₂) 0) : ¬ v.vle s₁ 0 := by
  intro hs₁
  apply h
  letI : ValuativeRel A := v.toValuativeRel
  have := ValuativeRel.mul_vle_mul_left hs₁ s₂
  rwa [zero_mul] at this

/-- `v(s₁ * s₂) ≠ 0` implies `v(s₂) ≠ 0`. -/
lemma not_vle_zero_right_of_mul {v : Spv A} {s₁ s₂ : A}
    (h : ¬ v.vle (s₁ * s₂) 0) : ¬ v.vle s₂ 0 := by
  rw [mul_comm] at h
  exact not_vle_zero_left_of_mul h

end Helpers

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A] [DecidableEq A]

/-- A rational subset is one of the form `rationalOpen T s` (Definition 7.29). -/
def IsRationalSubset (U : Set (Spv A)) : Prop :=
  ∃ (T : Finset A) (s : A), U = rationalOpen T s

/-- Adding `s` to `T` does not change `R(T/s)` (Remark 7.30(3)). -/
theorem rationalOpen_insert_s (T : Finset A) (s : A) :
    rationalOpen (insert s T) s = rationalOpen T s := by
  ext v
  constructor
  · rintro ⟨hv, hvT, hvs⟩
    exact ⟨hv, fun t ht ↦ hvT t (Finset.mem_insert_of_mem ht), hvs⟩
  · rintro ⟨hv, hvT, hvs⟩
    exact ⟨hv, fun t ht ↦ (Finset.mem_insert.mp ht).elim
      (fun h ↦ h ▸ (v.vle_total t t).elim id id) (hvT t), hvs⟩

/-- `R(T₁/s₁) ∩ R(T₂/s₂) = R(T₁·T₂ / s₁·s₂)` (Remark 7.30(5)). -/
theorem rationalOpen_inter (T₁ T₂ : Finset A) (s₁ s₂ : A)
    (hs₁ : s₁ ∈ T₁) (hs₂ : s₂ ∈ T₂) :
    rationalOpen T₁ s₁ ∩ rationalOpen T₂ s₂ =
      rationalOpen (T₁ * T₂) (s₁ * s₂) := by
  ext v
  letI : ValuativeRel A := v.toValuativeRel
  constructor
  · rintro ⟨⟨hv₁, hvT₁, hvs₁⟩, ⟨_, hvT₂, hvs₂⟩⟩
    refine ⟨hv₁, fun t ht ↦ ?_,
      ValuativeRel.zero_vlt_mul hvs₁ hvs₂⟩
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Finset.mem_mul.mp ht
    exact ValuativeRel.mul_vle_mul (hvT₁ t₁ ht₁) (hvT₂ t₂ ht₂)
  · rintro ⟨hv, hvT, hvs⟩
    have hs₁' : ¬ v.vle s₁ 0 := not_vle_zero_left_of_mul hvs
    have hs₂' : ¬ v.vle s₂ 0 := not_vle_zero_right_of_mul hvs
    refine ⟨⟨hv, fun t₁ ht₁ ↦ ?_, hs₁'⟩, ⟨hv, fun t₂ ht₂ ↦ ?_, hs₂'⟩⟩
    · have hle := hvT (t₁ * s₂) (Finset.mul_mem_mul ht₁ hs₂)
      rwa [ValuativeRel.mul_vle_mul_iff_left hs₂'] at hle
    · have hmem : s₁ * t₂ ∈ T₁ * T₂ := Finset.mul_mem_mul hs₁ ht₂
      have hle := hvT (s₁ * t₂) hmem
      rw [mul_comm s₁ t₂, mul_comm s₁ s₂] at hle
      rwa [ValuativeRel.mul_vle_mul_iff_left hs₁'] at hle

omit [DecidableEq A] in
/-- The intersection of two rational subsets is rational (Theorem 7.35(2)). -/
theorem IsRationalSubset.inter {U V : Set (Spv A)}
    (hU : IsRationalSubset U) (hV : IsRationalSubset V) :
    IsRationalSubset (U ∩ V) := by
  classical
  obtain ⟨T₁, s₁, rfl⟩ := hU
  obtain ⟨T₂, s₂, rfl⟩ := hV
  rw [← rationalOpen_insert_s T₁ s₁, ← rationalOpen_insert_s T₂ s₂]
  exact ⟨insert s₁ T₁ * insert s₂ T₂, s₁ * s₂,
    rationalOpen_inter _ _ _ _ (Finset.mem_insert_self s₁ T₁)
      (Finset.mem_insert_self s₂ T₂)⟩

omit [DecidableEq A] in
/-- Every rational subset is contained in `Spa A A⁺`. -/
theorem IsRationalSubset.subset_spa {U : Set (Spv A)} (hU : IsRationalSubset U) :
    U ⊆ Spa A A⁺ := by
  obtain ⟨_, _, rfl⟩ := hU; exact rationalOpen_subset_spa

/-! ### Openness of rational subsets -/

omit [TopologicalSpace A] [PlusSubring A] [DecidableEq A] in
/-- Each basic open set `Spv(A)(f/s)` is open. -/
theorem isOpen_basicOpen (f s : A) : IsOpen (basicOpen f s) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, s, rfl⟩

omit [DecidableEq A] in
/-- Rational subsets are open in `Spa(A, A⁺)` (Theorem 7.35(2)). -/
theorem rationalOpen_isOpen (T : Finset A) (s : A) :
    IsOpen (Subtype.val ⁻¹' rationalOpen T s : Set ↥(Spa A A⁺)) := by
  classical
  have heq : Subtype.val ⁻¹' rationalOpen T s =
      ⋂ t ∈ insert s T, (Subtype.val ⁻¹' basicOpen t s : Set ↥(Spa A A⁺)) := by
    ext ⟨v, hv⟩
    simp only [Set.mem_preimage, Set.mem_iInter, Finset.mem_insert,
      rationalOpen, basicOpen, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, hvT, hvs⟩ t (rfl | ht)
      · exact ⟨(v.vle_total t t).elim id id, hvs⟩
      · exact ⟨hvT t ht, hvs⟩
    · intro h
      exact ⟨hv, fun t ht ↦ (h t (Or.inr ht)).1, (h s (Or.inl rfl)).2⟩
  rw [heq]
  exact isOpen_biInter_finset fun t _ ↦ (isOpen_basicOpen t s).preimage continuous_subtype_val

omit [DecidableEq A] in
/-- A rational subset is open in `Spa(A, A⁺)`. -/
theorem IsRationalSubset.isOpen {U : Set (Spv A)} (hU : IsRationalSubset U) :
    IsOpen (Subtype.val ⁻¹' U : Set ↥(Spa A A⁺)) := by
  classical
  obtain ⟨T, s, rfl⟩ := hU
  exact rationalOpen_isOpen T s

end ValuationSpectrum
