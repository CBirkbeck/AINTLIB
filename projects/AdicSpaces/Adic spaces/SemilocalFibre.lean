/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicNakayama
import Mathlib.RingTheory.Artinian.Ring

/-!
# Semilocal fibre splitting of adic completions

([hrw-decomposition] HRW-5(iii) / leaf 14 core.) For an ideal `Q` with
Artinian quotient, the `Q`-adic completion splits as the product of the
completions at the finitely many maximal ideals over `Q`: the maximals of
`C⧸Q` are finite, their intersection (the Jacobson radical) is nilpotent,
and `AdicCompletion.semilocalSplit` applies.
-/

@[expose] public section

open scoped Classical

section SemilocalFibre

variable {C : Type*} [CommRing C] (Q : Ideal C) [IsArtinianRing (C ⧸ Q)]

/-- The (finite) index of maximal ideals of the fibre. -/
noncomputable def fibreMaximals : Type _ :=
  {J : Ideal (C ⧸ Q) // J.IsMaximal}

noncomputable instance : Fintype (fibreMaximals Q) :=
  (IsArtinianRing.setOf_isMaximal_finite (R := C ⧸ Q)).fintype

/-- The maximal ideals of `C` over `Q`, indexed by the fibre maximals. -/
noncomputable def overMaximal (𝔫 : fibreMaximals Q) : Ideal C :=
  Ideal.comap (Ideal.Quotient.mk Q) 𝔫.1

theorem overMaximal_isMaximal (𝔫 : fibreMaximals Q) :
    (overMaximal Q 𝔫).IsMaximal :=
  haveI := 𝔫.2
  Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem le_overMaximal (𝔫 : fibreMaximals Q) : Q ≤ overMaximal Q 𝔫 := by
  intro x hx
  show Ideal.Quotient.mk Q x ∈ 𝔫.1
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact 𝔫.1.zero_mem

theorem overMaximal_injective :
    Function.Injective (overMaximal Q) := by
  intro a b hab
  refine Subtype.ext ?_
  have h1 : ∀ J : fibreMaximals Q,
      (overMaximal Q J).map (Ideal.Quotient.mk Q) = J.1 :=
    fun J => Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [← h1 a, ← h1 b, hab]

theorem pairwise_coprime_overMaximal :
    Pairwise fun a b : fibreMaximals Q =>
      IsCoprime (overMaximal Q a) (overMaximal Q b) := by
  intro a b hab
  exact Ideal.isCoprime_iff_sup_eq.mpr
    ((overMaximal_isMaximal Q a).coprime_of_ne (overMaximal_isMaximal Q b)
      (fun h => hab (overMaximal_injective Q h)))

/-- Nilpotence of the intersection modulo `Q` (Jacobson radical of the
Artinian fibre). -/
theorem exists_pow_iInf_overMaximal_le :
    ∃ e : ℕ, 1 ≤ e ∧ (⨅ 𝔫, overMaximal Q 𝔫) ^ e ≤ Q := by
  obtain ⟨e, he⟩ := IsArtinianRing.isNilpotent_jacobson_bot
    (R := C ⧸ Q)
  refine ⟨e + 1, Nat.le_add_left 1 e, ?_⟩
  have hjac : (Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) ^ (e + 1) = ⊥ := by
    rw [pow_succ']
    rw [show (Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) ^ e = ⊥ from he]
    rw [Ideal.mul_bot]
  have hinf : (⨅ 𝔫, overMaximal Q 𝔫) ≤
      Ideal.comap (Ideal.Quotient.mk Q)
        (Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJmax⟩
    exact Ideal.mem_iInf.mp hx ⟨J, hJmax⟩
  calc (⨅ 𝔫, overMaximal Q 𝔫) ^ (e + 1) ≤
      (Ideal.comap (Ideal.Quotient.mk Q)
        (Ideal.jacobson (⊥ : Ideal (C ⧸ Q)))) ^ (e + 1) :=
        pow_le_pow_left' hinf (e + 1)
    _ ≤ Ideal.comap (Ideal.Quotient.mk Q)
        ((Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) ^ (e + 1)) :=
        Ideal.le_comap_pow _ (e + 1)
    _ = Q := by
        rw [hjac]
        ext x
        rw [Ideal.mem_comap]
        show Ideal.Quotient.mk Q x ∈ (⊥ : Ideal (C ⧸ Q)) ↔ x ∈ Q
        rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]

/-- **The fibre splitting of the adic completion**: the `Q`-adic completion
is the product of the completions at the maximal ideals over `Q`. -/
noncomputable def AdicCompletion.fibreSplit :
    AdicCompletion Q C ≃+* ∀ 𝔫 : fibreMaximals Q,
      AdicCompletion (overMaximal Q 𝔫) C :=
  AdicCompletion.semilocalSplit Q (overMaximal Q)
    (pairwise_coprime_overMaximal Q) (le_overMaximal Q)
    (exists_pow_iInf_overMaximal_le Q).choose
    (exists_pow_iInf_overMaximal_le Q).choose_spec.1
    (exists_pow_iInf_overMaximal_le Q).choose_spec.2

end SemilocalFibre
