import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Unramifiedness from the count of algebra homomorphisms

The converse of the section-count for étale algebras: a finite algebra `A` over a field
`K` with **as many** `K`-algebra homomorphisms `A →ₐ[K] K` as its dimension is split
(`A ≅ K^n` via evaluation, by Dedekind linear independence of characters), hence
formally unramified.

This is the endgame of the BB-DIFF kernel-count argument: `Γ(E[N])` over `κ̄` has `N²`
points (HasseWeil) and rank `N²` (BB-DEG), so it is étale.
-/

universe u

open Module

/-- **Split criterion by counting characters.** If a module-finite algebra `A` over a
field `K` admits exactly `finrank K A` many `K`-algebra homomorphisms to `K`, then the
evaluation map `A → K^(A →ₐ[K] K)` is an isomorphism (Dedekind independence of
characters + dimension count), so `A` is formally unramified over `K`. -/
theorem Algebra.FormallyUnramified.of_natCard_algHom_eq_finrank
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (h : Nat.card (A →ₐ[K] K) = Module.finrank K A) :
    Algebra.FormallyUnramified K A := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨Module.subsingleton A _⟩
  have hpos : 0 < Module.finrank K A := Module.finrank_pos
  haveI hfin : Finite (A →ₐ[K] K) := by
    rcases finite_or_infinite (A →ₐ[K] K) with h' | h'
    · exact h'
    · rw [Nat.card_eq_zero_of_infinite] at h
      omega
  haveI : Fintype (A →ₐ[K] K) := Fintype.ofFinite _
  have hcard : Fintype.card (A →ₐ[K] K) = Module.finrank K A := by
    rw [← Nat.card_eq_fintype_card, h]
  -- the evaluation algebra homomorphism into the product
  set ev : A →ₐ[K] ((A →ₐ[K] K) → K) := AlgHom.pi (fun f => f) with hev
  -- Dedekind: the characters span the full dual space
  have hli : LinearIndependent K
      (AlgHom.toLinearMap : (A →ₐ[K] K) → (A →ₗ[K] K)) :=
    linearIndependent_algHom_toLinearMap K A K
  haveI : Nonempty (A →ₐ[K] K) := by
    rw [← Fintype.card_pos_iff, hcard]
    exact hpos
  have hspan : Submodule.span K
      (Set.range (AlgHom.toLinearMap : (A →ₐ[K] K) → (A →ₗ[K] K))) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    rw [hcard]
    exact (Subspace.dual_finrank_eq).symm
  -- injectivity: an element killed by all characters is killed by the whole dual
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [← Module.forall_dual_apply_eq_zero_iff K a]
    intro φ
    have hφ : φ ∈ Submodule.span K
        (Set.range (AlgHom.toLinearMap : (A →ₐ[K] K) → (A →ₗ[K] K))) := by
      rw [hspan]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨f, rfl⟩ := hψ
      exact congrFun (congrArg (fun g => (g : (A →ₐ[K] K) → K)) ha) f
    | zero => rfl
    | add ψ₁ ψ₂ _ _ h₁ h₂ => simp [h₁, h₂]
    | smul c ψ _ hψ => simp [hψ]
  -- surjectivity by dimension count (rank–nullity)
  have hsurj : Function.Surjective ev := by
    have hinj' : Function.Injective ev.toLinearMap := hinj
    have h1 : Function.Surjective ev.toLinearMap := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj hinj', Module.finrank_pi, hcard]
    exact h1
  -- `A ≅ K^n`, and the product is formally unramified
  let e : A ≃ₐ[K] ((A →ₐ[K] K) → K) := AlgEquiv.ofBijective ev ⟨hinj, hsurj⟩
  haveI : Algebra.FormallyUnramified K ((A →ₐ[K] K) → K) := inferInstance
  exact Algebra.FormallyUnramified.of_surjective e.symm.toAlgHom e.symm.surjective
