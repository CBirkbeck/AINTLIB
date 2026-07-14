/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Hom-duality for finite split algebras

For finite split algebras over a field `k`, the functor `A ↦ (A →ₐ[k] k)` is a
contravariant equivalence onto finite sets in the ways needed for the fibrewise-iso
criterion (`[C5B-2 L2b-ii]`):

* `AlgHom.eq_evalAlgHom_of_pi` — every `k`-point of `ι → k` is a coordinate evaluation.
* `Algebra.IsFiniteSplit.eq_zero_of_forall_algHom_eq_zero` — `k`-points separate elements.
* `Algebra.IsFiniteSplit.bijective_of_precomp_bijective` — an algebra map of finite split
  algebras whose dual map on `k`-points is bijective is itself bijective.
-/

open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-- Every `k`-algebra map `(ι → k) →ₐ[k] k` is evaluation at a (unique) coordinate:
its values on the orthogonal idempotent basis are idempotents summing to `1`, so exactly
one is `1`. -/
theorem AlgHom.eq_evalAlgHom_of_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → k) →ₐ[k] k) : ∃ i, f = Pi.evalAlgHom k (fun _ => k) i := by
  -- the idempotent images
  have hidem : ∀ i, f (Pi.single i 1) = 0 ∨ f (Pi.single i 1) = 1 := by
    intro i
    have h2 : f (Pi.single i 1) * f (Pi.single i 1) = f (Pi.single i 1) := by
      rw [← map_mul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    have h3 : f (Pi.single i 1) * (f (Pi.single i 1) - 1) = 0 := by
      rw [mul_sub, mul_one, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have horth : ∀ i j, i ≠ j → f (Pi.single i 1) * f (Pi.single j 1) = 0 := by
    intro i j hij
    rw [← map_mul]
    have : (Pi.single i 1 : ι → k) * Pi.single j 1 = 0 := by
      ext m
      by_cases hm : m = i
      · subst hm; simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, hm]
    rw [this, map_zero]
  have hsum : ∑ i, f (Pi.single i 1) = 1 := by
    rw [← map_sum]
    have hsum1 : (∑ i : ι, Pi.single i (1 : k)) = (1 : ι → k) := by
      ext j
      simp [Pi.single_apply]
    rw [hsum1, map_one]
  -- exactly one idempotent maps to 1
  have hone : ∃ i, f (Pi.single i 1) = 1 := by
    by_contra hno
    push_neg at hno
    have hz : ∀ i, f (Pi.single i 1) = 0 := fun i =>
      (hidem i).resolve_right (hno i)
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi⟩ := hone
  refine ⟨i, ?_⟩
  ext x
  -- decompose x on the idempotent basis
  have hx : x = ∑ j, x j • Pi.single j (1 : k) := by
    ext m
    simp [Pi.single_apply]
  have hfx : f x = ∑ j, x j * f (Pi.single j 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have hzero : ∀ j, j ≠ i → f (Pi.single j 1) = 0 := by
    intro j hj
    rcases hidem j with h | h
    · exact h
    · exfalso
      have := horth j i hj
      rw [h, hi, one_mul] at this
      exact one_ne_zero this
  rw [hfx, Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, mul_zero])
    (fun hni => absurd (Finset.mem_univ i) hni), hi, mul_one]
  rfl

namespace Algebra.IsFiniteSplit

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- `k`-points separate the elements of a finite split algebra. -/
theorem eq_zero_of_forall_algHom_eq_zero [Algebra.IsFiniteSplit k A] {x : A}
    (hx : ∀ f : A →ₐ[k] k, f x = 0) : x = 0 := by
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k A
  have hcoord : ∀ i, (Pi.evalAlgHom k (fun _ => k) i).comp e.toAlgHom x = 0 := fun i =>
    hx _
  have : e x = 0 := by
    ext i
    exact hcoord i
  have := congrArg e.symm this
  rwa [e.symm_apply_apply, map_zero] at this

/-- The `k`-point count of a finite split algebra is its `k`-dimension. -/
theorem card_algHom [Algebra.IsFiniteSplit k A] :
    Nat.card (A →ₐ[k] k) = Module.finrank k A := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k A
  -- transport the point set along `e`
  have hEquiv : (A →ₐ[k] k) ≃ ((Fin m → k) →ₐ[k] k) :=
    { toFun := fun f => f.comp e.symm.toAlgHom
      invFun := fun f => f.comp e.toAlgHom
      left_inv := fun f => by
        ext x
        simp
      right_inv := fun f => by
        ext x
        simp }
  have hPi : ((Fin m → k) →ₐ[k] k) ≃ Fin m :=
    { toFun := fun f => (AlgHom.eq_evalAlgHom_of_pi (ι := Fin m) f).choose
      invFun := fun i => Pi.evalAlgHom k (fun _ => k) i
      left_inv := fun f =>
        ((AlgHom.eq_evalAlgHom_of_pi (ι := Fin m) f).choose_spec).symm
      right_inv := fun i => by
        have h := (AlgHom.eq_evalAlgHom_of_pi (ι := Fin m)
          (Pi.evalAlgHom k (fun _ : Fin m => k) i)).choose_spec
        by_contra hne
        have hval := congrArg (fun g : (Fin m → k) →ₐ[k] k => g (Pi.single i 1)) h
        have h1 : (Pi.evalAlgHom k (fun _ : Fin m => k) i) (Pi.single i 1) = 1 := by
          simp
        have h0 : (Pi.evalAlgHom k (fun _ : Fin m => k)
            ((AlgHom.eq_evalAlgHom_of_pi (ι := Fin m)
              (Pi.evalAlgHom k (fun _ : Fin m => k) i)).choose)) (Pi.single i 1) = 0 := by
          simp only [Pi.evalAlgHom_apply, Pi.single_apply]
          exact if_neg (fun hc => hne hc)
        exact one_ne_zero (h1.symm.trans (hval.trans h0)) }
  rw [Nat.card_congr (hEquiv.trans hPi), Nat.card_eq_fintype_card, Fintype.card_fin,
    e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]

/-- **The hom-duality criterion**: an algebra map of finite split algebras whose dual
map on `k`-points is bijective is itself bijective. -/
theorem bijective_of_precomp_bijective [Algebra.IsFiniteSplit k A]
    [Algebra.IsFiniteSplit k B] (ψ : A →ₐ[k] B)
    (h : Function.Bijective fun g : B →ₐ[k] k => g.comp ψ) :
    Function.Bijective ψ := by
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have hz : ∀ f : A →ₐ[k] k, f (x - y) = 0 := by
      intro f
      obtain ⟨g, hg⟩ := h.2 f
      rw [← hg]
      show g (ψ (x - y)) = 0
      rw [map_sub, hxy, sub_self, map_zero]
    exact sub_eq_zero.mp (eq_zero_of_forall_algHom_eq_zero hz)
  refine ⟨hinj, ?_⟩
  haveI : Module.Finite k A := inferInstance
  haveI : Module.Finite k B := inferInstance
  have hrank : Module.finrank k A = Module.finrank k B := by
    rw [← card_algHom (k := k) (A := A), ← card_algHom (k := k) (A := B)]
    exact (Nat.card_congr (Equiv.ofBijective _ h)).symm
  have hlin := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := ψ.toLinearMap) hrank).mp hinj
  exact hlin

end Algebra.IsFiniteSplit

/-- Bijectivity of a linear map over a field descends from any field extension:
`ψ ⊗ K` bijective implies `ψ` bijective (faithful flatness of `K/k`). -/
theorem LinearMap.bijective_of_bijective_lTensor_field {k : Type u} [Field k]
    (K : Type u) [Field K] [Algebra k K] {M N : Type u}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (φ : M →ₗ[k] N) (h : Function.Bijective (φ.lTensor K)) :
    Function.Bijective φ := by
  haveI : Module.FaithfullyFlat k K := inferInstance
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K φ).mp h
