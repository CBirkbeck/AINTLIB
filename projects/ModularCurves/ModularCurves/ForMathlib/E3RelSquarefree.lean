/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Squarefree.Basic

/-!
# The flex relation `β³ − (β+γ)³` is squarefree ([T-E15-NORM] Stage C heart)

Over a UFD `A` with `3` invertible, the `ℰ₃` flex relation
`e3Rel = X₀³ − (X₀+X₁)³ = −X₁·(3X₀² + 3X₀X₁ + X₁²)` is a **squarefree** element of
`A[X₀, X₁]`. Consequently (`Squarefree.isRadical` + `isRadical_iff_span_singleton` +
`Ideal.isRadical_iff_quotient_reduced`) the flex-locus ring `A[β,γ]/(e3Rel)` — the
`E3Quotient` — is **reduced**, which is what the field-points collision principle
(`hom_ext_of_forall_specPoint`) needs to lift the fibrewise `3`-torsion killing of the
universal `ℰ₃` sections to the section level over the universal base.

The proof is derivative-based but discriminant-free: if `p² ∣ f := X₁·S` then `p`
divides both partial derivatives `∂₀f = 3X₁(2X₀+X₁)` and `∂₁f = 3(X₀+X₁)²`; a prime
factor `r` of `p` then divides `X₁` or `2X₀+X₁` (primality), and divides `X₀+X₁`.
In the first case `X₁² ∣ f` forces `X₁ ∣ S`, contradicting `S(X,0) = 3X² ≠ 0`;
in the second `r ∣ (2X₀+X₁)−(X₀+X₁) = X₀` forces `X₀ ∣ f`, contradicting
`f(0,X) = X³ ≠ 0`. Only `3 ∈ Aˣ` and the UFD structure are used.
-/

open MvPolynomial

namespace ModularCurves

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- **(Stage C heart ★)** The product form `X₁·(3X₀²+3X₀X₁+X₁²)` of (minus) the flex
relation is squarefree over a UFD with `3` invertible. -/
theorem squarefree_e3RelMul (h3 : IsUnit (3 : A)) :
    Squarefree ((X 1) * (3 * (X 0) ^ 2 + 3 * (X 0) * (X 1) + (X 1) ^ 2) :
      MvPolynomial (Fin 2) A) := by
  have h3ne : (3 : A) ≠ 0 := h3.ne_zero
  set S : MvPolynomial (Fin 2) A := 3 * (X 0) ^ 2 + 3 * (X 0) * (X 1) + (X 1) ^ 2
    with hS
  set f : MvPolynomial (Fin 2) A := (X 1) * S with hf
  intro p hp
  by_contra hpu
  -- the evaluations `X₀ ↦ X, X₁ ↦ 0` and `X₀ ↦ 0, X₁ ↦ X` into `A[X]`
  set evγ0 : MvPolynomial (Fin 2) A →+* Polynomial A :=
    (eval₂Hom Polynomial.C ![Polynomial.X, 0]) with hevγ0
  set evβ0 : MvPolynomial (Fin 2) A →+* Polynomial A :=
    (eval₂Hom Polynomial.C ![0, Polynomial.X]) with hevβ0
  -- `f(0, X) = X³`, so `f ≠ 0`
  have hevf : evβ0 f = Polynomial.X ^ 3 := by
    simp only [hevβ0, hf, hS, map_mul, map_add, map_pow, map_ofNat, eval₂Hom_X',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have hfne : f ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hevf
    exact pow_ne_zero 3 Polynomial.X_ne_zero hevf.symm
  have hpne : p ≠ 0 := by
    rintro rfl
    have h0 : (0 : MvPolynomial (Fin 2) A) ∣ f := by simpa using hp
    exact hfne (zero_dvd_iff.mp h0)
  -- a prime factor of `p`
  obtain ⟨r, hrirr, hrp⟩ := WfDvdMonoid.exists_irreducible_factor hpu hpne
  have hrprime : Prime r := UniqueFactorizationMonoid.irreducible_iff_prime.mp hrirr
  have hpf : p ∣ f := (dvd_mul_right p p).trans hp
  -- `p` divides both partial derivatives
  obtain ⟨q, hq⟩ := hp
  have hkey : ∀ i : Fin 2, p ∣ pderiv i f := by
    intro i
    rw [hq, pderiv_mul, pderiv_mul]
    exact dvd_add
      (dvd_mul_of_dvd_left
        (dvd_add (Dvd.intro_left (pderiv i p) rfl) (Dvd.intro (pderiv i p) rfl)) q)
      (dvd_mul_of_dvd_left (dvd_mul_right p p) _)
  -- compute them: `∂₀f = 3X₁(2X₀+X₁)`, `∂₁f = 3(X₀+X₁)²`
  have hC3 : (3 : MvPolynomial (Fin 2) A) = C (3 : A) := (map_ofNat C 3).symm
  have hX00 : pderiv (0 : Fin 2) (X 0 : MvPolynomial (Fin 2) A) = 1 := pderiv_X_self 0
  have hX01 : pderiv (0 : Fin 2) (X 1 : MvPolynomial (Fin 2) A) = 0 :=
    pderiv_X_of_ne (by decide)
  have hX10 : pderiv (1 : Fin 2) (X 0 : MvPolynomial (Fin 2) A) = 0 :=
    pderiv_X_of_ne (by decide)
  have hX11 : pderiv (1 : Fin 2) (X 1 : MvPolynomial (Fin 2) A) = 1 := pderiv_X_self 1
  have hSprod : f = (X 1) * (C (3 : A) * ((X 0) * (X 0)) + C (3 : A) * ((X 0) * (X 1))
      + (X 1) * (X 1)) := by
    rw [hf, hS, hC3]; ring
  have hd0 : pderiv (0 : Fin 2) f = 3 * ((X 1) * (2 * (X 0) + (X 1))) := by
    rw [hSprod]
    simp only [pderiv_mul, map_add, pderiv_C, hX00, hX01]
    rw [← hC3]
    ring
  have hd1 : pderiv (1 : Fin 2) f = 3 * (((X 0) + (X 1)) ^ 2) := by
    rw [hSprod]
    simp only [pderiv_mul, map_add, pderiv_C, hX10, hX11]
    rw [← hC3]
    ring
  -- strip the unit `3`
  have h3u : IsUnit (3 : MvPolynomial (Fin 2) A) := by
    have h := h3.map (C : A →+* MvPolynomial (Fin 2) A)
    rwa [map_ofNat] at h
  obtain ⟨v, hv⟩ := h3u.exists_left_inv
  have hstrip : ∀ g : MvPolynomial (Fin 2) A, p ∣ 3 * g → p ∣ g := by
    intro g hg
    have h1 : p ∣ v * (3 * g) := hg.mul_left v
    rwa [← mul_assoc, hv, one_mul] at h1
  have hpd0 : p ∣ (X 1) * (2 * (X 0) + (X 1)) := hstrip _ (hd0 ▸ hkey 0)
  have hpd1 : p ∣ ((X 0) + (X 1)) ^ 2 := hstrip _ (hd1 ▸ hkey 1)
  -- the prime `r` inherits them
  have hr1 : r ∣ (X 1) * (2 * (X 0) + (X 1)) := hrp.trans hpd0
  have hrsum : r ∣ (X 0) + (X 1) := hrprime.dvd_of_dvd_pow (hrp.trans hpd1)
  have hX0 : Prime (X 0 : MvPolynomial (Fin 2) A) := MvPolynomial.X_prime
  have hX1 : Prime (X 1 : MvPolynomial (Fin 2) A) := MvPolynomial.X_prime
  rcases hrprime.2.2 _ _ hr1 with hrγ | hrlin
  · -- case `r ∣ X₁`: then `X₁² ∣ f = X₁·S` forces `X₁ ∣ S`; but `S(X, 0) = 3X²`
    have hassoc : Associated r (X 1 : MvPolynomial (Fin 2) A) :=
      hrprime.associated_of_dvd hX1 hrγ
    have hX1sq : (X 1 : MvPolynomial (Fin 2) A) * (X 1) ∣ f := by
      have h1 : r * r ∣ p * p := mul_dvd_mul hrp hrp
      have h2 : Associated (r * r) ((X 1 : MvPolynomial (Fin 2) A) * (X 1)) :=
        hassoc.mul_mul hassoc
      exact (h2.symm.dvd.trans h1).trans (hq ▸ dvd_mul_right _ _)
    have hX1S : (X 1 : MvPolynomial (Fin 2) A) ∣ S := by
      rw [hf] at hX1sq
      exact (mul_dvd_mul_iff_left hX1.ne_zero).mp hX1sq
    obtain ⟨t, ht⟩ := hX1S
    have hevS : evγ0 S = 3 * Polynomial.X ^ 2 := by
      simp only [hevγ0, hS, map_add, map_mul, map_pow, map_ofNat, eval₂Hom_X',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    have hX1ev : evγ0 (X 1 : MvPolynomial (Fin 2) A) = 0 := by
      rw [hevγ0, eval₂Hom_X']
      simp
    have hev0 : evγ0 S = 0 := by
      rw [ht, map_mul, hX1ev, zero_mul]
    rw [hevS] at hev0
    have h32 : (3 : A) = 0 := by
      have h := congrArg (fun g => Polynomial.coeff g 2) hev0
      simpa using h
    exact h3ne h32
  · -- case `r ∣ 2X₀+X₁`: with `r ∣ X₀+X₁` get `r ∣ X₀`, so `X₀ ∣ f`; but `f(0,X) = X³`
    have hrβ : r ∣ (X 0 : MvPolynomial (Fin 2) A) := by
      have h := dvd_sub hrlin hrsum
      rwa [show 2 * (X 0 : MvPolynomial (Fin 2) A) + (X 1) - ((X 0) + (X 1)) = X 0
        by ring] at h
    have hassoc : Associated r (X 0 : MvPolynomial (Fin 2) A) :=
      hrprime.associated_of_dvd hX0 hrβ
    have hX0f : (X 0 : MvPolynomial (Fin 2) A) ∣ f := hassoc.symm.dvd.trans (hrp.trans hpf)
    obtain ⟨t, ht⟩ := hX0f
    have hX0ev : evβ0 (X 0 : MvPolynomial (Fin 2) A) = 0 := by
      rw [hevβ0, eval₂Hom_X']
      simp
    have hev0 : evβ0 f = 0 := by
      rw [ht, map_mul, hX0ev, zero_mul]
    rw [hevf] at hev0
    exact pow_ne_zero 3 Polynomial.X_ne_zero hev0

/-- **(Stage C ★)** The `ℰ₃` flex relation `X₀³ − (X₀+X₁)³` is squarefree over a UFD
with `3` invertible: it is `−1` times the product form. -/
theorem squarefree_e3Rel (h3 : IsUnit (3 : A)) :
    Squarefree ((X 0) ^ 3 - ((X 0) + (X 1)) ^ 3 : MvPolynomial (Fin 2) A) := by
  have hassoc : Associated
      ((X 1) * (3 * (X 0) ^ 2 + 3 * (X 0) * (X 1) + (X 1) ^ 2) : MvPolynomial (Fin 2) A)
      ((X 0) ^ 3 - ((X 0) + (X 1)) ^ 3 : MvPolynomial (Fin 2) A) := by
    refine ⟨-1, ?_⟩
    simp only [Units.val_neg, Units.val_one]
    ring
  exact hassoc.squarefree_iff.mp (squarefree_e3RelMul h3)

/-- **(Stage C ★★, the collision-principle input)** The flex-locus ring
`A[X₀,X₁]/(X₀³−(X₀+X₁)³)` is **reduced** over a UFD with `3` invertible — this is
`IsReduced (E3Quotient A)` for `A = ℤ[1/3]`, which `hom_ext_of_forall_specPoint` needs
(after localization, which preserves reducedness) to lift the fibrewise `3`-torsion
killing of the universal `ℰ₃` sections to the section level. -/
theorem isReduced_e3RelQuotient (h3 : IsUnit (3 : A)) :
    IsReduced (MvPolynomial (Fin 2) A ⧸
      Ideal.span {((X 0) ^ 3 - ((X 0) + (X 1)) ^ 3 : MvPolynomial (Fin 2) A)}) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp (squarefree_e3Rel h3).isRadical)

end ModularCurves
