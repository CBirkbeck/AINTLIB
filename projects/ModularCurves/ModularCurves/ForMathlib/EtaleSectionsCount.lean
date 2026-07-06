import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Counting points of finite étale algebras over a separably closed field

For a formally étale, essentially-finite-type algebra `A` over a separably closed field
`K`, the `K`-algebra homomorphisms `A →ₐ[K] K` biject with `PrimeSpectrum A`
(`algHomEquivPrimeSpectrum`), and their number is `Module.finrank K A`
(`natCard_algHom_eq_finrank`). This is the algebraic heart of "a finite étale scheme of
rank `r` over `Spec k̄` has exactly `r` points" (ticket T-B6d; scheme side in
`EllipticCurve/TorsionFibre.lean`). Upstream candidate: `Mathlib.RingTheory.Etale.Field`.

Engine: mathlib's `Algebra.FormallyEtale.equivPiOfIsSepClosed : A ≃ₐ[K] (PrimeSpectrum A → K)`
together with its `_comap` and `_self_apply` lemmas.
-/

universe u

open Algebra Algebra.FormallyEtale

namespace ModularCurves

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A] [EssFiniteType K A]
  [FormallyEtale K A] [IsSepClosed K]

private lemma primeSpectrum_ext_of_forall_equivPi {q₁ q₂ : PrimeSpectrum A}
    (h : ∀ x, equivPiOfIsSepClosed K A x q₁ = equivPiOfIsSepClosed K A x q₂) :
    q₁ = q₂ := by
  by_contra hne
  classical
  have h1 := h ((equivPiOfIsSepClosed K A).symm (Pi.single q₁ 1))
  rw [show equivPiOfIsSepClosed K A ((equivPiOfIsSepClosed K A).symm (Pi.single q₁ 1)) =
      Pi.single q₁ 1 from (equivPiOfIsSepClosed K A).apply_symm_apply _] at h1
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h1
  exact one_ne_zero h1

/-- Algebra homomorphisms from a formally étale algebra over a separably closed field
to the base field biject with the prime spectrum. -/
noncomputable def algHomEquivPrimeSpectrum : (A →ₐ[K] K) ≃ PrimeSpectrum A where
  toFun ψ := (default : PrimeSpectrum K).comap ψ
  invFun p := (Pi.evalAlgHom K (fun _ => K) p).comp (equivPiOfIsSepClosed K A)
  left_inv ψ := by
    ext x
    show equivPiOfIsSepClosed K A x ((default : PrimeSpectrum K).comap ψ) = ψ x
    rw [equivPiOfIsSepClosed_comap ψ x default, equivPiOfIsSepClosed_self_apply]
  right_inv p := by
    refine primeSpectrum_ext_of_forall_equivPi K A fun x => ?_
    have hc := equivPiOfIsSepClosed_comap
      ((Pi.evalAlgHom K (fun _ => K) p).comp (equivPiOfIsSepClosed K A).toAlgHom) x
      (default : PrimeSpectrum K)
    rw [equivPiOfIsSepClosed_self_apply] at hc
    exact hc.trans rfl

/-- A formally étale, essentially-finite-type algebra over a separably closed field has
exactly `finrank` many homomorphisms to the base field. -/
theorem natCard_algHom_eq_finrank : Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  haveI := Algebra.FormallyUnramified.finite_of_free K A
  haveI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  haveI : Finite (PrimeSpectrum A) :=
    Finite.of_equiv _ IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm
  classical
  haveI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  rw [Nat.card_congr (algHomEquivPrimeSpectrum K A),
    (equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

end ModularCurves
