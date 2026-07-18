/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
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

open AlgebraicGeometry CategoryTheory Limits

section Schemes

variable {k : Type u} [Field k] [IsSepClosed k]

private def sectionsEquivOfIso {Y Z W : Scheme.{u}} (e : Y ≅ Z) (f : Y ⟶ W) :
    { s : W ⟶ Y // s ≫ f = 𝟙 W } ≃ { t : W ⟶ Z // t ≫ (e.inv ≫ f) = 𝟙 W } where
  toFun s := ⟨s.1 ≫ e.hom, by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact s.2⟩
  invFun t := ⟨t.1 ≫ e.inv, by rw [Category.assoc]; exact t.2⟩
  left_inv s := Subtype.ext (by simp)
  right_inv t := Subtype.ext (by simp)

private noncomputable def sectionsSpecEquivRetractions {R A : CommRingCat.{u}} (ψ : R ⟶ A) :
    { t : Spec R ⟶ Spec A // t ≫ Spec.map ψ = 𝟙 (Spec R) } ≃
      { χ : A ⟶ R // ψ ≫ χ = 𝟙 R } where
  toFun t := ⟨Spec.preimage t.1, Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, t.2, Spec.map_id])⟩
  invFun χ := ⟨Spec.map χ.1, by rw [← Spec.map_comp, χ.2, Spec.map_id]⟩
  left_inv t := Subtype.ext (Spec.map_preimage t.1)
  right_inv χ := Subtype.ext (Spec.preimage_map χ.1)

private def retractionsEquivAlgHom {A : CommRingCat.{u}} (ψ : CommRingCat.of k ⟶ A)
    [Algebra k ↑A] (hAlg : algebraMap k ↑A = ψ.hom) :
    { χ : A ⟶ CommRingCat.of k // ψ ≫ χ = 𝟙 (CommRingCat.of k) } ≃ (↑A →ₐ[k] k) where
  toFun χ :=
    { toRingHom := χ.1.hom
      commutes' := fun r => by
        have h := congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of k =>
          q.hom r) χ.2
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
          RingHom.id_apply] at h
        rw [hAlg]
        exact h }
  invFun φ := ⟨CommRingCat.ofHom φ.toRingHom, by
    ext r
    have h := φ.commutes r
    rw [hAlg] at h
    simpa using h⟩
  left_inv χ := Subtype.ext (by ext; rfl)
  right_inv φ := by ext; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-B6d)** A finite étale scheme over the spectrum of a separably closed field has
exactly `finrank` many sections. -/
theorem natCard_sections_eq_finrank {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [Etale f] (x₀ : ↑(Spec (CommRingCat.of k))) :
    Nat.card { s : Spec (CommRingCat.of k) ⟶ X // s ≫ f = 𝟙 (Spec (CommRingCat.of k)) }
      = f.finrank x₀ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  set ψ : CommRingCat.of k ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f) with hψdef
  have hψ : Spec.map ψ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  letI : Algebra k ↑Γ(X, ⊤) := ψ.hom.toAlgebra
  have hAlg : algebraMap k ↑Γ(X, ⊤) = ψ.hom := rfl
  haveI hE : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
  haveI hF : IsFinite (Spec.map ψ) := by
    rw [hψ]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite X.isoSpec.inv f).mpr
      inferInstance
  have hRE : RingHom.Etale ψ.hom := HasRingHomProperty.Spec_iff.mp hE
  have hRF : RingHom.Finite ψ.hom := (IsFinite.SpecMap_iff ψ).mp hF
  haveI : Algebra.Etale k ↑Γ(X, ⊤) := RingHom.etale_algebraMap.mp hRE
  haveI : Module.Finite k ↑Γ(X, ⊤) := hRF
  have hcard :
      Nat.card { s : Spec (CommRingCat.of k) ⟶ X //
          s ≫ f = 𝟙 (Spec (CommRingCat.of k)) } =
        Nat.card (↑Γ(X, ⊤) →ₐ[k] k) := by
    refine Nat.card_congr (((sectionsEquivOfIso X.isoSpec f).trans
      (Equiv.subtypeEquivRight fun t => ?_)).trans
      ((sectionsSpecEquivRetractions ψ).trans (retractionsEquivAlgHom ψ hAlg)))
    rw [hψ]
  rw [hcard, natCard_algHom_eq_finrank k ↑Γ(X, ⊤)]
  have h1 : f.finrank x₀ = (X.isoSpec.inv ≫ f).finrank x₀ :=
    (congrFun (Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.inv f) x₀).symm
  have h2 : (X.isoSpec.inv ≫ f).finrank x₀ = (Spec.map ψ).finrank x₀ := by rw [hψ]
  have h3 : (Spec.map ψ).finrank x₀ = Module.rankAtStalk (R := k) ↑Γ(X, ⊤) x₀ :=
    Scheme.Hom.finrank_SpecMap_algebraMap k ↑Γ(X, ⊤) x₀
  have h4 : Module.rankAtStalk (R := k) ↑Γ(X, ⊤) x₀ = Module.finrank k ↑Γ(X, ⊤) := by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [h1, h2, h3, h4]

end Schemes

/-- `Spec L`-valued points of `Spec A` over `Spec k` are `k`-algebra homomorphisms
`A →ₐ[k] L`. -/
noncomputable def specPointsEquivAlgHom (k A L : Type u) [CommRing k] [CommRing A]
    [CommRing L] [Algebra k A] [Algebra k L] :
    { h : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) //
        h ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L)) } ≃ (A →ₐ[k] L) where
  toFun h :=
    { toRingHom := (Spec.preimage h.1).hom
      commutes' := fun r => by
        have htri : CommRingCat.ofHom (algebraMap k A) ≫ Spec.preimage h.1 =
            CommRingCat.ofHom (algebraMap k L) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage]
          exact h.2
        have h2 := congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of L => q.hom r) htri
        simpa using h2 }
  invFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact φ.commutes r⟩
  left_inv h := Subtype.ext (Spec.map_preimage h.1)
  right_inv φ := by
    refine AlgHom.ext fun a => ?_
    exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of L => q.hom a)
      (Spec.preimage_map _)

end ModularCurves
