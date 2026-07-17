/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.Projective
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Rank rigidity for surjections of finite projective modules

**[KM-W0 / T-D8 ⟸ / RANK-RIGIDITY] ForMathlib brick (candidate mathlib PR).**
A surjective linear map between finite projective modules with equal rank at every
prime is bijective: the kernel is a finite projective direct summand of rank zero
everywhere, hence subsingleton. This is the module engine behind KM 1.10.2 ("a closed
subscheme of a finite flat scheme of the same constant rank is the whole scheme") —
the scheme-level statement reduces to this over affines.
-/

universe u

namespace ModularCurves

open Module

/-- A surjective linear map between finite projective modules of equal rank at every
prime is bijective. -/
theorem bijective_of_surjective_of_rankAtStalk_eq {R A B : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B]
    (φ : A →ₗ[R] B) (hsurj : Function.Surjective φ)
    (hrank : Module.rankAtStalk (R := R) A = Module.rankAtStalk (R := R) B) :
    Function.Bijective φ := by
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  have hσa : ∀ b, φ (σ b) = b := fun b => DFunLike.congr_fun hσ b
  -- the splitting equivalence `A ≃ ker φ × B`
  let e : A ≃ₗ[R] (LinearMap.ker φ) × B :=
    { toFun := fun a => (⟨a - σ (φ a), by
        rw [LinearMap.mem_ker, map_sub, hσa, sub_self]⟩, φ a)
      invFun := fun kb => kb.1.1 + σ kb.2
      left_inv := fun a => by simp
      right_inv := fun kb => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · have hk : φ kb.1.1 = 0 := kb.1.2
          simp [hk, hσa]
        · have hk : φ kb.1.1 = 0 := kb.1.2
          simp [hk, hσa]
      map_add' := fun a₁ a₂ => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_add, Prod.fst_add, Submodule.coe_add]
          abel
        · simp
      map_smul' := fun r a => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_smul, RingHom.id_apply, Prod.smul_fst, SetLike.val_smul]
          rw [smul_sub]
        · simp }
  -- the kernel is a finite projective direct summand
  haveI hkerProj : Module.Projective R (LinearMap.ker φ) :=
    Module.Projective.of_split ((LinearMap.ker φ).subtype)
      ((LinearMap.fst R (LinearMap.ker φ) B).comp e.toLinearMap)
      (by
        ext k
        have hk : φ k.1 = 0 := k.2
        simp [e, hk])
  haveI hkerFin : Module.Finite R (LinearMap.ker φ) :=
    Module.Finite.of_surjective ((LinearMap.fst R (LinearMap.ker φ) B).comp e.toLinearMap)
      (fun k => ⟨k.1, by
        refine Subtype.ext ?_
        have hk : φ k.1 = 0 := k.2
        simp [e, hk]⟩)
  -- rank bookkeeping: `rank A = rank ker + rank B` and `rank A = rank B`
  have hprod : Module.rankAtStalk (R := R) A
      = Module.rankAtStalk (R := R) (LinearMap.ker φ) + Module.rankAtStalk (R := R) B := by
    rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  have hzero : Module.rankAtStalk (R := R) (LinearMap.ker φ) = 0 := by
    funext p
    have h1 := congrFun hprod p
    have h2 := congrFun hrank p
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
    omega
  haveI hsub : Subsingleton (LinearMap.ker φ) :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp hzero
  refine ⟨LinearMap.ker_eq_bot.mp ?_, hsurj⟩
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have := Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker φ) ⟨0, (LinearMap.ker φ).zero_mem⟩
  exact congrArg Subtype.val this

open AlgebraicGeometry CategoryTheory

/-- **[G1]** A morphism of affine schemes whose global-sections map is an isomorphism
is an isomorphism (transport along `arrowIsoSpecΓOfIsAffine`). -/
theorem isIso_of_isIso_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (h : IsIso f.appTop) : IsIso f := by
  haveI h1 : IsIso (Spec.map f.appTop) := inferInstance
  have h2 : MorphismProperty.isomorphisms Scheme (Spec.map f.appTop) :=
    (MorphismProperty.isomorphisms.iff _).mpr h1
  exact (MorphismProperty.isomorphisms.iff _).mp
    (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (arrowIsoSpecΓOfIsAffine f)).mpr h2)

/-- **[KM 1.10.2, ideal form] Rank rigidity for nested finite flat subschemes.** If
`J ≤ I` are ideal sheaves on `C/S` whose subschemes are both finite, flat, and locally
of finite presentation over `S` with the same fibre rank everywhere, then `I = J`: the
subscheme inclusion is affine-locally a surjection of finite projective modules of equal
rank, hence an isomorphism. -/
theorem eq_of_le_of_finrank_eq {C S : Scheme.{u}} (π : C ⟶ S)
    (I J : Scheme.IdealSheafData C) (hle : J ≤ I)
    [IsFinite (I.subschemeι ≫ π)] [Flat (I.subschemeι ≫ π)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ π)]
    [IsFinite (J.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)]
    [LocallyOfFinitePresentation (J.subschemeι ≫ π)]
    (hrank : ∀ s : ↑S, (I.subschemeι ≫ π).finrank s = (J.subschemeι ≫ π).finrank s) :
    I = J := by
  have hcomp : Scheme.IdealSheafData.inclusion hle ≫ J.subschemeι = I.subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι hle
  haveI hci : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle) := by
    haveI : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle ≫ J.subschemeι) := by
      rw [hcomp]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ J.subschemeι
  -- the per-affine-piece isomorphism (the module core through the Γ-dictionary)
  have hpiece : ∀ (U : S.affineOpens),
      IsIso (Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) := by
    intro U
    -- the affine pieces
    haveI hWaff : IsAffineOpen ((J.subschemeι ≫ π) ⁻¹ᵁ U.1) :=
      U.2.preimage (J.subschemeι ≫ π)
    have hW' : Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)
        = (I.subschemeι ≫ π) ⁻¹ᵁ U.1 := by
      rw [← hcomp]
      rfl
    haveI hW'aff : IsAffineOpen (Scheme.IdealSheafData.inclusion hle
        ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) := by
      rw [hW']
      exact U.2.preimage (I.subschemeι ≫ π)
    -- instances on the restricted morphisms (base change along the open pieces)
    haveI hJfin : IsFinite ((J.subschemeι ≫ π) ∣_ U.1) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict (J.subschemeι ≫ π) U.1).flip inferInstance
    haveI hJflat : Flat ((J.subschemeι ≫ π) ∣_ U.1) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict (J.subschemeι ≫ π) U.1).flip inferInstance
    haveI hJlfp : LocallyOfFinitePresentation ((J.subschemeι ≫ π) ∣_ U.1) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict (J.subschemeι ≫ π) U.1).flip inferInstance
    haveI hCIres : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict (Scheme.IdealSheafData.inclusion hle)
          ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).flip inferInstance
    -- the composite restricted morphism equals the I-side restriction
    have hcompres : Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π) =
        I.subschemeι ≫ π := by
      rw [← Category.assoc, hcomp]
    -- the generic subst-bridge: transport a base-change-stable property through
    -- `q = inclusion ≫ (J-composite)` into the restricted composite
    have hbridge : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
        (q : I.subscheme ⟶ S)
        (hq : q = Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)),
        P q → P ((Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) ∣_ U.1) := by
      rintro P _ q rfl hP
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict
          (Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) U.1).flip hP
    haveI hIfinC : IsFinite ((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)) := by
      rw [← morphismRestrict_comp]
      exact hbridge @IsFinite _ hcompres.symm inferInstance
    haveI hIflatC : Flat ((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)) := by
      rw [← morphismRestrict_comp]
      exact hbridge @Flat _ hcompres.symm inferInstance
    haveI hIlfpC : LocallyOfFinitePresentation ((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)) := by
      rw [← morphismRestrict_comp]
      exact hbridge @LocallyOfFinitePresentation _ hcompres.symm inferInstance
    -- global-sections extractions over the affine pieces
    haveI hUaff : IsAffine ↑U.1 := U.2
    haveI hWaffS : IsAffine ↑((J.subschemeι ≫ π) ⁻¹ᵁ U.1) := hWaff
    haveI hW'affS : IsAffine ↑(Scheme.IdealSheafData.inclusion hle
        ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) := hW'aff
    have hsurjTop : Function.Surjective ((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).appTop) :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp hCIres).2
    have hfinB : RingHom.Finite ((((J.subschemeι ≫ π) ∣_ U.1)).appTop).hom :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp hJfin).2
    have hflatB : RingHom.Flat ((((J.subschemeι ≫ π) ∣_ U.1)).appTop).hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp hJflat
    have hlfpB : RingHom.FinitePresentation ((((J.subschemeι ≫ π) ∣_ U.1)).appTop).hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp hJlfp
    have hfinA : RingHom.Finite ((((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop).hom :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp hIfinC).2
    have hflatA : RingHom.Flat ((((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop).hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp hIflatC
    have hlfpA : RingHom.FinitePresentation ((((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop).hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp hIlfpC
    -- module structures over R := Γ(U)
    letI algB : Algebra ↑Γ(U.1, ⊤) ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) :=
      ((((J.subschemeι ≫ π) ∣_ U.1)).appTop).hom.toAlgebra
    letI algA : Algebra ↑Γ(U.1, ⊤)
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) :=
      ((((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop).hom.toAlgebra
    haveI hMfinB : Module.Finite ↑Γ(U.1, ⊤) ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) := hfinB
    haveI hMflatB : Module.Flat ↑Γ(U.1, ⊤) ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) := hflatB
    haveI hAfpB : Algebra.FinitePresentation ↑Γ(U.1, ⊤)
        ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) := hlfpB
    haveI hMfpB : Module.FinitePresentation ↑Γ(U.1, ⊤)
        ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) :=
      Module.FinitePresentation.of_finite_of_finitePresentation _ _
    haveI hMprojB : Module.Projective ↑Γ(U.1, ⊤)
        ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) :=
      Module.Flat.projective_of_finitePresentation
    haveI hMfinA : Module.Finite ↑Γ(U.1, ⊤)
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) := hfinA
    haveI hMflatA : Module.Flat ↑Γ(U.1, ⊤)
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) := hflatA
    haveI hAfpA : Algebra.FinitePresentation ↑Γ(U.1, ⊤)
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) := hlfpA
    haveI hMfpA : Module.FinitePresentation ↑Γ(U.1, ⊤)
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) :=
      Module.FinitePresentation.of_finite_of_finitePresentation _ _
    haveI hMprojA : Module.Projective ↑Γ(U.1, ⊤)
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) :=
      Module.Flat.projective_of_finitePresentation
    -- Spec-side instances for the isoSpec squares
    haveI hSpFinB : IsFinite (Spec.map (((J.subschemeι ≫ π) ∣_ U.1)).appTop) :=
      (IsFinite.SpecMap_iff _).mpr hfinB
    haveI hSpFlatB : Flat (Spec.map (((J.subschemeι ≫ π) ∣_ U.1)).appTop) :=
      Flat.SpecMap_iff.mpr hflatB
    haveI hSpFinA : IsFinite (Spec.map (((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop) :=
      (IsFinite.SpecMap_iff _).mpr hfinA
    haveI hSpFlatA : Flat (Spec.map (((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop) :=
      Flat.SpecMap_iff.mpr hflatA
    -- instances on the unrestricted composite
    haveI hIfinG : IsFinite (Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) := by
      rw [hcompres]
      infer_instance
    haveI hIflatG : Flat (Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) := by
      rw [hcompres]
      infer_instance
    -- the fibre-rank equality of the two Γ-modules
    have hrkeq : Module.rankAtStalk (R := ↑Γ(U.1, ⊤))
        ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤)
        = Module.rankAtStalk (R := ↑Γ(U.1, ⊤)) ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) := by
      funext p
      set u := ((U.1 : Scheme).isoSpec.inv).base p with hu
      have hup : ((U.1 : Scheme).isoSpec.hom).base u = p := by
        rw [hu]
        have h0 := Scheme.Hom.comp_apply ((U.1 : Scheme).isoSpec.inv)
          ((U.1 : Scheme).isoSpec.hom) p
        rw [Iso.inv_hom_id] at h0
        exact h0.symm
      -- B-side chain
      have hsqB : IsPullback (((J.subschemeι ≫ π) ⁻¹ᵁ U.1 : Scheme.Opens _) :
          Scheme).isoSpec.hom ((J.subschemeι ≫ π) ∣_ U.1)
          (Spec.map (((J.subschemeι ≫ π) ∣_ U.1)).appTop) ((U.1 : Scheme)).isoSpec.hom :=
        IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality _⟩
      have hB : Module.rankAtStalk (R := ↑Γ(U.1, ⊤))
          ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) p
          = ((J.subschemeι ≫ π) ∣_ U.1).finrank u := by
        have h1 : Module.rankAtStalk (R := ↑Γ(U.1, ⊤))
            ↑Γ((J.subschemeι ≫ π) ⁻¹ᵁ U.1, ⊤) p
            = ((((J.subschemeι ≫ π) ∣_ U.1)).appTop).hom.finrank p := rfl
        have h2 := congrFun (Scheme.Hom.finrank_SpecMap_eq_finrank hfinB hflatB) p
        have h3 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hsqB u
        rw [h1, ← h2, ← hup]
        exact h3.symm
      have hBres : ((J.subschemeι ≫ π) ∣_ U.1).finrank u
          = (J.subschemeι ≫ π).finrank (U.1.ι.base u) :=
        Scheme.Hom.finrank_of_isPullback _ _ _ _
          (isPullback_morphismRestrict (J.subschemeι ≫ π) U.1).flip u
      -- A-side chain
      have hsqA : IsPullback ((Scheme.IdealSheafData.inclusion hle
            ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1) : Scheme.Opens _) : Scheme).isoSpec.hom
          ((Scheme.IdealSheafData.inclusion hle
            ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))
          (Spec.map (((Scheme.IdealSheafData.inclusion hle
            ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1))).appTop)
          ((U.1 : Scheme)).isoSpec.hom :=
        IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality _⟩
      have hA : Module.rankAtStalk (R := ↑Γ(U.1, ⊤))
          ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) p
          = ((Scheme.IdealSheafData.inclusion hle
            ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)).finrank u := by
        have h1 : Module.rankAtStalk (R := ↑Γ(U.1, ⊤))
            ↑Γ(Scheme.IdealSheafData.inclusion hle ⁻¹ᵁ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1), ⊤) p
            = (((Scheme.IdealSheafData.inclusion hle
              ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)).appTop).hom.finrank
                p := rfl
        have h2 := congrFun (Scheme.Hom.finrank_SpecMap_eq_finrank hfinA hflatA) p
        have h3 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hsqA u
        rw [h1, ← h2, ← hup]
        exact h3.symm
      have hAres : ((Scheme.IdealSheafData.inclusion hle
            ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)).finrank u
          = (I.subschemeι ≫ π).finrank (U.1.ι.base u) := by
        have h4 : ((Scheme.IdealSheafData.inclusion hle
              ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ∣_ U.1)).finrank u
            = ((Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) ∣_ U.1).finrank u := by
          conv_rhs => rw [morphismRestrict_comp]
          rfl
        have h5 : ((Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) ∣_ U.1).finrank u
            = (Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)).finrank
                (U.1.ι.base u) :=
          Scheme.Hom.finrank_of_isPullback _ _ _ _
            (isPullback_morphismRestrict
              (Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)) U.1).flip u
        have h6 : (Scheme.IdealSheafData.inclusion hle ≫ (J.subschemeι ≫ π)).finrank
              (U.1.ι.base u)
            = (I.subschemeι ≫ π).finrank (U.1.ι.base u) :=
          congrArg (fun m => Scheme.Hom.finrank m (U.1.ι.base u)) hcompres
        exact (h4.trans h5).trans h6
      rw [hA, hAres, hB, hBres]
      exact hrank (U.1.ι.base u)
    -- the module core closes the Γ-map
    have hbij : Function.Bijective (((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).appTop).hom) := by
      have := bijective_of_surjective_of_rankAtStalk_eq
        (R := ↑Γ(U.1, ⊤))
        (AlgHom.toLinearMap
          { toRingHom := ((Scheme.IdealSheafData.inclusion hle
              ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).appTop).hom
            commutes' := fun r => rfl })
        hsurjTop hrkeq.symm
      exact this
    haveI : IsIso ((Scheme.IdealSheafData.inclusion hle
        ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).appTop) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    exact isIso_of_isIso_appTop _ inferInstance
  -- glue: open immersion + full range ⟹ iso
  haveI hoi : IsOpenImmersion (Scheme.IdealSheafData.inclusion hle) := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun U : S.affineOpens => (J.subschemeι ≫ π) ⁻¹ᵁ U.1) ?_ ?_
    · rw [eq_top_iff]
      intro y _
      obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ ((J.subschemeι ≫ π).base y)) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hyV⟩
    · intro U
      haveI := hpiece U
      infer_instance
  have hrange : (Scheme.IdealSheafData.inclusion hle).opensRange = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨U, hU⟩ : ∃ U : S.affineOpens, y ∈ (J.subschemeι ≫ π) ⁻¹ᵁ U.1 := by
      obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ ((J.subschemeι ≫ π).base y)) isOpen_univ
      exact ⟨⟨V, hV⟩, hyV⟩
    haveI := hpiece U
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.IdealSheafData.inclusion hle ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).base).2
      ⟨y, hU⟩
    refine ⟨((Scheme.IdealSheafData.inclusion hle) ⁻¹ᵁ
      ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).ι.base x, ?_⟩
    have h1 : ((J.subschemeι ≫ π) ⁻¹ᵁ U.1).ι.base
          ((Scheme.IdealSheafData.inclusion hle
            ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).base x)
        = (Scheme.IdealSheafData.inclusion hle).base
          (((Scheme.IdealSheafData.inclusion hle) ⁻¹ᵁ
            ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)).ι.base x) := by
      show ((Scheme.IdealSheafData.inclusion hle
          ∣_ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1)) ≫ ((J.subschemeι ≫ π) ⁻¹ᵁ U.1).ι).base x
        = _
      rw [morphismRestrict_ι]
      rfl
    rw [hx] at h1
    exact h1.symm
  haveI hiso : IsIso (Scheme.IdealSheafData.inclusion hle) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ hrange
  calc I = (I.subschemeι).ker := (Scheme.IdealSheafData.ker_subschemeι I).symm
    _ = (Scheme.IdealSheafData.inclusion hle ≫ J.subschemeι).ker := by rw [hcomp]
    _ = (J.subschemeι).ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = J := Scheme.IdealSheafData.ker_subschemeι J

end ModularCurves
