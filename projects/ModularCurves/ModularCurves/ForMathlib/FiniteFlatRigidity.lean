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
    sorry
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
