/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RelativeDescent
import «Adic spaces».RationalBasisHuber

/-!
# The keystone at open-span certificates (general-Huber base, YB6a)

The `RelativeDescent` keystone (`𝒪_A(E) ≃+* 𝒪_B(imgDatum D₀ E)`) is
parameterized on `span E.T = ⊤` over the base — false over `A_inf` for
window-interior data. The span enters only through the image datum's
constructor, so this file replays the development with the IMAGE-span
certificate (`span (canonicalMap '' E.T) = ⊤` over `B = 𝒪(D₀)`) as the
primitive — which holds for TATE `B` whenever `E.T` generates an open
ambient ideal (the window charts). Names carry an `O`-suffix.
-/

noncomputable section

open TopologicalSpace

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

universe u

/-- **The image rational datum at an open-span certificate.** -/
def imgDatumO (D₀ : RationalLocData A) (E : RationalLocData A)
    [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    RationalLocData (presheafValue D₀) :=
  genPieceDatum (presheafValue_concretePair D₀) (E.T.image D₀.canonicalMap)
    (D₀.canonicalMap E.s) hspanE

@[simp] theorem imgDatumO_T (D₀ E : RationalLocData A)
    [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    (imgDatumO D₀ E hspanE).T = E.T.image D₀.canonicalMap := rfl

@[simp] theorem imgDatumO_s (D₀ E : RationalLocData A)
    [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    (imgDatumO D₀ E hspanE).s = D₀.canonicalMap E.s := rfl

omit [PlusSubring A] in
theorem imgDatumO_isRational (D₀ E : RationalLocData A)
    [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    (imgDatumO D₀ E hspanE).IsRational :=
  RationalLocData.isRational_of_span_eq_top hspanE

variable [HasLocLiftPowerBounded A]

omit [HasLocLiftPowerBounded A] in
/-- **Containment transfer** (through `Spa`-restriction): an `A⁺`-level containment
of rational opens transfers to the `B⁺`-level containment of the image opens.
This is what makes the `B`-side restriction maps between image data available. -/
theorem imgDatumO_rationalOpen_subset (D₀ : RationalLocData A)
    {E E' : RationalLocData A} [DecidableEq (presheafValue D₀)]
    (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hspanE' : Ideal.span ((E'.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hE'E : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s) :
    rationalOpen (imgDatumO D₀ E' hspanE').T (imgDatumO D₀ E' hspanE').s ⊆
      rationalOpen (imgDatumO D₀ E hspanE).T (imgDatumO D₀ E hspanE).s := by
  intro w hw
  obtain ⟨hwSpa, hwT, hws⟩ := hw
  -- the restriction of `w` along the canonical map
  set v : Spv A := comap D₀.canonicalMap w with hvdef
  have hvSpa : v ∈ Spa A A⁺ :=
    comap_mem_spa (canonicalMap_continuous D₀) D₀.canonicalMap_integral hwSpa
  have hvE' : v ∈ rationalOpen E'.T E'.s := by
    refine ⟨hvSpa, fun t ht => ?_, fun h0 => ?_⟩
    · show w.vle (D₀.canonicalMap t) (D₀.canonicalMap E'.s)
      exact hwT _ (by
        rw [imgDatumO_T]
        exact Finset.mem_image_of_mem _ ht)
    · refine hws ?_
      show w.vle (imgDatumO D₀ E' hspanE').s 0
      have h0' : w.vle (D₀.canonicalMap E'.s) (D₀.canonicalMap 0) := h0
      rw [map_zero] at h0'
      exact h0'
  have hvE : v ∈ rationalOpen E.T E.s := hE'E hvE'
  refine ⟨hwSpa, fun b hb => ?_, fun h0 => ?_⟩
  · rw [imgDatumO_T] at hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    show w.vle (D₀.canonicalMap t) (D₀.canonicalMap E.s)
    exact hvE.2.1 t ht
  · refine hvE.2.2 ?_
    show w.vle (D₀.canonicalMap E.s) (D₀.canonicalMap 0)
    rw [map_zero]
    exact h0


section Keystone

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
    : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)

/-- The composed canonical map `A → 𝒪_B(imgDatumO D₀ E)`. -/
def imgCanonicalO : A →+* presheafValue (imgDatumO D₀ E hspanE) :=
  ((imgDatumO D₀ E hspanE).canonicalMap).comp D₀.canonicalMap

/-- `E.s` becomes a unit in the doubly-localized completion (it is the image
datum's own denominator, a unit in its own section ring). -/
theorem imgCanonicalO_isUnit_s : IsUnit ((imgCanonicalO D₀ hspanE) E.s) := by
  have := isUnit_canonicalMap_s (A := presheafValue D₀)
    (imgDatumO D₀ E hspanE) (imgDatumO D₀ E hspanE) subset_rfl
  rw [imgDatumO_s] at this
  exact this

/-- The forward lift on the localization: `Localization.Away E.s → 𝒪_B(img E)`. -/
def keystoneAlgO : Localization.Away E.s →+* presheafValue (imgDatumO D₀ E hspanE) :=
  IsLocalization.Away.lift E.s (imgCanonicalO_isUnit_s D₀ hspanE)

theorem keystoneAlgO_algebraMap (a : A) :
    keystoneAlgO D₀ hspanE (algebraMap A (Localization.Away E.s) a) =
      (imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap a) :=
  IsLocalization.Away.lift_eq E.s (imgCanonicalO_isUnit_s D₀ hspanE) a

/-- The forward lift sends the `t/s`-generators to the image datum's own
`t/s`-lifts (uniqueness of division by the unit `can E.s`). -/
theorem keystoneAlgO_divByS {t : A} (_ht : t ∈ E.T) :
    keystoneAlgO D₀ hspanE (divByS t E.s) =
      IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
        (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
        (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) := by
  refine (imgCanonicalO_isUnit_s D₀ hspanE).mul_left_cancel ?_
  have hspec := algebraMap_mul_divByS t E.s
  have hL : (imgCanonicalO D₀ hspanE) E.s * keystoneAlgO D₀ hspanE (divByS t E.s) =
      (imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap t) := by
    calc (imgCanonicalO D₀ hspanE) E.s * keystoneAlgO D₀ hspanE (divByS t E.s)
        = keystoneAlgO D₀ hspanE (algebraMap A (Localization.Away E.s) E.s) *
            keystoneAlgO D₀ hspanE (divByS t E.s) := by
          rw [keystoneAlgO_algebraMap]
          rfl
      _ = keystoneAlgO D₀ hspanE
            (algebraMap A (Localization.Away E.s) E.s * divByS t E.s) :=
          (map_mul _ _ _).symm
      _ = keystoneAlgO D₀ hspanE (algebraMap A (Localization.Away E.s) t) := by
          rw [hspec]
      _ = (imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap t) :=
          keystoneAlgO_algebraMap D₀ hspanE t
  have hspecB := algebraMap_mul_divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s
  have hR : (imgCanonicalO D₀ hspanE) E.s *
      IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
        (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
        (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) =
      (imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap t) := by
    calc (imgCanonicalO D₀ hspanE) E.s *
        IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
          (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
          (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s)
        = IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)
              (imgDatumO D₀ E hspanE).s) *
          IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) := by
          rw [IsLocalization.Away.lift_eq _ _ (imgDatumO D₀ E hspanE).s]
          rfl
      _ = IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)
              (imgDatumO D₀ E hspanE).s *
              divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) :=
          (map_mul _ _ _).symm
      _ = IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
            (isUnit_canonicalMap_s (A := presheafValue D₀) _ _ subset_rfl)
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)
              (D₀.canonicalMap t)) := by
          rw [hspecB]
      _ = (imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap t) :=
          IsLocalization.Away.lift_eq _ _ _
  rw [hL, hR]

/-- Continuity of the forward lift for the `E`-localization topology (through the
general engine `locTopology_continuous_lift`: the composed canonical map is
continuous, and the `t/s`-lifts are power-bounded by the `B`-level
`HasLocLiftPowerBounded` package at the reflexive containment). -/
theorem keystoneAlgO_continuous :
    @Continuous _ _ E.topology _ (keystoneAlgO D₀ hspanE) := by
  refine locTopology_continuous_lift E.P E.T E.s E.hopen _ ?_ ?_
  · -- continuity of `lift ∘ algebraMap = imgCanonicalO`
    have h_eq : (keystoneAlgO D₀ hspanE).comp (algebraMap A (Localization.Away E.s)) =
        imgCanonicalO D₀ hspanE := by
      ext a
      exact keystoneAlgO_algebraMap D₀ hspanE a
    rw [show ⇑((keystoneAlgO D₀ hspanE).comp (algebraMap A (Localization.Away E.s)))
        = ⇑(imgCanonicalO D₀ hspanE) from congrArg _ h_eq]
    exact (canonicalMap_continuous (imgDatumO D₀ E hspanE)).comp
      (canonicalMap_continuous D₀)
  · -- power-boundedness of the `t/s`-images
    intro t ht
    rw [keystoneAlgO_divByS D₀ hspanE ht]
    exact @HasLocLiftPowerBounded.locLift_divByS_isPowerBounded (presheafValue D₀)
      _ _ _ (presheafValue.instIsHuberRing D₀) _
      (imgDatumO D₀ E hspanE) (imgDatumO D₀ E hspanE) (fun _ hv => hv)
      (D₀.canonicalMap t) (by
        rw [imgDatumO_T]
        exact Finset.mem_image_of_mem _ ht)

/-- **The keystone, forward**: `𝒪_A(E) →+* 𝒪_B(imgDatumO D₀ E)`. -/
def keystoneHomO : presheafValue E →+* presheafValue (imgDatumO D₀ E hspanE) := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (keystoneAlgO D₀ hspanE)
    (keystoneAlgO_continuous D₀ hspanE)

theorem keystoneHomO_coe (x : Localization.Away E.s) :
    keystoneHomO D₀ hspanE
      (@UniformSpace.Completion.coeRingHom _ _ E.uniformSpace
        E.isTopologicalRing E.isUniformAddGroup x) = keystoneAlgO D₀ hspanE x := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ x

theorem keystoneHomO_continuous : Continuous (keystoneHomO D₀ hspanE) := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The keystone intertwines the canonical maps. -/
theorem keystoneHomO_canonicalMap (a : A) :
    keystoneHomO D₀ hspanE (E.canonicalMap a) =
      (imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap a) := by
  have := keystoneHomO_coe D₀ hspanE (algebraMap A (Localization.Away E.s) a)
  rw [keystoneAlgO_algebraMap] at this
  exact this

end Keystone

/-! ### The keystone, backward direction and round trips -/

section KeystoneInv

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
    : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
  (hE : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)

/-- `imgDatumO`'s denominator maps to a unit under the restriction map. -/
theorem restriction_isUnit_imgSO :
    IsUnit ((restrictionMapHom D₀ E hE) (imgDatumO D₀ E hspanE).s) := by
  rw [imgDatumO_s, restriction_canonicalMap' D₀ hE]
  exact isUnit_canonicalMap_s E E (fun _ hv => hv)

/-- The backward lift on the `B`-localization. -/
def keystoneInvAlgO :
    Localization.Away (imgDatumO D₀ E hspanE).s →+* presheafValue E :=
  IsLocalization.Away.lift (imgDatumO D₀ E hspanE).s
    (restriction_isUnit_imgSO D₀ hspanE hE)

theorem keystoneInvAlgO_algebraMap (b : presheafValue D₀) :
    keystoneInvAlgO D₀ hspanE hE
      (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s) b) =
      restrictionMapHom D₀ E hE b :=
  IsLocalization.Away.lift_eq (imgDatumO D₀ E hspanE).s
    (restriction_isUnit_imgSO D₀ hspanE hE) b

/-- The backward lift sends the image `t/s`-generators to the `A`-side `t/s`-lifts. -/
theorem keystoneInvAlgO_divByS {t : A} (_ht : t ∈ E.T) :
    keystoneInvAlgO D₀ hspanE hE
      (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) =
      IsLocalization.Away.lift E.s
        (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
        (divByS t E.s) := by
  refine (restriction_isUnit_imgSO D₀ hspanE hE).mul_left_cancel ?_
  have hspecB := algebraMap_mul_divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s
  have hspecA := algebraMap_mul_divByS t E.s
  have hL : (restrictionMapHom D₀ E hE) (imgDatumO D₀ E hspanE).s *
      keystoneInvAlgO D₀ hspanE hE
        (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) =
      E.canonicalMap t := by
    calc (restrictionMapHom D₀ E hE) (imgDatumO D₀ E hspanE).s *
        keystoneInvAlgO D₀ hspanE hE
          (divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s)
        = keystoneInvAlgO D₀ hspanE hE
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)
              (imgDatumO D₀ E hspanE).s *
              divByS (D₀.canonicalMap t) (imgDatumO D₀ E hspanE).s) := by
          rw [map_mul, keystoneInvAlgO_algebraMap]
      _ = keystoneInvAlgO D₀ hspanE hE
            (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)
              (D₀.canonicalMap t)) := by rw [hspecB]
      _ = restrictionMapHom D₀ E hE (D₀.canonicalMap t) :=
          keystoneInvAlgO_algebraMap D₀ hspanE hE _
      _ = E.canonicalMap t := restriction_canonicalMap' D₀ hE t
  have hR : (restrictionMapHom D₀ E hE) (imgDatumO D₀ E hspanE).s *
      IsLocalization.Away.lift E.s
        (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
        (divByS t E.s) =
      E.canonicalMap t := by
    have hs' : (restrictionMapHom D₀ E hE) (imgDatumO D₀ E hspanE).s =
        E.canonicalMap E.s := by
      rw [imgDatumO_s]
      exact restriction_canonicalMap' D₀ hE E.s
    calc (restrictionMapHom D₀ E hE) (imgDatumO D₀ E hspanE).s *
        IsLocalization.Away.lift E.s
          (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
          (divByS t E.s)
        = IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (algebraMap A (Localization.Away E.s) E.s) *
          IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (divByS t E.s) := by
          rw [IsLocalization.Away.lift_eq, hs']
      _ = IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (algebraMap A (Localization.Away E.s) E.s * divByS t E.s) :=
          (map_mul _ _ _).symm
      _ = IsLocalization.Away.lift E.s
            (HasLocLiftPowerBounded.isUnit_canonicalMap_s E E (fun _ hv => hv))
            (algebraMap A (Localization.Away E.s) t) := by rw [hspecA]
      _ = E.canonicalMap t := IsLocalization.Away.lift_eq E.s _ t
  rw [hL, hR]

/-- Continuity of the backward lift for the image localization topology over `B`. -/
theorem keystoneInvAlgO_continuous :
    @Continuous _ _ (imgDatumO D₀ E hspanE).topology _ (keystoneInvAlgO D₀ hspanE hE) := by
  refine locTopology_continuous_lift (imgDatumO D₀ E hspanE).P (imgDatumO D₀ E hspanE).T
    (imgDatumO D₀ E hspanE).s (imgDatumO D₀ E hspanE).hopen _ ?_ ?_
  · have h_eq : (keystoneInvAlgO D₀ hspanE hE).comp
        (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)) =
        restrictionMapHom D₀ E hE := by
      ext b
      exact keystoneInvAlgO_algebraMap D₀ hspanE hE b
    rw [show ⇑((keystoneInvAlgO D₀ hspanE hE).comp
        (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s)))
        = ⇑(restrictionMapHom D₀ E hE) from congrArg _ h_eq]
    exact restrictionMapHom_continuous D₀ E hE
  · intro b hb
    rw [imgDatumO_T] at hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    rw [keystoneInvAlgO_divByS D₀ hspanE hE ht]
    exact @HasLocLiftPowerBounded.locLift_divByS_isPowerBounded A
      _ _ _ _ _ E E (fun _ hv => hv) t ht

/-- **The keystone, backward**: `𝒪_B(imgDatumO D₀ E) →+* 𝒪_A(E)`. -/
def keystoneInvO : presheafValue (imgDatumO D₀ E hspanE) →+* presheafValue E := by
  letI : UniformSpace (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (keystoneInvAlgO D₀ hspanE hE)
    (keystoneInvAlgO_continuous D₀ hspanE hE)

theorem keystoneInvO_coe (x : Localization.Away (imgDatumO D₀ E hspanE).s) :
    keystoneInvO D₀ hspanE hE
      (@UniformSpace.Completion.coeRingHom _ _ (imgDatumO D₀ E hspanE).uniformSpace
        (imgDatumO D₀ E hspanE).isTopologicalRing
        (imgDatumO D₀ E hspanE).isUniformAddGroup x) =
      keystoneInvAlgO D₀ hspanE hE x := by
  letI : UniformSpace (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ x

theorem keystoneInvO_continuous : Continuous (keystoneInvO D₀ hspanE hE) := by
  letI : UniformSpace (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The backward keystone intertwines the `B`-canonical map with the restriction. -/
theorem keystoneInvO_canonicalMap (b : presheafValue D₀) :
    keystoneInvO D₀ hspanE hE ((imgDatumO D₀ E hspanE).canonicalMap b) =
      restrictionMapHom D₀ E hE b := by
  have := keystoneInvO_coe D₀ hspanE hE
    (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s) b)
  rw [keystoneInvAlgO_algebraMap] at this
  exact this

end KeystoneInv

/-! ### Round trips and the bundled keystone -/

section KeystoneRoundtrip

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
    : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
  (hE : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)

/-- **The base square**: the forward keystone turns the `A`-side restriction map
into the `B`-side canonical map. (Two continuous maps out of `B`, agreeing on the
dense image of the `D₀`-localization, which in turn is checked on the image of `A`
by `IsLocalization.ringHom_ext`.) -/
theorem keystoneHomO_restriction (b : presheafValue D₀) :
    keystoneHomO D₀ hspanE (restrictionMapHom D₀ E hE b) =
      (imgDatumO D₀ E hspanE).canonicalMap b := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  -- ring-hom equality on the `D₀`-localization
  have hloc : ((keystoneHomO D₀ hspanE).comp (restrictionMapHom D₀ E hE)).comp
      D₀.coeRingHom =
      ((imgDatumO D₀ E hspanE).canonicalMap).comp D₀.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
    ext a
    have h₁ : restrictionMapHom D₀ E hE
        (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
        E.canonicalMap a := restriction_canonicalMap' D₀ hE a
    show keystoneHomO D₀ hspanE (restrictionMapHom D₀ E hE
      (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a))) =
      (imgDatumO D₀ E hspanE).canonicalMap
        (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a))
    rw [h₁, keystoneHomO_canonicalMap]
    rfl
  -- extend by density and continuity
  have hdense : DenseRange (⇑(D₀.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ D₀.uniformSpace
  have hfun : ⇑(keystoneHomO D₀ hspanE) ∘ ⇑(restrictionMapHom D₀ E hE) =
      ⇑((imgDatumO D₀ E hspanE).canonicalMap) := by
    refine hdense.equalizer ?_ ?_ ?_
    · exact (keystoneHomO_continuous D₀ hspanE).comp
        (restrictionMapHom_continuous D₀ E hE)
    · exact canonicalMap_continuous (imgDatumO D₀ E hspanE)
    · funext x
      exact DFunLike.congr_fun hloc x
  exact congr_fun hfun b

/-- Round trip on `𝒪_A(E)`. -/
theorem keystoneInvO_keystoneHomO (x : presheafValue E) :
    keystoneInvO D₀ hspanE hE (keystoneHomO D₀ hspanE x) = x := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  have hloc : ((keystoneInvO D₀ hspanE hE).comp (keystoneAlgO D₀ hspanE)) =
      E.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers E.s) ?_
    ext a
    show keystoneInvO D₀ hspanE hE
      (keystoneAlgO D₀ hspanE (algebraMap A (Localization.Away E.s) a)) =
      E.coeRingHom (algebraMap A (Localization.Away E.s) a)
    rw [keystoneAlgO_algebraMap, keystoneInvO_canonicalMap,
      restriction_canonicalMap' D₀ hE]
    rfl
  have hdense : DenseRange (⇑(E.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ E.uniformSpace
  have hfun : ⇑(keystoneInvO D₀ hspanE hE) ∘ ⇑(keystoneHomO D₀ hspanE) =
      (id : presheafValue E → presheafValue E) := by
    refine hdense.equalizer ?_ continuous_id ?_
    · exact (keystoneInvO_continuous D₀ hspanE hE).comp
        (keystoneHomO_continuous D₀ hspanE)
    · funext l
      show keystoneInvO D₀ hspanE hE (keystoneHomO D₀ hspanE (E.coeRingHom l)) =
        E.coeRingHom l
      have h1 : keystoneHomO D₀ hspanE (E.coeRingHom l) = keystoneAlgO D₀ hspanE l :=
        keystoneHomO_coe D₀ hspanE l
      rw [h1]
      exact DFunLike.congr_fun hloc l
  exact congr_fun hfun x

/-- Round trip on `𝒪_B(imgDatumO D₀ E)`. -/
theorem keystoneHomO_keystoneInvO (y : presheafValue (imgDatumO D₀ E hspanE)) :
    keystoneHomO D₀ hspanE (keystoneInvO D₀ hspanE hE y) = y := by
  letI : UniformSpace (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imgDatumO D₀ E hspanE).s) :=
    (imgDatumO D₀ E hspanE).isUniformAddGroup
  have hloc : ((keystoneHomO D₀ hspanE).comp (keystoneInvAlgO D₀ hspanE hE)) =
      (imgDatumO D₀ E hspanE).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (imgDatumO D₀ E hspanE).s) ?_
    ext b
    show keystoneHomO D₀ hspanE (keystoneInvAlgO D₀ hspanE hE
      (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s) b)) =
      (imgDatumO D₀ E hspanE).coeRingHom
        (algebraMap (presheafValue D₀) (Localization.Away (imgDatumO D₀ E hspanE).s) b)
    rw [keystoneInvAlgO_algebraMap, keystoneHomO_restriction]
    rfl
  have hdense : DenseRange (⇑((imgDatumO D₀ E hspanE).coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ (imgDatumO D₀ E hspanE).uniformSpace
  have hfun : ⇑(keystoneHomO D₀ hspanE) ∘ ⇑(keystoneInvO D₀ hspanE hE) =
      (id : presheafValue (imgDatumO D₀ E hspanE) → presheafValue (imgDatumO D₀ E hspanE)) := by
    refine hdense.equalizer ?_ continuous_id ?_
    · exact (keystoneHomO_continuous D₀ hspanE).comp
        (keystoneInvO_continuous D₀ hspanE hE)
    · funext l
      show keystoneHomO D₀ hspanE (keystoneInvO D₀ hspanE hE
        ((imgDatumO D₀ E hspanE).coeRingHom l)) = (imgDatumO D₀ E hspanE).coeRingHom l
      have h1 : keystoneInvO D₀ hspanE hE ((imgDatumO D₀ E hspanE).coeRingHom l) =
          keystoneInvAlgO D₀ hspanE hE l := keystoneInvO_coe D₀ hspanE hE l
      rw [h1]
      exact DFunLike.congr_fun hloc l
  exact congr_fun hfun y

/-- **The noetherian-free keystone** (Wedhorn Lemma 8.1 / Prop 8.2(2) / Remark 8.4): the section
ring of a rational piece over `A` is canonically the section ring of its image
datum over `B = 𝒪(D₀)`, as topological rings
(`keystoneHomO_continuous`/`keystoneInvO_continuous`), compatibly with the canonical
maps (`keystoneHomO_canonicalMap`) and the restriction maps
(`keystoneHomO_restriction`). -/
def keystoneO : presheafValue E ≃+* presheafValue (imgDatumO D₀ E hspanE) where
  toFun := keystoneHomO D₀ hspanE
  invFun := keystoneInvO D₀ hspanE hE
  left_inv := keystoneInvO_keystoneHomO D₀ hspanE hE
  right_inv := keystoneHomO_keystoneInvO D₀ hspanE hE
  map_mul' := map_mul _
  map_add' := map_add _

end KeystoneRoundtrip

/-! ### The keystone restriction squares -/

section KeystoneSquares

variable [DecidableEq A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) {E E' : RationalLocData A}
  [DecidableEq (presheafValue D₀)]
  (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
    : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
  (hspanE' : Ideal.span ((E'.T.image D₀.canonicalMap
    : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
  (hE'E : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s)

/-- **The keystone square**: the forward keystones intertwine the `A`-side and
`B`-side restriction maps between pieces. (Both composites are continuous maps out
of `𝒪_A(E)`; they agree on the canonical image of `A`, hence on the dense image of
the `E`-localization, hence everywhere.) -/
theorem keystone_restriction_squareO (x : presheafValue E) :
    keystoneHomO D₀ hspanE' (restrictionMap E E' hE'E x) =
      restrictionMap (imgDatumO D₀ E hspanE) (imgDatumO D₀ E' hspanE')
        (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E)
        (keystoneHomO D₀ hspanE x) := by
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  -- ring-hom equality on the `E`-localization: both routes send `algebraMap a` to
  -- the doubly-canonical image of `a`
  have hloc : ((keystoneHomO D₀ hspanE').comp (restrictionMapHom E E' hE'E)).comp
      E.coeRingHom =
      ((restrictionMapHom (imgDatumO D₀ E hspanE) (imgDatumO D₀ E' hspanE')
          (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E)).comp
        (keystoneHomO D₀ hspanE)).comp E.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers E.s) ?_
    ext a
    have h₁ : restrictionMapHom E E' hE'E (E.canonicalMap a) = E'.canonicalMap a :=
      restriction_canonicalMap' E hE'E a
    have h₂ : restrictionMapHom (imgDatumO D₀ E hspanE) (imgDatumO D₀ E' hspanE')
        (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E)
        ((imgDatumO D₀ E hspanE).canonicalMap (D₀.canonicalMap a)) =
        (imgDatumO D₀ E' hspanE').canonicalMap (D₀.canonicalMap a) :=
      restriction_canonicalMap' (A := presheafValue D₀) (imgDatumO D₀ E hspanE)
        (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E) (D₀.canonicalMap a)
    show keystoneHomO D₀ hspanE' (restrictionMapHom E E' hE'E
        (E.coeRingHom (algebraMap A (Localization.Away E.s) a))) =
      restrictionMapHom (imgDatumO D₀ E hspanE) (imgDatumO D₀ E' hspanE')
        (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E)
        (keystoneHomO D₀ hspanE
          (E.coeRingHom (algebraMap A (Localization.Away E.s) a)))
    have hcanE : E.coeRingHom (algebraMap A (Localization.Away E.s) a) =
        E.canonicalMap a := rfl
    rw [hcanE, h₁, keystoneHomO_canonicalMap, keystoneHomO_canonicalMap, h₂]
  have hdense : DenseRange (⇑(E.coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ E.uniformSpace
  have hfun : ⇑(keystoneHomO D₀ hspanE') ∘ ⇑(restrictionMapHom E E' hE'E) =
      ⇑(restrictionMapHom (imgDatumO D₀ E hspanE) (imgDatumO D₀ E' hspanE')
          (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E)) ∘
        ⇑(keystoneHomO D₀ hspanE) := by
    refine hdense.equalizer ?_ ?_ ?_
    · exact (keystoneHomO_continuous D₀ hspanE').comp
        (restrictionMapHom_continuous E E' hE'E)
    · exact (restrictionMapHom_continuous (imgDatumO D₀ E hspanE)
        (imgDatumO D₀ E' hspanE')
        (imgDatumO_rationalOpen_subset D₀ hspanE hspanE' hE'E)).comp
        (keystoneHomO_continuous D₀ hspanE)
    · funext l
      exact DFunLike.congr_fun hloc l
  exact congr_fun hfun x

end KeystoneSquares



section ImgCovering

variable [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺ : Subring A)]

variable (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)]

/-- **Membership transfer into the image rational** (the two pure halves):
a `Spa`-point of the completion lies in the image rational iff its
`A`-shadow lies in the source rational. -/
theorem mem_imgDatumO_rationalOpen_iff
    {E : RationalLocData A}
    (hspanE : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    {w : Spv (presheafValue D₀)}
    (hw : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺) :
    w ∈ rationalOpen (imgDatumO D₀ E hspanE).T (imgDatumO D₀ E hspanE).s
      ↔ comap D₀.canonicalMap w ∈ rationalOpen E.T E.s := by
  constructor
  · rintro ⟨-, hT, hs⟩
    refine ⟨comap_mem_spa (canonicalMap_continuous D₀)
      D₀.canonicalMap_integral hw, ?_, ?_⟩
    · intro t ht
      rw [comap_vle]
      exact hT (D₀.canonicalMap t) (by
        rw [imgDatumO_T]
        exact Finset.mem_image_of_mem _ ht)
    · intro hcon
      refine hs ?_
      rw [show (imgDatumO D₀ E hspanE).s = D₀.canonicalMap E.s from rfl]
      have := (comap_vle D₀.canonicalMap w E.s 0).mp hcon
      rwa [map_zero] at this
  · rintro ⟨-, hT, hs⟩
    refine ⟨hw, ?_, ?_⟩
    · intro t' ht'
      rw [show (imgDatumO D₀ E hspanE).T = E.T.image D₀.canonicalMap
        from rfl] at ht'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      rw [show (imgDatumO D₀ E hspanE).s = D₀.canonicalMap E.s from rfl]
      exact (comap_vle D₀.canonicalMap w t E.s).mp (hT t ht)
    · intro hcon
      refine hs ?_
      rw [show (imgDatumO D₀ E hspanE).s = D₀.canonicalMap E.s from rfl]
        at hcon
      rw [comap_vle]
      rwa [show D₀.canonicalMap (0 : A) = 0 from map_zero _]

variable [DecidableEq (RationalLocData (presheafValue D₀))]

/-- The certificate-total image datum (`dite`-guarded, so `Finset.image`
needs no dependent lambda). -/
noncomputable def imgDatumOTot (E : RationalLocData A) :
    RationalLocData (presheafValue D₀) :=
  if h : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤
  then imgDatumO D₀ E h
  else globalLocData (presheafValue_concretePair D₀)

theorem imgDatumOTot_of_cert {E : RationalLocData A}
    (h : Ideal.span ((E.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    imgDatumOTot D₀ E = imgDatumO D₀ E h :=
  dif_pos h

/-- The image pieces (a plain `Finset.image`). -/
noncomputable def imgCoversO (C : RationalCoveringData A) :
    Finset (RationalLocData (presheafValue D₀)) :=
  C.covers.image (imgDatumOTot D₀)

/-- Membership shape of the image pieces (certificate-resolved). -/
theorem mem_imgCoversO (C : RationalCoveringData A)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    {D' : RationalLocData (presheafValue D₀)} :
    D' ∈ imgCoversO D₀ C ↔
      ∃ (D : RationalLocData A) (hD : D ∈ C.covers),
        D' = imgDatumO D₀ D (hcertP D hD) := by
  rw [imgCoversO, Finset.mem_image]
  constructor
  · rintro ⟨D, hD, rfl⟩
    exact ⟨D, hD, (imgDatumOTot_of_cert D₀ (hcertP D hD)).symm ▸ rfl⟩
  · rintro ⟨D, hD, rfl⟩
    exact ⟨D, hD, imgDatumOTot_of_cert D₀ (hcertP D hD)⟩

/-- The image pieces sit inside the image base (hoisted). -/
theorem imgCoversO_subset (C : RationalCoveringData A)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    ∀ D' ∈ imgCoversO D₀ C,
      rationalOpen D'.T D'.s
        ⊆ rationalOpen (imgDatumO D₀ C.base hcertB).T
            (imgDatumO D₀ C.base hcertB).s := by
  intro D' hD'
  obtain ⟨D, hD, rfl⟩ := (mem_imgCoversO D₀ C hcertP).mp hD'
  intro w hw
  have hwspa : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw.1
  have h1 := (mem_imgDatumO_rationalOpen_iff D₀ (hcertP D hD) hwspa).mp hw
  have h2 := C.hsubset D hD h1
  exact (mem_imgDatumO_rationalOpen_iff D₀ hcertB hwspa).mpr h2

/-- The image pieces cover the image base (hoisted). -/
theorem imgCoversO_cover (C : RationalCoveringData A)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    ∀ w ∈ rationalOpen (imgDatumO D₀ C.base hcertB).T
        (imgDatumO D₀ C.base hcertB).s,
      ∃ D' ∈ imgCoversO D₀ C, w ∈ rationalOpen D'.T D'.s := by
  intro w hw
  have hwspa : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw.1
  have h1 := (mem_imgDatumO_rationalOpen_iff D₀ hcertB hwspa).mp hw
  obtain ⟨D, hD, hmem⟩ := C.hcover _ h1
  refine ⟨imgDatumO D₀ D (hcertP D hD),
    (mem_imgCoversO D₀ C hcertP).mpr ⟨D, hD, rfl⟩, ?_⟩
  exact (mem_imgDatumO_rationalOpen_iff D₀ (hcertP D hD) hwspa).mpr hmem

/-- **The image covering** over the completion. -/
noncomputable def imgCoveringO (C : RationalCoveringData A)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    RationalCoveringData (presheafValue D₀) :=
  ⟨imgDatumO D₀ C.base hcertB, imgCoversO D₀ C,
    imgCoversO_subset D₀ C hcertB hcertP,
    imgCoversO_cover D₀ C hcertB hcertP⟩

/-- The image covering is rational. -/
theorem imgCoveringO_isRational (C : RationalCoveringData A)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    (imgCoveringO D₀ C hcertB hcertP).IsRational := by
  constructor
  · exact imgDatumO_isRational D₀ C.base hcertB
  · intro D' hD'
    obtain ⟨D, hD, rfl⟩ := (mem_imgCoversO D₀ C hcertP).mp hD'
    exact imgDatumO_isRational D₀ D (hcertP D hD)

end ImgCovering


section EqOpen

variable [HasLocLiftPowerBounded A]

/-- **Equal-open value coherence**: the cross restrictions between two data
presenting the same rational open compose to the identity. -/
theorem restrictionMap_cross_eq_id (D E : RationalLocData A)
    (hDE : rationalOpen D.T D.s = rationalOpen E.T E.s) (x : presheafValue D) :
    restrictionMap E D (le_of_eq hDE)
      (restrictionMap D E (ge_of_eq hDE) x) = x := by
  have hcomp := restrictionMap_restrictionMap D E D (ge_of_eq hDE) (le_of_eq hDE) x
  refine hcomp.trans ?_
  have hid := congr_fun (restrictionMap_id D) x
  exact (by simpa using hid :
    restrictionMap D D ((le_of_eq hDE).trans (ge_of_eq hDE)) x = x)

end EqOpen

section GluingTransport

variable [IsRingOfIntegralElements (A⁺ : Subring A)] [DecidableEq A]
variable (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)]
  [DecidableEq (RationalLocData (presheafValue D₀))]

/-- **The transported family** over the image covering: choose a preimage
piece and push its value through the keystone (cast along the membership
equation). -/
noncomputable def imgFamily (C : RationalCoveringData A)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hCD₀ : rationalOpen C.base.T C.base.s
      ⊆ rationalOpen D₀.T D₀.s)
    (f : ∀ D : ↥C.covers, presheafValue D.1) :
    ∀ D' : ↥(imgCoveringO D₀ C hcertB hcertP).covers,
      presheafValue D'.1 := fun D' =>
  let h := (mem_imgCoversO D₀ C hcertP).mp D'.2
  (h.choose_spec.choose_spec.symm ▸
    (keystoneO D₀ (hcertP h.choose h.choose_spec.choose)
      ((C.hsubset h.choose h.choose_spec.choose).trans hCD₀)
      (f ⟨h.choose, h.choose_spec.choose⟩)))

end GluingTransport


section ImgInter

variable [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [DecidableEq A]
variable (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)]

/-- **The two presentations of the image intersection agree** as rational
opens: the `B`-side intersection of the images equals the image of the
certified `A`-side intersection. -/
theorem imgDatumO_interDatumOpen_rationalOpen
    {D₁ D₂ : RationalLocData A} {M₁ M₂ : ℕ}
    (hle₁ : (Ideal.span (D₁.P.A₀.subtype '' (D₁.P.I : Set D₁.P.A₀))) ^ M₁
      ≤ Ideal.span (D₁.T : Set A))
    (hle₂ : (Ideal.span (D₁.P.A₀.subtype '' (D₁.P.I : Set D₁.P.A₀))) ^ M₂
      ≤ Ideal.span (D₂.T : Set A))
    (hcert₁ : Ideal.span ((D₁.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcert₂ : Ideal.span ((D₂.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertI : Ideal.span (((D₁.interDatumOpen D₂ M₁ M₂ hle₁ hle₂).T.image
        D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤) :
    rationalOpen (imgDatumO D₀ (D₁.interDatumOpen D₂ M₁ M₂ hle₁ hle₂) hcertI).T
        (imgDatumO D₀ (D₁.interDatumOpen D₂ M₁ M₂ hle₁ hle₂) hcertI).s
      = rationalOpen (imgDatumO D₀ D₁ hcert₁).T (imgDatumO D₀ D₁ hcert₁).s
        ∩ rationalOpen (imgDatumO D₀ D₂ hcert₂).T
            (imgDatumO D₀ D₂ hcert₂).s := by
  ext w
  constructor
  · intro hw
    have hwspa : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw.1
    have h1 := (mem_imgDatumO_rationalOpen_iff D₀ hcertI hwspa).mp hw
    rw [RationalLocData.interDatumOpen_rationalOpen] at h1
    exact ⟨(mem_imgDatumO_rationalOpen_iff D₀ hcert₁ hwspa).mpr h1.1,
      (mem_imgDatumO_rationalOpen_iff D₀ hcert₂ hwspa).mpr h1.2⟩
  · rintro ⟨hw₁, hw₂⟩
    have hwspa : w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ := hw₁.1
    refine (mem_imgDatumO_rationalOpen_iff D₀ hcertI hwspa).mpr ?_
    rw [RationalLocData.interDatumOpen_rationalOpen]
    exact ⟨(mem_imgDatumO_rationalOpen_iff D₀ hcert₁ hwspa).mp hw₁,
      (mem_imgDatumO_rationalOpen_iff D₀ hcert₂ hwspa).mp hw₂⟩

end ImgInter


section ImgAgreement

variable [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [DecidableEq A]
variable (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)]
  [DecidableEq (RationalLocData (presheafValue D₀))]

/-- **The transported family is exact-intersection compatible** (the B-side
gluing input): under a uniform certificate supplier, per B-pair the
agreement reduces through the cast-elimination, the equal-open cross hop
onto the image of the certified `A`-intersection, and the keystone squares
to the given `A`-side all-data agreement. -/
theorem imgFamily_agreement
    (hcertAll : ∀ E : RationalLocData A, E.IsRational →
      Ideal.span ((E.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (_hCD₀ : rationalOpen C.base.T C.base.s ⊆ rationalOpen D₀.T D₀.s)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hf : ∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂))
    (E₁ E₂ : RationalLocData A) (h₁ : E₁ ∈ C.covers) (h₂ : E₂ ∈ C.covers)
    (X : RationalLocData (presheafValue D₀))
    (hX₁ : rationalOpen X.T X.s
      ⊆ rationalOpen (imgDatumO D₀ E₁ (hcertAll E₁ (hC.piece h₁))).T
          (imgDatumO D₀ E₁ (hcertAll E₁ (hC.piece h₁))).s)
    (hX₂ : rationalOpen X.T X.s
      ⊆ rationalOpen (imgDatumO D₀ E₂ (hcertAll E₂ (hC.piece h₂))).T
          (imgDatumO D₀ E₂ (hcertAll E₂ (hC.piece h₂))).s) :
    restrictionMap _ X hX₁
        (keystoneHomO D₀ (hcertAll E₁ (hC.piece h₁)) (f ⟨E₁, h₁⟩))
      = restrictionMap _ X hX₂
        (keystoneHomO D₀ (hcertAll E₂ (hC.piece h₂)) (f ⟨E₂, h₂⟩)) := by
  classical
  -- the certified A-side intersection
  obtain ⟨M₁, hM₁⟩ := exists_pow_le_of_isRational E₁ (hC.piece h₁)
  obtain ⟨M₂', hM₂⟩ := exists_pow_le_of_isRational_pair E₁.P E₂ (hC.piece h₂)
  set I := E₁.interDatumOpen E₂ M₁ M₂' hM₁ hM₂ with hI
  have hIrat : I.IsRational :=
    RationalLocData.isRational_of_pow_le (M₁ + M₂') (E₁.interDatumOpen_pow_le E₂ M₁ M₂' hM₁ hM₂)
  have hIsub₁ : rationalOpen I.T I.s ⊆ rationalOpen E₁.T E₁.s := by
    rw [RationalLocData.interDatumOpen_rationalOpen]
    exact Set.inter_subset_left
  have hIsub₂ : rationalOpen I.T I.s ⊆ rationalOpen E₂.T E₂.s := by
    rw [RationalLocData.interDatumOpen_rationalOpen]
    exact Set.inter_subset_right
  have hA := hf ⟨E₁, h₁⟩ ⟨E₂, h₂⟩ I hIsub₁ hIsub₂
  -- transport through the keystone squares
  have hsq₁ := keystone_restriction_squareO D₀
    (hcertAll E₁ (hC.piece h₁)) (hcertAll _ hIrat) hIsub₁ (f ⟨E₁, h₁⟩)
  have hsq₂ := keystone_restriction_squareO D₀
    (hcertAll E₂ (hC.piece h₂)) (hcertAll _ hIrat) hIsub₂ (f ⟨E₂, h₂⟩)
  have hBI : restrictionMap _ _
      (imgDatumO_rationalOpen_subset D₀ (hcertAll E₁ (hC.piece h₁)) (hcertAll _ hIrat) hIsub₁)
      (keystoneHomO D₀ (hcertAll E₁ (hC.piece h₁)) (f ⟨E₁, h₁⟩))
      = restrictionMap _ _
      (imgDatumO_rationalOpen_subset D₀ (hcertAll E₂ (hC.piece h₂)) (hcertAll _ hIrat) hIsub₂)
      (keystoneHomO D₀ (hcertAll E₂ (hC.piece h₂)) (f ⟨E₂, h₂⟩)) := by
    rw [← hsq₁, ← hsq₂, hA]
  -- X refines the image intersection
  have hXI : rationalOpen X.T X.s
      ⊆ rationalOpen (imgDatumO D₀ I (hcertAll _ hIrat)).T
        (imgDatumO D₀ I (hcertAll _ hIrat)).s := by
    rw [imgDatumO_interDatumOpen_rationalOpen D₀ hM₁ hM₂
      (hcertAll E₁ (hC.piece h₁)) (hcertAll E₂ (hC.piece h₂))
      (hcertAll _ hIrat)]
    exact Set.subset_inter hX₁ hX₂
  -- collapse both sides through the intersection
  have hc₁ := restrictionMap_restrictionMap (imgDatumO D₀ E₁ (hcertAll E₁ (hC.piece h₁)))
    (imgDatumO D₀ I (hcertAll _ hIrat)) X
    (imgDatumO_rationalOpen_subset D₀ (hcertAll E₁ (hC.piece h₁)) (hcertAll _ hIrat) hIsub₁) hXI
    (keystoneHomO D₀ (hcertAll E₁ (hC.piece h₁)) (f ⟨E₁, h₁⟩))
  have hc₂ := restrictionMap_restrictionMap (imgDatumO D₀ E₂ (hcertAll E₂ (hC.piece h₂)))
    (imgDatumO D₀ I (hcertAll _ hIrat)) X
    (imgDatumO_rationalOpen_subset D₀ (hcertAll E₂ (hC.piece h₂)) (hcertAll _ hIrat) hIsub₂) hXI
    (keystoneHomO D₀ (hcertAll E₂ (hC.piece h₂)) (f ⟨E₂, h₂⟩))
  calc restrictionMap _ X hX₁ (keystoneHomO D₀ (hcertAll E₁ (hC.piece h₁)) (f ⟨E₁, h₁⟩))
      = restrictionMap _ X hXI (restrictionMap _ _
          (imgDatumO_rationalOpen_subset D₀ (hcertAll E₁ (hC.piece h₁)) (hcertAll _ hIrat) hIsub₁)
          (keystoneHomO D₀ (hcertAll E₁ (hC.piece h₁)) (f ⟨E₁, h₁⟩))) := hc₁.symm
    _ = restrictionMap _ X hXI (restrictionMap _ _
          (imgDatumO_rationalOpen_subset D₀ (hcertAll E₂ (hC.piece h₂)) (hcertAll _ hIrat) hIsub₂)
          (keystoneHomO D₀ (hcertAll E₂ (hC.piece h₂)) (f ⟨E₂, h₂⟩))) := by
        rw [hBI]
    _ = restrictionMap _ X hX₂ (keystoneHomO D₀ (hcertAll E₂ (hC.piece h₂)) (f ⟨E₂, h₂⟩)) :=
        hc₂

end ImgAgreement


section GluingTransportMain

variable [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [DecidableEq A]
variable (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)]
  [DecidableEq (RationalLocData (presheafValue D₀))]

variable (C : RationalCoveringData A)

/-- **Restriction of a transported family value** (cast-eliminated, member
abstract so the substitution motive computes). -/
theorem imgFamily_restriction
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hCD₀ : rationalOpen C.base.T C.base.s ⊆ rationalOpen D₀.T D₀.s)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (D' : ↥(imgCoveringO D₀ C hcertB hcertP).covers)
    (X : RationalLocData (presheafValue D₀))
    (hX : rationalOpen X.T X.s ⊆ rationalOpen D'.1.T D'.1.s) :
    restrictionMap D'.1 X hX (imgFamily D₀ C hcertB hcertP hCD₀ f D')
      = restrictionMap
          (imgDatumO D₀ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose
            (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose))
          X
          (hX.trans (le_of_eq (congrArg (fun E => rationalOpen E.T E.s)
            ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose_spec)))
          (keystoneHomO D₀
            (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose)
            (f ⟨((mem_imgCoversO D₀ C hcertP).mp D'.2).choose,
              ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose⟩)) := by
  set h := (mem_imgCoversO D₀ C hcertP).mp D'.2 with hh
  have hval : imgFamily D₀ C hcertB hcertP hCD₀ f D'
      = h.choose_spec.choose_spec.symm ▸
        (keystoneO D₀ (hcertP h.choose h.choose_spec.choose)
          ((C.hsubset h.choose h.choose_spec.choose).trans hCD₀)
          (f ⟨h.choose, h.choose_spec.choose⟩)) := rfl
  rw [hval, restrictionMap_cast _ _ h.choose_spec.choose_spec.symm _]
  have hc := restrictionMap_restrictionMap
    (imgDatumO D₀ h.choose (hcertP h.choose h.choose_spec.choose))
    D'.1 X
    (le_of_eq (congrArg (fun E => rationalOpen E.T E.s)
      h.choose_spec.choose_spec)) hX
    (keystoneHomO D₀ (hcertP h.choose h.choose_spec.choose)
      (f ⟨h.choose, h.choose_spec.choose⟩))
  exact hc

/-- **The transported family at an image piece**: the value of `imgFamily` at
`imgDatumO D₀ D` is the keystone transport of `f D`.  The witness `imgCoversO` picks
out need not be `D` itself, so the two are identified through `imgFamily_agreement`. -/
theorem imgFamily_imgDatumO
    (hcertAll : ∀ E : RationalLocData A, E.IsRational →
      Ideal.span ((E.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hC : C.IsRational)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
      : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hCD₀ : rationalOpen C.base.T C.base.s ⊆ rationalOpen D₀.T D₀.s)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hf : ∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂))
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (hDmem : imgDatumO D₀ D (hcertP D hD)
      ∈ (imgCoveringO D₀ C hcertB hcertP).covers) :
    imgFamily D₀ C hcertB hcertP hCD₀ f ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩
      = keystoneHomO D₀ (hcertP D hD) (f ⟨D, hD⟩) := by
  classical
  set hm := (mem_imgCoversO D₀ C hcertP).mp hDmem with hhm
  have hXfst : rationalOpen (imgDatumO D₀ D (hcertP D hD)).T
      (imgDatumO D₀ D (hcertP D hD)).s
      ⊆ rationalOpen
        (imgDatumO D₀ hm.choose (hcertP hm.choose hm.choose_spec.choose)).T
        (imgDatumO D₀ hm.choose (hcertP hm.choose hm.choose_spec.choose)).s :=
    le_of_eq (congrArg (fun E => rationalOpen E.T E.s)
      hm.choose_spec.choose_spec)
  have hagree := imgFamily_agreement D₀ hcertAll C hC hCD₀ f hf
    hm.choose D hm.choose_spec.choose hD
    (imgDatumO D₀ D (hcertP D hD)) hXfst (le_refl _)
  have hres := imgFamily_restriction D₀ C hcertB hcertP hCD₀ f
    ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩
    (imgDatumO D₀ D (hcertP D hD)) (le_refl _)
  have hid₁ := congr_fun (restrictionMap_id (imgDatumO D₀ D (hcertP D hD)))
    (imgFamily D₀ C hcertB hcertP hCD₀ f
      ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩)
  have hid₂ := congr_fun (restrictionMap_id (imgDatumO D₀ D (hcertP D hD)))
    (keystoneHomO D₀ (hcertP D hD) (f ⟨D, hD⟩))
  calc imgFamily D₀ C hcertB hcertP hCD₀ f
        ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩
      = restrictionMap _ _ (le_refl _)
          (imgFamily D₀ C hcertB hcertP hCD₀ f
            ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩) := by
        simpa using hid₁.symm
    _ = restrictionMap _ _ _
          (keystoneHomO D₀
            (hcertP hm.choose hm.choose_spec.choose)
            (f ⟨hm.choose, hm.choose_spec.choose⟩)) := hres
    _ = restrictionMap _ _ (le_refl _)
          (keystoneHomO D₀ (hcertP D hD) (f ⟨D, hD⟩)) := hagree
    _ = keystoneHomO D₀ (hcertP D hD) (f ⟨D, hD⟩) := by
        simpa using hid₂


/-- **The single-`D₀` gluing transport** (the core of the Y-local sheaf
condition): a compatible family over a valid rational covering inside
`R(D₀)` glues, provided the completion at `D₀` is a sheafy Tate ring. -/
theorem exists_glue_of_imgCovering
    [IsTateRing (presheafValue D₀)]
    [T2Space (presheafValue D₀)] [NonarchimedeanRing (presheafValue D₀)]
    [letI : UniformSpace (presheafValue D₀) :=
        IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀);
      CompleteSpace (presheafValue D₀)]
    [IsRingOfIntegralElements ((presheafValue D₀)⁺)]
    [IsSheafy (presheafValue D₀)]
    (hcertAll : ∀ E : RationalLocData A, E.IsRational →
      Ideal.span ((E.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hCD₀ : rationalOpen C.base.T C.base.s ⊆ rationalOpen D₀.T D₀.s)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hf : ∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  classical
  have hcertB := hcertAll _ hC.base
  have hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤ :=
    fun D hD => hcertAll D (hC.piece hD)
  have hCBrat := imgCoveringO_isRational D₀ C hcertB hcertP
  -- the transported family is all-data compatible
  have hfB : (imgCoveringO D₀ C hcertB hcertP).AllDataCompatible
      (imgFamily D₀ C hcertB hcertP hCD₀ f) := by
    rw [RationalCoveringData.allDataCompatible_iff_exactIntersectionCompatible
      hCBrat]
    intro D₁' D₂'
    -- both sides collapse through the transported-family restriction lemma
    rw [imgFamily_restriction D₀ C hcertB hcertP hCD₀ f D₁',
      imgFamily_restriction D₀ C hcertB hcertP hCD₀ f D₂']
    exact imgFamily_agreement D₀ hcertAll C hC hCD₀ f hf _ _
      ((mem_imgCoversO D₀ C hcertP).mp D₁'.2).choose_spec.choose
      ((mem_imgCoversO D₀ C hcertP).mp D₂'.2).choose_spec.choose _ _ _
  -- glue on the B side
  obtain ⟨xB, hxB⟩ := IsSheafy.gluing (A := presheafValue D₀)
    (imgCoveringO D₀ C hcertB hcertP) hCBrat
    (imgFamily D₀ C hcertB hcertP hCD₀ f) hfB
  -- pull back along the base keystone
  refine ⟨(keystoneO D₀ hcertB hCD₀).symm xB, ?_⟩
  rintro ⟨D, hD⟩
  -- the image member of this piece
  have hDmem : imgDatumO D₀ D (hcertP D hD)
      ∈ (imgCoveringO D₀ C hcertB hcertP).covers :=
    (mem_imgCoversO D₀ C hcertP).mpr ⟨D, hD, rfl⟩
  have hxD := hxB ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩
  -- the keystone square at base → piece
  have hsq := keystone_restriction_squareO D₀ hcertB (hcertP D hD)
    (C.hsubset D hD) ((keystoneO D₀ hcertB hCD₀).symm xB)
  have hbase : keystoneHomO D₀ hcertB ((keystoneO D₀ hcertB hCD₀).symm xB)
      = xB := (keystoneO D₀ hcertB hCD₀).apply_symm_apply xB
  rw [hbase] at hsq
  -- identify the glued restriction with the family value
  rw [show restrictionMap (imgDatumO D₀ C.base hcertB)
      (imgDatumO D₀ D (hcertP D hD))
      (imgDatumO_rationalOpen_subset D₀ hcertB (hcertP D hD)
        (C.hsubset D hD)) xB
    = imgFamily D₀ C hcertB hcertP hCD₀ f
        ⟨imgDatumO D₀ D (hcertP D hD), hDmem⟩ from hxD] at hsq
  -- apply the piece keystone's injectivity, then chain
  refine (keystoneO D₀ (hcertP D hD)
    ((C.hsubset D hD).trans hCD₀)).injective ?_
  refine hsq.trans ?_
  exact imgFamily_imgDatumO D₀ C hcertAll hC hcertB hcertP hCD₀ f hf D hD hDmem

end GluingTransportMain


section EmbeddingTransport

variable [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [DecidableEq A]
variable (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)]

omit [HasLocLiftPowerBounded A] in
omit [HasLocLiftPowerBounded A] in
omit [HasLocLiftPowerBounded A] in
omit [HasLocLiftPowerBounded A] in
omit [HasLocLiftPowerBounded A] in
omit [HasLocLiftPowerBounded A] in
/-- Casting along a datum equality is continuous (subst-form). -/
theorem continuous_cast_presheafValue {E₁ E₂ : RationalLocData (presheafValue D₀)}
    (heq : E₁ = E₂) :
    Continuous (fun v : presheafValue E₁ => heq ▸ v) := by
  subst heq
  exact continuous_id

variable [DecidableEq (RationalLocData (presheafValue D₀))]

/-- **The comparison square on products.** Restricting on `A` and then applying the
keystone map agrees with applying the keystone map and then restricting on the image
covering. -/
private theorem keystone_comp_productRestrictionSub_eq
    [IsSheafy (presheafValue D₀)]
    [T2Space (presheafValue D₀)] [NonarchimedeanRing (presheafValue D₀)]
    [letI : UniformSpace (presheafValue D₀) :=
        IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀);
      CompleteSpace (presheafValue D₀)]
    [IsRingOfIntegralElements ((presheafValue D₀)⁺)]
    (C : RationalCoveringData A)
    (hcertB : Ideal.span ((C.base.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (g : (∀ D : ↥C.covers, presheafValue D.1) →
      (∀ D' : ↥(imgCoveringO D₀ C hcertB hcertP).covers, presheafValue D'.1))
    (hgdef : g = fun s D' =>
      ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose_spec.symm ▸
        (keystoneHomO D₀
          (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose)
          (s ⟨((mem_imgCoversO D₀ C hcertP).mp D'.2).choose,
            ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose⟩))) :
    g ∘ productRestrictionSub A C
      = productRestrictionSub (presheafValue D₀)
          (imgCoveringO D₀ C hcertB hcertP)
        ∘ (keystoneHomO D₀ hcertB) := by
  subst hgdef
  funext x D'
  show (((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose_spec.symm ▸
      (keystoneHomO D₀ _ (restrictionMap C.base _ _ x))) = _
  rw [restrictionMap_cast _ _
    ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose_spec.symm _]
  have hsq := keystone_restriction_squareO D₀ hcertB
    (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose)
    (C.hsubset _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose)
    x
  rw [hsq]
  have hc := restrictionMap_restrictionMap
    (imgDatumO D₀ C.base hcertB)
    (imgDatumO D₀ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose
      (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose))
    D'.1
    (imgDatumO_rationalOpen_subset D₀ hcertB
      (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose)
      (C.hsubset _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose))
    (le_of_eq (congrArg (fun E => rationalOpen E.T E.s)
      ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose_spec))
    (keystoneHomO D₀ hcertB x)
  exact hc

/-- **The embedding transport** (the topological half of the single-`D₀`
sheaf transport): the product restriction of an interior covering is a
topological embedding, provided the completion at `D₀` is a sheafy Tate
ring. -/
theorem isEmbedding_productRestrictionSub_of_imgCovering
    [IsSheafy (presheafValue D₀)]
    [T2Space (presheafValue D₀)] [NonarchimedeanRing (presheafValue D₀)]
    [letI : UniformSpace (presheafValue D₀) :=
        IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀);
      CompleteSpace (presheafValue D₀)]
    [IsRingOfIntegralElements ((presheafValue D₀)⁺)]
    (hcertAll : ∀ E : RationalLocData A, E.IsRational →
      Ideal.span ((E.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hCD₀ : rationalOpen C.base.T C.base.s ⊆ rationalOpen D₀.T D₀.s) :
    Topology.IsEmbedding (productRestrictionSub A C) := by
  classical
  have hcertB := hcertAll _ hC.base
  have hcertP : ∀ D ∈ C.covers,
      Ideal.span ((D.T.image D₀.canonicalMap
        : Finset (presheafValue D₀)) : Set (presheafValue D₀)) = ⊤ :=
    fun D hD => hcertAll D (hC.piece hD)
  have hCBrat := imgCoveringO_isRational D₀ C hcertB hcertP
  -- the comparison map on products
  set g : (∀ D : ↥C.covers, presheafValue D.1) →
      (∀ D' : ↥(imgCoveringO D₀ C hcertB hcertP).covers, presheafValue D'.1) :=
    fun s D' =>
      ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose_spec.symm ▸
        (keystoneHomO D₀
          (hcertP _ ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose)
          (s ⟨((mem_imgCoversO D₀ C hcertP).mp D'.2).choose,
            ((mem_imgCoversO D₀ C hcertP).mp D'.2).choose_spec.choose⟩))
    with hgdef
  have hgcont : Continuous g := by
    refine continuous_pi fun D' => ?_
    exact (continuous_cast_presheafValue D₀ _).comp
      ((keystoneHomO_continuous D₀ _).comp (continuous_apply _))
  -- the composite is the B-side product restriction after the base keystone
  have hcomp := keystone_comp_productRestrictionSub_eq D₀ C hcertB hcertP g hgdef
  -- the composite is an embedding: B-side embedding after the base homeo
  have hkeyhomeo : Topology.IsEmbedding (keystoneHomO D₀ hcertB) := by
    have h : Topology.IsEmbedding
        (⇑(Homeomorph.mk (keystoneO D₀ hcertB hCD₀).toEquiv
          (keystoneHomO_continuous D₀ hcertB)
          (keystoneInvO_continuous D₀ hcertB hCD₀))) :=
      (Homeomorph.mk _ _ _).isEmbedding
    exact h
  have hcompEmb : Topology.IsEmbedding
      (productRestrictionSub (presheafValue D₀)
        (imgCoveringO D₀ C hcertB hcertP)
      ∘ (keystoneHomO D₀ hcertB)) :=
    (IsSheafy.embedding _ hCBrat).comp hkeyhomeo
  rw [← hcomp] at hcompEmb
  constructor
  · exact Topology.IsInducing.of_comp
      (productRestrictionSub_continuous C) hgcont
      hcompEmb.isInducing
  · exact Function.Injective.of_comp (f := g) hcompEmb.injective

end EmbeddingTransport

end ValuationSpectrum

end
