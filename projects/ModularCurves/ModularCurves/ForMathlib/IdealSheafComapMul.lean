/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Scheme-theoretic preimage of ideal sheaves is multiplicative

`(I * J).comap f = I.comap f * J.comap f` for ideal sheaves `I J` on `Y` and
`f : X ⟶ Y`. The scheme-theoretic preimage (`IdealSheafData.comap`, the kernel of the
first projection of the pulled-back closed subscheme) is affine-locally the extension
`Ideal.map` along the ring map, which is multiplicative.

Strategy (per the T-D6a-i design):
* `comap_ideal_top_of_isAffine`: over affine `X`, `Y` the top-value of `I.comap f` is
  `(I.ideal ⊤).map f.appTop` — the honest tensor computation
  (`Hom.ker_apply` + `pullbackSpecIso` + `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`).
* `comap_mul_of_isAffine`: `Ideal.map_mul` + the above.
* `comap_mul`: globalise over affine covers
  (`IdealSheafData.ext_of_iSup_eq_top` + comap-restriction compatibility).

Upstream candidate. Ticket: T-D6a-i (ModularCurves).
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The hard inclusion behind `comap_ideal_top_of_isAffine`: the kernel of the first
projection is at most the extension `(I.ideal ⊤).map f.appTop`. Rather than compute the
tensor product, map the competitor `Spec (Γ(X)/extension)` into the pullback and read the
kernel inclusion off the first projection. -/
private lemma comap_ideal_top_ker_le_map [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (hY : IsAffineOpen (⊤ : Y.Opens)) :
    RingHom.ker ((Limits.pullback.fst f I.subschemeι).appTop).hom ≤
      (I.ideal ⟨⊤, hY⟩).map (f.appTop).hom := by
  have hround : ∀ w : ↑Γ(X, ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤)))).hom.hom
        ((X.isoSpec.inv.appTop).hom w) = w := by
    intro w
    have h1 : X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
      rfl
    have h2 := congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) => g.hom w) h1
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_id, RingHom.coe_id, id_eq] at h2
    rwa [show X.isoSpec.hom.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤)))).hom from
      Scheme.toSpecΓ_appTop X] at h2
  set K := (I.ideal ⟨⊤, hY⟩).map (f.appTop).hom with hK
  set ιX : Spec (.of (↑Γ(X, ⊤) ⧸ K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.isoSpec.inv with hιX
  have hle : I.subschemeι.ker ≤ (ιX ≫ f).ker := by
    rw [ker_subschemeι, ker_of_isAffine]
    refine le_of_isAffine ?_
    rw [show (ofIdealTop (RingHom.ker ((ιX ≫ f).appTop).hom)).ideal
        ⟨⊤, isAffineOpen_top Y⟩ = RingHom.ker ((ιX ≫ f).appTop).hom by simp]
    intro x hx
    rw [RingHom.mem_ker]
    have hxK : (f.appTop).hom x ∈ K := Ideal.mem_map_of_mem _ hx
    have hval : ((ιX ≫ f).appTop).hom x =
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop).hom
          ((X.isoSpec.inv.appTop).hom ((f.appTop).hom x)) := rfl
    rw [hval]
    have hnat1 := congrArg
      (fun g : Γ(Spec (CommRingCat.of (↑Γ(X, ⊤))), ⊤) ⟶
          CommRingCat.of (↑Γ(X, ⊤) ⧸ K) =>
        g.hom ((X.isoSpec.inv.appTop).hom ((f.appTop).hom x)))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk K)))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at hnat1
    rw [hround ((f.appTop).hom x)] at hnat1
    refine (Scheme.ΓSpecIso (CommRingCat.of
      (↑Γ(X, ⊤) ⧸ K))).commRingCatIsoToRingEquiv.injective ?_
    show (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤) ⧸ K))).hom.hom _ =
      (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤) ⧸ K))).hom.hom 0
    rw [map_zero, hnat1,
      show Ideal.Quotient.mk K ((f.appTop).hom x) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hxK]
  set u : Spec (.of (↑Γ(X, ⊤) ⧸ K)) ⟶ Limits.pullback f I.subschemeι :=
    Limits.pullback.lift ιX (IsClosedImmersion.lift I.subschemeι (ιX ≫ f) hle)
      (IsClosedImmersion.lift_fac _ _ _).symm with hu
  have hufst : u ≫ Limits.pullback.fst f I.subschemeι = ιX :=
    Limits.pullback.lift_fst _ _ _
  intro z hz
  rw [RingHom.mem_ker] at hz
  have hzero : ((ιX).appTop).hom z = 0 := by
    rw [← hufst, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hz, map_zero]
  have hnatval := congrArg
    (fun g : Γ(Spec (CommRingCat.of (↑Γ(X, ⊤))), ⊤) ⟶
        CommRingCat.of (↑Γ(X, ⊤) ⧸ K) => g.hom ((X.isoSpec.inv.appTop).hom z))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk K)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hnatval
  have hdecomp : ((ιX).appTop).hom z =
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop).hom
        ((X.isoSpec.inv.appTop).hom z) := rfl
  rw [hdecomp] at hzero
  rw [hzero, map_zero] at hnatval
  rw [hround z] at hnatval
  exact Ideal.Quotient.eq_zero_iff_mem.mp hnatval.symm

/-- Over affine schemes, the scheme-theoretic preimage of an ideal sheaf has top-value
the extension of the top-value: `(I.comap f).ideal ⊤ = (I.ideal ⊤).map f.appTop`.
The heart of `comap_mul`. -/
theorem comap_ideal_top_of_isAffine [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (hX : IsAffineOpen (⊤ : X.Opens))
    (hY : IsAffineOpen (⊤ : Y.Opens)) :
    (I.comap f).ideal ⟨⊤, hX⟩ =
      (I.ideal ⟨⊤, hY⟩).map (f.appTop).hom := by
  have hker : (I.comap f).ideal ⟨⊤, hX⟩ =
      RingHom.ker ((Limits.pullback.fst f I.subschemeι).appTop).hom := by
    show ((Limits.pullback.fst f I.subschemeι).ker).ideal ⟨⊤, hX⟩ = _
    rw [ker_of_isAffine]
    simp
  rw [hker]
  refine le_antisymm (comap_ideal_top_ker_le_map I f hY) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hcomp : ((Limits.pullback.fst f I.subschemeι) ≫ f).appTop.hom x =
        ((Limits.pullback.snd f I.subschemeι) ≫ I.subschemeι).appTop.hom x := by
      rw [Limits.pullback.condition]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hcomp
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hcomp
    have hz : (I.subschemeι.appTop).hom x = 0 := by
      have happ := Scheme.IdealSheafData.subschemeι_app I ⟨⊤, isAffineOpen_top Y⟩
      have hval := congrArg (fun g => CommRingCat.Hom.hom g x) happ
      refine Eq.trans (rfl :
        (Scheme.Hom.appTop I.subschemeι).hom x =
        (Scheme.Hom.app I.subschemeι
          ↑(⟨⊤, isAffineOpen_top Y⟩ : Y.affineOpens)).hom x) ?_
      refine hval.trans ?_
      show (I.subschemeObjIso ⟨⊤, isAffineOpen_top Y⟩).inv.hom
        (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top Y⟩) x) = 0
      rw [show Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top Y⟩) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact map_zero _
    rwa [hz, map_zero] at hcomp

/-- Over affine schemes, the scheme-theoretic preimage of ideal sheaves is
multiplicative. -/
theorem comap_mul_of_isAffine [IsAffine X] [IsAffine Y]
    (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine ext_of_isAffine ?_
  rw [comap_ideal_top_of_isAffine (I * J) f (isAffineOpen_top X) (isAffineOpen_top Y),
    ideal_mul, Pi.mul_apply, Ideal.map_mul, ideal_mul, Pi.mul_apply,
    comap_ideal_top_of_isAffine I f (isAffineOpen_top X) (isAffineOpen_top Y),
    comap_ideal_top_of_isAffine J f (isAffineOpen_top X) (isAffineOpen_top Y)]

/-- The `⊤`-value of the double preimage along an affine `U ≤ f⁻¹V`, expressed through
the restriction `f.resLE`. -/
theorem comap_comap_ι_ideal_top (K : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    haveI : IsAffine U.1.toScheme := U.2
    haveI : IsAffine V.1.toScheme := V.2
    ((K.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((K.comap V.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩).map
        ((f.resLE V.1 U.1 hUV).appTop).hom := by
  haveI : IsAffine U.1.toScheme := U.2
  haveI : IsAffine V.1.toScheme := V.2
  rw [← comap_comp, show U.1.ι ≫ f = f.resLE V.1 U.1 hUV ≫ V.1.ι from
    (Scheme.Hom.resLE_comp_ι f hUV).symm, comap_comp,
    comap_ideal_top_of_isAffine (K.comap V.1.ι) (f.resLE V.1 U.1 hUV)
      (isAffineOpen_top _) (isAffineOpen_top _)]

/-- **The scheme-theoretic preimage of ideal sheaves is multiplicative**:
`(I * J).comap f = I.comap f * J.comap f`. Globalises the affine case
`comap_mul_of_isAffine` over a cover by affines `U x ≤ f⁻¹(V x)` via `ext_of_iSup_eq_top`. -/
theorem comap_mul (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  classical
  have hex : ∀ x : X, ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro x
    obtain ⟨V, hV⟩ : ∃ V : Y.affineOpens, f x ∈ V.1 := by
      have hmem : f x ∈ (⊤ : Y.Opens) := trivial
      rw [← iSup_affineOpens_eq_top Y] at hmem
      exact TopologicalSpace.Opens.mem_iSup.mp hmem
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (U := f ⁻¹ᵁ V.1) hV
    exact ⟨⟨W, hW⟩, V, hxW, hWle⟩
  choose U V hxU hUV using hex
  refine ext_of_iSup_eq_top U ?_ (fun x => ?_)
  · rw [eq_top_iff]
    exact fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  · haveI : IsAffine (U x).1.toScheme := (U x).2
    haveI : IsAffine (V x).1.toScheme := (V x).2
    set eU : ↑Γ(X, (U x).1.ι ''ᵁ ⊤) ≃+* ↑Γ((U x).1.toScheme, ⊤) :=
      ((U x).1.ι.appIso ⊤).commRingCatIsoToRingEquiv with heU
    set eV : ↑Γ(Y, (V x).1.ι ''ᵁ ⊤) ≃+* ↑Γ((V x).1.toScheme, ⊤) :=
      ((V x).1.ι.appIso ⊤).commRingCatIsoToRingEquiv with heV
    have hchain : ∀ K : Y.IdealSheafData,
        (K.comap f).ideal (U x) =
          ((((K.ideal ⟨(V x).1.ι ''ᵁ ⊤,
              (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map
            eV.toRingHom).map
              ((f.resLE (V x).1 (U x).1 (hUV x)).appTop).hom).map
                eU.symm.toRingHom).map
                  (X.presheaf.map (homOfLE ((U x).1.ι_image_top).ge).op).hom := by
      intro K
      -- inner value via the OI formula on Y (already in map-form after comap_symm)
      have hBV : ((K.comap (V x).1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ :
            Ideal ↑Γ((V x).1.toScheme, ⊤)) =
          (K.ideal ⟨(V x).1.ι ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map eV.toRingHom :=
        (ideal_comap_of_isOpenImmersion K (V x).1.ι ⟨⊤, isAffineOpen_top _⟩).trans
          (Ideal.comap_symm eV)
      -- ⊤-value of the double preimage via resLE
      have hT := comap_comap_ι_ideal_top K f (U x) (V x) (hUV x)
      rw [hBV] at hT
      -- image-open value from the ⊤-value
      have hB : ((K.comap f).ideal ⟨(U x).1.ι ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩ :
            Ideal ↑Γ(X, (U x).1.ι ''ᵁ ⊤)) =
          ((((K.comap f).comap (U x).1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ :
              Ideal ↑Γ((U x).1.toScheme, ⊤))).map
            eU.symm.toRingHom := by
        have h1 : (((K.comap f).comap (U x).1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ :
              Ideal ↑Γ((U x).1.toScheme, ⊤)) =
            ((K.comap f).ideal ⟨(U x).1.ι ''ᵁ ⊤,
              (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map eU.toRingHom :=
          (ideal_comap_of_isOpenImmersion (K.comap f) (U x).1.ι
            ⟨⊤, isAffineOpen_top _⟩).trans (Ideal.comap_symm eU)
        have h2 := congrArg (Ideal.map eU.symm.toRingHom) h1
        exact (h2.trans (Ideal.map_of_equiv eU)).symm
      -- value at U from the image-open value
      have hA : ((K.comap f).ideal (U x) : Ideal ↑Γ(X, (U x).1)) =
          ((K.comap f).ideal ⟨(U x).1.ι ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map
            (X.presheaf.map (homOfLE ((U x).1.ι_image_top).ge).op).hom :=
        (map_ideal (K.comap f) ((U x).1.ι_image_top).ge).symm
      rw [hA, hB, hT]
    rw [ideal_mul, Pi.mul_apply, hchain (I * J), hchain I, hchain J,
      ideal_mul, Pi.mul_apply, Ideal.map_mul, Ideal.map_mul, Ideal.map_mul,
      Ideal.map_mul]

/-- Scheme-theoretic preimage as a monoid homomorphism on ideal sheaves. -/
noncomputable def comapMonoidHom (f : X ⟶ Y) :
    Y.IdealSheafData →* X.IdealSheafData where
  toFun K := K.comap f
  map_one' := by rw [one_eq_top, comap_top, one_eq_top]
  map_mul' I J := comap_mul I J f

@[simp] lemma comapMonoidHom_apply (f : X ⟶ Y) (K : Y.IdealSheafData) :
    comapMonoidHom f K = K.comap f := rfl

/-- The scheme-theoretic preimage of a finite product of ideal sheaves. -/
lemma comap_prod {ι : Type*} (s : Finset ι) (K : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (∏ i ∈ s, K i).comap f = ∏ i ∈ s, (K i).comap f :=
  map_prod (comapMonoidHom f) K s

/-- `IdealSheafData.ideal` as a monoid homomorphism: products of ideal sheaves are
computed pointwise (`ideal_mul`), and the unit ideal sheaf `⊤` has value the unit ideal. -/
noncomputable def idealMonoidHom (X : Scheme.{u}) :
    X.IdealSheafData →* (∀ U : X.affineOpens, Ideal Γ(X, U.1)) where
  toFun := ideal
  map_one' := by
    funext U
    simp [one_eq_top, ideal_top, Ideal.one_eq_top]
  map_mul' I J := ideal_mul I J

@[simp] lemma idealMonoidHom_apply (X : Scheme.{u}) (I : X.IdealSheafData) :
    idealMonoidHom X I = I.ideal := rfl

/-- For an isomorphism of schemes, pushing an ideal sheaf forward along the hom agrees with
pulling it back along the inverse. -/
lemma map_hom_eq_comap_inv {X Y : Scheme.{u}} (φ : X ≅ Y) (I : X.IdealSheafData) :
    I.map φ.hom = I.comap φ.inv := by
  refine le_antisymm ?_ ?_
  · have h1 : ((I.map φ.hom).comap φ.hom).comap φ.inv ≤ I.comap φ.inv :=
      comap_mono φ.inv (comap_map_le _ _)
    rwa [← comap_comp, φ.inv_hom_id, comap_id] at h1
  · refine ((map_gc φ.hom) _ _).mp ?_
    show (I.comap φ.inv).comap φ.hom ≤ I
    rw [← comap_comp, φ.hom_inv_id, comap_id]

/-- The kernel of a morphism postcomposed with an isomorphism is the `comap` of the kernel
along the inverse. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.ker_comp_iso {T X Y : Scheme.{u}} (z : T ⟶ X)
    (φ : X ≅ Y) : Scheme.Hom.ker (z ≫ φ.hom) = (Scheme.Hom.ker z).comap φ.inv := by
  rw [Scheme.Hom.ker_comp]
  exact map_hom_eq_comap_inv φ z.ker

/-- Precomposition with an isomorphism does not change the kernel ideal sheaf. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.ker_iso_comp {X Y Z : Scheme.{u}} (τ : X ⟶ Y)
    [IsIso τ] (f : Y ⟶ Z) : Scheme.Hom.ker (τ ≫ f) = Scheme.Hom.ker f := by
  rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot_of_isIso, map_bot]

/-- **Factoring through a pulled-back subscheme = factoring through the original after
composing** (the `comapIso` dictionary). A map `g : T ⟶ X` factors through the scheme-
theoretic preimage `(I.comap f).subscheme` iff its composite `g ≫ f` factors through
`I.subscheme`. -/
lemma exists_factor_comap_iff {X Y T : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (g : T ⟶ X) :
    (∃ h : T ⟶ (I.comap f).subscheme, h ≫ (I.comap f).subschemeι = g) ↔
      (∃ h : T ⟶ I.subscheme, h ≫ I.subschemeι = g ≫ f) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h ≫ (I.comapIso f).hom ≫ pullback.snd f I.subschemeι, ?_⟩
    simp only [Category.assoc]
    rw [← pullback.condition, comapIso_hom_fst_assoc]
  · rintro ⟨h, hh⟩
    refine ⟨pullback.lift g h hh.symm ≫ (I.comapIso f).inv, ?_⟩
    rw [Category.assoc, comapIso_inv_subschemeι, pullback.lift_fst]

end AlgebraicGeometry.Scheme.IdealSheafData
