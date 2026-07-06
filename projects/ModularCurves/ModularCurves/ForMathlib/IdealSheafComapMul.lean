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
  refine le_antisymm ?_ ?_
  · -- the hard half: the kernel is at most the extension. Instead of computing the
    -- tensor product, map the competitor `Spec (Γ(X)/extension)` into the pullback
    -- and read off the kernel inclusion from the first projection.
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
      rw [show X.isoSpec.hom.appTop =
          (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤)))).hom from
        Scheme.toSpecΓ_appTop X] at h2
      exact h2
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
    -- hnatval : ΓSpecIsoS.hom (SpecMapMk.appTop (isoSpecInv.appTop z)) =
    --           mk (ΓSpecIsoR.hom (isoSpecInv.appTop z))
    have hdecomp : ((ιX).appTop).hom z =
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop).hom
          ((X.isoSpec.inv.appTop).hom z) := rfl
    rw [hdecomp] at hzero
    rw [hzero, map_zero] at hnatval
    rw [hround z] at hnatval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hnatval.symm
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
    rw [hz, map_zero] at hcomp
    exact hcomp

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

/-- **The scheme-theoretic preimage of ideal sheaves is multiplicative.**

REMAINING WORK (T-D6a-i; affine case and the resLE ⊤-value formula are proven above):
glue `comap_mul_of_isAffine` over a cover by affines `U x ≤ f⁻¹(V x)` via
`ext_of_iSup_eq_top`. The per-`U` value comparison transports through
`ideal_comap_of_isOpenImmersion` at `W := ⊤`, whose right-hand side is indexed by the
IMAGE open `(U x).1.ι ''ᵁ ⊤` — propositionally `U x` (`Scheme.Opens.ι_image_top`) but
a different index, so the equiv `((U x).1.ι.appIso ⊤).commRingCatIsoToRingEquiv` has
domain `Γ(X, ι''ᵁ⊤)`, not `Γ(X, U x)`. Close the cast either with `rw!` (as mathlib's
`le_of_iSup_eq_top` does for exactly this index) or by formulating the injectivity
transport entirely at the image index and casting the GOAL once at the start. Then:
LHS/RHS ⊤-values via `comap_comap_ι_ideal_top`, inner `(K.comap V.ι).⊤`-values via
`ideal_comap_of_isOpenImmersion` + `Ideal.comap_symm` (map-form), multiplicativity by
`ideal_mul`/`Pi.mul_apply` + `Ideal.map_mul` twice, and injectivity of map-along-equiv
(`Ideal.map_of_equiv` round-trip). -/
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

end AlgebraicGeometry.Scheme.IdealSheafData
