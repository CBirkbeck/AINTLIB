/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential
import ModularCurves.Moduli.EllCategory

/-!
# Base change of `ω`-bases over the elliptic-curve category (T-OM-B7 ★★)

**(T-E-OMEGA, `/develop --decompose` 2026-07-13, STREAM-OMEGA;
decomposition: `.mathlib-quality/decomposition-omega-r1.md`.)**

The `(Ell/R)`-functoriality of the `S`-bases of `ω_{E/S}`: along a morphism of
`EllObj R` (a cartesian pointed square), a basis of the target's invariant
differential transports to a basis of the source's — `omegaBasisMap`, contravariantly
functorial. This is what makes the ω-rigidified moduli problems of KM Ch. 2/4
(T-E12 `(E, ω)`, T-E14 Legendre) statable as `ModuliProblem R` functors:
`P(X) := {…, b ∈ OmegaBasis X} , P(φ) := omegaBasisMap φ`.

Route: `pulledCocycle_res` identifies the pullback of the ω-cocycle affine-locally
with the transition units of the transported charts (a pointwise affine refinement
argument through `omegaCocycle_res` and the four transport/restriction coherences);
`omegaCompat` glues the mixed comparisons into `UnitCocycle.Compat` data; and
`Compat.sectionsEquiv` transports bases.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme

namespace ModularCurves

variable {R : CommRingCat.{u}}

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7)** The pullback of the ω-cocycle restricts, on affine opens, to the
transition unit of the transported charts. -/
private theorem pulledCocycle_res {X X' : EllObj R} (φ : X' ⟶ X)
    (i₁ i₂ : X.curve.toEllipticCurveGeom.atlas.ι)
    (V : X'.base.affineOpens)
    (hV : V.1 ≤
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).U i₁ ⊓
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).U i₂) :
    Scheme.resUnit hV
        (((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).u i₁ i₂) =
      ((X.curve.toEllipticCurveGeom.atlas.presentation i₁).transport φ.baseHom φ.top
          φ.isPullback φ.zero_w (hV.trans inf_le_left)).transUnit
        ((X.curve.toEllipticCurveGeom.atlas.presentation i₂).transport φ.baseHom φ.top
          φ.isPullback φ.zero_w (hV.trans inf_le_right)) := by
  -- pointwise choice of a factoring affine pair
  have hchoice : ∀ v : V.1,
      ∃ (WS : X.base.affineOpens) (Vv : X'.base.affineOpens),
      WS.1 ≤ (X.curve.toEllipticCurveGeom.atlas.U i₁).1 ⊓
        (X.curve.toEllipticCurveGeom.atlas.U i₂).1 ∧
      v.1 ∈ Vv.1 ∧ Vv.1 ≤ V.1 ∧ Vv.1 ≤ φ.baseHom ⁻¹ᵁ WS.1 := by
    intro v
    have hfv : φ.baseHom.base v.1 ∈ (X.curve.toEllipticCurveGeom.atlas.U i₁).1 ⊓
        (X.curve.toEllipticCurveGeom.atlas.U i₂).1 :=
      ⟨(hV v.2).1, (hV v.2).2⟩
    obtain ⟨WS₀, hWSaff, hfvWS, hWSle⟩ := exists_isAffineOpen_mem_and_subset hfv
    obtain ⟨Vv₀, hVvaff, hvVv, hVvle⟩ := exists_isAffineOpen_mem_and_subset
      (show v.1 ∈ V.1 ⊓ (φ.baseHom ⁻¹ᵁ WS₀) from ⟨v.2, hfvWS⟩)
    exact ⟨⟨WS₀, hWSaff⟩, ⟨Vv₀, hVvaff⟩, hWSle, hvVv,
      le_trans hVvle inf_le_left, le_trans hVvle inf_le_right⟩
  choose WS Vv hWS hvmem hVvV hVvW using hchoice
  refine Scheme.unit_ext_of_res_cover X'.base (fun v : V.1 => (Vv v).1) hVvV
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hvmem ⟨x, hx⟩⟩) (fun v => ?_)
  rw [Scheme.resUnit_resUnit]
  -- LHS: unfold the pulled unit and factor through `WS v`
  rw [Scheme.UnitCocycle.pullbackCocycle_resUnit (omegaCocycle X.curve.toEllipticCurveGeom)
    φ.baseHom i₁ i₂ ((hVvV v).trans hV)]
  rw [← Scheme.map_appLE_resUnit φ.baseHom
    (show (WS v).1 ≤ (omegaCocycle X.curve.toEllipticCurveGeom).U i₁ ⊓
      (omegaCocycle X.curve.toEllipticCurveGeom).U i₂ from hWS v) (hVvW v)]
  rw [show Scheme.resUnit (show (WS v).1 ≤
        (omegaCocycle X.curve.toEllipticCurveGeom).U i₁ ⊓
        (omegaCocycle X.curve.toEllipticCurveGeom).U i₂ from hWS v)
      ((omegaCocycle X.curve.toEllipticCurveGeom).u i₁ i₂) =
    ((X.curve.toEllipticCurveGeom.atlas.presentation i₁).restrict
        ((hWS v).trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i₂).restrict
        ((hWS v).trans inf_le_right)) from
    omegaCocycle_res X.curve.toEllipticCurveGeom i₁ i₂ (WS v) (hWS v)]
  -- now both sides are transition units of transported pairs over `Vv v`
  rw [show Units.map ((φ.baseHom.appLE (WS v).1 (Vv v).1 (hVvW v)).hom).toMonoidHom
      (((X.curve.toEllipticCurveGeom.atlas.presentation i₁).restrict
          ((hWS v).trans inf_le_left)).transUnit
        ((X.curve.toEllipticCurveGeom.atlas.presentation i₂).restrict
          ((hWS v).trans inf_le_right))) =
    (((X.curve.toEllipticCurveGeom.atlas.presentation i₁).restrict
        ((hWS v).trans inf_le_left)).transport φ.baseHom φ.top φ.isPullback φ.zero_w
        (hVvW v)).transUnit
      (((X.curve.toEllipticCurveGeom.atlas.presentation i₂).restrict
        ((hWS v).trans inf_le_right)).transport φ.baseHom φ.top φ.isPullback φ.zero_w
        (hVvW v)) from
    (transUnit_transport φ.baseHom φ.top φ.isPullback φ.zero_w _ _ (hVvW v)).symm]
  rw [transUnit_restrict_pair_transport φ.baseHom φ.top φ.isPullback φ.zero_w _ _
    ((hWS v).trans inf_le_left) ((hWS v).trans inf_le_right) (hVvW v)]
  -- RHS: restrict the transported pair
  rw [← transUnit_restrict _ _ (hVvV v),
    transUnit_transport_pair_restrict φ.baseHom φ.top φ.isPullback φ.zero_w _ _
      (hV.trans inf_le_left) (hV.trans inf_le_right) (hVvV v)]

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- The glued mixed comparison unit of an own-chart against a transported chart. -/
private noncomputable def omegaCompatGlue {X X' : EllObj R} (φ : X' ⟶ X)
    (i' : X'.curve.toEllipticCurveGeom.atlas.ι)
    (i : X.curve.toEllipticCurveGeom.atlas.ι) :
    { g : Γ(X'.base, (omegaCocycle X'.curve.toEllipticCurveGeom).U i' ⊓
        ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).U i)ˣ //
      ∀ (V : X'.base.affineOpens)
        (hV : V.1 ≤ (omegaCocycle X'.curve.toEllipticCurveGeom).U i' ⊓
          ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).U i),
        Scheme.resUnit hV g =
          ((X'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
            (hV.trans inf_le_left)).transUnit
          ((X.curve.toEllipticCurveGeom.atlas.presentation i).transport φ.baseHom φ.top
            φ.isPullback φ.zero_w (hV.trans inf_le_right)) } := by
  have hglue := Scheme.exists_unit_glue X'.base
    ((omegaCocycle X'.curve.toEllipticCurveGeom).U i' ⊓
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).U i)
    (fun V hV =>
      ((X'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        (hV.trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).transport φ.baseHom φ.top
        φ.isPullback φ.zero_w (hV.trans inf_le_right)))
    (fun V V' hV h => by
      rw [← transUnit_restrict _ _ h,
        transUnit_restrict_transport φ.baseHom φ.top φ.isPullback φ.zero_w _ _
          (hV.trans inf_le_left) (hV.trans inf_le_right) h])
  exact ⟨hglue.choose, hglue.choose_spec.1⟩

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7)** The comparison data between the source's own ω-cocycle and the
pullback of the target's ω-cocycle along a morphism of `Ell/R`. -/
noncomputable def omegaCompat {X X' : EllObj R} (φ : X' ⟶ X) :
    (omegaCocycle X'.curve.toEllipticCurveGeom).Compat
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom) where
  w i' i := (omegaCompatGlue φ i' i).1
  left i'₁ i'₂ i := Scheme.unit_ext_of_affine_res X'.base (fun V hV => by
    rw [map_mul, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit,
      (omegaCompatGlue φ i'₂ i).2 V _, (omegaCompatGlue φ i'₁ i).2 V _,
      show Scheme.resUnit (show V.1 ≤
          (omegaCocycle X'.curve.toEllipticCurveGeom).U i'₁ ⊓
          (omegaCocycle X'.curve.toEllipticCurveGeom).U i'₂ from hV.trans inf_le_left)
        ((omegaCocycle X'.curve.toEllipticCurveGeom).u i'₁ i'₂) =
      ((X'.curve.toEllipticCurveGeom.atlas.presentation i'₁).restrict
          ((hV.trans inf_le_left).trans inf_le_left)).transUnit
        ((X'.curve.toEllipticCurveGeom.atlas.presentation i'₂).restrict
          ((hV.trans inf_le_left).trans inf_le_right)) from
      omegaCocycle_res X'.curve.toEllipticCurveGeom i'₁ i'₂ V (hV.trans inf_le_left),
      transUnit_trans])
  right i' i₁ i₂ := Scheme.unit_ext_of_affine_res X'.base (fun V hV => by
    rw [map_mul, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit,
      (omegaCompatGlue φ i' i₁).2 V _, (omegaCompatGlue φ i' i₂).2 V _,
      pulledCocycle_res φ i₁ i₂ V _,
      transUnit_trans])

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7 ★★)** Base change of `ω`-bases along a morphism of `Ell/R`: pull the
compatible unit family back componentwise, then transport through the cocycle
comparison. This is the datum that makes the ω-rigidified moduli problems
(T-E12/T-E14) functors on `(Ell/R)ᵒᵖ`. -/
noncomputable def omegaBasisMap {X X' : EllObj R} (φ : X' ⟶ X)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    OmegaBasis X'.curve.toEllipticCurveGeom :=
  ⟨(omegaCompat φ).sectionsEquiv ⊤
    (((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).sectionsMap
      (show (⊤ : X'.base.Opens) ≤ φ.baseHom ⁻¹ᵁ (⊤ : X.base.Opens) from
        fun x _ => trivial)
      ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback φ.baseHom b.1)),
   by
    rw [Scheme.UnitCocycle.Compat.isBasis_sectionsEquiv]
    exact Scheme.UnitCocycle.IsBasis.sectionsMap _ _
      (Scheme.UnitCocycle.isBasis_sectionsPullback
        (omegaCocycle X.curve.toEllipticCurveGeom) φ.baseHom b.2)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7)** `omegaBasisMap` is equivariant for the global-unit actions through
the section comparison of the base morphism — with `negVC_u`, KM 4.6.2's
`{±1}`-action transports along every `Ell/R`-morphism. -/
theorem omegaBasisMap_smul {X X' : EllObj R} (φ : X' ⟶ X) (g : Γ(X.base, ⊤)ˣ)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    omegaBasisMap φ (g • b) =
      Units.map ((φ.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom).toMonoidHom g •
        omegaBasisMap φ b := by
  refine Subtype.ext ?_
  have h1 : ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback φ.baseHom
      (g • b).1) =
    ((φ.baseHom.appLE ⊤ (φ.baseHom ⁻¹ᵁ (⊤ : X.base.Opens)) le_rfl).hom g.val) •
      ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback φ.baseHom b.1) :=
    Scheme.UnitCocycle.sectionsPullback_smul
      (omegaCocycle X.curve.toEllipticCurveGeom) φ.baseHom g.val b.1
  show ((omegaCompat φ).sectionsEquiv ⊤)
      (((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
        φ.baseHom).sectionsMap _
      ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback φ.baseHom
        (g • b).1)) = _
  rw [h1, Scheme.UnitCocycle.sectionsMap_smul, map_smul]
  show _ • ((omegaCompat φ).sectionsEquiv ⊤) _ = _
  congr 1
  rw [Scheme.resLE_appLE]
  rfl

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- The mixed comparison at the identity is the transition cocycle itself. -/
private theorem omegaCompat_id_w (X : EllObj R)
    (i' i : X.curve.toEllipticCurveGeom.atlas.ι) :
    (omegaCompat (𝟙 X)).w i' i =
      Scheme.resUnit (le_inf inf_le_left inf_le_right)
        ((omegaCocycle X.curve.toEllipticCurveGeom).u i' i) := by
  refine Scheme.unit_ext_of_affine_res X.base (fun V hV => ?_)
  rw [show (omegaCompat (𝟙 X)).w i' i = (omegaCompatGlue (𝟙 X) i' i).1 from rfl,
    (omegaCompatGlue (𝟙 X) i' i).2 V hV]
  refine Units.ext ?_
  have hval := congrArg Units.val (omegaCocycle_res X.curve.toEllipticCurveGeom i' i V
    (hV.trans (le_inf inf_le_left inf_le_right)))
  simp only [Scheme.resUnit_val, Scheme.resLE_resLE] at hval ⊢
  erw [Scheme.resLE_resLE]
  exact hval.symm

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7)** The identity morphism induces the identity on `ω`-bases: the mixed
comparison at `𝟙 X` is the transition cocycle itself, so the glued transport is
compatibility. -/
theorem omegaBasisMap_id (X : EllObj R) (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    omegaBasisMap (𝟙 X) b = b := by
  refine Subtype.ext (Subtype.ext (funext fun i' => ?_))
  -- separation over the chart cover of `⊤ ⊓ U i'`
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun j : X.curve.toEllipticCurveGeom.atlas.ι =>
      (⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
        ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (𝟙 X : X ⟶ X).baseHom).U j)
    ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i')
    (fun j => homOfLE inf_le_left) (by
      intro x hx
      obtain ⟨j, hxj⟩ := X.curve.toEllipticCurveGeom.atlas.covers x
      exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩) _ _ (fun j => ?_)
  -- the transported component's local description
  show Scheme.resLE inf_le_left
      (((omegaCompat (𝟙 X)).transportFun _).1 i') = Scheme.resLE inf_le_left (b.1.1 i')
  rw [(omegaCompat (𝟙 X)).transportFun_res _ i' j]
  -- rewrite the comparison as the cocycle and the pulled component as a restriction
  rw [show ((omegaCompat (𝟙 X)).w i' j) =
    Scheme.resUnit (le_inf inf_le_left inf_le_right)
      ((omegaCocycle X.curve.toEllipticCurveGeom).u i' j) from omegaCompat_id_w X i' j]
  -- both sides are now restriction-chains of `u i' j · b j` vs `b i'`; conclude by
  -- the compatibility of `b`
  have hb := congrArg (⇑(Scheme.resLE (X := X.base)
    (show (⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
        ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (𝟙 X : X ⟶ X).baseHom).U j ≤
      (⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
        (omegaCocycle X.curve.toEllipticCurveGeom).U j from le_rfl))) (b.1.2 i' j)
  simp only [Scheme.resUnit_val, Scheme.resLE_resLE, map_mul] at hb ⊢
  rw [hb]
  congr 1
  · erw [Scheme.resLE_resLE]
  -- the pulled `j`-component is the restriction of `b j`
  rw [show ((((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
      (𝟙 X : X ⟶ X).baseHom).sectionsMap
      (show (⊤ : X.base.Opens) ≤ (𝟙 X : X ⟶ X).baseHom ⁻¹ᵁ
        (⊤ : X.base.Opens) from fun x _ => trivial)
      ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback
        (𝟙 X : X ⟶ X).baseHom b.1)).1 j) =
    Scheme.resLE (inf_le_inf_right _ (show (⊤ : X.base.Opens) ≤ ⊤ from le_rfl))
      (sectionsMapLE (𝟙 X.base)
        (show ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U j : X.base.Opens) ≤
          (𝟙 X.base : X.base ⟶ X.base) ⁻¹ᵁ ((⊤ : X.base.Opens) ⊓
            (omegaCocycle X.curve.toEllipticCurveGeom).U j) from fun _ hy => hy)
        (b.1.1 j)) from rfl,
    sectionsMapLE_id]
  exact (Scheme.resLE_resLE _ _ _).trans (Scheme.resLE_resLE _ _ _)

end ModularCurves
