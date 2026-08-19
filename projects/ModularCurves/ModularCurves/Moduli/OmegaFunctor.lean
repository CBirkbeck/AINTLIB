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

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4, public spec)** The mixed comparison unit restricts, on affine opens, to
the transition unit of the own chart against the transported chart. -/
theorem omegaCompat_w_res {X X' : EllObj R} (φ : X' ⟶ X)
    (i' : X'.curve.toEllipticCurveGeom.atlas.ι)
    (i : X.curve.toEllipticCurveGeom.atlas.ι)
    (V : X'.base.affineOpens)
    (hV : V.1 ≤ (omegaCocycle X'.curve.toEllipticCurveGeom).U i' ⊓
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom).U i) :
    Scheme.resUnit hV ((omegaCompat φ).w i' i) =
      ((X'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        (hV.trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).transport φ.baseHom φ.top
        φ.isPullback φ.zero_w (hV.trans inf_le_right)) := by
  show Scheme.resUnit hV ((omegaCompatGlue φ i' i).1) = _
  exact (omegaCompatGlue φ i' i).2 V hV

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

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- The mixed comparison of a composite factors through the two comparisons: the
cocycle condition of the ω-functoriality, affine-locally at the value level. -/
private theorem omegaCompat_comp_w_val {X X' X'' : EllObj R} (φ : X'' ⟶ X') (ψ : X' ⟶ X)
    (i'' : X''.curve.toEllipticCurveGeom.atlas.ι)
    (j' : X'.curve.toEllipticCurveGeom.atlas.ι)
    (j : X.curve.toEllipticCurveGeom.atlas.ι)
    (V : X''.base.Opens)
    (h1 : V ≤ (omegaCocycle X''.curve.toEllipticCurveGeom).U i'')
    (h2 : V ≤ φ.baseHom ⁻¹ᵁ (omegaCocycle X'.curve.toEllipticCurveGeom).U j')
    (h3 : V ≤ φ.baseHom ⁻¹ᵁ
      (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)) :
    Scheme.resLE (le_inf h1 h3) ((omegaCompat (φ ≫ ψ)).w i'' j).val =
      Scheme.resLE (le_inf h1 h2) ((omegaCompat φ).w i'' j').val *
      (φ.baseHom.appLE
          ((omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
            (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)) V
          (fun _ hy => ⟨h2 hy, h3 hy⟩)).hom ((omegaCompat ψ).w j' j).val := by
  -- pointwise choice: an affine `W'` around `φ(v)` inside the mixed ψ-overlap, and an
  -- affine `Vv` around `v` inside `V ⊓ φ⁻¹W'`
  have hchoice : ∀ v : V,
      ∃ (W' : X'.base.affineOpens) (Vv : X''.base.affineOpens),
      W'.1 ≤ (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
        (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j) ∧
      v.1 ∈ Vv.1 ∧ Vv.1 ≤ V ∧ Vv.1 ≤ φ.baseHom ⁻¹ᵁ W'.1 := by
    intro v
    obtain ⟨W₀, hWaff, hfvW, hWle⟩ := exists_isAffineOpen_mem_and_subset
      (show φ.baseHom.base v.1 ∈ (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
        (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j) from
        ⟨h2 v.2, h3 v.2⟩)
    obtain ⟨Vv₀, hVvaff, hvVv, hVvle⟩ := exists_isAffineOpen_mem_and_subset
      (show v.1 ∈ V ⊓ (φ.baseHom ⁻¹ᵁ W₀) from ⟨v.2, hfvW⟩)
    exact ⟨⟨W₀, hWaff⟩, ⟨Vv₀, hVvaff⟩, hWle, hvVv,
      le_trans hVvle inf_le_left, le_trans hVvle inf_le_right⟩
  choose W' Vv hW' hvmem hVvV hVvW using hchoice
  refine TopCat.Sheaf.eq_of_locally_eq' X''.base.sheaf (fun v : V => (Vv v).1) V
    (fun v => homOfLE (hVvV v)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hvmem ⟨x, hx⟩⟩)
    _ _ (fun v => ?_)
  show Scheme.resLE (hVvV v) _ = Scheme.resLE (hVvV v) _
  rw [map_mul, Scheme.resLE_resLE, Scheme.resLE_resLE]
  -- the glue characterizations, at the value level
  have hL : Scheme.resLE ((hVvV v).trans (le_inf h1 h3))
      ((omegaCompat (φ ≫ ψ)).w i'' j).val =
    (((X''.curve.toEllipticCurveGeom.atlas.presentation i'').restrict
        (((hVvV v).trans (le_inf h1 h3)).trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport
        (φ ≫ ψ).baseHom (φ ≫ ψ).top (φ ≫ ψ).isPullback (φ ≫ ψ).zero_w
        (((hVvV v).trans (le_inf h1 h3)).trans inf_le_right))).val := by
    have h0 := congrArg Units.val ((omegaCompatGlue (φ ≫ ψ) i'' j).2 (Vv v)
      ((hVvV v).trans (le_inf h1 h3)))
    rw [Scheme.resUnit_val] at h0
    exact h0
  have hF : Scheme.resLE ((hVvV v).trans (le_inf h1 h2))
      ((omegaCompat φ).w i'' j').val =
    (((X''.curve.toEllipticCurveGeom.atlas.presentation i'').restrict
        (((hVvV v).trans (le_inf h1 h2)).trans inf_le_left)).transUnit
      ((X'.curve.toEllipticCurveGeom.atlas.presentation j').transport φ.baseHom φ.top
        φ.isPullback φ.zero_w
        (((hVvV v).trans (le_inf h1 h2)).trans inf_le_right))).val := by
    have h0 := congrArg Units.val ((omegaCompatGlue φ i'' j').2 (Vv v)
      ((hVvV v).trans (le_inf h1 h2)))
    rw [Scheme.resUnit_val] at h0
    exact h0
  have hΨ : Scheme.resLE (hW' v) ((omegaCompat ψ).w j' j).val =
    (((X'.curve.toEllipticCurveGeom.atlas.presentation j').restrict
        ((hW' v).trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport ψ.baseHom ψ.top
        ψ.isPullback ψ.zero_w ((hW' v).trans inf_le_right))).val := by
    have h0 := congrArg Units.val ((omegaCompatGlue ψ j' j).2 (W' v) (hW' v))
    rw [Scheme.resUnit_val] at h0
    exact h0
  -- push the ψ-comparison through `φ` (unit-level transport naturality)
  have hT := congrArg Units.val
    (transUnit_transport φ.baseHom φ.top φ.isPullback φ.zero_w
      ((X'.curve.toEllipticCurveGeom.atlas.presentation j').restrict
        ((hW' v).trans inf_le_left))
      ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport ψ.baseHom ψ.top
        ψ.isPullback ψ.zero_w ((hW' v).trans inf_le_right)) (hVvW v))
  -- normalize the pushed pair to composite transports
  have hN := transUnit_congr
    (((X'.curve.toEllipticCurveGeom.atlas.presentation j').restrict
        ((hW' v).trans inf_le_left)).transport φ.baseHom φ.top φ.isPullback φ.zero_w
        (hVvW v))
    (((X.curve.toEllipticCurveGeom.atlas.presentation j).transport ψ.baseHom ψ.top
        ψ.isPullback ψ.zero_w ((hW' v).trans inf_le_right)).transport φ.baseHom φ.top
        φ.isPullback φ.zero_w (hVvW v))
    ((X'.curve.toEllipticCurveGeom.atlas.presentation j').transport φ.baseHom φ.top
        φ.isPullback φ.zero_w
        ((hVvW v).trans ((Opens.map φ.baseHom.base).map
          (homOfLE ((hW' v).trans inf_le_left))).le))
    ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport
        (φ.baseHom ≫ ψ.baseHom) (φ.top ≫ ψ.top) (φ.isPullback.paste_horiz ψ.isPullback)
        (by rw [← Category.assoc, φ.zero_w, Category.assoc, ψ.zero_w, ← Category.assoc])
        ((hVvW v).trans ((Opens.map φ.baseHom.base).map
          (homOfLE ((hW' v).trans inf_le_right))).le))
    (by
      show (X'.curve.toEllipticCurveGeom.atlas.presentation j').W.map _ =
        ((X'.curve.toEllipticCurveGeom.atlas.presentation j').W.map _).map _
      rw [WeierstrassCurve.map_map]
      congr 1
      rw [sectionsMapLE_id, resLE_comp_sectionsMapLE φ.baseHom _ (hVvW v)])
    (by
      show (X.curve.toEllipticCurveGeom.atlas.presentation j).W.map _ =
        ((X.curve.toEllipticCurveGeom.atlas.presentation j).W.map _).map _
      rw [WeierstrassCurve.map_map]
      congr 1
      rw [sectionsMapLE_comp φ.baseHom ψ.baseHom ((hW' v).trans inf_le_right) (hVvW v)])
    (transportE_transport_restrict φ.baseHom φ.top φ.isPullback φ.zero_w
      (X'.curve.toEllipticCurveGeom.atlas.presentation j')
      ((hW' v).trans inf_le_left) (hVvW v))
    (transportE_transport_transport φ.baseHom ψ.baseHom φ.top ψ.top
      φ.isPullback ψ.isPullback φ.zero_w ψ.zero_w
      (X.curve.toEllipticCurveGeom.atlas.presentation j)
      ((hW' v).trans inf_le_right) (hVvW v))
  -- the cocycle chain at composite transports
  have hC := transUnit_trans
    ((X''.curve.toEllipticCurveGeom.atlas.presentation i'').restrict
      (((hVvV v).trans (le_inf h1 h2)).trans inf_le_left))
    ((X'.curve.toEllipticCurveGeom.atlas.presentation j').transport φ.baseHom φ.top
      φ.isPullback φ.zero_w
      ((hVvW v).trans ((Opens.map φ.baseHom.base).map
        (homOfLE ((hW' v).trans inf_le_left))).le))
    ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport
      (φ.baseHom ≫ ψ.baseHom) (φ.top ≫ ψ.top) (φ.isPullback.paste_horiz ψ.isPullback)
      (by rw [← Category.assoc, φ.zero_w, Category.assoc, ψ.zero_w, ← Category.assoc])
      ((hVvW v).trans ((Opens.map φ.baseHom.base).map
        (homOfLE ((hW' v).trans inf_le_right))).le))
  -- assemble
  calc Scheme.resLE ((hVvV v).trans (le_inf h1 h3))
        ((omegaCompat (φ ≫ ψ)).w i'' j).val
      = (((X''.curve.toEllipticCurveGeom.atlas.presentation i'').restrict
            (((hVvV v).trans (le_inf h1 h3)).trans inf_le_left)).transUnit
          ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport
            (φ ≫ ψ).baseHom (φ ≫ ψ).top (φ ≫ ψ).isPullback (φ ≫ ψ).zero_w
            (((hVvV v).trans (le_inf h1 h3)).trans inf_le_right))).val := hL
    _ = (((X''.curve.toEllipticCurveGeom.atlas.presentation i'').restrict
            (((hVvV v).trans (le_inf h1 h2)).trans inf_le_left)).transUnit
          ((X'.curve.toEllipticCurveGeom.atlas.presentation j').transport φ.baseHom
            φ.top φ.isPullback φ.zero_w
            ((hVvW v).trans ((Opens.map φ.baseHom.base).map
              (homOfLE ((hW' v).trans inf_le_left))).le)) *
        ((X'.curve.toEllipticCurveGeom.atlas.presentation j').transport φ.baseHom
            φ.top φ.isPullback φ.zero_w
            ((hVvW v).trans ((Opens.map φ.baseHom.base).map
              (homOfLE ((hW' v).trans inf_le_left))).le)).transUnit
          ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport
            (φ.baseHom ≫ ψ.baseHom) (φ.top ≫ ψ.top)
            (φ.isPullback.paste_horiz ψ.isPullback)
            (by rw [← Category.assoc, φ.zero_w, Category.assoc, ψ.zero_w,
              ← Category.assoc])
            ((hVvW v).trans ((Opens.map φ.baseHom.base).map
              (homOfLE ((hW' v).trans inf_le_right))).le))).val := by
        rw [hC]
        rfl
    _ = Scheme.resLE ((hVvV v).trans (le_inf h1 h2)) ((omegaCompat φ).w i'' j').val *
        Scheme.resLE (hVvV v)
          ((φ.baseHom.appLE
            ((omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
              (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)) V
            (fun _ hy => ⟨h2 hy, h3 hy⟩)).hom ((omegaCompat ψ).w j' j).val) := by
        rw [Units.val_mul]
        congr 1
        · exact hF.symm
        · rw [show Scheme.resLE (hVvV v)
              ((φ.baseHom.appLE
                ((omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
                  (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)) V
                (fun _ hy => ⟨h2 hy, h3 hy⟩)).hom ((omegaCompat ψ).w j' j).val) =
            (φ.baseHom.appLE (W' v).1 (Vv v).1 (hVvW v)).hom
              (Scheme.resLE (hW' v) ((omegaCompat ψ).w j' j).val) from by
              rw [Scheme.resLE_appLE, Scheme.appLE_resLE]]
          rw [hΨ]
          rw [show (φ.baseHom.appLE (W' v).1 (Vv v).1 (hVvW v)).hom
              ((((X'.curve.toEllipticCurveGeom.atlas.presentation j').restrict
                  ((hW' v).trans inf_le_left)).transUnit
                ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport ψ.baseHom
                  ψ.top ψ.isPullback ψ.zero_w ((hW' v).trans inf_le_right))).val) =
            (Units.map ((sectionsMapLE φ.baseHom (hVvW v)).toMonoidHom)
              (((X'.curve.toEllipticCurveGeom.atlas.presentation j').restrict
                  ((hW' v).trans inf_le_left)).transUnit
                ((X.curve.toEllipticCurveGeom.atlas.presentation j).transport ψ.baseHom
                  ψ.top ψ.isPullback ψ.zero_w ((hW' v).trans inf_le_right)))).val
            from rfl]
          rw [← hT]
          exact (congrArg Units.val hN).symm

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7 ★★)** Contravariant functoriality of the ω-base-change: transporting a
basis along a composite is the composite of the transports. With `omegaBasisMap_id`
and `omegaBasisMap_smul` this makes the ω-rigidified moduli problems functors on
`(Ell/R)ᵒᵖ`. -/
theorem omegaBasisMap_comp {X X' X'' : EllObj R} (φ : X'' ⟶ X') (ψ : X' ⟶ X)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    omegaBasisMap (φ ≫ ψ) b = omegaBasisMap φ (omegaBasisMap ψ b) := by
  refine Subtype.ext (Subtype.ext (funext fun i'' => ?_))
  -- separation over the double chart cover
  refine TopCat.Sheaf.eq_of_locally_eq' X''.base.sheaf
    (fun p : X'.curve.toEllipticCurveGeom.atlas.ι ×
        X.curve.toEllipticCurveGeom.atlas.ι =>
      ((⊤ : X''.base.Opens) ⊓ (omegaCocycle X''.curve.toEllipticCurveGeom).U i'') ⊓
        (φ.baseHom ⁻¹ᵁ (omegaCocycle X'.curve.toEllipticCurveGeom).U p.1) ⊓
        (φ.baseHom ⁻¹ᵁ (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U p.2)))
    ((⊤ : X''.base.Opens) ⊓ (omegaCocycle X''.curve.toEllipticCurveGeom).U i'')
    (fun p => homOfLE (inf_le_left.trans inf_le_left)) (by
      intro x hx
      obtain ⟨j', hxj'⟩ := X'.curve.toEllipticCurveGeom.atlas.covers (φ.baseHom.base x)
      obtain ⟨j, hxj⟩ := X.curve.toEllipticCurveGeom.atlas.covers
        (ψ.baseHom.base (φ.baseHom.base x))
      exact Opens.mem_iSup.mpr ⟨⟨j', j⟩, ⟨hx, hxj'⟩, hxj⟩) _ _ (fun p => ?_)
  obtain ⟨j', j⟩ := p
  -- the piece and its inclusions
  set T := ((⊤ : X''.base.Opens) ⊓ (omegaCocycle X''.curve.toEllipticCurveGeom).U i'') ⊓
    (φ.baseHom ⁻¹ᵁ (omegaCocycle X'.curve.toEllipticCurveGeom).U j') ⊓
    (φ.baseHom ⁻¹ᵁ (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j))
    with hT
  -- LHS: expand the composite transport at (i'', j) and restrict to `T`
  have hLHS := congrArg (⇑(Scheme.resLE (X := X''.base)
    (show T ≤ (⊤ : X''.base.Opens) ⊓
        (omegaCocycle X''.curve.toEllipticCurveGeom).U i'' ⊓
        ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (φ ≫ ψ).baseHom).U j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)))
    ((omegaCompat (φ ≫ ψ)).transportFun_res
      (((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (φ ≫ ψ).baseHom).sectionsMap
        (show (⊤ : X''.base.Opens) ≤ (φ ≫ ψ).baseHom ⁻¹ᵁ (⊤ : X.base.Opens) from
          fun x _ => trivial)
        ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback
          (φ ≫ ψ).baseHom b.1)) i'' j)
  simp only [Scheme.resUnit_val, map_mul, Scheme.resLE_resLE] at hLHS
  -- RHS: expand the φ-transport at (i'', j') and restrict to `T`
  have hRHS := congrArg (⇑(Scheme.resLE (X := X''.base)
    (show T ≤ (⊤ : X''.base.Opens) ⊓
        (omegaCocycle X''.curve.toEllipticCurveGeom).U i'' ⊓
        ((omegaCocycle X'.curve.toEllipticCurveGeom).pullbackCocycle
          φ.baseHom).U j' from
      le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))))
    ((omegaCompat φ).transportFun_res
      (((omegaCocycle X'.curve.toEllipticCurveGeom).pullbackCocycle
          φ.baseHom).sectionsMap
        (show (⊤ : X''.base.Opens) ≤ φ.baseHom ⁻¹ᵁ (⊤ : X'.base.Opens) from
          fun x _ => trivial)
        ((omegaCocycle X'.curve.toEllipticCurveGeom).sectionsPullback
          φ.baseHom (omegaBasisMap ψ b).1)) i'' j')
  simp only [Scheme.resUnit_val, map_mul, Scheme.resLE_resLE] at hRHS
  show Scheme.resLE (inf_le_left.trans inf_le_left)
      (((omegaCompat (φ ≫ ψ)).transportFun _).1 i'') =
    Scheme.resLE (inf_le_left.trans inf_le_left)
      (((omegaCompat φ).transportFun _).1 i'')
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  -- the piece's inclusions
  have hT1 : T ≤ (omegaCocycle X''.curve.toEllipticCurveGeom).U i'' :=
    (inf_le_left.trans inf_le_left).trans inf_le_right
  have hT2 : T ≤ φ.baseHom ⁻¹ᵁ (omegaCocycle X'.curve.toEllipticCurveGeom).U j' :=
    inf_le_left.trans inf_le_right
  have hT3 : T ≤ φ.baseHom ⁻¹ᵁ
      (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j) :=
    inf_le_right
  -- the cocycle condition of the mixed comparisons
  have hW := omegaCompat_comp_w_val φ ψ i'' j' j T hT1 hT2 hT3
  -- the pulled `b`-component of the composite side is a single composite pullback
  have hBL : Scheme.resLE (X := X''.base)
      (le_inf le_top inf_le_right : T ≤ (⊤ : X''.base.Opens) ⊓
        (φ.baseHom ⁻¹ᵁ (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)))
      ((((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (φ ≫ ψ).baseHom).sectionsMap
        (show (⊤ : X''.base.Opens) ≤ (φ ≫ ψ).baseHom ⁻¹ᵁ (⊤ : X.base.Opens) from
          fun x _ => trivial)
        ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback
          (φ ≫ ψ).baseHom b.1)).1 j) =
      ((φ ≫ ψ).baseHom.appLE
        ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U j) T
        (fun _ hx => ⟨trivial, hx.2⟩)).hom (b.1.1 j) :=
    (Scheme.resLE_resLE _ _ _).trans (Scheme.resLE_appLE _ _ _ _)
  -- the pulled `b`-component of the two-step side, before the inner expansion
  have hBR : Scheme.resLE (X := X''.base)
      (le_inf le_top (inf_le_left.trans inf_le_right) : T ≤ (⊤ : X''.base.Opens) ⊓
        (φ.baseHom ⁻¹ᵁ (omegaCocycle X'.curve.toEllipticCurveGeom).U j'))
      ((((omegaCocycle X'.curve.toEllipticCurveGeom).pullbackCocycle
          φ.baseHom).sectionsMap
        (show (⊤ : X''.base.Opens) ≤ φ.baseHom ⁻¹ᵁ (⊤ : X'.base.Opens) from
          fun x _ => trivial)
        ((omegaCocycle X'.curve.toEllipticCurveGeom).sectionsPullback
          φ.baseHom (omegaBasisMap ψ b).1)).1 j') =
      (φ.baseHom.appLE
        ((⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j') T
        (fun _ hx => ⟨trivial, hx.1.2⟩)).hom ((omegaBasisMap ψ b).1.1 j') :=
    (Scheme.resLE_resLE _ _ _).trans (Scheme.resLE_appLE _ _ _ _)
  -- the inner expansion: pull the ψ-transport description through `φ`
  have hψ : (φ.baseHom.appLE
        ((⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j') T
        (fun _ hx => ⟨trivial, hx.1.2⟩)).hom ((omegaBasisMap ψ b).1.1 j') =
      (φ.baseHom.appLE
        ((omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
          (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)) T
        (fun _ hx => ⟨hx.1.2, hx.2⟩)).hom ((omegaCompat ψ).w j' j).val *
      ((φ ≫ ψ).baseHom.appLE
        ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U j) T
        (fun _ hx => ⟨trivial, hx.2⟩)).hom (b.1.1 j) := by
    -- insert the restriction to the mixed triple on `X'`
    rw [show (φ.baseHom.appLE
        ((⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j') T
        (fun _ hx => ⟨trivial, hx.1.2⟩)).hom ((omegaBasisMap ψ b).1.1 j') =
      (φ.baseHom.appLE
        ((⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
          ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j) T
        (fun _ hx => ⟨⟨trivial, hx.1.2⟩, hx.2⟩)).hom
        (Scheme.resLE inf_le_left ((omegaBasisMap ψ b).1.1 j')) from
      (Scheme.appLE_resLE φ.baseHom inf_le_left _ _).symm]
    rw [show Scheme.resLE (X := X'.base) (inf_le_left :
          (⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j ≤
          (⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j')
        ((omegaBasisMap ψ b).1.1 j') =
      Scheme.resLE (show (⊤ : X'.base.Opens) ⊓
            (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j ≤
          (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j
          by order) ((omegaCompat ψ).w j' j).val *
      Scheme.resLE (show (⊤ : X'.base.Opens) ⊓
            (omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j ≤
          (⊤ : X'.base.Opens) ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j
          by order)
        ((((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
            ψ.baseHom).sectionsMap
          (show (⊤ : X'.base.Opens) ≤ ψ.baseHom ⁻¹ᵁ (⊤ : X.base.Opens) from
            fun x _ => trivial)
          ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback
            ψ.baseHom b.1)).1 j) from
      (omegaCompat ψ).transportFun_res _ j' j]
    rw [map_mul]
    congr 1
    · -- the `w`-factor: collapse the pullback of a restriction
      exact Scheme.appLE_resLE φ.baseHom _ _ _
    · -- the `b`-factor: two-step pullback is the composite pullback
      refine Eq.trans (congrArg (φ.baseHom.appLE _ T _).hom
        (Scheme.resLE_resLE _ _ _)) ?_
      refine Eq.trans (Scheme.appLE_resLE φ.baseHom _ _ _) ?_
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.Hom.appLE_comp_appLE φ.baseHom ψ.baseHom
          ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U j)
          (ψ.baseHom ⁻¹ᵁ (⊤ : X.base.Opens) ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle ψ.baseHom).U j)
          T (fun _ hx => ⟨trivial, hx.2⟩) (fun _ hx => ⟨trivial, hx.2⟩)))
        (b.1.1 j)
  calc Scheme.resLE (le_inf hT1 hT3) ((omegaCompat (φ ≫ ψ)).w i'' j).val *
        Scheme.resLE (X := X''.base)
          (le_inf le_top inf_le_right : T ≤ (⊤ : X''.base.Opens) ⊓
            (φ.baseHom ⁻¹ᵁ (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)))
          ((((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
              (φ ≫ ψ).baseHom).sectionsMap
            (show (⊤ : X''.base.Opens) ≤ (φ ≫ ψ).baseHom ⁻¹ᵁ (⊤ : X.base.Opens) from
              fun x _ => trivial)
            ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback
              (φ ≫ ψ).baseHom b.1)).1 j)
      = Scheme.resLE (le_inf hT1 hT2) ((omegaCompat φ).w i'' j').val *
          ((φ.baseHom.appLE
            ((omegaCocycle X'.curve.toEllipticCurveGeom).U j' ⊓
              (ψ.baseHom ⁻¹ᵁ (omegaCocycle X.curve.toEllipticCurveGeom).U j)) T
            (fun _ hx => ⟨hx.1.2, hx.2⟩)).hom ((omegaCompat ψ).w j' j).val *
          ((φ ≫ ψ).baseHom.appLE
            ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U j) T
            (fun _ hx => ⟨trivial, hx.2⟩)).hom (b.1.1 j)) :=
        (congrArg₂ (· * ·) hW hBL).trans (mul_assoc _ _ _)
    _ = Scheme.resLE (le_inf hT1 hT2) ((omegaCompat φ).w i'' j').val *
          (φ.baseHom.appLE
            ((⊤ : X'.base.Opens) ⊓ (omegaCocycle X'.curve.toEllipticCurveGeom).U j') T
            (fun _ hx => ⟨trivial, hx.1.2⟩)).hom ((omegaBasisMap ψ b).1.1 j') := by
        rw [hψ]
    _ = Scheme.resLE (le_inf hT1 hT2) ((omegaCompat φ).w i'' j').val *
          Scheme.resLE (X := X''.base)
            (le_inf le_top (inf_le_left.trans inf_le_right) : T ≤ (⊤ : X''.base.Opens) ⊓
              (φ.baseHom ⁻¹ᵁ (omegaCocycle X'.curve.toEllipticCurveGeom).U j'))
            ((((omegaCocycle X'.curve.toEllipticCurveGeom).pullbackCocycle
                φ.baseHom).sectionsMap
              (show (⊤ : X''.base.Opens) ≤ φ.baseHom ⁻¹ᵁ (⊤ : X'.base.Opens) from
                fun x _ => trivial)
              ((omegaCocycle X'.curve.toEllipticCurveGeom).sectionsPullback
                φ.baseHom (omegaBasisMap ψ b).1)).1 j') :=
        congrArg₂ (· * ·) rfl hBR.symm

/-- **(T-OM-B7 payload; KM 4.6.2, GME §2.2)** The **ω-moduli problem** `[(E, ω)]`:
to `E/S` assign the set of `S`-bases of the invariant differential `ω_{E/S}`,
contravariantly functorial along `Ell/R`-morphisms by `omegaBasisMap`. This is the
`ω`-half of every rigidified problem of KM Ch. 2/4 — T-E12 (`(E, ω)` itself), T-E13
(its rigidity), T-E14 (Legendre = `Γ(2)`-naive × ω). -/
noncomputable def omegaProblem (R : CommRingCat.{u}) : ModuliProblem R where
  obj X := OmegaBasis X.unop.curve.toEllipticCurveGeom
  map φ := ↾fun b => omegaBasisMap φ.unop b
  map_id X := by ext b; exact omegaBasisMap_id X.unop b
  map_comp φ ψ := by ext b; exact omegaBasisMap_comp ψ.unop φ.unop b

/-! ### T-OM-B9: the inversion acts by `−1` on ω-bases (KM 4.6.2's `{±1}`) -/

/-- **(T-OM-B9)** The inversion `[-1]` as an `Ell/R`-endomorphism over the identity
of the base. -/
noncomputable def negEllHom (X : EllObj R) : X ⟶ X where
  baseHom := 𝟙 X.base
  base_w := Category.id_comp _
  top := X.curve.toEllipticCurveGeom.negHom
  isPullback := X.curve.toEllipticCurveGeom.isPullback_negHom
  zero_w := X.curve.toEllipticCurveGeom.negHom_zero_w

/-- **(T-OM-B9)** Inversion is an `Ell/R`-automorphism (an involution). -/
noncomputable def negEllIso (X : EllObj R) : X ≅ X where
  hom := negEllHom X
  inv := negEllHom X
  hom_inv_id :=
    EllHom.ext (Category.id_comp _) X.curve.toEllipticCurveGeom.negHom_negHom
  inv_hom_id :=
    EllHom.ext (Category.id_comp _) X.curve.toEllipticCurveGeom.negHom_negHom

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B9)** The mixed comparison at the inversion is `−1` times the transition
cocycle: chartwise, `[-1]^* ω = −ω`. -/
private theorem omegaCompat_neg_w (X : EllObj R)
    (i' i : X.curve.toEllipticCurveGeom.atlas.ι) :
    (omegaCompat (negEllHom X)).w i' i =
      Scheme.resUnit (le_inf inf_le_left inf_le_right :
          (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
            ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
              (negEllHom X).baseHom).U i ≤ _)
        ((omegaCocycle X.curve.toEllipticCurveGeom).u i' i) * (-1) := by
  refine Scheme.unit_ext_of_affine_res X.base (fun V hV => ?_)
  rw [show (omegaCompat (negEllHom X)).w i' i =
      (omegaCompatGlue (negEllHom X) i' i).1 from rfl,
    (omegaCompatGlue (negEllHom X) i' i).2 V hV]
  -- split the mixed comparison through the plain restriction
  rw [show ((X.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        (hV.trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).transport
        (negEllHom X).baseHom (negEllHom X).top (negEllHom X).isPullback
        (negEllHom X).zero_w (hV.trans inf_le_right)) =
    ((X.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        (hV.trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).restrict
        (hV.trans inf_le_right)) *
    ((X.curve.toEllipticCurveGeom.atlas.presentation i).restrict
        (hV.trans inf_le_right)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).transport
        (negEllHom X).baseHom (negEllHom X).top (negEllHom X).isPullback
        (negEllHom X).zero_w (hV.trans inf_le_right)) from
    (transUnit_trans _ _ _).symm]
  rw [show ((X.curve.toEllipticCurveGeom.atlas.presentation i).restrict
        (hV.trans inf_le_right)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).transport
        (negEllHom X).baseHom (negEllHom X).top (negEllHom X).isPullback
        (negEllHom X).zero_w (hV.trans inf_le_right)) = -1 from
    transUnit_transport_neg i (negEllHom X).isPullback (negEllHom X).zero_w
      (hV.trans inf_le_right)]
  rw [show ((X.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        (hV.trans inf_le_left)).transUnit
      ((X.curve.toEllipticCurveGeom.atlas.presentation i).restrict
        (hV.trans inf_le_right)) =
    Scheme.resUnit (hV.trans (le_inf inf_le_left inf_le_right))
      ((omegaCocycle X.curve.toEllipticCurveGeom).u i' i) from
    (omegaCocycle_res X.curve.toEllipticCurveGeom i' i V
      (hV.trans (le_inf inf_le_left inf_le_right))).symm]
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Units.ext ?_
    simp only [Scheme.resUnit_val, Scheme.resLE_resLE]
  · refine Units.ext ?_
    simp only [Scheme.resUnit_val, Units.val_neg, Units.val_one, map_neg, map_one]

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B9 ★)** The inversion acts by `−1` on the `S`-bases of `ω_{E/S}` —
KM 4.6.2's `{±1}`-action, `[-1]^* ω = −ω`. -/
theorem omegaBasisMap_negEll (X : EllObj R)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    omegaBasisMap (negEllHom X) b = (-1 : Γ(X.base, ⊤)ˣ) • b := by
  refine Subtype.ext (Subtype.ext (funext fun i' => ?_))
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun j : X.curve.toEllipticCurveGeom.atlas.ι =>
      (⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
        ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (negEllHom X).baseHom).U j)
    ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i')
    (fun j => homOfLE inf_le_left) (by
      intro x hx
      obtain ⟨j, hxj⟩ := X.curve.toEllipticCurveGeom.atlas.covers x
      exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩) _ _ (fun j => ?_)
  show Scheme.resLE inf_le_left
      (((omegaCompat (negEllHom X)).transportFun _).1 i') =
    Scheme.resLE inf_le_left (((-1 : Γ(X.base, ⊤)ˣ) • b).1.1 i')
  rw [(omegaCompat (negEllHom X)).transportFun_res _ i' j]
  rw [omegaCompat_neg_w X i' j]
  rw [show ((-1 : Γ(X.base, ⊤)ˣ) • b).1 = ((-1 : Γ(X.base, ⊤)ˣ)).val • b.1 from rfl]
  -- compatibility of `b` restricted to the piece
  have hb := congrArg (⇑(Scheme.resLE (X := X.base)
    (show (⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
        ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
          (negEllHom X).baseHom).U j ≤
      (⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U i' ⊓
        (omegaCocycle X.curve.toEllipticCurveGeom).U j from le_rfl))) (b.1.2 i' j)
  simp only [Scheme.resUnit_val, Scheme.resLE_resLE, map_mul, Units.val_mul,
    Units.val_neg, Units.val_one, map_neg, map_one, mul_neg, neg_mul, one_mul, mul_one,
    Scheme.UnitCocycle.sections.smul_coe] at hb ⊢
  -- the pulled `j`-component is the restriction of `b j`
  rw [show ((((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle
      (negEllHom X).baseHom).sectionsMap
      (show (⊤ : X.base.Opens) ≤ (negEllHom X).baseHom ⁻¹ᵁ
        (⊤ : X.base.Opens) from fun x _ => trivial)
      ((omegaCocycle X.curve.toEllipticCurveGeom).sectionsPullback
        (negEllHom X).baseHom b.1)).1 j) =
    Scheme.resLE (inf_le_inf_right _ (show (⊤ : X.base.Opens) ≤ ⊤ from le_rfl))
      (sectionsMapLE (𝟙 X.base)
        (show ((⊤ : X.base.Opens) ⊓ (omegaCocycle X.curve.toEllipticCurveGeom).U j :
            X.base.Opens) ≤
          (𝟙 X.base : X.base ⟶ X.base) ⁻¹ᵁ ((⊤ : X.base.Opens) ⊓
            (omegaCocycle X.curve.toEllipticCurveGeom).U j) from fun _ hy => hy)
        (b.1.1 j)) from rfl,
    sectionsMapLE_id]
  rw [neg_inj]
  erw [Scheme.resLE_resLE, Scheme.resLE_resLE]
  exact hb.symm

/-- **(T-OM-B9 ★)** KM 4.6.2's `{±1}` on the ω-problem: the inversion automorphism
acts as the global unit `−1`. -/
theorem omegaProblem_map_negEll (X : EllObj R)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    (omegaProblem R).map (negEllHom X).op b = (-1 : Γ(X.base, ⊤)ˣ) • b :=
  omegaBasisMap_negEll X b

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-ACT)** Unit actions on ω-bases compose multiplicatively. -/
theorem OmegaBasis.mul_smul' {S : Scheme.{u}} {G : EllipticCurveGeom S}
    (g h : Γ(S, ⊤)ˣ) (b : OmegaBasis G) : g • h • b = (g * h) • b := by
  refine Subtype.ext (Subtype.ext (funext fun i => ?_))
  show Scheme.resLE inf_le_left g.val *
      (Scheme.resLE inf_le_left h.val * b.1.1 i) =
    Scheme.resLE inf_le_left (g.val * h.val) * b.1.1 i
  rw [map_mul, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-ACT)** The unit `1` acts trivially on ω-bases. -/
theorem OmegaBasis.one_smul' {S : Scheme.{u}} {G : EllipticCurveGeom S}
    (b : OmegaBasis G) : (1 : Γ(S, ⊤)ˣ) • b = b := by
  refine Subtype.ext (Subtype.ext (funext fun i => ?_))
  show Scheme.resLE inf_le_left (1 : Γ(S, ⊤)ˣ).val * b.1.1 i = b.1.1 i
  rw [Units.val_one, map_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-ACT, the `{±1}` of KM 4.6.2)** The sign automorphism of the ω-problem:
scale every basis by the global unit `−1`. Natural by `omegaBasisMap_smul` (ring maps
send `−1` to `−1`); an involution by `mul_smul'`. -/
noncomputable def omegaProblemNegAut (R : CommRingCat.{u}) :
    Aut (omegaProblem R) where
  hom :=
    { app := fun X => ↾fun b : OmegaBasis X.unop.curve.toEllipticCurveGeom =>
        (-1 : Γ(X.unop.base, ⊤)ˣ) • b
      naturality := fun X Y φ => by
        ext b
        refine Eq.trans ?_ (omegaBasisMap_smul φ.unop (-1) b).symm
        exact congrArg (· • omegaBasisMap φ.unop b) (Units.ext (by
          rw [Units.coe_map, Units.val_neg, Units.val_one]
          show ((φ.unop.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom) (-1) = -1
          rw [map_neg, map_one])).symm }
  inv :=
    { app := fun X => ↾fun b : OmegaBasis X.unop.curve.toEllipticCurveGeom =>
        (-1 : Γ(X.unop.base, ⊤)ˣ) • b
      naturality := fun X Y φ => by
        ext b
        refine Eq.trans ?_ (omegaBasisMap_smul φ.unop (-1) b).symm
        exact congrArg (· • omegaBasisMap φ.unop b) (Units.ext (by
          rw [Units.coe_map, Units.val_neg, Units.val_one]
          show ((φ.unop.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom) (-1) = -1
          rw [map_neg, map_one])).symm }
  hom_inv_id := by
    ext X b
    exact (OmegaBasis.mul_smul' _ _ _).trans
      (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)
  inv_hom_id := by
    ext X b
    exact (OmegaBasis.mul_smul' _ _ _).trans
      (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)

/-- **(T-E14-ACT)** The `{±1}`-action on the ω-problem in the engine's `G →* Aut Q`
interface (`representable_of_rigid_of_torsor`): `ℤˣ = {±1}` acts through the sign
automorphism. -/
noncomputable def omegaProblemSignAction (R : CommRingCat.{u}) :
    ℤˣ →* Aut (omegaProblem R) where
  toFun u := if u = 1 then 1 else omegaProblemNegAut R
  map_one' := if_pos rfl
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · rw [one_mul, if_pos rfl, one_mul]
    · rw [one_mul, if_pos rfl, one_mul]
    · rw [mul_one, if_pos rfl, mul_one]
    · rw [show (-1 : ℤˣ) * (-1) = 1 from by decide, if_pos rfl, if_neg (by decide)]
      refine Iso.ext ?_
      refine Eq.symm ?_
      ext X b
      exact (OmegaBasis.mul_smul' _ _ _).trans
        (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)

end ModularCurves
