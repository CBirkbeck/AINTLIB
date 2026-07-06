/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q5 (leaf T-Q5a).
-/
import ModularCurves.ForMathlib.AffineQuotient

/-!
# Group actions on schemes: vocabulary for the quotient construction

A `G`-action on a scheme `X` is recorded as a bare family `σ : G → (X ⟶ X)` with
the covariant composition laws (`SchemeAction`), matching the convention of
`AlgebraicGeometry.specSMul`. This file provides:

* `SchemeAction` — the two-law action structure, with `IsIso (σ.hom g)`;
* `SchemeAction.spec` — the tautological action on `Spec B` by `specSMul`;
* `SchemeAction.IsStableOpen` — `G`-stable opens (`(σ.hom g) ⁻¹ᵁ U = U`);
* `SchemeAction.gammaMulSemiringAction` — the induced ring action on the sections
  `Γ(X, U)` over a stable open, via `Scheme.Hom.appLE` (T-Q5a's Γ-bridge: over a
  stable *affine* open this reconnects to the affine quotient theory of
  `SpecGroupAction.lean`/`AffineQuotient.lean`).

This is the vocabulary layer of the quotient of a scheme by a finite group
([Loeffler, *Modular curves*, Prop 3.6.1]; the gluing itself is tickets T-Q5b–d).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (G : Type*) [Group G]

/-- An action of a group `G` on a scheme `X`, as a family of endomorphisms with the
covariant composition laws (each `hom g` is automatically an isomorphism,
`SchemeAction.isIso_hom`). The composition convention matches `specSMul`:
`hom (g * h) = hom g ≫ hom h`. -/
structure SchemeAction (X : Scheme.{u}) where
  /-- The endomorphism attached to `g`. -/
  hom : G → (X ⟶ X)
  hom_one : hom 1 = 𝟙 X
  hom_mul : ∀ g h : G, hom (g * h) = hom g ≫ hom h

namespace SchemeAction

variable {G}
variable {X : Scheme.{u}} (σ : SchemeAction G X)

instance isIso_hom (g : G) : IsIso (σ.hom g) :=
  ⟨σ.hom g⁻¹, by rw [← σ.hom_mul, mul_inv_cancel, σ.hom_one],
    by rw [← σ.hom_mul, inv_mul_cancel, σ.hom_one]⟩

variable (G) in
/-- The tautological action on `Spec B` induced by a ring action (`specSMul`). -/
noncomputable def spec (B : Type u) [CommRing B] [MulSemiringAction G B] :
    SchemeAction G (Spec (CommRingCat.of B)) where
  hom g := specSMul g
  hom_one := specSMul_one
  hom_mul := specSMul_mul

@[simp]
theorem spec_hom (B : Type u) [CommRing B] [MulSemiringAction G B] (g : G) :
    (spec G B).hom g = specSMul g := rfl

/-- A `G`-stable open of `X`: each `σ g` restricts to it. -/
def IsStableOpen (U : X.Opens) : Prop :=
  ∀ g : G, (σ.hom g) ⁻¹ᵁ U = U

theorem IsStableOpen.le_preimage {σ : SchemeAction G X} {U : X.Opens}
    (hU : σ.IsStableOpen U) (g : G) : U ≤ (σ.hom g) ⁻¹ᵁ U :=
  (hU g).ge

/-- The induced action on the sections over a `G`-stable open, through
`Scheme.Hom.appLE` (no `eqToHom` transport). Over a stable *affine* open this is
the bridge back to the affine quotient theory. Not an instance (it depends on the
stability hypothesis): bring it into scope with `letI`. -/
@[implicit_reducible]
noncomputable def gammaMulSemiringAction {U : X.Opens} (hU : σ.IsStableOpen U) :
    MulSemiringAction G ↑Γ(X, U) where
  smul g s := ((σ.hom g).appLE U U (hU.le_preimage g)).hom s
  one_smul s := by
    show ((σ.hom 1).appLE U U (hU.le_preimage 1)).hom s = s
    simp only [σ.hom_one]
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    have h1 : (homOfLE (show U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U from σ.hom_one ▸
        hU.le_preimage 1)).op = 𝟙 (Opposite.op U) := rfl
    rw [h1]
    erw [X.presheaf.map_id]
    rfl
  mul_smul g h s := by
    show ((σ.hom (g * h)).appLE U U (hU.le_preimage (g * h))).hom s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom
        (((σ.hom h).appLE U U (hU.le_preimage h)).hom s)
    simp only [σ.hom_mul]
    rw [← Scheme.Hom.appLE_comp_appLE (σ.hom g) (σ.hom h) U U U
      (hU.le_preimage h) (hU.le_preimage g)]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

@[simp]
theorem gammaMulSemiringAction_smul_def {U : X.Opens} (hU : σ.IsStableOpen U)
    (g : G) (s : ↑Γ(X, U)) :
    (gammaMulSemiringAction σ hU).smul g s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom s := rfl

/-- **Stable-affine refinement** (T-Q5b): if the `σ`-orbit of a point lies in an
affine open of a scheme with affine diagonal (e.g. any separated scheme), then the
point has a `G`-stable affine open neighbourhood, namely `⨅ g, (σ.hom g) ⁻¹ᵁ U`.
This is where "quasi-projective and `G` finite" enters Loeffler's Prop 3.6.1: quasi-
projectivity guarantees the orbit-in-affine hypothesis, and finiteness keeps the
refinement open and affine. -/
theorem exists_isStableOpen_isAffineOpen [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (horbit : ∀ g : G, σ.hom g x ∈ U) :
    ∃ V : X.Opens, σ.IsStableOpen V ∧ IsAffineOpen V ∧ x ∈ V := by
  refine ⟨⨅ g : G, (σ.hom g) ⁻¹ᵁ U, ?_, ?_, ?_⟩
  · intro g
    have hcoe : ∀ (f : X ⟶ X) (V : X.Opens), (↑(f ⁻¹ᵁ V) : Set X) = ⇑f.base ⁻¹' ↑V :=
      fun f V => rfl
    refine TopologicalSpace.Opens.ext ?_
    rw [hcoe, TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]
    have h1 : ∀ h : G, ⇑(σ.hom g).base ⁻¹' (↑(σ.hom h ⁻¹ᵁ U) : Set X) =
        ↑(σ.hom (g * h) ⁻¹ᵁ U) := by
      intro h
      rw [hcoe, hcoe, ← Set.preimage_comp]
      congr 1
      rw [σ.hom_mul]
      rfl
    rw [Set.iInter_congr h1]
    exact (Equiv.mulLeft g).surjective.iInter_comp
      (fun k => (↑(σ.hom k ⁻¹ᵁ U) : Set X))
  · exact IsAffineOpen.iInf (fun g => hU.preimage_of_isIso (σ.hom g))
  · show x ∈ (↑(⨅ g : G, (σ.hom g) ⁻¹ᵁ U) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun g => horbit g)

/-- The local quotient of a `G`-stable affine open: `Spec (Γ(X, V)ᴳ)` (T-Q5c,
local piece). -/
@[reducible]
noncomputable def localQuotient {V : X.Opens} (hV : σ.IsStableOpen V) : Scheme.{u} :=
  letI := σ.gammaMulSemiringAction hV
  Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, V) G))

/-- The local quotient map `V ⟶ Spec (Γ(X, V)ᴳ)` on a `G`-stable affine open:
the affine identification followed by the invariants morphism of the section-ring
action. -/
noncomputable def localQuotientπ {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) : (V : Scheme.{u}) ⟶ σ.localQuotient hV :=
  letI := σ.gammaMulSemiringAction hV
  hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ

/-- The affine identification intertwines the geometric action restricted to a
stable affine open with the `Spec` of the section-ring action (the c3 bridge:
`resLE`/`isoSpec` naturality). -/
@[reassoc]
theorem resLE_isoSpec_hom {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    (σ.hom g).resLE V V (hV.le_preimage g) ≫ hVa.isoSpec.hom =
      hVa.isoSpec.hom ≫ specSMul g := by
  letI := σ.gammaMulSemiringAction hV
  haveI : IsAffine (V : Scheme.{u}) := hVa
  have hnat := Scheme.isoSpec_hom_naturality ((σ.hom g).resLE V V (hV.le_preimage g))
  -- unfold `IsAffineOpen.isoSpec` as `Scheme.isoSpec ≪≫ Spec.mapIso (topIso.symm.op)`
  show (σ.hom g).resLE V V (hV.le_preimage g) ≫
      ((V : Scheme.{u}).isoSpec ≪≫ Scheme.Spec.mapIso V.topIso.symm.op).hom = _
  rw [Iso.trans_hom, ← Category.assoc, ← hnat, Category.assoc]
  show _ = ((V : Scheme.{u}).isoSpec ≪≫ Scheme.Spec.mapIso V.topIso.symm.op).hom ≫ _
  rw [Iso.trans_hom, Category.assoc]
  congr 1
  -- now a pure `Spec.map` computation
  show Spec.map ((σ.hom g).resLE V V (hV.le_preimage g)).appTop ≫
      Spec.map V.topIso.inv =
    Spec.map V.topIso.inv ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G ↑Γ(X, V) g))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  have hsq : V.topIso.hom ≫ (σ.hom g).appLE V V (hV.le_preimage g) =
      ((σ.hom g).resLE V V (hV.le_preimage g)).appTop ≫ V.topIso.hom :=
    (arrowResLEAppIso (σ.hom g) V V (hV.le_preimage g)).hom.w
  have hof : CommRingCat.ofHom (MulSemiringAction.toRingHom G ↑Γ(X, V) g) =
      (σ.hom g).appLE V V (hV.le_preimage g) := rfl
  rw [hof, Iso.inv_comp_eq, ← Category.assoc, hsq, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem localQuotientπ_def {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) :
    letI := σ.gammaMulSemiringAction hV
    σ.localQuotientπ hV hVa = hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ := rfl

/-- The local quotient map coequalizes the restricted action (T-Q5c, local
invariance). -/
@[reassoc]
theorem resLE_localQuotientπ {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    (σ.hom g).resLE V V (hV.le_preimage g) ≫ σ.localQuotientπ hV hVa =
      σ.localQuotientπ hV hVa := by
  letI := σ.gammaMulSemiringAction hV
  have h1 := resLE_isoSpec_hom σ hV hVa g
  show (σ.hom g).resLE V V (hV.le_preimage g) ≫ hVa.isoSpec.hom ≫
      invariantsπ G ↑Γ(X, V) ℤ = hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ
  rw [← Category.assoc, h1, Category.assoc, specSMul_invariantsπ]

/-- Inverse form of the intertwiner bridge. -/
@[reassoc]
theorem specSMul_isoSpec_inv {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    specSMul g ≫ hVa.isoSpec.inv =
      hVa.isoSpec.inv ≫ (σ.hom g).resLE V V (hV.le_preimage g) := by
  letI := σ.gammaMulSemiringAction hV
  rw [Iso.eq_inv_comp, ← Category.assoc, ← resLE_isoSpec_hom σ hV hVa g,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The restricted action commutes with the inclusion of a smaller stable open. -/
@[reassoc]
theorem resLE_homOfLE {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hV : σ.IsStableOpen V) (hWV : W ≤ V) (g : G) :
    (σ.hom g).resLE W W (hW.le_preimage g) ≫ X.homOfLE hWV =
      X.homOfLE hWV ≫ (σ.hom g).resLE V V (hV.le_preimage g) := by
  rw [Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]

variable [Finite G]

omit [Finite G] in
private theorem localQuotientMap_invariance {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    letI := σ.gammaMulSemiringAction hW
    ∀ g : G, specSMul g ≫
        (hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) =
      hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa := by
  letI := σ.gammaMulSemiringAction hW
  intro g
  rw [specSMul_isoSpec_inv_assoc σ hW hWa g, resLE_homOfLE_assoc σ hW hV hWV g,
    resLE_localQuotientπ σ hV hVa g]

/-- The descended map between the local quotients of nested stable affine opens:
the (unique) morphism under `invariantsπ` induced by the inclusion `W ≤ V`. -/
noncomputable def localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) : σ.localQuotient hW ⟶ σ.localQuotient hV :=
  letI := σ.gammaMulSemiringAction hW
  (exists_invariantsπ_lift G ↑Γ(X, W) ℤ
    (hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa)
    (σ.localQuotientMap_invariance hW hWa hV hVa hWV)).choose

/-- Defining property of `localQuotientMap`. -/
theorem invariantsπ_localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    letI := σ.gammaMulSemiringAction hW
    invariantsπ G ↑Γ(X, W) ℤ ≫ σ.localQuotientMap hW hWa hV hVa hWV =
      hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa :=
  letI := σ.gammaMulSemiringAction hW
  (exists_invariantsπ_lift G ↑Γ(X, W) ℤ
    (hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa)
    (σ.localQuotientMap_invariance hW hWa hV hVa hWV)).choose_spec

/-- The local quotient maps are compatible with the local quotient projections. -/
@[reassoc]
theorem localQuotientπ_localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV =
      X.homOfLE hWV ≫ σ.localQuotientπ hV hVa := by
  letI := σ.gammaMulSemiringAction hW
  have h1 := σ.invariantsπ_localQuotientMap hW hWa hV hVa hWV
  show (hWa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, W) ℤ) ≫
      σ.localQuotientMap hW hWa hV hVa hWV = _
  rw [Category.assoc, h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section OpenImmersion

variable {W V : X.Opens}

/-- The "window" of a smaller open inside the affine identification of a stable
affine open: `W ⟶ Spec Γ(X, V)`. -/
private noncomputable def windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V) :
    (W : Scheme.{u}) ⟶ Spec Γ(X, V) :=
  X.homOfLE hWV ≫ hVa.isoSpec.hom

private instance (hWV : W ≤ V) (hVa : IsAffineOpen V) :
    IsOpenImmersion (windowHom (X := X) hWV hVa) := by
  rw [windowHom]
  infer_instance

omit [Finite G] in
/-- The window intertwines the restricted geometric action with `specSMul` of the
section-ring action. -/
private theorem resLE_windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    (σ.hom g).resLE W W (hW.le_preimage g) ≫ windowHom hWV hVa =
      windowHom hWV hVa ≫ specSMul g := by
  letI := σ.gammaMulSemiringAction hV
  show (σ.hom g).resLE W W (hW.le_preimage g) ≫ X.homOfLE hWV ≫ hVa.isoSpec.hom =
    (X.homOfLE hWV ≫ hVa.isoSpec.hom) ≫ specSMul g
  rw [← Category.assoc, resLE_homOfLE σ hW hV hWV g, Category.assoc,
    resLE_isoSpec_hom σ hV hVa g, Category.assoc]

omit [Finite G] in
/-- Stability of the window range under the section-ring action. -/
private theorem specSMul_mem_range_windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (g : G)
    (x : Spec Γ(X, V))
    (hx : x ∈ Set.range ⇑(windowHom (X := X) hWV hVa)) :
    letI := σ.gammaMulSemiringAction hV
    specSMul g x ∈ Set.range ⇑(windowHom (X := X) hWV hVa) := by
  letI := σ.gammaMulSemiringAction hV
  obtain ⟨w, rfl⟩ := hx
  refine ⟨(σ.hom g).resLE W W (hW.le_preimage g) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, resLE_windowHom σ hWV hVa hW hV g,
    Scheme.Hom.comp_apply]

/-- The open of the local quotient carved out by a smaller stable open. -/
private noncomputable def imageOpens (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    (σ.localQuotient hV).Opens :=
  letI := σ.gammaMulSemiringAction hV
  ⟨⇑(invariantsπ G ↑Γ(X, V) ℤ).base '' Set.range ⇑(windowHom (X := X) hWV hVa),
    isOpen_image_invariantsπ_of_stable G ↑Γ(X, V) ℤ
      (windowHom (X := X) hWV hVa).isOpenEmbedding.isOpen_range
      (fun g x hx => specSMul_mem_range_windowHom σ hWV hVa hW hV g x hx)⟩

/-- Saturation: the pullback of the image open is exactly the window. -/
private theorem range_fst_imageOpens (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    Set.range ⇑(pullback.fst (invariantsπ G ↑Γ(X, V) ℤ)
        (imageOpens σ hWV hVa hW hV).ι) =
      Set.range ⇑(windowHom (X := X) hWV hVa) := by
  letI := σ.gammaMulSemiringAction hV
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G ↑Γ(X, V) ℤ t x).mp htx
    rw [← hg]
    exact specSMul_mem_range_windowHom σ hWV hVa hW hV g t ht
  · intro hx
    show invariantsπ G ↑Γ(X, V) ℤ x ∈
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV))
    exact ⟨x, hx, rfl⟩

/-- The window is the pullback of the image open: the canonical isomorphism. -/
private noncomputable def windowIso (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    (W : Scheme.{u}) ≅
      pullback (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι :=
  letI := σ.gammaMulSemiringAction hV
  IsOpenImmersion.isoOfRangeEq (windowHom (X := X) hWV hVa) (pullback.fst _ _)
    (range_fst_imageOpens σ hWV hVa hW hV).symm

private theorem windowIso_hom_fst (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    (windowIso σ hWV hVa hW hV).hom ≫
        pullback.fst (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι =
      windowHom (X := X) hWV hVa :=
  letI := σ.gammaMulSemiringAction hV
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem windowIso_inv_window (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    (windowIso σ hWV hVa hW hV).inv ≫ windowHom (X := X) hWV hVa =
      pullback.fst (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι :=
  letI := σ.gammaMulSemiringAction hV
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The relative action on the pullback of the image open is conjugate to the
restricted geometric action under the window isomorphism. -/
private theorem pullbackSpecSMul_windowIso_inv (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    pullbackSpecSMul G ↑Γ(X, V) ℤ (imageOpens σ hWV hVa hW hV).ι g ≫
        (windowIso σ hWV hVa hW hV).inv =
      (windowIso σ hWV hVa hW hV).inv ≫
        (σ.hom g).resLE W W (hW.le_preimage g) := by
  letI := σ.gammaMulSemiringAction hV
  rw [← cancel_mono (windowHom (X := X) hWV hVa), Category.assoc, Category.assoc,
    resLE_windowHom σ hWV hVa hW hV g, windowIso_inv_window σ hWV hVa hW hV,
    pullbackSpecSMul_fst, ← Category.assoc, windowIso_inv_window σ hWV hVa hW hV]

/-- The local quotient projection is surjective on points. -/
private theorem localQuotientπ_surjective {V' : X.Opens} (hV' : σ.IsStableOpen V')
    (hV'a : IsAffineOpen V') :
    Function.Surjective ⇑(σ.localQuotientπ hV' hV'a) := by
  letI := σ.gammaMulSemiringAction hV'
  intro q₀
  obtain ⟨y, hy⟩ := invariantsπ_surjective G ↑Γ(X, V') ℤ q₀
  refine ⟨hV'a.isoSpec.inv y, ?_⟩
  show (σ.localQuotientπ hV' hV'a) (hV'a.isoSpec.inv y) = q₀
  rw [localQuotientπ_def, Scheme.Hom.comp_apply]
  have h60 : hV'a.isoSpec.hom (hV'a.isoSpec.inv y) = y := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [h60]
  exact hy

/-- **The local quotient maps are open immersions** (T-Q5 (α)): the descended map
between the local quotients of nested stable affine opens is an isomorphism onto
the saturated image open. -/
instance isOpenImmersion_localQuotientMap (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    IsOpenImmersion (σ.localQuotientMap hW hWa hV hVa hWV) := by
  letI := σ.gammaMulSemiringAction hV
  letI := σ.gammaMulSemiringAction hW
  -- the inverse-up-to-inclusion, from the keystone
  obtain ⟨q, hq⟩ := exists_invariantsπ_lift_of_isOpenImmersion G ↑Γ(X, V) ℤ
    (imageOpens σ hWV hVa hW hV).ι
    ((windowIso σ hWV hVa hW hV).inv ≫ σ.localQuotientπ hW hWa)
    (fun g => by
      rw [← Category.assoc, pullbackSpecSMul_windowIso_inv σ hWV hVa hW hV g,
        Category.assoc, resLE_localQuotientπ σ hW hWa g])
  -- the corestriction through the image open
  have hrangeMap : Set.range ⇑(σ.localQuotientMap hW hWa hV hVa hWV) ⊆
      Set.range ⇑(imageOpens σ hWV hVa hW hV).ι := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := localQuotientπ_surjective σ hW hWa t
    rw [Scheme.Opens.range_ι]
    show (σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV) w ∈
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV))
    rw [localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV]
    refine ⟨windowHom (X := X) hWV hVa w, ⟨w, rfl⟩, ?_⟩
    show invariantsπ G ↑Γ(X, V) ℤ (windowHom (X := X) hWV hVa w) =
      (X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) w
    rw [Scheme.Hom.comp_apply, localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ ≫ (imageOpens σ hWV hVa hW hV).ι =
      σ.localQuotientMap hW hWa hV hVa hWV :=
    ⟨IsOpenImmersion.lift _ _ hrangeMap, IsOpenImmersion.lift_fac _ _ hrangeMap⟩
  -- `π^W ≫ m₀` is the window followed by `snd`
  have hπm₀ : σ.localQuotientπ hW hWa ≫ m₀ =
      (windowIso σ hWV hVa hW hV).hom ≫
        pullback.snd (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι := by
    rw [← cancel_mono (imageOpens σ hWV hVa hW hV).ι, Category.assoc, hm₀,
      localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV, Category.assoc,
      ← pullback.condition, ← Category.assoc, windowIso_hom_fst σ hWV hVa hW hV]
    show X.homOfLE hWV ≫ σ.localQuotientπ hV hVa =
      (X.homOfLE hWV ≫ hVa.isoSpec.hom) ≫ invariantsπ G ↑Γ(X, V) ℤ
    rw [localQuotientπ_def, Category.assoc]
  -- the projection expressed through the local quotient map
  have hπ' : invariantsπ G ↑Γ(X, W) ℤ = hWa.isoSpec.inv ≫ σ.localQuotientπ hW hWa := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- two-sided inverse
  have hmq : m₀ ≫ q = 𝟙 _ := by
    refine invariantsπ_hom_ext G ↑Γ(X, W) ℤ _ _ ?_
    rw [Category.comp_id, hπ', Category.assoc]
    congr 1
    rw [← Category.assoc, hπm₀, Category.assoc, hq, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  have hqm : q ≫ m₀ = 𝟙 _ := by
    refine invariantsπ_hom_ext_of_isOpenImmersion G ↑Γ(X, V) ℤ
      (imageOpens σ hWV hVa hW hV).ι _ _ ?_
    rw [Category.comp_id, ← Category.assoc, hq, Category.assoc, hπm₀,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  haveI : IsIso m₀ := ⟨q, hmq, hqm⟩
  rw [← hm₀]
  infer_instance

omit [Finite G] in
/-- Intersections of stable opens are stable. -/
theorem IsStableOpen.inf {τ : SchemeAction G X} {U V : X.Opens}
    (hU : τ.IsStableOpen U) (hV : τ.IsStableOpen V) :
    τ.IsStableOpen (U ⊓ V) := by
  intro g
  rw [Scheme.Hom.preimage_inf, hU g, hV g]

/-- The local quotient map at equal opens is the identity. -/
theorem localQuotientMap_self {W : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) :
    σ.localQuotientMap hW hWa hW hWa le_rfl = 𝟙 _ := by
  letI := σ.gammaMulSemiringAction hW
  refine invariantsπ_hom_ext G ↑Γ(X, W) ℤ _ _ ?_
  have h1 : invariantsπ G ↑Γ(X, W) ℤ =
      hWa.isoSpec.inv ≫ σ.localQuotientπ hW hWa := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Category.comp_id, h1, Category.assoc]
  congr 1
  rw [localQuotientπ_localQuotientMap σ hW hWa hW hWa le_rfl, Scheme.homOfLE_rfl,
    Category.id_comp]

/-- The local quotient maps compose along inclusions. -/
@[reassoc]
theorem localQuotientMap_trans {W V U : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hU : σ.IsStableOpen U) (hUa : IsAffineOpen U) (hWV : W ≤ V) (hVU : V ≤ U) :
    σ.localQuotientMap hW hWa hV hVa hWV ≫ σ.localQuotientMap hV hVa hU hUa hVU =
      σ.localQuotientMap hW hWa hU hUa (hWV.trans hVU) := by
  letI := σ.gammaMulSemiringAction hW
  refine invariantsπ_hom_ext G ↑Γ(X, W) ℤ _ _ ?_
  have h1 : invariantsπ G ↑Γ(X, W) ℤ =
      hWa.isoSpec.inv ≫ σ.localQuotientπ hW hWa := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [h1, Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV,
    Category.assoc, localQuotientπ_localQuotientMap σ hV hVa hU hUa hVU,
    localQuotientπ_localQuotientMap σ hW hWa hU hUa (hWV.trans hVU),
    ← Category.assoc, ← Scheme.homOfLE_homOfLE (X := X) hWV hVU]

/-- The range of the local quotient map is exactly the saturated image open
(β2a). -/
private theorem range_localQuotientMap (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) :
    Set.range ⇑(σ.localQuotientMap hW hWa hV hVa hWV) =
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV)) := by
  letI := σ.gammaMulSemiringAction hV
  letI := σ.gammaMulSemiringAction hW
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := localQuotientπ_surjective σ hW hWa t
    show (σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV) w ∈
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV))
    rw [localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV]
    refine ⟨windowHom (X := X) hWV hVa w, ⟨w, rfl⟩, ?_⟩
    show invariantsπ G ↑Γ(X, V) ℤ (windowHom (X := X) hWV hVa w) =
      (X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) w
    rw [Scheme.Hom.comp_apply, localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl
  · rintro t ⟨s, ⟨w, rfl⟩, rfl⟩
    -- π(window w) = map (π^W w)
    refine ⟨σ.localQuotientπ hW hWa w, ?_⟩
    rw [← Scheme.Hom.comp_apply, localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV]
    show (X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) w =
      invariantsπ G ↑Γ(X, V) ℤ (windowHom (X := X) hWV hVa w)
    rw [Scheme.Hom.comp_apply, localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl

omit [Finite G] in
private theorem range_windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V) :
    Set.range ⇑(windowHom (X := X) hWV hVa) =
      ⇑hVa.isoSpec.hom '' ↑(V.ι ⁻¹ᵁ W) := by
  show Set.range (⇑hVa.isoSpec.hom ∘ ⇑(X.homOfLE hWV)) = _
  rw [Set.range_comp]
  congr 1
  have h70 := Scheme.opensRange_homOfLE (X := X) hWV
  exact congrArg (fun t : (V : Scheme.{u}).Opens => (t : Set (V : Scheme.{u}))) h70

omit [Finite G] in
/-- Windows intersect as expected (β2b, window level). -/
private theorem range_windowHom_inter {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) :
    Set.range ⇑(windowHom (X := X) hW₁V hVa) ∩
        Set.range ⇑(windowHom (X := X) hW₂V hVa) =
      Set.range ⇑(windowHom (X := X) (W := W₁ ⊓ W₂) (inf_le_left.trans hW₁V) hVa) := by
  rw [range_windowHom (X := X) hW₁V hVa, range_windowHom (X := X) hW₂V hVa,
    range_windowHom (X := X) (W := W₁ ⊓ W₂) (inf_le_left.trans hW₁V) hVa,
    ← Set.image_inter (hVa.isoSpec.hom.isOpenEmbedding.injective)]
  congr 1

/-- Saturated image opens intersect as expected (β2b). -/
private theorem imageOpens_inf {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₂ : σ.IsStableOpen W₂)
    (hV : σ.IsStableOpen V) :
    imageOpens σ hW₁V hVa hW₁ hV ⊓ imageOpens σ hW₂V hVa hW₂ hV =
      imageOpens σ (inf_le_left.trans hW₁V) hVa (hW₁.inf hW₂) hV := by
  letI := σ.gammaMulSemiringAction hV
  refine TopologicalSpace.Opens.ext ?_
  show (imageOpens σ hW₁V hVa hW₁ hV : Set (σ.localQuotient hV)) ∩
      (imageOpens σ hW₂V hVa hW₂ hV : Set (σ.localQuotient hV)) = _
  apply Set.Subset.antisymm
  · rintro p ⟨⟨a, haA, ha⟩, ⟨b, hbB, hb⟩⟩
    -- both fibre points are in the same orbit; stability puts one in both windows
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G ↑Γ(X, V) ℤ a b).mp (by rw [ha, hb])
    have hbA : b ∈ Set.range ⇑(windowHom (X := X) hW₁V hVa) := by
      rw [← hg]
      exact specSMul_mem_range_windowHom σ hW₁V hVa hW₁ hV g a haA
    refine ⟨b, ?_, hb⟩
    rw [← range_windowHom_inter (X := X) hW₁V hW₂V hVa]
    exact ⟨hbA, hbB⟩
  · rintro p ⟨a, haA, ha⟩
    have h71 : a ∈ Set.range ⇑(windowHom (X := X) hW₁V hVa) ∩
        Set.range ⇑(windowHom (X := X) hW₂V hVa) := by
      rw [range_windowHom_inter (X := X) hW₁V hW₂V hVa]
      exact haA
    exact ⟨⟨a, h71.1, ha⟩, ⟨a, h71.2, ha⟩⟩

/-- The two saturated image opens of an intersection agree at the level of sets
(coe of `imageOpens_inf`). -/
private theorem range_inter_localQuotientMap {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁)
    (hW₁a : IsAffineOpen W₁) (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂)
    (hV : σ.IsStableOpen V) (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    Set.range ⇑(σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hV hVa
        (inf_le_left.trans hW₁V)) =
      Set.range ⇑(σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V) ∩
        Set.range ⇑(σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) := by
  rw [range_localQuotientMap σ (inf_le_left.trans hW₁V) hVa (hW₁.inf hW₂) hW₁₂a hV,
    range_localQuotientMap σ hW₁V hVa hW₁ hW₁a hV,
    range_localQuotientMap σ hW₂V hVa hW₂ hW₂a hV]
  have h80 := imageOpens_inf σ hW₁V hW₂V hVa hW₁ hW₂ hV
  have h81 := congrArg
    (fun t : (σ.localQuotient hV).Opens => (t : Set (σ.localQuotient hV))) h80
  exact h81.symm

/-- **The triple-overlap comparison** (β2c): the pullback of two local quotient
immersions is the local quotient of the intersection. -/
private noncomputable def tripleIso {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    σ.localQuotient (hW₁.inf hW₂) ≅
      pullback (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
        (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) :=
  IsOpenImmersion.isoOfRangeEq
    (σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hV hVa (inf_le_left.trans hW₁V))
    (pullback.fst _ _ ≫ σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
    (by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact range_inter_localQuotientMap σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a)

private theorem tripleIso_hom_comp {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).hom ≫
        pullback.fst _ _ ≫ σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V =
      σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hV hVa (inf_le_left.trans hW₁V) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The first-projection compatibility of the triple comparison. -/
private theorem tripleIso_hom_fst {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).hom ≫ pullback.fst _ _ =
      σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₁ hW₁a inf_le_left := by
  rw [← cancel_mono (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V), Category.assoc,
    tripleIso_hom_comp σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a,
    localQuotientMap_trans σ (hW₁.inf hW₂) hW₁₂a hW₁ hW₁a hV hVa inf_le_left hW₁V]

/-- The second-projection compatibility of the triple comparison. -/
private theorem tripleIso_hom_snd {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).hom ≫ pullback.snd _ _ =
      σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₂ hW₂a inf_le_right := by
  rw [← cancel_mono (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V), Category.assoc,
    ← pullback.condition, ← Category.assoc, Category.assoc,
    tripleIso_hom_comp σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a,
    localQuotientMap_trans σ (hW₁.inf hW₂) hW₁₂a hW₂ hW₂a hV hVa inf_le_right hW₂V]

/-- Local quotient maps along equal opens are isomorphisms. -/
theorem isIso_localQuotientMap_of_le_le {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) (hVW : V ≤ W) :
    IsIso (σ.localQuotientMap hW hWa hV hVa hWV) := by
  refine ⟨σ.localQuotientMap hV hVa hW hWa hVW, ?_, ?_⟩
  · rw [localQuotientMap_trans σ hW hWa hV hVa hW hWa hWV hVW]
    exact σ.localQuotientMap_self hW hWa
  · rw [localQuotientMap_trans σ hV hVa hW hWa hV hVa hVW hWV]
    exact σ.localQuotientMap_self hV hVa

/-- The first projection of the local-quotient pullback, through the triple
comparison. -/
private theorem fst_eq_tripleIso_inv {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁)
    (hW₁a : IsAffineOpen W₁) (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂)
    (hV : σ.IsStableOpen V) (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    pullback.fst (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
        (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) =
      (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).inv ≫
        σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₁ hW₁a inf_le_left := by
  rw [Iso.eq_inv_comp]
  exact tripleIso_hom_fst σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a

/-- The second projection of the local-quotient pullback, through the triple
comparison. -/
private theorem snd_eq_tripleIso_inv {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁)
    (hW₁a : IsAffineOpen W₁) (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂)
    (hV : σ.IsStableOpen V) (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    pullback.snd (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
        (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) =
      (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).inv ≫
        σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₂ hW₂a inf_le_right := by
  rw [Iso.eq_inv_comp]
  exact tripleIso_hom_snd σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a

omit [Finite G] in
private theorem triple_le {A B C : X.Opens} :
    (A ⊓ B) ⊓ (A ⊓ C) ≤ (B ⊓ C) ⊓ (B ⊓ A) :=
  le_inf (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))

section Glue

variable [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
variable (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x))

/-- The pairwise piece of the quotient glue data. -/
@[reducible]
private noncomputable def glueF (i j : X) :
    σ.localQuotient ((hVs i).inf (hVs j)) ⟶ σ.localQuotient (hVs i) :=
  σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j)) (hVs i) (hVa i)
    inf_le_left

/-- The transition map of the quotient glue data. -/
@[reducible]
private noncomputable def glueT (i j : X) :
    σ.localQuotient ((hVs i).inf (hVs j)) ⟶
      σ.localQuotient ((hVs j).inf (hVs i)) :=
  σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
    ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (le_inf inf_le_right inf_le_left)

/-- The triple transition of the quotient glue data. -/
@[reducible]
private noncomputable def glueT' (i j k : X) :
    pullback (glueF σ V hVs hVa i j) (glueF σ V hVs hVa i k) ⟶
      pullback (glueF σ V hVs hVa j k) (glueF σ V hVs hVa j i) :=
  (σ.tripleIso inf_le_left inf_le_left (hVa i) ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) ((hVs i).inf (hVs k)) ((hVa i).inf (hVa k)) (hVs i)
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))).inv ≫
    σ.localQuotientMap (((hVs i).inf (hVs j)).inf ((hVs i).inf (hVs k)))
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))
      (((hVs j).inf (hVs k)).inf ((hVs j).inf (hVs i)))
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))) triple_le ≫
    (σ.tripleIso inf_le_left inf_le_left (hVa j) ((hVs j).inf (hVs k))
      ((hVa j).inf (hVa k)) ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j)
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i)))).hom

private theorem glueT'_fac (i j k : X) :
    glueT' σ V hVs hVa i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ glueT σ V hVs hVa i j := by
  rw [glueT', Category.assoc, Category.assoc,
    snd_eq_tripleIso_inv σ inf_le_left inf_le_left (hVa j) ((hVs j).inf (hVs k))
      ((hVa j).inf (hVa k)) ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j)
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))),
    Iso.hom_inv_id_assoc,
    localQuotientMap_trans σ _ (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))) _ ((hVa j).inf (hVa i))
      triple_le inf_le_right,
    fst_eq_tripleIso_inv σ inf_le_left inf_le_left (hVa i) ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) ((hVs i).inf (hVs k)) ((hVa i).inf (hVa k)) (hVs i)
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))),
    Category.assoc, glueT,
    localQuotientMap_trans σ _ (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      ((hVa i).inf (hVa j)) _ ((hVa j).inf (hVa i)) inf_le_left
      (le_inf inf_le_right inf_le_left)]

private theorem glueT'_cocycle (i j k : X) :
    glueT' σ V hVs hVa i j k ≫ glueT' σ V hVs hVa j k i ≫
      glueT' σ V hVs hVa k i j = 𝟙 _ := by
  show ((σ.tripleIso _ _ _ _ _ _ _ _ _).inv ≫ _ ≫ (σ.tripleIso _ _ _ _ _ _ _ _ _).hom) ≫
    ((σ.tripleIso _ _ _ _ _ _ _ _ _).inv ≫ _ ≫ (σ.tripleIso _ _ _ _ _ _ _ _ _).hom) ≫
    ((σ.tripleIso _ _ _ _ _ _ _ _ _).inv ≫ _ ≫ (σ.tripleIso _ _ _ _ _ _ _ _ _).hom) = 𝟙 _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [localQuotientMap_trans_assoc σ _
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))) _
      (((hVa k).inf (hVa i)).inf ((hVa k).inf (hVa j))) triple_le triple_le,
    localQuotientMap_trans_assoc σ _
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      (((hVa k).inf (hVa i)).inf ((hVa k).inf (hVa j))) _
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))
      (triple_le.trans triple_le) triple_le,
    show σ.localQuotientMap _ (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
        (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))
        ((triple_le.trans triple_le).trans triple_le) = 𝟙 _ from
      σ.localQuotientMap_self _ _,
    Category.id_comp, Iso.inv_hom_id]

/-- **The quotient glue data** (T-Q5 c4): the local quotients of a stable affine
atlas, glued along the saturated overlaps. -/
@[reducible]
private noncomputable def quotientGlueData : Scheme.GlueData where
  J := X
  U := fun i => σ.localQuotient (hVs i)
  V := fun p => σ.localQuotient ((hVs p.1).inf (hVs p.2))
  f := fun i j => glueF σ V hVs hVa i j
  f_id := fun i =>
    σ.isIso_localQuotientMap_of_le_le ((hVs i).inf (hVs i))
      ((hVa i).inf (hVa i)) (hVs i) (hVa i) inf_le_left (le_inf le_rfl le_rfl)
  t := fun i j => glueT σ V hVs hVa i j
  t_id := fun i => σ.localQuotientMap_self ((hVs i).inf (hVs i)) ((hVa i).inf (hVa i))
  t' := fun i j k => glueT' σ V hVs hVa i j k
  t_fac := fun i j k => glueT'_fac σ V hVs hVa i j k
  cocycle := fun i j k => glueT'_cocycle σ V hVs hVa i j k
  f_open := fun i j => inferInstance

/-- **The quotient of a scheme by a finite group action** (T-Q5d): the local
quotients of a stable affine atlas, glued. -/
noncomputable def quotient : Scheme.{u} := (quotientGlueData σ V hVs hVa).glued

/-- The chart composites into the quotient agree on overlaps. -/
private theorem chartCompat (i j : X) :
    X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ σ.localQuotientπ (hVs i) (hVa i) ≫
      (quotientGlueData σ V hVs hVa).ι i =
    X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ σ.localQuotientπ (hVs j) (hVa j) ≫
      (quotientGlueData σ V hVs hVa).ι j := by
  rw [← Category.assoc, ← localQuotientπ_localQuotientMap σ ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) (hVs i) (hVa i) inf_le_left,
    ← Category.assoc, ← localQuotientπ_localQuotientMap σ ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) (hVs j) (hVa j) inf_le_right,
    Category.assoc, Category.assoc]
  congr 1
  have h90 := (quotientGlueData σ V hVs hVa).glue_condition i j
  show σ.localQuotientMap _ _ _ _ _ ≫ (quotientGlueData σ V hVs hVa).ι i =
    σ.localQuotientMap _ _ _ _ _ ≫ (quotientGlueData σ V hVs hVa).ι j
  rw [← h90, ← Category.assoc]
  congr 1
  exact localQuotientMap_trans σ ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
    ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j) (hVa j)
    (le_inf inf_le_right inf_le_left) inf_le_left

variable (hVmem : ∀ x : X, x ∈ V x)

/-- The quotient projection `X ⟶ X/G`, glued from the local quotient
projections. -/
noncomputable def quotientπ : X ⟶ σ.quotient V hVs hVa := by
  refine ((Scheme.Cover.mkOfCovers (J := ↥X)
      (fun x => (V x : Scheme.{u}))
      (fun x => (V x).ι)
      (fun x => by
        have h : x ∈ Set.range ⇑(V x).ι := by
          rw [Scheme.Opens.range_ι]
          exact hVmem x
        obtain ⟨v, hv⟩ := h
        exact ⟨x, v, hv⟩)
      (fun x => inferInstance) : X.OpenCover)).glueMorphisms
    (fun x => σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x)
    ?_
  intro x y
  show pullback.fst ((V x).ι) ((V y).ι) ≫
      (σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x) =
    pullback.snd ((V x).ι) ((V y).ι) ≫
      (σ.localQuotientπ (hVs y) (hVa y) ≫ (quotientGlueData σ V hVs hVa).ι y)
  have htop : (V y).ι ⁻¹ᵁ (V y) = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun v => ?_)
    show (V y).ι v ∈ (V y : Set X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨v, rfl⟩
  have H := IsOpenImmersion.isPullback (X.homOfLE (inf_le_left : V x ⊓ V y ≤ V x))
    (X.homOfLE (inf_le_right : V x ⊓ V y ≤ V y)) (V x).ι (V y).ι
    (by simp)
    (by rw [Scheme.Opens.opensRange_ι, Scheme.opensRange_homOfLE,
      Scheme.Hom.preimage_inf, htop, inf_top_eq])
  rw [← cancel_epi H.isoPullback.hom, H.isoPullback_hom_fst_assoc,
    H.isoPullback_hom_snd_assoc]
  exact chartCompat σ V hVs hVa x y

end Glue

end OpenImmersion

end SchemeAction

end AlgebraicGeometry
