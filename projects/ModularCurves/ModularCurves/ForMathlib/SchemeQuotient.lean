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

end OpenImmersion

end SchemeAction

end AlgebraicGeometry
