/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DivisorClass
import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.Picard.SurjectiveInvertible

/-!
# Pullback compatibility of ideal modules (naturality layer for (2.16))

The enabling leaf for the naturality of `sectionToPicRel` in the base `T` (making the
GME (2.16) assembly a morphism into `picRelFunctor`): the module pullback of an ideal
module along a base-change projection is the ideal module of the comap ideal. The
divisor-level statement is the engine's `RelEffCartierDiv.baseChange_ideal`
(`(D.baseChange t).ideal = D.ideal.comap (pullback.fst π t)`); this file records the
module-level comparison. Locally principal case only — the comparison multiplies the
local generator through, mirroring `bijective_idealGenHom_app`.

Statement-only skeleton (next-session execution per board v10.166).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

section RingCore

open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[NAT-3-CORE, ring level]** The kernel of the base-change map into the tensor
quotient is the extended ideal: `ker (B → B ⊗[A] (A ⧸ I)) = I·B`. -/
theorem ker_algebraMap_tensorQuot {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) :
    RingHom.ker (algebraMap B (B ⊗[A] (A ⧸ I))) = I.map (algebraMap A B) := by
  ext b
  rw [RingHom.mem_ker]
  constructor
  · intro hb
    have hcomm := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).commutes b
    have h0 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I)
        (algebraMap B (B ⧸ I.map (algebraMap A B)) b) = 0 := by
      rw [hcomm, hb]
    have h1 : algebraMap B (B ⧸ I.map (algebraMap A B)) b = 0 := by
      have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm h0
      rwa [AlgEquiv.symm_apply_apply, map_zero] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h1
  · intro hb
    have h1 : algebraMap B (B ⧸ I.map (algebraMap A B)) b = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hb
    have hcomm := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).commutes b
    rw [← hcomm, h1, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[NAT-3-CORE, principal case]** `ker (B → B ⊗[A] (A ⧸ (a))) = (φ a)`. -/
theorem ker_algebraMap_tensorQuot_span {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (a : A) :
    RingHom.ker (algebraMap B (B ⊗[A] (A ⧸ Ideal.span {a}))) =
      Ideal.span {algebraMap A B a} := by
  rw [ker_algebraMap_tensorQuot, Ideal.map_span, Set.image_singleton]

end RingCore

variable {X' X : Scheme.{u}} (f : X' ⟶ X) (J : X.IdealSheafData)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A section of the ideal pulls back to a section of the comap ideal:
`fst♯ (f♯ g) = snd♯ (ι♯ g) = 0` by the pullback square defining the comap. -/
theorem app_mem_idealSections_comap (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    {g : Γ(X, U.unop)} (hg : g ∈ idealSections J U) :
    f.app U.unop g ∈ idealSections (J.comap f)
      (Opposite.op ((TopologicalSpace.Opens.map f.base).obj U.unop)) := by
  refine RingHom.mem_ker.mpr ?_
  have hι : (J.comap f).subschemeι =
      (J.comapIso f).hom ≫ Limits.pullback.fst f J.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_inv_subschemeι J f, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  have hstep1 : ((Limits.pullback.fst f J.subschemeι ≫ f).app U.unop).hom g = 0 := by
    rw [Scheme.Hom.congr_app Limits.pullback.condition U.unop]
    have hz : ((Limits.pullback.snd f J.subschemeι ≫ J.subschemeι).app U.unop).hom g
        = 0 := by
      show ((Limits.pullback.snd f J.subschemeι).app _).hom
        ((J.subschemeι.app U.unop).hom g) = 0
      rw [RingHom.mem_ker.mp hg]
      exact map_zero _
    show ((Limits.pullback f J.subschemeι).presheaf.map _).hom
      (((Limits.pullback.snd f J.subschemeι ≫ J.subschemeι).app U.unop).hom g) = 0
    rw [hz]
    exact map_zero _
  rw [hι]
  show ((J.comapIso f).hom.app _).hom
    (((Limits.pullback.fst f J.subschemeι).app _).hom ((f.app U.unop).hom g)) = 0
  have h1 : ((Limits.pullback.fst f J.subschemeι).app _).hom
      ((f.app U.unop).hom g) = 0 := hstep1
  rw [h1]
  exact map_zero _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from the ideal presheaf to the pushforward of the comap
ideal presheaf: componentwise `g ↦ f♯ g`. -/
noncomputable def idealPushHom :
    idealPresheaf J ⟶
      (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).obj
        (idealPresheaf (J.comap f)) where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).obj
      (idealPresheaf (J.comap f))).obj U)
    { toFun := fun g => ⟨f.app U.unop g.1, app_mem_idealSections_comap f J U g.2⟩
      map_add' := fun g g' => Subtype.ext (by
        show (f.app U.unop).hom (g.1 + g'.1) = _
        rw [map_add]
        rfl)
      map_smul' := fun r g => Subtype.ext (by
        let r' : Γ(X, U.unop) := r
        show (f.app U.unop).hom (r' * g.1) =
          (f.app U.unop).hom r' * (f.app U.unop).hom g.1
        exact map_mul _ r' g.1) }
  naturality {U V} i := by
    refine ModuleCat.hom_ext (LinearMap.ext fun g => ?_)
    refine Subtype.ext ?_
    show (f.app V.unop).hom ((X.presheaf.map i).hom g.1) =
      (X'.presheaf.map ((TopologicalSpace.Opens.map f.base).map i.unop).op).hom
        ((f.app U.unop).hom g.1)
    have h1 : (X'.presheaf.map ((TopologicalSpace.Opens.map f.base).map i.unop).op).hom
        ((f.app U.unop).hom g.1) =
        (ConcreteCategory.hom (f.app U.unop ≫
          X'.presheaf.map ((TopologicalSpace.Opens.map f.base).map i.unop).op)) g.1 := rfl
    have h2 : (f.app V.unop).hom ((X.presheaf.map i).hom g.1) =
        (ConcreteCategory.hom (X.presheaf.map i ≫ f.app V.unop)) g.1 := rfl
    rw [h1, h2]
    exact congrArg (fun (ψ : _ ⟶ _) => (ConcreteCategory.hom ψ) g.1)
      (f.naturality i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comap ideal at an affine open is the kernel of the base-changed inclusion's
component (`Hom.ker_apply`; the first projection off a closed immersion is
quasi-compact). -/
theorem comap_ideal_eq_ker (V' : X'.affineOpens) :
    (J.comap f).ideal V' =
      RingHom.ker ((Limits.pullback.fst f J.subschemeι).app V'.1).hom := by
  haveI : IsClosedImmersion (Limits.pullback.fst f J.subschemeι) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact Scheme.Hom.ker_apply _ V'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[NAT-3-SCHEME]** The comap ideal on an affine chart of the source is generated by
the pulled-back generator (the affine base-change kernel computation: `Spec` of
`ker (B → B ⊗[A] A/(g)) = (φ g)`, via `ker_algebraMap_tensorQuot_span`). -/
theorem comap_ideal_eq_span_appLE {V : X.affineOpens} {g : Γ(X, V.1)}
    (hspan : J.ideal V = Ideal.span {g}) (V' : X'.affineOpens) (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (J.comap f).ideal V' = Ideal.span {f.appLE V.1 V'.1 hV' g} := by
  rw [ModularCurves.ideal_comap_affineOpens_span J f V' V hV' g hspan,
    ModularCurves.affinePullbackSection_eq_appLE]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The transposed comparison: from the presheaf pullback of the ideal presheaf to the
comap ideal presheaf (adjunction transpose of `idealPushHom`). -/
noncomputable def idealPullHom :
    (PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom).obj (idealPresheaf J) ⟶
      idealPresheaf (J.comap f) :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    f.toRingCatSheafHom.hom).homEquiv _ _).symm (idealPushHom f J)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A7-3 evaluation]** The adjunction-triangle value of the transposed comparison at
a unit image: `ψ (η g) = f♯ g`. The only computable values of a map out of the abstract
left-adjoint pullback are those on unit images, and they are exactly the pushed
sections. -/
theorem idealPullHom_app_unit (V : X.Opens) (g : Γ(X, V))
    (hg : g ∈ idealSections J (Opposite.op V)) :
    (idealPullHom f J).app (Opposite.op (f ⁻¹ᵁ V))
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          f.toRingCatSheafHom.hom).unit.app (idealPresheaf J)).app
            (Opposite.op V) ⟨g, hg⟩) =
      ⟨f.app V g, app_mem_idealSections_comap f J (Opposite.op V) hg⟩ := by
  have htri := ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    f.toRingCatSheafHom.hom).homEquiv (idealPresheaf J)
      (idealPresheaf (J.comap f))).apply_symm_apply (idealPushHom f J)
  rw [Adjunction.homEquiv_unit] at htri
  have hval := congrArg (fun (m : idealPresheaf J ⟶
      (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).obj
        (idealPresheaf (J.comap f))) =>
    (ConcreteCategory.hom (m.app (Opposite.op V))) ⟨g, hg⟩) htri
  exact hval

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A7-3]** The transposed comparison is locally surjective: near any point, the
comap ideal is the span of the pulled-back generator (`comap_ideal_eq_span_appLE`), and
that generator is the value of the comparison at a unit image
(`idealPullHom_app_unit`), so every section is a scalar multiple of a value. -/
theorem isLocallySurjective_idealPullHom
    (h : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      J.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1)) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X')
      ((PresheafOfModules.toPresheaf _).map (idealPullHom f J)) := by
  constructor
  intro V₀ s
  rw [Opens.mem_grothendieckTopology]
  intro x' hx'
  obtain ⟨V, hcV, g, hspan, hnzd⟩ := h (f.base x')
  have hopen : x' ∈ f ⁻¹ᵁ V.1 ⊓ V₀ := ⟨hcV, hx'⟩
  obtain ⟨_, ⟨V's, hV'aff, rfl⟩, hxV', hsub⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hopen (f ⁻¹ᵁ V.1 ⊓ V₀).2
  have hVle1 : V's ≤ f ⁻¹ᵁ V.1 := fun a ha => (hsub ha).1
  have hVle0 : V's ≤ V₀ := fun a ha => (hsub ha).2
  have hspan' := comap_ideal_eq_span_appLE f J hspan ⟨V's, hV'aff⟩ hVle1
  -- the restriction of `s` to the chart, and its span decomposition
  let sV' := ((PresheafOfModules.toPresheaf _).obj
    (idealPresheaf (J.comap f))).map (homOfLE hVle0).op s
  let sv : idealSections (J.comap f) (Opposite.op V's) := sV'
  have hsmem : sv.1 ∈ (J.comap f).ideal ⟨V's, hV'aff⟩ :=
    ((J.comap f).ker_subschemeι_app ⟨V's, hV'aff⟩) ▸ sv.2
  rw [hspan'] at hsmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hsmem
  have hgmem : g ∈ idealSections J (Opposite.op V.1) := by
    rw [show idealSections J (Opposite.op V.1) = J.ideal V from
      J.ker_subschemeι_app V, hspan]
    exact Ideal.mem_span_singleton_self g
  -- the unit image, restricted to the chart
  let η := (PresheafOfModules.pullbackPushforwardAdjunction.{u}
    f.toRingCatSheafHom.hom).unit.app (idealPresheaf J)
  let τ₀ : ((PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom).obj
      (idealPresheaf J)).obj (Opposite.op (f ⁻¹ᵁ V.1)) :=
    η.app (Opposite.op V.1) ⟨g, hgmem⟩
  let τ₁ := ((PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom).obj
    (idealPresheaf J)).map (homOfLE hVle1).op τ₀
  let b' : ((X'.ringCatSheaf.obj).obj (Opposite.op V's)) := b
  refine ⟨V's, homOfLE hVle0, ⟨b' • τ₁, ?_⟩, hxV'⟩
  -- evaluate: linearity, naturality, the unit evaluation, and the span identity
  have hlin := ((idealPullHom f J).app (Opposite.op V's)).hom.map_smul b' τ₁
  have hnat := PresheafOfModules.naturality_apply (idealPullHom f J)
    (homOfLE hVle1).op τ₀
  have heval := idealPullHom_app_unit f J V.1 g hgmem
  show (idealPullHom f J).app (Opposite.op V's) (b' • τ₁) = sV'
  rw [hlin]
  have hτ₁ : (idealPullHom f J).app (Opposite.op V's) τ₁ =
      (idealPresheaf (J.comap f)).map (homOfLE hVle1).op
        ((idealPullHom f J).app (Opposite.op (f ⁻¹ᵁ V.1)) τ₀) := hnat
  rw [hτ₁]
  have heval' : (idealPullHom f J).app (Opposite.op (f ⁻¹ᵁ V.1)) τ₀ =
      ⟨f.app V.1 g, app_mem_idealSections_comap f J (Opposite.op V.1) hgmem⟩ :=
    heval
  rw [heval']
  refine Subtype.ext ?_
  show b * (X'.presheaf.map (homOfLE hVle1).op) ((f.app V.1) g) = sv.1
  rw [← hb]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[NAT-3]** The transposed comparison is inverted by sheafification: it is locally
surjective (`isLocallySurjective_idealPullHom`), its sheafification is a map of
invertible modules (the pullback of the ideal line and the comap ideal line), and a
locally surjective map of invertible modules is an isomorphism
(`isIso_of_isLocallySurjective_of_isInvertible`) — injectivity is never chased through
the opaque left-adjoint pullback. -/
theorem sheafificationW_idealPullHom
    (h : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      J.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1))
    (h' : ∀ c : ↥X', ∃ V : X'.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X', V.1),
      (J.comap f).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X', V.1)) :
    PresheafOfModules.sheafificationW (𝟙 X'.ringCatSheaf.obj) (idealPullHom f J) := by
  classical
  rw [PresheafOfModules.sheafificationW_iff]
  -- the unit of the sheafification adjunction on the codomain is in W, hence locally
  -- surjective; compose with the local surjectivity of the comparison itself
  have hWunit : PresheafOfModules.sheafificationW (𝟙 X'.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X'.ringCatSheaf.obj)).unit.app (idealPresheaf (J.comap f))) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X'.ringCatSheaf.obj)).left_triangle_components (idealPresheaf (J.comap f))
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X'.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 X'.ringCatSheaf.obj)).obj
            (idealPresheaf (J.comap f)))) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  obtain ⟨-, hunitSurj⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunit
  haveI := hunitSurj
  haveI hψ := isLocallySurjective_idealPullHom f J h
  -- naturality of the unit: ψ ≫ η_Q = η_PB ≫ RA(L ψ); local surjectivity of the
  -- left side gives local surjectivity of the second factor
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X'.ringCatSheaf.obj)).unit.naturality (idealPullHom f J)
  rw [Functor.id_map] at hnat
  haveI h1 : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X')
      ((PresheafOfModules.toPresheaf
        ((sheafToPresheaf (Opens.grothendieckTopology ↥X') RingCat).obj
          X'.ringCatSheaf)).map (idealPullHom f J) ≫
        (PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥X') RingCat).obj
            X'.ringCatSheaf)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X'.ringCatSheaf.obj)).unit.app (idealPresheaf (J.comap f)))) := by
    haveI hψ' : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X')
        ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥X') RingCat).obj
            X'.ringCatSheaf)).map (idealPullHom f J)) := hψ
    haveI hu' : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X')
        ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥X') RingCat).obj
            X'.ringCatSheaf)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X'.ringCatSheaf.obj)).unit.app (idealPresheaf (J.comap f)))) :=
      hunitSurj
    infer_instance
  rw [← Functor.map_comp, hnat, Functor.map_comp] at h1
  -- extract the second factor's local surjectivity by hand: every image-sieve of the
  -- composite refines the image-sieve of the second factor (shift the witness)
  have hLsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X')
      ((PresheafOfModules.toPresheaf _).map
        (((PresheafOfModules.sheafification (𝟙 X'.ringCatSheaf.obj)).map
          (idealPullHom f J)).val)) := by
    constructor
    intro U s
    refine (Opens.grothendieckTopology ↥X').superset_covering ?_
      (h1.imageSieve_mem s)
    intro Y i hi
    obtain ⟨t, ht⟩ := hi
    exact ⟨((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X'.ringCatSheaf.obj)).unit.app
          ((PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom).obj
            (idealPresheaf J)))).app _ t, ht⟩
  -- both sides of the sheafified comparison are invertible modules
  have hInvDom : IsInvertible ((PresheafOfModules.sheafification
      (𝟙 X'.ringCatSheaf.obj)).obj ((PresheafOfModules.pullback.{u}
      f.toRingCatSheafHom.hom).obj (idealPresheaf J))) := by
    refine IsInvertible.of_iso ((isInvertible_idealModule J h).pullback f) ?_
    exact (pullbackIsoSheafifyPresheafPullback f (idealModule J)).symm
  have hInvCod : IsInvertible ((PresheafOfModules.sheafification
      (𝟙 X'.ringCatSheaf.obj)).obj (idealPresheaf (J.comap f))) := by
    refine IsInvertible.of_iso (isInvertible_idealModule (J.comap f) h') ?_
    exact sheafifyValIso (idealModule (J.comap f))
  exact isIso_of_isLocallySurjective_of_isInvertible
    ((PresheafOfModules.sheafification (𝟙 X'.ringCatSheaf.obj)).map
      (idealPullHom f J)) hInvDom hInvCod hLsurj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Pullback of a locally principal ideal module** (KM 1.1.2 shape: effective Cartier
divisors pull back to effective Cartier divisors along base change, at the level of
ideal modules): if `J` is affine-locally generated by a single nonzerodivisor and its
comap along `f` is too, the module pullback of `idealModule J` is the ideal module of
the comap. -/
theorem nonempty_pullback_idealModule {X' X : Scheme.{u}} (f : X' ⟶ X)
    (J : X.IdealSheafData)
    (h : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      J.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1))
    (h' : ∀ c : ↥X', ∃ V : X'.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X', V.1),
      (J.comap f).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X', V.1)) :
    Nonempty ((Modules.pullback f).obj (idealModule J) ≅ idealModule (J.comap f)) := by
  have hw := sheafificationW_idealPullHom f J h h'
  rw [PresheafOfModules.sheafificationW_iff] at hw
  haveI : IsIso ((PresheafOfModules.sheafification (𝟙 X'.ringCatSheaf.obj)).map
    (idealPullHom f J)) := hw
  exact ⟨pullbackIsoSheafifyPresheafPullback f (idealModule J) ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 X'.ringCatSheaf.obj)).map
      (idealPullHom f J)) ≪≫ sheafifyValIso (idealModule (J.comap f))⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-change transport for the ideal module of a section divisor.** The module
pullback of `I(D_z)` along the base-change projection is the ideal module of the
base-changed section's divisor.

Both local-principality hypotheses of `nonempty_pullback_idealModule` come for free from
`RelEffCartierDiv.sectionDivisor_isOfficial` (upstairs, and downstairs after
base-changing the smoothness), so this is the usable form: it is what lets an identity
between ideal modules proved over the *universal* pair of points be transported to an
arbitrary base. -/
theorem nonempty_pullback_idealModule_ker_sectionBaseChange {C S T : Scheme.{u}}
    {π : C ⟶ S} [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    Nonempty ((Modules.pullback (Limits.pullback.fst π t)).obj
          (idealModule (Scheme.Hom.ker z)) ≅
        idealModule (Scheme.Hom.ker
          (Limits.pullback.lift (t ≫ z) (𝟙 T)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) :
            T ⟶ Limits.pullback π t))) := by
  haveI hsep : IsSeparated (Limits.pullback.snd π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) π t ‹_›
  have hsm' : SmoothOfRelativeDimension 1 (Limits.pullback.snd π t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) π t hsm
  have hker := ModularCurves.RelEffCartierDiv.ker_sectionBaseChange z hz t
  -- both local-principality hypotheses, stated at the `Scheme.Hom.ker` form the pullback
  -- comparison wants (`(sectionDivisor _ z hz).ideal` is `z.ker`, but only definitionally)
  have hJ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ f : Γ(C, V.1),
      (Scheme.Hom.ker z).ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors Γ(C, V.1) :=
    (ModularCurves.RelEffCartierDiv.sectionDivisor_isOfficial hsm z hz).locallyPrincipal
  have hJ' : ∀ c : ↥(Limits.pullback π t), ∃ V : (Limits.pullback π t).affineOpens,
      c ∈ V.1 ∧ ∃ f : Γ(Limits.pullback π t, V.1),
        ((Scheme.Hom.ker z).comap (Limits.pullback.fst π t)).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(Limits.pullback π t, V.1) := by
    rw [← hker]
    exact (ModularCurves.RelEffCartierDiv.sectionDivisor_isOfficial hsm'
      (Limits.pullback.lift (t ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      (Limits.pullback.lift_snd _ _ _)).locallyPrincipal
  exact ⟨(nonempty_pullback_idealModule (Limits.pullback.fst π t) (Scheme.Hom.ker z)
    hJ hJ').some ≪≫ eqToIso (congrArg idealModule hker.symm)⟩

end AlgebraicGeometry.Scheme.Modules
