/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import ModularCurves.ForMathlib.SheafOfModulesMonoidal
import ModularCurves.Picard.InvertibleSheaf

/-!
# Pullback of sheaves of modules and the sheafified tensor — [PIC-P1b-MONO]

The AINTLIB ModularCurves stream leaf **[PIC-P1b-MONO]**: compatibility of the
sheaf-of-modules pullback with the sheafified tensor, `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`.

## Main results (all sorry-free, axiom-clean)

* `Scheme.Modules.nonempty_pullback_tensorObj_of_isOpenImmersion`: the **open-immersion**
  case, in full — pullback along `f : Y ⟶ X` open immersion commutes with `tensorObj`.
  This is the case the invertibility layer consumes (trivializing covers restrict along
  open inclusions), so with it:
* `Scheme.Modules.IsInvertible.tensorObj` (moved here from `Picard/InvertibleSheaf.lean`,
  statement unchanged): the tensor product of invertible `𝒪ₓ`-modules is invertible —
  GME 2.2.2, previously GAP-1-gated, now sorry-free.

The ι-route ingredients, each of independent (mathlib-PR-able) interest:

* `ModuleCat.restrictScalarsTensorIso` (**ι-CORE**): restriction of scalars along a
  bijective ring hom is strongly monoidal at objects (`TensorProduct.equivOfCompatibleSMul`,
  both directions `x ⊗ₜ y ↦ x ⊗ₜ y`).
* `PresheafOfModules.restrictScalarsTensorObjIso` / `pushforwardTensorIso` (**ι-PF⊗**):
  the presheaf-of-modules pushforward along a componentwise-iso ring comparison is strongly
  monoidal at objects (reindexing half = mathlib's `pushforward₀OfCommRingCat.Monoidal`).
* `functorPullback_opensFunctor_mem` + `isLocallyInjective/Surjective_whiskerLeft_opensFunctor`
  (**ι-LOCBIJ**): restriction along an open immersion preserves local bijectivity
  (Zariski sieve transfer).
* `PresheafOfModules.nonempty_sheafify_tensor_idem` (**D-Idem**): the sheafification
  collapses its own double-tensor, `sh(A ⊗ B) ≅ sh(sh(A).val ⊗ sh(B).val)` — from this
  stream's GAP1-W-MONO leaf `sheafificationW_tensorHom`.

## Registered residual (general `f`)

`nonempty_sheafify_presheafPullback_tensor` below and `nonempty_pullback_tensorObj` in
`Picard/InvertibleSheaf.lean` state the general-`f` forms; both remain `sorry`
([PIC-P1b-MONO]-general, gating nothing). NOTE (adversarial, from the decompose): the
presheaf pullback is **not** strong monoidal for general `f` at the presheaf level
(`pullback φ := (pushforward φ).leftAdjoint` hides an inverse-image left Kan extension);
only the *sheafified* comparison is an iso (stalkwise, hence locally bijective). Route
notes, verbatim source quotes and attack logs:
`.mathlib-quality/decomposition-pullback-monoidal.md`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Functor

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

/-- **[PIC-P1b-MONO], leaf D-Idem — this project's GAP1-W-MONO, repackaged.**
The presheaf sheafification is strong monoidal for the presheaf tensor: the canonical map
`sh(A ⊗ B) → sh(sh(A).val ⊗ sh(B).val)` induced by the sheafification units is an iso.
Proved from `sheafificationW_tensorHom` (the GAP1-W-MONO leaf: the tensor of two
locally-bijective maps is locally bijective) applied to the two unit maps `η_A, η_B`
(each in `sheafificationW`, since `sh.map η` is inverse to the iso counit by the triangle
identity), then "`sh` inverts `sheafificationW`". Stated over a sheaf of commutative rings
`⟨S ⋙ forget₂, hS⟩` (the reflective `α = 𝟙` setting where the localization machinery
resolves, mirroring `SheafOfModulesMonoidal`'s instantiation) and `Nonempty`-wrapped. -/
theorem nonempty_sheafify_tensor_idem
    (A B : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    Nonempty
      ((sheafification (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj
          (A ⊗ B) ≅
        (sheafification (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj
          (((sheafification
                (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj A).val ⊗
            ((sheafification
                (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ :
                  Sheaf J RingCat.{u}).obj)).obj B).val)) := by
  have hunit : ∀ (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)),
      sheafificationW
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)
        ((sheafificationAdjunction
          (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).unit.app M) := by
    intro M
    rw [sheafificationW_iff_isLocallyBijective,
      toPresheaf_map_sheafificationAdjunction_unit_app]
    exact ⟨(J.W_toSheafify M.presheaf).isLocallyInjective,
      (J.W_toSheafify M.presheaf).isLocallySurjective⟩
  have hstab := sheafificationW_tensorHom
    (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)
    ((sheafificationAdjunction
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).unit.app A)
    ((sheafificationAdjunction
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).unit.app B)
    (hunit A) (hunit B)
  rw [sheafificationW_iff] at hstab
  exact ⟨@asIso _ _ _ _ _ hstab⟩

end PresheafOfModules

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **[PIC-P1b-MONO], leaf ι-CORE.** Restriction of scalars along a *bijective* ring
homomorphism is strongly monoidal at the object level: the tensor product over `R` of the
restricted modules is the restriction of the tensor product over `S`. Both directions are
`x ⊗ₜ y ↦ x ⊗ₜ y` (`TensorProduct.equivOfCompatibleSMul`); the `R`- and `S`-actions are
intertwined by `g`, so each is compatible for the other's tensor. -/
noncomputable def restrictScalarsTensorIso (g : R →+* S) (hg : Function.Bijective g)
    (M N : ModuleCat.{u} S) :
    (restrictScalars g).obj M ⊗ (restrictScalars g).obj N ≅
      (restrictScalars g).obj (M ⊗ N) := by
  let e : R ≃+* S := RingEquiv.ofBijective g hg
  letI : Module R ↑M := Module.compHom ↑M g
  letI : Module R ↑N := Module.compHom ↑N g
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S R := (e.symm : S →+* R).toAlgebra
  haveI hMt : IsScalarTower R S ↑M := ⟨fun r s m => mul_smul (g r) s m⟩
  haveI hNt : IsScalarTower R S ↑N := ⟨fun r s n => mul_smul (g r) s n⟩
  haveI hMt' : IsScalarTower S R ↑M := ⟨fun s r m => by
    show e (e.symm s * r) • m = s • e r • m
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  haveI hNt' : IsScalarTower S R ↑N := ⟨fun s r n => by
    show e (e.symm s * r) • n = s • e r • n
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  haveI : SMulCommClass S R ↑M := ⟨fun s r m => by
    show s • e r • m = e r • s • m
    rw [smul_comm]⟩
  haveI : SMulCommClass R R ↑M := ⟨fun r r' m => by
    show e r • e r' • m = e r' • e r • m
    rw [smul_comm]⟩
  exact (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars g).obj M ⊗ (restrictScalars g).obj N))
    (M₂ := ↑((restrictScalars g).obj (M ⊗ N)))
    (TensorProduct.equivOfCompatibleSMul S R R ↑M ↑N).toAddEquiv
    (fun r x => (TensorProduct.equivOfCompatibleSMul S R R ↑M ↑N).map_smul r x)).toModuleIso

@[simp]
lemma restrictScalarsTensorIso_hom_tmul (g : R →+* S) (hg : Function.Bijective g)
    (M N : ModuleCat.{u} S)
    (m : ↑((restrictScalars g).obj M)) (n : ↑((restrictScalars g).obj N)) :
    (restrictScalarsTensorIso g hg M N).hom (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl

@[simp]
lemma restrictScalarsTensorIso_inv_tmul (g : R →+* S) (hg : Function.Bijective g)
    (M N : ModuleCat.{u} S) (m : ↑M) (n : ↑N) :
    (restrictScalarsTensorIso g hg M N).inv (m ⊗ₜ n) =
      (m ⊗ₜ n : ↑((restrictScalars g).obj M ⊗ (restrictScalars g).obj N)) :=
  rfl

end ModuleCat

namespace PresheafOfModules

section RestrictScalarsTensor

variable {C : Type u₁} [Category.{v₁} C] {T₁ T₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
  (ψ : T₁ ⋙ forget₂ CommRingCat RingCat ⟶ T₂ ⋙ forget₂ CommRingCat RingCat)
  [∀ X : Cᵒᵖ, IsIso (ψ.app X)]

/-- **[PIC-P1b-MONO], leaf ι-PF⊗ (restriction half).** Restriction of scalars of presheaves
of modules along a *componentwise-isomorphic* morphism of presheaves of commutative rings is
strongly monoidal at the object level: `rs(M) ⊗ rs(N) ≅ rs(M ⊗ N)`. Componentwise this is
`ModuleCat.restrictScalarsTensorIso` (both directions `x ⊗ₜ y ↦ x ⊗ₜ y`); the presheaf
tensor is sectionwise. -/
noncomputable def restrictScalarsTensorObjIso
    (M N : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) :
    (restrictScalars ψ).obj M ⊗ (restrictScalars ψ).obj N ≅
      (restrictScalars ψ).obj (M ⊗ N) :=
  isoMk
    (fun X => ModuleCat.restrictScalarsTensorIso (ψ.app X).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app X)) (M.obj X) (N.obj X))
    (fun X Y f => ModuleCat.MonoidalCategory.tensor_ext (fun m n => by
      dsimp
      erw [Monoidal.tensorObj_map_tmul]))

end RestrictScalarsTensor

section PushforwardTensor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))
  [∀ X : Cᵒᵖ, IsIso (φ.app X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[PIC-P1b-MONO], leaf ι-PF⊗.** The presheaf-of-modules pushforward along a site functor
with *componentwise-isomorphic* ring comparison `φ` is strongly monoidal at the object level:
`pf(P) ⊗ pf(Q) ≅ pf(P ⊗ Q)`. Factors as the reindexing `pushforward₀OfCommRingCat` (strongly
monoidal by mathlib, `μIso = Iso.refl`) followed by restriction of scalars along the
componentwise-iso `φ` (`restrictScalarsTensorObjIso`). This covers the restriction of
modules along an open immersion of schemes, where the abstract inverse-image pullback
agrees with this pushforward. -/
noncomputable def pushforwardTensorIso
    (P Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (pushforward.{u} φ).obj P ⊗ (pushforward.{u} φ).obj Q ≅
      (pushforward.{u} φ).obj (P ⊗ Q) :=
  restrictScalarsTensorObjIso (T₁ := S) (T₂ := F.op ⋙ R) φ
      ((pushforward₀OfCommRingCat F R).obj P) ((pushforward₀OfCommRingCat F R).obj Q) ≪≫
    (restrictScalars φ).mapIso
      (Functor.Monoidal.μIso (pushforward₀OfCommRingCat F R) P Q)

end PushforwardTensor

end PresheafOfModules

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- **[PIC-P1b-MONO], leaf ι-LOCBIJ (sieve transfer).** For an open immersion `f`, the
`opensFunctor`-pullback of a Zariski-covering sieve of `f ''ᵁ U` covers `U`: any point of `U`
maps into some member `W` of the sieve, and `f ⁻¹ᵁ W ≤ U` witnesses coverage (its image lies
in `W` by `image_preimage_le`, so the sieve's downward closure catches it; parallel maps of
opens are equal by proof irrelevance). -/
lemma functorPullback_opensFunctor_mem {U : X.Opens} (S : Sieve (f.opensFunctor.obj U))
    (hS : S ∈ Opens.grothendieckTopology Y (f.opensFunctor.obj U)) :
    S.functorPullback f.opensFunctor ∈ Opens.grothendieckTopology X U := by
  intro x hx
  obtain ⟨W, g, hg, hW⟩ := hS (f.base x) ⟨x, hx, rfl⟩
  refine ⟨f ⁻¹ᵁ W, homOfLE ?_, ?_, hW⟩
  · exact (Scheme.Hom.preimage_image_eq f U) ▸
        (fun a ha => g.le ha : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ (f ''ᵁ U))
  · show S (f.opensFunctor.map _)
    have h1 : f.opensFunctor.obj (f ⁻¹ᵁ W) ≤ W := Scheme.Hom.image_preimage_le f W
    exact Subsingleton.elim (homOfLE h1 ≫ g) (f.opensFunctor.map _) ▸
      S.downward_closed hg (homOfLE h1)

/-- **[PIC-P1b-MONO], leaf ι-LOCBIJ (injective half).** Whiskering with the `opensFunctor`
of an open immersion preserves local injectivity of morphisms of presheaves: the equalizer
sieve of the whiskered map is the `functorPullback` of the equalizer sieve upstairs, which
covers by the sieve transfer. -/
lemma isLocallyInjective_whiskerLeft_opensFunctor
    {A B : (Y.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}} (g : A ⟶ B)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) g] :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Functor.whiskerLeft f.opensFunctor.op g) := by
  constructor
  intro U x y h
  exact functorPullback_opensFunctor_mem f _
    (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology Y) g x y h)

/-- **[PIC-P1b-MONO], leaf ι-LOCBIJ (surjective half).** Whiskering with the `opensFunctor`
of an open immersion preserves local surjectivity: the image sieve of the whiskered map is
the `functorPullback` of the image sieve upstairs. -/
lemma isLocallySurjective_whiskerLeft_opensFunctor
    {A B : (Y.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}} (g : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) g] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Functor.whiskerLeft f.opensFunctor.op g) := by
  constructor
  intro U t
  exact functorPullback_opensFunctor_mem f _
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology Y) g t)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The ring comparison of restriction along an open immersion `f : Y ⟶ X`, as a raw
morphism of `RingCat`-valued presheaves on `Y.Opens` — the `whiskerRight` of the `appIso`
inverses, exactly the morphism `Scheme.Modules.restrictFunctor` pushes forward along. -/
noncomputable def restrictRingHom (f : Y ⟶ X) [IsOpenImmersion f] :
    Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat ⟶
      f.opensFunctor.op ⋙ (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) where
  app U := (forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv
  naturality {_U _V} i :=
    ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
      ((congrArg (fun g => (forget₂ CommRingCat RingCat).map g)
        (f.appIso_inv_naturality i)).trans
        ((forget₂ CommRingCat RingCat).map_comp _ _))

instance (f : Y ⟶ X) [IsOpenImmersion f] (U : (Y.Opens)ᵒᵖ) :
    IsIso ((restrictRingHom f).app U) :=
  inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map ((f.appIso U.unop).inv)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Y`-side sheafification inverts the restricted `X`-side sheafification unit of
`M.val ⊗ N.val`: the unit is locally bijective, and restriction along the open immersion `f`
preserves local injectivity/surjectivity (`isLocally…_whiskerLeft_opensFunctor`). -/
theorem sheafificationW_pushforward_unit_tensor (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) :
    PresheafOfModules.sheafificationW (𝟙 Y.ringCatSheaf.obj)
      ((PresheafOfModules.pushforward (restrictRingHom f)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (M.val ⊗ N.val))) := by
  rw [PresheafOfModules.sheafificationW_iff_isLocallyBijective]
  haveI hi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (M.val ⊗ N.val))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallyInjective
  haveI hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (M.val ⊗ N.val))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  exact ⟨isLocallyInjective_whiskerLeft_opensFunctor f
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (M.val ⊗ N.val))),
    isLocallySurjective_whiskerLeft_opensFunctor f
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (M.val ⊗ N.val)))⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- **[PIC-P1b-MONO], leaf ι-MAIN.** Pullback along an *open immersion* commutes with the
sheafified tensor: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`. Route: identify `f^*` with sectionwise
restriction (`restrictFunctorIsoPullback`), un-sheafify (`sheafifyValIso`), collapse the
inner `X`-side sheafification (its unit is locally bijective; restriction preserves local
bijectivity by `isLocallyInjective/Surjective_whiskerLeft_opensFunctor`, so the `Y`-side
sheafification inverts the restricted unit), and interchange restriction with the presheaf
tensor (`pushforwardTensorIso`, sectionwise `x ⊗ₜ y ↦ x ⊗ₜ y`). -/
theorem nonempty_pullback_tensorObj_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) :
    Nonempty ((Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N)) := by
  have hmem := sheafificationW_pushforward_unit_tensor f M N
  rw [PresheafOfModules.sheafificationW_iff] at hmem
  have e1 : (Modules.pullback f).obj (tensorObj M N) ≅
      (restrictFunctor f).obj (tensorObj M N) :=
    (restrictFunctorIsoPullback f).symm.app (tensorObj M N)
  have e2 : (restrictFunctor f).obj (tensorObj M N) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        (((restrictFunctor f).obj (tensorObj M N)).val) :=
    (sheafifyValIso _).symm
  have e3 : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        (((restrictFunctor f).obj (tensorObj M N)).val) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward (restrictRingHom f)).obj (M.val ⊗ N.val)) :=
    (@asIso _ _ _ _ _ hmem).symm
  have e4 : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward (restrictRingHom f)).obj (M.val ⊗ N.val)) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward (restrictRingHom f)).obj M.val ⊗
          (PresheafOfModules.pushforward (restrictRingHom f)).obj N.val) :=
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.pushforwardTensorIso (restrictRingHom f) M.val N.val)).symm
  have e5a : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward (restrictRingHom f)).obj M.val ⊗
          (PresheafOfModules.pushforward (restrictRingHom f)).obj N.val) ≅
      tensorObj ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) :=
    Iso.refl _
  have e5b : tensorObj ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) ≅
      tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N) :=
    tensorObjCongr ((restrictFunctorIsoPullback f).app M)
      ((restrictFunctorIsoPullback f).app N)
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5a ≪≫ e5b⟩



section Collapse

/-- The symmetric monoidal structure on `X.PresheafOfModules` (same transport as the
monoidal instances in `Picard/InvertibleSheaf.lean`), providing the braiding `β_` for the
commutativity of the sheafified tensor. -/
noncomputable instance (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory
    (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

variable (X) in
/-- The sheafification unit of any presheaf of modules on a scheme is inverted by
sheafification (its underlying map is `toSheafify`, a `J.W`-member). Scheme-side workhorse
for the collapse lemmas below. -/
theorem sheafificationW_unit_app (A : X.PresheafOfModules) :
    PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app A) := by
  rw [PresheafOfModules.sheafificationW_iff_isLocallyBijective,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact ⟨(GrothendieckTopology.W_toSheafify _ _).isLocallyInjective,
    (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Left collapse**: re-sheafifying the left tensor factor changes nothing,
`sh(A ⊗ B) ≅ sh(sh(A).val ⊗ B)`. Input to the Picard-group associativity/unit laws. -/
theorem nonempty_sheafify_tensor_left_collapse (A B : X.PresheafOfModules) :
    Nonempty ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (A ⊗ B) ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A).val ⊗ B)) := by
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥X)
      (𝟙 X.ringCatSheaf.obj) := inferInstanceAs (Presheaf.IsLocallyInjective _
        (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (𝟙 X.ringCatSheaf.obj) := inferInstanceAs (Presheaf.IsLocallySurjective _
        (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
  have hstab := PresheafOfModules.sheafificationW_tensorHom (𝟙 X.ringCatSheaf.obj)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app A) (𝟙 B)
    (sheafificationW_unit_app X A)
    (by rw [PresheafOfModules.sheafificationW_iff, CategoryTheory.Functor.map_id]; infer_instance)
  rw [PresheafOfModules.sheafificationW_iff] at hstab
  exact ⟨@asIso _ _ _ _ _ hstab⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Right collapse**: re-sheafifying the right tensor factor changes nothing,
`sh(A ⊗ B) ≅ sh(A ⊗ sh(B).val)`. Input to the Picard-group associativity/unit laws. -/
theorem nonempty_sheafify_tensor_right_collapse (A B : X.PresheafOfModules) :
    Nonempty ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (A ⊗ B) ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (A ⊗ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj B).val)) := by
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥X)
      (𝟙 X.ringCatSheaf.obj) := inferInstanceAs (Presheaf.IsLocallyInjective _
        (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (𝟙 X.ringCatSheaf.obj) := inferInstanceAs (Presheaf.IsLocallySurjective _
        (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
  have hstab := PresheafOfModules.sheafificationW_tensorHom (𝟙 X.ringCatSheaf.obj)
    (𝟙 A) ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app B)
    (by rw [PresheafOfModules.sheafificationW_iff, CategoryTheory.Functor.map_id]; infer_instance)
    (sheafificationW_unit_app X B)
  rw [PresheafOfModules.sheafificationW_iff] at hstab
  exact ⟨@asIso _ _ _ _ _ hstab⟩

/-- **Associativity of the sheafified tensor**, `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)` — GME p. 108's
implicit group-law coherence, now gap-free: collapse both re-sheafifications and transport
the presheaf associator. Input to the Picard-group multiplication. -/
theorem nonempty_tensorObj_assoc (M N P : X.Modules) :
    Nonempty (tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P)) := by
  obtain ⟨eL⟩ := nonempty_sheafify_tensor_left_collapse (M.val ⊗ N.val) P.val
  obtain ⟨eR⟩ := nonempty_sheafify_tensor_right_collapse M.val (N.val ⊗ P.val)
  exact ⟨eL.symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (α_ M.val N.val P.val) ≪≫
    eR⟩

/-- **Commutativity of the sheafified tensor**, `M ⊗ N ≅ N ⊗ M` (the presheaf braiding,
sheafified). Input to the Picard group's commutativity. -/
theorem nonempty_tensorObj_comm (M N : X.Modules) :
    Nonempty (tensorObj M N ≅ tensorObj N M) :=
  ⟨(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)⟩

end Collapse

/-- The tensor product of invertible `𝒪ₓ`-modules is invertible (GME p. 108: `Pic(E_T)`
is "the group of isomorphism classes of all invertible sheaves"). On the common refinement
`{U i ⊓ V j}` of the two trivializing covers both factors are trivial, so — using that
pullback along the (open-immersion) inclusions commutes with the sheafified tensor
(`nonempty_pullback_tensorObj_of_isOpenImmersion`) — the tensor restricts to `𝒪 ⊗ 𝒪 ≅ 𝒪`
there. Sorry-free: the GME 2.2.2 tensor-invertibility, previously gated by GAP-1. -/
theorem IsInvertible.tensorObj {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) : IsInvertible (tensorObj M N) := by
  obtain ⟨ιM, U, hU, htrivM⟩ := hM
  obtain ⟨ιN, V, hV, htrivN⟩ := hN
  refine ⟨ιM × ιN, fun p => U p.1 ⊓ V p.2, ?_, fun p => ?_⟩
  · apply le_antisymm le_top
    rw [← hU]
    refine iSup_le fun i => ?_
    rw [← inf_top_eq (U i), ← hV, inf_iSup_eq]
    exact iSup_le fun j => le_iSup (fun p : ιM × ιN => U p.1 ⊓ V p.2) (i, j)
  · obtain ⟨eM⟩ := htrivM p.1
    obtain ⟨eN⟩ := htrivN p.2
    obtain ⟨eT⟩ := nonempty_tensorObj_unit_iso (unitObj ↑(U p.1 ⊓ V p.2))
    obtain ⟨ePb⟩ := nonempty_pullback_tensorObj_of_isOpenImmersion (U p.1 ⊓ V p.2).ι M N
    exact ⟨ePb ≪≫ tensorObjCongr (restrictTrivialization inf_le_left eM)
      (restrictTrivialization inf_le_right eN) ≪≫ eT⟩

end AlgebraicGeometry.Scheme.Modules
