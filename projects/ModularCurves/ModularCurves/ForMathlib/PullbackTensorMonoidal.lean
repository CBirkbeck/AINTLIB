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
# Strong monoidality of the sheaf-of-modules pullback — decomposition skeleton

`/develop --decompose` skeleton for the AINTLIB ModularCurves stream leaf **[PIC-P1b-MONO]**
(board v10.77): the strong monoidality of the sheaf-of-modules pullback,
`f^*(M ⊗ N) ≅ f^* M ⊗ f^* N`, which gates `nonempty_pullback_tensorObj` in
`ModularCurves/Picard/InvertibleSheaf.lean` (and, downstream, the whole Pic group law).

**Route D (direct)** — chosen adversarially over route M (mates on a `SheafOfModules`
monoidal category, which is *out*: mathlib has no `SheafOfModules/Monoidal.lean`; the
sheaf-level tensor `tensorObj := sheafify(M.val ⊗ N.val)` is this project's own
construction, so there is no `MonoidalCategory (SheafOfModules R)` for
`leftAdjointOplaxMonoidal` to consume without first building the entire group-law layer
this leaf gates). Route D assembles, at the sheaf level:

* `SheafOfModules.sheafificationCompPullback` (mathlib): `sh_S ⋙ f^* ≅ f^*ᵖ ⋙ sh_R`,
  applied at `M.val ⊗ N.val`, gives `f^*(M ⊗ N) ≅ sh_R(f^*ᵖ(M.val ⊗ N.val))`.
* `SheafOfModules.pullbackIso` (mathlib): `f^* ≅ forget ⋙ f^*ᵖ ⋙ sh_R`, giving
  `(f^* M).val ≅ (sh_R(f^*ᵖ M.val)).val`, so
  `f^* M ⊗ f^* N ≅ sh_R((sh_R(f^*ᵖ M.val)).val ⊗ (sh_R(f^*ᵖ N.val)).val)`.
* `nonempty_sheafify_tensor_idem` below (**this project's GAP1-W-MONO leaf**): collapses
  the double sheafification, `sh_R(sh_R(A).val ⊗ sh_R(B).val) ≅ sh_R(A ⊗ B)`.
* `nonempty_sheafify_presheafPullback_tensor` below (**the one genuinely new leaf, D-PresPB′**):
  `sh_R(f^*ᵖ(P ⊗ Q)) ≅ sh_R(f^*ᵖ P ⊗ f^*ᵖ Q)` — the presheaf pullback commutes with the
  tensor *after sheafification*. NOTE (adversarial): the presheaf pullback is **not** strong
  monoidal for general `f` at the presheaf level (`pullback φ := (pushforward φ).leftAdjoint`
  hides an inverse-image left-Kan-extension along the site functor, which does not commute
  with the presheaf tensor); the comparison map is only a *stalkwise* iso, hence *locally
  bijective*, hence inverted by `sh_R`. So the sheafified form here is the correct true
  statement, provable by the same `sheafificationW`-membership technology as D-Idem.

Both new leaves stated `sorry` (skeleton only — no tickets; see
`.mathlib-quality/decomposition-pullback-monoidal.md`). The top assembly target
`nonempty_pullback_tensorObj` already lives (sorried) in `Picard/InvertibleSheaf.lean`.
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
                (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj B).val)) := by
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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
  naturality {U V} i :=
    ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
      ((congrArg (fun g => (forget₂ CommRingCat RingCat).map g)
        (f.appIso_inv_naturality i)).trans
        ((forget₂ CommRingCat RingCat).map_comp _ _))

instance (f : Y ⟶ X) [IsOpenImmersion f] (U : (Y.Opens)ᵒᵖ) :
    IsIso ((restrictRingHom f).app U) :=
  inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map ((f.appIso U.unop).inv)))

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
  have hmem : PresheafOfModules.sheafificationW (𝟙 Y.ringCatSheaf.obj)
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


/-- **[PIC-P1b-MONO], leaf D-PresPB′ — the one genuinely new leaf (refined, general `f`).**
The presheaf pullback commutes with the presheaf tensor *after sheafification*:
`sh_Y(f^*ᵖ(P ⊗ Q)) ≅ sh_Y(f^*ᵖ P ⊗ f^*ᵖ Q)`, where `f^*ᵖ := PresheafOfModules.pullback
f.toRingCatSheafHom.hom`. The un-sheafified comparison `f^*ᵖ(P⊗Q) → f^*ᵖP ⊗ f^*ᵖQ` (the
oplax structure map of the pullback, whose lax partner comes from `restrictScalars`) is a
*stalkwise* isomorphism — the stalk of an inverse image is the stalk at the image point and
tensor commutes with stalks — hence locally bijective, hence inverted by `sh_Y`. This is the
step that would be *false* if stated at the presheaf level for general `f`. `Nonempty`-wrapped. -/
theorem nonempty_sheafify_presheafPullback_tensor (f : Y ⟶ X) (P Q : X.PresheafOfModules) :
    Nonempty ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj (P ⊗ Q)) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj P ⊗
          (PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj Q)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
