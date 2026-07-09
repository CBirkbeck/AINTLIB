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
    (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
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
  restrictScalarsTensorObjIso φ
      ((pushforward₀OfCommRingCat F R).obj P) ((pushforward₀OfCommRingCat F R).obj Q) ≪≫
    (restrictScalars φ).mapIso
      (Functor.Monoidal.μIso (pushforward₀OfCommRingCat F R) P Q)

end PushforwardTensor

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

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
