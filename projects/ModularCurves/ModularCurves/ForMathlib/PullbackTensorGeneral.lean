/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import ModularCurves.Picard.Pic
import ModularCurves.ForMathlib.PullbackTensorMonoidal

/-!
# General pullback–tensor compatibility — decomposition skeleton (Route G)

`/develop --decompose` skeleton for **D-PresPB′-general** (board v10.98/v10.99): the general-`f`
pullback–tensor gate of the GME (2.16) Picard-functoriality chain. Route G (construction-grain):
give the presheaf pushforward its lax monoidal structure, get the oplax comparison `δ` on the
pullback by doctrinal adjunction, show `δ` is an iso on free-yoneda generators (on an Opens-site
the tensor of free-yonedas is the free-yoneda of the meet — the lattice miracle — and
`freeFunctorCompPullbackIso` matches the pullback side), and extend along free presentations by
two single-variable five-lemma passes in the abelian target. Payoff:
`functorMonoidalOfComp` ⟹ `(Modules.pullback f).Monoidal` ⟹ `Skeleton.monoidHom` ⟹
`Pic(f) : Pic X →* Pic Y`.

All leaves are stated `Nonempty`-wrapped (`Prop`s — no `sorryAx` in monoidal DATA, the v10.8
discipline; the data is built at execution time, each structure landing only when its leaf is
sorry-free). Full route adjudication, verbatim anchors and attack logs:
`.mathlib-quality/decomposition-pullback-monoidal-general.md`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Functor

namespace PresheafOfModules

section RestrictScalarsLax

variable {C : Type u₁} [Category.{v₁} C] {T₁ T₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
  (ψ : T₁ ⋙ forget₂ CommRingCat RingCat ⟶ T₂ ⋙ forget₂ CommRingCat RingCat)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaf B1a (unit component).** The unit comparison of the lax
monoidal structure on presheaf-level restriction of scalars, at a section: the ring map
`ψ.app U` itself, as a linear map into the restricted module. -/
noncomputable def restrictScalarsLaxεApp (U : Cᵒᵖ) :
    ((𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U) ⟶
      ((restrictScalars ψ).obj
        (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)))).obj U :=
  ModuleCat.ofHom
    (X := (𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U)
    (Y := ((restrictScalars ψ).obj
      (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)))).obj U)
    { toFun := fun x => (ψ.app U).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => (ψ.app U).hom.map_mul r x }

@[simp]
lemma restrictScalarsLaxεApp_apply (U : Cᵒᵖ)
    (x : ((𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))).obj U)) :
    restrictScalarsLaxεApp ψ U x = (ψ.app U).hom x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaf B1a (tensorator component).** The tensorator of the lax
monoidal structure on presheaf-level restriction of scalars, at a section:
`x ⊗ₜ y ↦ x ⊗ₜ y` from the tensor over the downstairs ring to the (restricted) tensor over
the upstairs ring (`TensorProduct.mapOfCompatibleSMul` — the lax direction needs no
bijectivity: the downstairs action slides in the upstairs tensor because it factors
through `ψ`). -/
noncomputable def restrictScalarsLaxμApp
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    (((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U) ⟶
      (((restrictScalars ψ).obj (P ⊗ Q)).obj U) := by
  letI : Module ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    Module.compHom _ ((ψ.app U).hom)
  letI : Module ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(Q.obj U) :=
    Module.compHom _ ((ψ.app U).hom)
  letI : Algebra ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) := ((ψ.app U).hom).toAlgebra
  haveI : IsScalarTower ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun r s m => mul_smul ((ψ.app U).hom r) s m⟩
  haveI : IsScalarTower ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(Q.obj U) :=
    ⟨fun r s n => mul_smul ((ψ.app U).hom r) s n⟩
  haveI : SMulCommClass ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun s r m => by
      show s • (ψ.app U).hom r • m = (ψ.app U).hom r • s • m
      rw [smul_comm]⟩
  haveI : SMulCommClass ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) :=
    ⟨fun r r' m => by
      show (ψ.app U).hom r • (ψ.app U).hom r' • m = (ψ.app U).hom r' • (ψ.app U).hom r • m
      rw [smul_comm]⟩
  exact ModuleCat.ofHom
    (X := (((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U))
    (Y := (((restrictScalars ψ).obj (P ⊗ Q)).obj U))
    (TensorProduct.mapOfCompatibleSMul ↑((T₂ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U)
      ↑((T₁ ⋙ forget₂ CommRingCat RingCat).obj U) ↑(P.obj U) ↑(Q.obj U))

@[simp]
lemma restrictScalarsLaxμApp_tmul
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (p : ↑(((restrictScalars ψ).obj P).obj U)) (q : ↑(((restrictScalars ψ).obj Q).obj U)) :
    restrictScalarsLaxμApp ψ P Q U (p ⊗ₜ q) =
      (p ⊗ₜ q : ↑(((restrictScalars ψ).obj (P ⊗ Q)).obj U)) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaf B1a (unit).** The unit comparison as a morphism of presheaves
of modules; naturality is the naturality of `ψ`. -/
noncomputable def restrictScalarsLaxε :
    (𝟙_ (PresheafOfModules.{u} (T₁ ⋙ forget₂ CommRingCat RingCat))) ⟶
      (restrictScalars ψ).obj
        (𝟙_ (PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat))) where
  app U := restrictScalarsLaxεApp ψ U
  naturality {U V} f := by
    ext
    simp [restrictScalarsLaxεApp]
    have h := RingHom.congr_fun (congrArg RingCat.Hom.hom (ψ.naturality f)) 1
    simp only [RingCat.hom_comp, RingHom.comp_apply] at h
    exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaf B1a (tensorator).** The tensorator as a morphism of
presheaves of modules; naturality is a `tmul`-chase (all components are `x ⊗ₜ y ↦ x ⊗ₜ y`). -/
noncomputable def restrictScalarsLaxμ
    (P Q : PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) :
    (restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q ⟶
      (restrictScalars ψ).obj (P ⊗ Q) where
  app U := restrictScalarsLaxμApp ψ P Q U
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext (fun p q => by
    erw [Monoidal.tensorObj_map_tmul])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaf B1a.** Presheaf-level restriction of scalars along an
arbitrary morphism of `CommRingCat`-valued ring presheaves is lax monoidal (sectionwise
`x ⊗ₜ y ↦ x ⊗ₜ y`; no iso hypothesis). -/
noncomputable def restrictScalarsLaxMonoidal : (restrictScalars ψ).LaxMonoidal where
  ε := restrictScalarsLaxε ψ
  μ P Q := restrictScalarsLaxμ ψ P Q
  μ_natural_left {P P'} f Q := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl
  μ_natural_right {Q Q'} P f := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    rfl
  associativity P Q R' := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext₃' (fun p q r => ?_)
    rfl
  left_unitality P := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun r p => ?_)
    rfl
  right_unitality P := by
    ext1 U
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p r => ?_)
    rfl

end RestrictScalarsLax

section LaxPushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pushforward, spelled as its definitional factorization `pushforward₀ ⋙
restrictScalars` (the spelling at which both factors carry their lax monoidal structures
natively — mathlib's `pushforward₀OfCommRingCat.Monoidal` and our
`restrictScalarsLaxMonoidal`). Componentwise-identity isomorphic to `pushforward φ`. -/
noncomputable def pushforwardFactored :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) :=
  pushforward₀OfCommRingCat F R ⋙
    restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison of the pushforward with its factored spelling (componentwise the
identity). -/
noncomputable def pushforwardIsoFactored :
    pushforward.{u} φ ≅ pushforwardFactored φ :=
  NatIso.ofComponents (fun P => Iso.refl _) (fun f => by simp; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaf B1 (lax structure on the factored pushforward).** -/
noncomputable def pushforwardFactoredLaxMonoidal : (pushforwardFactored φ).LaxMonoidal :=
  letI : (restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal :=
    restrictScalarsLaxMonoidal (T₂ := F.op ⋙ R) φ
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙
    restrictScalars (R' := (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[D-PresPB′-general], leaves B1+B2 (fused milestone).** The presheaf pullback along an
arbitrary ring comparison carries an oplax monoidal structure: transport the
pullback–pushforward adjunction to the factored spelling of the pushforward
(`Adjunction.ofNatIsoRight` along the componentwise-identity iso), where the lax structure
lives natively, and apply doctrinal adjunction (`Adjunction.leftAdjointOplaxMonoidal`).
Its `δ_{P,Q} : f^*ᵖ(P⊗Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` is the comparison map whose sheafified
invertibility is the remaining content (leaves G1/G3). -/
theorem nonempty_pullback_oplaxMonoidal [(pushforward.{u} φ).IsRightAdjoint] :
    Nonempty ((pullback.{u} φ).OplaxMonoidal) := by
  letI := pushforwardFactoredLaxMonoidal φ
  exact ⟨((pullbackPushforwardAdjunction.{u} φ).ofNatIsoRight
    (pushforwardIsoFactored φ)).leftAdjointOplaxMonoidal⟩

end LaxPushforward

section FreeYonedaTensor

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **[D-PresPB′-general], leaf G1 (the lattice miracle).** On the Opens-site of a scheme, the
presheaf tensor of two free-yoneda presheaves of modules is the free-yoneda of the meet:
pointwise, `Hom(V,U₁) × Hom(V,U₂) = [V ≤ U₁ ⊓ U₂]` (a meet-semilattice has representable
products of representables), and the free-module functor sends products of types to tensor
products of free modules (`finsuppTensorFinsupp`-style). Together with mathlib's
`freeFunctorCompPullbackIso` this makes the oplax comparison `δ` an isomorphism on free-yoneda
pairs — before sheafifying. -/
theorem nonempty_freeYoneda_tensor_iso (U₁ U₂ : X.Opens) :
    Nonempty (((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
        (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂) :
          PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (U₁ ⊓ U₂))) := by
  sorry

end FreeYonedaTensor

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **[D-PresPB′-general], payoff packaging (leaves G3 + A).** The pullback of sheaves of
modules along an arbitrary morphism of schemes is a monoidal functor for the (v10.97)
localized-monoidal structures: the objectwise content is the general-`f` sheafified
pullback–tensor comparison (`nonempty_sheafify_presheafPullback_tensor`, extended from the
free-yoneda generators by two single-variable presentation passes in the abelian
`SheafOfModules`), packaged through `functorMonoidalOfComp` with the `Lifting` instance
`sheafificationCompPullback`. Consumer: `Skeleton.monoidHom` then gives
`Pic(f) : Pic X →* Pic Y` — the GME (2.16) Picard functor. -/
theorem nonempty_pullback_monoidal (f : Y ⟶ X) :
    letI := Modules.monoidalCategory X
    letI := Modules.monoidalCategory Y
    Nonempty ((Modules.pullback f).Monoidal) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
