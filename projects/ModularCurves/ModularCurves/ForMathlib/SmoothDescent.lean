/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Smoothness descends along surjective étale precomposition (Stacks 02KM)

The AINTLIB ModularCurves [YF-QSM] development: if `π : X ⟶ Y` is étale and surjective
and `π ≫ f` is smooth, then `f` is smooth — KM 4.7.1's implicit quotient step ("smooth is
étale-local on the source"). Source of record: Stacks 02KM (Descent, Lemma 35.14.4, smooth
column, étale `π` specializing via étale ⟹ smooth), whose proof combines

* Stacks 02KL (Descent 35.14.3; EGA IV 17.7.5): locally-of-finite-presentation descends
  along a surjective flat locally-finitely-presented precomposition;
* Stacks 02K5 (Morphisms 29.35.19): given (1) `π` surjective smooth, (2) `π ≫ f` smooth,
  (3) `f` locally of finite presentation, then `f` is smooth — via flatness of `f`
  (Morphisms 29.26.13) and the relative-cotangent rank bookkeeping
  (29.35.12/29.35.16/29.29.2/29.35.14(2)).

mathlib (pin 11b908e5cdd9) has the fpqc **base**-descent of smoothness
(`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`) but no source-locality:
`MorphismProperty.HasOfPrecompProperty @Smooth _` does not exist, nor do the
scheme-level right-cancellations for `Flat`/`LocallyOfFinitePresentation`. This file
stages the decomposition with the Stacks locators; the module-theoretic core of the
flatness leaf (29.26.13) is proven below, and the remaining leaves are registered
work-in-progress (board: STREAM-YFULL [YF-QSM], v10.51/v10.55).

## Main results

* `Module.Flat.of_comp_of_faithfullyFlat`: for `C ⟶ B ⟶ A` with `A` faithfully flat
  over `B` and flat over `C`, the ring `B` is flat over `C` — the module core of
  Stacks 29.26.13 (also Stacks 05UT-adjacent).
* `AlgebraicGeometry.Flat.of_precomp_of_surjective` (WIP): scheme form of 29.26.13.
* `AlgebraicGeometry.LocallyOfFinitePresentation.of_precomp_of_surjective` (WIP):
  Stacks 02KL.
* `AlgebraicGeometry.Smooth.of_precomp_etale_of_surjective` (WIP): the target, Stacks
  02KM at étale generality.
-/

universe u

open TensorProduct

section ModuleCore

variable (C B A : Type u) [CommRing C] [CommRing B] [CommRing A]
variable [Algebra C B] [Algebra B A] [Algebra C A] [IsScalarTower C B A]

/-- **Flatness right-cancels along a faithfully flat step** (module core of Stacks
29.26.13 / EGA IV 2.2.11-type sorites): if `A` is faithfully flat over `B` and the
composite `C → B → A` is flat, then `B` is flat over `C`. The proof reflects
injectivity of `- ⊗[C] B` through the faithfully flat `- ⊗[B] A`, transporting along
`A ⊗[B] (B ⊗[C] N) ≃ A ⊗[C] N`. -/
theorem Module.Flat.of_comp_of_faithfullyFlat
    [Module.FaithfullyFlat B A] [Module.Flat C A] : Module.Flat C B := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro Q _ _ S
  set f : S →ₗ[C] Q := S.subtype with hf'
  have hf : Function.Injective f := Subtype.val_injective
  set g : B ⊗[C] S →ₗ[B] B ⊗[C] Q :=
    AlgebraTensorModule.map (LinearMap.id : B →ₗ[B] B) f with hg
  suffices hInj : Function.Injective g by
    have hfun : ⇑(f.lTensor B) = ⇑g := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b p => simp [hg]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hfun]
    exact hInj
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B A g]
  have hA : Function.Injective (f.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hsq : ∀ x, (AlgebraTensorModule.cancelBaseChange C B B A Q) ((g.lTensor A) x) =
      (f.lTensor A) ((AlgebraTensorModule.cancelBaseChange C B B A S) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b p => simp [hg]
      | add y₁ y₂ h₁ h₂ =>
        simp only [tmul_add, map_add] at h₁ h₂ ⊢
        rw [h₁, h₂]
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add] at h₁ h₂ ⊢
      rw [h₁, h₂]
  intro x y hxy
  apply (AlgebraTensorModule.cancelBaseChange C B B A S).injective
  apply hA
  rw [← hsq, ← hsq, hxy]

end ModuleCore

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y Z : Scheme.{u}}

/-- **(Stacks 02KL = Descent 35.14.3; EGA IV 17.7.5 (i))** Locally-of-finite-presentation
descends along a surjective, flat, locally-finitely-presented precomposition: if
`π ≫ f` is locally of finite presentation with `π` surjective flat lfp, so is `f`.
Stacks proof route: reduce to affine `Z`, `Y` (lfp is Zariski-local on source and
target); `π` flat lfp is open, `Y` quasi-compact, so finitely many affine opens
`X_i ⊆ X` have `Y = ⋃ π(X_i)`; replace `X` by `⊔ X_i` (affine); conclude by the affine
case Descent 35.14.1, whose algebra content is the finite-presentation sorites over a
faithfully flat finitely-presented cover. WIP leaf of [YF-QSM].

**EXECUTION-READY REDUCTION (NEW-GH, scoped v10.75 — next-session first act).** Confirmed:
mathlib has NO precomp/source-descent shortcut (the `DescendsAlong _ (@Surjective ⊓ @Flat
⊓ @QuasiCompact)` instances of `LocalFlatDescent.lean` are BASE-CHANGE descent — covers of
the target — the wrong direction; no `HasOfPrecompProperty` for lfp). Recipe:
1. `rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]`; `rintro U V e`
   with `U : Z.affineOpens`, `V : Y.affineOpens`, `e : V.1 ≤ f ⁻¹ᵁ U.1`. Goal:
   `RingHom.FinitePresentation (f.appLE U.1 V.1 e).hom` — set `R := Γ(U)`, `S := Γ(V)`.
2. Build ONE faithfully-flat FP affine `W ⟶ V` from `π`: over the affine `V`, `π` restricts
   to a flat-lfp-surjective morphism; `π` is an open map (flat + lfp), so finitely many
   affine opens `W_j ⊆ X` of `π⁻¹ᵁ V.1` have images covering the quasi-compact `V`; set
   `W := ∐_{finite} W_j` (affine — `isAffineOpen_opensRange (Sigma.desc …)`, Limits.lean:668
   pattern) with `T := Γ(W) = ∏ Γ(W_j)`.
3. `S → T` is faithfully flat + FP: `flat_and_surjective_iff_faithfullyFlat_of_isAffine`
   (Flat.lean:163) — each `W_j → V` flat FP, jointly surjective ⟹ `∐ W_j → V` faithfully
   flat FP.
4. `R → T` is FP: it is `R → S → T` `= (π ≫ f)`'s chart map, FP from `h`
   (`Scheme.Hom.appLE_comp_appLE` bookkeeping).
5. `R → S` FP by `RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`
   (RingTheory/Finiteness/Descent.lean:128: `R→S→T`, `S→T` faithfully flat, `R→T` FP ⟹
   `R→S` FP). ∎  The ~100-line work is step 2's finite-affine-subcover + coproduct. -/
theorem LocallyOfFinitePresentation.of_precomp_of_surjective (π : X ⟶ Y) (f : Y ⟶ Z)
    [Flat π] [LocallyOfFinitePresentation π] (hπ : Function.Surjective π.base)
    (h : LocallyOfFinitePresentation (π ≫ f)) : LocallyOfFinitePresentation f := by
  sorry

/-- **(Stacks 29.26.13, scheme form)** Flatness descends along a surjective flat
precomposition: if `π ≫ f` is flat and `π` is surjective and flat, then `f` is flat.
Module core: `Module.Flat.of_comp_of_faithfullyFlat` above (pointwise over affine
charts, a flat cover of a local ring is faithfully flat). WIP leaf of [YF-QSM]. -/
theorem Flat.of_precomp_of_surjective (π : X ⟶ Y) (f : Y ⟶ Z) [Flat π]
    (hπ : Function.Surjective π.base) (h : Flat (π ≫ f)) : Flat f := by
  refine Flat.of_stalkMap f fun y => ?_
  obtain ⟨x, rfl⟩ := hπ y
  have h1 : ((π ≫ f).stalkMap x).hom.Flat := Flat.stalkMap (π ≫ f) x
  have h2 : (π.stalkMap x).hom.Flat := Flat.stalkMap π x
  have hcomp : (π ≫ f).stalkMap x = f.stalkMap (π.base x) ≫ π.stalkMap x :=
    Scheme.Hom.stalkMap_comp π f x
  letI : Algebra ↑(Z.presheaf.stalk (f.base (π.base x))) ↑(Y.presheaf.stalk (π.base x)) :=
    (f.stalkMap (π.base x)).hom.toAlgebra
  letI : Algebra ↑(Y.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) :=
    (π.stalkMap x).hom.toAlgebra
  letI : Algebra ↑(Z.presheaf.stalk (f.base (π.base x))) ↑(X.presheaf.stalk x) :=
    ((π ≫ f).stalkMap x).hom.toAlgebra
  haveI : IsScalarTower ↑(Z.presheaf.stalk (f.base (π.base x)))
      ↑(Y.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      show ((π ≫ f).stalkMap x).hom =
        ((π.stalkMap x).hom).comp ((f.stalkMap (π.base x)).hom)
      rw [hcomp]
      rfl)
  haveI : Module.Flat ↑(Y.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) := h2
  haveI : IsLocalHom (algebraMap ↑(Y.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
  haveI : Module.FaithfullyFlat ↑(Y.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat ↑(Z.presheaf.stalk (f.base (π.base x))) ↑(X.presheaf.stalk x) := h1
  exact Module.Flat.of_comp_of_faithfullyFlat ↑(Z.presheaf.stalk (f.base (π.base x)))
    ↑(Y.presheaf.stalk (π.base x)) ↑(X.presheaf.stalk x)

/-- **(Stacks 02KM, smooth column, étale case — the [YF-QSM] target)** Smoothness
descends along a surjective étale precomposition: if `π : X ⟶ Y` is étale and
surjective and `π ≫ f` is smooth, then `f` is smooth ("smooth is étale-local on the
source"; KM 4.7.1's quotient step). Stacks assembly: `f` is lfp by
`LocallyOfFinitePresentation.of_precomp_of_surjective` (02KL) and flat by
`Flat.of_precomp_of_surjective` (29.26.13); the remaining content is Stacks 02K5's
fibrewise conclusion, which at étale `π` degenerates (relative dimension `0`:
`π^*Ω_{Y/Z} ≅ Ω_{X/Z}`). mathlib-side route for the last step: pointwise via
`Algebra.smoothLocus_eq_univ_iff` + `Algebra.IsSmoothAt`, reflecting formal smoothness
of localizations along the faithfully flat formally étale local-ring maps
`𝒪_{Y,y} → 𝒪_{X,x}` (mathlib has the base-descent
`Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat` and the localized
`H1Cotangent` machinery of `Mathlib.RingTheory.Etale.Kaehler`; the formally-étale-step
transfer is the open piece). WIP milestone of [YF-QSM]. -/
theorem Smooth.of_precomp_etale_of_surjective (π : X ⟶ Y) (f : Y ⟶ Z) [Etale π]
    (hπ : Function.Surjective π.base) (h : Smooth (π ≫ f)) : Smooth f := by
  sorry

end AlgebraicGeometry
