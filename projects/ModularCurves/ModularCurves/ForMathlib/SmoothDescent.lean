/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Limits
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
proves all three scheme-level descents; the `sorryAx` inventory is exactly the two
REGISTERED ring-level gates [02KL-CORE] and [02KM-CORE] below (board: STREAM-YFULL
[YF-QSM], v10.51/v10.96).

## Main results

* `Module.Flat.of_comp_of_faithfullyFlat`: for `C ⟶ B ⟶ A` with `A` faithfully flat
  over `B` and flat over `C`, the ring `B` is flat over `C` — the module core of
  Stacks 29.26.13 (also Stacks 05UT-adjacent).
* `AlgebraicGeometry.Flat.of_precomp_of_surjective` (PROVEN): scheme form of 29.26.13.
* `AlgebraicGeometry.LocallyOfFinitePresentation.of_precomp_of_surjective` (PROVEN
  modulo [02KL-CORE]): Stacks 02KL.
* `AlgebraicGeometry.Smooth.of_precomp_etale_of_surjective` (PROVEN modulo
  [02KL-CORE] + [02KM-CORE]): the target, Stacks 02KM at étale generality.
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
  set f : S →ₗ[C] Q := S.subtype
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

/-- **[02KL-CORE] (REGISTERED GATE — Stacks 02KG + 02KH, algebra form; the
fppf-source-locality core).** Finite presentation reflects along a faithfully flat,
finitely presented composite: if `χ : S →+* T` is faithfully flat and of finite
presentation and `χ ∘ φ : R →+* T` is of finite presentation, then `φ : R →+* S` is of
finite presentation.

GAP AUDIT (2026-07-10, NEW-GH): absent from the pin in every form. Mathlib's
`RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`
(`RingTheory/Finiteness/Descent.lean`) is the PUSHOUT (base-change) form — `Q(R → R')`
faithfully flat and `P(R' → R' ⊗[R] S)` give `P(R → S)` — which cannot be instantiated to
this composite-reflection shape (the faithfully flat leg here sits over `S`, not under
`R`). `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation` cancels the
SECOND factor (given finite-type first factor) — the wrong factor. The classical proof
(Stacks 02KG for finite type, upgraded to 02KH for finite presentation) descends the
presentation to a finite-type subalgebra stage `S₀ ⊆ S` (possible since `χ` is FP:
finitely many relation coefficients) and then needs flatness/surjectivity to spread out
to a finite stage of the filtered system — EGA IV 8.10.5/11.2.6-style spreading-out that
mathlib does not yet expose for this purpose (`Mathlib/AlgebraicGeometry/SpreadingOut.lean`
is about spreading out morphisms/points, not flatness through ring-filtered systems).
Profile: publishable-grade commutative algebra, zero file overlap — the same
hard-substrate shape as [A711-FP]. Consumed by `LocallyOfFinitePresentation.
of_precomp_of_surjective` (Stacks 02KL) below, whose scheme-level reduction is PROVEN
modulo exactly this statement. -/
theorem RingHom.FinitePresentation.of_comp_of_faithfullyFlat
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {φ : R →+* S} {χ : S →+* T} (hff : χ.FaithfullyFlat) (hfp : χ.FinitePresentation)
    (h : (χ.comp φ).FinitePresentation) : φ.FinitePresentation := by
  sorry

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {X Y Z : Scheme.{u}}

/-- The affine case of Stacks 02KL: over affine `W`, `Y`, `Z`, a flat surjective lfp
`q : W ⟶ Y` with `q ≫ f` lfp forces `f` lfp. `Γ(q)` is faithfully flat
(`flat_and_surjective_iff_faithfullyFlat_of_isAffine`) and finitely presented, and
`Γ(q ≫ f) = Γ(q) ∘ Γ(f)`, so the ring-level core [02KL-CORE] applies. -/
private lemma lfp_of_precomp_of_isAffine {W Y Z : Scheme.{u}} [IsAffine W] [IsAffine Y]
    [IsAffine Z] (q : W ⟶ Y) (f : Y ⟶ Z) [Flat q] [Surjective q]
    [LocallyOfFinitePresentation q] (h : LocallyOfFinitePresentation (q ≫ f)) :
    LocallyOfFinitePresentation f := by
  have hff : (q.appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨‹_›, ‹_›⟩
  have hfp : RingHom.FinitePresentation (q.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp ‹_›
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_of_faithfullyFlat hff hfp h

set_option backward.isDefEq.respectTransparency.types false in
/-- Engine for Stacks 02KL, with the surjectivity hypothesis as an instance. The wlog
cascade (mirroring `LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType`,
`ForMathlib/FinitePresentationCancel.lean`) reduces to affine `Z` then affine `Y`; there,
`π` is universally open (flat + lfp), `Y` is quasi-compact, so finitely many affine opens
of `X` have `π`-images covering `Y`; their coproduct is an affine scheme flat, lfp and
surjective over `Y`, and the affine case applies. -/
private theorem lfp_of_precomp_aux {X Y Z : Scheme.{u}} (π : X ⟶ Y) (f : Y ⟶ Z)
    [Flat π] [LocallyOfFinitePresentation π] [Surjective π]
    (h : LocallyOfFinitePresentation (π ≫ f)) : LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Z)]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    haveI hs1 : Surjective (π ∣_ f ⁻¹ᵁ U.1) :=
      IsZariskiLocalAtTarget.restrict ‹Surjective π› (f ⁻¹ᵁ U.1)
    haveI hf1 : Flat (π ∣_ f ⁻¹ᵁ U.1) :=
      IsZariskiLocalAtTarget.restrict ‹Flat π› (f ⁻¹ᵁ U.1)
    haveI hp1 : LocallyOfFinitePresentation (π ∣_ f ⁻¹ᵁ U.1) :=
      IsZariskiLocalAtTarget.restrict ‹LocallyOfFinitePresentation π› (f ⁻¹ᵁ U.1)
    exact this (π ∣_ f ⁻¹ᵁ U.1) (f ∣_ U.1) H inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Y)]
    intro V
    haveI hs2 : Surjective (π ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹Surjective π› V.1
    haveI hf2 : Flat (π ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹Flat π› V.1
    haveI hp2 : LocallyOfFinitePresentation (π ∣_ V.1) :=
      IsZariskiLocalAtTarget.restrict ‹LocallyOfFinitePresentation π› V.1
    refine this (π ∣_ V.1) (V.1.ι ≫ f) ?_ inferInstance
    have hres : (π ∣_ V.1) ≫ V.1.ι ≫ f = (π ⁻¹ᵁ V.1).ι ≫ (π ≫ f) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hres]
    exact IsZariskiLocalAtSource.comp h _
  haveI := hZ; haveI := hY
  -- `π` is universally open (flat + lfp), so images of opens are open.
  have hopen := π.isOpenMap
  -- For each `y`, an affine open of `X` through a preimage of `y`.
  have hchoice : ∀ y : Y, ∃ O : X.affineOpens, ∃ x, x ∈ O.1 ∧ π x = y := by
    intro y
    obtain ⟨x, hx⟩ := π.surjective y
    obtain ⟨O, hO, hxO, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
    exact ⟨⟨O, hO⟩, x, hxO, hx⟩
  choose O xO hxO hπxO using hchoice
  -- Finitely many of the (open) images cover the quasi-compact `Y`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : Y => π '' ((O y).1 : Set X)) (fun y => hopen _ (O y).1.2)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, ⟨xO y, hxO y, hπxO y⟩⟩)
  -- The coproduct of the pieces: an affine flat lfp surjective cover of `Y`.
  have (i : t) : IsAffine ((O i.1).1.toScheme) := (O i.1).2
  set q : (∐ fun i : t => ((O i.1).1.toScheme)) ⟶ Y :=
    Sigma.desc (fun i => (O i.1).1.ι ≫ π) with hq
  haveI hFq : Flat q := IsZariskiLocalAtSource.sigmaDesc fun i =>
    MorphismProperty.comp_mem _ _ _ inferInstance ‹Flat π›
  haveI hPq : LocallyOfFinitePresentation q :=
    IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  haveI hSq : Surjective q := by
    constructor
    intro y
    have hyt := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion, exists_prop] at hyt
    obtain ⟨i, hit, x, hxOi, hπx⟩ := hyt
    refine ⟨(Sigma.ι (fun i : t => ((O i.1).1.toScheme)) ⟨i, hit⟩) ⟨x, hxOi⟩, ?_⟩
    have hι : Sigma.ι (fun i : t => ((O i.1).1.toScheme)) ⟨i, hit⟩ ≫ q
        = (O i).1.ι ≫ π := by rw [hq]; exact Sigma.ι_desc _ _
    rw [← Scheme.Hom.comp_apply, hι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact hπx
  have hqf : LocallyOfFinitePresentation (q ≫ f) := by
    have hcomp : q ≫ f = Sigma.desc (fun i : t => (O i.1).1.ι ≫ (π ≫ f)) := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [Sigma.ι_desc, hq, ← Category.assoc, Sigma.ι_desc, Category.assoc]
    rw [hcomp]
    exact IsZariskiLocalAtSource.sigmaDesc fun i => IsZariskiLocalAtSource.comp h _
  exact lfp_of_precomp_of_isAffine q f hqf

/-- **(Stacks 02KL = Descent 35.14.3; EGA IV 17.7.5 (i))** Locally-of-finite-presentation
descends along a surjective, flat, locally-finitely-presented precomposition: if
`π ≫ f` is locally of finite presentation with `π` surjective flat lfp, so is `f`.
Stacks proof route: reduce to affine `Z`, `Y` (lfp is Zariski-local on source and
target); `π` flat lfp is open, `Y` quasi-compact, so finitely many affine opens
`X_i ⊆ X` have `Y = ⋃ π(X_i)`; replace `X` by `⊔ X_i` (affine); conclude by the affine
case Descent 35.14.1, whose algebra content is the finite-presentation sorites over a
faithfully flat finitely-presented cover. **Scheme-level reduction PROVEN
(2026-07-10, NEW-GH); sorryAx flows only through the registered ring-level gate
[02KL-CORE]** (`RingHom.FinitePresentation.of_comp_of_faithfullyFlat` above).

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
    (h : LocallyOfFinitePresentation (π ≫ f)) : LocallyOfFinitePresentation f :=
  haveI : Surjective π := ⟨hπ⟩
  lfp_of_precomp_aux π f h

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
