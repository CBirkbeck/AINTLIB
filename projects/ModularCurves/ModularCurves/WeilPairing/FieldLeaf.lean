/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMBilinear
import ModularCurves.WeilPairing.FieldComparisonBridge
import ModularCurves.WeilPairing.Basic
import ModularCurves.WeilPairing.OverRestrictionSquare
import ModularCurves.ForMathlib.PullbackTensorMonoidal
import HasseWeil.HasseBound.WeilPairing.Constancy

/-!
# The field leaf: comparing the KM pairing with the Silverman pairing (U5)

Per the validated sub-decomposition (`.mathlib-quality/decomposition-e4a-self.md`, U5
section): over a field the Katz–Mazur pairing value `torsionSplittingEval` and HasseWeil's
Silverman pairing `weilPairing` satisfy the *same* translation characterisation
(`τ_{P}^# g = e · g`) against divisor-matched function objects, so they agree; alternation
then imports from `HasseWeil.weilPairing_self`.

This file builds the comparison bottom-up:
* **L2a (this commit)** — the τ-relation for a *held* normalised splitting, extracted from
  the proof of `torsionSplittingEval_add` (`KMBilinear.lean`) as a standalone lemma:
  `τ_{P'}^# h_i = h_i · π^# h(P')`, over any base.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

-- the `(E.baseChange t).E`-vs-`pullback E.π t` semireducible wall (v4.33 idiom)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)
variable (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
variable (M : (pullback E.π t).Modules)
variable (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  (kappa E hsm t Q).val = toSkeleton M)
variable {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
variable (e : ∀ i, M.over (W i) ≅
  _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
variable (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
  sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))

/-- **(U5-L2a — the τ-relation for a held splitting, KM p. 89)** For any normalised splitting
`h` of the `[N]`-pulled transition cocycle and any `N`-torsion section `P'`,

  `τ_{P'}^# h_i = h_i · π^# h(P')`,

where `h(P') = torsionSplittingEval … P'`. Extracted verbatim from the proof of
`torsionSplittingEval_add` (`KMBilinear.lean`) so the field-level comparison can consume the
relation on a single chart. -/
theorem unitPullback_translateByPoint_eq_of_splitting
    (h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
      (mulByN E t N ⁻¹ᵁ W i))
    (hsplit : ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      Scheme.resUnit (inf_le_left : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W i) (h i) *
        (Scheme.resUnit (inf_le_right : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W j) (h j))⁻¹)
    (P' : (E.baseChange t).Point (𝟙 T)) (hP' : P' ∈ torsionPoints E t N) (i : ι) :
    unitPullback (translateByPoint E t P') (mulByN E t N ⁻¹ᵁ W i) (mulByN E t N ⁻¹ᵁ W i)
        (le_of_eq (preimage_translateByPoint_mulByN E t P' N hP' (W i)).symm) (h i) =
      h i * globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i)
        (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP') := by
  have hτle : ∀ i, mulByN E t N ⁻¹ᵁ W i ≤
      translateByPoint E t P' ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := fun i =>
    le_of_eq (preimage_translateByPoint_mulByN E t P' N hP' (W i)).symm
  have hτinf : ∀ i j, mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
      translateByPoint E t P' ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j) := fun i j =>
    le_of_eq (preimage_translateByPoint_mulByN E t P' N hP' (W i ⊓ W j)).symm
  have hFeq : ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      unitPullback (mulByN E t N) (W i ⊓ W j)
        (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j)
        (Scheme.Hom.preimage_inf (mulByN E t N)).ge (transitionUnitOfCover M W e i j) :=
    fun i j => map_app_eq_unitPullback _ _ _
  have hτF : ∀ i j, unitPullback (translateByPoint E t P')
      (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j)
      (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j) (hτinf i j)
      (Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j)) =
      Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) := by
    intro i j
    rw [hFeq i j, unitPullback_unitPullback]
    exact unitPullback_congr (translateByPoint_comp_mulByN E t P' N hP') _ _ _ _ _
  have hzval : ((0 : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t) =
      baseChangeZero E.π E.zero E.zero_π t :=
    ((E.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hzτ : baseChangeZero E.π E.zero E.zero_π t ≫ translateByPoint E t P' =
      (P'.1 : T ⟶ pullback E.π t) := by
    rw [← hzval]
    exact (comp_translateByPoint E t P' 0).trans (congrArg Subtype.val (zero_add P'))
  have hC : ∀ i, sectionEval (baseChangeZero E.π E.zero E.zero_π t) (mulByN E t N ⁻¹ᵁ W i)
        (unitPullback (translateByPoint E t P') (mulByN E t N ⁻¹ᵁ W i)
          (mulByN E t N ⁻¹ᵁ W i) (hτle i) (h i)) =
      Scheme.resUnit (le_top : baseChangeZero E.π E.zero E.zero_π t ⁻¹ᵁ
          (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤)
        (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP') := by
    intro i
    have hP'le : baseChangeZero E.π E.zero E.zero_π t ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤
        (P'.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := by
      rw [← hzτ]
      exact Scheme.Hom.preimage_mono _ (hτle i)
    calc sectionEval (baseChangeZero E.π E.zero E.zero_π t) (mulByN E t N ⁻¹ᵁ W i)
          (unitPullback (translateByPoint E t P') (mulByN E t N ⁻¹ᵁ W i)
            (mulByN E t N ⁻¹ᵁ W i) (hτle i) (h i))
        = Scheme.resUnit
            (Scheme.Hom.preimage_mono (baseChangeZero E.π E.zero E.zero_π t) (hτle i))
            (sectionEval (baseChangeZero E.π E.zero E.zero_π t ≫ translateByPoint E t P')
              (mulByN E t N ⁻¹ᵁ W i) (h i)) := sectionEval_unitPullback _ _ _ _
      _ = Scheme.resUnit hP'le
            (sectionEval (P'.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i)) :=
          resUnit_sectionEval_congr hzτ (mulByN E t N ⁻¹ᵁ W i) (h i)
            (Scheme.Hom.preimage_mono (baseChangeZero E.π E.zero E.zero_π t) (hτle i)) hP'le
      _ = Scheme.resUnit hP'le (Scheme.resUnit
            (le_top : (P'.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤)
            (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP')) := by
          rw [resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP' h hn hsplit i]
      _ = _ := Scheme.resUnit_resUnit _ _ _
  have hkey := eq_mul_globalTwist_of_translate t
    E.toEllipticCurveGeom.universallyOConnected
    (baseChangeZero_snd E.π E.zero E.zero_π t)
    (fun i => mulByN E t N ⁻¹ᵁ W i)
    ((mulByN E t N).iSup_preimage_eq_top hW)
    (F := fun i j => Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
      (transitionUnitOfCover M W e i j))
    hn hsplit hτle hτinf hτF hC
  exact hkey i

/-! ## The generic-point germ push (U5-L2c) -/

section GermPush

/-- **(U5-L2c)** Pushing a `unitPullback` multiplicativity relation into the function field:
if `τ^#(u) = u · w` as sections over `V` (with `V ≤ τ⁻¹V`), then
`τ^♭(germ u) = germ u · germ w` in `K(X)`. -/
theorem functionFieldMap_germToFunctionField_of_unitPullback_eq
    {X : Scheme.{u}} [IrreducibleSpace X] (τ : X ⟶ X) [IsDominant τ]
    (V : X.Opens) [Nonempty V] (hle : V ≤ τ ⁻¹ᵁ V)
    (u : Γ(X, V)ˣ) (w : Γ(X, V))
    (hrel : ((unitPullback τ V V hle u : Γ(X, V)ˣ) : Γ(X, V)) = (u : Γ(X, V)) * w) :
    τ.functionFieldMap.hom (X.germToFunctionField V (u : Γ(X, V)))
      = X.germToFunctionField V (u : Γ(X, V)) * X.germToFunctionField V w := by
  haveI : Nonempty (τ ⁻¹ᵁ V : X.Opens) :=
    ⟨⟨genericPoint X, genericPoint_mem_preimage τ V⟩⟩
  have h1 : τ.functionFieldMap.hom (X.germToFunctionField V (u : Γ(X, V)))
      = X.presheaf.germ (τ ⁻¹ᵁ V) (genericPoint X) (genericPoint_mem_preimage τ V)
          (Scheme.Hom.app τ V (u : Γ(X, V))) :=
    functionFieldMap_germToFunctionField τ V (u : Γ(X, V))
  have h2 : X.germToFunctionField V ((unitPullback τ V V hle u : Γ(X, V)ˣ) : Γ(X, V))
      = X.presheaf.germ (τ ⁻¹ᵁ V) (genericPoint X) (genericPoint_mem_preimage τ V)
          (Scheme.Hom.app τ V (u : Γ(X, V))) := by
    show X.presheaf.germ V (genericPoint X) _
        (X.presheaf.map (homOfLE hle).op (Scheme.Hom.app τ V (u : Γ(X, V)))) = _
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) (genericPoint X) _ _
  rw [h1, ← h2, hrel, map_mul]

end GermPush

/-! ## The identity-base-change crossing (U5-L2b)

The KM apparatus lives on `pullback E.π t`; over a field the leaf statements live on the
curve itself. For `t = 𝟙 S` the first projection is an isomorphism, and it intertwines the
translation endomorphisms: `τ_{P'} ≫ fst = fst ≫ τ_x` for `x` the crossed point. The
monoid-hom input is the rigidity theorem `isMonHom_of_one_comp_eq'` (GIT Cor 6.4), which
applies since a field base is locally noetherian. -/

section IdentityBase

open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The first projection of the identity base change, as a morphism of `Over S`. -/
noncomputable def baseChangeIdFstOver : (E.baseChange (𝟙 S)).asOver ⟶ E.asOver :=
  Over.homMk (pullback.fst E.π (𝟙 S)) (by
    show pullback.fst E.π (𝟙 S) ≫ E.π = pullback.snd E.π (𝟙 S)
    rw [pullback.condition, Category.comp_id])

@[simp] theorem baseChangeIdFstOver_left :
    (baseChangeIdFstOver E).left = pullback.fst E.π (𝟙 S) := rfl

/-- The crossing is pointed: the base-changed zero section projects to the zero section. -/
theorem baseChangeIdFstOver_one :
    η[(E.baseChange (𝟙 S)).asOver] ≫ baseChangeIdFstOver E = η[E.asOver] := by
  apply Over.OverMorphism.ext
  show η[(E.baseChange (𝟙 S)).asOver].left ≫ pullback.fst E.π (𝟙 S) = η[E.asOver].left
  rw [(E.baseChange (𝟙 S)).one_eq_zero, E.one_eq_zero]
  show (𝟙_ (Over S)).hom ≫ (pullback.lift ((𝟙 S) ≫ E.zero) (𝟙 S) _ ≫ pullback.fst E.π (𝟙 S))
    = (𝟙_ (Over S)).hom ≫ E.zero
  rw [pullback.lift_fst, Category.id_comp]

/-- **(U5-L2b-i)** The identity-base-change projection is a homomorphism of group objects —
rigidity (`isMonHom_of_one_comp_eq'`, GIT Cor 6.4) applied to the pointed crossing. -/
theorem isMonHom_baseChangeIdFstOver [IsLocallyNoetherian S] [IsSeparated E.π] :
    IsMonHom (baseChangeIdFstOver E) := by
  haveI : IsProper (E.baseChange (𝟙 S)).asOver.hom :=
    inferInstanceAs (IsProper (E.baseChange (𝟙 S)).π)
  haveI : Smooth (E.baseChange (𝟙 S)).π :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := (E.baseChange (𝟙 S)).π)
  haveI : Flat (E.baseChange (𝟙 S)).asOver.hom :=
    inferInstanceAs (Flat (E.baseChange (𝟙 S)).π)
  haveI : IsSeparated E.asOver.hom := inferInstanceAs (IsSeparated E.π)
  exact
    { one_hom := baseChangeIdFstOver_one E
      mul_hom := isMonHom_of_one_comp_eq'
        (E.baseChange (𝟙 S)).toEllipticCurveGeom.universallyOConnected
        (baseChangeIdFstOver E) (baseChangeIdFstOver_one E) }

/-- **(U5-L2b-ii)** Translation intertwines with a pointed homomorphism of elliptic records:
`τ_x ≫ φ = φ ≫ τ_{φ(x)}`. Pure hom-group algebra from `translateBy = 𝟙 * constPt x`. -/
theorem translateBy_comp_of_isMonHom {E F : EllipticCurve S}
    (φ : E.asOver ⟶ F.asOver) [IsMonHom φ] (x : 𝟙_ (Over S) ⟶ E.asOver) :
    E.translateBy x ≫ φ = φ ≫ F.translateBy (x ≫ φ) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (E.asOver ⟶ F.asOver) := Hom.commGroup
  letI : CommGroup (F.asOver ⟶ F.asOver) := Hom.commGroup
  rw [E.translateBy_def x, F.translateBy_def (x ≫ φ)]
  have hpost := map_mul (IsMonHom.monoidHom φ E.asOver)
    (𝟙 E.asOver) (E.constPt x)
  simp only [IsMonHom.monoidHom_apply] at hpost
  rw [hpost, MonObj.comp_mul, Category.id_comp, Category.comp_id]
  congr 1
  show E.constPt x ≫ φ = φ ≫ F.constPt (x ≫ φ)
  rw [EllipticCurve.constPt, EllipticCurve.constPt,
    ← Category.assoc φ (toUnit F.asOver) (x ≫ φ),
    CartesianMonoidalCategory.toUnit_unique (φ ≫ toUnit F.asOver) (toUnit E.asOver),
    Category.assoc]

/-- **(U5-L2b-iii)** The `.left`-level crossing consumed by the bridge: `translateByPoint`
on the identity base change projects to `translateBy` at the crossed section. -/
theorem translateByPoint_id_comp_fst [IsLocallyNoetherian S] [IsSeparated E.π]
    (P' : (E.baseChange (𝟙 S)).Point (𝟙 S)) :
    translateByPoint E (𝟙 S) P' ≫ pullback.fst E.π (𝟙 S)
      = pullback.fst E.π (𝟙 S)
        ≫ (E.translateBy (overPoint E (𝟙 S) P' ≫ baseChangeIdFstOver E)).left := by
  haveI := isMonHom_baseChangeIdFstOver E
  have h := translateBy_comp_of_isMonHom (baseChangeIdFstOver E) (overPoint E (𝟙 S) P')
  exact congrArg CategoryTheory.CommaMorphism.left h

end IdentityBase

/-! ## The field instantiation (U5-L2e)

Over `S := Spec K` with `t := 𝟙 S`, the KM apparatus lives on `pullback E.π (𝟙 S)`,
which the first projection identifies with the total curve. The τ-relation (L2a)
germ-pushes (L2c) into the function field of the pullback presentation. -/

section FieldInstantiation

variable {S : Scheme.{u}} (E : EllipticCurve S)
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]

/-- The pullback presentation over the identity inherits integrality through the
first-projection isomorphism. -/
theorem isIntegral_pullback_id [AlgebraicGeometry.IsIntegral E.E] :
    AlgebraicGeometry.IsIntegral (pullback E.π (𝟙 S)) :=
  AlgebraicGeometry.IsIntegral.of_isIso (inv (pullback.fst E.π (𝟙 S)))

/-- **(U5-L2e)** The τ-relation in the function field of the pullback presentation:
for a normalised splitting `h` of the pulled cocycle and an `N`-torsion section `P'`,
on any chart `V i` whose `[N]`-preimage is nonempty,

  `τ_{P'}^♭ (germ h_i) = germ h_i · germ (π^# h(P'))` in `K(pullback E.π (𝟙 S))`.

Assembly of L2a (`unitPullback_translateByPoint_eq_of_splitting`) and L2c
(`functionFieldMap_germToFunctionField_of_unitPullback_eq`). -/
theorem functionFieldMap_translateByPoint_germ [AlgebraicGeometry.IsIntegral E.E]
    (N : ℕ) (Q : (E.baseChange (𝟙 S)).Point (𝟙 S))
    (hQ : Q ∈ torsionPoints E (𝟙 S) N)
    (M : (pullback E.π (𝟙 S)).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π (𝟙 S))
      (kappa E hsm (𝟙 S) Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π (𝟙 S)).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π (𝟙 S)).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π (𝟙 S)) (W i ⊓ W j))
    (h : ∀ i, Γ(pullback E.π (𝟙 S), mulByN E (𝟙 S) N ⁻¹ᵁ W i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero E.π E.zero E.zero_π (𝟙 S))
      (mulByN E (𝟙 S) N ⁻¹ᵁ W i))
    (hsplit : ∀ i j, Units.map ((mulByN E (𝟙 S) N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      Scheme.resUnit (inf_le_left : mulByN E (𝟙 S) N ⁻¹ᵁ W i ⊓
          mulByN E (𝟙 S) N ⁻¹ᵁ W j ≤ mulByN E (𝟙 S) N ⁻¹ᵁ W i) (h i) *
        (Scheme.resUnit (inf_le_right : mulByN E (𝟙 S) N ⁻¹ᵁ W i ⊓
          mulByN E (𝟙 S) N ⁻¹ᵁ W j ≤ mulByN E (𝟙 S) N ⁻¹ᵁ W j) (h j))⁻¹)
    (P' : (E.baseChange (𝟙 S)).Point (𝟙 S)) (hP' : P' ∈ torsionPoints E (𝟙 S) N)
    [IsDominant (translateByPoint E (𝟙 S) P')]
    (i : ι) [Nonempty (mulByN E (𝟙 S) N ⁻¹ᵁ W i : (pullback E.π (𝟙 S)).Opens)] :
    haveI : AlgebraicGeometry.IsIntegral (pullback E.π (𝟙 S)) := isIntegral_pullback_id E
    (translateByPoint E (𝟙 S) P').functionFieldMap.hom
        ((pullback E.π (𝟙 S)).germToFunctionField (mulByN E (𝟙 S) N ⁻¹ᵁ W i)
          ((h i : Γ(pullback E.π (𝟙 S), mulByN E (𝟙 S) N ⁻¹ᵁ W i))))
      = (pullback E.π (𝟙 S)).germToFunctionField (mulByN E (𝟙 S) N ⁻¹ᵁ W i)
          ((h i : Γ(pullback E.π (𝟙 S), mulByN E (𝟙 S) N ⁻¹ᵁ W i)))
        * (pullback E.π (𝟙 S)).germToFunctionField (mulByN E (𝟙 S) N ⁻¹ᵁ W i)
          ((globalTwist (pullback.snd E.π (𝟙 S)) (mulByN E (𝟙 S) N ⁻¹ᵁ W i)
            (torsionSplittingEval E hsm (𝟙 S) N Q hQ M hM W hW e hnorm P' hP') :
              Γ(pullback E.π (𝟙 S), mulByN E (𝟙 S) N ⁻¹ᵁ W i))) := by
  haveI : AlgebraicGeometry.IsIntegral (pullback E.π (𝟙 S)) := isIntegral_pullback_id E
  refine functionFieldMap_germToFunctionField_of_unitPullback_eq
    (translateByPoint E (𝟙 S) P') (mulByN E (𝟙 S) N ⁻¹ᵁ W i)
    (le_of_eq (preimage_translateByPoint_mulByN E (𝟙 S) P' N hP' (W i)).symm)
    (h i) _ ?_
  have hrel := unitPullback_translateByPoint_eq_of_splitting E hsm (𝟙 S) N Q hQ M hM
    W hW e hnorm h hn hsplit P' hP' i
  exact congrArg Units.val hrel

/-- **(U5-L2f)** The first-projection conjugation of function-field pullbacks: the
`translateByPoint`-action on the pullback presentation corresponds to the
`translateBy`-action on the curve through `fst`. Value form of the L2b crossing under
`functionFieldMap_comp`. -/
theorem functionFieldMap_translateByPoint_conj [IsLocallyNoetherian S]
    [IrreducibleSpace ↥E.E] [IrreducibleSpace ↥(pullback E.π (𝟙 S))]
    (P' : (E.baseChange (𝟙 S)).Point (𝟙 S))
    [IsDominant (translateByPoint E (𝟙 S) P')]
    (τp : E.E ⟶ E.E)
    (hτp : τp = (E.translateBy (overPoint E (𝟙 S) P' ≫ baseChangeIdFstOver E)).left)
    [IsDominant τp]
    (z : E.E.functionField) :
    (translateByPoint E (𝟙 S) P').functionFieldMap.hom
        ((pullback.fst E.π (𝟙 S)).functionFieldMap.hom z)
      = (pullback.fst E.π (𝟙 S)).functionFieldMap.hom
          (τp.functionFieldMap.hom z) := by
  haveI : IsDominant (pullback.fst E.π (𝟙 S)) := inferInstance
  have hsq : translateByPoint E (𝟙 S) P' ≫ pullback.fst E.π (𝟙 S)
      = pullback.fst E.π (𝟙 S) ≫ τp := by
    rw [hτp]
    exact translateByPoint_id_comp_fst E P'
  haveI hd1 : IsDominant (translateByPoint E (𝟙 S) P' ≫ pullback.fst E.π (𝟙 S)) := by
    rw [hsq]
    infer_instance
  have h1 := functionFieldMap_comp (translateByPoint E (𝟙 S) P')
    (pullback.fst E.π (𝟙 S))
  have h2 := functionFieldMap_comp (pullback.fst E.π (𝟙 S)) τp
  have hcross := functionFieldMap_congr hsq
  exact congrArg (fun (m : CommRingCat.of E.E.functionField ⟶
      CommRingCat.of (pullback E.π (𝟙 S)).functionField) => m.hom z)
    (h1.symm.trans (hcross.trans h2))

end FieldInstantiation

/-! ## The bridge hookup (U5-L2g) -/

section BridgeHookup

variable {K : Type u} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [W.toAffine.IsElliptic]
variable [AlgebraicGeometry.IsIntegral (projModel W)]
variable [(W.baseChange K).toAffine.IsElliptic]

/-- **(U5-L2g)** The bridge instantiated at a pullback-presentation section: the classical
translation action of the dictionary point computes, through
`EllipticCurve.projModelFunctionFieldEquiv`, the function-field pullback of the crossed translation. -/
theorem translateAlgEquivOfPoint_functionFieldMap_of_section
    (P'pb : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))))
    (p : SpecPoints (projModel W) (projModelπ W) K)
    (hxp : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P'pb ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = p.1)
    (τp : projModel W ⟶ projModel W)
    (hτp : τp = ((modelEllipticCurve W).translateBy
      (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P'pb ≫
        baseChangeIdFstOver (modelEllipticCurve W))).left)
    [IsDominant τp] (z : (projModel W).functionField) :
    HasseWeil.translateAlgEquivOfPoint W
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K p))
        (EllipticCurve.projModelFunctionFieldEquiv W z)
      = EllipticCurve.projModelFunctionFieldEquiv W (τp.functionFieldMap.hom z) := by
  have hb := EllipticCurve.functionFieldMap_translateBy W
    (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P'pb ≫
      baseChangeIdFstOver (modelEllipticCurve W)) p hxp
    (projModelPointsEquiv W K p) rfl
    (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) rfl
    τp (by rw [hτp]; rfl)
  have happ := congrArg (fun (m : W.toAffine.FunctionField →+* W.toAffine.FunctionField)
    => m (EllipticCurve.projModelFunctionFieldEquiv W z)) hb
  simpa [RingHom.comp_apply, RingEquiv.symm_apply_apply] using happ

end BridgeHookup

/-! ## The Picard group of a one-point scheme is trivial (U5-L1, Pic brick) -/

section PicPoint

open AlgebraicGeometry.Scheme.Modules

/-- **(U5-L1 Pic brick)** A scheme whose space is a nonempty subsingleton (e.g. the
spectrum of a field) has trivial Picard group: any invertible class trivialises over a
cover, some member of which must be `⊤`, and pullback along the (iso) inclusion of `⊤`
reflects the trivialisation. -/
theorem subsingleton_pic_of_subsingleton_space {X : Scheme.{u}}
    [Subsingleton ↥X] [Nonempty ↥X] :
    Subsingleton (AlgebraicGeometry.Scheme.Pic X) := by
  letI := Scheme.Modules.monoidalCategory X
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ u : AlgebraicGeometry.Scheme.Pic X, u = 1 by rw [h a, h b]
  intro u
  have hinv : IsInvertible ((fromSkeleton X.Modules).obj u.val) :=
    isInvertible_of_isUnit_toSkeleton (by
      rw [toSkeleton_fromSkeleton_obj]
      exact u.isUnit)
  obtain ⟨ι, U, hU, htriv⟩ := hinv
  obtain ⟨x⟩ := ‹Nonempty ↥X›
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hUi : (U i : TopologicalSpace.Opens ↥X) = ⊤ := by
    refine le_antisymm le_top ?_
    intro y _
    rwa [Subsingleton.elim y x]
  haveI : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) :=
    inferInstanceAs (IsIso (Scheme.topIso X).hom)
  haveI : IsIso (U i).ι := hUi.symm ▸ ‹IsIso (Scheme.Opens.ι (⊤ : X.Opens))›
  letI : (Scheme.Modules.pullback (U i).ι).IsEquivalence :=
    pullback_isEquivalence_of_iso (asIso (U i).ι)
  obtain ⟨e⟩ := htriv i
  have eglob : (fromSkeleton X.Modules).obj u.val ≅ unitObj X :=
    (Scheme.Modules.pullback (U i).ι).preimageIso (e ≪≫ (pullbackUnitIso (U i).ι).symm)
  have h1 : toSkeleton ((fromSkeleton X.Modules).obj u.val) = 1 :=
    toSkeleton_eq_one_of_iso_unitObj ⟨eglob⟩
  refine Units.ext ?_
  rw [← toSkeleton_fromSkeleton_obj u.val]
  exact h1

/-- Over the spectrum of a field the base has trivial Picard group, so the relative
normalisation in `κ` is invisible: `κ(Q) = [𝒪(Q)]·[𝒪(0)]⁻¹` on the nose. -/
theorem kappa_eq_sectionCls_mul_inv_zeroCls_of_field {K : Type u} [Field K]
    (E : EllipticCurve (Spec (CommRingCat.of K)))
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (Q : (E.baseChange (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K)))) :
    kappa E hsm (𝟙 (Spec (CommRingCat.of K))) Q =
      sectionCls E hsm (𝟙 (Spec (CommRingCat.of K))) Q.1 Q.2 *
        (zeroCls E hsm (𝟙 (Spec (CommRingCat.of K))))⁻¹ := by
  haveI hsub : Subsingleton ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI hne : Nonempty ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  haveI hpic : Subsingleton (AlgebraicGeometry.Scheme.Pic (Spec (CommRingCat.of K))) :=
    subsingleton_pic_of_subsingleton_space
  set x := sectionCls E hsm (𝟙 (Spec (CommRingCat.of K))) Q.1 Q.2 *
    (zeroCls E hsm (𝟙 (Spec (CommRingCat.of K))))⁻¹ with hx
  have hval : kappa E hsm (𝟙 (Spec (CommRingCat.of K))) Q =
      x * (Scheme.Pic.map (pullback.snd E.π (𝟙 (Spec (CommRingCat.of K))))
        (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π
          (𝟙 (Spec (CommRingCat.of K)))) x))⁻¹ :=
    kappa_eq_picRelProj E hsm (𝟙 (Spec (CommRingCat.of K))) Q
  rw [hval, show Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π
      (𝟙 (Spec (CommRingCat.of K)))) x = 1 from Subsingleton.elim _ _,
    map_one, inv_one, mul_one]

-- `ModularCurves.idealModule` (PoleSheaf, of a morphism) shadows the ideal-sheaf version
-- inside `namespace ModularCurves`; pin the one every statement below means
-- (the `Picard/SelfAdjointN.lean` idiom).
local notation "idealModule" => AlgebraicGeometry.Scheme.Modules.idealModule

/-- **(U5-L1a, the module dictionary)** Over a field, any module representing `κ(Q)`
tensored with the section ideal is isomorphic to the zero-section ideal:
`M ⊗ I(Q) ≅ I(0)`. Unit algebra in the skeleton from the class collapse. -/
theorem nonempty_tensorObj_sectionIdeal_iso_zeroIdeal_of_field {K : Type u} [Field K]
    (E : EllipticCurve (Spec (CommRingCat.of K)))
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (Q : (E.baseChange (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))))
    (M : (pullback E.π (𝟙 (Spec (CommRingCat.of K)))).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π (𝟙 (Spec (.of K))))
      (kappa E hsm (𝟙 (Spec (CommRingCat.of K))) Q).val = toSkeleton M) :
    letI := Scheme.Modules.monoidalCategory (pullback E.π (𝟙 (Spec (.of K))))
    Nonempty (tensorObj M
        (idealModule (Scheme.Hom.ker
          (Q.1 : Spec (CommRingCat.of K) ⟶ pullback E.π (𝟙 (Spec (CommRingCat.of K)))))) ≅
      idealModule (Scheme.Hom.ker
        (baseChangeZero E.π E.zero E.zero_π (𝟙 (Spec (CommRingCat.of K)))))) := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π (𝟙 (Spec (CommRingCat.of K))))
  haveI hsep : IsSeparated (pullback.snd E.π (𝟙 (Spec (CommRingCat.of K)))) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π (𝟙 (Spec (CommRingCat.of K)))
      ‹_›
  have hsm' : SmoothOfRelativeDimension 1
      (pullback.snd E.π (𝟙 (Spec (CommRingCat.of K)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π
      (𝟙 (Spec (CommRingCat.of K))) hsm
  set uQ := ((RelEffCartierDiv.sectionDivisor
      (pullback.snd E.π (𝟙 (Spec (CommRingCat.of K))))
      (Q.1 : Spec (CommRingCat.of K) ⟶ pullback E.π (𝟙 (Spec (CommRingCat.of K))))
      Q.2).isInvertible_idealModule
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' _ Q.2)).isUnit_toSkeleton.unit
    with huQ
  set u0 := ((RelEffCartierDiv.sectionDivisor
      (pullback.snd E.π (𝟙 (Spec (CommRingCat.of K))))
      (baseChangeZero E.π E.zero E.zero_π (𝟙 (Spec (CommRingCat.of K))))
      (baseChangeZero_snd E.π E.zero E.zero_π
        (𝟙 (Spec (CommRingCat.of K))))).isInvertible_idealModule
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' _
      (baseChangeZero_snd E.π E.zero E.zero_π
        (𝟙 (Spec (CommRingCat.of K)))))).isUnit_toSkeleton.unit with hu0
  have hcls : kappa E hsm (𝟙 (Spec (CommRingCat.of K))) Q = uQ⁻¹ * (u0⁻¹)⁻¹ :=
    kappa_eq_sectionCls_mul_inv_zeroCls_of_field E hsm Q
  letI := Scheme.Modules.symmetricCategory (pullback E.π (𝟙 (Spec (CommRingCat.of K))))
  have hval : toSkeleton M * uQ.val = u0.val := by
    have h1 := hM.symm.trans (congrArg Units.val hcls)
    rw [inv_inv] at h1
    calc toSkeleton M * uQ.val
        = ((uQ⁻¹ * u0) * uQ).val := by rw [Units.val_mul (uQ⁻¹ * u0) uQ, ← h1]
      _ = ((uQ⁻¹ * uQ) * u0).val := by
          rw [mul_assoc, mul_comm u0 uQ, ← mul_assoc]
      _ = u0.val := by rw [inv_mul_cancel, one_mul]
  have huQval : uQ.val = toSkeleton (idealModule (Scheme.Hom.ker
      (Q.1 : Spec (CommRingCat.of K) ⟶ pullback E.π (𝟙 (Spec (CommRingCat.of K)))))) :=
    IsUnit.unit_spec _
  have hu0val : u0.val = toSkeleton (idealModule (Scheme.Hom.ker
      (baseChangeZero E.π E.zero E.zero_π (𝟙 (Spec (CommRingCat.of K)))))) :=
    IsUnit.unit_spec _
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  refine (toSkeleton_tensorObj_eq M _).trans ?_
  refine (congrArg (toSkeleton M * ·) huQval.symm).trans ?_
  exact hval.trans hu0val

/-- **(U5-L1a step 3a)** A common principal refinement on an integral scheme: at every
point there is an affine open contained in a prescribed open on which both ideals are
principal with nonzerodivisor generators. Per-point choices, one further basic-open
refinement, `IdealSheafData.map_ideal` + `Ideal.map_span` for the spans, and integrality
for the nonzerodivisor transfer (sections rings are domains, restrictions injective). -/
theorem exists_affine_common_principal {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (J₁ J₂ : X.IdealSheafData)
    (h₁ : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ f : Γ(X, V.1),
      J₁.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors Γ(X, V.1))
    (h₂ : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ f : Γ(X, V.1),
      J₂.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors Γ(X, V.1))
    (W : ↥X → X.Opens) (hW : ∀ c, c ∈ W c) :
    ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ V.1 ≤ W c ∧
      (∃ f : Γ(X, V.1), J₁.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∃ f : Γ(X, V.1), J₂.ideal V = Ideal.span {f} ∧ f ∈ nonZeroDivisors Γ(X, V.1)) := by
  intro c
  obtain ⟨V₁, hc1, f₁, hspan1, hnzd1⟩ := h₁ c
  obtain ⟨V₂, hc2, f₂, hspan2, hnzd2⟩ := h₂ c
  obtain ⟨b, hble, hcb⟩ := V₁.2.exists_basicOpen_le
    (V := V₂.1 ⊓ W c) ⟨c, ⟨hc2, hW c⟩⟩ hc1
  set V : X.affineOpens := X.affineBasicOpen b with hV
  have hVle1 : V ≤ V₁ := X.affineBasicOpen_le b
  have hVle2 : V.1 ≤ V₂.1 := le_trans hble inf_le_left
  have hVleW : V.1 ≤ W c := le_trans hble inf_le_right
  haveI hne : Nonempty ↥(V.1 : X.Opens) := ⟨⟨c, hcb⟩⟩
  haveI hne1 : Nonempty ↥(V₁.1 : X.Opens) := ⟨⟨c, hc1⟩⟩
  haveI hne2 : Nonempty ↥(V₂.1 : X.Opens) := ⟨⟨c, hc2⟩⟩
  haveI : IsDomain Γ(X, V.1) :=
    @AlgebraicGeometry.IsIntegral.component_integral X ‹_› (V.1 : X.Opens) hne
  haveI : IsDomain Γ(X, V₁.1) :=
    @AlgebraicGeometry.IsIntegral.component_integral X ‹_› (V₁.1 : X.Opens) hne1
  haveI : IsDomain Γ(X, V₂.1) :=
    @AlgebraicGeometry.IsIntegral.component_integral X ‹_› (V₂.1 : X.Opens) hne2
  have hVle2' : V ≤ V₂ := hVle2
  have hs1 : J₁.ideal V = Ideal.span
      {X.presheaf.map (homOfLE (show V.1 ≤ V₁.1 from hVle1)).op f₁} := by
    rw [← J₁.map_ideal (U := V) (V := V₁) hVle1, hspan1, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hs2 : J₂.ideal V = Ideal.span
      {X.presheaf.map (homOfLE (show V.1 ≤ V₂.1 from hVle2)).op f₂} := by
    rw [← J₂.map_ideal (U := V) (V := V₂) hVle2', hspan2, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hn1 : X.presheaf.map (homOfLE (show V.1 ≤ V₁.1 from hVle1)).op f₁ ∈
      nonZeroDivisors Γ(X, V.1) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    refine (mem_nonZeroDivisors_iff_ne_zero.mp hnzd1) ?_
    refine @AlgebraicGeometry.map_injective_of_isIntegral X ‹_› _ _
      (homOfLE (show V.1 ≤ V₁.1 from hVle1)) hne f₁ 0 ?_
    rw [h0, map_zero]
  have hn2 : X.presheaf.map (homOfLE (show V.1 ≤ V₂.1 from hVle2)).op f₂ ∈
      nonZeroDivisors Γ(X, V.1) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    refine (mem_nonZeroDivisors_iff_ne_zero.mp hnzd2) ?_
    refine @AlgebraicGeometry.map_injective_of_isIntegral X ‹_› _ _
      (homOfLE (show V.1 ≤ V₂.1 from hVle2)) hne f₂ 0 ?_
    rw [h0, map_zero]
  exact ⟨V, hcb, hVleW, ⟨_, hs1, hn1⟩, ⟨_, hs2, hn2⟩⟩

/-- **(U5-L1a step 3b-i)** On a principal affine chart the generator trivialises the ideal
module: `idealGenHom` is an isomorphism. Extraction of the inner assembly of
`isInvertible_idealModule` (Picard/IdealModule.lean) for a *given* chart. -/
theorem isIso_idealGenHom_of_principal {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1)) :
    IsIso (idealGenHom J V.1 f hfmem) := by
  refine isIso_of_bijective_app_on_basis _
    {W | ∃ (b : Γ(X, V.1)) (_ : X.basicOpen b ≤ V.1),
      W = V.1.ι ⁻¹ᵁ X.basicOpen b} ?_ ?_
  · intro x U hxU
    have hxV : V.1.ι.base x ∈ V.1 := x.2
    obtain ⟨b, hble, hxb⟩ := V.2.exists_basicOpen_le
      (V := V.1.ι ''ᵁ U) ⟨V.1.ι.base x, ⟨x, hxU, rfl⟩⟩ hxV
    refine ⟨V.1.ι ⁻¹ᵁ X.basicOpen b,
      ⟨b, hble.trans (V.1.ι_image_le U), rfl⟩, hxb, ?_⟩
    calc V.1.ι ⁻¹ᵁ X.basicOpen b
        ≤ V.1.ι ⁻¹ᵁ (V.1.ι ''ᵁ U) := fun y hy => hble hy
      _ = U := Scheme.Hom.preimage_image_eq _ U
  · rintro W ⟨b, hb, rfl⟩
    exact bijective_idealGenHom_app J V f hspan hnzd hfmem b hb

/-- **(U5-L1a step 3b-i, packaged)** The pullback of the ideal module to a principal
affine chart is trivial. -/
theorem nonempty_pullback_idealModule_iso_unit_of_principal {X : Scheme.{u}}
    (J : X.IdealSheafData) (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1)) :
    Nonempty ((Scheme.Modules.pullback V.1.ι).obj (idealModule J) ≅
      unitObj ↑(V.1)) := by
  have hfmem : f ∈ idealSections J (Opposite.op V.1) := by
    rw [show idealSections J (Opposite.op V.1) = J.ideal V from
      J.ker_subschemeι_app V, hspan]
    exact Ideal.mem_span_singleton_self f
  haveI := isIso_idealGenHom_of_principal J V f hspan hnzd hfmem
  exact ⟨(restrictFunctorIsoPullback V.1.ι).symm.app (idealModule J) ≪≫
    (asIso (idealGenHom J V.1 f hfmem)).symm⟩

/-- **(U5-L1a step 3b-ii)** On a chart where both ideals are principal, any module whose
tensor with the first ideal is the second ideal trivialises:
`pb M ≅ pb M ⊗ 𝒪 ≅ pb M ⊗ pb I₁ ≅ pb (M ⊗ I₁) ≅ pb I₂ ≅ 𝒪`. -/
theorem nonempty_pullback_iso_unit_of_tensor_ideal {X : Scheme.{u}}
    (M : X.Modules) (J₁ J₂ : X.IdealSheafData)
    (hMdict : Nonempty (tensorObj M (idealModule J₁) ≅ idealModule J₂))
    (V : X.affineOpens) (f₁ f₂ : Γ(X, V.1))
    (hspan₁ : J₁.ideal V = Ideal.span {f₁}) (hnzd₁ : f₁ ∈ nonZeroDivisors Γ(X, V.1))
    (hspan₂ : J₂.ideal V = Ideal.span {f₂}) (hnzd₂ : f₂ ∈ nonZeroDivisors Γ(X, V.1)) :
    Nonempty ((Scheme.Modules.pullback V.1.ι).obj M ≅ unitObj ↑(V.1)) := by
  obtain ⟨e⟩ := hMdict
  obtain ⟨t⟩ := nonempty_pullback_tensorObj V.1.ι M (idealModule J₁)
  obtain ⟨u₁⟩ := nonempty_pullback_idealModule_iso_unit_of_principal J₁ V f₁ hspan₁ hnzd₁
  obtain ⟨u₂⟩ := nonempty_pullback_idealModule_iso_unit_of_principal J₂ V f₂ hspan₂ hnzd₂
  exact ⟨(tensorObjUnitIso ((Scheme.Modules.pullback V.1.ι).obj M)).symm ≪≫
    tensorObjCongr (Iso.refl _) u₁.symm ≪≫ t.symm ≪≫
    (Scheme.Modules.pullback V.1.ι).mapIso e ≪≫ u₂⟩

/-- **(U5-L1a step 3c-ii, the generator-change law, per-app form)** Changing the
generator of an ideal module by a unit factor changes `idealGenHom` by the
multiplication endomorphism of that factor: at every open `W` of the chart and every
section `a`, the `f₂ * u`-trivialisation is the `f₂`-trivialisation precomposed with
mult-by-`u`. Stated per-application (hom-level `ext` whnf-walls on the endo-composite);
this is the shape 3c-iii consumes. -/
theorem idealGenHom_mul_app {X : Scheme.{u}} (J : X.IdealSheafData) (V : X.Opens)
    (f₂ u : Γ(X, V))
    (hm₁ : f₂ * u ∈ idealSections J (Opposite.op V))
    (hm₂ : f₂ ∈ idealSections J (Opposite.op V))
    (W : (V.toScheme.Opens)ᵒᵖ) (a : Γ(V.toScheme, W.unop)) :
    ((idealGenHom J V (f₂ * u) hm₁).val.app W).hom a =
      ((idealGenHom J V f₂ hm₂).val.app W).hom
        (((ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection V u)).val.app W).hom a) := by
  refine Subtype.ext ?_
  show _ * _ = _
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [idealGenHom, Scheme.Modules.openTopSection, map_mul,
    ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  simp [Scheme.Hom.appIso_inv_naturality, Scheme.Hom.appIso_hom_naturality,
    ← Functor.map_comp]
  rw [mul_right_comm, mul_assoc]
  congr 1
  congr 1
  erw [CategoryTheory.ConcreteCategory.id_apply]
  erw [← CategoryTheory.ConcreteCategory.comp_apply]
  rw [← Functor.map_comp]
  exact congrArg (fun g => (CategoryTheory.ConcreteCategory.hom (X.presheaf.map g)) u)
    (Subsingleton.elim _ _)

/-- **(U5-L1a step 3b-i, definite form)** The trivialisation of the pulled-back ideal
module on a principal affine chart, as a *definite* iso (not merely `Nonempty`): the
3c-iii transition computation must read ratios off a pinned choice. -/
noncomputable def pullbackIdealTrivOfPrincipal {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1)) :
    (Scheme.Modules.pullback V.1.ι).obj (idealModule J) ≅ unitObj ↑(V.1) :=
  haveI := isIso_idealGenHom_of_principal J V f hspan hnzd hfmem
  (restrictFunctorIsoPullback V.1.ι).symm.app (idealModule J) ≪≫
    (asIso (idealGenHom J V.1 f hfmem)).symm

/-- **(U5-L1a step 3b-ii, definite form)** The chart trivialisation of a module `M` with
`M ⊗ I₁ ≅ I₂`, as the definite five-step iso
`pb M ≅ pb M ⊗ 𝒪 ≅ pb M ⊗ pb I₁ ≅ pb (M ⊗ I₁) ≅ pb I₂ ≅ 𝒪`
(3c-iii reads the overlap transition ratios off this construction). -/
noncomputable def pullbackTrivOfTensorIdeal {X : Scheme.{u}}
    (M : X.Modules) (J₁ J₂ : X.IdealSheafData)
    (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (V : X.affineOpens) (f₁ f₂ : Γ(X, V.1))
    (hspan₁ : J₁.ideal V = Ideal.span {f₁}) (hnzd₁ : f₁ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₁ : f₁ ∈ idealSections J₁ (Opposite.op V.1))
    (hspan₂ : J₂.ideal V = Ideal.span {f₂}) (hnzd₂ : f₂ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₂ : f₂ ∈ idealSections J₂ (Opposite.op V.1)) :
    (Scheme.Modules.pullback V.1.ι).obj M ≅ unitObj ↑(V.1) :=
  (tensorObjUnitIso ((Scheme.Modules.pullback V.1.ι).obj M)).symm ≪≫
    tensorObjCongr (Iso.refl _)
      (pullbackIdealTrivOfPrincipal J₁ V f₁ hspan₁ hnzd₁ hfmem₁).symm ≪≫
    (pullbackTensorObjIsoOfIsOpenImmersion V.1.ι M (idealModule J₁)).symm ≪≫
    (Scheme.Modules.pullback V.1.ι).mapIso e ≪≫
    pullbackIdealTrivOfPrincipal J₂ V f₂ hspan₂ hnzd₂ hfmem₂

/-- **(U5-L1a 3c-iii A0)** The inclusion of the ideal module into the structure sheaf
(componentwise `Subtype.val`) — the global comparison hom against which chart
trivialisations are characterised (`restrictOverTrivialization_inv_comp_over`-style).
Natural home after cleanup: `Picard/IdealModule.lean`. -/
noncomputable def idealModuleToUnitHom {X : Scheme.{u}} (J : X.IdealSheafData) :
    idealModule J ⟶ unitObj X :=
  ⟨{ app := fun U => ModuleCat.ofHom
      { toFun := fun m => m.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
     naturality := fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }⟩

/-- **(U5-L1a 3c-iii A1-pre)** Feeding the definite 3b-i trivialisation through the
pullback→restriction bridge recovers the bare `idealGenHom`-inverse: the
`restrictFunctorIsoPullback` clothing cancels. -/
theorem restrictIsoOfPullbackIso_pullbackIdealTrivOfPrincipal {X : Scheme.{u}}
    (J : X.IdealSheafData) (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1)) :
    restrictIsoOfPullbackIso (idealModule J) V.1
        (pullbackIdealTrivOfPrincipal J V f hspan hnzd hfmem) =
      haveI := isIso_idealGenHom_of_principal J V f hspan hnzd hfmem
      (asIso (idealGenHom J V.1 f hfmem)).symm := by
  haveI := isIso_idealGenHom_of_principal J V f hspan hnzd hfmem
  refine Iso.ext ?_
  show ((restrictFunctorIsoPullback V.1.ι).app (idealModule J)).hom ≫
      (((restrictFunctorIsoPullback V.1.ι).symm.app (idealModule J)) ≪≫
        (asIso (idealGenHom J V.1 f hfmem)).symm).hom = _
  rw [Iso.trans_hom, ← Category.assoc]
  simp

/-- **(U5-L1a 3c-iii A1)** The characterisation of the generator trivialisation against
the ideal inclusion: `idealGenHom` composed with the restricted inclusion is
multiplication by (the restriction of) `f` — the defining formula, per-app. -/
theorem idealGenHom_comp_toUnitHom_app_apply {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.Opens) (f : Γ(X, V))
    (hfmem : f ∈ idealSections J (Opposite.op V))
    (W : (V.toScheme.Opens)ᵒᵖ) (g : Γ(V.toScheme, W.unop)) :
    ((idealGenHom J V f hfmem ≫
        (restrictFunctor V.ι).map (idealModuleToUnitHom J)).val.app W).hom g =
      X.presheaf.map (homOfLE (V.ι_image_le W.unop)).op f *
        (CategoryTheory.ConcreteCategory.hom (V.ι.appIso W.unop).inv) g := rfl

/-- **(U5-L1a 3c-iii B1-leaf)** The unit-comparison micro-leaf of the B1
characterisation: the mult-by-`f` map `idealGenHom ≫ incl` transported through the
over-equivalence unit plumbing is the scalar endomorphism of the top-section of `f`.
Everything else in B1 is proven functor algebra; this is the one residual app-level
identity (the `overFunctorEquiv`/`sheafOfModulesEquivOverUnit` collapse — toolkit:
`localModuleSection` app-lemmas in `DualPullback/OpenUnit.lean`,
`restrictUnitIso_inv_app_applyP` in `DualPullback/UnitComp.lean`). -/
theorem idealGenHom_comp_toUnitHom_comp_unitComparison {X : Scheme.{u}}
    (J : X.IdealSheafData) (V : X.affineOpens) (f : Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1)) :
    (idealGenHom J V.1 f hfmem ≫
        (restrictFunctor V.1.ι).map (idealModuleToUnitHom J) ≫
        (overFunctorEquiv V.1).inv.app (unitObj X)) ≫
      (V.1.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
    ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection V.1 f) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  repeat' erw [sheafOfModules_comp_app_apply]
  erw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  erw [sheafOfModulesEquivOverUnit_hom_app_apply]
  erw [show (CategoryTheory.ConcreteCategory.hom
        (((restrictFunctor (V.1).ι).map
          (ModularCurves.idealModuleToUnitHom J)).val.app W))
      ((CategoryTheory.ConcreteCategory.hom
        ((idealGenHom J (V.1) f hfmem).val.app W)) x) =
    X.presheaf.map (homOfLE ((V.1).ι_image_le W.unop)).op f *
      (CategoryTheory.ConcreteCategory.hom ((V.1).ι.appIso W.unop).inv) x from rfl]
  rw [mul_comm]
  congr 1
  · first
      | rfl
      | (rw [Scheme.Opens.ι_appIso]; simp;
         erw [CategoryTheory.ConcreteCategory.id_apply])
      | (rw [Scheme.Opens.ι_appIso]; simp)
  · have h := openTopSection_restrict (V.1) W.unop f
    rw [Scheme.Opens.ι_appIso] at h
    first
      | exact h
      | exact h.symm

/-- **(U5-L1a 3c-iii B1)** The over-site characterisation of the definite 3b-i
trivialisation against the ideal inclusion: its inverse composed with the restricted
inclusion is multiplication by the generator. This is the
`restrictOverTrivialization_inv_comp_over`-shaped input that makes the transition of the
trivialisation family computable after restriction to overlaps. Proof: the
`G.map_injective` choreography of `overTrivializationOfRestrictIso_hom_eq_comp_scalar`
(PoleSheaf) + the A1-pre cancellation + `overEquiv_unitScalarEnd` conjugation, closed by
the `B1-leaf` micro-lemma. -/
theorem overTriv_pullbackIdealTriv_inv_comp_toUnitHom {X : Scheme.{u}}
    (J : X.IdealSheafData) (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1)) :
    (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) V.1
        (restrictIsoOfPullbackIso (idealModule J) V.1
          (pullbackIdealTrivOfPrincipal J V f hspan hnzd hfmem))).inv ≫
      (idealModuleToUnitHom J).over V.1 =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf V.1 f := by
  rw [restrictIsoOfPullbackIso_pullbackIdealTrivOfPrincipal]
  haveI := isIso_idealGenHom_of_principal J V f hspan hnzd hfmem
  let G := (Scheme.Modules.overEquiv V.1).functor
  let F := Scheme.Modules.overFunctorEquiv V.1
  let C := V.1.sheafOfModulesEquivOverUnit X.ringCatSheaf
  apply G.map_injective
  rw [Functor.map_comp]
  simp only [Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.map_preimage,
    Iso.trans_inv, Iso.symm_inv]
  have hs : G.map (ModularCurves.SheafOfModules.overUnitScalarEnd
      X.ringCatSheaf V.1 f) =
      C.hom ≫ ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection V.1 f) ≫ C.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.Modules.overEquiv_unitScalarEnd V.1 f
  rw [hs]
  have hnat : (restrictFunctor V.1.ι).map (idealModuleToUnitHom J) ≫
      F.inv.app (unitObj X) =
      F.inv.app (idealModule J) ≫
        G.map (SheafOfModules.Hom.over (idealModuleToUnitHom J) V.1) :=
    F.inv.naturality _
  have hFinv : ((overFunctorEquiv V.1).app (idealModule J)).inv =
      F.inv.app (idealModule J) := by
    simp [F]
  rw [Category.assoc, Category.assoc, hFinv, ← hnat]
  simp only [asIso_hom]
  rw [cancel_epi C.hom, Iso.eq_comp_inv]
  have h := idealGenHom_comp_toUnitHom_comp_unitComparison J V f hfmem
  calc (idealGenHom J V.1 f hfmem ≫
        (restrictFunctor V.1.ι).map (idealModuleToUnitHom J) ≫
          F.inv.app (unitObj X)) ≫ C.hom
      = (idealGenHom J V.1 f hfmem ≫
          (restrictFunctor V.1.ι).map (idealModuleToUnitHom J) ≫
          (overFunctorEquiv V.1).inv.app (unitObj X)) ≫
          (V.1.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom := rfl
    _ = ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection V.1 f) := h

/-- **(U5-L1a 3c-iii B2)** Componentwise-nonzerodivisor scalars act monomorphically on
the over-site unit module: the cancellation step of the transition computation. The
hypothesis is componentwise so that the consumer can discharge it from chart
integrality (nonempty case) or vacuously (empty overlap). -/
theorem mono_overUnitScalarEnd_of_nonZeroDivisors {X : Scheme.{u}} (V : X.Opens)
    (r : Γ(X, V))
    (hr : ∀ (W : X.Opens) (h : W ≤ V),
      X.presheaf.map (homOfLE h).op r ∈ nonZeroDivisors Γ(X, W)) :
    Mono ((SheafOfModules.overUnitScalarEnd X.ringCatSheaf V r :
      CategoryTheory.End (SheafOfModules.unit (X.ringCatSheaf.over V)))) := by
  constructor
  intro Z g₁ g₂ hgg
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have happ := congrArg (fun q => (CategoryTheory.ConcreteCategory.hom
    (q.val.app W)) x) hgg
  simp only [sheafOfModules_comp_app_apply] at happ
  erw [SheafOfModules.overUnitScalarEnd_app_apply,
    SheafOfModules.overUnitScalarEnd_app_apply] at happ
  dsimp only at happ
  have happ' : ((show Γ(X, (Opposite.unop W).left) from
        (CategoryTheory.ConcreteCategory.hom (g₁.val.app W)) x) *
      (CategoryTheory.ConcreteCategory.hom
        (X.presheaf.map (homOfLE (leOfHom (Opposite.unop W).hom)).op)) r) =
      ((show Γ(X, (Opposite.unop W).left) from
        (CategoryTheory.ConcreteCategory.hom (g₂.val.app W)) x) *
      (CategoryTheory.ConcreteCategory.hom
        (X.presheaf.map (homOfLE (leOfHom (Opposite.unop W).hom)).op)) r) := by
    exact happ
  have h0' := sub_eq_zero_of_eq happ'
  rw [← sub_mul] at h0'
  have hz := (mem_nonZeroDivisors_iff.mp
    (hr (Opposite.unop W).left (leOfHom (Opposite.unop W).hom))).2 _ h0'
  exact sub_eq_zero.mp hz

/-- **(U5-L1a 3c-iii C(i)-a)** The ideal inclusion is a monomorphism on every over-site
(componentwise `Subtype.val` is injective). With this, two chart trivialisations
characterised against the inclusion (B1-style) are equal up to exactly the scalar
relating their characterisation values — the transition read-off needs no cancellation
beyond this. -/
theorem mono_idealModuleToUnitHom_over {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.Opens) :
    Mono ((idealModuleToUnitHom J).over V) := by
  constructor
  intro Z g₁ g₂ hgg
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have happ := congrArg (fun q => (CategoryTheory.ConcreteCategory.hom
    (q.val.app W)) x) hgg
  simp only [sheafOfModules_comp_app_apply] at happ
  exact Subtype.ext happ

/-- **(U5-L1a 3c-iii C(i))** The scalar endomorphisms are multiplicative:
`scalar (a·b) = scalar a ≫ scalar b`. -/
theorem overUnitScalarEnd_mul {X : Scheme.{u}} (V : X.Opens) (a b : Γ(X, V)) :
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf V (a * b) =
    (SheafOfModules.overUnitScalarEnd X.ringCatSheaf V a ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf V b :
      CategoryTheory.End (SheafOfModules.unit (X.ringCatSheaf.over V))) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [sheafOfModules_comp_app_apply]
  erw [SheafOfModules.overUnitScalarEnd_app_apply,
    SheafOfModules.overUnitScalarEnd_app_apply,
    SheafOfModules.overUnitScalarEnd_app_apply]
  dsimp only
  show ((show Γ(X, (Opposite.unop W).left) from x) *
      (CategoryTheory.ConcreteCategory.hom
        (X.presheaf.map (homOfLE (leOfHom (Opposite.unop W).hom)).op)) (a * b)) =
    (((show Γ(X, (Opposite.unop W).left) from x) *
      (CategoryTheory.ConcreteCategory.hom
        (X.presheaf.map (homOfLE (leOfHom (Opposite.unop W).hom)).op)) a) *
      (CategoryTheory.ConcreteCategory.hom
        (X.presheaf.map (homOfLE (leOfHom (Opposite.unop W).hom)).op)) b)
  rw [map_mul]
  exact (mul_assoc _ _ _).symm

/-- **(U5-L1a 3c-iii C(i)-b, the transition read-off)** Two trivialisations of the
ideal module characterised against the inclusion by scalars `r₁ = u·r₂` differ by
exactly `scalar u`: `T₁.inv ≫ T₂.hom = scalar u`. Combined with the B1
characterisation, `restrictOverTrivialization_inv_comp_over` (restriction), and 3c-i
(the generator unit), this computes `trivializationTransitionUnit` for the ideal legs
with no further cancellation. -/
theorem trivialization_inv_comp_hom_of_characterisation {X : Scheme.{u}}
    (J : X.IdealSheafData) (V : X.Opens)
    (T₁ T₂ : (idealModule J).over V ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over V))
    (r₁ r₂ u : Γ(X, V))
    (h₁ : T₁.inv ≫ (idealModuleToUnitHom J).over V =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf V r₁)
    (h₂ : T₂.inv ≫ (idealModuleToUnitHom J).over V =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf V r₂)
    (hu : r₁ = u * r₂) :
    T₁.inv ≫ T₂.hom = SheafOfModules.overUnitScalarEnd X.ringCatSheaf V u := by
  haveI := mono_idealModuleToUnitHom_over J V
  have key : T₁.inv = SheafOfModules.overUnitScalarEnd X.ringCatSheaf V u ≫ T₂.inv := by
    rw [← cancel_mono ((idealModuleToUnitHom J).over V), h₁, Category.assoc, h₂, hu]
    exact overUnitScalarEnd_mul V u r₂
  rw [key, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **(U5-L1a 3c-iii, the general pullback-side restriction)** A pullback-level iso of
two modules restricts to any smaller open (the general-target sibling of
`restrictTrivialization`, InvertibleSheaf:229 — same clothing with the `N`-side
comparison in place of `pullbackUnitIso`). Every prefix-leg's inf-version is this
applied to the leg. -/
noncomputable def restrictPullbackIso {X : Scheme.{u}} (M N : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N) :
    (Scheme.Modules.pullback W.ι).obj M ≅ (Scheme.Modules.pullback W.ι).obj N :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hWU).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hWU)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).app N ≪≫
    ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWU).symm).app N).symm

/-- **(U5-L1a 3c-iii)** The general pullback-side restriction respects composition:
prefix chains restrict leg-wise at the pullback level. -/
theorem restrictPullbackIso_trans {X : Scheme.{u}} (M N P : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (e₁ : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N)
    (e₂ : (Scheme.Modules.pullback U.ι).obj N ≅ (Scheme.Modules.pullback U.ι).obj P) :
    restrictPullbackIso M P hWU (e₁ ≪≫ e₂) =
      restrictPullbackIso M N hWU e₁ ≪≫ restrictPullbackIso N P hWU e₂ := by
  refine Iso.ext ?_
  simp [restrictPullbackIso]

/-- **(U5-L1a 3c-iii)** The general two-sided pullback/restriction bridge (the
arbitrary-target sibling of `pullbackIsoOfRestrictIso`). -/
noncomputable def pullbackIsoOfRestrictIsoGen {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (φ : M.restrict U.ι ≅ N.restrict U.ι) :
    (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N :=
  ((restrictFunctorIsoPullback U.ι).app M).symm ≪≫ φ ≪≫
    (restrictFunctorIsoPullback U.ι).app N

/-- **(U5-L1a 3c-iii)** The restrict-side restriction of a general restrict-site iso to
a smaller open, through the pullback bridges: the `φ`-restriction every prefix-leg's
overlap comparison consumes. -/
noncomputable def restrictRestrictIso {X : Scheme.{u}} (M N : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (φ : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict W.ι ≅ N.restrict W.ι :=
  (restrictFunctorIsoPullback W.ι).app M ≪≫
    restrictPullbackIso M N hWU (pullbackIsoOfRestrictIsoGen M N U φ) ≪≫
    ((restrictFunctorIsoPullback W.ι).app N).symm


/-- **(U5-L1a 3c-iii, tail identification)** The over-form of the definite ideal
trivialisation is the over-form of the bare generator division: `congrArg` of the
A1-pre clothing cancellation. -/
theorem overTriv_pullbackIdealTriv_eq {X : Scheme.{u}} (J : X.IdealSheafData)
    (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1)) :
    Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) V.1
        (restrictIsoOfPullbackIso (idealModule J) V.1
          (pullbackIdealTrivOfPrincipal J V f hspan hnzd hfmem)) =
      Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) V.1
        (haveI := isIso_idealGenHom_of_principal J V f hspan hnzd hfmem
         (asIso (idealGenHom J V.1 f hfmem)).symm) :=
  congrArg _ (restrictIsoOfPullbackIso_pullbackIdealTrivOfPrincipal J V f
    hspan hnzd hfmem)

/-- **(U5-L1a 3c-iii C-rest-1)** The B1 characterisation restricted to a sub-open: the
restriction of the chart trivialisation is characterised by the restricted generator.
Direct instantiation of `restrictOverTrivialization_inv_comp_over` at B1; feeding two
charts' restrictions to the overlap into the C(i)-b read-off computes the ideal-leg
transition as the 3c-i unit. -/
theorem overTriv_pullbackIdealTriv_restrict_inv_comp_toUnitHom {X : Scheme.{u}}
    (J : X.IdealSheafData) (V : X.affineOpens) (f : Γ(X, V.1))
    (hspan : J.ideal V = Ideal.span {f}) (hnzd : f ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem : f ∈ idealSections J (Opposite.op V.1))
    {U : X.Opens} (hUV : U ≤ V.1) :
    (SheafOfModules.restrictOverTrivialization X.ringCatSheaf (idealModule J) V.1
        (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) V.1
          (restrictIsoOfPullbackIso (idealModule J) V.1
            (pullbackIdealTrivOfPrincipal J V f hspan hnzd hfmem)))
        (Over.mk (homOfLE hUV))).inv ≫
      (idealModuleToUnitHom J).over U =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
      (X.presheaf.map (homOfLE hUV).op f) :=
  restrictOverTrivialization_inv_comp_over (idealModuleToUnitHom J) V.1
    (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) V.1
      (restrictIsoOfPullbackIso (idealModule J) V.1
        (pullbackIdealTrivOfPrincipal J V f hspan hnzd hfmem)))
    f (overTriv_pullbackIdealTriv_inv_comp_toUnitHom J V f hspan hnzd hfmem) hUV

/-- **(U5-L1a 3c-iii, THE IDEAL-LEG TRANSITION — hom level)** On the overlap of two
principal charts whose generators are related by `res fᵢ = u · res fⱼ`, the restricted
chart trivialisations differ by exactly `scalar u`. Pure assembly:
C-rest-1 at both charts + the C(i)-b read-off. -/
theorem idealTriv_restrict_inv_comp_hom {X : Scheme.{u}} (J : X.IdealSheafData)
    (Vi Vj : X.affineOpens) (fi : Γ(X, Vi.1)) (fj : Γ(X, Vj.1))
    (hspani : J.ideal Vi = Ideal.span {fi}) (hnzdi : fi ∈ nonZeroDivisors Γ(X, Vi.1))
    (hfmemi : fi ∈ idealSections J (Opposite.op Vi.1))
    (hspanj : J.ideal Vj = Ideal.span {fj}) (hnzdj : fj ∈ nonZeroDivisors Γ(X, Vj.1))
    (hfmemj : fj ∈ idealSections J (Opposite.op Vj.1))
    (u : Γ(X, Vi.1 ⊓ Vj.1))
    (hu : X.presheaf.map (homOfLE (inf_le_left : Vi.1 ⊓ Vj.1 ≤ Vi.1)).op fi =
      u * X.presheaf.map (homOfLE (inf_le_right : Vi.1 ⊓ Vj.1 ≤ Vj.1)).op fj) :
    (SheafOfModules.restrictOverTrivialization X.ringCatSheaf (idealModule J) Vi.1
        (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) Vi.1
          (restrictIsoOfPullbackIso (idealModule J) Vi.1
            (pullbackIdealTrivOfPrincipal J Vi fi hspani hnzdi hfmemi)))
        (Over.mk (homOfLE inf_le_left))).inv ≫
      (SheafOfModules.restrictOverTrivialization X.ringCatSheaf (idealModule J) Vj.1
        (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) Vj.1
          (restrictIsoOfPullbackIso (idealModule J) Vj.1
            (pullbackIdealTrivOfPrincipal J Vj fj hspanj hnzdj hfmemj)))
        (Over.mk (homOfLE inf_le_right))).hom =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf (Vi.1 ⊓ Vj.1) u :=
  trivialization_inv_comp_hom_of_characterisation J (Vi.1 ⊓ Vj.1) _ _
    (X.presheaf.map (homOfLE (inf_le_left : Vi.1 ⊓ Vj.1 ≤ Vi.1)).op fi)
    (X.presheaf.map (homOfLE (inf_le_right : Vi.1 ⊓ Vj.1 ≤ Vj.1)).op fj) u
    (overTriv_pullbackIdealTriv_restrict_inv_comp_toUnitHom J Vi fi hspani hnzdi
      hfmemi inf_le_left)
    (overTriv_pullbackIdealTriv_restrict_inv_comp_toUnitHom J Vj fj hspanj hnzdj
      hfmemj inf_le_right)
    hu

/-- **(U5-L1a 3c-iii, THE IDEAL-LEG TRANSITION — unit level)** The
`trivializationTransitionUnit` of the two restricted chart trivialisations is the 3c-i
generator unit. This is the `transitionUnitOfCover`-shaped output for the ideal legs. -/
theorem trivializationTransitionUnit_idealTriv {X : Scheme.{u}} (J : X.IdealSheafData)
    (Vi Vj : X.affineOpens) (fi : Γ(X, Vi.1)) (fj : Γ(X, Vj.1))
    (hspani : J.ideal Vi = Ideal.span {fi}) (hnzdi : fi ∈ nonZeroDivisors Γ(X, Vi.1))
    (hfmemi : fi ∈ idealSections J (Opposite.op Vi.1))
    (hspanj : J.ideal Vj = Ideal.span {fj}) (hnzdj : fj ∈ nonZeroDivisors Γ(X, Vj.1))
    (hfmemj : fj ∈ idealSections J (Opposite.op Vj.1))
    (u : Γ(X, Vi.1 ⊓ Vj.1)ˣ)
    (hu : X.presheaf.map (homOfLE (inf_le_left : Vi.1 ⊓ Vj.1 ≤ Vi.1)).op fi =
      (u : Γ(X, Vi.1 ⊓ Vj.1)) *
        X.presheaf.map (homOfLE (inf_le_right : Vi.1 ⊓ Vj.1 ≤ Vj.1)).op fj) :
    trivializationTransitionUnit (Vi.1 ⊓ Vj.1)
      (SheafOfModules.restrictOverTrivialization X.ringCatSheaf (idealModule J) Vi.1
        (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) Vi.1
          (restrictIsoOfPullbackIso (idealModule J) Vi.1
            (pullbackIdealTrivOfPrincipal J Vi fi hspani hnzdi hfmemi)))
        (Over.mk (homOfLE inf_le_left)))
      (SheafOfModules.restrictOverTrivialization X.ringCatSheaf (idealModule J) Vj.1
        (Scheme.Modules.overTrivializationOfRestrictIso (idealModule J) Vj.1
          (restrictIsoOfPullbackIso (idealModule J) Vj.1
            (pullbackIdealTrivOfPrincipal J Vj fj hspanj hnzdj hfmemj)))
        (Over.mk (homOfLE inf_le_right))) = u := by
  letI : ∀ (U : (TopologicalSpace.Opens ↥X)ᵒᵖ),
      IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩
  apply Units.ext
  apply (SheafOfModules.overUnitScalarEndRingEquiv
    X.ringCatSheaf (Vi.1 ⊓ Vj.1)).injective
  refine Eq.trans (overUnitScalarEnd_transitionUnit (Vi.1 ⊓ Vj.1) _ _) ?_
  exact idealTriv_restrict_inv_comp_hom J Vi Vj fi fj hspani hnzdi hfmemi
    hspanj hnzdj hfmemj u hu

/-- **(U5-L1a 3c-iii C-rest-3b)** `overTrivializationOfRestrictIso` splits along a
factorisation of the restrict-side trivialisation: the prefix becomes the general
over-iso, the tail the over-trivialisation. This is the leg-wise decomposition of the
five-chain's over-form. -/
theorem overTrivializationOfRestrictIso_trans {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (φ : M.restrict U.ι ≅ N.restrict U.ι)
    (e : N.restrict U.ι ≅ unitObj U.toScheme) :
    Scheme.Modules.overTrivializationOfRestrictIso M U (φ ≪≫ e) =
      overIsoOfRestrictIso M N U φ ≪≫
        Scheme.Modules.overTrivializationOfRestrictIso N U e := by
  refine Iso.ext ?_
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp only [Scheme.Modules.overTrivializationOfRestrictIso, overIsoOfRestrictIso,
    Iso.trans_hom, Functor.FullyFaithful.preimageIso_hom, Functor.map_comp,
    Functor.FullyFaithful.map_preimage]
  simp [Category.assoc]

/-- The opposite of the top open is initial in `(Opens X)ᵒᵖ`: the arrow-supply of the
central-scalar principle (its `to`-arrows land at literal objects, with `hom_ext`
killing every spelling mismatch). -/
noncomputable def isInitialOpTop (X : Scheme.{u}) :
    Limits.IsInitial (Opposite.op (⊤ : X.Opens)) :=
  Limits.initialOpOfTerminal
    (Limits.IsTerminal.ofUniqueHom (fun _ => homOfLE le_top)
      (fun _ _ => Subsingleton.elim _ _))

/-- **(U5-L1a 3c-iii, the central-scalar principle — carrier)** Scaling by a global
section `r ∈ Γ(X, ⊤)` as an endomorphism of an arbitrary sheaf of modules:
componentwise `res r • ·`, with the restriction taken along the initial-object arrows
of `(Opens X)ᵒᵖ` so that every component lives at its literal open. -/
noncomputable def smulEndo {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤)) :
    M ⟶ M :=
  ⟨{ app := fun U => ModuleCat.ofHom
      { toFun := fun m => (X.ringCatSheaf.obj.map ((isInitialOpTop X).to U) r) • m
        map_add' := fun _ _ => smul_add _ _ _
        map_smul' := fun s m => by
          dsimp only [RingHom.id_apply]
          rw [← mul_smul, ← mul_smul]
          congr 1
          have hcomm : IsMulCommutative (X.ringCatSheaf.obj.obj U) := by
            change IsMulCommutative (X.presheaf.obj U)
            exact ⟨⟨fun a b => mul_comm a b⟩⟩
          exact hcomm.is_comm.comm _ _ }
     naturality := fun {U V} i => by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      show (X.ringCatSheaf.obj.map ((isInitialOpTop X).to V) r) •
          (CategoryTheory.ConcreteCategory.hom (M.val.map i)) m =
        (CategoryTheory.ConcreteCategory.hom (M.val.map i))
          ((X.ringCatSheaf.obj.map ((isInitialOpTop X).to U) r) • m)
      refine Eq.trans ?_ (M.val.map_smul i
        (X.ringCatSheaf.obj.map ((isInitialOpTop X).to U) r) m).symm
      congr 1
      rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun g =>
        (CategoryTheory.ConcreteCategory.hom (X.ringCatSheaf.obj.map g)) r)
        ((isInitialOpTop X).hom_ext _ _) }⟩

/-- The value of the scaling endomorphism (kept separate from the definition so
consumers never unfold the `IsInitial`-packaging). -/
theorem smulEndo_app_apply {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤))
    (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) (m : M.val.obj U) :
    ((smulEndo M r).val.app U).hom m =
      (X.ringCatSheaf.obj.map ((isInitialOpTop X).to U) r) • m := rfl

attribute [irreducible] isInitialOpTop smulEndo

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- **(U5-L1a 3c-iii, the central-scalar principle)** Every homomorphism of sheaf
modules commutes with the global scaling endomorphisms: each conjugation step of the
transition computation is one application of this. -/
theorem smulEndo_naturality {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    (r : Γ(X, ⊤)) :
    smulEndo M r ≫ g = g ≫ smulEndo N r := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [sheafOfModules_comp_app_apply, sheafOfModules_comp_app_apply]
  erw [smulEndo_app_apply, smulEndo_app_apply]
  exact map_smul ((g.val.app W).hom) _ x

/-- **(U5-L1a 3c-iii)** The general over-converter respects composition: the five-chain
prefix converts leg-wise. -/
theorem overIsoOfRestrictIso_trans {X : Scheme.{u}} (M N P : X.Modules) (U : X.Opens)
    (φ₁ : M.restrict U.ι ≅ N.restrict U.ι) (φ₂ : N.restrict U.ι ≅ P.restrict U.ι) :
    overIsoOfRestrictIso M P U (φ₁ ≪≫ φ₂) =
      overIsoOfRestrictIso M N U φ₁ ≪≫ overIsoOfRestrictIso N P U φ₂ := by
  refine Iso.ext ?_
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp only [overIsoOfRestrictIso, Iso.trans_hom,
    Functor.FullyFaithful.preimageIso_hom, Functor.map_comp,
    Functor.FullyFaithful.map_preimage]
  simp [Category.assoc]

/-- **(U5-L1a 3c-iii)** General over-iso restriction respects composition. -/
theorem restrictOverIso_trans {X : Scheme.{u}} (M N P : X.Modules) (U : X.Opens)
    (φ₁ : M.over U ≅ N.over U) (φ₂ : N.over U ≅ P.over U)
    (V : CategoryTheory.Over U) :
    restrictOverIso M P U (φ₁ ≪≫ φ₂) V =
      restrictOverIso M N U φ₁ V ≪≫ restrictOverIso N P U φ₂ V := by
  refine Iso.ext ?_
  simp [restrictOverIso]

/-- **(square shape-iii, leg value)** The restricted over-iso's action is the original
action at the transported object (mirror of `restrictOverTrivialization_inv_app_apply`). -/
@[simp]
theorem restrictOverIso_hom_app_apply {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : M.over U ≅ N.over U) (V : CategoryTheory.Over U)
    (Z : (CategoryTheory.Over V.left)ᵒᵖ)
    (x : ((M.over V.left)).val.obj Z) :
    (restrictOverIso M N U e V).hom.val.app Z x =
      e.hom.val.app (Opposite.op ((CategoryTheory.Over.map V.hom).obj Z.unop)) x :=
  rfl

/-- **(square shape-iii, leg value)** Inverse direction. -/
@[simp]
theorem restrictOverIso_inv_app_apply {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : M.over U ≅ N.over U) (V : CategoryTheory.Over U)
    (Z : (CategoryTheory.Over V.left)ᵒᵖ)
    (x : ((N.over V.left)).val.obj Z) :
    (restrictOverIso M N U e V).inv.val.app Z x =
      e.inv.val.app (Opposite.op ((CategoryTheory.Over.map V.hom).obj Z.unop)) x :=
  rfl

/-- **(U5-L1a 3c-iii)** Restriction respects composition of over-site isos with a
trivialisation tail: the five-chain's over-form restricts leg-wise. -/
theorem restrictOverTrivialization_comp_iso {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (φ : M.over U ≅ N.over U)
    (e : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : CategoryTheory.Over U) :
    SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U (φ ≪≫ e) V =
      restrictOverIso M N U φ V ≪≫
        SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U e V := by
  refine Iso.ext ?_
  simp [SheafOfModules.restrictOverTrivialization, restrictOverIso]

/-- **(U5-L1a 3c-iii, the five-chain prefix)** Everything in the chart trivialisation
before the final generator division, as a definite restrict-site iso
`M|_V ≅ I₂|_V`. Chart-dependence enters only through the `J₁`-leg (its generator
trivialisation); the `J₂`-generator lives in the factorisation's tail. -/
noncomputable def tensorChainPrefix {X : Scheme.{u}}
    (M : X.Modules) (J₁ J₂ : X.IdealSheafData)
    (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (V : X.affineOpens) (f₁ : Γ(X, V.1))
    (hspan₁ : J₁.ideal V = Ideal.span {f₁}) (hnzd₁ : f₁ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₁ : f₁ ∈ idealSections J₁ (Opposite.op V.1)) :
    M.restrict V.1.ι ≅ (idealModule J₂).restrict V.1.ι :=
  (restrictFunctorIsoPullback V.1.ι).app M ≪≫
    (tensorObjUnitIso ((Scheme.Modules.pullback V.1.ι).obj M)).symm ≪≫
    tensorObjCongr (Iso.refl _)
      (pullbackIdealTrivOfPrincipal J₁ V f₁ hspan₁ hnzd₁ hfmem₁).symm ≪≫
    (pullbackTensorObjIsoOfIsOpenImmersion V.1.ι M (idealModule J₁)).symm ≪≫
    (Scheme.Modules.pullback V.1.ι).mapIso e ≪≫
    (restrictFunctorIsoPullback V.1.ι).symm.app (idealModule J₂)

/-- **(U5-L1a 3c-iii, the five-chain factorisation)** The chart trivialisation's
restrict-side form factors as the chain prefix followed by the generator division:
the input shape for the leg-wise transition computation. -/
theorem restrictIsoOfPullbackIso_pullbackTrivOfTensorIdeal {X : Scheme.{u}}
    (M : X.Modules) (J₁ J₂ : X.IdealSheafData)
    (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (V : X.affineOpens) (f₁ f₂ : Γ(X, V.1))
    (hspan₁ : J₁.ideal V = Ideal.span {f₁}) (hnzd₁ : f₁ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₁ : f₁ ∈ idealSections J₁ (Opposite.op V.1))
    (hspan₂ : J₂.ideal V = Ideal.span {f₂}) (hnzd₂ : f₂ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₂ : f₂ ∈ idealSections J₂ (Opposite.op V.1)) :
    restrictIsoOfPullbackIso M V.1
        (pullbackTrivOfTensorIdeal M J₁ J₂ e V f₁ f₂ hspan₁ hnzd₁ hfmem₁
          hspan₂ hnzd₂ hfmem₂) =
      tensorChainPrefix M J₁ J₂ e V f₁ hspan₁ hnzd₁ hfmem₁ ≪≫
        haveI := isIso_idealGenHom_of_principal J₂ V f₂ hspan₂ hnzd₂ hfmem₂
        (asIso (idealGenHom J₂ V.1 f₂ hfmem₂)).symm := by
  haveI := isIso_idealGenHom_of_principal J₂ V f₂ hspan₂ hnzd₂ hfmem₂
  refine Iso.ext ?_
  simp [restrictIsoOfPullbackIso, pullbackTrivOfTensorIdeal, tensorChainPrefix,
    pullbackIdealTrivOfPrincipal, Category.assoc]

/-- **(U5-L1a 3c-iii RUNG-1a)** The over-site scaling endomorphism of an arbitrary
module by a section over the base open (the general-`M` sibling of
`overUnitScalarEnd`): componentwise `res r • ·` along the over-structure arrows. -/
noncomputable def overSmulEndo {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) : (M.over U) ⟶ (M.over U) :=
  ⟨{ app := fun W => ModuleCat.ofHom
      { toFun := fun m =>
          (X.ringCatSheaf.obj.map (Opposite.unop W).hom.op r) • m
        map_add' := fun _ _ => smul_add _ _ _
        map_smul' := fun s m => by
          dsimp only [RingHom.id_apply]
          rw [← mul_smul, ← mul_smul]
          congr 1
          have hcomm : IsMulCommutative
              (X.ringCatSheaf.obj.obj (Opposite.op (Opposite.unop W).left)) := by
            change IsMulCommutative (X.presheaf.obj (Opposite.op (Opposite.unop W).left))
            exact ⟨⟨fun a b => mul_comm a b⟩⟩
          exact hcomm.is_comm.comm _ _ }
     naturality := fun {W W'} i => by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      show (X.ringCatSheaf.obj.map (Opposite.unop W').hom.op r) •
          (CategoryTheory.ConcreteCategory.hom ((M.over U).val.map i)) m =
        (CategoryTheory.ConcreteCategory.hom ((M.over U).val.map i))
          ((X.ringCatSheaf.obj.map (Opposite.unop W).hom.op r) • m)
      refine Eq.trans ?_ ((M.over U).val.map_smul i
        (X.ringCatSheaf.obj.map (Opposite.unop W).hom.op r) m).symm
      congr 1
      change (CategoryTheory.ConcreteCategory.hom
          (X.ringCatSheaf.obj.map (Opposite.unop W').hom.op)) r =
        (CategoryTheory.ConcreteCategory.hom
          (X.ringCatSheaf.obj.map i.unop.left.op))
          ((CategoryTheory.ConcreteCategory.hom
            (X.ringCatSheaf.obj.map (Opposite.unop W).hom.op)) r)
      have h1 : (Opposite.unop W').hom.op =
          (Opposite.unop W).hom.op ≫ i.unop.left.op := Subsingleton.elim _ _
      rw [h1, Functor.map_comp]
      rfl }⟩

/-- The value of the over-site scaling endomorphism. -/
theorem overSmulEndo_app_apply {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (W : (CategoryTheory.Over U)ᵒᵖ) (m : (M.over U).val.obj W) :
    ((overSmulEndo M U r).val.app W).hom m =
      (X.ringCatSheaf.obj.map (Opposite.unop W).hom.op r) • m := rfl

/-- **(U5-L1a 3c-iii RUNG-1b)** Every over-site module homomorphism commutes with the
over-site scaling endomorphisms. -/
theorem overSmulEndo_naturality {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)
    (g : M.over U ⟶ N.over U) (r : Γ(X, U)) :
    overSmulEndo M U r ≫ g = g ≫ overSmulEndo N U r := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [sheafOfModules_comp_app_apply, sheafOfModules_comp_app_apply]
  erw [overSmulEndo_app_apply, overSmulEndo_app_apply]
  exact map_smul ((g.val.app W).hom) _ x

/-- **(U5-L1a 3c-iii RUNG-1e)** On the unit module the over-site scaling coincides with
`overUnitScalarEnd` (left- vs right-multiplication, commutativity). -/
theorem overSmulEndo_unit {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    overSmulEndo (unitObj X) U r =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [overSmulEndo_app_apply, SheafOfModules.overUnitScalarEnd_app_apply]
  dsimp only
  have hcomm : IsMulCommutative
      (X.ringCatSheaf.obj.obj (Opposite.op (Opposite.unop W).left)) := by
    change IsMulCommutative (X.presheaf.obj (Opposite.op (Opposite.unop W).left))
    exact ⟨⟨fun a b => mul_comm a b⟩⟩
  exact hcomm.is_comm.comm _ _

/-- **(U5-L1a 3c-iii C-algebra)** `tensorObjCongr` respects identities. Natural home
after cleanup: `Picard/InvertibleSheaf.lean`. -/
theorem tensorObjCongr_refl {X : Scheme.{u}} (M N : X.Modules) :
    tensorObjCongr (Iso.refl M) (Iso.refl N) = Iso.refl (tensorObj M N) := by
  simp [tensorObjCongr, Iso.ext_iff]
  rfl

/-- **(U5-L1a 3c-iii C-algebra)** `tensorObjCongr` respects inversion. -/
theorem tensorObjCongr_symm {X : Scheme.{u}} {M M' N N' : X.Modules}
    (eM : M ≅ M') (eN : N ≅ N') :
    (tensorObjCongr eM eN).symm = tensorObjCongr eM.symm eN.symm := by
  simp [tensorObjCongr, Iso.ext_iff]

/-- **(U5-L1a 3c-iii C-algebra)** `tensorObjCongr` respects composition — the shared-leg
cancellation input of the transition computation. -/
theorem tensorObjCongr_trans {X : Scheme.{u}} {M M' M'' N N' N'' : X.Modules}
    (e₁ : M ≅ M') (e₂ : M' ≅ M'') (f₁ : N ≅ N') (f₂ : N' ≅ N'') :
    tensorObjCongr (e₁ ≪≫ e₂) (f₁ ≪≫ f₂) =
      tensorObjCongr e₁ f₁ ≪≫ tensorObjCongr e₂ f₂ := by
  simp [tensorObjCongr, Iso.ext_iff,
    ← MonoidalCategory.tensorHom_comp_tensorHom]

/-! ### The M-chain transition ([C-rest-3], route C: chart-dependent characterisation)

The transition unit of the tensor-ideal chart trivialisations is `u₂ · u₁⁻¹`, read off
from characterisations against the chart-dependent comparison map `ν` (the
`(· ⊗ f₁)`-insertion followed by the dictionary and the ideal inclusion). The skeleton
below follows `.mathlib-quality/decomposition-e4a-self.md` ([C-rest-3] ROUTE LOCKED). -/

/-- **([C-rest-3] SK-normal)** The restrict-side restriction of a pullback-bridge
trivialisation is the pullback-bridge of the pullback-side restriction: `rOT` and
`restrictTrivialization` correspond under `restrictIsoOfPullbackIso`. -/
theorem restrictOpenTrivialization_restrictIsoOfPullbackIso {X : Scheme.{u}}
    (M : X.Modules) {V W : X.Opens} (hWV : W ≤ V)
    (t : (Scheme.Modules.pullback V.ι).obj M ≅ unitObj V.toScheme) :
    Scheme.Modules.restrictOpenTrivialization hWV (restrictIsoOfPullbackIso M V t) =
      restrictIsoOfPullbackIso M W (restrictTrivialization hWV t) := by
  rw [Scheme.Modules.restrictOpenTrivialization_eq_pullback]
  simp only [Scheme.Modules.restrictOpenTrivializationPullback,
    restrictIsoOfPullbackIso]
  congr 1
  have hpair : (restrictFunctorIsoPullback V.ι).symm.app M ≪≫
      (restrictFunctorIsoPullback V.ι).app M =
      Iso.refl ((Scheme.Modules.pullback V.ι).obj M) :=
    Iso.ext (Iso.inv_hom_id_app (restrictFunctorIsoPullback V.ι) M)
  exact (congrArg (fun q => restrictTrivialization hWV (q ≪≫ t)) hpair).trans
    (congrArg (restrictTrivialization hWV) (Iso.refl_trans t))

/-- **([C-rest-3] SK-triv)** The pullback-side ideal trivialisation from an
iso-generator at an arbitrary open (the non-affine sibling of
`pullbackIdealTrivOfPrincipal`; at the overlap the generator hypothesis arrives as
`IsIso` transported from the affine charts). -/
noncomputable def pullbackIdealTrivOfGen {X : Scheme.{u}} (J : X.IdealSheafData)
    (W : X.Opens) (g : Γ(X, W)) (hg : g ∈ idealSections J (Opposite.op W))
    (hgi : IsIso (idealGenHom J W g hg)) :
    (Scheme.Modules.pullback W.ι).obj (idealModule J) ≅ unitObj W.toScheme :=
  letI := hgi
  (restrictFunctorIsoPullback W.ι).symm.app (idealModule J) ≪≫
    (asIso (idealGenHom J W g hg)).symm

/-- **([C-rest-3] SK-slot)** The `⊗`-slot iso at the overlap: the tensor-unit collapse
followed by the generator trivialisation in the ideal slot and the monoidal comparison —
the chart-independent-shape prefix of the five-chain, at `W` with generator `g`. -/
noncomputable def tensorIdealSlotIso {X : Scheme.{u}} (M : X.Modules)
    (J₁ : X.IdealSheafData) (W : X.Opens) (g : Γ(X, W))
    (hg : g ∈ idealSections J₁ (Opposite.op W))
    (hgi : IsIso (idealGenHom J₁ W g hg)) :
    (Scheme.Modules.pullback W.ι).obj M ≅
      (Scheme.Modules.pullback W.ι).obj (tensorObj M (idealModule J₁)) :=
  (tensorObjUnitIso ((Scheme.Modules.pullback W.ι).obj M)).symm ≪≫
    tensorObjCongr (Iso.refl _) (pullbackIdealTrivOfGen J₁ W g hg hgi).symm ≪≫
    (pullbackTensorObjIsoOfIsOpenImmersion W.ι M (idealModule J₁)).symm

/-- **([C-rest-3] SK-ν)** The chart's comparison map at the overlap: insert the
generator in the `⊗`-slot, apply the dictionary, include the ideal, collapse the unit.
Chart-dependence enters only through `g`. -/
noncomputable def nuPullback {X : Scheme.{u}} (M : X.Modules)
    (J₁ J₂ : X.IdealSheafData) (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (W : X.Opens) (g : Γ(X, W)) (hg : g ∈ idealSections J₁ (Opposite.op W))
    (hgi : IsIso (idealGenHom J₁ W g hg)) :
    (Scheme.Modules.pullback W.ι).obj M ⟶ unitObj W.toScheme :=
  (tensorIdealSlotIso M J₁ W g hg hgi).hom ≫
    (Scheme.Modules.pullback W.ι).map e.hom ≫
    (Scheme.Modules.pullback W.ι).map (idealModuleToUnitHom J₂) ≫
    (pullbackUnitIso W.ι).hom

/-- **([C-rest-3] SK-ratio-1)** Hom-level packaging of `idealGenHom_mul_app`:
multiplying the generator by a section factors as the scalar endomorphism followed by
the original generator map. -/
theorem idealGenHom_mul {X : Scheme.{u}} (J : X.IdealSheafData) (V : X.Opens)
    (f u : Γ(X, V))
    (hm₁ : f * u ∈ idealSections J (Opposite.op V))
    (hm₂ : f ∈ idealSections J (Opposite.op V)) :
    idealGenHom J V (f * u) hm₁ =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection V u) ≫ idealGenHom J V f hm₂ := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact idealGenHom_mul_app J V f u hm₁ hm₂ Y a

/-- **([C-rest-3] RUNG-1e-restrict)** At the unit, the central scalar endomorphism is
multiplication by the top section (`mul_comm` modulo the initial-object arrow). -/
theorem smulEndo_unitObj {Y : Scheme.{u}} (r : Γ(Y, (⊤ : Y.Opens))) :
    smulEndo (unitObj Y) r = ModularCurves.unitEndomorphismOfTopSection r := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [smulEndo_app_apply]
  erw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  have harr := congrArg (fun (a : Opposite.op (⊤ : Y.Opens) ⟶ U) =>
    (CategoryTheory.ConcreteCategory.hom (Y.ringCatSheaf.obj.map a)) r)
    (Subsingleton.elim ((isInitialOpTop Y).to U)
      (homOfLE (le_top : U.unop ≤ ⊤)).op)
  refine (congrArg (fun t => t • x) harr).trans ?_
  exact mul_comm (G := Γ(Y, U.unop)) _ _

/-- **([C-rest-3] RUNG-1c, THE TENSOR-MEETS-SCALAR ATOM)** Whiskering the unit-slot
scalar through the sheafified tensor is the central scalar endomorphism of the tensor:
the one place the `⊗`-slot meets the scalar action. Proven by the sheafification
adjunction, `TensorProduct.induction_on`, and a base-ring re-typing of the scalar. -/
theorem sheafificationMap_whiskerLeft_unitEndomorphism {Y : Scheme.{u}}
    (A : Y.Modules) (r : Γ(Y, (⊤ : Y.Opens))) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
        (MonoidalCategoryStruct.whiskerLeft A.val
          (ModularCurves.unitEndomorphismOfTopSection r).val) =
      smulEndo (tensorObj A (unitObj Y)) r := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).unit.naturality
    (MonoidalCategoryStruct.whiskerLeft A.val
      (ModularCurves.unitEndomorphismOfTopSection r).val)
  refine Eq.trans (Eq.trans ?_ hnat.symm) ?_
  · rfl
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  refine LinearMap.ext ?_
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
      simp only [Functor.id_map, PresheafOfModules.comp_app, ModuleCat.hom_comp,
        LinearMap.comp_apply]
      erw [PresheafOfModules.whiskerLeft_app]
      erw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
      erw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
      erw [smulEndo_app_apply]
      have hswap := congrArg (fun (i : Opposite.op (⊤ : Y.Opens) ⟶ U) =>
        (CategoryTheory.ConcreteCategory.hom (Y.ringCatSheaf.obj.map i)) r •
          (ModuleCat.Hom.hom
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 Y.ringCatSheaf.obj)).unit.app
                (MonoidalCategoryStruct.tensorObj A.val (unitObj Y).val)).app U))
            (x ⊗ₜ a))
        (Subsingleton.elim ((isInitialOpTop Y).to U)
          (homOfLE (le_top : U.unop ≤ ⊤)).op)
      refine Eq.trans ?_ hswap.symm
      refine Eq.trans ?_ (LinearMap.map_smul
        (ModuleCat.Hom.hom
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 Y.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj A.val (unitObj Y).val)).app U)) _ _)
      refine congrArg (ModuleCat.Hom.hom
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val (unitObj Y).val)).app U)) ?_
      refine Eq.trans (congrArg (fun t => x ⊗ₜ t) ?_) (TensorProduct.tmul_smul
        (show ↑(((sheafToPresheaf (Opens.grothendieckTopology ↥Y) CommRingCat).obj
            Y.sheaf ⋙ forget₂ CommRingCat RingCat).obj U) from
          (CategoryTheory.ConcreteCategory.hom
            (Y.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op)) r) x a)
      exact mul_comm (G := Γ(Y, U.unop)) _ _
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- **([C-rest-3] SK-B2-restrict)** The restrict-side sibling of
`mono_overUnitScalarEnd_of_nonZeroDivisors`: multiplication by a non-zero-divisor
section is a mono endomorphism of the structure sheaf. Supplies the `cancel_mono` of
the transition read-off. -/
theorem mono_unitEndomorphismOfTopSection_of_nonZeroDivisors {X : Scheme.{u}}
    (W : X.Opens) (r : Γ(X, W))
    (hr : ∀ (Z : W.toScheme.Opens),
      W.toScheme.presheaf.map (homOfLE (le_top : Z ≤ ⊤)).op
        (Scheme.Modules.openTopSection W r) ∈ nonZeroDivisors Γ(W.toScheme, Z)) :
    Mono (ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W r)) := by
  constructor
  intro Z g₁ g₂ hgg
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have happ := congrArg (fun q => (CategoryTheory.ConcreteCategory.hom
    (q.val.app Y)) x) hgg
  erw [sheafOfModules_comp_app_apply, sheafOfModules_comp_app_apply] at happ
  erw [ModularCurves.unitEndomorphismOfTopSection_app_apply,
    ModularCurves.unitEndomorphismOfTopSection_app_apply] at happ
  dsimp only at happ
  exact (mul_cancel_right_mem_nonZeroDivisors (hr Y.unop)).mp happ

/-- **([C-rest-3] N-native)** The overlap-native tensor-ideal trivialisation: the slot
iso followed by the dictionary and the `J₂`-generator division, all at `W` with the
restricted generators. The transition middle-man of the native-middle route. -/
noncomputable def nativeTensorIdealTriv {X : Scheme.{u}} (M : X.Modules)
    (J₁ J₂ : X.IdealSheafData) (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (W : X.Opens) (g₁ g₂ : Γ(X, W))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁ : IsIso (idealGenHom J₁ W g₁ hg₁))
    (hg₂ : g₂ ∈ idealSections J₂ (Opposite.op W))
    (hgi₂ : IsIso (idealGenHom J₂ W g₂ hg₂)) :
    (Scheme.Modules.pullback W.ι).obj M ≅ unitObj W.toScheme :=
  tensorIdealSlotIso M J₁ W g₁ hg₁ hgi₁ ≪≫
    (Scheme.Modules.pullback W.ι).mapIso e ≪≫
    pullbackIdealTrivOfGen J₂ W g₂ hg₂ hgi₂

/-- **([C-rest-3] N1)** The `W`-level `A1`-sibling: the generator trivialisation's
inverse followed by the ideal inclusion and the unit collapse is multiplication by the
generator. Concrete: `idealGenHom`'s app formula against `Subtype.val`. -/
theorem pullbackIdealTrivOfGen_inv_comp_toUnit {X : Scheme.{u}}
    (J : X.IdealSheafData) (W : X.Opens) (g : Γ(X, W))
    (hg : g ∈ idealSections J (Opposite.op W))
    (hgi : IsIso (idealGenHom J W g hg)) :
    (pullbackIdealTrivOfGen J W g hg hgi).inv ≫
        (Scheme.Modules.pullback W.ι).map (idealModuleToUnitHom J) ≫
        (pullbackUnitIso W.ι).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W g) := by
  sorry

/-- **([C-rest-3] N2-cancel)** The native trivialisation's characterisation against
`ν`: the shared slot/dictionary prefix cancels and only the `N1`-tail remains. Pure
iso-algebra plus `N1`. -/
theorem nativeTensorIdealTriv_inv_comp_nu {X : Scheme.{u}} (M : X.Modules)
    (J₁ J₂ : X.IdealSheafData) (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (W : X.Opens) (g₁ g₂ : Γ(X, W))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁ : IsIso (idealGenHom J₁ W g₁ hg₁))
    (hg₂ : g₂ ∈ idealSections J₂ (Opposite.op W))
    (hgi₂ : IsIso (idealGenHom J₂ W g₂ hg₂)) :
    (nativeTensorIdealTriv M J₁ J₂ e W g₁ g₂ hg₁ hgi₁ hg₂ hgi₂).inv ≫
        nuPullback M J₁ J₂ e W g₁ hg₁ hgi₁ =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W g₂) := by
  simp only [nativeTensorIdealTriv, nuPullback, Iso.trans_inv, Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact pullbackIdealTrivOfGen_inv_comp_toUnit J₂ W g₂ hg₂ hgi₂

/-- **([C-rest-3] H3-τ)** The two-step-to-one-step pullback transport at an object:
the composition iso followed by the congruence to the direct inclusion pullback. The
frame through which the per-chart chase's V-data reaches the overlap. -/
noncomputable def pullbackRestrictTransport {X : Scheme.{u}} {V W : X.Opens}
    (hWV : W ≤ V) (A : X.Modules) :
    (Scheme.Modules.pullback (X.homOfLE hWV)).obj
      ((Scheme.Modules.pullback V.ι).obj A) ⟶
      (Scheme.Modules.pullback W.ι).obj A :=
  (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom) ≫
    (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app A).inv)

/-- **([C-rest-3] H3-τ-nat)** The transport is natural: a global map walks through it
from the two-step to the one-step pullback. Handles every map-leg of the per-chart
chase in one stroke. -/
theorem pullbackRestrictTransport_naturality {X : Scheme.{u}} {V W : X.Opens}
    (hWV : W ≤ V) {A B : X.Modules} (q : A ⟶ B) :
    (Scheme.Modules.pullback (X.homOfLE hWV)).map
        ((Scheme.Modules.pullback V.ι).map q) ≫
      pullbackRestrictTransport hWV B =
    pullbackRestrictTransport hWV A ≫ (Scheme.Modules.pullback W.ι).map q := by
  have h1' : (Scheme.Modules.pullback (X.homOfLE hWV)).map
      ((Scheme.Modules.pullback V.ι).map q) ≫
      ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app B).hom =
      ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom ≫
      (Scheme.Modules.pullback (X.homOfLE hWV ≫ V.ι)).map q :=
    ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).hom).naturality q
  have h2' : (Scheme.Modules.pullback (X.homOfLE hWV ≫ V.ι)).map q ≫
      ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app B).inv =
      ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app A).inv ≫
      (Scheme.Modules.pullback W.ι).map q :=
    ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).inv).naturality q
  simp only [pullbackRestrictTransport]
  exact (congrArg (fun t => t ≫
      ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app B).inv) h1').trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t =>
        ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom ≫ t) h2').trans
        (Category.assoc _ _ _).symm))

/-- **([C-rest-3] H3-S)** The slot iso commutes with the pullback transport: the
overlap's slot at the restricted generator, precomposed with the transport, is the
pullback of the chart's slot followed by the transport at the tensor. The merged
tensor-transport coherence of the per-chart chase (subsumes the tensor-unit, generator,
and monoidal legs in one adjunction-transposable square). -/
theorem pullbackRestrictTransport_tensorIdealSlotIso {X : Scheme.{u}}
    (M : X.Modules) (J₁ : X.IdealSheafData) {V W : X.Opens} (hWV : W ≤ V)
    (g : Γ(X, V)) (hgV : g ∈ idealSections J₁ (Opposite.op V))
    (hgiV : IsIso (idealGenHom J₁ V g hgV))
    (hgW : X.presheaf.map (homOfLE hWV).op g ∈ idealSections J₁ (Opposite.op W))
    (hgiW : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g) hgW)) :
    pullbackRestrictTransport hWV M ≫
        (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g)
          hgW hgiW).hom =
      (Scheme.Modules.pullback (X.homOfLE hWV)).map
          (tensorIdealSlotIso M J₁ V g hgV hgiV).hom ≫
        pullbackRestrictTransport hWV (tensorObj M (idealModule J₁)) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (X.homOfLE hWV)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  sorry

/-- **([C-rest-3] H3-T1)** The tensor comparison commutes with pullback composition:
the open-immersion monoidal comparison for the composite is the pullback of the inner
comparison conjugated by the composition isos on both factors and on the tensor.
(The one irreducible tensor-transport coherence of the per-chart chase; atom-technique.) -/
theorem pullbackTensorObjIso_comp {X : Scheme.{u}} {Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    [IsOpenImmersion (g ≫ f)] (A B : X.Modules) :
    pullbackTensorObjIsoOfIsOpenImmersion (g ≫ f) A B =
      (Scheme.Modules.pullbackComp g f).symm.app (tensorObj A B) ≪≫
        (Scheme.Modules.pullback g).mapIso
          (pullbackTensorObjIsoOfIsOpenImmersion f A B) ≪≫
        pullbackTensorObjIsoOfIsOpenImmersion g
          ((Scheme.Modules.pullback f).obj A)
          ((Scheme.Modules.pullback f).obj B) ≪≫
        tensorObjCongr ((Scheme.Modules.pullbackComp g f).app A)
          ((Scheme.Modules.pullbackComp g f).app B) := by
  sorry

/-- **([C-rest-3] H2)** The restricted trivialisation's inverse at the top section:
the pullback-transported trivialising section of the chart, `eqToHom`-corrected. The
inversion tool (`sheafIso_inv_app_eq_of_hom_app_eqT`) plus the η-transport family. -/
theorem restrictTrivialization_inv_app_top_one {X : Scheme.{u}} {P : X.Modules}
    {U W' : X.Opens} (hWU : W' ≤ U)
    (t : (Scheme.Modules.pullback U.ι).obj P ≅ unitObj U.toScheme)
    (htop : (⊤ : W'.toScheme.Opens) = (X.homOfLE hWU) ⁻¹ᵁ (⊤ : U.toScheme.Opens)) :
    (restrictTrivialization hWU t).inv.val.app
        (Opposite.op (⊤ : W'.toScheme.Opens))
        (show W'.toScheme.presheaf.obj (Opposite.op (⊤ : W'.toScheme.Opens))
          from 1) =
      ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWU).symm).app P).inv.val.app
        (Opposite.op (⊤ : W'.toScheme.Opens))
        (((Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).app P).hom.val.app
          (Opposite.op (⊤ : W'.toScheme.Opens))
          (((Scheme.Modules.pullback (X.homOfLE hWU)).obj
              ((Scheme.Modules.pullback U.ι).obj P)).presheaf.map (eqToHom htop).op
            (((Scheme.Modules.pullbackPushforwardAdjunction
                (X.homOfLE hWU)).unit.app
              ((Scheme.Modules.pullback U.ι).obj P)).val.app
              (Opposite.op (⊤ : U.toScheme.Opens))
              (t.inv.val.app (Opposite.op (⊤ : U.toScheme.Opens))
                (show U.toScheme.presheaf.obj
                  (Opposite.op (⊤ : U.toScheme.Opens)) from 1))))) := by
  refine sheafIso_inv_app_eq_of_hom_app_eqT _ _ _ _ ?_
  simp only [restrictTrivialization, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  erw [sheafOfModules_comp_app_apply, sheafOfModules_comp_app_apply,
    sheafOfModules_comp_app_apply]
  have g1 := congrArg (fun w => (CategoryTheory.ConcreteCategory.hom ((pullbackUnitIso (X.homOfLE hWU)).hom.val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) ((CategoryTheory.ConcreteCategory.hom (((Scheme.Modules.pullback (X.homOfLE hWU)).map t.hom).val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) ((CategoryTheory.ConcreteCategory.hom (((Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).app P).inv.val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) w)))
    (iso_inv_hom_app_applyT ((Scheme.Modules.pullbackCongr
      (X.homOfLE_ι hWU).symm).app P) (Opposite.op (⊤ : W'.toScheme.Opens)) ((((Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).app P).hom.val.app (Opposite.op (⊤ : W'.toScheme.Opens))) ((((Scheme.Modules.pullback (X.homOfLE hWU)).obj ((Scheme.Modules.pullback U.ι).obj P)).presheaf.map (eqToHom htop).op) (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWU)).unit.app ((Scheme.Modules.pullback U.ι).obj P)).val.app (Opposite.op (⊤ : U.toScheme.Opens)) (t.inv.val.app (Opposite.op (⊤ : U.toScheme.Opens)) (show U.toScheme.presheaf.obj (Opposite.op (⊤ : U.toScheme.Opens)) from 1))))))
  have g2 := congrArg (fun w => (CategoryTheory.ConcreteCategory.hom ((pullbackUnitIso (X.homOfLE hWU)).hom.val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) ((CategoryTheory.ConcreteCategory.hom (((Scheme.Modules.pullback (X.homOfLE hWU)).map t.hom).val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) w))
    (iso_hom_inv_app_applyT ((Scheme.Modules.pullbackComp
      (X.homOfLE hWU) U.ι).app P) (Opposite.op (⊤ : W'.toScheme.Opens)) ((((Scheme.Modules.pullback (X.homOfLE hWU)).obj ((Scheme.Modules.pullback U.ι).obj P)).presheaf.map (eqToHom htop).op) (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWU)).unit.app ((Scheme.Modules.pullback U.ι).obj P)).val.app (Opposite.op (⊤ : U.toScheme.Opens)) (t.inv.val.app (Opposite.op (⊤ : U.toScheme.Opens)) (show U.toScheme.presheaf.obj (Opposite.op (⊤ : U.toScheme.Opens)) from 1)))))
  have g3 := congrArg (fun w => (CategoryTheory.ConcreteCategory.hom ((pullbackUnitIso (X.homOfLE hWU)).hom.val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) w)
    (pullbackUnit_map_transportT (X.homOfLE hWU) t.hom ⊤ ⊤ htop (t.inv.val.app (Opposite.op (⊤ : U.toScheme.Opens)) (show U.toScheme.presheaf.obj (Opposite.op (⊤ : U.toScheme.Opens)) from 1)))
  have g4 := congrArg (fun w => (CategoryTheory.ConcreteCategory.hom ((pullbackUnitIso (X.homOfLE hWU)).hom.val.app (Opposite.op (⊤ : W'.toScheme.Opens)))) ((CategoryTheory.ConcreteCategory.hom ((((Scheme.Modules.pullback (X.homOfLE hWU)).obj (unitObj U.toScheme)).presheaf.map (eqToHom htop).op))) (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWU)).unit.app (unitObj U.toScheme)).val.app (Opposite.op (⊤ : U.toScheme.Opens)) w)))
    (iso_inv_hom_app_applyT t (Opposite.op (⊤ : U.toScheme.Opens)) (show U.toScheme.presheaf.obj (Opposite.op (⊤ : U.toScheme.Opens)) from 1))
  have g5 := PresheafOfModules.naturality_apply
    (pullbackUnitIso (X.homOfLE hWU)).hom.val (eqToHom htop).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWU)).unit.app
      (unitObj U.toScheme)).val.app (Opposite.op (⊤ : U.toScheme.Opens))
      (show U.toScheme.presheaf.obj (Opposite.op (⊤ : U.toScheme.Opens)) from 1))
  have g6 := congrArg
    (CategoryTheory.ConcreteCategory.hom
      ((unitObj W'.toScheme).val.map (eqToHom htop).op))
    (pullbackUnitIso_hom_unit_oneT (X.homOfLE hWU))
  have g7 : (CategoryTheory.ConcreteCategory.hom
      (W'.toScheme.presheaf.map (eqToHom htop).op))
      (show W'.toScheme.presheaf.obj
        (Opposite.op ((X.homOfLE hWU) ⁻¹ᵁ (⊤ : U.toScheme.Opens))) from 1) =
      (show W'.toScheme.presheaf.obj
        (Opposite.op (⊤ : W'.toScheme.Opens)) from 1) :=
    map_one (CategoryTheory.ConcreteCategory.hom
      (W'.toScheme.presheaf.map (eqToHom htop).op))
  exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans g7)))))

/-- **([C-rest-3] SK-per-chart)** The per-chart characterisation: the restricted
five-chain trivialisation composed with the chart's `ν` is multiplication by the
restricted `J₂`-generator. All cancellations are within one chart. -/
theorem restrictTrivialization_pullbackTrivOfTensorIdeal_inv_comp_nu {X : Scheme.{u}}
    (M : X.Modules) (J₁ J₂ : X.IdealSheafData)
    (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (V : X.affineOpens) (f₁ f₂ : Γ(X, V.1))
    (hspan₁ : J₁.ideal V = Ideal.span {f₁}) (hnzd₁ : f₁ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₁ : f₁ ∈ idealSections J₁ (Opposite.op V.1))
    (hspan₂ : J₂.ideal V = Ideal.span {f₂}) (hnzd₂ : f₂ ∈ nonZeroDivisors Γ(X, V.1))
    (hfmem₂ : f₂ ∈ idealSections J₂ (Opposite.op V.1))
    {W : X.Opens} (hWV : W ≤ V.1)
    (hg : X.presheaf.map (homOfLE hWV).op f₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op f₁) hg)) :
    (restrictTrivialization hWV (pullbackTrivOfTensorIdeal M J₁ J₂ e V f₁ f₂
        hspan₁ hnzd₁ hfmem₁ hspan₂ hnzd₂ hfmem₂)).inv ≫
      nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op f₁) hg hgi =
    ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op f₂)) := by
  -- Value-route (grind-plan in decomposition-e4a-self.md): both sides are unit-source
  -- homs, determined by their `unitHomEquiv`-section; the RHS's section is free.
  apply (_root_.SheafOfModules.unit
    (W.toScheme.ringCatSheaf)).unitHomEquiv.injective
  rw [_root_.SheafOfModules.unitHomEquiv_comp_apply]
  refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
  have htop : (_root_.SheafOfModules.sectionsMap
        (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op f₁) hg hgi)
        ((_root_.SheafOfModules.unitHomEquiv
          ((Scheme.Modules.pullback W.ι).obj M))
          (restrictTrivialization hWV (pullbackTrivOfTensorIdeal M J₁ J₂ e V f₁ f₂
            hspan₁ hnzd₁ hfmem₁ hspan₂ hnzd₂ hfmem₂)).inv)).1
      (Opposite.op (⊤ : W.toScheme.Opens)) =
      (ModularCurves.moduleSectionsOfTop (unitObj W.toScheme)
        (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op f₂))).1
      (Opposite.op (⊤ : W.toScheme.Opens)) := by
    show (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op f₁) hg hgi).val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        ((restrictTrivialization hWV (pullbackTrivOfTensorIdeal M J₁ J₂ e V f₁ f₂
          hspan₁ hnzd₁ hfmem₁ hspan₂ hnzd₂ hfmem₂)).inv.val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (show W.toScheme.presheaf.obj (Opposite.op (⊤ : W.toScheme.Opens))
            from 1)) =
      (unitObj W.toScheme).val.map
        (homOfLE (le_top : (⊤ : W.toScheme.Opens) ≤ ⊤)).op
        (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op f₂))
    have h1 : (unitObj W.toScheme).val.map
        (homOfLE (le_top : (⊤ : W.toScheme.Opens) ≤ ⊤)).op
        (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op f₂)) =
        Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op f₂) := by
      rw [show (homOfLE (le_top : (⊤ : W.toScheme.Opens) ≤ ⊤)).op =
        𝟙 (Opposite.op (⊤ : W.toScheme.Opens)) from Subsingleton.elim _ _]
      simp
      erw [ModuleCat.restrictScalarsId'App_inv_apply]
    refine Eq.trans ?_ h1.symm
    have htop' : (⊤ : W.toScheme.Opens) =
        (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.1.toScheme.Opens) := rfl
    refine (congrArg (fun w =>
      (CategoryTheory.ConcreteCategory.hom
        ((nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op f₁)
          hg hgi).val.app (Opposite.op (⊤ : W.toScheme.Opens)))) w)
      (restrictTrivialization_inv_app_top_one hWV
        (pullbackTrivOfTensorIdeal M J₁ J₂ e V f₁ f₂
          hspan₁ hnzd₁ hfmem₁ hspan₂ hnzd₂ hfmem₂) htop')).trans ?_
    erw [sheafOfModules_comp_app_apply, sheafOfModules_comp_app_apply,
      sheafOfModules_comp_app_apply]
    sorry
  refine Subtype.ext (funext fun Z => ?_)
  rw [← (_root_.SheafOfModules.sectionsMap
      (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op f₁) hg hgi)
      ((_root_.SheafOfModules.unitHomEquiv
        ((Scheme.Modules.pullback W.ι).obj M))
        (restrictTrivialization hWV (pullbackTrivOfTensorIdeal M J₁ J₂ e V f₁ f₂
          hspan₁ hnzd₁ hfmem₁ hspan₂ hnzd₂ hfmem₂)).inv)).2
    ((homOfLE (le_top : Z.unop ≤ ⊤)).op)]
  rw [← (ModularCurves.moduleSectionsOfTop (unitObj W.toScheme)
      (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op f₂))).2
    ((homOfLE (le_top : Z.unop ≤ ⊤)).op)]
  exact congrArg _ htop

/-- **([C-rest-3] SK-ratio)** `ν` is linear in the inserted generator: multiplying the
generator by a section multiplies `ν` by that section (the `3c-ii`
`idealGenHom_mul_app` species lifted through the slot iso). -/
theorem nuPullback_mul {X : Scheme.{u}} (M : X.Modules)
    (J₁ J₂ : X.IdealSheafData) (e : tensorObj M (idealModule J₁) ≅ idealModule J₂)
    (W : X.Opens) (g u : Γ(X, W))
    (hgu : g * u ∈ idealSections J₁ (Opposite.op W))
    (hg : g ∈ idealSections J₁ (Opposite.op W))
    (hgui : IsIso (idealGenHom J₁ W (g * u) hgu))
    (hgi : IsIso (idealGenHom J₁ W g hg)) :
    nuPullback M J₁ J₂ e W (g * u) hgu hgui =
      nuPullback M J₁ J₂ e W g hg hgi ≫
        ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection W u) := by
  letI := hgui
  letI := hgi
  have h2core : (((restrictFunctorIsoPullback W.ι).symm.app (idealModule J₁) ≪≫
        (asIso (idealGenHom J₁ W (g * u) hgu)).symm)).inv =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W u) ≫
        (((restrictFunctorIsoPullback W.ι).symm.app (idealModule J₁) ≪≫
          (asIso (idealGenHom J₁ W g hg)).symm)).inv := by
    simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom]
    rw [idealGenHom_mul J₁ W g u hgu hg, Category.assoc]
  have h2 : (pullbackIdealTrivOfGen J₁ W (g * u) hgu hgui).inv =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W u) ≫
        (pullbackIdealTrivOfGen J₁ W g hg hgi).inv := h2core
  have hp1 : ∀ {N N' : W.toScheme.Modules} (β : N ≅ N'),
      (tensorObjCongr (Iso.refl ((Scheme.Modules.pullback W.ι).obj M)) β).hom =
        (PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)).map
          (MonoidalCategoryStruct.whiskerLeft
            ((Scheme.Modules.pullback W.ι).obj M).val β.hom.val) := by
    intro N N' β
    simp only [tensorObjCongr, Functor.mapIso_hom,
      MonoidalCategory.tensorIso_hom, Functor.mapIso_refl, Iso.refl_hom,
      MonoidalCategory.id_tensorHom]
    rfl
  have h3 : (tensorObjCongr (Iso.refl ((Scheme.Modules.pullback W.ι).obj M))
        (pullbackIdealTrivOfGen J₁ W (g * u) hgu hgui).symm).hom =
      smulEndo (tensorObj ((Scheme.Modules.pullback W.ι).obj M)
          (unitObj W.toScheme)) (Scheme.Modules.openTopSection W u) ≫
        (tensorObjCongr (Iso.refl ((Scheme.Modules.pullback W.ι).obj M))
          (pullbackIdealTrivOfGen J₁ W g hg hgi).symm).hom := by
    rw [hp1, hp1]
    rw [show ((pullbackIdealTrivOfGen J₁ W (g * u) hgu hgui).symm).hom =
      (pullbackIdealTrivOfGen J₁ W (g * u) hgu hgui).inv from rfl]
    rw [h2]
    rw [show (ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W u) ≫
        (pullbackIdealTrivOfGen J₁ W g hg hgi).inv).val =
      (ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W u)).val ≫
        (pullbackIdealTrivOfGen J₁ W g hg hgi).inv.val from rfl]
    rw [MonoidalCategory.whiskerLeft_comp, Functor.map_comp]
    rw [sheafificationMap_whiskerLeft_unitEndomorphism]
    rfl
  simp only [nuPullback, tensorIdealSlotIso, Iso.trans_hom, Category.assoc]
  rw [h3]
  simp only [Category.assoc]
  rw [smulEndo_naturality
    ((tensorObjCongr (Iso.refl ((Scheme.Modules.pullback W.ι).obj M))
        (pullbackIdealTrivOfGen J₁ W g hg hgi).symm).hom ≫
      (pullbackTensorObjIsoOfIsOpenImmersion W.ι M (idealModule J₁)).symm.hom ≫
      (Scheme.Modules.pullback W.ι).map e.hom ≫
      (Scheme.Modules.pullback W.ι).map (idealModuleToUnitHom J₂) ≫
      (pullbackUnitIso W.ι).hom) (Scheme.Modules.openTopSection W u)]
  simp only [Category.assoc, smulEndo_unitObj]

/-- **([C-rest-3] SK-read-off)** The pullback-side `C(i)-b`: two trivialisations
characterised against the same comparison map, with a scalar ratio between the
characterising sections and the smaller section's endo mono, differ by exactly the
ratio. Pure `cancel_mono` — the comparison map itself need not be mono. -/
theorem pullbackTrivialization_inv_comp_hom_of_nu {X : Scheme.{u}}
    (M : X.Modules) {W : X.Opens}
    (T₁ T₂ : (Scheme.Modules.pullback W.ι).obj M ≅ unitObj W.toScheme)
    (ν : (Scheme.Modules.pullback W.ι).obj M ⟶ unitObj W.toScheme)
    (r₁ r₂ v : Γ(X, W))
    (h₁ : T₁.inv ≫ ν = ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W r₁))
    (h₂ : T₂.inv ≫ ν = ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W r₂))
    (hr : r₁ = v * r₂)
    (hmono : Mono (ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W r₂))) :
    T₁.inv ≫ T₂.hom = ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W v) := by
  haveI := hmono
  refine (cancel_mono (ModularCurves.unitEndomorphismOfTopSection
    (Scheme.Modules.openTopSection W r₂))).mp ?_
  have htop : Scheme.Modules.openTopSection W r₁ =
      Scheme.Modules.openTopSection W v * Scheme.Modules.openTopSection W r₂ := by
    rw [hr]
    simp [Scheme.Modules.openTopSection, map_mul]
  have hsub := congrArg (fun t => T₁.inv ≫ T₂.hom ≫ t) h₂.symm
  have halg : T₁.inv ≫ T₂.hom ≫ T₂.inv ≫ ν = T₁.inv ≫ ν :=
    congrArg (fun t => T₁.inv ≫ t) (Iso.hom_inv_id_assoc T₂ ν)
  have hval : T₁.inv ≫ ν = ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W v) ≫
        ModularCurves.unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection W r₂) :=
    h₁.trans ((congrArg ModularCurves.unitEndomorphismOfTopSection htop).trans
      (ModularCurves.unitEndomorphismOfTopSection_comp _ _).symm)
  exact (Category.assoc _ _ _).trans (hsub.trans (halg.trans hval))

/-- **([C-rest-3] SK-W2')** The transition unit of two `overTrivializationOfRestrictIso`
images is read off from the restrict-side composite: if `ψ₁.inv ≫ ψ₂.hom` is
multiplication by `u`, the over-side transition is `overUnitScalarEnd u`. Bridge:
`overEquiv_unitScalarEnd`. -/
theorem overTriv_inv_comp_hom_of_restrict_scalar {X : Scheme.{u}}
    (M : X.Modules) (W : X.Opens)
    (ψ₁ ψ₂ : M.restrict W.ι ≅ unitObj W.toScheme) (u : Γ(X, W))
    (h : ψ₁.inv ≫ ψ₂.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W u)) :
    (Scheme.Modules.overTrivializationOfRestrictIso M W ψ₁).inv ≫
      (Scheme.Modules.overTrivializationOfRestrictIso M W ψ₂).hom =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf W u := by
  apply (Scheme.Modules.overEquiv W).functor.map_injective
  simp only [Functor.map_comp, Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv]
  have hG := Scheme.Modules.overEquiv_unitScalarEnd (X := X) W u
  have hGimg := (Iso.eq_comp_inv
    (W.sheafOfModulesEquivOverUnit X.ringCatSheaf)).mpr hG
  have hcol := congrArg
    (fun t => (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ ψ₁.inv ≫ t)
    (Iso.inv_hom_id_assoc ((overFunctorEquiv W).app M)
      (ψ₂.hom ≫ (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv))
  have hsub := congrArg
    (fun t => (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ t ≫
      (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv) h
  have hregroup1 := congrArg
    (fun t => (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ t)
    ((Category.assoc ψ₁.inv ψ₂.hom
      (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv).symm)
  have hregroup2 := (Category.assoc
    (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom
    (ModularCurves.unitEndomorphismOfTopSection (Scheme.Modules.openTopSection W u))
    (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv).symm
  have full := hcol.trans (hregroup1.trans (hsub.trans (hregroup2.trans hGimg.symm)))
  have bridge := (Category.assoc
    ((W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ ψ₁.inv)
    ((overFunctorEquiv W).app M).inv
    (((overFunctorEquiv W).app M).hom ≫ ψ₂.hom ≫
      (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv)).trans
    (Category.assoc
      (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ψ₁.inv
      (((overFunctorEquiv W).app M).inv ≫ ((overFunctorEquiv W).app M).hom ≫
        ψ₂.hom ≫ (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv))
  exact bridge.trans full

end PicPoint

section DivisorConstancy

open WeierstrassCurve HasseWeil.Curves HasseWeil.WeilPairing

/-- **(U5-L1b core)** Two nonzero functions with equal projective divisors differ by a
nonzero base-field constant: the quotient has trivial divisor
(`projectiveDivisorOf_mul` + cancellation) and the HasseWeil constancy anchor applies.
This is the "div G = div g_Q ⟹ G = a·g_Q, a ∈ k̄ˣ" step of the L1 dictionary. -/
theorem exists_const_mul_of_projectiveDivisorOf_eq {K : Type u} [Field K]
    [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve K).CoordinateRing]
    (G gQ : (⟨W⟩ : SmoothPlaneCurve K).FunctionField) (hG : G ≠ 0) (hgQ : gQ ≠ 0)
    (hdiv : (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf G =
      (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf gQ) :
    ∃ c : K, c ≠ 0 ∧
      G = algebraMap K (⟨W⟩ : SmoothPlaneCurve K).FunctionField c * gQ := by
  have hq : G / gQ ≠ 0 := div_ne_zero hG hgQ
  have hdivq : (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf (G / gQ) = 0 := by
    have hmul := (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf_mul
      (f := G / gQ) (g := gQ) hq hgQ
    rw [div_mul_cancel₀ G hgQ, hdiv] at hmul
    have h0 : (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf (G / gQ) +
        (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf gQ =
        0 + (⟨W⟩ : SmoothPlaneCurve K).projectiveDivisorOf gQ := by
      rw [zero_add]; exact hmul.symm
    exact add_right_cancel h0
  obtain ⟨c, hc0, hc⟩ := const_unit_of_projectiveDivisorOf_eq_zero
    (G / gQ) hq hdivq
  refine ⟨c, hc0, ?_⟩
  rw [← hc]
  field_simp

end DivisorConstancy

section ValuePlumbing

open EllipticCurve

/-- **(U5-L4, value plumbing)** The register pairing evaluates as
`torsionSplittingEval` of *any* normalised dataset for the second point: the composite
of the two proven bridges `weilPairingEval_eq_weilPairingKM` (register → canonical) and
`weilPairingKM_eq_torsionSplittingEval` (canonical → engine value at a dataset). This is
the shape the U5 comparison chain consumes: the L2 τ-scalar `c` is the `algebraMap`
image of the right-hand side at the dataset built from the 3b trivialisations. -/
theorem weilPairingEval_eq_torsionSplittingEval {S : Scheme.{u}} (E : EllipticCurve S)
    {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (M : (Limits.pullback E.π g).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (Limits.pullback E.π g)
      (kappa E E.smooth g (EllipticCurve.Point.asSection E g y)).val = toSkeleton M)
    {ι : Type*} (W : ι → (Limits.pullback E.π g).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((Limits.pullback E.π g).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π g) (W i ⊓ W j)) :
    (E.weilPairingEval x y hx hy : Γ(T, ⊤)) =
      ((torsionSplittingEval E E.smooth g N
        (EllipticCurve.Point.asSection E g y) (asSection_mem_torsionPoints E y hy)
        M hM W hW e hnorm
        (EllipticCurve.Point.asSection E g x) (asSection_mem_torsionPoints E x hx) :
          Γ(T, ⊤)ˣ) : Γ(T, ⊤)) := by
  rw [E.weilPairingEval_eq_weilPairingKM x y hx hy]
  exact congrArg Units.val
    (weilPairingKM_eq_torsionSplittingEval E E.smooth g N
      (EllipticCurve.Point.asSection E g x) (asSection_mem_torsionPoints E x hx)
      (EllipticCurve.Point.asSection E g y) (asSection_mem_torsionPoints E y hy)
      M hM W hW e hnorm)

end ValuePlumbing

end ModularCurves
