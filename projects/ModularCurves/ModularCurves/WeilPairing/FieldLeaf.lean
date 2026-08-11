/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMBilinear
import ModularCurves.WeilPairing.FieldComparisonBridge

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

end ModularCurves
