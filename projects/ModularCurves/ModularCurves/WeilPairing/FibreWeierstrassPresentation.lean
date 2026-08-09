/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.TheoremOfSquareFibrewise

/-!
# The Weierstrass presentation of a field-valued fibre (B3-step1b)

`WeilPairing/TheoremOfSquareFibrewise.lean` reduces the seesaw's fibrewise-triviality binder
`hfib` for the theorem-of-the-square discrepancy module to a **Weierstrass presentation of the
fibre**: an isomorphism `Limits.pullback π x ≅ projModel W` over a field-valued point `x` of the
base, together with the identification of the four base-changed sections `P`, `Q`, `P + Q`, `0`
with `pointSection W p`, `pointSection W q`, `pointSection W (p + q)`, `projModelZero W`.

This file **produces** that data for the tautological family — the projective model
`projModelπ W₀ : projModel W₀ ⟶ Spec A` of an elliptic Weierstrass curve over a ring `A` — and
hence removes the presentation hypothesis from
`ModularCurves.nonempty_pullback_discrepancy_iso_unitObj_of_field`.

## The three ingredients

1. **The fibre is a projective model.** `isPullback_projModelBaseChange`
   (`EllipticCurve/WeierstrassModel.lean`) says the base change of `projModel W₀` along
   `Spec (A → k)` *is* `projModel (W₀.map (algebraMap A k))`; `projModelFibreIso` is the
   resulting isomorphism of the fibre with the model of the base-changed curve, and
   `projModelFibreIso_hom_comp_projModelBaseChange` / `_projModelπ` are its two legs.
2. **`P` and `Q` are free.** The presentation demands `sectionBaseChange P hP x ≫ e.hom =
   pointSection W p` for *some* `p`; taking `p := fibrePoint P hP`, the image of the fibre
   section under the points dictionary `projModelPointsEquiv`, makes this
   `Equiv.symm_apply_apply` (`pointSection_fibrePoint`). The zero section is
   `projModelZero_baseChange`, the T-A5b zero leg (`sectionBaseChange_projModelZero_fibreIso`).
3. **The sum section is the substantive part.** The additive matching is done *at the level of
   scheme morphisms*, not through an `≃+`: `mulModelHom_map`
   (`EllipticCurve/GroupLawConstruction.lean`, the base-change naturality of the Bosma–Lenstra
   two-law multiplication) says the fibre of the sum section is the `mulModelHom` of the fibres
   (`sectionBaseChange_mul_projModelFibreIso`, proved by the universal property of the
   base-change square), and `mulModelHom_specPoints` (`EllipticCurve/AdditionSpecPoints.lean`)
   turns that `mulModelHom` into `+` on `Affine.Point` (`pointSection_add_fibrePoint`). This
   route sidesteps `projModelPointsAddEquiv` — which would need the *dictionary* to be compared
   across two different base rings — by keeping everything over `k`.

## Contents

* `projModelFibreIso` — the presentation isomorphism of the fibre.
* `fibrePoint` — the affine point of `W₀.map (algebraMap A k)` attached to a section.
* `sectionBaseChange_projModelFibreIso_eq_pointSection_add`,
  `sectionBaseChange_projModelZero_fibreIso`, `pointSection_fibrePoint` — the four section
  identifications.
* `nonempty_pullback_discrepancy_iso_unitObj_projModel` — the `hfib`-shaped conclusion for the
  tautological family, with **no presentation hypothesis**; `..._of_point` is its
  `EllipticCurve.Point`-flavoured form, where the third section is literally `(P + Q).1` for the
  model record `modelEllipticCurve W₀`.

The general-base statement `nonempty_pullback_discrepancy_iso_unitObj_of_field` is kept as is:
this file only *adds* the hypothesis-free specialisation.
-/

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {A : Type u} [CommRing A] {W₀ : WeierstrassCurve A} [W₀.IsElliptic]
variable {k : Type u} [Field k] [Algebra A k]

/-- The field-valued point of `Spec A` attached to an `A`-algebra `k`. -/
noncomputable abbrev fibreSpecPt (A : Type u) [CommRing A] (k : Type u) [CommRing k]
    [Algebra A k] : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A k))

/-! ## Step 1: the fibre of the tautological family is a projective model -/

/-- **The Weierstrass presentation of a field-valued fibre.** The fibre of `projModel W₀` over
the `k`-point of `Spec A` is the projective model of the base-changed curve — this is the T-A5a
base-change square `isPullback_projModelBaseChange`, read as an isomorphism. -/
noncomputable def projModelFibreIso (W₀ : WeierstrassCurve A) [W₀.IsElliptic] :
    Limits.pullback (projModelπ W₀) (fibreSpecPt A k) ≅ projModel (W₀.map (algebraMap A k)) :=
  (isPullback_projModelBaseChange (R' := k) W₀).isoPullback.symm

@[reassoc]
lemma projModelFibreIso_hom_comp_projModelBaseChange :
    (projModelFibreIso W₀ (k := k)).hom ≫ projModelBaseChange (algebraMap A k) W₀ =
      pullback.fst (projModelπ W₀) (fibreSpecPt A k) :=
  (isPullback_projModelBaseChange (R' := k) W₀).isoPullback_inv_fst

@[reassoc]
lemma projModelFibreIso_hom_comp_projModelπ :
    (projModelFibreIso W₀ (k := k)).hom ≫ projModelπ (W₀.map (algebraMap A k)) =
      pullback.snd (projModelπ W₀) (fibreSpecPt A k) :=
  (isPullback_projModelBaseChange (R' := k) W₀).isoPullback_inv_snd

/-- The horizontal leg of a base-changed section read through the presentation: it is the
restriction of the section to the fibre. -/
lemma sectionBaseChange_fibreIso_baseChange (z : Spec (CommRingCat.of A) ⟶ projModel W₀)
    (hz : z ≫ projModelπ W₀ = 𝟙 _) :
    (sectionBaseChange z hz (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) ≫
      projModelBaseChange (algebraMap A k) W₀ = fibreSpecPt A k ≫ z := by
  rw [Category.assoc, projModelFibreIso_hom_comp_projModelBaseChange, sectionBaseChange_fst]

/-- A base-changed section read through the presentation is still a section. -/
lemma sectionBaseChange_fibreIso_projModelπ (z : Spec (CommRingCat.of A) ⟶ projModel W₀)
    (hz : z ≫ projModelπ W₀ = 𝟙 _) :
    (sectionBaseChange z hz (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) ≫
      projModelπ (W₀.map (algebraMap A k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Category.assoc, projModelFibreIso_hom_comp_projModelπ, sectionBaseChange_snd]

/-- `sectionBaseChange_fibreIso_projModelπ` in the `SpecPoints` spelling, which is what the
points dictionary consumes (`𝟙 = Spec (k → k)`). -/
lemma sectionBaseChange_fibreIso_projModelπ' (z : Spec (CommRingCat.of A) ⟶ projModel W₀)
    (hz : z ≫ projModelπ W₀ = 𝟙 _) :
    (sectionBaseChange z hz (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) ≫
        projModelπ (W₀.map (algebraMap A k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
  rw [sectionBaseChange_fibreIso_projModelπ]
  exact (Spec.map_id _).symm

/-! ## Step 2: the zero section -/

/-- **The zero section is preserved by the presentation.** T-A5b zero leg
(`projModelZero_baseChange`) plus the universal property of the base-change square. -/
lemma sectionBaseChange_projModelZero_fibreIso :
    sectionBaseChange (projModelZero W₀) (projModelZero_projModelπ W₀) (fibreSpecPt A k) ≫
        (projModelFibreIso W₀).hom = projModelZero (W₀.map (algebraMap A k)) := by
  refine (isPullback_projModelBaseChange (R' := k) W₀).hom_ext ?_ ?_
  · rw [sectionBaseChange_fibreIso_baseChange, projModelZero_baseChange]
  · rw [sectionBaseChange_fibreIso_projModelπ, projModelZero_projModelπ]

/-! ## Step 3: the sum section -/

/-- The comparison morphism of the two model squares turns a lift of two fibre sections into the
fibre restriction of the lift of the two sections. The `fst`/`snd` legs of the square-level
`pullback.map` of `mulModelHom_map`. -/
lemma lift_fibreIso_comp_pullbackMap {P Q : Spec (CommRingCat.of A) ⟶ projModel W₀}
    (hP : P ≫ projModelπ W₀ = 𝟙 _) (hQ : Q ≫ projModelπ W₀ = 𝟙 _)
    (w : (sectionBaseChange P hP (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) ≫
        projModelπ (W₀.map (algebraMap A k)) =
      (sectionBaseChange Q hQ (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) ≫
        projModelπ (W₀.map (algebraMap A k))) :
    pullback.lift (sectionBaseChange P hP (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
        (sectionBaseChange Q hQ (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) w ≫
        pullback.map (projModelπ (W₀.map (algebraMap A k)))
          (projModelπ (W₀.map (algebraMap A k))) (projModelπ W₀) (projModelπ W₀)
          (projModelBaseChange (algebraMap A k) W₀) (projModelBaseChange (algebraMap A k) W₀)
          (fibreSpecPt A k) (projModelBaseChange_π (algebraMap A k) W₀).symm
          (projModelBaseChange_π (algebraMap A k) W₀).symm =
      fibreSpecPt A k ≫ pullback.lift P Q (hP.trans hQ.symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      sectionBaseChange_fibreIso_baseChange, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      sectionBaseChange_fibreIso_baseChange, Category.assoc, pullback.lift_snd]

/-- **[B3-step1b, the substantive step] The fibre of a sum section is the sum of the fibres, as
scheme morphisms.** If `Rs` is the `mulModelHom`-sum of the sections `P` and `Q` of the
tautological family, then its base change, read through the presentation, is the `mulModelHom`
of the base changes of `P` and `Q`.

The proof is the universal property of the base-change square: the `π`-legs are both `𝟙`
(`mulModelHom_π`), and the `projModelBaseChange`-legs agree by the base-change naturality
`mulModelHom_map` of the two-law multiplication. No points, no `≃+`. -/
lemma sectionBaseChange_mul_projModelFibreIso {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀}
    (hP : P ≫ projModelπ W₀ = 𝟙 _) (hQ : Q ≫ projModelπ W₀ = 𝟙 _)
    (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀) :
    sectionBaseChange Rs hR (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom =
      pullback.lift (sectionBaseChange P hP (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
        (sectionBaseChange Q hQ (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
        ((sectionBaseChange_fibreIso_projModelπ P hP).trans
          (sectionBaseChange_fibreIso_projModelπ Q hQ).symm) ≫
      mulModelHom (W₀.map (algebraMap A k)) := by
  refine (isPullback_projModelBaseChange (R' := k) W₀).hom_ext ?_ ?_
  · have hlhs : (sectionBaseChange Rs hR (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom) ≫
          projModelBaseChange (algebraMap A k) W₀ =
        (fibreSpecPt A k ≫ pullback.lift P Q (hP.trans hQ.symm)) ≫ mulModelHom W₀ := by
      rw [sectionBaseChange_fibreIso_baseChange, hRs, ← Category.assoc]
    have hrhs : (pullback.lift
            (sectionBaseChange P hP (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
            (sectionBaseChange Q hQ (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
            ((sectionBaseChange_fibreIso_projModelπ P hP).trans
              (sectionBaseChange_fibreIso_projModelπ Q hQ).symm) ≫
          mulModelHom (W₀.map (algebraMap A k))) ≫
            projModelBaseChange (algebraMap A k) W₀ =
        (fibreSpecPt A k ≫ pullback.lift P Q (hP.trans hQ.symm)) ≫ mulModelHom W₀ := by
      rw [Category.assoc, mulModelHom_map, ← Category.assoc,
        lift_fibreIso_comp_pullbackMap hP hQ]
    exact hlhs.trans hrhs.symm
  · rw [sectionBaseChange_fibreIso_projModelπ, Category.assoc, mulModelHom_π, ← Category.assoc,
      pullback.lift_fst, sectionBaseChange_fibreIso_projModelπ]

/-! ## Step 4: the points dictionary on the fibre -/

/-- **The fibre point of a section.** The base change of a section of `projModel W₀` along a
field-valued point of the base, read through the presentation `projModelFibreIso` and then
through the points dictionary `projModelPointsEquiv`, is an affine point of the base-changed
Weierstrass curve. -/
noncomputable def fibrePoint (z : Spec (CommRingCat.of A) ⟶ projModel W₀)
    (hz : z ≫ projModelπ W₀ = 𝟙 _) : (W₀.map (algebraMap A k)).toAffine.Point :=
  projModelPointsEquiv (W₀.map (algebraMap A k)) k
    ⟨sectionBaseChange z hz (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom,
      sectionBaseChange_fibreIso_projModelπ' z hz⟩

/-- **The `P`- and `Q`-legs of the presentation, for free.** `pointSection` is the inverse of
the dictionary, so the section attached to the fibre point of `z` is the fibre of `z`. -/
lemma pointSection_fibrePoint [DecidableEq k] (z : Spec (CommRingCat.of A) ⟶ projModel W₀)
    (hz : z ≫ projModelπ W₀ = 𝟙 _) :
    pointSection (W₀.map (algebraMap A k)) (fibrePoint (k := k) z hz) =
      sectionBaseChange z hz (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom :=
  congrArg Subtype.val
    ((projModelPointsEquiv (W₀.map (algebraMap A k)) k).symm_apply_apply
      ⟨sectionBaseChange z hz (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom,
        sectionBaseChange_fibreIso_projModelπ' z hz⟩)

/-- **The dictionary reads `mulModelHom` as `+`.** `mulModelHom_specPoints` says the two-law
multiplication computes mathlib's `Affine.Point` addition on field points; inverting the
dictionary turns that into a statement about `pointSection`. -/
lemma pointSection_add_fibrePoint [DecidableEq k]
    {P Q : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) :
    pointSection (W₀.map (algebraMap A k))
        (fibrePoint (k := k) P hP + fibrePoint (k := k) Q hQ) =
      pullback.lift (sectionBaseChange P hP (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
        (sectionBaseChange Q hQ (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom)
        ((sectionBaseChange_fibreIso_projModelπ P hP).trans
          (sectionBaseChange_fibreIso_projModelπ Q hQ).symm) ≫
      mulModelHom (W₀.map (algebraMap A k)) := by
  have hmul := mulModelHom_specPoints (W₀.map (algebraMap A k)) k
    (⟨_, sectionBaseChange_fibreIso_projModelπ' P hP⟩ :
      SpecPoints (projModel (W₀.map (algebraMap A k))) (projModelπ (W₀.map (algebraMap A k))) k)
    (⟨_, sectionBaseChange_fibreIso_projModelπ' Q hQ⟩ :
      SpecPoints (projModel (W₀.map (algebraMap A k))) (projModelπ (W₀.map (algebraMap A k))) k)
  refine Eq.trans (congrArg
    (fun t => (((projModelPointsEquiv (W₀.map (algebraMap A k)) k).symm) t).1) hmul.symm) ?_
  exact congrArg Subtype.val
    ((projModelPointsEquiv (W₀.map (algebraMap A k)) k).symm_apply_apply _)

/-- **[B3-step1b] The `R`-leg of the presentation.** The base change of the sum section, read
through the presentation, is `pointSection` of the sum of the two fibre points. -/
lemma sectionBaseChange_projModelFibreIso_eq_pointSection_add [DecidableEq k]
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀) :
    sectionBaseChange Rs hR (fibreSpecPt A k) ≫ (projModelFibreIso W₀).hom =
      pointSection (W₀.map (algebraMap A k))
        (fibrePoint (k := k) P hP + fibrePoint (k := k) Q hQ) :=
  (sectionBaseChange_mul_projModelFibreIso hP hQ hR hRs).trans
    (pointSection_add_fibrePoint hP hQ).symm

/-! ## The hypothesis-free fibrewise triviality -/

/-- **[B3-step1b, headline] The theorem-of-the-square discrepancy of the tautological family is
trivial on every field-valued fibre — no presentation hypothesis.**

For the projective model `projModelπ W₀ : projModel W₀ ⟶ Spec A` of an elliptic Weierstrass
curve, with sections `P`, `Q`, their `mulModelHom`-sum `Rs`, the zero section, and a
`⊗`-inverse `N` of `I(D_P) ⊗ I(D_Q)`, the discrepancy module `(I(D_Rs) ⊗ I(D_0)) ⊗ N` restricts
to `𝒪` on every field-valued fibre.

This is `nonempty_pullback_discrepancy_iso_unitObj_of_field` with its Weierstrass-presentation
hypotheses discharged by `projModelFibreIso` and the four section identifications of this file.
The conclusion is literally the seesaw's `hfib` binder, so a consumer writes
`fun {k} _ x => nonempty_pullback_discrepancy_iso_unitObj_projModel hP hQ hR hRs N hN x`. -/
theorem nonempty_pullback_discrepancy_iso_unitObj_projModel
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀)
    (N : (projModel W₀).Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
        (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj (projModel W₀)))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (projModelπ W₀) x)).obj
        (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker Rs))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (projModelZero W₀)))) N) ≅
      unitObj (Limits.pullback (projModelπ W₀) x)) := by
  classical
  letI : Algebra A k := (Spec.preimage x).hom.toAlgebra
  have hx : x = fibreSpecPt A k := by
    have h1 : CommRingCat.ofHom (algebraMap A k) = Spec.preimage x := CommRingCat.ofHom_hom _
    show x = Spec.map (CommRingCat.ofHom (algebraMap A k))
    rw [h1, Spec.map_preimage]
  rw [hx]
  exact nonempty_pullback_discrepancy_iso_unitObj_of_field (projModel_smooth W₀) hP hQ hR
    (projModelZero_projModelπ W₀) N hN _ (W₀.map (algebraMap A k)) (projModelFibreIso W₀)
    (fibrePoint (k := k) P hP) (fibrePoint (k := k) Q hQ)
    (pointSection_fibrePoint P hP).symm (pointSection_fibrePoint Q hQ).symm
    (sectionBaseChange_projModelFibreIso_eq_pointSection_add hP hQ hR hRs)
    sectionBaseChange_projModelZero_fibreIso

/-- **[B3-step1b] The `EllipticCurve.Point` form.** Same statement, with the two sections given
as points of the model record `modelEllipticCurve W₀` and the third section literally their sum
`(P + Q).1`; `modelEllipticCurve_point_add_val` supplies the `mulModelHom` presentation of the
sum. This is the shape `Picard/SelfAdjointN.lean` works in. -/
theorem nonempty_pullback_discrepancy_iso_unitObj_projModel_of_point
    (P Q : (modelEllipticCurve W₀).Point (𝟙 (Spec (CommRingCat.of A))))
    (N : (projModel W₀).Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P.1))
        (Scheme.Modules.idealModule (Scheme.Hom.ker Q.1))) N ≅ unitObj (projModel W₀)))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (projModelπ W₀) x)).obj
        (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker (P + Q).1))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (projModelZero W₀)))) N) ≅
      unitObj (Limits.pullback (projModelπ W₀) x)) :=
  nonempty_pullback_discrepancy_iso_unitObj_projModel P.2 Q.2 (P + Q).2
    (modelEllipticCurve_point_add_val W₀ P Q) N hN x

end ModularCurves
