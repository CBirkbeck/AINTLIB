/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.DescentFromCharts
import ModularCurves.WeilPairing.TautologicalPair
import ModularCurves.WeilPairing.TheoremOfSquareField
import ModularCurves.ForMathlib.IdealSheafComapMul

/-!
# The theorem of the square, fibrewise (B3-step1)

The field-level theorem of the square
(`ModularCurves.nonempty_tensorObj_idealModule_add_field`) says that on the projective model
of an elliptic Weierstrass curve over a field `k`,

  `I(D_P) ⊗ I(D_Q) ≅ I(D_{P+Q}) ⊗ I(D_0)`.

The seesaw
(`ForMathlib/Seesaw.lean`, `exists_pullback_iso_of_fibrewise_trivial_of_isReduced`, and its
arbitrary-base form in `ForMathlib/SeesawGlobalBase.lean`) consumes fibrewise triviality in the
shape

  `hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst π x)).obj M ≅
        unitObj (Limits.pullback π x))`.

This file transports the first statement into the second, for the theorem-of-the-square
**discrepancy module**

  `Δ = (I(D_R) ⊗ I(D_Z)) ⊗ N`,   `N` a `⊗`-inverse of `I(D_P) ⊗ I(D_Q)`,

which is exactly the packaging that
`Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add_of_discrepancy_trivial`
consumes (there `R = Q + Q'` and `Z` is the zero section).

## The transport, in four steps

Nothing here is new mathematics; every ingredient is already proved elsewhere.

1. `ModularCurves.nonempty_pullback_tensorObj` (`WeilPairing/TautologicalPair.lean`) splits the
   pullback of a tensor product into the tensor product of the pullbacks — this breaks `Δ` into
   its ideal-module factors and the `N`-factor.
2. `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_idealModule_ker_sectionBaseChange`
   (`Picard/IdealModulePullback.lean`) identifies the pullback of `I(D_z)` along
   `Limits.pullback.fst π x` — *syntactically the morphism appearing in `hfib`* — with the ideal
   module of the base-changed section. Both of its local-principality hypotheses come from
   smoothness, so `SmoothOfRelativeDimension 1 π` and `IsSeparated π` are all that is needed.
   Steps 1 and 2 are already packaged together for a *pair* of sections by
   `ModularCurves.nonempty_pullback_tensorObj_idealModule_pair`
   (`WeilPairing/DescentFromCharts.lean`), which is what is used here.
3. `AlgebraicGeometry.Scheme.Hom.ker_comp_iso` (`ForMathlib/IdealSheafComapMul.lean`) moves ideal
   sheaves across an isomorphism of schemes, which is how a Weierstrass presentation of the fibre
   `Limits.pullback π x ≅ projModel W` carries the field theorem onto the fibre.
4. `ModularCurves.nonempty_pullback_iso_unitObj` (`WeilPairing/TautologicalPair.lean`) pulls the
   global trivialisation `(I(D_P) ⊗ I(D_Q)) ⊗ N ≅ 𝒪` back to the fibre, where it is the last leg
   of the chain.

## Contents

* `nonempty_pullback_discrepancy_iso_unitObj_of_fibre_iso` — **the `hfib`-shaped statement**,
  from the fibre-level two-sided iso.
* `nonempty_tensorObj_idealModule_fibre_of_projModel_iso` — the fibre-level two-sided iso, from
  the field theorem and a Weierstrass presentation of the fibre (step 3).
* `nonempty_pullback_discrepancy_iso_unitObj_of_field` — the composite.

The Weierstrass presentation of the fibre (the isomorphism `Limits.pullback π x ≅ projModel W`
together with the four section identifications) is left as a hypothesis here, so that the results
of this file apply to any family that carries one.

**It is produced, for the tautological family `projModelπ W₀`, in
`WeilPairing/FibreWeierstrassPresentation.lean`** — `projModelFibreIso` from
`isPullback_projModelBaseChange` (`EllipticCurve/WeierstrassModel.lean`), and the additive
matching of `P + Q` at the level of *scheme morphisms* from `mulModelHom_map` +
`mulModelHom_specPoints`, giving the hypothesis-free
`nonempty_pullback_discrepancy_iso_unitObj_projModel`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {C S : Scheme.{u}} {π : C ⟶ S}

/-! ## The `hfib`-shaped statement -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step1] The theorem-of-the-square discrepancy is trivial on every field-valued fibre.**

Let `π : C ⟶ S` be a separated smooth relative curve with four sections `P`, `Q`, `R`, `Z`, let
`N` be a `⊗`-inverse of `I(D_P) ⊗ I(D_Q)` (`hN`), and form the discrepancy module

  `Δ = (I(D_R) ⊗ I(D_Z)) ⊗ N`.

If over a field-valued point `x` of the base the two pairs of base-changed sections have
isomorphic ideal-module products (`hfield` — this is the theorem of the square on the fibre, with
`R` playing the role of `P + Q` and `Z` of the zero section), then `Δ` restricts to `𝒪` on that
fibre.

The conclusion is **literally the seesaw's `hfib` binder** with `M := Δ`: the pullback is taken
along `Limits.pullback.fst π x` and the target is `unitObj (Limits.pullback π x)`, so this lemma
can be handed to `exists_pullback_iso_of_fibrewise_trivial_of_isReduced` and to
`exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover` (`ForMathlib/Seesaw.lean`,
`ForMathlib/SeesawGlobalBase.lean`) as `fun {k} _ x => ...`.

The proof is the chain

  `f^*((I_R ⊗ I_Z) ⊗ N) ≅ f^*(I_R ⊗ I_Z) ⊗ f^*N ≅ (I_{R_x} ⊗ I_{Z_x}) ⊗ f^*N`
  `≅ (I_{P_x} ⊗ I_{Q_x}) ⊗ f^*N ≅ f^*(I_P ⊗ I_Q) ⊗ f^*N ≅ f^*((I_P ⊗ I_Q) ⊗ N) ≅ f^*𝒪 ≅ 𝒪`,

whose only non-formal link is `hfield`. -/
theorem nonempty_pullback_discrepancy_iso_unitObj_of_fibre_iso [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {P Q R Z : S ⟶ C} (hP : P ≫ π = 𝟙 S)
    (hQ : Q ≫ π = 𝟙 S) (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S) (N : C.Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
        (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj C))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (hfield : Nonempty (tensorObj
          (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange R hR x)))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange Z hZ x))) ≅
        tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange P hP x)))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange Q hQ x))))) :
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst π x)).obj
        (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Z))) N) ≅ unitObj (Limits.pullback π x)) := by
  obtain ⟨eRZ⟩ := nonempty_pullback_tensorObj (Limits.pullback.fst π x)
    (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Z))) N
  obtain ⟨ePQ⟩ := nonempty_pullback_tensorObj (Limits.pullback.fst π x)
    (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N
  obtain ⟨fRZ⟩ := nonempty_pullback_tensorObj_idealModule_pair hsm R Z hR hZ x
  obtain ⟨fPQ⟩ := nonempty_pullback_tensorObj_idealModule_pair hsm P Q hP hQ x
  obtain ⟨hu⟩ := nonempty_pullback_iso_unitObj (Limits.pullback.fst π x) hN
  exact ⟨eRZ ≪≫ tensorObjCongr (fRZ ≪≫ hfield.some ≪≫ fPQ.symm) (Iso.refl _) ≪≫
    ePQ.symm ≪≫ hu⟩

/-! ## Step 3: the field theorem on the fibre -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The kernel ideal sheaf of a section of the fibre is the `comap`, along a presentation
isomorphism, of the kernel ideal sheaf of the corresponding section of the model.

Pure `IdealSheafData` bookkeeping: `Scheme.Hom.ker_comp_iso` applied to `e.symm`. -/
theorem comap_ker_eq_ker_of_comp_iso {F X : Scheme.{u}} (e : F ≅ X) {T : Scheme.{u}}
    {s : T ⟶ F} {z : T ⟶ X} (hs : s ≫ e.hom = z) :
    (Scheme.Hom.ker z).comap e.hom = Scheme.Hom.ker s := by
  have hz : z ≫ e.symm.hom = s := by
    rw [← hs, Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h := Scheme.Hom.ker_comp_iso z e.symm
  rw [hz] at h
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Transport of a section ideal module across a presentation of the fibre.** With
`e : Limits.pullback π x ≅ projModel W` a presentation of the fibre and `s` a section of the fibre
matching the model section `z`, the pullback along `e.hom` of `I(D_z)` is `I(D_s)`.

The two local-principality inputs of `nonempty_pullback_idealModule` are supplied by the caller;
in the fibre setting both are instances of `RelEffCartierDiv.sectionDivisor_isOfficial`. -/
theorem nonempty_pullback_idealModule_of_comp_iso {F X : Scheme.{u}} (e : F ≅ X) {T : Scheme.{u}}
    {s : T ⟶ F} {z : T ⟶ X} (hs : s ≫ e.hom = z)
    (hz : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      (Scheme.Hom.ker z).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1))
    (hsloc : ∀ c : ↥F, ∃ V : F.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(F, V.1),
      (Scheme.Hom.ker s).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(F, V.1)) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj
          (Scheme.Modules.idealModule (Scheme.Hom.ker z)) ≅
        Scheme.Modules.idealModule (Scheme.Hom.ker s)) := by
  have hker := comap_ker_eq_ker_of_comp_iso e hs
  refine ⟨(nonempty_pullback_idealModule e.hom (Scheme.Hom.ker z) hz ?_).some ≪≫
    eqToIso (congrArg Scheme.Modules.idealModule hker)⟩
  rw [hker]
  exact hsloc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step1, step 3] The field theorem of the square, read on a fibre.**

Given a Weierstrass presentation of the fibre — an isomorphism
`e : Limits.pullback π x ≅ projModel W` together with an identification of the four base-changed
sections with `pointSection W p`, `pointSection W q`, `pointSection W (p + q)` and
`projModelZero W` — the proved field-level theorem of the square
`ModularCurves.nonempty_tensorObj_idealModule_add_field` transports to the two-sided iso of ideal
modules on the fibre, i.e. exactly the `hfield` hypothesis of
`nonempty_pullback_discrepancy_iso_unitObj_of_fibre_iso`.

The compatibility `hsR` is where `projModelPointsAddEquiv` (`EllipticCurve/MulByHomDegree.lean`)
is meant to be used by the caller: it is an `≃+`, so a section that is the sum of the sections
matching `p` and `q` matches `p + q`. -/
theorem nonempty_tensorObj_idealModule_fibre_of_projModel_iso [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {P Q R Z : S ⟶ C} (hP : P ≫ π = 𝟙 S)
    (hQ : Q ≫ π = 𝟙 S) (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S) {k : Type u} [Field k]
    [DecidableEq k] (x : Spec (CommRingCat.of k) ⟶ S) (W : WeierstrassCurve k) [W.IsElliptic]
    (e : Limits.pullback π x ≅ projModel W) (p q : W.toAffine.Point)
    (hsP : sectionBaseChange P hP x ≫ e.hom = pointSection W p)
    (hsQ : sectionBaseChange Q hQ x ≫ e.hom = pointSection W q)
    (hsR : sectionBaseChange R hR x ≫ e.hom = pointSection W (p + q))
    (hsZ : sectionBaseChange Z hZ x ≫ e.hom = projModelZero W) :
    Nonempty (tensorObj
          (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange R hR x)))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange Z hZ x))) ≅
        tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange P hP x)))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (sectionBaseChange Q hQ x)))) := by
  haveI hsep : IsSeparated (Limits.pullback.snd π x) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) π x ‹_›
  have hsm' : SmoothOfRelativeDimension 1 (Limits.pullback.snd π x) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) π x hsm
  have hloc : ∀ (z : S ⟶ C) (hz : z ≫ π = 𝟙 S),
      ∀ c : ↥(Limits.pullback π x), ∃ V : (Limits.pullback π x).affineOpens, c ∈ V.1 ∧
        ∃ g : Γ(Limits.pullback π x, V.1),
          (Scheme.Hom.ker (sectionBaseChange z hz x)).ideal V = Ideal.span {g} ∧
            g ∈ nonZeroDivisors Γ(Limits.pullback π x, V.1) := fun z hz =>
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm' (sectionBaseChange z hz x)
      (sectionBaseChange_snd z hz x)).locallyPrincipal
  obtain ⟨eP⟩ := nonempty_pullback_idealModule_of_comp_iso e hsP
    (exists_affineOpen_ker_pointSection_span_nzd W p) (hloc P hP)
  obtain ⟨eQ⟩ := nonempty_pullback_idealModule_of_comp_iso e hsQ
    (exists_affineOpen_ker_pointSection_span_nzd W q) (hloc Q hQ)
  obtain ⟨eR⟩ := nonempty_pullback_idealModule_of_comp_iso e hsR
    (exists_affineOpen_ker_pointSection_span_nzd W (p + q)) (hloc R hR)
  obtain ⟨eZ⟩ := nonempty_pullback_idealModule_of_comp_iso e hsZ
    (exists_affineOpen_ker_projModelZero_span_nzd W) (hloc Z hZ)
  obtain ⟨tRZ⟩ := nonempty_pullback_tensorObj e.hom
    (Scheme.Modules.idealModule (Scheme.Hom.ker (pointSection W (p + q))))
    (Scheme.Modules.idealModule (Scheme.Hom.ker (projModelZero W)))
  obtain ⟨tPQ⟩ := nonempty_pullback_tensorObj e.hom
    (Scheme.Modules.idealModule (Scheme.Hom.ker (pointSection W p)))
    (Scheme.Modules.idealModule (Scheme.Hom.ker (pointSection W q)))
  obtain ⟨esq⟩ := nonempty_tensorObj_idealModule_add_field W p q
  exact ⟨tensorObjCongr eR.symm eZ.symm ≪≫ tRZ.symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso esq.symm ≪≫ tPQ ≪≫ tensorObjCongr eP eQ⟩

/-! ## The composite -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step1, headline] The theorem-of-the-square discrepancy module is trivial on every
field-valued fibre, from the field theorem of the square.**

This is `nonempty_pullback_discrepancy_iso_unitObj_of_fibre_iso` with its `hfield` hypothesis
discharged by `nonempty_tensorObj_idealModule_fibre_of_projModel_iso`, i.e. by the proved
field-level theorem of the square read through a Weierstrass presentation of the fibre.

The conclusion is the seesaw's `hfib` binder for `M := (I(D_R) ⊗ I(D_Z)) ⊗ N`. Because the
presentation data mention `pointSection`, which needs `DecidableEq k`, the instance appears in
the binder list here; a consumer supplying `hfib` writes
`fun {k} _ x => by classical exact nonempty_pullback_discrepancy_iso_unitObj_of_field …`. -/
theorem nonempty_pullback_discrepancy_iso_unitObj_of_field [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {P Q R Z : S ⟶ C} (hP : P ≫ π = 𝟙 S)
    (hQ : Q ≫ π = 𝟙 S) (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S) (N : C.Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
        (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj C))
    {k : Type u} [Field k] [DecidableEq k] (x : Spec (CommRingCat.of k) ⟶ S)
    (W : WeierstrassCurve k) [W.IsElliptic] (e : Limits.pullback π x ≅ projModel W)
    (p q : W.toAffine.Point)
    (hsP : sectionBaseChange P hP x ≫ e.hom = pointSection W p)
    (hsQ : sectionBaseChange Q hQ x ≫ e.hom = pointSection W q)
    (hsR : sectionBaseChange R hR x ≫ e.hom = pointSection W (p + q))
    (hsZ : sectionBaseChange Z hZ x ≫ e.hom = projModelZero W) :
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst π x)).obj
        (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Z))) N) ≅
      unitObj (Limits.pullback π x)) :=
  nonempty_pullback_discrepancy_iso_unitObj_of_fibre_iso hsm hP hQ hR hZ N hN x
    (nonempty_tensorObj_idealModule_fibre_of_projModel_iso hsm hP hQ hR hZ x W e p q
      hsP hsQ hsR hsZ)

end ModularCurves
