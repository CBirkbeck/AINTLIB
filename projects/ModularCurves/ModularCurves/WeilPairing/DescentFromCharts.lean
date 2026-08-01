/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.IteratedTwist
import ModularCurves.Picard.RigidDescent

/-!
# Descent of a trivialization from charts of the base (W2)

`Picard/RigidDescent.lean` glues *generating sections* whose overlap comparison units are
`1` along the zero section. The line/vertical construction produces *trivializations* over
the preimages of a cover of the base, so this file supplies the bridge: a trivialization
gives a generating section (`generatorOfRestrictIso`), two generating sections differ by a
unit (`exists_isUnit_smul_eq_of_generators`), and the resulting comparison units are the
data the rigidified glue lemma consumes.

The zero-section normalization stays a hypothesis: it is the rigidification step, and the
theorem of the square is exactly the statement that it can be arranged (after twisting by
the base bundle `N = 0^*Δ`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W2-d] Descent from chart trivializations.** An invertible module on the total
space which is trivial over the preimage of each member of a cover of the base, with
comparison units normalized along the zero section, is trivial. -/
theorem nonempty_unitObj_iso_of_chart_trivializations
    (hp : UniversallyOConnected p)
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (L : (pullback p g).Modules) {ι : Type u} (U : ι → T.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, (restrictFunctor (pullback.snd p g ⁻¹ᵁ U i).ι).obj L ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (hnorm : ∀ i j, ∀ u : Γ(pullback p g,
        pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j),
      (L.presheaf.map
          (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
            (pullback.snd p g ⁻¹ᵁ U j)).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (e i))
        = u • L.presheaf.map
          (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
            (pullback.snd p g ⁻¹ᵁ U j)).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U j) (e j))) →
      (Scheme.Hom.appLE z (pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j)
        (U i ⊓ U j) (le_inf_preimage_preimage g hz (U i) (U j))).hom u = 1)
    (hgen : ∀ (i : ι) (W : (pullback p g).Opens)
      (hW : W ≤ pullback.snd p g ⁻¹ᵁ U i),
      Function.Bijective fun r : Γ(pullback p g, W) =>
        r • L.presheaf.map (homOfLE hW).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (e i))) :
    Nonempty (unitObj (pullback p g) ≅ L) := by
  classical
  -- the comparison units on overlaps, from the two generating sections there
  have hcomp : ∀ i j, ∃ u : Γ(pullback p g,
      pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j),
      L.presheaf.map
          (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
            (pullback.snd p g ⁻¹ᵁ U j)).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (e i))
        = u • L.presheaf.map
          (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
            (pullback.snd p g ⁻¹ᵁ U j)).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U j) (e j)) := by
    intro i j
    obtain ⟨u, -, hu⟩ := exists_isUnit_smul_eq_of_generators
      (pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j)
      (L.presheaf.map
        (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (e i)))
      (L.presheaf.map
        (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U j) (e j)))
      (hgen i _ inf_le_left) (hgen j _ inf_le_right)
    exact ⟨u, hu⟩
  choose u hu using hcomp
  exact nonempty_unitObj_iso_of_normalized_glue g hp hz L U hU
    (fun i => generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (e i))
    u hu (fun i j => hnorm i j (u i j) (hu i j)) hgen

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W2-e] Rescaling a generator by a base unit.** The pullback of a unit of the base
scales a generating section to another generating section. -/
theorem bijective_smul_pullback_unit_smul
    {L : (pullback p g).Modules} (W : (pullback p g).Opens)
    (c : Γ(pullback p g, W)) (hc : IsUnit c) (s : Γ(L, W))
    (hs : Function.Bijective (fun r : Γ(pullback p g, W) => r • s)) :
    Function.Bijective (fun r : Γ(pullback p g, W) => r • (c • s)) := by
  obtain ⟨v, rfl⟩ := hc
  constructor
  · intro a b hab
    have h1 : (a * (v : Γ(pullback p g, W))) • s =
        (b * (v : Γ(pullback p g, W))) • s := by
      rw [mul_smul, mul_smul]
      exact hab
    have h2 := hs.injective h1
    have h3 := congrArg (fun t => t * (↑v⁻¹ : Γ(pullback p g, W))) h2
    simpa [mul_assoc] using h3
  · intro y
    obtain ⟨a, ha⟩ := hs.surjective y
    refine ⟨a * (↑v⁻¹ : Γ(pullback p g, W)), ?_⟩
    show (a * (↑v⁻¹ : Γ(pullback p g, W))) • ((v : Γ(pullback p g, W)) • s) = y
    rw [← mul_smul, mul_assoc, Units.inv_mul, mul_one]
    exact ha

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4 brick] A section reads back what was pulled back along it.** Restricting a
base section to a chart preimage and then evaluating along `z` returns the section. This
is the one computation the cocycle argument runs on, so it is stated on its own. -/
theorem appLE_z_appLE_snd_eq_self
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (Wb : T.Opens) (e : Wb ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ Wb)) (w : Γ(T, Wb)) :
    (Scheme.Hom.appLE z (pullback.snd p g ⁻¹ᵁ Wb) Wb e).hom
        ((Scheme.Hom.appLE (pullback.snd p g) Wb (pullback.snd p g ⁻¹ᵁ Wb)
          le_rfl).hom w) = w := by
  have h1 : (pullback.snd p g).app Wb =
      (pullback.snd p g).appLE Wb (pullback.snd p g ⁻¹ᵁ Wb) le_rfl :=
    (Scheme.Hom.appLE_eq_app _).symm
  have h2 := congrArg (fun φ : Γ(T, Wb) ⟶ Γ(T, Wb) => φ.hom w)
    (app_appLE_section g hz Wb e)
  rw [h1] at h2
  exact h2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W2-e] The rigidification cocycle.** If the comparison unit of two generators has
`z`-value `c i · (c j)⁻¹` for base units `c`, then after rescaling by the pullbacks of
`c⁻¹` the comparison unit has `z`-value `1` — the hypothesis the rigidified glue lemma
wants. Stated for the scalars only; the section rescaling is
`bijective_smul_pullback_unit_smul`. -/
theorem appLE_z_rescaled_eq_one
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (V : (pullback p g).Opens) (Wb : T.Opens) (hV : V = pullback.snd p g ⁻¹ᵁ Wb)
    (e : Wb ≤ z ⁻¹ᵁ V)
    (u : Γ(pullback p g, V)) (ci cj : Γ(T, Wb))
    (hu : (Scheme.Hom.appLE z V Wb e).hom u = ci * cj) :
    (Scheme.Hom.appLE z V Wb e).hom
      ((Scheme.Hom.appLE (pullback.snd p g) Wb V (by rw [hV]) ci) *
        u * (Scheme.Hom.appLE (pullback.snd p g) Wb V (by rw [hV]) cj)) =
      ci * (ci * cj) * cj := by
  subst hV
  have hsec : ∀ w : Γ(T, Wb), (Scheme.Hom.appLE z (pullback.snd p g ⁻¹ᵁ Wb) Wb e).hom
      ((Scheme.Hom.appLE (pullback.snd p g) Wb (pullback.snd p g ⁻¹ᵁ Wb)
        le_rfl).hom w) = w :=
    fun w => appLE_z_appLE_snd_eq_self g hz Wb e w
  rw [map_mul, map_mul, hsec, hsec, hu]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.1] A section undoes its own pullback.** For `z` a section of `f`, the
composite `z^* f^*` is the identity on modules of the base. This is the first brick of
the un-normalized descent: it identifies the base bundle `N` that the rigidification
contributes as `N = z^* L`. -/
noncomputable def pullbackSectionIso {T' E' : Scheme.{u}} (f : E' ⟶ T') (z : T' ⟶ E')
    (hz : z ≫ f = 𝟙 T') (N : T'.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback z).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) ≅ N :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp z f).app N ≪≫
    eqToIso (by rw [hz]) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId T').app N

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.2] Pulling back a chart trivialization.** A trivialization of `N` over `U`
gives one of `f^* N` over `f ⁻¹ᵁ U`. This is the trivialization-level content of
`IsInvertible.pullback`, extracted as a usable iso so that the descent can twist by
`f^* N` chart by chart. -/
noncomputable def restrictPullbackTrivialization {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : X.Modules) (U : X.Opens)
    (e : (restrictFunctor U.ι).obj N ≅ unitObj U.toScheme) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) ≅
      unitObj (f ⁻¹ᵁ U).toScheme :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app N ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (morphismRestrict_ι f U).symm).app N ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app N ≪≫
          (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso
            ((restrictFunctorIsoPullback U.ι).symm.app N ≪≫ e) ≪≫
            pullbackUnitIso (f ∣_ U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.3] The tensor of two chart trivializations.** Trivializing both factors on a
chart trivializes their tensor there. Phrased entirely in `tensorObj` (no monoidal
instance in sight) — going through `⊗` makes the elaborator unify the whole monoidal
structure and blows the whnf budget. -/
theorem nonempty_tensorObj_restrict_trivialization {X : Scheme.{u}} {M L : X.Modules}
    (U : X.Opens)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    Nonempty ((restrictFunctor U.ι).obj (tensorObj M L) ≅ unitObj U.toScheme) := by
  obtain ⟨e⟩ := nonempty_pullback_tensorObj_of_isOpenImmersion U.ι M L
  refine ⟨(restrictFunctorIsoPullback U.ι).app (tensorObj M L) ≪≫ e ≪≫ ?_⟩
  refine tensorObjCongr ((restrictFunctorIsoPullback U.ι).symm.app M ≪≫ eM)
    ((restrictFunctorIsoPullback U.ι).symm.app L ≪≫ eL) ≪≫ ?_
  exact (nonempty_tensorObj_unit_iso (unitObj U.toScheme)).some

end ModularCurves
