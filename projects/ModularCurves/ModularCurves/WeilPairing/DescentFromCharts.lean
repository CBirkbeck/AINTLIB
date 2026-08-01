/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PullbackTensorSection
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

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite MonoidalCategory
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4.a] The comparison units satisfy the cocycle identity.** Stated as the module
algebra it is: three sections of an invertible module over a common refinement, related
pairwise by scalars, with the third generating freely. The geometric restriction
bookkeeping is the caller's; the content is that `a * b = c` is forced.

This is what makes the `z`-values of the comparison units a Čech cocycle on the base,
hence what the gluing engine needs in order to produce the base bundle `N`. -/
theorem unit_cocycle_of_generator_relations {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] {t₁ t₂ t₃ : M} {a b c : A}
    (e12 : t₁ = a • t₂) (e23 : t₂ = b • t₃) (e13 : t₁ = c • t₃)
    (hinj : Function.Injective (fun r : A => r • t₃)) :
    a * b = c := by
  apply hinj
  show (a * b) • t₃ = c • t₃
  rw [mul_smul, ← e23, ← e12, e13]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4] A section's preimage of a preimage.** -/
theorem preimage_preimage_section {X T' : Scheme.{u}} (f : X ⟶ T') (z : T' ⟶ X)
    (hz : z ≫ f = 𝟙 T') (V : T'.Opens) : z ⁻¹ᵁ (f ⁻¹ᵁ V) = V := by
  have h : z ⁻¹ᵁ (f ⁻¹ᵁ V) = (z ≫ f) ⁻¹ᵁ V := rfl
  rw [h, hz]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4] The pulled-back trivialization, at a chart presented as an equal open.**
`subst` on the open avoids the motive problems that rewriting inside `restrictFunctor`
and `unitObj` would create. -/
theorem nonempty_restrictPullbackTrivialization_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Y.Modules) (U : Y.Opens) (V : X.Opens) (hV : V = f ⁻¹ᵁ U)
    (e : (restrictFunctor U.ι).obj N ≅ unitObj U.toScheme) :
    Nonempty ((restrictFunctor V.ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) ≅ unitObj V.toScheme) := by
  subst hV
  exact ⟨restrictPullbackTrivialization f N U e⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4] Chart trivializations of `N := z^* L`.** A trivialization of `L` over the
preimage chart `f ⁻¹ᵁ U` gives one of `z^* L` over `U` itself, because `z` is a section
of `f`. This is the first step of the revised descent: the base bundle is `z^* L`, and
its charts are the base charts. -/
theorem nonempty_trivialization_pullback_section {X T' : Scheme.{u}} (f : X ⟶ T')
    (z : T' ⟶ X) (hz : z ≫ f = 𝟙 T') (L : X.Modules) (U : T'.Opens)
    (e : (restrictFunctor (f ⁻¹ᵁ U).ι).obj L ≅ unitObj (f ⁻¹ᵁ U).toScheme) :
    Nonempty ((restrictFunctor U.ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L) ≅ unitObj U.toScheme) :=
  nonempty_restrictPullbackTrivialization_of_eq z L (f ⁻¹ᵁ U) U
    (preimage_preimage_section f z hz U).symm e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4 revised, step 2] Chart trivializations of `f^*(z^* L)`.** Composing the two
pullback transports: the twist factor is trivial on exactly the charts `L` is. -/
theorem nonempty_trivialization_pullback_section_pullback {X T' : Scheme.{u}}
    (f : X ⟶ T') (z : T' ⟶ X) (hz : z ≫ f = 𝟙 T') (L : X.Modules) (U : T'.Opens)
    (e : (restrictFunctor (f ⁻¹ᵁ U).ι).obj L ≅ unitObj (f ⁻¹ᵁ U).toScheme) :
    Nonempty ((restrictFunctor (f ⁻¹ᵁ U).ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)) ≅
      unitObj (f ⁻¹ᵁ U).toScheme) := by
  obtain ⟨eN⟩ := nonempty_trivialization_pullback_section f z hz L U e
  exact ⟨restrictPullbackTrivialization f _ U eN⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4 revised, step 3] The twisted bundle is trivial on every chart.** With
`N := z^* L`, the twist `L ⊗ (f^* N)^∨` is trivial on exactly the charts where `L` is:
the dual of a trivialized module is trivialized (`dualRestrictIsoOfRestrictIso`) and the
tensor of two trivializations is one (W3.3). Its comparison units are the ones whose
`z`-values cancel — which is what makes the rigidified glue lemma apply. -/
theorem nonempty_trivialization_twisted {X T' : Scheme.{u}}
    (f : X ⟶ T') (z : T' ⟶ X) (hz : z ≫ f = 𝟙 T') (L : X.Modules) (U : T'.Opens)
    (e : (restrictFunctor (f ⁻¹ᵁ U).ι).obj L ≅ unitObj (f ⁻¹ᵁ U).toScheme) :
    Nonempty ((restrictFunctor (f ⁻¹ᵁ U).ι).obj
        (tensorObj L (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)))) ≅
      unitObj (f ⁻¹ᵁ U).toScheme) := by
  obtain ⟨eFN⟩ := nonempty_trivialization_pullback_section_pullback f z hz L U e
  exact nonempty_tensorObj_restrict_trivialization (f ⁻¹ᵁ U) e
    (dualRestrictIsoOfRestrictIso _ (f ⁻¹ᵁ U) eFN)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3 — THE UN-NORMALIZED DESCENT]** A module on the total space that is trivial over
the preimage of each member of a base cover is the pullback of a bundle on the base,
namely of `N = z^* L`. This is the "differs by `f^*`" statement the relative theorem of
the square needs — the exact-triviality conclusion of
`nonempty_unitObj_iso_of_chart_trivializations` is false in general (the
Poincaré/biextension obstruction survives on charts), and this is its correct form.

The proof twists by `(f^* z^* L)^∨`, whose chart trivializations are supplied by
`nonempty_trivialization_twisted`, applies the rigidified glue to the twist, and cancels
the dual with `nonempty_eval_iso` + `nonempty_iso_of_tensorObj_unitObj`.

The normalization hypothesis is stated *for the twisted bundle*: it says the comparison
units of `L ⊗ (f^*z^*L)^∨` have `z`-value `1`. That is the cocycle cancellation — the one
input still to be discharged, and the only place the rigidification enters. -/
theorem nonempty_iso_pullback_section_of_chart_trivializations
    (hp : UniversallyOConnected p)
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (L : (pullback p g).Modules) {ι : Type u} (U : ι → T.Opens) (hU : iSup U = ⊤)
    (hL : IsInvertible L)
    (e : ∀ i, (restrictFunctor (pullback.snd p g ⁻¹ᵁ U i).ι).obj L ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (etw : ∀ i, (restrictFunctor (pullback.snd p g ⁻¹ᵁ U i).ι).obj
        (tensorObj L (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)))) ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (hnorm : ∀ i j, ∀ u : Γ(pullback p g,
        pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j),
      ((tensorObj L (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)))).presheaf.map
          (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
            (pullback.snd p g ⁻¹ᵁ U j)).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (etw i))
        = u • (tensorObj L (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd p g)).obj
              ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)))).presheaf.map
          (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
            (pullback.snd p g ⁻¹ᵁ U j)).op
          (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U j) (etw j))) →
      (Scheme.Hom.appLE z (pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j)
        (U i ⊓ U j) (le_inf_preimage_preimage g hz (U i) (U j))).hom u = 1)
    (hgen : ∀ (i : ι) (W : (pullback p g).Opens)
      (hW : W ≤ pullback.snd p g ⁻¹ᵁ U i),
      Function.Bijective fun r : Γ(pullback p g, W) =>
        r • (tensorObj L (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd p g)).obj
              ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)))).presheaf.map
          (homOfLE hW).op (generatorOfRestrictIso (pullback.snd p g ⁻¹ᵁ U i) (etw i))) :
    Nonempty (L ≅ (AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)) := by
  classical
  -- the twist is trivial
  obtain ⟨etriv⟩ := nonempty_unitObj_iso_of_chart_trivializations g hp hz
    (tensorObj L (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
      (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L))))
    U hU etw hnorm hgen
  -- and the twist factor pairs with `f^* N` to the unit
  have hM : IsInvertible ((AlgebraicGeometry.Scheme.Modules.pullback
      (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)) :=
    (hL.pullback z).pullback (pullback.snd p g)
  exact nonempty_iso_of_tensorObj_unitObj ⟨etriv.symm⟩ (nonempty_eval_iso hM)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.5] The tensor of two chart trivializations, as an explicit iso.** The definitional
form of `nonempty_tensorObj_restrict_trivialization`. The cocycle computation needs *this*
and not a choice: the generator it produces must be the tensor of the two generators, since
an arbitrary choice would shift each chart's generator by a unit and destroy the
normalization along the zero section. -/
noncomputable def tensorObjRestrictTrivialization {X : Scheme.{u}} {M L : X.Modules}
    (U : X.Opens)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    (restrictFunctor U.ι).obj (tensorObj M L) ≅ unitObj U.toScheme :=
  (restrictFunctorIsoPullback U.ι).app (tensorObj M L) ≪≫
    pullbackTensorObjIsoOfIsOpenImmersion U.ι M L ≪≫
      tensorObjCongr ((restrictFunctorIsoPullback U.ι).symm.app M ≪≫ eM)
        ((restrictFunctorIsoPullback U.ι).symm.app L ≪≫ eL) ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorObjUnitIso (unitObj U.toScheme)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.5] Comparison units multiply under `tensorSection`.** If two module sections
are related by scalars, so are their pure tensors — with the product scalar. Together
with `tensorSection_restrict` (naturality) this is the whole cocycle computation for the
twisted bundle: `u'ᵢⱼ = uᵢⱼ · vᵢⱼ`. -/
theorem tensorSection_comparison {X : Scheme.{u}} (M N : X.Modules) (V : X.Opens)
    (a b : Γ(X, V)) (x x' : Γ(M, V)) (y y' : Γ(N, V))
    (hx : x = a • x') (hy : y = b • y') :
    tensorSection M N V x y = (a * b) • tensorSection M N V x' y' := by
  subst hx
  subst hy
  rw [tensorSection_smul_left, tensorSection_smul_right, ← mul_smul]

noncomputable local instance descentModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance mulCommutativeRingCatSheaf (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.5b] The dual frame's comparison unit is the inverse.** If two coefficient-one
frames of `M` differ by a unit `u`, their dual frames differ by `u⁻¹` — *after pairing
against the first frame*. Stated in the pairing form, which is what the cocycle argument
consumes and which needs no nondegeneracy input: both sides pair to `1` against
`x_e`. -/
theorem dualPairing_frame_comparison {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e f : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (u : Γ(X, U)) (v : Γ(X, U)) (huv : u * v = 1)
    (hs : overTrivializationSection M U e 1 = u • overTrivializationSection M U f 1) :
    (dualPairing M).val.app (Opposite.op U)
        (tensorSection M (Scheme.Modules.dualObj M) U
          (overTrivializationSection M U e 1)
          (v • overTrivializationSection (Scheme.Modules.dualObj M) U
            (SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U f) 1)) =
      (show Γ(X, U) from 1) := by
  rw [tensorSection_smul_right, _root_.map_smul, hs, tensorSection_smul_left,
    _root_.map_smul, dualPairing_overTrivializationSection_one M U f,
    smul_eq_mul, smul_eq_mul, mul_one, mul_comm v u, huv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.6] The twisted bundle's comparison relation.** On an overlap, the pure-tensor
section's comparison unit is the product of the two factors' comparison units. This is
the `hu` hypothesis of `nonempty_unitObj_iso_of_normalized_glue` for the twisted bundle,
assembled from `tensorSection_restrict` (naturality) and `tensorSection_comparison`
(bilinearity). -/
theorem tensorSection_restrict_comparison {X : Scheme.{u}} (M N : X.Modules)
    {V₁ V₂ W : X.Opens} (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) (a b : Γ(X, W))
    (x₁ : Γ(M, V₁)) (x₂ : Γ(M, V₂)) (y₁ : Γ(N, V₁)) (y₂ : Γ(N, V₂))
    (hx : M.val.map (homOfLE h₁).op x₁ = a • M.val.map (homOfLE h₂).op x₂)
    (hy : N.val.map (homOfLE h₁).op y₁ = b • N.val.map (homOfLE h₂).op y₂) :
    (MonoidalCategory.tensorObj M N).val.map (homOfLE h₁).op
        (tensorSection M N V₁ x₁ y₁) =
      (a * b) • (MonoidalCategory.tensorObj M N).val.map (homOfLE h₂).op
        (tensorSection M N V₂ x₂ y₂) := by
  rw [tensorSection_restrict M N h₁ x₁ y₁, tensorSection_restrict M N h₂ x₂ y₂]
  exact tensorSection_comparison M N W a b _ _ _ _ hx hy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.6] The cocycle cancellation, numerically.** If the twist factor is the pullback
of the inverse of the `z`-value of the comparison unit, then the product's `z`-value is
`1` — the `hnorm` hypothesis of `nonempty_unitObj_iso_of_normalized_glue`. This is the
final step of the un-normalized descent: everything above it produces exactly this shape,
and `appLE_z_appLE_snd_eq_self` is what makes the two `z`-values cancel. -/
theorem appLE_z_mul_pullback_inv_eq_one
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (Wb : T.Opens) (e : Wb ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ Wb))
    (a b : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ Wb)) (c : Γ(T, Wb)ˣ)
    (hc : (Scheme.Hom.appLE z (pullback.snd p g ⁻¹ᵁ Wb) Wb e).hom a = (c : Γ(T, Wb)))
    (hb : b = (Scheme.Hom.appLE (pullback.snd p g) Wb
      (pullback.snd p g ⁻¹ᵁ Wb) le_rfl).hom (↑c⁻¹ : Γ(T, Wb))) :
    (Scheme.Hom.appLE z (pullback.snd p g ⁻¹ᵁ Wb) Wb e).hom (a * b) = 1 := by
  rw [map_mul, hc, hb, appLE_z_appLE_snd_eq_self g hz Wb e, Units.mul_inv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.7] The tensor of two coefficient-one sections is the coefficient-one section of
the tensor frame.** Coefficients multiply
(`overTrivializationOfRestrictIso_tensorSection_coefficient`) and a section is determined
by its coefficient (`overTrivializationSection_coefficient_self`), so `1 · 1 = 1` pins the
pure tensor exactly — not merely up to a unit, which is what the descent needs: a unit
ambiguity here would shift each chart's generator and destroy the normalization along the
zero section. -/
theorem tensorSection_one_one {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (eM : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (eN : N.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    tensorSection M N U
        (overTrivializationSection M U
          (Scheme.Modules.overTrivializationOfRestrictIso M U eM) 1)
        (overTrivializationSection N U
          (Scheme.Modules.overTrivializationOfRestrictIso N U eN) 1) =
      overTrivializationSection (MonoidalCategory.tensorObj M N) U
        (Scheme.Modules.overTrivializationOfRestrictIso
          (MonoidalCategory.tensorObj M N) U
          (restrictMonoidalTensorIso U.ι M N ≪≫
            (eM ⊗ᵢ eN) ≪≫ unitObjTensorIso U.toScheme)) 1 := by
  set x := overTrivializationSection M U
    (Scheme.Modules.overTrivializationOfRestrictIso M U eM) 1 with hx
  set y := overTrivializationSection N U
    (Scheme.Modules.overTrivializationOfRestrictIso N U eN) 1 with hy
  set eT := Scheme.Modules.overTrivializationOfRestrictIso
    (MonoidalCategory.tensorObj M N) U
    (restrictMonoidalTensorIso U.ι M N ≪≫
      (eM ⊗ᵢ eN) ≪≫ unitObjTensorIso U.toScheme) with heT
  have hcoeff := overTrivializationOfRestrictIso_tensorSection_coefficient M N U eM eN x y
  simp only [hx, hy, overTrivializationSection_coefficient, mul_one] at hcoeff
  have hself := overTrivializationSection_coefficient_self
    (MonoidalCategory.tensorObj M N) U eT (tensorSection M N U x y)
  rw [← hself, heT]
  exact congrArg _ hcoeff

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.7] A coefficient-one frame section generates.** Scaling it is scaling `1` in the
structure sheaf, so the map is bijective. With `tensorSection_one_one` this is the `hbij`
input of the rigidified glue for the twisted bundle. -/
theorem bijective_smul_overTrivializationSection_one {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective
      (fun r : Γ(X, U) => r • overTrivializationSection M U e (1 : Γ(X, U))) := by
  have hkey : ∀ r : Γ(X, U), r • overTrivializationSection M U e (1 : Γ(X, U))
      = overTrivializationSection M U e r := by
    intro r
    rw [overTrivializationSection_smul, mul_one]
  have hsec : Function.Bijective
      (fun r : Γ(X, U) => overTrivializationSection M U e r) := by
    constructor
    · intro a b h
      replace h : overTrivializationSection M U e a =
        overTrivializationSection M U e b := h
      have ha := overTrivializationSection_coefficient M U e a
      have hbb := overTrivializationSection_coefficient M U e b
      rw [h] at ha
      exact ha.symm.trans hbb
    · intro y
      exact ⟨e.hom.val.app (.op (Over.mk (𝟙 U))) y,
        overTrivializationSection_coefficient_self M U e y⟩
  simpa only [hkey] using hsec

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.7c] The coefficient-one section generates on every subopen.** Restricting it
gives the coefficient-one section of the restricted frame
(`overTrivializationSection_restrict`), so `bijective_smul_overTrivializationSection_one`
applies there too. This is the `hbij` hypothesis of
`nonempty_unitObj_iso_of_normalized_glue` in the exact form it is stated. -/
theorem bijective_smul_restrict_overTrivializationSection_one {X : Scheme.{u}}
    (M : X.Modules) {U W : X.Opens} (hW : W ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective (fun r : Γ(X, W) =>
      r • M.presheaf.map (homOfLE hW).op
        (overTrivializationSection M U e (1 : Γ(X, U)))) := by
  have h := overTrivializationSection_restrict M hW e (1 : Γ(X, U))
  rw [map_one] at h
  rw [h]
  exact bijective_smul_overTrivializationSection_one M W _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.8] THE TWISTED GLUE.** With coefficient-one generators built as pure tensors,
the rigidified glue applies to `L ⊗ D` from purely chart-level data: the two factors'
comparison units, and the single normalization `z(uᵢⱼ · vᵢⱼ) = 1`. Every input is a
proved lemma — `tensorSection_restrict_comparison` for `hu`, `tensorSection_one_one` plus
`bijective_smul_restrict_overTrivializationSection_one` for `hbij`. -/
theorem nonempty_unitObj_iso_tensorObj_of_frames
    (hp : UniversallyOConnected p)
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (L D : (pullback p g).Modules)
    {ι : Type u} (U : ι → T.Opens) (hU : iSup U = ⊤)
    (eL : ∀ i, L.restrict (pullback.snd p g ⁻¹ᵁ U i).ι ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (eD : ∀ i, D.restrict (pullback.snd p g ⁻¹ᵁ U i).ι ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (u v : ∀ i j, Γ(pullback p g,
      pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j))
    (hu : ∀ i j, L.presheaf.map
        (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection L (pullback.snd p g ⁻¹ᵁ U i)
          (Scheme.Modules.overTrivializationOfRestrictIso L _ (eL i)) 1) =
      u i j • L.presheaf.map
        (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection L (pullback.snd p g ⁻¹ᵁ U j)
          (Scheme.Modules.overTrivializationOfRestrictIso L _ (eL j)) 1))
    (hv : ∀ i j, D.presheaf.map
        (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection D (pullback.snd p g ⁻¹ᵁ U i)
          (Scheme.Modules.overTrivializationOfRestrictIso D _ (eD i)) 1) =
      v i j • D.presheaf.map
        (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection D (pullback.snd p g ⁻¹ᵁ U j)
          (Scheme.Modules.overTrivializationOfRestrictIso D _ (eD j)) 1))
    (hnorm : ∀ i j, (Scheme.Hom.appLE z
        (pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j) (U i ⊓ U j)
        (le_inf_preimage_preimage g hz (U i) (U j))).hom (u i j * v i j) = 1) :
    Nonempty (unitObj (pullback p g) ≅ MonoidalCategory.tensorObj L D) := by
  classical
  refine nonempty_unitObj_iso_of_normalized_glue g hp hz
    (MonoidalCategory.tensorObj L D) U hU
    (fun i => tensorSection L D (pullback.snd p g ⁻¹ᵁ U i)
      (overTrivializationSection L _
        (Scheme.Modules.overTrivializationOfRestrictIso L _ (eL i)) 1)
      (overTrivializationSection D _
        (Scheme.Modules.overTrivializationOfRestrictIso D _ (eD i)) 1))
    (fun i j => u i j * v i j) (fun i j => ?_) hnorm (fun i W hW => ?_)
  · exact tensorSection_restrict_comparison L D _ _ (u i j) (v i j) _ _ _ _
      (hu i j) (hv i j)
  · rw [tensorSection_one_one L D _ (eL i) (eD i)]
    exact bijective_smul_restrict_overTrivializationSection_one _ hW _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.9] Untwisting.** A trivialization of `L ⊗ D` (monoidal) where `D` is the dual of
an invertible `M` identifies `L` with `M`: transport to `tensorObj` along
`monoidalTensorObjIso`, then cancel `D` against `nonempty_eval_iso`. -/
theorem nonempty_iso_of_tensorObj_dual_trivial {X : Scheme.{u}} (L M : X.Modules)
    (hM : IsInvertible M)
    (h : Nonempty (unitObj X ≅ MonoidalCategory.tensorObj L (dualObj M))) :
    Nonempty (L ≅ M) := by
  have h' : Nonempty (Scheme.Modules.tensorObj L (dualObj M) ≅ unitObj X) :=
    ⟨(monoidalTensorObjIso L (dualObj M)).symm ≪≫ h.some.symm⟩
  exact nonempty_iso_of_tensorObj_unitObj h' (nonempty_eval_iso hM)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.10 — THE UN-NORMALIZED DESCENT, FROM CHART FRAMES]** An invertible module on the
total space is the pullback of `z^* L` as soon as, on the preimage of a base cover, it and
the dual of `f^*(z^* L)` carry frames whose comparison units cancel along `z`. This is the
"differs by `f^*`" form of the relative theorem of the square, with **no** residual
hypothesis about generators: `hu`, `hv` and `hnorm` are all statements about the two
comparison units. -/
theorem nonempty_iso_pullback_section_of_frames
    (hp : UniversallyOConnected p)
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (L : (pullback p g).Modules) (hL : IsInvertible L)
    {ι : Type u} (U : ι → T.Opens) (hU : iSup U = ⊤)
    (eL : ∀ i, L.restrict (pullback.snd p g ⁻¹ᵁ U i).ι ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (eD : ∀ i, (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.snd p g)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L))).restrict
        (pullback.snd p g ⁻¹ᵁ U i).ι ≅
      unitObj ((pullback.snd p g ⁻¹ᵁ U i : (pullback p g).Opens)).toScheme)
    (u v : ∀ i j, Γ(pullback p g,
      pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j))
    (hu : ∀ i j, L.presheaf.map
        (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection L (pullback.snd p g ⁻¹ᵁ U i)
          (Scheme.Modules.overTrivializationOfRestrictIso L _ (eL i)) 1) =
      u i j • L.presheaf.map
        (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection L (pullback.snd p g ⁻¹ᵁ U j)
          (Scheme.Modules.overTrivializationOfRestrictIso L _ (eL j)) 1))
    (hv : ∀ i j, (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L))).presheaf.map
        (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection _ (pullback.snd p g ⁻¹ᵁ U i)
          (Scheme.Modules.overTrivializationOfRestrictIso _ _ (eD i)) 1) =
      v i j • (dualObj ((AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L))).presheaf.map
        (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i)
          (pullback.snd p g ⁻¹ᵁ U j)).op
        (overTrivializationSection _ (pullback.snd p g ⁻¹ᵁ U j)
          (Scheme.Modules.overTrivializationOfRestrictIso _ _ (eD j)) 1))
    (hnorm : ∀ i j, (Scheme.Hom.appLE z
        (pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j) (U i ⊓ U j)
        (le_inf_preimage_preimage g hz (U i) (U j))).hom (u i j * v i j) = 1) :
    Nonempty (L ≅ (AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback z).obj L)) :=
  nonempty_iso_of_tensorObj_dual_trivial L _
    ((hL.pullback z).pullback (pullback.snd p g))
    (nonempty_unitObj_iso_tensorObj_of_frames g hp hz L _ U hU eL eD u v hu hv hnorm)

end ModularCurves
