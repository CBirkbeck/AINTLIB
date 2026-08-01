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

end ModularCurves
