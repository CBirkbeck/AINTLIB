/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.GlueTrivialization
import ModularCurves.EllipticCurve.SectionRigidity

/-!
# Rigidified descent: locally trivial on the base ⟹ trivial (Gap A workhorse)

Putting the two halves together. On `E_T = X ×_S T` with `p` universally `O`-connected and
a section `z` of `f = pr₂`:

* `nonempty_unitObj_iso_of_normalized_glue` — an `𝒪`-module with generating sections over
  `f ⁻¹ᵁ U i` for a cover `U` **of the base**, whose comparison units along overlaps restrict
  to `1` on the zero section, is trivial.

The overlap agreement is *not* a hypothesis to be checked cocycle by cocycle: it is forced.
Two generating sections differ by a unit; a unit which is `1` along the zero section is `1`
(`ModularCurves.eq_one_of_pullback_eq_one`, which is just `f_*𝒪 = 𝒪` plus the splitting by
`z`). So normalizing each local section along the zero section makes the family
automatically compatible, and `nonempty_unitObj_iso_of_glue` glues it.

This is what turns the relative theorem of the square into a statement that may be checked
**locally on the base**, where an explicit Weierstrass model and its line function are
available.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)

/-- An open of the base sits inside the `z`-preimage of its `f`-preimage. -/
theorem le_preimage_preimage {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (W : T.Opens) : W ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ W) := by
  intro x hx
  have h : (pullback.snd p g).base (z.base x) = x :=
    congrArg (fun m : T ⟶ T => m.base x) hz
  show (pullback.snd p g).base (z.base x) ∈ W
  rw [h]
  exact hx

/-- The intersection form of `le_preimage_preimage`, matching the shape overlaps take. -/
theorem le_inf_preimage_preimage {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (W W' : T.Opens) :
    W ⊓ W' ≤ z ⁻¹ᵁ (pullback.snd p g ⁻¹ᵁ W ⊓ pullback.snd p g ⁻¹ᵁ W') :=
  fun _ hx => ⟨le_preimage_preimage g hz W hx.1, le_preimage_preimage g hz W' hx.2⟩

/-- **Rigidified descent.** If `L` has generating sections over the `f`-preimages of a cover
of the base, and the units comparing them on overlaps are `1` along the zero section, then
`L` is trivial. -/
theorem nonempty_unitObj_iso_of_normalized_glue (hp : UniversallyOConnected p)
    {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (L : (pullback p g).Modules) {ι : Type u} (U : ι → T.Opens) (hU : iSup U = ⊤)
    (s : ∀ i, Γ(L, pullback.snd p g ⁻¹ᵁ U i))
    (u : ∀ i j, Γ(pullback p g,
      pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j))
    (hu : ∀ i j, L.presheaf.map
        (Opens.infLELeft (pullback.snd p g ⁻¹ᵁ U i) (pullback.snd p g ⁻¹ᵁ U j)).op (s i)
      = u i j • L.presheaf.map
        (Opens.infLERight (pullback.snd p g ⁻¹ᵁ U i) (pullback.snd p g ⁻¹ᵁ U j)).op (s j))
    (hnorm : ∀ i j, (z.appLE (pullback.snd p g ⁻¹ᵁ U i ⊓ pullback.snd p g ⁻¹ᵁ U j)
        (U i ⊓ U j) (le_inf_preimage_preimage g hz (U i) (U j))).hom (u i j) = 1)
    (hbij : ∀ (i : ι) (W : (pullback p g).Opens) (hW : W ≤ pullback.snd p g ⁻¹ᵁ U i),
      Function.Bijective fun r : Γ(pullback p g, W) =>
        r • L.presheaf.map (homOfLE hW).op (s i)) :
    Nonempty (unitObj (pullback p g) ≅ L) := by
  refine nonempty_unitObj_iso_of_glue L (fun i => pullback.snd p g ⁻¹ᵁ U i)
    ((pullback.snd p g).iSup_preimage_eq_top hU) s (fun i j => ?_) hbij
  have hone : u i j = 1 :=
    eq_one_of_pullback_eq_one' g hp hz (U i ⊓ U j) _
      (by ext x; simp) (le_inf_preimage_preimage g hz (U i) (U j)) (hnorm i j)
  rw [hu i j, hone, one_smul]

end ModularCurves
