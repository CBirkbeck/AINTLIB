/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-!
# The relative Picard functor (GME §2.2.2, functor layer of (2.16))

For `p : E ⟶ S` with a section `z : S ⟶ E` (the zero section of an elliptic curve, but
stated for any retraction pair), GME p. 108 introduces the contravariant functor

`Pic_{E/S}(T) = Pic(E ×_S T)/f_T^* Pic(T)` for `f_T : E ×_S T → T`,

and p. 109 gives the working model: "Since we have the 0-section `0 : S ↪ E`, we have a
group homomorphism `0* : Pic(E) → Pic(S)` for which `f*` is a section. Thus
`Pic(E) = Ker(0*) ⊕ Im(f*)`". We take the kernel `Ker(0*)` as the definition (`picRel`)
and record the comparison with the displayed quotient as `nonempty_picRel_mulEquiv_quotient`.

This file is the skeleton produced by the `/develop --decompose` pass recorded in
`.mathlib-quality/decomposition-pic-rel-functor.md`; the degree-0 subfunctor and Abel's
isomorphism `E ≅ Pic⁰` ((2.16) proper) are explicitly deferred there.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.picRel`: the relative Picard group of `T ⟶ S`, as the
  kernel of the zero-section pullback on `Pic (E ×_S T)`.
* `AlgebraicGeometry.Scheme.Modules.picRelFunctor`: `Pic_{E/S}` as a contravariant
  group-valued functor on `S`-schemes.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {S E : Scheme.{u}} (p : E ⟶ S) (z : S ⟶ E) (hz : z ≫ p = 𝟙 S)

variable {T T' T'' : Scheme.{u}}

/-- The base change to `T` of the section `z`: `z_T : T ⟶ E ×_S T`. -/
noncomputable def baseChangeZero (t : T ⟶ S) : T ⟶ Limits.pullback p t :=
  Limits.pullback.lift (t ≫ z) (𝟙 T)
    (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])

/-- The base-changed section is a section of the base-changed structure map. -/
theorem baseChangeZero_snd (t : T ⟶ S) :
    baseChangeZero p z hz t ≫ Limits.pullback.snd p t = 𝟙 T := by
  sorry

/-- **The relative Picard group in its kernel model** (GME p. 109: "Thus
`Pic(E) = Ker(0*) ⊕ Im(f*)` and therefore `Pic_{E/S}` is actually a subfunctor of
`Pic_{/E}`"): classes on `E ×_S T` whose zero-section pullback is trivial. -/
noncomputable def picRel (t : T ⟶ S) : Subgroup (Pic (Limits.pullback p t)) :=
  (Pic.map (baseChangeZero p z hz t)).ker

/-- **Comparison with the displayed definition** (GME p. 108, the definition preceding
(2.16): "`Pic_{E/S}(T) = Pic(E ×_S T)/f_T^* Pic(T)`"): the zero-section splitting
identifies the quotient with the kernel model. -/
theorem nonempty_picRel_mulEquiv_quotient (t : T ⟶ S) :
    Nonempty ((Pic (Limits.pullback p t) ⧸ (Pic.map (Limits.pullback.snd p t)).range) ≃*
      picRel p z hz t) := by
  sorry

/-- The base change `g_E = 1_E ×_S g` of `g : T' ⟶ T` over `S` (GME p. 108: "If
`g : T' → T` is an `S`-morphism, we have `g_E = 1_E ×_S g : E'_T → E_T`"). -/
noncomputable def baseChangeMap {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    Limits.pullback p t' ⟶ Limits.pullback p t :=
  Limits.pullback.map p t' p t (𝟙 E) g (𝟙 S) (by simp) (by simp [hg])

/-- Base change of the zero section is compatible with base change of the curve. -/
theorem baseChangeZero_baseChangeMap {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') :
    baseChangeZero p z hz t' ≫ baseChangeMap p g hg = g ≫ baseChangeZero p z hz t := by
  sorry

/-- Pullback along `g_E` preserves the kernel model (GME p. 108: "This induces
`Pic^ν(g)(L) = g_E^*(L)`"). -/
theorem pic_map_baseChangeMap_mem {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') {L : Pic (Limits.pullback p t)} (hL : L ∈ picRel p z hz t) :
    Pic.map (baseChangeMap p g hg) L ∈ picRel p z hz t' := by
  sorry

/-- Base change of maps is functorial. -/
theorem baseChangeMap_id (t : T ⟶ S) :
    baseChangeMap p (𝟙 T) (Category.id_comp t) = 𝟙 (Limits.pullback p t) := by
  sorry

/-- Base change of maps is functorial. -/
theorem baseChangeMap_comp {t : T ⟶ S} {t' : T' ⟶ S} {t'' : T'' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t') (g' : T'' ⟶ T') (hg' : g' ≫ t' = t'') :
    baseChangeMap p (g' ≫ g) (by rw [Category.assoc, hg, hg']) =
      baseChangeMap p g' hg' ≫ baseChangeMap p g hg := by
  sorry

/-- **`Pic_{E/S}` as a contravariant group functor on `S`-schemes** (GME p. 108: "we
consider the following contravariant functors `Pic_{E/S}, Pic^ν : SCH_{/S} → SETS`";
the group structure is GME p. 108 bottom: "`Pic⁰` is a group functor with the identity
`O_E` under the multiplication: `L · L' = L ⊗ L'`"). -/
noncomputable def picRelFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (picRel p z hz T.unop.hom)
  map {T T'} g := CommGrpCat.ofHom
    (((Pic.map (baseChangeMap p g.unop.left (Over.w g.unop))).comp
      (picRel p z hz T.unop.hom).subtype).codRestrict _
      (fun L => pic_map_baseChangeMap_mem p z hz g.unop.left (Over.w g.unop) L.2))
  map_id := by
    sorry
  map_comp := by
    sorry

end AlgebraicGeometry.Scheme.Modules
