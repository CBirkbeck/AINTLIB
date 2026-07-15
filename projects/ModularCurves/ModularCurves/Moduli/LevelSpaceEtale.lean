/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LevelSpaces
import ModularCurves.GroupScheme.TorsionEtaleTriv
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# [GHA3] Towards étaleness of the full-level space (KM 3.7.1, route β)

The KM 1.6.7 fallback route to `levelSpaceΓπ_etale` (`U_{Γ(N)} → S` is étale for `N`
invertible), avoiding the Weil pairing:

* **β1** — `E[N]` is trivialized by a surjective étale cover `p : T ⟶ S`
  (`torsion_etaleLocal_triv`, PROVEN in `GroupScheme/TorsionEtaleTriv.lean`).
* **β2** — the level space commutes with base change: `U_{Γ(N)}(E) ×_S T ≅ U_{Γ(N)}(E_T)`
  compatibly over the torsion ambient. Mechanism: closed subschemes are determined by their
  factorization predicate (`exists_iso_of_factor_iff` below), and both sides classify Drinfeld
  full-level pairs (`levelSpaceΓ_spec` on either curve, matched through the fibrewise-generation
  form `fullLevel_divisor_iff_naive_gen` whose geometric-point condition composes across base
  changes).
* **β3** — over the trivialized curve the incidence locus is a clopen of the constant scheme
  `((ℤ/N)² × (ℤ/N)²)_T`, hence étale over `T`.
* **β4** — étaleness descends along the surjective flat locally-finitely-presented `p`
  (mathlib `DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` + the fpqc→fppf
  upgrade): `levelSpaceΓπ_etale_of_cover` below.

This file provides the two reusable mechanisms (the mono factorization-predicate uniqueness and
the descent shell); β2/β3 land against them.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

section FactorIff

variable {C : Type*} [Category C]

/-- **Subobjects are determined by their factorization predicate**: two monomorphisms into a
common target through which exactly the same morphisms factor differ by an isomorphism over the
target. (Applied to closed immersions: a closed subscheme is determined by which `V`-points of
the ambient it absorbs.) -/
theorem exists_iso_of_factor_iff {A L L' : C} (i : L ⟶ A) (i' : L' ⟶ A) [Mono i] [Mono i']
    (h : ∀ (V : C) (v : V ⟶ A), (∃ w : V ⟶ L, w ≫ i = v) ↔ ∃ w' : V ⟶ L', w' ≫ i' = v) :
    ∃ e : L ≅ L', e.hom ≫ i' = i := by
  obtain ⟨w, hw⟩ := (h L i).mp ⟨𝟙 L, Category.id_comp i⟩
  obtain ⟨w', hw'⟩ := (h L' i').mpr ⟨𝟙 L', Category.id_comp i'⟩
  refine ⟨⟨w, w', ?_, ?_⟩, hw⟩
  · rw [← cancel_mono i, Category.assoc, hw', hw, Category.id_comp]
  · rw [← cancel_mono i', Category.assoc, hw, hw', Category.id_comp]

end FactorIff

variable {S : Scheme.{u}}

/-- **(β4, the descent shell)** Étaleness descends along any surjective flat
locally-finitely-presented cover of the base: if `X ×_S T → T` is étale then `X → S` is étale.
Instance chain: mathlib's `DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` (fpqc
descent of étaleness, `LocalFlatDescent`) upgraded to the fppf form (`FlatDescent`), which needs
no quasi-compactness of the cover — exactly right for the sigma-assembled trivializing cover of
β1. Applied to `levelSpaceΓπ` this is the final leg of [GHA3]. -/
theorem etale_of_etale_pullback_snd_of_cover {X T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    [Surjective p] [Flat p] [LocallyOfFinitePresentation p]
    (hpb : Etale (pullback.snd f p)) : Etale f :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨‹Surjective p›, ‹Flat p›⟩, ‹LocallyOfFinitePresentation p›⟩ hpb

end ModularCurves
