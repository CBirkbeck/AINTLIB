/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FullLevelPairing
import ModularCurves.Moduli.GammaHRepresentability

/-!
# The level trivialisation commutes with base change (route β, item (A) step 1)

`fullLevelHom_pullAlong` says the level trivialisation is compatible with base change:
`constSchemeMapAlong` followed by `fullLevelHom L` is `fullLevelHom` of the pulled-back level
structure followed by `torsionBaseChangeHom`.

This lives in its own file only because of an import: `Point.asSection_add`
(`Moduli/GammaHRepresentability.lean`, and in namespace `ModularCurves` rather than
`ModularCurves.EllipticCurve`, unlike its sibling `Point.asSection_zsmul`) is not in
`WeilPairing/FullLevelPairing.lean`'s closure, and importing moduli representability *into* the
group-scheme layer would invert the intended dependency direction. A leaf file importing both is the
cycle-free option.

The proof works the **right-hand** side down: rewriting the left first unfolds
`↑(v₀ • P + v₁ • Q)` into a `CartesianMonoidalCategory.lift …` normal form that nothing matches
afterwards.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ} [NeZero N]

/-- **(route β, item (A) step 1, the section identity)** Pulling a level basis back along `σ` and
then forming the combination labelled `v` is the same as forming the combination first and pulling the
result back: `asSection ∘ pull` is `ℤ`-linear.

`Point.pull_add` / `_zsmul` and `Point.asSection_add` / `_zsmul`; the final `rfl` is
`(L.pullAlong σ).1.i = Point.asSection E σ (Point.pull E σ L.1.i)`, true by definition. -/
theorem asSection_pull_basisComb {T' : Scheme.{u}} (σ : T' ⟶ S) (L : E.FullLevelPt N)
    (v : Fin 2 → ZMod N) :
    EllipticCurve.Point.asSection E σ (EllipticCurve.Point.pull E σ
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)) =
      ((v 0).val : ℤ) • (L.pullAlong σ).1.1 + ((v 1).val : ℤ) • (L.pullAlong σ).1.2 := by
  rw [EllipticCurve.Point.pull_add, EllipticCurve.Point.pull_zsmul,
    EllipticCurve.Point.pull_zsmul, Point.asSection_add,
    EllipticCurve.Point.asSection_zsmul, EllipticCurve.Point.asSection_zsmul]
  rfl

/-- **(route β, item (A) step 1, the torsion hypothesis)** The basis combination labelled `v` is
killed by `N` — the side condition `fullLevelHom` carries, extracted so that
`comp_pointToTorsion_of_eq` can be applied to it. -/
theorem basisComb_comp_mulByHom {L : E.FullLevelPt N} (v : Fin 2 → ZMod N) :
    ((((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2 : E.Point (𝟙 S)) : S ⟶ E.E) ≫
        E.mulByHom N =
      (𝟙 S) ≫ E.zero :=
  (E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
    rw [smul_add, smul_comm (N : ℤ) ((v 0).val : ℤ) L.1.1,
      smul_comm (N : ℤ) ((v 1).val : ℤ) L.1.2, L.2.1.1, L.2.1.2, smul_zero, smul_zero, add_zero])

/- **`fullLevelHom_pullAlong` — remaining choreography.** With the two lemmas above, plus
`pointToTorsion_asSection_torsionBaseChangeHom` and `comp_pointToTorsion_of_eq`
(`WeilPairing/TorsionSqBaseChange.lean`), the proof runs:

  refine Sigma.hom_ext _ _ fun v => ?_
  rw [← Category.assoc, ι_constSchemeMapAlong]
  simp only [fullLevelHom, Category.assoc, Sigma.ι_desc, Sigma.ι_desc_assoc]
  simp only [← E.asSection_pull_basisComb σ L v]   -- `rw` FAILS here (motive not type correct: the
                                                  -- combination sits in `pointToTorsion`'s dependent
                                                  -- proof argument); `simp only` handles it.
  refine Eq.trans (E.comp_pointToTorsion_of_eq σ _ (E.basisComb_comp_mulByHom v)
      (Category.comp_id σ) ?_) ?_
  · -- `(σ ≫ ↑comb) ≫ mulByHom N = σ ≫ zero`
  · exact (E.pointToTorsion_asSection_torsionBaseChangeHom σ _ _ _).symm

Everything up to and including the `simp only [← …]` step is verified to work. What remains is
calibrating the last two steps against the actual goal: leaving `comp_pointToTorsion_of_eq`'s point and
`hy` arguments as `_` produced an application type mismatch, so they must be spelled out. -/

end EllipticCurve

end ModularCurves
