/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TorsionCombination

/-!
# Points of the combination-clopen locus

The scheme-side point spec of `fullLevelLocus`: a `T`-point of the locus over
`g : T ⟶ S` is the same as a pair of `T`-points of `E[N]` over `g` all of whose
nontrivial combinations avoid the zero section topologically.

* `torsionPairSectionsEquiv` — points of `E[N] ×_S E[N]` over `g` are pairs of points
  of `E[N]` over `g`.
* `fullLevelLocusSectionsEquiv` — points of the locus are points of the pair scheme
  landing in the full-level set (open-immersion factorisation).
* `comp_combinationHom` — the combination morphisms are natural in `T`-points:
  `w ≫ c_v` is the torsion point of the `v`-combination of the legs.

The group-theoretic translation (torsion points, `PairGeneratesOfCardSq`, geometric
fibres) is the `Moduli`-side layer.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### Points of the pair scheme -/

/-- `T`-points of `E[N] ×_S E[N]` over `g` are pairs of `T`-points of `E[N]` over
`g`. -/
noncomputable def torsionPairSectionsEquiv {T : Scheme.{u}} (g : T ⟶ S) :
    { w : T ⟶ E.torsionPair N // w ≫ E.torsionPairπ N = g } ≃
      { ab : (T ⟶ E.torsion N) × (T ⟶ E.torsion N) //
        ab.1 ≫ E.torsionπ N = g ∧ ab.2 ≫ E.torsionπ N = g } where
  toFun w := ⟨⟨w.1 ≫ pullback.fst _ _, w.1 ≫ pullback.snd _ _⟩,
    by rw [Category.assoc]; exact w.2,
    by
      rw [Category.assoc, show pullback.snd (E.torsionπ N) (E.torsionπ N) ≫
        E.torsionπ N = E.torsionPairπ N from (pullback.condition).symm]
      exact w.2⟩
  invFun ab := ⟨pullback.lift ab.1.1 ab.1.2 (ab.2.1.trans ab.2.2.symm),
    by rw [← Category.assoc, pullback.lift_fst]; exact ab.2.1⟩
  left_inv w := Subtype.ext (by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd])
  right_inv ab := Subtype.ext (Prod.ext (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _))

/-! ### Naturality of the combination morphisms -/

/-- Composition with `pointToTorsion` is computed on the underlying `E`-points:
`w ≫ pointToTorsion x hx` is `pointToTorsion` of the composite point. -/
theorem comp_pointToTorsion {T T' : Scheme.{u}} {g : T ⟶ S} (w : T' ⟶ T)
    (x : E.Point g) (hx : (x : T ⟶ E.E) ≫ E.mulByHom N = g ≫ E.zero) :
    w ≫ E.pointToTorsion x hx = E.pointToTorsion
      (⟨w ≫ (x : T ⟶ E.E), by rw [Category.assoc, x.2]⟩ : E.Point (w ≫ g))
      (by rw [Category.assoc, hx, ← Category.assoc]) := by
  apply pullback.hom_ext
  · show w ≫ E.pointToTorsion x hx ≫ E.torsionι N = _ ≫ E.torsionι N
    rw [E.pointToTorsion_torsionι, E.pointToTorsion_torsionι]
  · show w ≫ E.pointToTorsion x hx ≫ E.torsionπ N = _ ≫ E.torsionπ N
    rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]

/-! ### Points of the locus -/

/-- `T`-points of the full-level locus over `g` are `T`-points of the pair scheme
over `g` whose image lies in the full-level set. -/
noncomputable def fullLevelLocusSectionsEquiv (h : NIsInvertible S N)
    {T : Scheme.{u}} (g : T ⟶ S) :
    { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g } ≃
      { w : T ⟶ E.torsionPair N // w ≫ E.torsionPairπ N = g ∧
        ∀ t : T, w.base t ∈ E.fullLevelSet N } where
  toFun h' := ⟨h'.1 ≫ E.fullLevelLocusι N h,
    by rw [Category.assoc]; exact h'.2,
    fun t => by
      have : (E.fullLevelLocusι N h).base (h'.1.base t) ∈
          Set.range (E.fullLevelLocusι N h).base := Set.mem_range_self _
      rw [Scheme.Opens.range_ι] at this
      exact this⟩
  invFun w := ⟨IsOpenImmersion.lift (E.fullLevelLocusι N h) w.1
      (by
        rw [Scheme.Opens.range_ι]
        rintro x ⟨t, rfl⟩
        exact w.2.2 t),
    by
      rw [show E.fullLevelLocusπ N h = E.fullLevelLocusι N h ≫ E.torsionPairπ N
        from rfl, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact w.2.1⟩
  left_inv h' := Subtype.ext (by
    haveI : Mono (E.fullLevelLocusι N h) := IsOpenImmersion.mono _
    exact (cancel_mono (E.fullLevelLocusι N h)).mp (IsOpenImmersion.lift_fac _ _ _))
  right_inv w := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

end EllipticCurve

end ModularCurves
