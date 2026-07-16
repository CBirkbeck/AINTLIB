/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LevelSpaceEtale
import ModularCurves.LevelStructure.CombinationLevel

/-!
# [GHA3 CLOSED] The level-space structure morphism is étale (KM 3.7.1, étale half)

The plug-in: G0's master seam `forall_mem_fullLevelSet_iff_isNaiveFullLevel`
(`LevelStructure/CombinationLevel.lean`, the fibrewise generation dictionary through the
combination locus) composed with the T-D8 dictionary `isFullLevel_iff_naive` instantiates the
`hmaster` hypothesis of `levelSpaceΓ_structure_etale_of_master` (`Moduli/LevelSpaceEtale.lean`).
The level space `U_{Γ(N)}` is thereby identified with the clopen combination locus, and its
structure morphism is étale through `fullLevelLocusπ_etale`.

This file is the meeting point of the two development lines (it must sit downstream of both:
`CombinationLevel` itself imports `LevelSpaceEtale` for the generation criterion).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

open EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- Glue: this development's spelling of the first tautological section agrees with the
carrier-of-record's `torsionMapSection`. -/
lemma asSection_pullAlong_fst_eq {V : Scheme.{u}} (v : V ⟶ E.torsionPair N) :
    EllipticCurve.Point.asSection E (v ≫ E.torsionPairπ N)
        (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N))
      = E.torsionMapSection N (v ≫ E.torsionPairπ N)
          (v ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) (by rw [Category.assoc]) := by
  refine Subtype.ext ?_
  apply pullback.hom_ext
  · show pullback.lift _ (𝟙 V) _ ≫ pullback.fst E.π _
      = pullback.lift _ (𝟙 V) _ ≫ pullback.fst E.π _
    rw [pullback.lift_fst, pullback.lift_fst, Category.assoc]
    rfl
  · show pullback.lift _ (𝟙 V) _ ≫ pullback.snd E.π _
      = pullback.lift _ (𝟙 V) _ ≫ pullback.snd E.π _
    rw [pullback.lift_snd, pullback.lift_snd]

omit [NeZero N] in
/-- Glue (second leg). -/
lemma asSection_pullAlong_snd_eq {V : Scheme.{u}} (v : V ⟶ E.torsionPair N) :
    EllipticCurve.Point.asSection E (v ≫ E.torsionPairπ N)
        (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N))
      = E.torsionMapSection N (v ≫ E.torsionPairπ N)
          (v ≫ pullback.snd (E.torsionπ N) (E.torsionπ N))
          (by rw [Category.assoc, ← pullback.condition]) := by
  refine Subtype.ext ?_
  apply pullback.hom_ext
  · show pullback.lift _ (𝟙 V) _ ≫ pullback.fst E.π _
      = pullback.lift _ (𝟙 V) _ ≫ pullback.fst E.π _
    rw [pullback.lift_fst, pullback.lift_fst, Category.assoc]
    rfl
  · show pullback.lift _ (𝟙 V) _ ≫ pullback.snd E.π _
      = pullback.lift _ (𝟙 V) _ ≫ pullback.snd E.π _
    rw [pullback.lift_snd, pullback.lift_snd]

/-- **THE MASTER IFF (the `hmaster` instance)** — G0's seam
`forall_mem_fullLevelSet_iff_isNaiveFullLevel` plugged through the T-D8 dictionary
`isFullLevel_iff_naive`. -/
theorem master_iff (h : NIsInvertible S N) {V : Scheme.{u}} (v : V ⟶ E.torsionPair N) :
    (E.baseChange (v ≫ E.torsionPairπ N)).IsFullLevel N
        (EllipticCurve.Point.asSection E _
          (EllipticCurve.Point.pullAlong E v (E.torsionPairFst N)))
        (EllipticCurve.Point.asSection E _
          (EllipticCurve.Point.pullAlong E v (E.torsionPairSnd N)))
      ↔ ∀ t : V, v.base t ∈ E.fullLevelSet N := by
  have hNV : NIsInvertible V N := NIsInvertible.of_hom (v ≫ E.torsionPairπ N) h
  rw [isFullLevel_iff_naive _ N hNV, asSection_pullAlong_fst_eq, asSection_pullAlong_snd_eq]
  rw [← E.forall_mem_fullLevelSet_iff_isNaiveFullLevel N (v ≫ E.torsionPairπ N) h
    (v ≫ pullback.fst (E.torsionπ N) (E.torsionπ N))
    (v ≫ pullback.snd (E.torsionπ N) (E.torsionπ N))
    (by rw [Category.assoc]) (by rw [Category.assoc, ← pullback.condition])]
  have hv : pullback.lift (v ≫ pullback.fst (E.torsionπ N) (E.torsionπ N))
      (v ≫ pullback.snd (E.torsionπ N) (E.torsionπ N))
      (((by rw [Category.assoc]) : (v ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) ≫
          E.torsionπ N = v ≫ E.torsionPairπ N).trans
        (((by rw [Category.assoc, ← pullback.condition]) : (v ≫ pullback.snd (E.torsionπ N)
          (E.torsionπ N)) ≫ E.torsionπ N = v ≫ E.torsionPairπ N)).symm) = v := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  rw [hv]

/-- **★★ [GHA3] — `U_{Γ(N)} → S` is étale for `N` invertible (KM 3.7.1, the étale half).**
The composite spelling of `levelSpaceΓπ`. -/
theorem levelSpaceΓ_structure_etale (h : NIsInvertible S N) :
    Etale (levelSpaceΓι E N ≫
      pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) :=
  levelSpaceΓ_structure_etale_of_master E N h (fun v => master_iff E N h v)

end ModularCurves
