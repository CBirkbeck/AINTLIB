import ModularCurves.ModularCurve.YRho
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# [T-EQ-3b] Descent of ρ-level structures along flat covers

A `ρ`-level structure over the total space of a quasi-compact flat surjective
cover, whose two pullbacks to the double fibre product agree, descends uniquely
to the base. The engine is mathlib's effective-epi property of qc + flat +
surjective morphisms of schemes (`AlgebraicGeometry.Sites.Fpqc`), applied to the
`N`-torsion base change of the cover (which is again such a cover, by the
cartesian torsion square `isPullback_torsionMapOfEllHom`).

This is the gluing half of the KM 4.7 value-equivalence (T-EQ-3): sections of the
carved quotient produce `ρ`-structures étale-locally (through the torsor and the
dictionary), agreeing on overlaps by `rhoLevelStructureOfFramed_glSmul` (T-EQ-2),
and descend by this module.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ModularCurves

noncomputable section

variable {N : ℕ} [NeZero N]

/-- **[T-EQ-3b-i]** The torsion base change of a qc flat surjective cover is qc
flat surjective (the cartesian torsion square transports the classes). -/
theorem torsionMapOfEllHom_flat_surjective_qc
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    [Flat g.baseHom] [Surjective g.baseHom] [QuasiCompact g.baseHom] :
    Flat (torsionMapOfEllHom g N) ∧ Surjective (torsionMapOfEllHom g N) ∧
      QuasiCompact (torsionMapOfEllHom g N) := by
  have hpb := isPullback_torsionMapOfEllHom g N
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hpb.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip ‹_›

/-- **[T-EQ-3b-i]** The torsion base change of a qc flat surjective cover is an
effective epimorphism of schemes (mathlib's fpqc effective-epi instance). -/
theorem torsionMapOfEllHom_effectiveEpi
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    [Flat g.baseHom] [Surjective g.baseHom] [QuasiCompact g.baseHom] :
    EffectiveEpi (torsionMapOfEllHom g N) := by
  obtain ⟨h1, h2, h3⟩ := torsionMapOfEllHom_flat_surjective_qc (N := N) g
  haveI := h1
  haveI := h2
  haveI := h3
  infer_instance

end

end ModularCurves
