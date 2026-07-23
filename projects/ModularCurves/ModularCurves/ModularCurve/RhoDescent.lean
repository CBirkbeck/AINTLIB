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

/-- **[T-EQ-3b-ii]** The `V_ρ`-side projection of the cover: from the pulled-back
`ρ`-torsion space over `T''` to the one over the base. -/
def vRhoCoverPrj (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    {T'' : Scheme.{0}} (c : T'' ⟶ X.base) :
    pullback (vRhoπ D) (X.pullbackAlong c).structMap ⟶
      pullback (vRhoπ D) X.structMap :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c) (by
    rw [pullback.condition]
    exact (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem vRhoCoverPrj_fst (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    {T'' : Scheme.{0}} (c : T'' ⟶ X.base) :
    vRhoCoverPrj D X c ≫ pullback.fst (vRhoπ D) X.structMap =
      pullback.fst (vRhoπ D) (X.pullbackAlong c).structMap :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem vRhoCoverPrj_snd (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    {T'' : Scheme.{0}} (c : T'' ⟶ X.base) :
    vRhoCoverPrj D X c ≫ pullback.snd (vRhoπ D) X.structMap =
      pullback.snd (vRhoπ D) (X.pullbackAlong c).structMap ≫ c :=
  pullback.lift_snd _ _ _

/-- **[T-EQ-3b-ii]** The `V_ρ`-side projection square is cartesian (pasting). -/
theorem isPullback_vRhoCoverPrj (D : GaloisRepData N)
    (X : EllObj (CommRingCat.of ℚ)) {T'' : Scheme.{0}} (c : T'' ⟶ X.base) :
    IsPullback (vRhoCoverPrj D X c)
      (pullback.snd (vRhoπ D) (X.pullbackAlong c).structMap)
      (pullback.snd (vRhoπ D) X.structMap) c := by
  have hbig := IsPullback.of_hasPullback (vRhoπ D) (X.pullbackAlong c).structMap
  have hfst : vRhoCoverPrj D X c ≫ pullback.fst (vRhoπ D) X.structMap =
      pullback.fst (vRhoπ D) (X.pullbackAlong c).structMap :=
    pullback.lift_fst _ _ _
  rw [← hfst] at hbig
  exact IsPullback.of_right hbig (vRhoCoverPrj_snd D X c)
    (IsPullback.of_hasPullback (vRhoπ D) X.structMap)

/-- **[T-EQ-3b-ii]** The `V_ρ`-side projection is qc flat surjective. -/
theorem vRhoCoverPrj_flat_surjective_qc (D : GaloisRepData N)
    (X : EllObj (CommRingCat.of ℚ)) {T'' : Scheme.{0}} (c : T'' ⟶ X.base)
    [Flat c] [Surjective c] [QuasiCompact c] :
    Flat (vRhoCoverPrj D X c) ∧ Surjective (vRhoCoverPrj D X c) ∧
      QuasiCompact (vRhoCoverPrj D X c) := by
  have hpb := isPullback_vRhoCoverPrj D X c
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) hpb.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip ‹_›⟩

/-- **[T-EQ-3b-ii]** The `V_ρ`-side projection is an effective epimorphism. -/
theorem vRhoCoverPrj_effectiveEpi (D : GaloisRepData N)
    (X : EllObj (CommRingCat.of ℚ)) {T'' : Scheme.{0}} (c : T'' ⟶ X.base)
    [Flat c] [Surjective c] [QuasiCompact c] :
    EffectiveEpi (vRhoCoverPrj D X c) := by
  obtain ⟨h1, h2, h3⟩ := vRhoCoverPrj_flat_surjective_qc D X c
  haveI := h1
  haveI := h2
  haveI := h3
  infer_instance

/-- The torsion cover of a pulled-back structure map is an effective epi (the
`baseHom`-instances transported definitionally). -/
theorem pullbackAlongπ_torsion_effectiveEpi (X : EllObj (CommRingCat.of ℚ))
    {T'' : Scheme.{0}} (c : T'' ⟶ X.base)
    [Flat c] [Surjective c] [QuasiCompact c] :
    EffectiveEpi (torsionMapOfEllHom (X.pullbackAlongπ c) N) := by
  haveI : Flat (X.pullbackAlongπ c).baseHom := ‹Flat c›
  haveI : Surjective (X.pullbackAlongπ c).baseHom := ‹Surjective c›
  haveI : QuasiCompact (X.pullbackAlongπ c).baseHom := ‹QuasiCompact c›
  exact torsionMapOfEllHom_effectiveEpi _

section Descend

variable (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
variable {T'' : Scheme.{0}} (c : T'' ⟶ X.base)
variable [Flat c] [Surjective c] [QuasiCompact c]
variable (α : RhoLevelStructure D (X.pullbackAlong c).structMap
  (X.pullbackAlong c).curve)

/-- **[T-EQ-3b-iii]** The descended trivialization hom (via the effective epi of the
torsion cover). `Hhom` is the double-point agreement of the `V_ρ`-reads. -/
def descTorsionHom
    (Hhom : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ (X.pullbackAlong c).curve.torsion N),
      g₁ ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N =
        g₂ ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N →
      g₁ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X c =
        g₂ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X c) :
    X.curve.torsion N ⟶ pullback (vRhoπ D) X.structMap :=
  haveI : EffectiveEpi (torsionMapOfEllHom (X.pullbackAlongπ c) N) :=
    pullbackAlongπ_torsion_effectiveEpi X c
  EffectiveEpi.desc (torsionMapOfEllHom (X.pullbackAlongπ c) N)
    (α.torsionIso.hom ≫ vRhoCoverPrj D X c) (fun g₁ g₂ h => Hhom g₁ g₂ h)

theorem descTorsionHom_fac (Hhom) :
    torsionMapOfEllHom (X.pullbackAlongπ c) N ≫ descTorsionHom D X c α Hhom =
      α.torsionIso.hom ≫ vRhoCoverPrj D X c :=
  haveI : EffectiveEpi (torsionMapOfEllHom (X.pullbackAlongπ c) N) :=
    pullbackAlongπ_torsion_effectiveEpi X c
  EffectiveEpi.fac _ _ _

/-- **[T-EQ-3b-iii]** The descended trivialization inverse (via the effective epi of
the `V_ρ`-side cover). -/
def descTorsionInv
    (Hinv : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ pullback (vRhoπ D) (X.pullbackAlong c).structMap),
      g₁ ≫ vRhoCoverPrj D X c = g₂ ≫ vRhoCoverPrj D X c →
      g₁ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N =
        g₂ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N) :
    pullback (vRhoπ D) X.structMap ⟶ X.curve.torsion N :=
  haveI : EffectiveEpi (vRhoCoverPrj D X c) := vRhoCoverPrj_effectiveEpi D X c
  EffectiveEpi.desc (vRhoCoverPrj D X c)
    (α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N)
    (fun g₁ g₂ h => Hinv g₁ g₂ h)

theorem descTorsionInv_fac (Hinv) :
    vRhoCoverPrj D X c ≫ descTorsionInv D X c α Hinv =
      α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N :=
  haveI : EffectiveEpi (vRhoCoverPrj D X c) := vRhoCoverPrj_effectiveEpi D X c
  EffectiveEpi.fac _ _ _

/-- **[T-EQ-3b-iii]** The descended trivialization is an isomorphism, over `T`. -/
theorem descTorsion_hom_inv_id (Hhom) (Hinv) :
    descTorsionHom D X c α Hhom ≫ descTorsionInv D X c α Hinv =
      𝟙 (X.curve.torsion N) := by
  haveI : EffectiveEpi (torsionMapOfEllHom (X.pullbackAlongπ c) N) :=
    pullbackAlongπ_torsion_effectiveEpi X c
  haveI : Epi (torsionMapOfEllHom (X.pullbackAlongπ c) N) := inferInstance
  rw [← cancel_epi (torsionMapOfEllHom (X.pullbackAlongπ c) N),
    ← Category.assoc, descTorsionHom_fac, Category.assoc, descTorsionInv_fac,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]

theorem descTorsion_inv_hom_id (Hhom) (Hinv) :
    descTorsionInv D X c α Hinv ≫ descTorsionHom D X c α Hhom =
      𝟙 (pullback (vRhoπ D) X.structMap) := by
  haveI : EffectiveEpi (vRhoCoverPrj D X c) := vRhoCoverPrj_effectiveEpi D X c
  haveI : Epi (vRhoCoverPrj D X c) := inferInstance
  rw [← cancel_epi (vRhoCoverPrj D X c),
    ← Category.assoc, descTorsionInv_fac, Category.assoc, descTorsionHom_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- **[T-EQ-3b-iii]** The descended trivialization lies over `T`. -/
theorem descTorsionHom_over (Hhom) :
    descTorsionHom D X c α Hhom ≫ pullback.snd (vRhoπ D) X.structMap =
      X.curve.torsionπ N := by
  haveI : EffectiveEpi (torsionMapOfEllHom (X.pullbackAlongπ c) N) :=
    pullbackAlongπ_torsion_effectiveEpi X c
  haveI : Epi (torsionMapOfEllHom (X.pullbackAlongπ c) N) := inferInstance
  rw [← cancel_epi (torsionMapOfEllHom (X.pullbackAlongπ c) N),
    ← Category.assoc, descTorsionHom_fac]
  rw [Category.assoc, vRhoCoverPrj_snd, ← Category.assoc, α.over_T]
  exact ((isPullback_torsionMapOfEllHom (X.pullbackAlongπ c) N).w).symm

end Descend

end

end ModularCurves
