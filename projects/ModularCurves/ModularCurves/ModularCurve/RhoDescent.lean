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

-- v4.33 bump: neither the `Scheme`/`CommAlgCat` category instances nor the semireducible
-- component types are transparent enough for the rewrites and instance searches below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- **[T-EQ-3b-iv]** The descended trivialization, packaged. -/
def descTorsionIso
    (Hhom : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ (X.pullbackAlong c).curve.torsion N),
      g₁ ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N =
        g₂ ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N →
      g₁ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X c =
        g₂ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X c)
    (Hinv : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ pullback (vRhoπ D) (X.pullbackAlong c).structMap),
      g₁ ≫ vRhoCoverPrj D X c = g₂ ≫ vRhoCoverPrj D X c →
      g₁ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N =
        g₂ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N) :
    X.curve.torsion N ≅ pullback (vRhoπ D) X.structMap where
  hom := descTorsionHom D X c α Hhom
  inv := descTorsionInv D X c α Hinv
  hom_inv_id := descTorsion_hom_inv_id D X c α Hhom Hinv
  inv_hom_id := descTorsion_inv_hom_id D X c α Hhom Hinv

/-- **[T-EQ-3b-iv]** The coordinate read of the descended trivialization at a
transported point is the original coordinate read (the two reads are reads of the
*same* `V_ρ`-point, by the descent factorization). -/
theorem coord_descTorsionIso (Hhom) (Hinv)
    (t'' : Spec (.of (AlgebraicClosure ℚ)) ⟶ T'')
    (ht : (t'' ≫ c) ≫ X.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x'' : (X.pullbackAlong c).curve.Point t'')
    (hx'' : x''.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      t'' ≫ (X.pullbackAlong c).curve.zero) :
    coord D X.structMap (descTorsionIso D X c α Hhom Hinv)
      (descTorsionHom_over D X c α Hhom) (t'' ≫ c) ht
      (EllHom.mapPoint (X.pullbackAlongπ c) t'' x'')
      (EllHom.mapPoint_torsion (X.pullbackAlongπ c) x'' hx'') =
    coord D (X.pullbackAlong c).structMap α.torsionIso α.over_T t''
      (by
        show t'' ≫ (X.pullbackAlong c).structMap = _
        rw [show (X.pullbackAlong c).structMap = c ≫ X.structMap from rfl,
          ← Category.assoc]
        exact ht) x'' hx'' := by
  refine congrArg (vRhoPointsEquiv D) (Subtype.ext ?_)
  show X.curve.pointToTorsion (EllHom.mapPoint (X.pullbackAlongπ c) t'' x'')
      (EllHom.mapPoint_torsion (X.pullbackAlongπ c) x'' hx'') ≫
      (descTorsionIso D X c α Hhom Hinv).hom ≫
      pullback.fst (vRhoπ D) X.structMap =
    (X.pullbackAlong c).curve.pointToTorsion x'' hx'' ≫
      α.torsionIso.hom ≫ pullback.fst (vRhoπ D) (X.pullbackAlong c).structMap
  rw [← pointToTorsion_mapPoint (X.pullbackAlongπ c) x'' hx'']
  rw [show (descTorsionIso D X c α Hhom Hinv).hom =
    descTorsionHom D X c α Hhom from rfl]
  rw [Category.assoc, ← Category.assoc
    (torsionMapOfEllHom (X.pullbackAlongπ c) N),
    descTorsionHom_fac]
  rw [Category.assoc, vRhoCoverPrj_fst]

end Descend

/-- **[T-EQ-3b-v]** The point transport along an `Ell`-morphism, packaged as an
additive equivalence (its forward map is `EllHom.mapPoint`). -/
noncomputable def mapPointEquiv {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} (t : T ⟶ A.base) :
    A.curve.Point t ≃+ B.curve.Point (t ≫ g.baseHom) :=
  (EllHom.pointTransportEquiv (CommRingCat.of ℚ) g t).trans
    (EllipticCurve.Point.baseChangeEquiv B.curve g.baseHom t)

theorem mapPointEquiv_apply {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} (t : T ⟶ A.base) (x : A.curve.Point t) :
    mapPointEquiv g t x = EllHom.mapPoint g t x := rfl

/-- **[T-EQ-3b-iv]** Geometric points lift through a finite étale surjective cover
(the section-counting argument of `QuotPkg.projQ_geom_surjective`). -/
theorem exists_lift_of_finite_etale_surjective {T' T'' : Scheme.{0}}
    (c : T'' ⟶ T') [IsFinite c] [Etale c] [Surjective c]
    (t : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ T') :
    ∃ t'' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ T'', t'' ≫ c = t := by
  haveI : IsFinite (pullback.snd c t) :=
    MorphismProperty.pullback_snd _ _ ‹IsFinite c›
  haveI : Etale (pullback.snd c t) :=
    MorphismProperty.pullback_snd _ _ ‹Etale c›
  have hne : Nonempty ↑(Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
    ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨x₀⟩ := hne
  have hcard := natCard_sections_eq_finrank (k := AlgebraicClosure ℚ)
    (pullback.snd c t) x₀
  have hpos : 1 ≤ (pullback.snd c t).finrank x₀ := by
    rw [Scheme.Hom.finrank_pullback_snd]
    exact (Scheme.Hom.one_le_finrank_iff_surjective c).mpr ‹Surjective c› _
  obtain ⟨⟨s, hs⟩⟩ := Nat.card_pos_iff.mp (hcard ▸ hpos) |>.1
  refine ⟨s ≫ pullback.fst c t, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs,
    Category.id_comp]

/-- `pointToTorsion` under precomposition: a point whose underlying section is
`k ≫ x.1` reads to `k ≫` the torsion read (the base point is forced). -/
theorem pointToTorsion_comp {S : Scheme.{0}} {E : EllipticCurve S}
    {W W' : Scheme.{0}} (k : W' ⟶ W) {t : W ⟶ S} {t' : W' ⟶ S}
    (x : E.Point t) (x' : E.Point t') (hval : x'.1 = k ≫ x.1)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = t' ≫ E.zero) :
    E.pointToTorsion x' hx' = k ≫ E.pointToTorsion x hx := by
  apply pullback.hom_ext
  · show E.pointToTorsion x' hx' ≫ E.torsionι N =
      (k ≫ E.pointToTorsion x hx) ≫ E.torsionι N
    rw [E.pointToTorsion_torsionι, Category.assoc, E.pointToTorsion_torsionι]
    exact hval
  · show E.pointToTorsion x' hx' ≫ E.torsionπ N =
      (k ≫ E.pointToTorsion x hx) ≫ E.torsionπ N
    rw [E.pointToTorsion_torsionπ, Category.assoc, E.pointToTorsion_torsionπ]
    rw [← x'.2, hval, Category.assoc, x.2]

/-- `torsionPairEval` is congruent in the points (proofs transport). -/
theorem torsionPairEval_congr (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    {W : Scheme.{0}} {t : W ⟶ T} {x₁ x₂ y₁ y₂ : E.Point t}
    (hx12 : x₁ = x₂) (hy12 : y₁ = y₂)
    (hx : x₁.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y₁.1 ≫ E.mulByHom N = t ≫ E.zero) :
    torsionPairEval D sT t x₁ y₁ hx hy =
      torsionPairEval D sT t x₂ y₂ (hx12 ▸ hx) (hy12 ▸ hy) := by
  subst hx12; subst hy12; rfl

/-- `coordPairLift` is congruent in the points (proofs transport). -/
theorem coordPairLift_congr (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    {W : Scheme.{0}} {t : W ⟶ T} {x₁ x₂ y₁ y₂ : E.Point t}
    (hx12 : x₁ = x₂) (hy12 : y₁ = y₂)
    (hx : x₁.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y₁.1 ≫ E.mulByHom N = t ≫ E.zero) :
    coordPairLift D sT torsionIso hOver t x₁ y₁ hx hy =
      coordPairLift D sT torsionIso hOver t x₂ y₂ (hx12 ▸ hx) (hy12 ▸ hy) := by
  subst hx12; subst hy12; rfl

/-- `torsionPairEval` under precomposition. -/
theorem torsionPairEval_comp (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    {W W' : Scheme.{0}} (k : W' ⟶ W) {t : W ⟶ T} {t' : W' ⟶ T}
    (x y : E.Point t) (x' y' : E.Point t')
    (hxval : x'.1 = k ≫ x.1) (hyval : y'.1 = k ≫ y.1)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = t' ≫ E.zero)
    (hy' : y'.1 ≫ E.mulByHom N = t' ≫ E.zero) :
    torsionPairEval D sT t' x' y' hx' hy' =
      k ≫ torsionPairEval D sT t x y hx hy := by
  have hlift : pullback.lift (f := E.torsionπ N) (g := E.torsionπ N)
      (E.pointToTorsion x' hx') (E.pointToTorsion y' hy')
      (by simp) = k ≫ pullback.lift (f := E.torsionπ N) (g := E.torsionπ N)
      (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact pointToTorsion_comp k x x' hxval hx hx'
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
      exact pointToTorsion_comp k y y' hyval hy hy'
  show pullback.lift (E.pointToTorsion x' hx') (E.pointToTorsion y' hy')
      (by simp) ≫ E.weilPairing N ≫ muNMapAlong sT N ≫ (muNSpecQIso D).hom =
    k ≫ (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
      (by simp) ≫ E.weilPairing N ≫ muNMapAlong sT N ≫ (muNSpecQIso D).hom)
  rw [hlift]
  simp only [Category.assoc]

/-- `coordPairLift` under precomposition. -/
theorem coordPairLift_comp (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    {W W' : Scheme.{0}} (k : W' ⟶ W) {t : W ⟶ T} {t' : W' ⟶ T}
    (x y : E.Point t) (x' y' : E.Point t')
    (hxval : x'.1 = k ≫ x.1) (hyval : y'.1 = k ≫ y.1)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = t' ≫ E.zero)
    (hy' : y'.1 ≫ E.mulByHom N = t' ≫ E.zero) :
    coordPairLift D sT torsionIso hOver t' x' y' hx' hy' =
      k ≫ coordPairLift D sT torsionIso hOver t x y hx hy := by
  apply pullback.hom_ext
  · show pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D) =
      (k ≫ pullback.lift _ _ _) ≫ pullback.fst (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    rw [pointToTorsion_comp k x x' hxval hx hx']
    simp only [Category.assoc]
  · show pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D) =
      (k ≫ pullback.lift _ _ _) ≫ pullback.snd (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
    rw [pointToTorsion_comp k y y' hyval hy hy']
    simp only [Category.assoc]

/-- **[T-EQ-3b-vi]** Naturality of the scheme-level Weil-pairing read along an
`Ell/ℚ`-morphism (the `W`-generic crossing extracted from
`RhoLevelStructure.pull`, riding the DS4-registered `weilPairingEval_mapPoint`
through the `μ_N`-points dictionary). -/
theorem torsionPairEval_mapPoint (D : GaloisRepData N) [Fact (1 < N)]
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {W : Scheme.{0}} (t : W ⟶ A.base) (x y : A.curve.Point t)
    (hx : x.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero)
    (hy : y.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero) :
    torsionPairEval D A.structMap t x y hx hy =
      torsionPairEval D B.structMap (t ≫ g.baseHom)
        (EllHom.mapPoint g t x) (EllHom.mapPoint g t y)
        (EllHom.mapPoint_torsion g x hx) (EllHom.mapPoint_torsion g y hy) := by
  have hoverA : (pullback.lift (A.curve.pointToTorsion x hx)
      (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N) ≫
      muNπ A.base N = t := by
    rw [Category.assoc, A.curve.weilPairing_over N, ← Category.assoc,
      pullback.lift_fst, A.curve.pointToTorsion_torsionπ]
  have h1 : ((muNPointsEquiv B.base N (t ≫ g.baseHom))
      ⟨(pullback.lift (A.curve.pointToTorsion x hx)
          (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N) ≫
        muNMapAlong g.baseHom N, by
          rw [Category.assoc, muNMapAlong_π, ← Category.assoc, hoverA]⟩ :
        Γ(W, ⊤)) =
      ((muNPointsEquiv B.base N (t ≫ g.baseHom))
        ⟨pullback.lift (B.curve.pointToTorsion (EllHom.mapPoint g t x)
              (EllHom.mapPoint_torsion g x hx))
            (B.curve.pointToTorsion (EllHom.mapPoint g t y)
              (EllHom.mapPoint_torsion g y hy)) (by simp) ≫
          B.curve.weilPairing N, by
            rw [Category.assoc, B.curve.weilPairing_over N, ← Category.assoc,
              pullback.lift_fst, B.curve.pointToTorsion_torsionπ]⟩ : Γ(W, ⊤)) := by
    rw [muNPointsEquiv_mapAlong g.baseHom N t
      ⟨pullback.lift (A.curve.pointToTorsion x hx)
          (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N,
        hoverA⟩]
    exact (weilPairingEval_mapPoint g t x y hx hy).symm
  have h3 := congrArg Subtype.val
    ((muNPointsEquiv B.base N (t ≫ g.baseHom)).injective (Subtype.ext h1))
  show pullback.lift (A.curve.pointToTorsion x hx)
      (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N ≫
      muNMapAlong A.structMap N ≫ (muNSpecQIso D).hom =
    pullback.lift (B.curve.pointToTorsion (EllHom.mapPoint g t x)
        (EllHom.mapPoint_torsion g x hx))
      (B.curve.pointToTorsion (EllHom.mapPoint g t y)
        (EllHom.mapPoint_torsion g y hy)) (by simp) ≫
      B.curve.weilPairing N ≫ muNMapAlong B.structMap N ≫ (muNSpecQIso D).hom
  have hstruct : muNMapAlong A.structMap N =
      muNMapAlong g.baseHom N ≫ muNMapAlong B.structMap N :=
    (congrArg (fun m => muNMapAlong m N) g.base_w.symm).trans
      (muNMapAlong_comp g.baseHom B.structMap N)
  rw [hstruct]
  simp only [Category.assoc]
  rw [reassoc_of% h3]

section Fields

variable {D : GaloisRepData N} {X : EllObj (CommRingCat.of ℚ)}
variable {T'' : Scheme.{0}} {c : T'' ⟶ X.base}
variable [Flat c] [Surjective c] [QuasiCompact c]
variable {α : RhoLevelStructure D (X.pullbackAlong c).structMap
  (X.pullbackAlong c).curve}

/-- Kill transfer along the point transport (backwards). -/
theorem point_kill_of_mapPoint_kill {W'' : Scheme.{0}} {t'' : W'' ⟶ T''}
    (x'' : (X.pullbackAlong c).curve.Point t'')
    (hx : (EllHom.mapPoint (X.pullbackAlongπ c) t'' x'').1 ≫
      X.curve.mulByHom N = (t'' ≫ (X.pullbackAlongπ c).baseHom) ≫ X.curve.zero) :
    x''.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      t'' ≫ (X.pullbackAlong c).curve.zero := by
  refine ((X.pullbackAlong c).curve.smul_eq_zero_iff_comp_mulByHom t'' N
    x'').mp ?_
  refine (mapPointEquiv (X.pullbackAlongπ c) t'').injective ?_
  show EllHom.mapPoint (X.pullbackAlongπ c) t'' ((N : ℤ) • x'') =
    EllHom.mapPoint (X.pullbackAlongπ c) t'' 0
  rw [map_zsmul, map_zero]
  exact (X.curve.smul_eq_zero_iff_comp_mulByHom
    (t'' ≫ (X.pullbackAlongπ c).baseHom) N _).mpr hx

/-- **[T-EQ-3b-v]** Additivity of the descended coordinates (lift the geometric
point through the cover, transport, and use the original additivity). -/
theorem descTorsion_coords_additive [IsFinite c] [Etale c] (Hhom) (Hinv)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ X.base)
    (ht : t ≫ X.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : X.curve.Point t)
    (hx : x.1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero)
    (hy : y.1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero)
    (hxy : (x + y).1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero) :
    coord D X.structMap (descTorsionIso D X c α Hhom Hinv)
      (descTorsionHom_over D X c α Hhom) t ht (x + y) hxy =
    coord D X.structMap (descTorsionIso D X c α Hhom Hinv)
      (descTorsionHom_over D X c α Hhom) t ht x hx +
    coord D X.structMap (descTorsionIso D X c α Hhom Hinv)
      (descTorsionHom_over D X c α Hhom) t ht y hy := by
  obtain ⟨t'', rfl⟩ := exists_lift_of_finite_etale_surjective c t
  obtain ⟨x'', rfl⟩ : ∃ x'', EllHom.mapPoint (X.pullbackAlongπ c) t'' x'' = x :=
    ⟨(mapPointEquiv (X.pullbackAlongπ c) t'').symm x,
      (mapPointEquiv (X.pullbackAlongπ c) t'').apply_symm_apply x⟩
  obtain ⟨y'', rfl⟩ : ∃ y'', EllHom.mapPoint (X.pullbackAlongπ c) t'' y'' = y :=
    ⟨(mapPointEquiv (X.pullbackAlongπ c) t'').symm y,
      (mapPointEquiv (X.pullbackAlongπ c) t'').apply_symm_apply y⟩
  have hx'' := point_kill_of_mapPoint_kill x'' hx
  have hy'' := point_kill_of_mapPoint_kill y'' hy
  have hxy'' : (x'' + y'').1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      t'' ≫ (X.pullbackAlong c).curve.zero := by
    refine point_kill_of_mapPoint_kill (x'' + y'') ?_
    rw [map_add]
    exact hxy
  refine Eq.trans (coord_congr D X.structMap _ _ _ ht
    (show EllHom.mapPoint (X.pullbackAlongπ c) t'' x'' +
        EllHom.mapPoint (X.pullbackAlongπ c) t'' y'' =
      EllHom.mapPoint (X.pullbackAlongπ c) t'' (x'' + y'') from
      (map_add _ _ _).symm) hxy) ?_
  refine Eq.trans (coord_descTorsionIso D X c α Hhom Hinv t'' ht (x'' + y'')
    hxy'') ?_
  refine Eq.trans (α.coords_additive t'' _ x'' y'' hx'' hy'' hxy'') ?_
  exact congrArg₂ (· + ·)
    (coord_descTorsionIso D X c α Hhom Hinv t'' ht x'' hx'').symm
    (coord_descTorsionIso D X c α Hhom Hinv t'' ht y'' hy'').symm

/-- **[T-EQ-3b-v]** Pairing compatibility of the descended trivialization (lift the
geometric point, cross the evaluation by the mapPoint register, and use the original
compatibility). -/
theorem descTorsion_pairing_compat [IsFinite c] [Etale c] (Hhom) (Hinv)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ X.base)
    (ht : t ≫ X.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : X.curve.Point t)
    (hx : x.1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero)
    (hy : y.1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero) :
    PairingCompatAt D X.structMap (descTorsionIso D X c α Hhom Hinv)
      (descTorsionHom_over D X c α Hhom) t ht x y hx hy := by
  obtain ⟨t'', rfl⟩ := exists_lift_of_finite_etale_surjective c t
  obtain ⟨x'', rfl⟩ : ∃ x'', EllHom.mapPoint (X.pullbackAlongπ c) t'' x'' = x :=
    ⟨(mapPointEquiv (X.pullbackAlongπ c) t'').symm x,
      (mapPointEquiv (X.pullbackAlongπ c) t'').apply_symm_apply x⟩
  obtain ⟨y'', rfl⟩ : ∃ y'', EllHom.mapPoint (X.pullbackAlongπ c) t'' y'' = y :=
    ⟨(mapPointEquiv (X.pullbackAlongπ c) t'').symm y,
      (mapPointEquiv (X.pullbackAlongπ c) t'').apply_symm_apply y⟩
  have hx'' := point_kill_of_mapPoint_kill x'' hx
  have hy'' := point_kill_of_mapPoint_kill y'' hy
  have hα := α.pairing_compat t'' (by
      show t'' ≫ (X.pullbackAlong c).structMap = _
      rw [show (X.pullbackAlong c).structMap = c ≫ X.structMap from rfl,
        ← Category.assoc]
      exact ht) x'' y'' hx'' hy''
  show (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
      (X.curve.weilPairingEval (EllHom.mapPoint (X.pullbackAlongπ c) t'' x'')
        (EllHom.mapPoint (X.pullbackAlongπ c) t'' y'') hx hy).1 = _
  refine Eq.trans (congrArg
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
    (weilPairingEval_mapPoint (X.pullbackAlongπ c) t'' x'' y'' hx'' hy'')) ?_
  rw [coord_descTorsionIso D X c α Hhom Hinv t'' ht x'' hx'',
    coord_descTorsionIso D X c α Hhom Hinv t'' ht y'' hy'']
  exact hα

/-- **[T-EQ-3b-vi]** The map-level first leg of the descended trivialization at a
transported torsion point (the `W`-generic core of `coord_descTorsionIso`). -/
theorem descTorsionIso_fst_leg (Hhom) (Hinv) {W' : Scheme.{0}} (tW : W' ⟶ T'')
    (x'' : (X.pullbackAlong c).curve.Point tW)
    (hx'' : x''.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      tW ≫ (X.pullbackAlong c).curve.zero) :
    X.curve.pointToTorsion (EllHom.mapPoint (X.pullbackAlongπ c) tW x'')
        (EllHom.mapPoint_torsion (X.pullbackAlongπ c) x'' hx'') ≫
      (descTorsionIso D X c α Hhom Hinv).hom ≫ pullback.fst (vRhoπ D) X.structMap =
    (X.pullbackAlong c).curve.pointToTorsion x'' hx'' ≫
      α.torsionIso.hom ≫ pullback.fst (vRhoπ D) (X.pullbackAlong c).structMap := by
  rw [← pointToTorsion_mapPoint (X.pullbackAlongπ c) x'' hx'']
  rw [show (descTorsionIso D X c α Hhom Hinv).hom =
    descTorsionHom D X c α Hhom from rfl]
  rw [Category.assoc, ← Category.assoc
    (torsionMapOfEllHom (X.pullbackAlongπ c) N),
    descTorsionHom_fac]
  rw [Category.assoc, vRhoCoverPrj_fst]

/-- **[T-EQ-3b-vi]** The coordinate-pair read of the descended trivialization at
transported points is the original coordinate-pair read. -/
theorem coordPairLift_descTorsionIso (Hhom) (Hinv) {W' : Scheme.{0}}
    (tW : W' ⟶ T'') (x'' y'' : (X.pullbackAlong c).curve.Point tW)
    (hx'' : x''.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      tW ≫ (X.pullbackAlong c).curve.zero)
    (hy'' : y''.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      tW ≫ (X.pullbackAlong c).curve.zero) :
    coordPairLift D X.structMap (descTorsionIso D X c α Hhom Hinv)
      (descTorsionHom_over D X c α Hhom) (tW ≫ c)
      (EllHom.mapPoint (X.pullbackAlongπ c) tW x'')
      (EllHom.mapPoint (X.pullbackAlongπ c) tW y'')
      (EllHom.mapPoint_torsion (X.pullbackAlongπ c) x'' hx'')
      (EllHom.mapPoint_torsion (X.pullbackAlongπ c) y'' hy'') =
    coordPairLift D (X.pullbackAlong c).structMap α.torsionIso α.over_T tW
      x'' y'' hx'' hy'' := by
  apply pullback.hom_ext
  · show pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D) =
      pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_fst, pullback.lift_fst]
    exact descTorsionIso_fst_leg Hhom Hinv tW x'' hx''
  · show pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D) =
      pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_snd, pullback.lift_snd]
    exact descTorsionIso_fst_leg Hhom Hinv tW y'' hy''

/-- **[T-EQ-3b-vi]** Scheme-level pairing identity of the descended trivialization
(cancel along the base-changed cover, transport through the point equivalence, and
use the original scheme-level identity). -/
theorem descTorsion_pairing_scheme [Fact (1 < N)] (Hhom) (Hinv)
    {W : Scheme.{0}} (t : W ⟶ X.base) (x y : X.curve.Point t)
    (hx : x.1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero)
    (hy : y.1 ≫ X.curve.mulByHom N = t ≫ X.curve.zero) :
    torsionPairEval D X.structMap t x y hx hy =
      coordPairLift D X.structMap (descTorsionIso D X c α Hhom Hinv)
        (descTorsionHom_over D X c α Hhom) t x y hx hy ≫ vRhoPairingMap D := by
  haveI : Flat (pullback.snd c t) :=
    MorphismProperty.pullback_snd _ _ ‹Flat c›
  haveI : Surjective (pullback.snd c t) :=
    MorphismProperty.pullback_snd _ _ ‹Surjective c›
  haveI : QuasiCompact (pullback.snd c t) :=
    MorphismProperty.pullback_snd _ _ ‹QuasiCompact c›
  refine (cancel_epi (pullback.snd c t)).mp ?_
  let px : X.curve.Point (pullback.fst c t ≫ c) :=
    ⟨pullback.snd c t ≫ x.1, by
      rw [Category.assoc, x.2, ← pullback.condition]⟩
  let py : X.curve.Point (pullback.fst c t ≫ c) :=
    ⟨pullback.snd c t ≫ y.1, by
      rw [Category.assoc, y.2, ← pullback.condition]⟩
  have hpx : px.1 ≫ X.curve.mulByHom N =
      (pullback.fst c t ≫ c) ≫ X.curve.zero := by
    show (pullback.snd c t ≫ x.1) ≫ _ = _
    rw [Category.assoc, hx, ← Category.assoc, ← pullback.condition,
      Category.assoc]
  have hpy : py.1 ≫ X.curve.mulByHom N =
      (pullback.fst c t ≫ c) ≫ X.curve.zero := by
    show (pullback.snd c t ≫ y.1) ≫ _ = _
    rw [Category.assoc, hy, ← Category.assoc, ← pullback.condition,
      Category.assoc]
  obtain ⟨x', hmx⟩ : ∃ x'', EllHom.mapPoint (X.pullbackAlongπ c)
      (pullback.fst c t) x'' = px :=
    ⟨(mapPointEquiv (X.pullbackAlongπ c) (pullback.fst c t)).symm px,
      (mapPointEquiv (X.pullbackAlongπ c) (pullback.fst c t)).apply_symm_apply px⟩
  obtain ⟨y', hmy⟩ : ∃ y'', EllHom.mapPoint (X.pullbackAlongπ c)
      (pullback.fst c t) y'' = py :=
    ⟨(mapPointEquiv (X.pullbackAlongπ c) (pullback.fst c t)).symm py,
      (mapPointEquiv (X.pullbackAlongπ c) (pullback.fst c t)).apply_symm_apply py⟩
  have hkx : (EllHom.mapPoint (X.pullbackAlongπ c) (pullback.fst c t) x').1 ≫
      X.curve.mulByHom N =
      (pullback.fst c t ≫ (X.pullbackAlongπ c).baseHom) ≫ X.curve.zero := by
    rw [hmx]; exact hpx
  have hky : (EllHom.mapPoint (X.pullbackAlongπ c) (pullback.fst c t) y').1 ≫
      X.curve.mulByHom N =
      (pullback.fst c t ≫ (X.pullbackAlongπ c).baseHom) ≫ X.curve.zero := by
    rw [hmy]; exact hpy
  have hx' : x'.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      pullback.fst c t ≫ (X.pullbackAlong c).curve.zero :=
    point_kill_of_mapPoint_kill x' hkx
  have hy' : y'.1 ≫ (X.pullbackAlong c).curve.mulByHom N =
      pullback.fst c t ≫ (X.pullbackAlong c).curve.zero :=
    point_kill_of_mapPoint_kill y' hky
  refine Eq.trans (torsionPairEval_comp D X.structMap (pullback.snd c t)
    x y px py rfl rfl hx hy hpx hpy).symm ?_
  refine Eq.trans (torsionPairEval_congr D X.structMap hmx.symm hmy.symm
    hpx hpy) ?_
  refine Eq.trans (torsionPairEval_mapPoint D (X.pullbackAlongπ c)
    (pullback.fst c t) x' y' hx' hy').symm ?_
  refine Eq.trans (α.pairing_scheme (pullback.fst c t) x' y' hx' hy') ?_
  rw [← Category.assoc]
  refine congrArg (· ≫ vRhoPairingMap D) ?_
  refine Eq.trans (coordPairLift_descTorsionIso Hhom Hinv (pullback.fst c t)
    x' y' hx' hy').symm ?_
  refine Eq.trans (coordPairLift_congr D X.structMap
    (descTorsionIso D X c α Hhom Hinv) (descTorsionHom_over D X c α Hhom)
    hmx hmy (EllHom.mapPoint_torsion (X.pullbackAlongπ c) x' hx')
    (EllHom.mapPoint_torsion (X.pullbackAlongπ c) y' hy')) ?_
  exact coordPairLift_comp D X.structMap (descTorsionIso D X c α Hhom Hinv)
    (descTorsionHom_over D X c α Hhom) (pullback.snd c t)
    x y px py rfl rfl hx hy hpx hpy

/-- **[T-EQ-3b]** The descended ρ-level structure: a ρ-structure on the total space
of a finite étale (qc flat surjective) cover whose trivialization matches on the
double fibre product descends to the base. -/
noncomputable def RhoLevelStructure.descend [IsFinite c] [Etale c]
    (Hhom : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ (X.pullbackAlong c).curve.torsion N),
      g₁ ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N =
        g₂ ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N →
      g₁ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X c =
        g₂ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X c)
    (Hinv : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ pullback (vRhoπ D) (X.pullbackAlong c).structMap),
      g₁ ≫ vRhoCoverPrj D X c = g₂ ≫ vRhoCoverPrj D X c →
      g₁ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N =
        g₂ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X.pullbackAlongπ c) N) :
    RhoLevelStructure D X.structMap X.curve where
  torsionIso := descTorsionIso D X c α Hhom Hinv
  over_T := descTorsionHom_over D X c α Hhom
  coords_additive := descTorsion_coords_additive Hhom Hinv
  pairing_compat := descTorsion_pairing_compat Hhom Hinv
  pairing_scheme := by
    intro _ W t x y hx hy
    exact descTorsion_pairing_scheme Hhom Hinv t x y hx hy

@[simp]
theorem descend_torsionIso [IsFinite c] [Etale c] (Hhom) (Hinv) :
    (RhoLevelStructure.descend (α := α) Hhom Hinv).torsionIso =
      descTorsionIso D X c α Hhom Hinv := rfl

/-- **[T-EQ-3b]** Pulling the descended structure back along the cover recovers the
original structure on the total space. -/
theorem pull_descend [IsFinite c] [Etale c] (Hhom) (Hinv) :
    RhoLevelStructure.pull D (X.pullbackAlongπ c)
      (RhoLevelStructure.descend (α := α) Hhom Hinv) = α := by
  refine RhoLevelStructure.ext_torsionIso ?_
  refine Iso.ext ?_
  apply pullback.hom_ext
  · rw [show (RhoLevelStructure.pull D (X.pullbackAlongπ c)
        (RhoLevelStructure.descend (α := α) Hhom Hinv)).torsionIso =
      pullTorsionIso D (X.pullbackAlongπ c)
        (RhoLevelStructure.descend (α := α) Hhom Hinv) from rfl]
    rw [pullTorsionIso_fst, descend_torsionIso]
    rw [show (descTorsionIso D X c α Hhom Hinv).hom =
      descTorsionHom D X c α Hhom from rfl]
    rw [← Category.assoc, descTorsionHom_fac, Category.assoc, vRhoCoverPrj_fst]
  · rw [show (RhoLevelStructure.pull D (X.pullbackAlongπ c)
        (RhoLevelStructure.descend (α := α) Hhom Hinv)).torsionIso =
      pullTorsionIso D (X.pullbackAlongπ c)
        (RhoLevelStructure.descend (α := α) Hhom Hinv) from rfl]
    rw [pullTorsionIso_over, ← α.over_T]

end Fields

end

end ModularCurves
