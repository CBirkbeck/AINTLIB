/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.FrobeniusValuation
import «Adic spaces».FarguesFontaine.Curve

/-!
# The curve object: saturation infrastructure and the `φ`-fixed sections
(D-iv-1/2)

Toward the adic Fargues–Fontaine curve as a `𝒱`-object: the carrier bridge
between the `𝒴`-presheafed space and the `Spv`-level quotient of `Curve.lean`,
saturated preimages of curve opens and their Frobenius stability (carrier and
ambient level), and the `φ`-fixed subring of sections over a saturated
preimage — the equalizer of the Frobenius transport against the restriction
along the stability equality (closed, hence complete in the limit topology).
The curve's structure presheaf takes these as its values (D-iv-2 tail).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter CategoryTheory Opposite Pointwise

set_option linter.overlappingInstances false

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A]
  [NonarchimedeanRing A]

omit [HasLocLiftPowerBounded A] in
/-- **The value over an empty rational is trivial — general Huber form**
(Wedhorn: `𝒪(∅) = 0`): a nonzero value would carry a `Spa`-point whose
`comap` lies in the empty rational open. -/
theorem presheafValue_subsingleton_of_rationalOpen_empty_huber
    (E : RationalLocData A) (hempty : rationalOpen E.T E.s = ∅) :
    Subsingleton (presheafValue E) := by
  have : IsHuberRing (presheafValue E) := presheafValue_isHuberRing_huber E
  letI P_B : PairOfDefinition (presheafValue E) := presheafValue_concretePair E
  have : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete E
  have h0 : IsUnit (0 : presheafValue E) := by
    rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B]
    intro w hw
    exfalso
    have hmem := comap_canonicalMap_mem_rationalOpen E
      (canonicalMap_continuous E) hw
    rw [hempty] at hmem
    exact hmem
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)
/-- Every rational index of an open with empty trace has empty rational
open (the rational open sits inside the trace). -/
theorem rationalOpen_eq_empty_of_index {V : Opens ↥(Spa A A⁺)}
    (hV : (V : Set ↥(Spa A A⁺)) = ∅) (i : RationalIndex V) :
    rationalOpen i.D.T i.D.s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v hv => ?_
  have hvs : (⟨v, rationalOpen_subset_spa hv⟩ : ↥(Spa A A⁺)) ∈ spaOpen i.D :=
    hv
  have := i.subset hvs
  rw [hV] at this
  exact this

/-- **Sections over an empty-trace open are trivial.** -/
theorem limitSections_subsingleton_of_empty {V : Opens ↥(Spa A A⁺)}
    (hV : (V : Set ↥(Spa A A⁺)) = ∅) :
    Subsingleton ↥(limitSections V) := by
  refine ⟨fun x y => Subtype.ext (funext fun i => ?_)⟩
  have := presheafValue_subsingleton_of_rationalOpen_empty_huber i.D
    (rationalOpen_eq_empty_of_index hV i)
  exact Subsingleton.elim _ _

end ValuationSpectrum

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

/-- The carrier bridge: points of the `𝒴`-carrier are points of `↥(Y)`
(the `Spv`-level subtype used by the curve quotient). -/
def yTopToY (y : ↥(yTop p F ϖ)) : ↥(Y p F ϖ) :=
  ⟨y.1.1, y.2⟩

/-- The quotient projection from the `𝒴`-carrier. -/
def yTopToCurve (y : ↥(yTop p F ϖ)) : Curve p F ϖ :=
  toCurve p F ϖ (yTopToY p F ϖ y)

/-- The Frobenius on the `𝒴`-carrier is the `(-k)`-action downstairs. -/
theorem yTopToY_yFrobTop (k : ℤ) (y : ↥(yTop p F ϖ)) :
    yTopToY p F ϖ (yFrobTop p F ϖ k y)
      = (Multiplicative.ofAdd (-k)) • yTopToY p F ϖ y := by
  refine Subtype.ext ?_
  show (spaFrob p F k y.1).1
    = (Multiplicative.ofAdd (-k)) • (yTopToY p F ϖ y).1
  exact spaFrob_coe p F k y.1

/-- The Frobenius preserves curve fibers. -/
theorem yTopToCurve_yFrobTop (k : ℤ) (y : ↥(yTop p F ϖ)) :
    yTopToCurve p F ϖ (yFrobTop p F ϖ k y) = yTopToCurve p F ϖ y := by
  show toCurve p F ϖ (yTopToY p F ϖ (yFrobTop p F ϖ k y)) = _
  rw [yTopToY_yFrobTop p F ϖ k y]
  exact Quotient.sound (MulAction.orbitRel_apply.mpr
    (MulAction.mem_orbit (yTopToY p F ϖ y) _))

theorem continuous_yTopToY : Continuous (yTopToY p F ϖ) :=
  Continuous.subtype_mk
    ((continuous_subtype_val).comp continuous_subtype_val) _

theorem continuous_yTopToCurve : Continuous (yTopToCurve p F ϖ) :=
  (isOpenQuotientMap_toCurve p F ϖ).continuous.comp
    (continuous_yTopToY p F ϖ)

/-- **The saturated preimage of a curve open** in the `𝒴`-carrier. -/
def curvePreimage (V : Opens (Curve p F ϖ)) : Opens ↥(yTop p F ϖ) :=
  ⟨yTopToCurve p F ϖ ⁻¹' (V : Set (Curve p F ϖ)),
    V.2.preimage (continuous_yTopToCurve p F ϖ)⟩

/-- **Frobenius stability of saturated preimages** (the carrier level). -/
theorem map_yFrobTop_curvePreimage (k : ℤ) (V : Opens (Curve p F ϖ)) :
    (Opens.map (yFrobTop p F ϖ k)).obj (curvePreimage p F ϖ V)
      = curvePreimage p F ϖ V := by
  refine Opens.ext ?_
  ext y
  show yTopToCurve p F ϖ (yFrobTop p F ϖ k y) ∈ (V : Set (Curve p F ϖ))
    ↔ yTopToCurve p F ϖ y ∈ (V : Set (Curve p F ϖ))
  rw [yTopToCurve_yFrobTop p F ϖ k y]

/-- **Frobenius stability of saturated preimages** (the ambient level). -/
theorem frobOpens_yFunctor_curvePreimage (k : ℤ) (V : Opens (Curve p F ϖ)) :
    frobOpens p F k ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V))
      = (yFunctor p F ϖ).obj (curvePreimage p F ϖ V) := by
  rw [yFunctor_frobOpens p F ϖ k (curvePreimage p F ϖ V),
    map_yFrobTop_curvePreimage p F ϖ k V]

/-- **The `φ`-fixed subring of sections over a saturated preimage**
(the value of the curve's structure presheaf): the equalizer of the
Frobenius transport and the restriction along the stability equality. -/
noncomputable def frobFixed (V : Opens (Curve p F ϖ)) :
    Subring ↥(limitSections
      ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V))) :=
  RingHom.eqLocus
    (limitFrobHom p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)))
    (limitRestrict
      (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)))

theorem mem_frobFixed (V : Opens (Curve p F ϖ))
    (s : ↥(limitSections
      ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)))) :
    s ∈ frobFixed p F ϖ V
      ↔ limitFrobHom p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) s
        = limitRestrict
            (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)) s :=
  Iff.rfl

/-- The fixed subring is closed (equalizer of continuous maps into a
Hausdorff limit). -/
theorem isClosed_frobFixed (V : Opens (Curve p F ϖ)) :
    IsClosed ((frobFixed p F ϖ V : Set ↥(limitSections
      ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V))))) :=
  isClosed_eq (limitFrobHom_continuous p F 1 _)
    (limitRestrict_continuous _)

/-- Monotonicity of the saturated ambient preimage. -/
theorem yFunctor_curvePreimage_mono {V' V : Opens (Curve p F ϖ)}
    (h : V' ≤ V) :
    (yFunctor p F ϖ).obj (curvePreimage p F ϖ V')
      ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ V) :=
  leOfHom ((yFunctor p F ϖ).map (homOfLE (fun _ hy => h hy)))

/-- **Restriction preserves `φ`-invariance.** -/
theorem frobFixed_restrict {V' V : Opens (Curve p F ϖ)} (h : V' ≤ V)
    {s : ↥(limitSections
      ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)))}
    (hs : s ∈ frobFixed p F ϖ V) :
    limitRestrict (yFunctor_curvePreimage_mono p F ϖ h) s
      ∈ frobFixed p F ϖ V' := by
  rw [mem_frobFixed]
  rw [mem_frobFixed] at hs
  have h1 := limitFrobHom_limitRestrict p F 1
    (yFunctor_curvePreimage_mono p F ϖ h) s
  rw [h1, hs]
  have h2 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (frobOpens_mono p F 1 (yFunctor_curvePreimage_mono p F ϖ h))
    (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)))) s
  have h3 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 V'))
    (yFunctor_curvePreimage_mono p F ϖ h))) s
  exact h2.trans h3.symm

instance frobFixed.completeSpace (V : Opens (Curve p F ϖ)) :
    CompleteSpace ↥(frobFixed p F ϖ V) :=
  (isClosed_frobFixed p F ϖ V).completeSpace_coe

instance frobFixed.isUniformAddGroup (V : Opens (Curve p F ϖ)) :
    IsUniformAddGroup ↥(frobFixed p F ϖ V) :=
  IsUniformInducing.isUniformAddGroup (frobFixed p F ϖ V).subtype
    isUniformEmbedding_subtype_val.isUniformInducing

/-- The curve as a topological-category object. -/
def CurveTop : TopCat := TopCat.of (Curve p F ϖ)

/-- The restriction of invariant sections, as a ring homomorphism. -/
noncomputable def frobFixedRestrict {V' V : Opens (Curve p F ϖ)}
    (h : V' ≤ V) :
    ↥(frobFixed p F ϖ V) →+* ↥(frobFixed p F ϖ V') :=
  RingHom.codRestrict
    ((limitRestrict (yFunctor_curvePreimage_mono p F ϖ h)).comp
      (frobFixed p F ϖ V).subtype)
    (frobFixed p F ϖ V')
    (fun s => frobFixed_restrict p F ϖ h s.2)

theorem frobFixedRestrict_continuous {V' V : Opens (Curve p F ϖ)}
    (h : V' ≤ V) : Continuous (frobFixedRestrict p F ϖ h) := by
  refine continuous_induced_rng.mpr ?_
  have hfun : (Subtype.val ∘ ⇑(frobFixedRestrict p F ϖ h))
      = fun s : ↥(frobFixed p F ϖ V) =>
        limitRestrict (yFunctor_curvePreimage_mono p F ϖ h) s.1 := rfl
  rw [hfun]
  exact (limitRestrict_continuous _).comp continuous_subtype_val

/-- **The structure presheaf of the adic Fargues–Fontaine curve**
(D-iv-2): values the `φ`-fixed sections over saturated preimages. -/
noncomputable def xStructurePresheaf :
    TopCat.Presheaf CompleteTopCommRingCat.{u_1} (CurveTop p F ϖ) where
  obj V :=
    letI := frobFixed.isUniformAddGroup p F ϖ V.unop
    letI := frobFixed.completeSpace p F ϖ V.unop
    CompleteTopCommRingCat.of ↥(frobFixed p F ϖ V.unop)
  map {V W} i := ⟨frobFixedRestrict p F ϖ (leOfHom i.unop),
    frobFixedRestrict_continuous p F ϖ (leOfHom i.unop)⟩
  map_id V := by
    refine Subtype.ext (RingHom.ext fun s => Subtype.ext (Subtype.ext
      (funext fun i => ?_)))
    rfl
  map_comp {U V W} i j := by
    refine Subtype.ext (RingHom.ext fun s => Subtype.ext (Subtype.ext
      (funext fun i => ?_)))
    rfl

/-- **The adic curve as a presheafed space of complete topological rings.** -/
noncomputable def curveSpace : TopRingPresheafedSpace where
  carrier := CurveTop p F ϖ
  presheaf := xStructurePresheaf p F ϖ

/-- The projection as a `TopCat`-morphism. -/
def yTopToCurveTop : yTop p F ϖ ⟶ CurveTop p F ϖ :=
  TopCat.ofHom ⟨yTopToCurve p F ϖ, continuous_yTopToCurve p F ϖ⟩

/-- The saturated preimage is the `Opens.map`-preimage of the projection. -/
theorem curvePreimage_eq_opensMap (V : Opens (Curve p F ϖ)) :
    curvePreimage p F ϖ V = (Opens.map (yTopToCurveTop p F ϖ)).obj V :=
  rfl

/-- **The projection component**: invariant sections over the saturated
preimage are in particular sections of the `𝒴`-presheaf over it. -/
noncomputable def piComponent (V : Opens (Curve p F ϖ)) :
    ↥(frobFixed p F ϖ V)
      →+* ↥(limitSections ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V))) :=
  (frobFixed p F ϖ V).subtype

/-- **The curve projection as a morphism of presheafed spaces** (D-iv-3(i)):
base the quotient map, comparison the inclusion of invariants. -/
noncomputable def piYHom : yPresheafedSpace p F ϖ ⟶ curveSpace p F ϖ where
  base := yTopToCurveTop p F ϖ
  c := {
    app := fun V => ⟨piComponent p F ϖ V.unop, continuous_subtype_val⟩
    naturality := fun V W i => by
      refine Subtype.ext (RingHom.ext fun s => Subtype.ext
        (funext fun j => ?_))
      rfl }

omit [CharP F p] in
/-- `yTopToY` is a bijection. -/
theorem yTopToY_bijective : Function.Bijective (yTopToY p F ϖ) := by
  constructor
  · intro y₁ y₂ h
    have h1 : y₁.1.1 = y₂.1.1 :=
      congrArg (fun z : ↥(Y p F ϖ) => (z : Spv (Ainf p F))) h
    exact Subtype.ext (Subtype.ext h1)
  · intro z
    have hz : z.1 ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) := z.2.1
    exact ⟨⟨⟨z.1, hz⟩, z.2⟩, rfl⟩

/-- `yTopToY` is inducing (both sides carry the `Spv`-subspace topology). -/
theorem yTopToY_isInducing : Topology.IsInducing (yTopToY p F ϖ) := by
  constructor
  refine le_antisymm ?_ ?_
  · exact (continuous_yTopToY p F ϖ).le_induced
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := hU
    obtain ⟨S, hS, rfl⟩ := hV
    refine ⟨Subtype.val ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
    rfl

/-- `yTopToY` as a homeomorphism (the two subtype presentations of `𝒴`
agree topologically). -/
noncomputable def yTopToYHomeo : ↥(yTop p F ϖ) ≃ₜ ↥(Y p F ϖ) :=
  (Equiv.ofBijective _ (yTopToY_bijective p F ϖ)).toHomeomorphOfIsInducing
    (yTopToY_isInducing p F ϖ)

/-- The projection from the `𝒴`-carrier is an open quotient map. -/
theorem isOpenQuotientMap_yTopToCurve :
    IsOpenQuotientMap (yTopToCurve p F ϖ) := by
  have hcomp : yTopToCurve p F ϖ
      = (toCurve p F ϖ) ∘ (yTopToYHomeo p F ϖ) := rfl
  rw [hcomp]
  exact (isOpenQuotientMap_toCurve p F ϖ).comp
    (yTopToYHomeo p F ϖ).isOpenQuotientMap

/-- The open image of a `𝒴`-carrier open on the curve. -/
def xImage (W : Opens ↥(yTop p F ϖ)) : Opens (Curve p F ϖ) :=
  ⟨yTopToCurve p F ϖ '' (W : Set ↥(yTop p F ϖ)),
    (isOpenQuotientMap_yTopToCurve p F ϖ).isOpenMap _ W.2⟩

/-- **Saturation identity**: the preimage of the image is the union of the
Frobenius translates. -/
theorem curvePreimage_xImage (W : Opens ↥(yTop p F ϖ)) :
    curvePreimage p F ϖ (xImage p F ϖ W)
      = ⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W := by
  refine Opens.ext ?_
  ext y
  constructor
  · rintro ⟨w, hwW, hw⟩
    -- yTopToCurve w = yTopToCurve y: same orbit
    have hrel : yTopToY p F ϖ w ∈ MulAction.orbit (Multiplicative ℤ)
        (yTopToY p F ϖ y) :=
      MulAction.orbitRel_apply.mp (Quotient.eq''.mp hw)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
    -- w = the (toAdd g)-translate of y; then yFrobTop-translate membership
    rw [Opens.coe_iSup]
    refine Set.mem_iUnion.mpr ⟨-(Multiplicative.toAdd g), ?_⟩
    show yFrobTop p F ϖ (-(Multiplicative.toAdd g)) y ∈ W
    have hkey : yTopToY p F ϖ
        (yFrobTop p F ϖ (-(Multiplicative.toAdd g)) y)
        = yTopToY p F ϖ w := by
      rw [yTopToY_yFrobTop p F ϖ (-(Multiplicative.toAdd g)) y, neg_neg,
        ofAdd_toAdd]
      exact hg
    have := (yTopToY_bijective p F ϖ).1 hkey
    rwa [this]
  · intro hy
    rw [Opens.coe_iSup] at hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    refine ⟨yFrobTop p F ϖ k y, hk, ?_⟩
    exact yTopToCurve_yFrobTop p F ϖ k y

/-- **Wandering at the `𝒴`-carrier**: every point has an open neighbourhood
whose nontrivial Frobenius translates are disjoint from it. -/
theorem exists_disjoint_translates (y : ↥(yTop p F ϖ)) :
    ∃ W : Opens ↥(yTop p F ϖ), y ∈ W ∧
      ∀ k : ℤ, k ≠ 0 →
        Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
            : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
          ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) := by
  obtain ⟨W₀, hyW₀, hWY, hWopen, hdis⟩ :=
    exists_nhd_smul_disjoint y.2
  refine ⟨⟨Subtype.val ⁻¹' (Subtype.val ⁻¹' W₀),
    hWopen.preimage continuous_subtype_val⟩, hyW₀, ?_⟩
  intro k hk
  refine Set.disjoint_left.mpr ?_
  rintro z hz1 hz2
  -- hz1 : (yFrobTop k z).1.1 ∈ W₀; hz2 : z.1.1 ∈ W₀
  have h1 : (Multiplicative.ofAdd (-k)) • (z.1.1 : Spv (Ainf p F)) ∈ W₀ := by
    have := spaFrob_coe p F k z.1
    show _ ∈ W₀
    rw [← this]
    exact hz1
  have h2 : (Multiplicative.ofAdd k) •
      ((Multiplicative.ofAdd (-k)) • (z.1.1 : Spv (Ainf p F)))
      ∈ (Multiplicative.ofAdd k) • W₀ :=
    Set.smul_mem_smul_set h1
  rw [show (Multiplicative.ofAdd k) •
      ((Multiplicative.ofAdd (-k)) • (z.1.1 : Spv (Ainf p F)))
      = (z.1.1 : Spv (Ainf p F)) by
    rw [smul_smul]
    rw [show (Multiplicative.ofAdd k * Multiplicative.ofAdd (-k))
        = (1 : Multiplicative ℤ) by
      rw [← ofAdd_add]
      simp]
    rw [one_smul]] at h2
  exact Set.disjoint_left.mp (hdis k hk) h2 hz2

theorem frobPow_zero : frobPow p F 0 = RingEquiv.refl (Ainf p F) := by
  show ((frob p F ^ (0 : ℤ) : RingAut (Ainf p F)) : Ainf p F ≃+* Ainf p F) = _
  rw [zpow_zero]
  rfl

theorem spaFrob_zero (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    spaFrob p F 0 v = v := by
  refine Subtype.ext ?_
  show comap (frobPow p F 0).toRingHom v.1 = v.1
  rw [frobPow_zero]
  exact congr_fun (comap_id) v.1

theorem frobOpens_zero (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    frobOpens p F 0 W = W := by
  refine Opens.ext ?_
  ext v
  show spaFrob p F 0 v ∈ (W : Set _) ↔ v ∈ (W : Set _)
  rw [spaFrob_zero]

theorem frobPow_neg_zero_eq_refl :
    frobPow p F (-0) = RingEquiv.refl (Ainf p F) := by
  rw [neg_zero, frobPow_zero]

/-- **The zero-power transport is the restriction along the preimage
collapse.** -/
theorem limitFrobHom_zero
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (s : ↥(limitSections W)) :
    limitFrobHom p F 0 W s
      = limitRestrict (le_of_eq (frobOpens_zero p F W)) s := by
  refine Subtype.ext (funext fun E => ?_)
  have hDeq : E.D.mapHuber (frobPow p F (-0)) (continuous_frobPow p F (-0))
      (continuous_frobPow_symm p F (-0)) = E.D :=
    RationalLocData.mapHuber_eq_of_eq_refl _ _
      (frobPow_neg_zero_eq_refl p F) E.D
  have hle' : rationalOpen E.D.T E.D.s
      ⊆ rationalOpen (E.D.mapHuber (frobPow p F (-0))
          (continuous_frobPow p F (-0))
          (continuous_frobPow_symm p F (-0))).T
        (E.D.mapHuber (frobPow p F (-0)) (continuous_frobPow p F (-0))
          (continuous_frobPow_symm p F (-0))).s := by
    rw [hDeq]
  have hle : rationalOpen (E.D.mapHuber (frobPow p F (-0))
        (continuous_frobPow p F (-0))
        (continuous_frobPow_symm p F (-0))).T
      (E.D.mapHuber (frobPow p F (-0)) (continuous_frobPow p F (-0))
        (continuous_frobPow_symm p F (-0))).s
      ⊆ rationalOpen E.D.T E.D.s := by
    rw [hDeq]
  have hsymm := ValuationSpectrum.presheafValueRingEquivHuber_symm_apply_of_eq_refl
    (continuous_frobPow p F (-0)) (continuous_frobPow_symm p F (-0))
    (frobPow_neg_zero_eq_refl p F) E.D hle' hle
    ((s : ∀ j : RationalIndex W, presheafValue j.D) (frobIndex p F 0 E))
  have hset : ((frobOpens p F 0 W
        : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      = ((W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
    rw [frobOpens_zero p F W]
  have hcompat := s.2 (frobIndex p F 0 E)
    ⟨E.D, E.isRational, E.subset.trans hset.le⟩
    hle'
  exact ((limitFrobHom_component p F 0 W s E).trans hsymm).trans hcompat
/-- The zero-power Frobenius on the `𝒴`-carrier is the identity. -/
theorem yFrobTop_zero (y : ↥(yTop p F ϖ)) :
    yFrobTop p F ϖ 0 y = y := by
  refine Subtype.ext ?_
  show spaFrob p F 0 y.1 = y.1
  exact spaFrob_zero p F y.1

theorem map_yFrobTop_zero (W : Opens ↥(yTop p F ϖ)) :
    (Opens.map (yFrobTop p F ϖ 0)).obj W = W := by
  refine Opens.ext ?_
  ext y
  show yFrobTop p F ϖ 0 y ∈ (W : Set _) ↔ y ∈ (W : Set _)
  rw [yFrobTop_zero p F ϖ y]

theorem frobPow_toRingHom_comp (k l : ℤ) :
    (frobPow p F (k + l)).toRingHom
      = (frobPow p F k).toRingHom.comp (frobPow p F l).toRingHom := by
  refine RingHom.ext fun x => ?_
  show ((frob p F ^ (k + l) : RingAut (Ainf p F)) : Ainf p F ≃+* Ainf p F) x
    = ((frob p F ^ k : RingAut (Ainf p F)) : Ainf p F ≃+* Ainf p F)
        (((frob p F ^ l : RingAut (Ainf p F)) : Ainf p F ≃+* Ainf p F) x)
  rw [zpow_add]
  rfl

/-- Additivity of the `Spa`-Frobenius. -/
theorem spaFrob_add (k l : ℤ)
    (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    spaFrob p F (k + l) v = spaFrob p F l (spaFrob p F k v) := by
  refine Subtype.ext ?_
  show comap (frobPow p F (k + l)).toRingHom v.1
    = comap (frobPow p F l).toRingHom (comap (frobPow p F k).toRingHom v.1)
  rw [frobPow_toRingHom_comp p F k l]
  exact congr_fun (ValuationSpectrum.comap_comp
    (frobPow p F l).toRingHom (frobPow p F k).toRingHom) v.1

/-- Additivity of the `𝒴`-carrier Frobenius. -/
theorem yFrobTop_add (k l : ℤ) (y : ↥(yTop p F ϖ)) :
    yFrobTop p F ϖ (k + l) y
      = yFrobTop p F ϖ l (yFrobTop p F ϖ k y) := by
  refine Subtype.ext ?_
  show spaFrob p F (k + l) y.1 = spaFrob p F l (spaFrob p F k y.1)
  exact spaFrob_add p F k l y.1

/-- **Pairwise disjointness of distinct Frobenius translates.** -/
theorem translates_pairwise_disjoint
    {W : Opens ↥(yTop p F ϖ)}
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    {i j : ℤ} (hij : i ≠ j) :
    Disjoint (((Opens.map (yFrobTop p F ϖ i)).obj W
        : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
      (((Opens.map (yFrobTop p F ϖ j)).obj W
        : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) := by
  refine Set.disjoint_left.mpr ?_
  rintro y hyi hyj
  -- yFrobTop i y ∈ W and yFrobTop j y ∈ W
  have hcomp : yFrobTop p F ϖ (j - i) (yFrobTop p F ϖ i y)
      = yFrobTop p F ϖ j y := by
    rw [← yFrobTop_add p F ϖ i (j - i) y]
    norm_num
  have h1 : yFrobTop p F ϖ i y
      ∈ (((Opens.map (yFrobTop p F ϖ (j - i))).obj W
        : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) := by
    show yFrobTop p F ϖ (j - i) (yFrobTop p F ϖ i y) ∈ (W : Set _)
    rw [hcomp]
    exact hyj
  exact Set.disjoint_left.mp (hdis (j - i) (by omega)) h1 hyi

/-- Each translate lies in the saturated preimage. -/
theorem translate_le_curvePreimage_xImage (W : Opens ↥(yTop p F ϖ)) (k : ℤ) :
    (Opens.map (yFrobTop p F ϖ k)).obj W
      ≤ curvePreimage p F ϖ (xImage p F ϖ W) := by
  rw [curvePreimage_xImage p F ϖ W]
  exact le_iSup (fun k : ℤ => (Opens.map (yFrobTop p F ϖ k)).obj W) k

/-- The translated-piece family of a section. -/
noncomputable def translateFam (W : Opens ↥(yTop p F ϖ))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) (k : ℤ) :
    ↥(limitSections ((yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ k)).obj W))) :=
  limitRestrict (le_of_eq (yFunctor_frobOpens p F ϖ k W).symm)
    (limitFrobHom p F k ((yFunctor p F ϖ).obj W) s)

/-- The `yFunctor`-image inclusion of a translate into the saturation. -/
theorem yFunctor_translate_le (W : Opens ↥(yTop p F ϖ)) (k : ℤ) :
    (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ k)).obj W)
      ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)) :=
  leOfHom ((yFunctor p F ϖ).map
    (homOfLE (translate_le_curvePreimage_xImage p F ϖ W k)))

/-- Translates of a section along distinct Frobenius shifts agree on their overlaps —
vacuously: by `hdis` the overlaps are empty, so their `limitSections` are subsingletons, and
the diagonal case is `rfl`.

Extracted from `exists_translateFam_glue`, where it was the dominant `have`. -/
private theorem translateFam_pairwise_compat (W : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ∀ i j : ℤ,
      limitRestrict (inf_le_left
        (a := (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ i)).obj W))
        (b := (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ j)).obj W)))
        (translateFam p F ϖ W s i)
      = limitRestrict (inf_le_right
          (a := (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ i)).obj W))
          (b := (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ j)).obj W)))
          (translateFam p F ϖ W s j) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rfl
  · have hsub : Subsingleton ↥(limitSections
        ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ i)).obj W)
          ⊓ (yFunctor p F ϖ).obj
            ((Opens.map (yFrobTop p F ϖ j)).obj W))) := by
      refine ValuationSpectrum.limitSections_subsingleton_of_empty
        (Set.eq_empty_of_forall_notMem fun v hv => ?_)
      obtain ⟨hvi, hvj⟩ := hv
      obtain ⟨y₁, hy₁, hy₁v⟩ := hvi
      obtain ⟨y₂, hy₂, hy₂v⟩ := hvj
      have hyy : y₁ = y₂ :=
        Subtype.val_injective (hy₁v.trans hy₂v.symm)
      subst hyy
      exact Set.disjoint_left.mp
        (translates_pairwise_disjoint p F ϖ hdis hij) hy₁ hy₂
    exact hsub.elim _ _

/-- **The glued invariant-candidate section over the saturation**
(D-iv-3(ii-c β)): the translate family glues — compatibility is trivial on
the diagonal and vacuous elsewhere (disjoint translates). -/
theorem exists_translateFam_glue (W : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ∃ g : ↥(limitSections ((yFunctor p F ϖ).obj
        (curvePreimage p F ϖ (xImage p F ϖ W)))),
      ∀ k : ℤ, limitRestrict (yFunctor_translate_le p F ϖ W k) g
        = translateFam p F ϖ W s k := by
  have hVS : (((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W))
      : Opens ↥(SpaTop (Ainf p F))) : Set ↥(SpaTop (Ainf p F)))
      ⊆ Subtype.val ⁻¹' Y p F ϖ :=
    yFunctor_trace p F ϖ _
  have hcov : (((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W))
      : Opens ↥(SpaTop (Ainf p F))) : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ k : ℤ, (((yFunctor p F ϖ).obj
          ((Opens.map (yFrobTop p F ϖ k)).obj W)
        : Opens ↥(SpaTop (Ainf p F))) : Set ↥(SpaTop (Ainf p F))) := by
    rintro v ⟨y, hy, rfl⟩
    have hy' := hy
    rw [show curvePreimage p F ϖ (xImage p F ϖ W)
        = ⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W from
      curvePreimage_xImage p F ϖ W] at hy'
    rw [Opens.coe_iSup] at hy'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy'
    exact Set.mem_iUnion.mpr ⟨k, ⟨y, hk, rfl⟩⟩
  have hcompat := translateFam_pairwise_compat p F ϖ W hdis s
  have hcov' : (((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W))
      : Opens ↥(SpaTop (Ainf p F))) : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ k : ULift ℤ, (((yFunctor p F ϖ).obj
          ((Opens.map (yFrobTop p F ϖ k.down)).obj W)
        : Opens ↥(SpaTop (Ainf p F))) : Set ↥(SpaTop (Ainf p F))) := by
    intro v hv
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov hv)
    exact Set.mem_iUnion.mpr ⟨⟨k⟩, hk⟩
  obtain ⟨g, hg⟩ := (isLimitSheafOn_Y p F ϖ).glue
    (V := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))
    hVS (ι := ULift ℤ)
    (U := fun k : ULift ℤ => (yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ k.down)).obj W))
    (fun k => yFunctor_translate_le p F ϖ W k.down) hcov'
    (fun k => translateFam p F ϖ W s k.down)
    (fun i j => hcompat i.down j.down)
  exact ⟨g, fun k => hg ⟨k⟩⟩

/-- The zero-translate inclusion into `W`. -/
theorem yFunctor_translate_zero_le (W : Opens ↥(yTop p F ϖ)) :
    (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ 0)).obj W)
      ≤ (yFunctor p F ϖ).obj W :=
  leOfHom ((yFunctor p F ϖ).map (homOfLE
    (le_of_eq (map_yFrobTop_zero p F ϖ W))))

/-- **The zero-piece of the translate family is the plain restriction.** -/
theorem translateFam_zero (W : Opens ↥(yTop p F ϖ))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    translateFam p F ϖ W s 0
      = limitRestrict (yFunctor_translate_zero_le p F ϖ W) s := by
  show limitRestrict (le_of_eq (yFunctor_frobOpens p F ϖ 0 W).symm)
      (limitFrobHom p F 0 ((yFunctor p F ϖ).obj W) s)
    = limitRestrict (yFunctor_translate_zero_le p F ϖ W) s
  rw [limitFrobHom_zero p F ((yFunctor p F ϖ).obj W) s]
  exact congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (yFunctor_frobOpens p F ϖ 0 W).symm)
    (le_of_eq (frobOpens_zero p F ((yFunctor p F ϖ).obj W))))) s

/-- **The invariant-extension existence, extension form** (D-iv-3(ii-c β),
first half): the glued candidate restricts on the zero translate to `s`. -/
theorem exists_glue_extending (W : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ∃ g : ↥(limitSections ((yFunctor p F ϖ).obj
        (curvePreimage p F ϖ (xImage p F ϖ W)))),
      (∀ k : ℤ, limitRestrict (yFunctor_translate_le p F ϖ W k) g
        = translateFam p F ϖ W s k)
      ∧ limitRestrict (yFunctor_translate_le p F ϖ W 0) g
        = limitRestrict (yFunctor_translate_zero_le p F ϖ W) s := by
  obtain ⟨g, hg⟩ := exists_translateFam_glue p F ϖ W hdis s
  exact ⟨g, hg, (hg 0).trans (translateFam_zero p F ϖ W s)⟩

/-- Additivity of the Frobenius preimage of opens. -/
theorem frobOpens_add (k l : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    frobOpens p F (k + l) W = frobOpens p F k (frobOpens p F l W) := by
  refine Opens.ext ?_
  ext v
  show spaFrob p F (k + l) v ∈ (W : Set _)
    ↔ spaFrob p F l (spaFrob p F k v) ∈ (W : Set _)
  rw [spaFrob_add p F k l v]

/-- Frobenius powers compose. -/
theorem frobPow_trans (a b : ℤ) :
    (frobPow p F a).trans (frobPow p F b) = frobPow p F (a + b) := by
  refine RingEquiv.ext fun x => ?_
  show (frobPow p F b) ((frobPow p F a) x) = (frobPow p F (a + b)) x
  have h := congr_fun (congrArg DFunLike.coe
    (frobPow_toRingHom_comp p F b a)) x
  rw [show b + a = a + b from add_comm b a] at h
  exact h.symm

/-- The negated-sum collapse of Frobenius powers. -/
theorem frobPow_trans_neg (k l : ℤ) :
    (frobPow p F (-k)).trans (frobPow p F (-l)) = frobPow p F (-(k + l)) := by
  rw [frobPow_trans p F (-k) (-l)]
  congr 1
  omega

/-- The composed datum of the double transport equals the sum transport. -/
theorem mapHuber_frobPow_add (k l : ℤ) (D : RationalLocData (Ainf p F)) :
    (D.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
        (continuous_frobPow p F (-l)) (continuous_frobPow_symm p F (-l))
      = D.mapHuber (frobPow p F (-(k + l)))
          (continuous_frobPow p F (-(k + l)))
          (continuous_frobPow_symm p F (-(k + l))) := by
  rw [RationalLocData.mapHuber_comp (frobPow p F (-k))
    (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
    (frobPow p F (-l)) (continuous_frobPow p F (-l))
    (continuous_frobPow_symm p F (-l)) D]
  exact RationalLocData.mapHuber_congr_e _ _ _ _
    (frobPow_trans_neg p F k l) D

private theorem hle3_lem
    (k l : ℤ)
    (hct : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))))
    (hct' : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))).symm)
    (ED : RationalLocData (Ainf p F))
    (hDeq : ED.mapHuber (frobPow p F (-(k + l)))
      (continuous_frobPow p F (-(k + l)))
      (continuous_frobPow_symm p F (-(k + l)))
    = (ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
        (continuous_frobPow p F (-l)) (continuous_frobPow_symm p F (-l))) :
    rationalOpen
    (ED.mapHuber (frobPow p F (-(k + l)))
      (continuous_frobPow p F (-(k + l)))
      (continuous_frobPow_symm p F (-(k + l)))).T
    (ED.mapHuber (frobPow p F (-(k + l)))
      (continuous_frobPow p F (-(k + l)))
      (continuous_frobPow_symm p F (-(k + l)))).s
    ⊆ rationalOpen
      ((ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
        (continuous_frobPow p F (-l))
        (continuous_frobPow_symm p F (-l))).T
      ((ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
        (continuous_frobPow p F (-l))
        (continuous_frobPow_symm p F (-l))).s := by
  rw [hDeq]

private theorem hle2_lem
    (k l : ℤ)
    (hct : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))))
    (hct' : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))).symm)
    (ED : RationalLocData (Ainf p F)) :
    rationalOpen
    (ED.mapHuber (frobPow p F (-(k + l)))
      (continuous_frobPow p F (-(k + l)))
      (continuous_frobPow_symm p F (-(k + l)))).T
    (ED.mapHuber (frobPow p F (-(k + l)))
      (continuous_frobPow p F (-(k + l)))
      (continuous_frobPow_symm p F (-(k + l)))).s
    ⊆ rationalOpen
      (ED.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l)))
        hct hct').T
      (ED.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l)))
        hct hct').s := by
  rw [ValuationSpectrum.RationalLocData.mapHuber_congr_e
    (continuous_frobPow p F (-(k + l)))
    (continuous_frobPow_symm p F (-(k + l)))
    hct hct'
    (frobPow_trans_neg p F k l).symm ED]

private theorem hle'_lem
    (k l : ℤ)
    (hct : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))))
    (hct' : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))).symm)
    (ED : RationalLocData (Ainf p F)) :
    rationalOpen
    (ED.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l)))
      hct hct').T
    (ED.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l)))
      hct hct').s
    ⊆ rationalOpen
      ((ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
        (continuous_frobPow p F (-l))
        (continuous_frobPow_symm p F (-l))).T
      ((ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
        (continuous_frobPow p F (-l))
        (continuous_frobPow_symm p F (-l))).s := by
  rw [RationalLocData.mapHuber_comp]

private theorem hle_lem
    (k l : ℤ)
    (hct : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))))
    (hct' : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))).symm)
    (ED : RationalLocData (Ainf p F)) :
    rationalOpen
    ((ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
      (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
      (continuous_frobPow p F (-l))
      (continuous_frobPow_symm p F (-l))).T
    ((ED.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
      (continuous_frobPow_symm p F (-k))).mapHuber (frobPow p F (-l))
      (continuous_frobPow p F (-l))
      (continuous_frobPow_symm p F (-l))).s
    ⊆ rationalOpen
      (ED.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l)))
        hct hct').T
      (ED.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l)))
        hct hct').s := by
  rw [RationalLocData.mapHuber_comp]

/-- **Additivity of the limit transport** (componentwise through the value
composite law). -/
theorem limitFrobHom_add (k l : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (s : ↥(limitSections W)) :
    limitFrobHom p F (k + l) W s
      = limitRestrict (le_of_eq (frobOpens_add p F k l W))
          (limitFrobHom p F k (frobOpens p F l W)
            (limitFrobHom p F l W s)) := by
  -- Name the six continuity proofs once; spelled out, they are most of this proof.
  have hck := continuous_frobPow p F (-k)
  have hck' := continuous_frobPow_symm p F (-k)
  have hcl := continuous_frobPow p F (-l)
  have hcl' := continuous_frobPow_symm p F (-l)
  have hckl := continuous_frobPow p F (-(k + l))
  have hckl' := continuous_frobPow_symm p F (-(k + l))
  have hct : Continuous ⇑((frobPow p F (-k)).trans (frobPow p F (-l))) :=
    (continuous_frobPow p F (-l)).comp (continuous_frobPow p F (-k))
  have hct' : Continuous
      ⇑((frobPow p F (-k)).trans (frobPow p F (-l))).symm :=
    (continuous_frobPow_symm p F (-k)).comp
      (continuous_frobPow_symm p F (-l))
  refine Subtype.ext (funext fun E => ?_)
  set Elift : RationalIndex (frobOpens p F k (frobOpens p F l W)) :=
    ⟨E.D, E.isRational, E.subset.trans (by
      rw [← frobOpens_add p F k l W])⟩ with hElift
  -- The single section value every step below transports.
  set sv := (s : ∀ j : RationalIndex W, presheafValue j.D)
    (frobIndex p F l (frobIndex p F k Elift))
  have hDeq := mapHuber_frobPow_add p F k l E.D
  have hle := hle_lem p F k l hct hct' E.D
  have hle' := hle'_lem p F k l hct hct' E.D
  have hle2 := hle2_lem p F k l hct hct' E.D
  have hle3 := hle3_lem p F k l hct hct' E.D hDeq.symm
  have h1 := ValuationSpectrum.presheafValueRingEquivHuber_comp_symm_apply
    (frobPow p F (-k)) hck hck' (frobPow p F (-l)) hcl hcl' E.D hle hle' sv
  have h2 := ValuationSpectrum.presheafValueRingEquivHuber_congr_e_symm
    hct hct' hckl hckl' (frobPow_trans_neg p F k l) E.D hle2
    (restrictionMap _ _ hle' sv)
  have h3 := restrictionMap_restrictionMap
    ((E.D.mapHuber (frobPow p F (-k)) hck hck').mapHuber (frobPow p F (-l)) hcl hcl')
    (E.D.mapHuber ((frobPow p F (-k)).trans (frobPow p F (-l))) hct hct')
    (E.D.mapHuber (frobPow p F (-(k + l))) hckl hckl') hle' hle2 sv
  have h4 := s.2 (frobIndex p F l (frobIndex p F k Elift))
    (frobIndex p F (k + l) E) hle3
  show (presheafValueRingEquivHuber (frobPow p F (-(k + l))) hckl hckl' E.D).symm
      ((s : ∀ j : RationalIndex W, presheafValue j.D) (frobIndex p F (k + l) E))
    = (presheafValueRingEquivHuber (frobPow p F (-k)) hck hck' E.D).symm
        ((presheafValueRingEquivHuber (frobPow p F (-l)) hcl hcl'
          (E.D.mapHuber (frobPow p F (-k)) hck hck')).symm sv)
  rw [h1, h2]
  refine congrArg _ ?_
  exact (h3.trans h4).symm

/-- The carrier-level translate shift (subtraction-free form). -/
theorem map_yFrobTop_shift (m : ℤ) (W : Opens ↥(yTop p F ϖ)) :
    (Opens.map (yFrobTop p F ϖ 1)).obj
        ((Opens.map (yFrobTop p F ϖ m)).obj W)
      = (Opens.map (yFrobTop p F ϖ (1 + m))).obj W := by
  refine Opens.ext ?_
  ext y
  show yFrobTop p F ϖ m (yFrobTop p F ϖ 1 y) ∈ (W : Set _)
    ↔ yFrobTop p F ϖ (1 + m) y ∈ (W : Set _)
  rw [← yFrobTop_add p F ϖ 1 m y]

/-- **The piece shift** (subtraction-free): the Frobenius preimage of the
`m`-th translate piece is the `(1+m)`-th. -/
theorem piece_shift (m : ℤ) (W : Opens ↥(yTop p F ϖ)) :
    frobOpens p F 1 ((yFunctor p F ϖ).obj
        ((Opens.map (yFrobTop p F ϖ m)).obj W))
      = (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W) := by
  rw [yFunctor_frobOpens p F ϖ 1 ((Opens.map (yFrobTop p F ϖ m)).obj W)]
  rw [map_yFrobTop_shift p F ϖ m W]

/-- Inversion of the additivity identity: the double transport is the
restriction of the sum transport. -/
theorem limitFrobHom_double (k l : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (s : ↥(limitSections W)) :
    limitFrobHom p F k (frobOpens p F l W) (limitFrobHom p F l W s)
      = limitRestrict (le_of_eq (frobOpens_add p F k l W).symm)
          (limitFrobHom p F (k + l) W s) := by
  rw [limitFrobHom_add p F k l W s]
  have hcomp := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (frobOpens_add p F k l W).symm)
    (le_of_eq (frobOpens_add p F k l W))))
    (limitFrobHom p F k (frobOpens p F l W) (limitFrobHom p F l W s))
  have hid := congr_fun (congrArg DFunLike.coe (limitRestrict_id
    (frobOpens p F k (frobOpens p F l W))))
    (limitFrobHom p F k (frobOpens p F l W) (limitFrobHom p F l W s))
  exact (hcomp.trans hid).symm

/-- **The translate-family recurrence** (subtraction-free): the generator
transport carries the `m`-th piece to the `(1+m)`-th. -/
theorem translateFam_succ (m : ℤ) (W : Opens ↥(yTop p F ϖ))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    limitRestrict (le_of_eq (piece_shift p F ϖ m W))
        (translateFam p F ϖ W s (1 + m))
      = limitFrobHom p F 1
          ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ m)).obj W))
          (translateFam p F ϖ W s m) := by
  show limitRestrict (le_of_eq (piece_shift p F ϖ m W))
      (limitRestrict (le_of_eq (yFunctor_frobOpens p F ϖ (1 + m) W).symm)
        (limitFrobHom p F (1 + m) ((yFunctor p F ϖ).obj W) s))
    = limitFrobHom p F 1
        ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ m)).obj W))
        (limitRestrict (le_of_eq (yFunctor_frobOpens p F ϖ m W).symm)
          (limitFrobHom p F m ((yFunctor p F ϖ).obj W) s))
  rw [limitFrobHom_limitRestrict p F 1
    (le_of_eq (yFunctor_frobOpens p F ϖ m W).symm)
    (limitFrobHom p F m ((yFunctor p F ϖ).obj W) s)]
  rw [limitFrobHom_double p F 1 m ((yFunctor p F ϖ).obj W) s]
  have h1 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (piece_shift p F ϖ m W))
    (le_of_eq (yFunctor_frobOpens p F ϖ (1 + m) W).symm)))
    (limitFrobHom p F (1 + m) ((yFunctor p F ϖ).obj W) s)
  have h2 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (frobOpens_mono p F 1
      (le_of_eq (yFunctor_frobOpens p F ϖ m W).symm))
    (le_of_eq (frobOpens_add p F 1 m ((yFunctor p F ϖ).obj W)).symm)))
    (limitFrobHom p F (1 + m) ((yFunctor p F ϖ).obj W) s)
  exact h1.trans h2.symm

/-- The `(1+m)`-th piece sits inside the Frobenius preimage of the
saturation. -/
theorem piece_le_frobOpens_sat (m : ℤ) (W : Opens ↥(yTop p F ϖ)) :
    (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W)
      ≤ frobOpens p F 1
          ((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W))) := by
  rw [← piece_shift p F ϖ m W]
  exact frobOpens_mono p F 1 (yFunctor_translate_le p F ϖ W m)

/-- The shifted pieces cover the Frobenius preimage of the saturation
(membership form). -/
theorem pieces_cover_frobOpens_sat (W : Opens ↥(yTop p F ϖ))
    (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (hv : v ∈ frobOpens p F 1 ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))) :
    ∃ m : ℤ, v ∈ (yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W) := by
  rw [show frobOpens p F 1 ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))
    = (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)) from
    frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W)] at hv
  obtain ⟨y, hy, rfl⟩ := hv
  rw [show curvePreimage p F ϖ (xImage p F ϖ W)
      = ⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W from
    curvePreimage_xImage p F ϖ W] at hy
  rw [Opens.coe_iSup] at hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  refine ⟨k - 1, ⟨y, ?_, rfl⟩⟩
  show y ∈ ((Opens.map (yFrobTop p F ϖ (1 + (k - 1)))).obj W : Set _)
  rw [show (1 : ℤ) + (k - 1) = k by omega]
  exact hk

/-- **The per-piece invariance computation**: on each shifted piece, the
transported glued section agrees with the stability restriction. -/
theorem glue_piece_eq (W : Opens ↥(yTop p F ϖ))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W)))
    (g : ↥(limitSections ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))))
    (hg : ∀ k : ℤ, limitRestrict (yFunctor_translate_le p F ϖ W k) g
      = translateFam p F ϖ W s k) (m : ℤ) :
    limitRestrict (piece_le_frobOpens_sat p F ϖ m W)
        (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
          (curvePreimage p F ϖ (xImage p F ϖ W))) g)
      = limitRestrict (piece_le_frobOpens_sat p F ϖ m W)
          (limitRestrict (le_of_eq
            (frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W)))
            g) := by
  have hL1 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (piece_shift p F ϖ m W).symm)
    (frobOpens_mono p F 1 (yFunctor_translate_le p F ϖ W m))))
    (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W))) g)
  have hL2 := limitFrobHom_limitRestrict p F 1
    (yFunctor_translate_le p F ϖ W m) g
  have hL3 := congrArg (limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm))
    (congrArg (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ m)).obj W))) (hg m))
  have hL4 := congrArg (limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm))
    (translateFam_succ p F ϖ m W s).symm
  have hL5 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (piece_shift p F ϖ m W).symm)
    (le_of_eq (piece_shift p F ϖ m W))))
    (translateFam p F ϖ W s (1 + m))
  have hL6 := congr_fun (congrArg DFunLike.coe (limitRestrict_id
    ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W))))
    (translateFam p F ϖ W s (1 + m))
  have hR1 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (piece_le_frobOpens_sat p F ϖ m W)
    (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W)))))
    g
  calc limitRestrict (piece_le_frobOpens_sat p F ϖ m W)
        (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
          (curvePreimage p F ϖ (xImage p F ϖ W))) g)
      = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitRestrict (frobOpens_mono p F 1
            (yFunctor_translate_le p F ϖ W m))
            (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
              (curvePreimage p F ϖ (xImage p F ϖ W))) g)) := hL1.symm
    _ = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
            ((Opens.map (yFrobTop p F ϖ m)).obj W))
            (limitRestrict (yFunctor_translate_le p F ϖ W m) g)) :=
        congrArg _ hL2.symm
    _ = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitFrobHom p F 1 ((yFunctor p F ϖ).obj
            ((Opens.map (yFrobTop p F ϖ m)).obj W))
            (translateFam p F ϖ W s m)) := hL3
    _ = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitRestrict (le_of_eq (piece_shift p F ϖ m W))
            (translateFam p F ϖ W s (1 + m))) := hL4
    _ = translateFam p F ϖ W s (1 + m) := hL5.trans hL6
    _ = limitRestrict (yFunctor_translate_le p F ϖ W (1 + m)) g := (hg (1 + m)).symm
    _ = limitRestrict (piece_le_frobOpens_sat p F ϖ m W)
          (limitRestrict (le_of_eq
            (frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W)))
            g) := hR1.symm

/-- **The glued section is `φ`-invariant** (D-iv-3(ii-c β), completed):
sheaf separation over the shifted translate cover. -/
theorem glue_invariant (W : Opens ↥(yTop p F ϖ))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W)))
    (g : ↥(limitSections ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))))
    (hg : ∀ k : ℤ, limitRestrict (yFunctor_translate_le p F ϖ W k) g
      = translateFam p F ϖ W s k) :
    limitFrobHom p F 1 ((yFunctor p F ϖ).obj
        (curvePreimage p F ϖ (xImage p F ϖ W))) g
      = limitRestrict (le_of_eq
          (frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W))) g := by
  have hVS : ((frobOpens p F 1 ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))
      : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      ⊆ Subtype.val ⁻¹' Y p F ϖ := by
    rw [frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W)]
    exact yFunctor_trace p F ϖ _
  have hcov : ((frobOpens p F 1 ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))
      : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      ⊆ ⋃ m : ULift ℤ, (SetLike.coe ((yFunctor p F ϖ).obj
          ((Opens.map (yFrobTop p F ϖ (1 + m.down))).obj W))) := by
    intro v hv
    obtain ⟨m, hm⟩ := pieces_cover_frobOpens_sat p F ϖ W v hv
    exact Set.mem_iUnion.mpr ⟨⟨m⟩, hm⟩
  exact (isLimitSheafOn_Y p F ϖ).injective hVS
    (ι := ULift ℤ)
    (U := fun m : ULift ℤ => (yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ (1 + m.down))).obj W))
    (fun m => piece_le_frobOpens_sat p F ϖ m.down W) hcov
    (fun m => glue_piece_eq p F ϖ W s g hg m.down)

/-- **The invariant extension** (D-iv-3(ii-c β), the bundled form): every
section over a wandering-separated open extends to a `φ`-invariant section
of the curve presheaf over the saturation, restricting back to it on the
zero translate. -/
theorem exists_invariant_extension (W : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ∃ g : ↥(frobFixed p F ϖ (xImage p F ϖ W)),
      limitRestrict (yFunctor_translate_le p F ϖ W 0) g.1
        = limitRestrict (yFunctor_translate_zero_le p F ϖ W) s := by
  obtain ⟨g, hg, hg0⟩ := exists_glue_extending p F ϖ W hdis s
  exact ⟨⟨g, glue_invariant p F ϖ W s g hg⟩, hg0⟩

/-- **Germ naturality of the projection stalk map**: the stalk map of the
curve projection carries the germ of an invariant section to the germ of its
underlying section. -/
theorem ringStalkMap_piYHom_germ (y : ↥(yTop p F ϖ))
    (V : Opens (Curve p F ϖ)) (hy : yTopToCurve p F ϖ y ∈ V)
    (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op V))) :
    (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom
        ((curveSpace p F ϖ).ringPresheaf.germ V (yTopToCurve p F ϖ y) hy t)
      = (yPresheafedSpace p F ϖ).ringPresheaf.germ
          ((Opens.map (yTopToCurveTop p F ϖ)).obj V) y hy
          (piComponent p F ϖ V t) := by
  have hunfold : ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y
      = (TopCat.Presheaf.stalkFunctor CommRingCat
            (ConcreteCategory.hom (piYHom p F ϖ).base y)).map
          (Functor.whiskerRight (piYHom p F ϖ).c
            CompleteTopCommRingCat.forgetToCommRingCat)
        ≫ TopCat.Presheaf.stalkPushforward CommRingCat
            (piYHom p F ϖ).base
            ((yPresheafedSpace p F ϖ).presheaf
              ⋙ CompleteTopCommRingCat.forgetToCommRingCat) y := rfl
  have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := CommRingCat) V (ConcreteCategory.hom (piYHom p F ϖ).base y)
    hy (Functor.whiskerRight (piYHom p F ϖ).c
      CompleteTopCommRingCat.forgetToCommRingCat) t
  have h2 := TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat
    (piYHom p F ϖ).base
    ((yPresheafedSpace p F ϖ).presheaf
      ⋙ CompleteTopCommRingCat.forgetToCommRingCat) V y hy
    ((Functor.whiskerRight (piYHom p F ϖ).c
      CompleteTopCommRingCat.forgetToCommRingCat).app (op V) t)
  exact (congrArg (fun h => (ConcreteCategory.hom h)
      ((ConcreteCategory.hom (TopCat.Presheaf.germ
        ((curveSpace p F ϖ).presheaf
          ⋙ CompleteTopCommRingCat.forgetToCommRingCat) V
        (ConcreteCategory.hom (piYHom p F ϖ).base y) hy)) t))
      hunfold).trans
    (rfl.trans ((congrArg (ConcreteCategory.hom
      (TopCat.Presheaf.stalkPushforward CommRingCat (piYHom p F ϖ).base
        ((yPresheafedSpace p F ϖ).presheaf
          ⋙ CompleteTopCommRingCat.forgetToCommRingCat) y)) h1).trans h2))

/-- The restricted ring presheaf's action is the `yFunctor`-level
restriction (pointwise). -/
theorem yRingPresheaf_map_apply {V' V : Opens ↥(yTop p F ϖ)} (h : V' ≤ V)
    (f : ToType ((yPresheafedSpace p F ϖ).ringPresheaf.obj (op V))) :
    (ConcreteCategory.hom
        ((yPresheafedSpace p F ϖ).ringPresheaf.map (homOfLE h).op)) f
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE h))) f :=
  structurePresheaf_map (((yFunctor p F ϖ).map (homOfLE h)).op) f

/-- Germ-restriction collapse for the restricted presheaf (the
`limitRestrict` form). -/
theorem yGerm_limitRestrict {V' V : Opens ↥(yTop p F ϖ)} (h : V' ≤ V)
    {y : ↥(yTop p F ϖ)} (hy : y ∈ V')
    (f : ToType ((yPresheafedSpace p F ϖ).ringPresheaf.obj (op V))) :
    (yPresheafedSpace p F ϖ).ringPresheaf.germ V' y hy
        (limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE h))) f)
      = (yPresheafedSpace p F ϖ).ringPresheaf.germ V y (h hy) f := by
  rw [← yRingPresheaf_map_apply p F ϖ h f]
  exact TopCat.Presheaf.germ_res_apply
    ((yPresheafedSpace p F ϖ).ringPresheaf) (homOfLE h) y hy f

/-- **Surjectivity of the projection stalk map** (D-iv-3(γ ii)): every germ
of the `𝒴`-presheaf lifts to an invariant germ of the curve presheaf. -/
theorem ringStalkMap_piYHom_surjective (y : ↥(yTop p F ϖ)) :
    Function.Surjective
      (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom := by
  intro a
  obtain ⟨U, hyU, f, rfl⟩ := ((yPresheafedSpace p F ϖ).ringPresheaf).exists_germ_eq a
  obtain ⟨W₀, hyW₀, hdis₀⟩ := exists_disjoint_translates p F ϖ y
  set W : Opens ↥(yTop p F ϖ) := U ⊓ W₀ with hWdef
  have hyW : y ∈ W := ⟨hyU, hyW₀⟩
  have hdis : ∀ k : ℤ, k ≠ 0 → Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) := by
    intro k hk
    refine (hdis₀ k hk).mono ?_ ?_
    · intro z hz
      exact (hz : z ∈ (Opens.map (yFrobTop p F ϖ k)).obj (U ⊓ W₀)).2
    · exact fun z hz => (hz : z ∈ (U ⊓ W₀ : Opens _)).2
  set fW := limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE
      (inf_le_left : W ≤ U)))) f with hfWdef
  obtain ⟨t, ht0⟩ := exists_invariant_extension p F ϖ W hdis fW
  have hmem : yTopToCurve p F ϖ y ∈ xImage p F ϖ W := ⟨y, hyW, rfl⟩
  refine ⟨(curveSpace p F ϖ).ringPresheaf.germ (xImage p F ϖ W) (yTopToCurve p F ϖ y) hmem t, ?_⟩
  rw [ringStalkMap_piYHom_germ p F ϖ y (xImage p F ϖ W) hmem t]
  -- the zero-translate membership of y
  have hy0 : y ∈ (Opens.map (yFrobTop p F ϖ 0)).obj W := by
    show yFrobTop p F ϖ 0 y ∈ (W : Set _)
    rw [yFrobTop_zero p F ϖ y]
    exact hyW
  -- chase both germs down to the zero translate
  have h1 := yGerm_limitRestrict p F ϖ (translate_le_curvePreimage_xImage p F ϖ W 0) hy0 t.1
  have h2 := yGerm_limitRestrict p F ϖ (le_of_eq (map_yFrobTop_zero p F ϖ W)) hy0 fW
  have h3 := yGerm_limitRestrict p F ϖ (inf_le_left : W ≤ U) hyW f
  have hchain : ((yPresheafedSpace p F ϖ).ringPresheaf.germ
      ((Opens.map (yTopToCurveTop p F ϖ)).obj (xImage p F ϖ W)) y hmem)
      (piComponent p F ϖ (xImage p F ϖ W) t)
      = ((yPresheafedSpace p F ϖ).ringPresheaf.germ U y hyU) f := by
    have e1 : ((yPresheafedSpace p F ϖ).ringPresheaf.germ
        ((Opens.map (yTopToCurveTop p F ϖ)).obj (xImage p F ϖ W)) y hmem)
        (piComponent p F ϖ (xImage p F ϖ W) t)
        = ((yPresheafedSpace p F ϖ).ringPresheaf.germ ((Opens.map (yFrobTop p F ϖ 0)).obj W) y hy0)
          (limitRestrict (yFunctor_translate_le p F ϖ W 0) t.1) := h1.symm
    have e2 : ((yPresheafedSpace p F ϖ).ringPresheaf.germ
        ((Opens.map (yFrobTop p F ϖ 0)).obj W) y hy0)
        (limitRestrict (yFunctor_translate_le p F ϖ W 0) t.1)
        = ((yPresheafedSpace p F ϖ).ringPresheaf.germ ((Opens.map (yFrobTop p F ϖ 0)).obj W) y hy0)
          (limitRestrict (yFunctor_translate_zero_le p F ϖ W) fW) :=
      congrArg _ ht0
    have e3 : ((yPresheafedSpace p F ϖ).ringPresheaf.germ
        ((Opens.map (yFrobTop p F ϖ 0)).obj W) y hy0)
        (limitRestrict (yFunctor_translate_zero_le p F ϖ W) fW)
        = ((yPresheafedSpace p F ϖ).ringPresheaf.germ W y hyW) fW := h2
    exact ((e1.trans e2).trans e3).trans h3
  exact hchain

/-- The general piece inclusion into the Frobenius preimage of a saturated
open. -/
theorem piece_le_frobOpens_general (V : Opens (Curve p F ϖ)) (m : ℤ)
    {W : Opens ↥(yTop p F ϖ)}
    (hWle : ∀ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W
      ≤ curvePreimage p F ϖ V) :
    (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W)
      ≤ frobOpens p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) := by
  rw [← piece_shift p F ϖ m W]
  exact frobOpens_mono p F 1
    (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m))))

/-- **The invariant piece transport**: the `(1+m)`-piece restriction of an
invariant section is the Frobenius transport of its `m`-piece restriction. -/
theorem invariant_piece_transport (V : Opens (Curve p F ϖ))
    (t : ↥(frobFixed p F ϖ V)) (m : ℤ) {W : Opens ↥(yTop p F ϖ)}
    (hWle : ∀ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W
      ≤ curvePreimage p F ϖ V) :
    limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle (1 + m)))))
        t.1
      = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitFrobHom p F 1
            ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ m)).obj W))
            (limitRestrict
              (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m)))) t.1)) := by
  have hinv : limitFrobHom p F 1
      ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) t.1
      = limitRestrict (le_of_eq
          (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)) t.1 := t.2
  have hL1 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (piece_shift p F ϖ m W).symm)
    (frobOpens_mono p F 1
      (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m)))))))
    (limitFrobHom p F 1
      ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) t.1)
  have hL2 := limitFrobHom_limitRestrict p F 1
    (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m)))) t.1
  have hR1 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (piece_le_frobOpens_general p F ϖ V m hWle)
    (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)))) t.1
  calc limitRestrict
        (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle (1 + m))))) t.1
      = limitRestrict (piece_le_frobOpens_general p F ϖ V m hWle)
          (limitRestrict (le_of_eq
            (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)) t.1) := hR1.symm
    _ = limitRestrict (piece_le_frobOpens_general p F ϖ V m hWle)
          (limitFrobHom p F 1
            ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) t.1) :=
        congrArg _ hinv.symm
    _ = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitRestrict (frobOpens_mono p F 1
            (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m)))))
            (limitFrobHom p F 1
              ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) t.1)) :=
        hL1.symm
    _ = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm)
          (limitFrobHom p F 1
            ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ m)).obj W))
            (limitRestrict
              (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m)))) t.1)) :=
        congrArg _ hL2.symm

/-- **The piece step**: invariant sections agreeing on the `m`-th piece
agree on the `(1+m)`-th. -/
theorem invariant_piece_step (V : Opens (Curve p F ϖ))
    (t t' : ↥(frobFixed p F ϖ V)) (m : ℤ)
    {W : Opens ↥(yTop p F ϖ)}
    (hWle : ∀ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W
      ≤ curvePreimage p F ϖ V)
    (hm : limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m))))
        t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m))))
        t'.1) :
    limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle (1 + m)))))
        t.1
      = limitRestrict
          (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle (1 + m))))) t'.1 := by
  rw [invariant_piece_transport p F ϖ V t m hWle,
    invariant_piece_transport p F ϖ V t' m hWle, hm]

/-! ### The transport inversion toolkit and full piece determination
(D-iv-3 gamma-iii): the Frobenius transports are injective, so an invariant
section is determined on every translate by its zero piece. -/

theorem frobOpens_inv_collapse (a : ℤ)
    (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    frobOpens p F (-a) (frobOpens p F a U) = U := by
  rw [← frobOpens_add p F (-a) a U]
  rw [show (-a) + a = 0 by omega]
  exact frobOpens_zero p F U

/-- The zero-sum transport collapse (index-generalized). -/
theorem limitFrobHom_eq_zero_of (c : ℤ) (hc : c = 0)
    (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (s : ↥(limitSections U))
    (hUc : frobOpens p F c U = U) :
    limitFrobHom p F c U s = limitRestrict (le_of_eq hUc) s := by
  subst hc
  exact limitFrobHom_zero p F U s

/-- The left inverse of the limit transport. -/
theorem limitFrobHom_leftInv (a : ℤ)
    (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (s : ↥(limitSections U)) :
    limitFrobHom p F (-a) (frobOpens p F a U) (limitFrobHom p F a U s)
      = limitRestrict (le_of_eq (frobOpens_inv_collapse p F a U)) s := by
  rw [limitFrobHom_double p F (-a) a U s]
  have hUc : frobOpens p F ((-a) + a) U = U := by
    rw [show (-a) + a = 0 by omega]
    exact frobOpens_zero p F U
  rw [limitFrobHom_eq_zero_of p F ((-a) + a) (by omega) U s hUc]
  exact congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (frobOpens_add p F (-a) a U).symm)
    (le_of_eq hUc))) s

/-- Restrictions along an equality of opens are injective. -/
theorem limitRestrict_eq_injective
    {U U' : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} (h : U = U') :
    Function.Injective
      (limitRestrict (A := Ainf p F) (le_of_eq h)) := by
  intro X X' hXX
  have h2 := congrArg (limitRestrict (le_of_eq h.symm)) hXX
  have hcomp := fun z => congr_fun (congrArg DFunLike.coe
    (limitRestrict_comp (le_of_eq h.symm) (le_of_eq h))) z
  have hid := fun z => congr_fun (congrArg DFunLike.coe
    (limitRestrict_id U')) z
  calc X = limitRestrict (le_of_eq h.symm)
        (limitRestrict (le_of_eq h) X) := ((hcomp X).trans (hid X)).symm
    _ = limitRestrict (le_of_eq h.symm)
        (limitRestrict (le_of_eq h) X') := h2
    _ = X' := (hcomp X').trans (hid X')

/-- **The limit transport is injective.** -/
theorem limitFrobHom_injective (a : ℤ)
    (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    Function.Injective (limitFrobHom p F a U) := by
  intro X X' h
  have h1 := congrArg (limitFrobHom p F (-a) (frobOpens p F a U)) h
  rw [limitFrobHom_leftInv p F a U X, limitFrobHom_leftInv p F a U X'] at h1
  exact limitRestrict_eq_injective p F (frobOpens_inv_collapse p F a U) h1

/-- The piece step, index-flexible form. -/
theorem invariant_piece_step' (V : Opens (Curve p F ϖ))
    (t t' : ↥(frobFixed p F ϖ V)) (m k : ℤ) (hk : 1 + m = k)
    {W : Opens ↥(yTop p F ϖ)}
    (hWle : ∀ j : ℤ, (Opens.map (yFrobTop p F ϖ j)).obj W
      ≤ curvePreimage p F ϖ V)
    (hm : limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m))))
        t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m))))
        t'.1) :
    limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle k)))) t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle k))))
        t'.1 := by
  subst hk
  exact invariant_piece_step p F ϖ V t t' m hWle hm

/-- The backward piece step, index-flexible form. -/
theorem invariant_piece_back' (V : Opens (Curve p F ϖ))
    (t t' : ↥(frobFixed p F ϖ V)) (m k : ℤ) (hk : 1 + m = k)
    {W : Opens ↥(yTop p F ϖ)}
    (hWle : ∀ j : ℤ, (Opens.map (yFrobTop p F ϖ j)).obj W
      ≤ curvePreimage p F ϖ V)
    (hkeq : limitRestrict
        (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle k)))) t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle k))))
        t'.1) :
    limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m)))) t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle m))))
        t'.1 := by
  subst hk
  have ht := invariant_piece_transport p F ϖ V t m hWle
  have ht' := invariant_piece_transport p F ϖ V t' m hWle
  rw [ht, ht'] at hkeq
  have h2 := limitRestrict_eq_injective p F
    (piece_shift p F ϖ m W).symm hkeq
  exact limitFrobHom_injective p F 1 _ h2

/-- **Invariant sections agreeing on the zero piece agree on every piece.** -/
theorem invariant_pieces_eq (V : Opens (Curve p F ϖ))
    (t t' : ↥(frobFixed p F ϖ V)) {W : Opens ↥(yTop p F ϖ)}
    (hWle : ∀ j : ℤ, (Opens.map (yFrobTop p F ϖ j)).obj W
      ≤ curvePreimage p F ϖ V)
    (h0 : limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle 0))))
        t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle 0))))
        t'.1) (k : ℤ) :
    limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle k)))) t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE (hWle k))))
        t'.1 := by
  induction k using Int.induction_on with
  | zero => exact h0
  | succ n ih =>
    exact invariant_piece_step' p F ϖ V t t' n (n + 1) (by omega) hWle ih
  | pred n ih =>
    exact invariant_piece_back' p F ϖ V t t' (-(n : ℤ) - 1) (-n) (by omega)
      hWle ih

/-- The image bound: opens inside a saturated preimage have image inside
the saturating open. -/
theorem xImage_le (W : Opens ↥(yTop p F ϖ)) (V : Opens (Curve p F ϖ))
    (h : W ≤ curvePreimage p F ϖ V) : xImage p F ϖ W ≤ V := by
  rintro x ⟨w, hw, rfl⟩
  exact h hw

/-- **Separation of invariant sections** (D-iv-3(γ iii), the section-level
statement): two `φ`-invariant sections over a saturation agreeing on the
zero translate are equal. -/
theorem invariant_sections_eq_of_zero_piece (W : Opens ↥(yTop p F ϖ))
    (t t' : ↥(frobFixed p F ϖ (xImage p F ϖ W)))
    (h0 : limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE
        (translate_le_curvePreimage_xImage p F ϖ W 0)))) t.1
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE
        (translate_le_curvePreimage_xImage p F ϖ W 0)))) t'.1) :
    t = t' := by
  have hall := invariant_pieces_eq p F ϖ (xImage p F ϖ W) t t'
    (fun k => translate_le_curvePreimage_xImage p F ϖ W k) h0
  have hcov : (((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))
      : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ m : ULift ℤ, (SetLike.coe ((yFunctor p F ϖ).obj
          ((Opens.map (yFrobTop p F ϖ m.down)).obj W))) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hv
    rw [show curvePreimage p F ϖ (xImage p F ϖ W)
        = ⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W from
      curvePreimage_xImage p F ϖ W] at hy
    rw [Opens.coe_iSup] at hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨⟨k⟩, ⟨y, hk, rfl⟩⟩
  refine Subtype.ext ((isLimitSheafOn_Y p F ϖ).injective
    (V := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))
    (yFunctor_trace p F ϖ _)
    (ι := ULift ℤ)
    (U := fun m : ULift ℤ => (yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ m.down)).obj W))
    (fun m => leOfHom ((yFunctor p F ϖ).map (homOfLE
      (translate_le_curvePreimage_xImage p F ϖ W m.down)))) hcov
    (fun m => hall m.down))

/-- The curve ring presheaf's action is the invariant restriction
(pointwise). -/
theorem curveRingPresheaf_map_apply {V' V : Opens (Curve p F ϖ)}
    (h : V' ≤ V)
    (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op V))) :
    (ConcreteCategory.hom
        ((curveSpace p F ϖ).ringPresheaf.map (homOfLE h).op)) t
      = frobFixedRestrict p F ϖ h t := rfl

/-- Two germ-equal sections have equal Frobenius-fixed restrictions on the
wandering open. The core of `ringStalkMap_piYHom_injective`. -/
private theorem frobFixedRestrict_eq_of_germ_eq (y : ↥(yTop p F ϖ))
    {V₁ V₂ : Opens (Curve p F ϖ)}
    (t₁ : ((curveSpace p F ϖ).ringPresheaf).obj (Opposite.op V₁))
    (t₂ : ((curveSpace p F ϖ).ringPresheaf).obj (Opposite.op V₂))
    {U W₀ : Opens ↥(yTop p F ϖ)}
    {iU : U ⟶ curvePreimage p F ϖ V₁} {iV : U ⟶ curvePreimage p F ϖ V₂}
    (hres : ((yPresheafedSpace p F ϖ).ringPresheaf).map iU.op
        (piComponent p F ϖ V₁ t₁)
      = ((yPresheafedSpace p F ϖ).ringPresheaf).map iV.op
        (piComponent p F ϖ V₂ t₂))
    (hU₁ : U ≤ curvePreimage p F ϖ V₁) (hU₂ : U ≤ curvePreimage p F ϖ V₂)
    (hWU : U ⊓ W₀ ≤ U)
    (hle₁ : xImage p F ϖ (U ⊓ W₀) ≤ V₁)
    (hle₂ : xImage p F ϖ (U ⊓ W₀) ≤ V₂) :
    frobFixedRestrict p F ϖ hle₁ t₁ = frobFixedRestrict p F ϖ hle₂ t₂ := by
  refine invariant_sections_eq_of_zero_piece p F ϖ (U ⊓ W₀) _ _ ?_
  have hUres : limitRestrict
      (leOfHom ((yFunctor p F ϖ).map (homOfLE hU₁))) t₁.1
      = limitRestrict
        (leOfHom ((yFunctor p F ϖ).map (homOfLE hU₂))) t₂.1 :=
    (yRingPresheaf_map_apply p F ϖ hU₁
        (piComponent p F ϖ V₁ t₁)).symm.trans
      (hres.trans (yRingPresheaf_map_apply p F ϖ hU₂
        (piComponent p F ϖ V₂ t₂)))
  have hZU : (Opens.map (yFrobTop p F ϖ 0)).obj (U ⊓ W₀) ≤ U :=
    le_trans (le_of_eq (map_yFrobTop_zero p F ϖ (U ⊓ W₀))) hWU
  have hstep := congrArg (limitRestrict
    (leOfHom ((yFunctor p F ϖ).map (homOfLE hZU)))) hUres
  have hcol₁ := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (leOfHom ((yFunctor p F ϖ).map (homOfLE hZU)))
    (leOfHom ((yFunctor p F ϖ).map (homOfLE hU₁))))) t₁.1
  have hcol₂ := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (leOfHom ((yFunctor p F ϖ).map (homOfLE hZU)))
    (leOfHom ((yFunctor p F ϖ).map (homOfLE hU₂))))) t₂.1
  have hexp₁ := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (leOfHom ((yFunctor p F ϖ).map (homOfLE
      (translate_le_curvePreimage_xImage p F ϖ (U ⊓ W₀) 0))))
    (yFunctor_curvePreimage_mono p F ϖ hle₁))) t₁.1
  have hexp₂ := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (leOfHom ((yFunctor p F ϖ).map (homOfLE
      (translate_le_curvePreimage_xImage p F ϖ (U ⊓ W₀) 0))))
    (yFunctor_curvePreimage_mono p F ϖ hle₂))) t₂.1
  exact hexp₁.trans ((hcol₁.symm.trans (hstep.trans hcol₂)).trans
    hexp₂.symm)

/-- **Injectivity of the projection stalk map** (D-iv-3(γ iii)): an
invariant germ is determined by its underlying `𝒴`-germ. -/
theorem ringStalkMap_piYHom_injective (y : ↥(yTop p F ϖ)) :
    Function.Injective
      (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom := by
  intro a b hab
  obtain ⟨V₁, h₁, t₁, rfl⟩ :=
    ((curveSpace p F ϖ).ringPresheaf).exists_germ_eq a
  obtain ⟨V₂, h₂, t₂, rfl⟩ :=
    ((curveSpace p F ϖ).ringPresheaf).exists_germ_eq b
  have hyab : ((yPresheafedSpace p F ϖ).ringPresheaf.germ
      ((Opens.map (yTopToCurveTop p F ϖ)).obj V₁) y h₁)
      (piComponent p F ϖ V₁ t₁)
      = ((yPresheafedSpace p F ϖ).ringPresheaf.germ
        ((Opens.map (yTopToCurveTop p F ϖ)).obj V₂) y h₂)
        (piComponent p F ϖ V₂ t₂) :=
    (ringStalkMap_piYHom_germ p F ϖ y V₁ h₁ t₁).symm.trans
      (hab.trans (ringStalkMap_piYHom_germ p F ϖ y V₂ h₂ t₂))
  obtain ⟨U, hyU, iU, iV, hres⟩ :=
    TopCat.Presheaf.germ_eq ((yPresheafedSpace p F ϖ).ringPresheaf)
      y h₁ h₂ _ _ hyab
  obtain ⟨W₀, hyW₀, hdis₀⟩ := exists_disjoint_translates p F ϖ y
  have hyW : y ∈ U ⊓ W₀ := ⟨hyU, hyW₀⟩
  have hWU : U ⊓ W₀ ≤ U := inf_le_left
  have hU₁ : U ≤ curvePreimage p F ϖ V₁ := leOfHom iU
  have hU₂ : U ≤ curvePreimage p F ϖ V₂ := leOfHom iV
  have hle₁ : xImage p F ϖ (U ⊓ W₀) ≤ V₁ :=
    xImage_le p F ϖ (U ⊓ W₀) V₁ (le_trans hWU hU₁)
  have hle₂ : xImage p F ϖ (U ⊓ W₀) ≤ V₂ :=
    xImage_le p F ϖ (U ⊓ W₀) V₂ (le_trans hWU hU₂)
  have hmem : yTopToCurve p F ϖ y ∈ xImage p F ϖ (U ⊓ W₀) := ⟨y, hyW, rfl⟩
  -- the two invariant restrictions agree: separation over the translates
  have hz := frobFixedRestrict_eq_of_germ_eq p F ϖ y t₁ t₂ hres hU₁ hU₂ hWU
    hle₁ hle₂
  -- both germs collapse to the common germ at the saturation image
  have hg₁ : ((curveSpace p F ϖ).ringPresheaf.germ V₁
      (yTopToCurve p F ϖ y) h₁) t₁
      = ((curveSpace p F ϖ).ringPresheaf.germ
        (xImage p F ϖ (U ⊓ W₀)) (yTopToCurve p F ϖ y) hmem)
        (frobFixedRestrict p F ϖ hle₁ t₁) :=
    (TopCat.Presheaf.germ_res_apply
      ((curveSpace p F ϖ).ringPresheaf) (homOfLE hle₁)
      (yTopToCurve p F ϖ y) hmem t₁).symm
  have hg₂ : ((curveSpace p F ϖ).ringPresheaf.germ V₂
      (yTopToCurve p F ϖ y) h₂) t₂
      = ((curveSpace p F ϖ).ringPresheaf.germ
        (xImage p F ϖ (U ⊓ W₀)) (yTopToCurve p F ϖ y) hmem)
        (frobFixedRestrict p F ϖ hle₂ t₂) :=
    (TopCat.Presheaf.germ_res_apply
      ((curveSpace p F ϖ).ringPresheaf) (homOfLE hle₂)
      (yTopToCurve p F ϖ y) hmem t₂).symm
  exact hg₁.trans ((congrArg
    (((curveSpace p F ϖ).ringPresheaf.germ (xImage p F ϖ (U ⊓ W₀))
      (yTopToCurve p F ϖ y) hmem)) hz).trans hg₂.symm)

/-! ### The curve as an object of Wedhorn's category (D-iv-γ packaging) -/

/-- A chosen point of the `𝒴`-fiber over a curve point. -/
noncomputable def fiberPoint (x : Curve p F ϖ) : ↥(yTop p F ϖ) :=
  ((isOpenQuotientMap_yTopToCurve p F ϖ).surjective x).choose

theorem yTopToCurve_fiberPoint (x : Curve p F ϖ) :
    yTopToCurve p F ϖ (fiberPoint p F ϖ x) = x :=
  ((isOpenQuotientMap_yTopToCurve p F ϖ).surjective x).choose_spec

/-- **The bijectivity of the projection stalk map** (D-iv-3(γ),
assembled). -/
theorem ringStalkMap_piYHom_bijective (y : ↥(yTop p F ϖ)) :
    Function.Bijective
      (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom :=
  ⟨ringStalkMap_piYHom_injective p F ϖ y,
    ringStalkMap_piYHom_surjective p F ϖ y⟩

/-- **The stalk comparison of the curve** (D-iv-3(γ), the packaged form):
the stalk of the curve's structure presheaf at a point is identified with
the `𝒴`-stalk at a chosen fiber point, via point-transport followed by the
bijective projection stalk map. -/
noncomputable def xStalkEquiv (x : Curve p F ϖ) :
    ToType ((curveSpace p F ϖ).ringStalk x)
      ≃+* ToType ((yPresheafedSpace p F ϖ).ringStalk
        (fiberPoint p F ϖ x)) :=
  (((curveSpace p F ϖ).ringPresheaf.stalkCongr
      (Inseparable.of_eq (yTopToCurve_fiberPoint p F ϖ x).symm)
      ).commRingCatIsoToRingEquiv).trans
    (RingEquiv.ofBijective
      (ValuationSpectrum.ringStalkMap (piYHom p F ϖ)
        (fiberPoint p F ϖ x)).hom
      (ringStalkMap_piYHom_bijective p F ϖ (fiberPoint p F ϖ x)))

/-- **The stalks of the curve are local rings** (transport along the stalk
comparison). -/
theorem isLocalRing_xStalk (x : Curve p F ϖ) :
    IsLocalRing (ToType ((curveSpace p F ϖ).ringStalk x)) := by
  have : IsLocalRing (ToType ((yPresheafedSpace p F ϖ).ringStalk
      (fiberPoint p F ϖ x))) :=
    isLocalRing_yStalk p F ϖ (fiberPoint p F ϖ x)
  exact (xStalkEquiv p F ϖ x).symm.isLocalRing

/-- The `𝒴`-stalk valuation (the value of `yVPreObj.val`, standalone). -/
noncomputable def yStalkValue (y : ↥(yTop p F ϖ)) :
    Spv (ToType ((yPresheafedSpace p F ϖ).ringStalk y)) :=
  comap ((yRingStalkEquiv p F ϖ y : _ →+* _))
    (stalkValue (ySpaPoint p F ϖ y))

/-- The support of the `𝒴`-stalk valuation is the maximal ideal
(the `yVPreObj.val_supp` computation, standalone). -/
theorem yStalkValue_supp (y : ↥(yTop p F ϖ)) :
    (yStalkValue p F ϖ y).supp
      = @IsLocalRing.maximalIdeal _ _ (isLocalRing_yStalk p F ϖ y) := by
  have hSloc : IsLocalRing (ToType ((spaRingPresheaf (Ainf p F)).stalk
      (ySpaPoint p F ϖ y))) :=
    isLocalRing_stalk_Y p F ϖ (ySpaPoint p F ϖ y) (ySpaPoint_mem_Y p F ϖ y)
  rw [show yStalkValue p F ϖ y
      = comap ((yRingStalkEquiv p F ϖ y : _ →+* _))
        (stalkValue (ySpaPoint p F ϖ y)) from rfl]
  rw [supp_comap]
  rw [show (stalkValue (ySpaPoint p F ϖ y)).supp
      = @IsLocalRing.maximalIdeal _ _ hSloc from
    (maximalIdeal_stalk_Y p F ϖ (ySpaPoint p F ϖ y)
      (ySpaPoint_mem_Y p F ϖ y)).symm]
  exact @IsLocalRing.maximalIdeal_comap _ _ _ (isLocalRing_yStalk p F ϖ y)
    _ hSloc (((yRingStalkEquiv p F ϖ y) : _ →+* _))
    ⟨fun a ha => (isLocalHom_equiv (yRingStalkEquiv p F ϖ y)).map_nonunit a ha⟩

/-- **The adic Fargues–Fontaine curve as an object of `𝒱^pre`**
(D-iv, the pre-object): the `φ`-invariant structure presheaf on the
quotient, with the stalk-local-ring and stalk-valuation package
transported from `𝒴` along the bijective projection stalk maps. -/
noncomputable def xVPreObj : VPreObj where
  toPresheafedSpace := curveSpace p F ϖ
  isLocalRing_stalk := fun x => isLocalRing_xStalk p F ϖ x
  val := fun x => comap ((xStalkEquiv p F ϖ x : _ →+* _))
    (yStalkValue p F ϖ (fiberPoint p F ϖ x))
  val_supp := fun x => by
    have hSloc : IsLocalRing (ToType ((yPresheafedSpace p F ϖ).ringStalk
        (fiberPoint p F ϖ x))) :=
      isLocalRing_yStalk p F ϖ (fiberPoint p F ϖ x)
    rw [supp_comap]
    rw [show (yStalkValue p F ϖ (fiberPoint p F ϖ x)).supp
        = @IsLocalRing.maximalIdeal _ _ hSloc from
      yStalkValue_supp p F ϖ (fiberPoint p F ϖ x)]
    exact @IsLocalRing.maximalIdeal_comap _ _ _ (isLocalRing_xStalk p F ϖ x)
      _ hSloc (((xStalkEquiv p F ϖ x) : _ →+* _))
      ⟨fun a ha => (isLocalHom_equiv (xStalkEquiv p F ϖ x)).map_nonunit a ha⟩

/-- Saturated preimages commute with binary intersections. -/
theorem curvePreimage_inf (V₁ V₂ : Opens (Curve p F ϖ)) :
    curvePreimage p F ϖ (V₁ ⊓ V₂)
      = curvePreimage p F ϖ V₁ ⊓ curvePreimage p F ϖ V₂ := by
  refine Opens.ext ?_
  rw [Opens.coe_inf]
  rfl

/-- Saturated preimages commute with unions. -/
theorem curvePreimage_iSup {ι : Type*} (U : ι → Opens (Curve p F ϖ)) :
    curvePreimage p F ϖ (iSup U) = ⨆ i, curvePreimage p F ϖ (U i) := by
  refine Opens.ext ?_
  rw [Opens.coe_iSup]
  show yTopToCurve p F ϖ ⁻¹' ((iSup U : Opens (Curve p F ϖ))
      : Set (Curve p F ϖ))
    = ⋃ i, (curvePreimage p F ϖ (U i) : Set ↥(yTop p F ϖ))
  rw [Opens.coe_iSup, Set.preimage_iUnion]
  rfl

/-- The curve presheaf's action is the invariant restriction (pointwise,
the bundled-morphism form). -/
theorem xPresheaf_map_apply {V' V : Opens (Curve p F ϖ)} (h : V' ≤ V)
    (t : ((curveSpace p F ϖ).presheaf.obj (op V) : Type _)) :
    ((curveSpace p F ϖ).presheaf.map (homOfLE h).op).1 t
      = frobFixedRestrict p F ϖ h t := rfl

/-- The 𝒴-side family inherits the compatibility of the `X`-side family: both
`curvePreimage` and `yFunctor` preserve `⊓`, so the two pullbacks agree. -/
private theorem xPresheaf_glue_compat (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {ι : Type u} (U : ι → Opens ↥(curveSpace p F ϖ).carrier)
    (f : ∀ i, {g : T →+* ((curveSpace p F ϖ).presheaf.obj
      (Opposite.op (U i)) : Type _) // Continuous g})
    (hcompat : ∀ i j : ι,
      ((curveSpace p F ϖ).presheaf.map
          (homOfLE (inf_le_left (a := U i) (b := U j))).op).1.comp (f i).1 =
        ((curveSpace p F ϖ).presheaf.map
          (homOfLE (inf_le_right (a := U i) (b := U j))).op).1.comp (f j).1) :
    ∀ i j,
      (limitRestrict (inf_le_left
          (a := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U i)))
          (b := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U j))))).comp
          ((piComponent p F ϖ (U i)).comp (f i).1)
        = (limitRestrict (inf_le_right
            (a := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U i)))
            (b := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U j))))).comp
            ((piComponent p F ϖ (U j)).comp (f j).1) := by
  set U' : ι → Opens ↥(SpaTop (Ainf p F)) :=
    fun i => (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U i)) with hU'def
  intro i j
  refine RingHom.ext fun t => ?_
  have h0 := DFunLike.congr_fun (hcompat i j) t
  have h0' := congrArg Subtype.val
    ((xPresheaf_map_apply p F ϖ
        (inf_le_left (a := U i) (b := U j)) ((f i).1 t)).symm.trans
      (h0.trans (xPresheaf_map_apply p F ϖ
        (inf_le_right (a := U i) (b := U j)) ((f j).1 t))))
  have e1 := curvePreimage_inf p F ϖ (U i) (U j)
  have e2 := yFunctor_inf p F ϖ (curvePreimage p F ϖ (U i))
    (curvePreimage p F ϖ (U j))
  have hpre : (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U i ⊓ U j))
      = U' i ⊓ U' j := by rw [e1, e2]
  exact ValuationSpectrum.limitRestrict_cross_eq_of_opens_eq hpre
    (yFunctor_curvePreimage_mono p F ϖ
      (inf_le_left (a := U i) (b := U j)))
    (yFunctor_curvePreimage_mono p F ϖ
      (inf_le_right (a := U i) (b := U j)))
    (inf_le_left (a := U' i) (b := U' j))
    (inf_le_right (a := U' i) (b := U' j)) h0'


/-- The per-piece half of Frobenius-invariance of the glued section: on each cover piece the
frobenius image and the stability-restriction of `x` agree.

Quantified over a SINGLE piece rather than over the index type. `IsLimitSheafOn.injective`
quantifies its index as `Type u` for the ambient `u` — that of `Ainf p F`, hence of `F`, which
`variable (F : Type*)` auto-binds and therefore leaves unnameable — so any helper that CALLS it
cannot be extracted. Taking the piece as an argument sidesteps the constraint entirely. -/
private theorem xPresheaf_frobEq_on_piece
    (V' Ui : Opens ↥(SpaTop (Ainf p F))) (hlei : Ui ≤ V')
    (stabV : frobOpens p F 1 V' = V') (stabUi : frobOpens p F 1 Ui = Ui)
    (hle2i : Ui ≤ frobOpens p F 1 V')
    (x : ↥(limitSections V')) (ai : ↥(limitSections Ui))
    (hai : limitFrobHom p F 1 Ui ai = limitRestrict (le_of_eq stabUi) ai)
    (hgai : limitRestrict hlei x = ai) :
    limitRestrict hle2i (limitFrobHom p F 1 V' x)
      = limitRestrict hle2i (limitRestrict (le_of_eq stabV) x) := by
  have hLa := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq stabUi.symm) (frobOpens_mono p F 1 hlei)))
    (limitFrobHom p F 1 V' x)
  have hLb := limitFrobHom_limitRestrict p F 1 hlei x
  have hLc := congrArg
    (fun s => limitRestrict (le_of_eq stabUi.symm)
      (limitFrobHom p F 1 Ui s)) (hgai)
  have hLd : limitFrobHom p F 1 Ui ai
      = limitRestrict (le_of_eq stabUi) ai :=
    hai
  have hLe := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq stabUi.symm) (le_of_eq stabUi))) ai
  have hLf := congr_fun (congrArg DFunLike.coe
    (limitRestrict_id Ui)) ai
  have hL : limitRestrict hle2i (limitFrobHom p F 1 V' x)
      = ai :=
    (hLa.symm.trans (congrArg
        (limitRestrict (le_of_eq stabUi.symm)) hLb)).trans
      ((hLc.trans (congrArg
        (limitRestrict (le_of_eq stabUi.symm)) hLd)).trans
      (hLe.trans hLf))
  have hRa := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    hle2i (le_of_eq stabV))) x
  have hR : limitRestrict hle2i
      (limitRestrict (le_of_eq stabV) x) = ai :=
    hRa.trans (hgai)
  exact hL.trans hR.symm


/-- The saturated cover data: transporting `hVS` / `hle` / `hcov` along `stabV`.

Pure `stabV`-transport — it never touches the sheaf structure, which is what lets it out of
`hginv`.  `hginv` itself cannot be extracted (it *calls* `IsLimitSheafOn.injective`, whose
`∀ {ι : Type u}` binds the ambient unnameable universe), but the constraint attaches to that
call, not to the block around it. -/
private theorem xPresheaf_saturated_cover {ι : Type*}
    (V' : Opens ↥(SpaTop (Ainf p F))) (U' : ι → Opens ↥(SpaTop (Ainf p F)))
    (hle : ∀ i, U' i ≤ V')
    (hVS : (V' : Set ↥(SpaTop (Ainf p F))) ⊆ Subtype.val ⁻¹' Y p F ϖ)
    (hcov : (V' : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ i, (U' i : Set ↥(SpaTop (Ainf p F))))
    (stabV : frobOpens p F 1 V' = V') :
    ((frobOpens p F 1 V'
        : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        ⊆ Subtype.val ⁻¹' Y p F ϖ ∧
      (∀ i, U' i ≤ frobOpens p F 1 V') ∧
      ((frobOpens p F 1 V'
        : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        ⊆ ⋃ i, (U' i : Set ↥(SpaTop (Ainf p F))) :=
  ⟨fun v hv => hVS (stabV ▸ hv),
   fun i => le_trans (hle i) (le_of_eq stabV.symm),
   fun v hv => hcov (stabV ▸ hv)⟩


/-- The restriction-compatibility a competing glue must satisfy, in the form
`IsLimitSheafOn.homGlue`'s uniqueness clause consumes.

`g''` and `hg''` come from destructuring the `∃!` in `IsSheafOfTopologicalRings`, whose types
are never written out in the proof; they are transcribed here from the definition
(`HomSheafPredicate.lean:64`) rather than guessed. -/
private theorem xPresheaf_glue_res {ι : Type*} (U : ι → Opens (Curve p F ϖ))
    {T : Type*} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    (f : ∀ i, {g : T →+*
      ↥((curveSpace p F ϖ).presheaf.obj (op (U i))) // Continuous g})
    (g'' : T →+* ↥((curveSpace p F ϖ).presheaf.obj (op (iSup U))))
    (hg'' : ∀ i, ((curveSpace p F ϖ).presheaf.map
      (homOfLE (le_iSup U i)).op).1.comp g'' = (f i).1)
    (hle : ∀ i, (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U i))
      ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ (iSup U))) :
    ∀ i, (limitRestrict (hle i)).comp ((piComponent p F ϖ (iSup U)).comp g'')
      = (piComponent p F ϖ (U i)).comp (f i).1 := by
  intro i
  refine RingHom.ext fun t => ?_
  exact congrArg Subtype.val
    ((xPresheaf_map_apply p F ϖ (le_iSup U i) (g'' t)).symm.trans
      (DFunLike.congr_fun (hg'' i) t))


/-- **The curve presheaf is a sheaf of topological rings** (D-iv-4, Wedhorn
Remark 8.20 for the quotient): compatible continuous `T`-families of
invariant sections glue uniquely — glue the underlying `𝒴`-sections over
the saturated preimages, then check invariance by separation over the
same saturated cover. -/
theorem xPresheaf_isSheafOfTopologicalRings :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (curveSpace p F ϖ).presheaf := by
  intro T _tc _tt _tr ι U f hcompat
  set V' : Opens ↥(SpaTop (Ainf p F)) :=
    (yFunctor p F ϖ).obj (curvePreimage p F ϖ (iSup U)) with hV'def
  set U' : ι → Opens ↥(SpaTop (Ainf p F)) :=
    fun i => (yFunctor p F ϖ).obj (curvePreimage p F ϖ (U i)) with hU'def
  have hle : ∀ i, U' i ≤ V' :=
    fun i => yFunctor_curvePreimage_mono p F ϖ (le_iSup U i)
  have hVS : (V' : Set ↥(SpaTop (Ainf p F)))
      ⊆ Subtype.val ⁻¹' Y p F ϖ := yFunctor_trace p F ϖ _
  have hcov : (V' : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ i, (U' i : Set ↥(SpaTop (Ainf p F))) := by
    rw [hV'def, curvePreimage_iSup p F ϖ U]
    exact yFunctor_cov p F ϖ (fun i => curvePreimage p F ϖ (U i))
  -- the stability equalities
  have stabV : frobOpens p F 1 V' = V' :=
    frobOpens_yFunctor_curvePreimage p F ϖ 1 (iSup U)
  have stabU : ∀ i, frobOpens p F 1 (U' i) = U' i :=
    fun i => frobOpens_yFunctor_curvePreimage p F ϖ 1 (U i)
  -- the underlying 𝒴-side family
  have hcompat' := xPresheaf_glue_compat p F ϖ T U f hcompat
  obtain ⟨g, hg, huniq⟩ := (isLimitSheafOn_Y p F ϖ).homGlue hVS hle hcov
    (fun i => (piComponent p F ϖ (U i)).comp (f i).1)
    (fun i => continuous_subtype_val.comp (f i).2) hcompat'
  -- the glued section is invariant at every T-input
  have hginv : ∀ t : T, g.1 t ∈ frobFixed p F ϖ (iSup U) := by
    intro t
    rw [mem_frobFixed]
    -- separation over the saturated pieces
    obtain ⟨hVS2, hle2, hcov2⟩ :=
      xPresheaf_saturated_cover p F ϖ V' U' hle hVS hcov stabV
    refine (isLimitSheafOn_Y p F ϖ).injective hVS2 hle2 hcov2
      (fun i => ?_)
    -- the common value on the piece: the underlying section of `f i t`
    exact xPresheaf_frobEq_on_piece p F V' (U' i) (hle i) stabV (stabU i) (hle2 i)
      (g.1 t) ((f i).1 t).1 ((f i).1 t).2 (DFunLike.congr_fun (hg i) t)
  -- package the glued invariant section
  set gX : T →+* ↥(frobFixed p F ϖ (iSup U)) :=
    RingHom.codRestrict g.1 (frobFixed p F ϖ (iSup U)) hginv with hgXdef
  have hgXc : Continuous gX := by
    refine continuous_induced_rng.mpr ?_
    exact g.2
  refine ⟨⟨gX, hgXc⟩, fun i => ?_, ?_⟩
  · refine RingHom.ext fun t => ?_
    refine (xPresheaf_map_apply p F ϖ (le_iSup U i) (gX t)).trans ?_
    refine Subtype.ext ?_
    exact DFunLike.congr_fun (hg i) t
  · rintro ⟨g'', hg''c⟩ hg''
    have hres := xPresheaf_glue_res p F ϖ U f g'' hg'' hle
    have := huniq ⟨(piComponent p F ϖ (iSup U)).comp g'',
      continuous_subtype_val.comp hg''c⟩ hres
    have hval := congrArg Subtype.val this
    refine Subtype.ext (RingHom.ext fun t => Subtype.ext ?_)
    exact DFunLike.congr_fun hval t

/-- **The adic Fargues–Fontaine curve as an object of Wedhorn's category
`𝒱`** (D-iv-5, the headline): the `𝒱^pre`-object together with the
sheaf-of-topological-rings condition. -/
noncomputable def xVObj : ValuationSpectrum.VObj :=
  { xVPreObj p F ϖ with
    isSheafTopRings := xPresheaf_isSheafOfTopologicalRings p F ϖ }

end FarguesFontaine

end
