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

/-- **The value over an empty rational is trivial — general Huber form**
(Wedhorn: `𝒪(∅) = 0`): a nonzero value would carry a `Spa`-point whose
`comap` lies in the empty rational open. -/
theorem presheafValue_subsingleton_of_rationalOpen_empty_huber
    (E : RationalLocData A) (hempty : rationalOpen E.T E.s = ∅) :
    Subsingleton (presheafValue E) := by
  haveI : IsHuberRing (presheafValue E) := presheafValue_isHuberRing_huber E
  letI P_B : PairOfDefinition (presheafValue E) := presheafValue_concretePair E
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete E
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
  haveI := presheafValue_subsingleton_of_rationalOpen_empty_huber i.D
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
      = (z.1.1 : Spv (Ainf p F)) from by
    rw [smul_smul]
    rw [show (Multiplicative.ofAdd k * Multiplicative.ofAdd (-k))
        = (1 : Multiplicative ℤ) from by
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
  have hcompat : ∀ i j : ℤ,
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

end FarguesFontaine

end
