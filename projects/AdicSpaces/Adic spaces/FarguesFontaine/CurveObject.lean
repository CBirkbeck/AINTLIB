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

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter CategoryTheory Opposite

set_option linter.overlappingInstances false

noncomputable section

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

end FarguesFontaine

end
