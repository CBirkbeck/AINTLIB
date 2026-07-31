/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».SpaRationalOpenComparison
import «Adic spaces».RationalBasisHuber
import «Adic spaces».PresheafFunctoriality
import «Adic spaces».RationalBasis
import «Adic spaces».StructurePresheafLimit
import «Adic spaces».StructurePresheafBundled
import «Adic spaces».HuberLocLift
import «Adic spaces».SpaRationalOpenHomeomorph
import «Adic spaces».StructureSheaf
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Stalk theory of the structure presheaf, I: point valuations (Wedhorn §8.3)

The valuation-theoretic substrate of the stalk package for `Spa (A, A⁺)`:

* `ValuationSpectrum.pointValue` : the unique Spa-point of `presheafValue D`
  over a Spa-point of `A` inside `R(D.T/D.s)` — Wedhorn Proposition 8.2 read
  backwards through `spaPresheafValueEquivRationalOpen`;
* `ValuationSpectrum.comap_pointValue` / `eq_pointValue_of_comap_eq` : the
  defining property and its uniqueness;
* `ValuationSpectrum.comap_restrictionMapHom_pointValue` : **germ coherence**
  — point valuations are intertwined by the restriction maps, the input for
  the valuation on the stalk (Wedhorn 8.14).
-/

noncomputable section

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **The point valuation on a rational value** (Wedhorn 8.2 read backwards): a
Spa-point of `A` inside the rational subset `R(D.T/D.s)` induces a Spa-point of
the completed rational localization `presheafValue D`, its unique extension. -/
def pointValue (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    Spv (presheafValue D) :=
  ((spaPresheafValueEquivRationalOpen D).symm ⟨v, hv⟩).val

theorem pointValue_mem_spa (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    pointValue D hv ∈ Spa (presheafValue D) (presheafValue D)⁺ :=
  ((spaPresheafValueEquivRationalOpen D).symm ⟨v, hv⟩).property

theorem pointValue_isContinuous (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    (pointValue D hv).IsContinuous :=
  ((mem_spa_iff _).mp (pointValue_mem_spa D hv)).1

/-- The defining property: the point valuation pulls back to the point. -/
theorem comap_pointValue (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap D.canonicalMap (pointValue D hv) = v :=
  congrArg Subtype.val
    ((spaPresheafValueEquivRationalOpen D).apply_symm_apply ⟨v, hv⟩)

/-- Uniqueness: any continuous valuation on the value pulling back to the point
is the point valuation. -/
theorem eq_pointValue_of_comap_eq (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
    {w : Spv (presheafValue D)} (hw : w.IsContinuous)
    (h : comap D.canonicalMap w = v) :
    w = pointValue D hv :=
  comap_canonicalMap_inj_of_isContinuous D hw
    (pointValue_isContinuous D hv) (h.trans (comap_pointValue D hv).symm)

/-- **Restriction compatibility of point valuations** (the germ coherence, S2):
pulling the point valuation of the smaller rational back along the restriction
map gives the point valuation of the larger rational. -/
theorem comap_restrictionMapHom_pointValue [HasLocLiftPowerBounded A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) {v : Spv A}
    (hv' : v ∈ (rationalOpen D'.T D'.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap (restrictionMapHom D D' h) (pointValue D' hv')
      = pointValue D ⟨h hv'.1, hv'.2⟩ := by
  refine eq_pointValue_of_comap_eq D ⟨h hv'.1, hv'.2⟩
    (comap_isContinuous (restrictionMapHom_continuous D D' h)
      (pointValue_isContinuous D' hv')) ?_
  have hcomp : (restrictionMapHom D D' h).comp D.canonicalMap
      = D'.canonicalMap :=
    RingHom.ext (restrictionMapHom_canonicalMap_generic D D' h)
  calc comap D.canonicalMap
        (comap (restrictionMapHom D D' h) (pointValue D' hv'))
      = comap ((restrictionMapHom D D' h).comp D.canonicalMap)
          (pointValue D' hv') := by
        rw [comap_comp]
        rfl
    _ = comap D'.canonicalMap (pointValue D' hv') := by rw [hcomp]
    _ = v := comap_pointValue D' hv'


/-! ### Valuation-theoretic generic bricks and plus functoriality (S4-core) -/

section Generic

variable {B : Type*} [CommRing B]

/-- **(B1)** The `≤ 1`-locus of a continuous valuation is closed (the
ultrametric translate argument: around a point of value `> 1`, the ball
`a + {v < v a}` stays in the complement). -/
theorem isClosed_setOf_vle_one [TopologicalSpace B] [IsTopologicalRing B]
    {w : Spv B} (hw : w.IsContinuous) :
    IsClosed {y : B | w.vle y 1} := by
  letI : ValuativeRel B := w.toValuativeRel
  have hbridge : ∀ x y : B, w.vle x y ↔
      ValuativeRel.valuation B x ≤ ValuativeRel.valuation B y := fun x y =>
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B) x y
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have hlt : ValuativeRel.valuation B 1 < ValuativeRel.valuation B a :=
    lt_of_not_ge (fun hle => ha ((hbridge a 1).mpr hle))
  have hball : IsOpen {h : B | ValuativeRel.valuation B h
      < ValuativeRel.valuation B a} := hw _
  have hmem : (0 : B) ∈ {h : B | ValuativeRel.valuation B h
      < ValuativeRel.valuation B a} := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact lt_of_le_of_lt zero_le hlt
  have htrans : (fun h : B => a + h) '' {h : B | ValuativeRel.valuation B h
      < ValuativeRel.valuation B a} ∈ nhds a := by
    have hopen : IsOpen ((fun h : B => a + h) '' {h : B |
        ValuativeRel.valuation B h < ValuativeRel.valuation B a}) := by
      have := (Homeomorph.addLeft a).isOpenMap _ hball
      simpa using this
    refine hopen.mem_nhds ⟨0, hmem, by simp⟩
  refine Filter.mem_of_superset htrans ?_
  rintro y ⟨h, hh, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  intro hcon
  have hval : ValuativeRel.valuation B (a + h) = ValuativeRel.valuation B a :=
    Valuation.map_add_eq_of_lt_left _ hh
  exact absurd (le_trans (le_of_eq hval.symm) ((hbridge _ 1).mp hcon))
    (not_le_of_gt hlt)

/-- **(B2)** An element integral over a `≤ 1`-bounded subring is `≤ 1`
(the valuation bound on integral extensions). -/
theorem vle_one_of_isIntegral {w : Spv B} {S : Subring B}
    (hS : ∀ y ∈ S, w.vle y 1) {x : B}
    (hx : letI : Algebra ↥S B := S.subtype.toAlgebra; IsIntegral ↥S x) :
    w.vle x 1 := by
  letI : Algebra ↥S B := S.subtype.toAlgebra
  letI : ValuativeRel B := w.toValuativeRel
  have hbridge : ∀ x y : B, w.vle x y ↔
      ValuativeRel.valuation B x ≤ ValuativeRel.valuation B y := fun x y =>
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B) x y
  set v := ValuativeRel.valuation B with hv
  by_contra hgt
  have h1 : (1 : _) < v x := by
    have := lt_of_not_ge (fun hle => hgt ((hbridge x 1).mpr hle))
    rwa [map_one] at this
  obtain ⟨p, hmonic, heval⟩ := hx
  set n := p.natDegree with hn
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · have hp1 : p = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero hmonic h0
    rw [hp1] at heval
    simp only [Polynomial.eval₂_one] at heval
    refine hgt ((hbridge x 1).mpr ?_)
    have hx0 : x = 0 := by
      rw [← mul_one x, show (1 : B) = 0 from heval, mul_zero]
    rw [hx0, map_zero]
    exact zero_le
  have hexp : ∑ i ∈ Finset.range (n + 1), S.subtype (p.coeff i) * x ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact heval
  rw [Finset.sum_range_succ] at hexp
  have hcn : S.subtype (p.coeff n) = 1 := by
    rw [show p.coeff n = 1 from hmonic.coeff_natDegree]
    exact map_one _
  rw [hcn, one_mul] at hexp
  have hxn : x ^ n = -∑ i ∈ Finset.range n, S.subtype (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hexp)
  have hbound : v (x ^ n) ≤ v x ^ (n - 1) := by
    rw [hxn, Valuation.map_neg]
    refine Valuation.map_sum_le v ?_
    intro i hi
    rw [Valuation.map_mul, Valuation.map_pow]
    have hci : v (S.subtype (p.coeff i)) ≤ 1 := by
      have hm := hS (S.subtype (p.coeff i)) (SetLike.coe_mem _)
      have := (hbridge _ 1).mp hm
      rwa [map_one] at this
    have hpow : v x ^ i ≤ v x ^ (n - 1) := pow_le_pow_right₀ h1.le (by
        have := Finset.mem_range.mp hi
        omega)
    calc v (S.subtype (p.coeff i)) * v x ^ i ≤ 1 * v x ^ (n - 1) := mul_le_mul' hci hpow
      _ = v x ^ (n - 1) := one_mul _
  rw [Valuation.map_pow] at hbound
  have hstrict : v x ^ (n - 1) < v x ^ n := pow_lt_pow_right₀ h1 (by omega)
  exact absurd hbound (not_le_of_gt hstrict)

/-- Reflexivity of `vle`. -/
theorem vle_refl {w : Spv B} (a : B) : w.vle a a :=
  (w.vle_total a a).elim id id

/-- `vle 0 1`. -/
theorem vle_zero_one {w : Spv B} : w.vle (0 : B) 1 := by
  letI : ValuativeRel B := w.toValuativeRel
  have hbridge := fun x y : B =>
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B) x y
  refine (hbridge 0 1).mpr ?_
  rw [map_zero]
  exact zero_le

/-- The `≤ 1`-elements are multiplicatively stable. -/
theorem vle_one_mul {w : Spv B} {a b : B} (ha : w.vle a 1) (hb : w.vle b 1) :
    w.vle (a * b) 1 := by
  have h1 := w.mul_vle_mul_left ha b
  rw [one_mul] at h1
  exact w.vle_trans h1 hb

/-- The `≤ 1`-elements are stable under negation. -/
theorem vle_one_neg {w : Spv B} {a : B} (ha : w.vle a 1) : w.vle (-a) 1 := by
  letI : ValuativeRel B := w.toValuativeRel
  have hbridge := fun x y : B =>
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B) x y
  have hneg : w.vle (-a) a := by
    refine (hbridge (-a) a).mpr ?_
    rw [Valuation.map_neg]
  exact w.vle_trans hneg ha

end Generic

section PlusFunctoriality

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A]

/-- The `A⁺`-image generators of `locPlusSubring` are bounded by 1 after restriction. -/
private theorem vle_one_of_algebraMap_Aplus (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (w'' : Spv (presheafValue D'))
    (hw'' : w'' ∈ Spa (presheafValue D') (presheafValue D')⁺)
    {a : A} (ha : a ∈ (A⁺ : Set A)) :
    w''.vle (restrictionMapHom D D' h
        (D.coeRingHom (algebraMap A (Localization.Away D.s) a)))
      (restrictionMapHom D D' h (D.coeRingHom 1)) := by
  rw [map_one, map_one]
  rw [show D.coeRingHom (algebraMap A (Localization.Away D.s) a)
      = D.canonicalMap a from rfl,
    restrictionMapHom_canonicalMap_generic D D' h a]
  exact hw''.2 _ (D'.canonicalMap_Aplus_le_completedPlusSubring a ha)

/-- The `t/s` generators of `locPlusSubring` are bounded by 1 after restriction, by
cancelling against the unit `ρ'(D.s)`. -/
private theorem vle_one_of_divByS_gen (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (w'' : Spv (presheafValue D'))
    (hv''D : comap D'.canonicalMap w'' ∈ rationalOpen D.T D.s)
    (t : D.T) :
    w''.vle (restrictionMapHom D D' h (D.coeRingHom (divByS (t : A) D.s)))
      (restrictionMapHom D D' h (D.coeRingHom 1)) := by
  refine (show w''.vle (restrictionMapHom D D' h
      (D.coeRingHom (divByS (t : A) D.s)))
      (restrictionMapHom D D' h (D.coeRingHom 1)) → _ from fun hh => hh) ?_
  rw [map_one, map_one]
  have hs0 : ¬ w''.vle (D'.canonicalMap D.s) 0 := by
    intro hcon
    refine hv''D.2.2 ?_
    show w''.vle (D'.canonicalMap D.s) (D'.canonicalMap 0)
    rw [map_zero]
    exact hcon
  have hkey : restrictionMapHom D D' h (D.coeRingHom (divByS (t : A) D.s))
      * D'.canonicalMap D.s = D'.canonicalMap (t : A) := by
    calc restrictionMapHom D D' h (D.coeRingHom (divByS (t : A) D.s))
        * D'.canonicalMap D.s
        = restrictionMapHom D D' h (D.coeRingHom (divByS (t : A) D.s))
          * restrictionMapHom D D' h (D.canonicalMap D.s) := by
          rw [restrictionMapHom_canonicalMap_generic D D' h D.s]
      _ = restrictionMapHom D D' h (D.coeRingHom (divByS (t : A) D.s)
          * D.canonicalMap D.s) := (map_mul _ _ _).symm
      _ = restrictionMapHom D D' h (D.canonicalMap (t : A)) := by
          congr 1
          show D.coeRingHom (divByS (t : A) D.s)
              * D.coeRingHom (algebraMap A (Localization.Away D.s) D.s)
            = D.coeRingHom (algebraMap A (Localization.Away D.s) (t : A))
          rw [← map_mul, mul_comm, algebraMap_s_mul_divByS D (t : A)]
      _ = D'.canonicalMap (t : A) :=
          restrictionMapHom_canonicalMap_generic D D' h (t : A)
  have hvt : w''.vle (D'.canonicalMap (t : A)) (D'.canonicalMap D.s) :=
    hv''D.2.1 (t : A) t.2
  have hprod : w''.vle (restrictionMapHom D D' h
      (D.coeRingHom (divByS (t : A) D.s)) * D'.canonicalMap D.s)
      (1 * D'.canonicalMap D.s) := by
    rw [hkey, one_mul]
    exact hvt
  exact w''.vle_mul_cancel hs0 hprod

/-- **Plus functoriality of the restriction maps** (the `σ(B⁺) ⊆ B'⁺` half of
Wedhorn Prop 8.2(3)): the canonical plus subring of a completed rational
localization maps into that of any smaller one. Proof: by the Spa
characterization of the plus ring (`mem_plus_of_forall_spa_vle_one_huber`),
reduce to `≤ 1`-bounds of the pulled-back valuation on the generators, then
climb the closure tower with `isClosed_setOf_vle_one` and
`vle_one_of_isIntegral`. -/
theorem aplus_le_comap_restrictionMapHom (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    ((presheafValue D)⁺ : Subring (presheafValue D))
      ≤ ((presheafValue D')⁺).comap (restrictionMapHom D D' h) := by
  intro x hx
  show restrictionMapHom D D' h x ∈ ((presheafValue D')⁺ : Subring _)
  refine mem_plus_of_forall_spa_vle_one_huber D' _ (fun w'' hw'' => ?_)
  have hwcont : (comap (restrictionMapHom D D' h) w'').IsContinuous :=
    comap_isContinuous (restrictionMapHom_continuous D D' h) ((mem_spa_iff _).mp hw'').1
  have hred : (comap (restrictionMapHom D D' h) w'').vle x 1 →
      w''.vle (restrictionMapHom D D' h x) 1 := by
    intro hh
    have h1 : w''.vle (restrictionMapHom D D' h x) (restrictionMapHom D D' h 1) := hh
    rwa [map_one] at h1
  refine hred ?_
  -- the base point of `w''`, inside both rationals
  have hv''D' := comap_canonicalMap_mem_rationalOpen_inter_spa D' ⟨w'', hw''⟩
  have hv''D : comap D'.canonicalMap w'' ∈ rationalOpen D.T D.s := h hv''D'.1
  -- generator bounds at the localization level
  have hgen : ∀ y ∈ D.locPlusSubring,
      (comap D.coeRingHom (comap (restrictionMapHom D D' h) w'')).vle y 1 := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩ | ⟨t, rfl⟩
      · -- an `A⁺`-image
        exact vle_one_of_algebraMap_Aplus D D' h w'' hw'' ha
      · exact vle_one_of_divByS_gen D D' h w'' hv''D t
    | one => exact vle_refl 1
    | zero => exact vle_zero_one
    | mul a b _ _ iha ihb => exact vle_one_mul iha ihb
    | add a b _ _ iha ihb => exact (comap _ _).vle_add iha ihb
    | neg a _ iha => exact vle_one_neg iha
  -- integral closure at the localization
  have hIntCl : ∀ z ∈ (integralClosure ↥(D.locPlusSubring) (Localization.Away D.s)).toSubring,
      (comap D.coeRingHom (comap (restrictionMapHom D D' h) w'')).vle z 1 := by
    intro z hz
    rw [Subalgebra.mem_toSubring] at hz
    exact vle_one_of_isIntegral hgen hz
  -- the mapped core, then the topological closure
  have hbase : ∀ y ∈ D.completedPlusSubringBase,
      (comap (restrictionMapHom D D' h) w'').vle y 1 := by
    intro y hy
    have hsub : (((integralClosure ↥(D.locPlusSubring)
        (Localization.Away D.s)).toSubring.map D.coeRingHom) : Set (presheafValue D)) ⊆
        {y | (comap (restrictionMapHom D D' h) w'').vle y 1} := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 := hIntCl z hz
      show (comap (restrictionMapHom D D' h) w'').vle (D.coeRingHom z) 1
      have h2 : (comap (restrictionMapHom D D' h) w'').vle (D.coeRingHom z)
          (D.coeRingHom 1) := h1
      rwa [map_one] at h2
    exact closure_minimal hsub (isClosed_setOf_vle_one hwcont) hy
  -- the integral closure at the completion
  refine vle_one_of_isIntegral hbase ?_
  have hx' : x ∈ (integralClosure ↥(D.completedPlusSubringBase)
      (presheafValue D)).toSubring := hx
  rw [Subalgebra.mem_toSubring] at hx'
  exact hx'

/-- Spa-pullback of restriction maps (the point-set half of Wedhorn 8.2(3)):
`comap` along a restriction map sends `Spa` of the smaller value into `Spa` of
the larger. -/
theorem comap_restrictionMapHom_mem_spa (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    {w : Spv (presheafValue D')}
    (hw : w ∈ Spa (presheafValue D') (presheafValue D')⁺) :
    comap (restrictionMapHom D D' h) w
      ∈ Spa (presheafValue D) (presheafValue D)⁺ :=
  comap_mem_spa (restrictionMapHom_continuous D D' h)
    (aplus_le_comap_restrictionMapHom D D' h) hw

end PlusFunctoriality

/-! ### The point valuation on the sections over an arbitrary open (S3a)

Over a Tate pair with integrally-closed plus-ring, the rational opens form a
basis (`exists_isRational_spaOpen_subset`), and the point valuation extends to
the projective-limit sections `limitSections V` over any open neighbourhood,
coherently with all restrictions. -/

section OpenValue

open TopologicalSpace

variable [IsRingOfIntegralElements (A⁺ : Subring A)]
  [HasLocLiftPowerBounded A]

noncomputable local instance : DecidableEq A := Classical.decEq _

/-- Every open neighbourhood admits a valid rational index containing the
point (the rational basis, in `RationalIndex` form). -/
theorem exists_rationalIndex_mem {V : Opens ↥(Spa A A⁺)} {v : ↥(Spa A A⁺)}
    (hv : v ∈ V) : ∃ i : RationalIndex V,
      (v : Spv A) ∈ (rationalOpen i.D.T i.D.s ∩ Spa A A⁺ : Set (Spv A)) := by
  obtain ⟨D, hDrat, hvD, hDV⟩ := exists_isRational_spaOpen_subset_huber V.2 hv
  exact ⟨⟨D, hDrat, hDV⟩, hvD, v.2⟩

/-- **The valuation of a point on the sections over any open neighbourhood**:
pull the point valuation of a rational neighbourhood back along the rational
evaluation. Independence of the choice is `comap_limitEvalHom_pointValue`. -/
noncomputable def openValue (V : Opens ↥(Spa A A⁺)) {v : ↥(Spa A A⁺)}
    (hv : v ∈ V) : Spv ↥(limitSections V) :=
  comap (limitEvalHom (exists_rationalIndex_mem hv).choose)
    (pointValue _ (exists_rationalIndex_mem hv).choose_spec)

/-- Evaluation-restriction compatibility: restricting a compatible family and
evaluating is evaluating (the defining property of the limit). -/
theorem restrictionMapHom_comp_limitEvalHom {V : Opens ↥(Spa A A⁺)}
    (i k : RationalIndex V)
    (h : rationalOpen k.D.T k.D.s ⊆ rationalOpen i.D.T i.D.s) :
    (restrictionMapHom i.D k.D h).comp (limitEvalHom i) = limitEvalHom k :=
  RingHom.ext fun x => x.2 i k h

/-- **Choice independence**: any rational index containing the point computes
`openValue`. -/
theorem comap_limitEvalHom_pointValue {V : Opens ↥(Spa A A⁺)}
    {v : ↥(Spa A A⁺)} (hv : v ∈ V) (i : RationalIndex V)
    (hvi : (v : Spv A) ∈ (rationalOpen i.D.T i.D.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap (limitEvalHom i) (pointValue i.D hvi) = openValue V hv := by
  set j := (exists_rationalIndex_mem hv).choose with hjdef
  have hj := (exists_rationalIndex_mem hv).choose_spec
  -- refine at `v` inside the open intersection of the two rational opens
  obtain ⟨E, hErat, hvE, hEsub⟩ := exists_isRational_spaOpen_subset_huber
    (IsOpen.inter (isOpen_spaOpen i.D) (isOpen_spaOpen j.D))
    (Set.mem_inter (mem_spaOpen.mpr hvi.1) (mem_spaOpen.mpr hj.1))
  have hEi : rationalOpen E.T E.s ⊆ rationalOpen i.D.T i.D.s :=
    spaOpen_subset_iff.mp (hEsub.trans Set.inter_subset_left)
  have hEj : rationalOpen E.T E.s ⊆ rationalOpen j.D.T j.D.s :=
    spaOpen_subset_iff.mp (hEsub.trans Set.inter_subset_right)
  have hvE' : (v : Spv A) ∈ (rationalOpen E.T E.s ∩ Spa A A⁺ : Set (Spv A)) :=
    ⟨mem_spaOpen.mp hvE, v.2⟩
  have key : ∀ (l : RationalIndex V)
      (hvl : (v : Spv A) ∈ (rationalOpen l.D.T l.D.s ∩ Spa A A⁺ : Set (Spv A)))
      (hEl : rationalOpen E.T E.s ⊆ rationalOpen l.D.T l.D.s),
      comap (limitEvalHom l) (pointValue l.D hvl)
        = comap (limitEvalHom
            (⟨E, hErat, (hEsub.trans Set.inter_subset_left).trans i.subset⟩
              : RationalIndex V))
          (pointValue E hvE') := by
    intro l hvl hEl
    have hS2 := comap_restrictionMapHom_pointValue l.D E hEl hvE'
    have hpv : pointValue l.D hvl
        = comap (restrictionMapHom l.D E hEl) (pointValue E hvE') := by
      rw [hS2]
    rw [hpv]
    rw [show comap (limitEvalHom l)
        (comap (restrictionMapHom l.D E hEl) (pointValue E hvE'))
      = comap ((restrictionMapHom l.D E hEl).comp (limitEvalHom l))
          (pointValue E hvE') from by rw [comap_comp]; rfl]
    rw [restrictionMapHom_comp_limitEvalHom l
      ⟨E, hErat, (hEsub.trans Set.inter_subset_left).trans i.subset⟩ hEl]
  rw [key i hvi hEi, ← key j hj hEj]
  rfl

/-- **Restriction coherence**: the point's valuation is intertwined by the
presheaf restrictions. -/
theorem comap_limitRestrict_openValue {V W : Opens ↥(Spa A A⁺)} (h : W ≤ V)
    {v : ↥(Spa A A⁺)} (hvW : v ∈ W) :
    comap (limitRestrict h) (openValue W hvW) = openValue V (h hvW) := by
  set k := (exists_rationalIndex_mem hvW).choose with hkdef
  have hk := (exists_rationalIndex_mem hvW).choose_spec
  have h1 : openValue W hvW = comap (limitEvalHom k) (pointValue k.D hk) := rfl
  rw [h1]
  rw [show comap (limitRestrict h) (comap (limitEvalHom k) (pointValue k.D hk))
      = comap ((limitEvalHom k).comp (limitRestrict h)) (pointValue k.D hk)
    from by rw [comap_comp]; rfl]
  rw [show (limitEvalHom k).comp (limitRestrict h)
      = limitEvalHom (k.mono h) from RingHom.ext fun x => rfl]
  exact comap_limitEvalHom_pointValue (h hvW) (k.mono h) hk

/-- The `vle`-relation of the point is restriction-invariant. -/
theorem openValue_vle_restrict {V W : Opens ↥(Spa A A⁺)} (h : W ≤ V)
    {v : ↥(Spa A A⁺)} (hvW : v ∈ W) (f g : ↥(limitSections V)) :
    (openValue V (h hvW)).vle f g
      ↔ (openValue W hvW).vle (limitRestrict h f) (limitRestrict h g) := by
  rw [← comap_limitRestrict_openValue h hvW, comap_vle]

end OpenValue


/-! ### The stalk valuation (S3b, Wedhorn 8.14 substrate)

The germ relation on the ring stalk of the structure presheaf is a valuative
relation; the resulting point `stalkValue v` of `Spv` pulls back to
`openValue` along every germ map. -/

section StalkValue

open TopologicalSpace CategoryTheory TopCat

variable [IsRingOfIntegralElements (A⁺ : Subring A)]
  [HasLocLiftPowerBounded A]

noncomputable local instance : DecidableEq A := Classical.decEq _

variable (A) in
/-- The underlying `CommRingCat`-presheaf of the structure presheaf. -/
abbrev spaRingPresheaf : TopCat.Presheaf CommRingCat.{u} (SpaTop A) :=
  structurePresheaf A ⋙ CompleteTopCommRingCat.forgetToCommRingCat

/-- Germs commute with restriction (the `limitRestrict` form). -/
theorem germ_limitRestrict {V W : Opens ↥(Spa A A⁺)} (h : W ≤ V)
    {v : ↥(Spa A A⁺)} (hvW : v ∈ W) (f : ↥(limitSections V)) :
    (spaRingPresheaf A).germ W v hvW (limitRestrict h f)
      = (spaRingPresheaf A).germ V v (h hvW) f := by
  have hres := TopCat.Presheaf.germ_res_apply (spaRingPresheaf A)
    (homOfLE h) v hvW f
  rw [← hres]
  rfl

/-- **The stalk relation**: two stalk elements compare if some common
representatives over a neighbourhood compare under the point's valuation. -/
def stalkVle (v : ↥(Spa A A⁺))
    (a b : ToType ((spaRingPresheaf A).stalk v)) : Prop :=
  ∃ (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) (f g : ↥(limitSections U)),
    (spaRingPresheaf A).germ U v hvU f = a
    ∧ (spaRingPresheaf A).germ U v hvU g = b
    ∧ (openValue U hvU).vle f g

/-- Any two stalk elements admit common representatives. -/
theorem exists_common_rep (v : ↥(Spa A A⁺))
    (a b : ToType ((spaRingPresheaf A).stalk v)) :
    ∃ (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) (f g : ↥(limitSections U)),
      (spaRingPresheaf A).germ U v hvU f = a
      ∧ (spaRingPresheaf A).germ U v hvU g = b := by
  obtain ⟨U₁, h₁, f, rfl⟩ := (spaRingPresheaf A).exists_germ_eq a
  obtain ⟨U₂, h₂, g, rfl⟩ := (spaRingPresheaf A).exists_germ_eq b
  refine ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩, limitRestrict inf_le_left f,
    limitRestrict inf_le_right g, ?_, ?_⟩
  · exact germ_limitRestrict inf_le_left ⟨h₁, h₂⟩ f
  · exact germ_limitRestrict inf_le_right ⟨h₁, h₂⟩ g

/-- **Witness transport**: a `stalkVle`-witness descends to any pair of
representatives after shrinking the neighbourhood. -/
theorem stalkVle_elim {v : ↥(Spa A A⁺)}
    {a b : ToType ((spaRingPresheaf A).stalk v)}
    (hab : stalkVle v a b) {U : Opens ↥(Spa A A⁺)} (hvU : v ∈ U)
    {f g : ↥(limitSections U)}
    (hf : (spaRingPresheaf A).germ U v hvU f = a)
    (hg : (spaRingPresheaf A).germ U v hvU g = b) :
    ∃ (W : Opens ↥(Spa A A⁺)) (hvW : v ∈ W) (hWU : W ≤ U),
      (openValue W hvW).vle (limitRestrict hWU f) (limitRestrict hWU g) := by
  obtain ⟨U', hvU', f', g', hf', hg', hvle⟩ := hab
  obtain ⟨W₁, hvW₁, i₁, i₁', he₁⟩ := TopCat.Presheaf.germ_eq
    (spaRingPresheaf A) v hvU hvU' f f' (hf.trans hf'.symm)
  obtain ⟨W₂, hvW₂, i₂, i₂', he₂⟩ := TopCat.Presheaf.germ_eq
    (spaRingPresheaf A) v hvU hvU' g g' (hg.trans hg'.symm)
  have hWU : W₁ ⊓ W₂ ≤ U := inf_le_left.trans (leOfHom i₁)
  have hWU' : W₁ ⊓ W₂ ≤ U' := inf_le_left.trans (leOfHom i₁')
  refine ⟨W₁ ⊓ W₂, ⟨hvW₁, hvW₂⟩, hWU, ?_⟩
  have hres₁ : limitRestrict hWU f = limitRestrict hWU' f' := by
    have h1 := congrArg
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) he₁
    exact h1
  have hres₂ : limitRestrict hWU g = limitRestrict hWU' g' := by
    have h2 := congrArg
      (limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) he₂
    exact h2
  have hfinal := (openValue_vle_restrict hWU' ⟨hvW₁, hvW₂⟩ f' g').mp hvle
  rw [← hres₁, ← hres₂] at hfinal
  exact hfinal

theorem stalkVle_intro {v : ↥(Spa A A⁺)} {U : Opens ↥(Spa A A⁺)}
    {hvU : v ∈ U} {f g : ↥(limitSections U)}
    (h : (openValue U hvU).vle f g) :
    stalkVle v ((spaRingPresheaf A).germ U v hvU f)
      ((spaRingPresheaf A).germ U v hvU g) :=
  ⟨U, hvU, f, g, rfl, rfl, h⟩

theorem germ_add {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U)
    (f g : ↥(limitSections U)) :
    (spaRingPresheaf A).germ U v hvU (f + g)
      = (spaRingPresheaf A).germ U v hvU f
        + (spaRingPresheaf A).germ U v hvU g :=
  map_add ((spaRingPresheaf A).germ U v hvU).hom f g

theorem germ_mul {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U)
    (f g : ↥(limitSections U)) :
    (spaRingPresheaf A).germ U v hvU (f * g)
      = (spaRingPresheaf A).germ U v hvU f
        * (spaRingPresheaf A).germ U v hvU g :=
  map_mul ((spaRingPresheaf A).germ U v hvU).hom f g

theorem germ_one {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) :
    (spaRingPresheaf A).germ U v hvU 1 = 1 :=
  map_one ((spaRingPresheaf A).germ U v hvU).hom

theorem germ_zero {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) :
    (spaRingPresheaf A).germ U v hvU 0 = 0 :=
  map_zero ((spaRingPresheaf A).germ U v hvU).hom

theorem stalkVle_total (v : ↥(Spa A A⁺))
    (a b : ToType ((spaRingPresheaf A).stalk v)) :
    stalkVle v a b ∨ stalkVle v b a := by
  obtain ⟨U, hvU, f, g, hf, hg⟩ := exists_common_rep v a b
  rcases (openValue U hvU).vle_total f g with h | h
  · exact Or.inl (hf ▸ hg ▸ stalkVle_intro h)
  · exact Or.inr (hg ▸ hf ▸ stalkVle_intro h)

theorem stalkVle_add {v : ↥(Spa A A⁺)}
    {x y z : ToType ((spaRingPresheaf A).stalk v)}
    (hxz : stalkVle v x z) (hyz : stalkVle v y z) :
    stalkVle v (x + y) z := by
  obtain ⟨U₁, h₁, fx, fy, hfx, hfy⟩ := exists_common_rep v x y
  obtain ⟨U₂, h₂, fz, rfl⟩ := (spaRingPresheaf A).exists_germ_eq z
  have hvU : v ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hfx' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx) = x :=
    (germ_limitRestrict inf_le_left hvU fx).trans hfx
  have hfy' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy) = y :=
    (germ_limitRestrict inf_le_left hvU fy).trans hfy
  have hfz' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_right fz)
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    germ_limitRestrict inf_le_right hvU fz
  obtain ⟨W₁, hvW₁, hW₁, hv1⟩ := stalkVle_elim hxz hvU hfx' hfz'
  obtain ⟨W₂, hvW₂, hW₂, hv2⟩ := stalkVle_elim hyz hvU hfy' hfz'
  have hvW : v ∈ W₁ ⊓ W₂ := ⟨hvW₁, hvW₂⟩
  have hd1 := (openValue_vle_restrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁) hvW _ _).mp hv1
  have hd2 := (openValue_vle_restrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂) hvW _ _).mp hv2
  -- the two z-restrictions agree (proof-irrelevant restriction paths)
  have hzz : limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
      (limitRestrict hW₂ (limitRestrict inf_le_right fz))
      = limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_right fz)) := rfl
  rw [hzz] at hd2
  have hadd := (openValue (W₁ ⊓ W₂) hvW).vle_add hd1 hd2
  have hfin := stalkVle_intro (v := v) hadd
  have hgx : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_left fx))) = x :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₁ _).trans hfx')
  have hgy : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
        (limitRestrict hW₂ (limitRestrict inf_le_left fy))) = y :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₂ _).trans hfy')
  have hgz : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_right fz)))
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₁ _).trans hfz')
  have hsum : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
          (limitRestrict hW₁ (limitRestrict inf_le_left fx))
        + limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
          (limitRestrict hW₂ (limitRestrict inf_le_left fy))) = x + y :=
    (germ_add _ hvW _ _).trans (congrArg₂ (· + ·) hgx hgy)
  exact hsum ▸ hgz ▸ hfin

theorem stalkVle_mul_left {v : ↥(Spa A A⁺)}
    {x y : ToType ((spaRingPresheaf A).stalk v)}
    (h : stalkVle v x y) (z : ToType ((spaRingPresheaf A).stalk v)) :
    stalkVle v (x * z) (y * z) := by
  obtain ⟨U₁, h₁, fx, fy, hfx, hfy⟩ := exists_common_rep v x y
  obtain ⟨U₂, h₂, fz, rfl⟩ := (spaRingPresheaf A).exists_germ_eq z
  have hvU : v ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hfx' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx) = x :=
    (germ_limitRestrict inf_le_left hvU fx).trans hfx
  have hfy' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy) = y :=
    (germ_limitRestrict inf_le_left hvU fy).trans hfy
  obtain ⟨W, hvW, hW, hv1⟩ := stalkVle_elim h hvU hfx' hfy'
  have hmul := (openValue W hvW).mul_vle_mul_left hv1
    (limitRestrict hW (limitRestrict inf_le_right fz))
  have hfin := stalkVle_intro (v := v) hmul
  have hgz : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_right fz))
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_limitRestrict _ hvW _).trans (germ_limitRestrict _ hvU _)
  have hprodx : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fx)
        * limitRestrict hW (limitRestrict inf_le_right fz))
      = x * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvW _ _).trans (congrArg₂ (· * ·)
      ((germ_limitRestrict _ hvW _).trans hfx') hgz)
  have hprody : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fy)
        * limitRestrict hW (limitRestrict inf_le_right fz))
      = y * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvW _ _).trans (congrArg₂ (· * ·)
      ((germ_limitRestrict _ hvW _).trans hfy') hgz)
  exact hprodx ▸ hprody ▸ hfin

theorem stalkVle_mul_comm {v : ↥(Spa A A⁺)}
    {x y : ToType ((spaRingPresheaf A).stalk v)} :
    stalkVle v (x * y) (y * x) := by
  obtain ⟨U, hvU, f, g, hf, hg⟩ := exists_common_rep v x y
  have h := (openValue U hvU).vle_mul_comm (x := f) (y := g)
  have hfin := stalkVle_intro (v := v) h
  have h1 : (spaRingPresheaf A).germ U v hvU (f * g) = x * y :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hf hg)
  have h2 : (spaRingPresheaf A).germ U v hvU (g * f) = y * x :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hg hf)
  exact h1 ▸ h2 ▸ hfin

theorem not_stalkVle_one_zero (v : ↥(Spa A A⁺)) :
    ¬ stalkVle v (1 : ToType ((spaRingPresheaf A).stalk v)) 0 := by
  intro hcon
  have h1 : (spaRingPresheaf A).germ ⊤ v (TopologicalSpace.Opens.mem_top v)
      (1 : ↥(limitSections ⊤)) = 1 := germ_one ⊤ (TopologicalSpace.Opens.mem_top v)
  have h0 : (spaRingPresheaf A).germ ⊤ v (TopologicalSpace.Opens.mem_top v)
      (0 : ↥(limitSections ⊤)) = 0 := germ_zero ⊤ (TopologicalSpace.Opens.mem_top v)
  obtain ⟨W, hvW, hWU, hres⟩ := stalkVle_elim hcon (TopologicalSpace.Opens.mem_top v) h1 h0
  have hone : limitRestrict hWU (1 : ↥(limitSections ⊤)) = 1 := map_one _
  have hzero : limitRestrict hWU (0 : ↥(limitSections ⊤)) = 0 := map_zero _
  rw [hone, hzero] at hres
  exact (openValue W hvW).not_vle_one_zero hres

theorem stalkVle_trans {v : ↥(Spa A A⁺)}
    {c b a : ToType ((spaRingPresheaf A).stalk v)}
    (hab : stalkVle v a b) (hbc : stalkVle v b c) : stalkVle v a c := by
  obtain ⟨U, hvU, f, g, hfa, hgb⟩ := exists_common_rep v a b
  obtain ⟨U', hvU', g', h', hgb', hhc⟩ := exists_common_rep v b c
  have hvU0 : v ∈ U ⊓ U' := ⟨hvU, hvU'⟩
  have ha0 : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_left f) = a :=
    (germ_limitRestrict _ hvU0 _).trans hfa
  have hb0 : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_left g) = b :=
    (germ_limitRestrict _ hvU0 _).trans hgb
  have hb0' : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_right g') = b :=
    (germ_limitRestrict _ hvU0 _).trans hgb'
  have hc0 : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_right h') = c :=
    (germ_limitRestrict _ hvU0 _).trans hhc
  obtain ⟨W₁, hvW₁, hW₁, hv1⟩ := stalkVle_elim hab hvU0 ha0 hb0
  obtain ⟨W₂, hvW₂, hW₂, hv2⟩ := stalkVle_elim hbc hvU0 hb0' hc0
  obtain ⟨W₃, hvW₃, i₃, i₃', he₃⟩ := TopCat.Presheaf.germ_eq
    (spaRingPresheaf A) v hvU0 hvU0 (limitRestrict inf_le_left g)
    (limitRestrict inf_le_right g') (hb0.trans hb0'.symm)
  have hvW : v ∈ W₁ ⊓ W₂ ⊓ W₃ := ⟨⟨hvW₁, hvW₂⟩, hvW₃⟩
  have hda := (openValue_vle_restrict
    ((inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁)) hvW _ _).mp hv1
  have hdc := (openValue_vle_restrict
    ((inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂)) hvW _ _).mp hv2
  have hbb : limitRestrict (inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁)
      (limitRestrict hW₁ (limitRestrict inf_le_left g))
      = limitRestrict (inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂)
        (limitRestrict hW₂ (limitRestrict inf_le_right g')) := by
    have h3 := congrArg
      (limitRestrict (inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₃)) he₃
    exact h3
  rw [hbb] at hda
  have htr := (openValue (W₁ ⊓ W₂ ⊓ W₃) hvW).vle_trans hda hdc
  have hfin := stalkVle_intro (v := v) htr
  have hga : (spaRingPresheaf A).germ (W₁ ⊓ W₂ ⊓ W₃) v hvW
      (limitRestrict (inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_left f))) = a :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₁ _).trans ha0)
  have hgc : (spaRingPresheaf A).germ (W₁ ⊓ W₂ ⊓ W₃) v hvW
      (limitRestrict (inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂)
        (limitRestrict hW₂ (limitRestrict inf_le_right h'))) = c :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₂ _).trans hc0)
  exact hga ▸ hgc ▸ hfin

theorem stalkVle_mul_cancel {v : ↥(Spa A A⁺)}
    {x y z : ToType ((spaRingPresheaf A).stalk v)}
    (hz : ¬ stalkVle v z 0) (hmul : stalkVle v (x * z) (y * z)) :
    stalkVle v x y := by
  obtain ⟨U₁, h₁, fx, fy, hfx, hfy⟩ := exists_common_rep v x y
  obtain ⟨U₂, h₂, fz, rfl⟩ := (spaRingPresheaf A).exists_germ_eq z
  have hvU : v ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hfx' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx) = x :=
    (germ_limitRestrict _ hvU _).trans hfx
  have hfy' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy) = y :=
    (germ_limitRestrict _ hvU _).trans hfy
  have hfz' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_right fz)
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    germ_limitRestrict _ hvU _
  have hxz : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx * limitRestrict inf_le_right fz)
      = x * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hfx' hfz')
  have hyz : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy * limitRestrict inf_le_right fz)
      = y * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hfy' hfz')
  obtain ⟨W, hvW, hW, hres⟩ := stalkVle_elim hmul hvU hxz hyz
  have hznz : ¬ (openValue W hvW).vle
      (limitRestrict hW (limitRestrict inf_le_right fz)) 0 := by
    intro hcon
    refine hz ⟨W, hvW, limitRestrict hW (limitRestrict inf_le_right fz), 0,
      ?_, germ_zero W hvW, hcon⟩
    exact (germ_limitRestrict _ hvW _).trans hfz'
  have hres' : (openValue W hvW).vle
      (limitRestrict hW (limitRestrict inf_le_left fx)
        * limitRestrict hW (limitRestrict inf_le_right fz))
      (limitRestrict hW (limitRestrict inf_le_left fy)
        * limitRestrict hW (limitRestrict inf_le_right fz)) := hres
  have hcanc := (openValue W hvW).vle_mul_cancel hznz hres'
  have hfin := stalkVle_intro (v := v) hcanc
  have hgx : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fx)) = x :=
    (germ_limitRestrict _ hvW _).trans hfx'
  have hgy : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fy)) = y :=
    (germ_limitRestrict _ hvW _).trans hfy'
  exact hgx ▸ hgy ▸ hfin

/-- **The stalk `ValuativeRel`** (Wedhorn 8.14 substrate): the germ relation
is a valuative relation on the ring stalk. -/
noncomputable def stalkValuativeRel (v : ↥(Spa A A⁺)) :
    ValuativeRel (ToType ((spaRingPresheaf A).stalk v)) where
  vle := stalkVle v
  vle_total := stalkVle_total v
  vle_trans := stalkVle_trans
  vle_add := stalkVle_add
  mul_vle_mul_left := stalkVle_mul_left
  vle_mul_cancel := stalkVle_mul_cancel
  not_vle_one_zero := not_stalkVle_one_zero v
  vle_mul_comm := fun {_x _y} => stalkVle_mul_comm

/-- **The valuation of the point on the stalk** of the structure presheaf. -/
noncomputable def stalkValue (v : ↥(Spa A A⁺)) :
    Spv (ToType ((spaRingPresheaf A).stalk v)) :=
  ⟨stalkValuativeRel v⟩

/-- The stalk valuation pulls back to the point's valuation on the sections
over any open neighbourhood. -/
theorem comap_germ_stalkValue {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺))
    (hvU : v ∈ U) :
    comap ((spaRingPresheaf A).germ U v hvU).hom (stalkValue v)
      = openValue U hvU := by
  refine ValuationSpectrum.ext (funext₂ fun f g => propext ?_)
  constructor
  · intro h
    obtain ⟨W, hvW, hWU, hres⟩ := stalkVle_elim h hvU rfl rfl
    exact (openValue_vle_restrict hWU hvW f g).mpr hres
  · intro h
    exact stalkVle_intro h

/-! ### Locality of the stalk (S4: Wedhorn 8.14, reduced to the shrink claim) -/

/-- A stalk unit has nonzero stalk value. -/
theorem not_stalkValue_vle_zero_of_isUnit {v : ↥(Spa A A⁺)}
    {x : ToType ((spaRingPresheaf A).stalk v)} (hx : IsUnit x) :
    ¬ (stalkValue v).vle x 0 := by
  intro h
  obtain ⟨u, rfl⟩ := hx
  have h1 := (stalkValue v).mul_vle_mul_left h ((u⁻¹ : _ˣ) : _)
  rw [Units.mul_inv, zero_mul] at h1
  exact (stalkValue v).not_vle_one_zero h1

/-- The germ of a section that is a unit is a stalk unit. -/
theorem isUnit_germ_of_isUnit {v : ↥(Spa A A⁺)} {U : Opens ↥(Spa A A⁺)}
    (hvU : v ∈ U) {f : ↥(limitSections U)} (hf : IsUnit f) :
    IsUnit ((spaRingPresheaf A).germ U v hvU f) :=
  hf.map ((spaRingPresheaf A).germ U v hvU).hom

/-- The stalk is nontrivial. -/
theorem stalk_nontrivial (v : ↥(Spa A A⁺)) :
    Nontrivial (ToType ((spaRingPresheaf A).stalk v)) := by
  refine ⟨1, 0, fun h => ?_⟩
  refine (stalkValue v).not_vle_one_zero ?_
  rw [h]
  rcases (stalkValue v).vle_total 0 0 with h0 | h0 <;> exact h0

/-- **The shrink claim** (the hard half of Wedhorn 8.14, discharged in the
S4-core step): every stalk element of nonzero value is a unit. -/
def StalkShrink (v : ↥(Spa A A⁺)) : Prop :=
  ∀ x : ToType ((spaRingPresheaf A).stalk v),
    ¬ (stalkValue v).vle x 0 → IsUnit x

/-- Under the shrink claim, units are exactly the elements of nonzero value. -/
theorem isUnit_iff_not_vle_zero {v : ↥(Spa A A⁺)} (hs : StalkShrink v)
    (x : ToType ((spaRingPresheaf A).stalk v)) :
    IsUnit x ↔ ¬ (stalkValue v).vle x 0 :=
  ⟨not_stalkValue_vle_zero_of_isUnit, hs x⟩

/-- Under the shrink claim, the nonunits are the support of the stalk
valuation. -/
theorem mem_nonunits_iff_vle_zero {v : ↥(Spa A A⁺)} (hs : StalkShrink v)
    (x : ToType ((spaRingPresheaf A).stalk v)) :
    x ∈ nonunits (ToType ((spaRingPresheaf A).stalk v))
      ↔ x ∈ (stalkValue v).supp := by
  rw [mem_supp_iff, mem_nonunits_iff, isUnit_iff_not_vle_zero hs x, not_not]

/-- **Wedhorn 8.14, packaged**: under the shrink claim the stalk is a local
ring. -/
theorem isLocalRing_stalk_of_shrink {v : ↥(Spa A A⁺)} (hs : StalkShrink v) :
    IsLocalRing (ToType ((spaRingPresheaf A).stalk v)) := by
  haveI := stalk_nontrivial v
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff_vle_zero hs] at ha hb ⊢
  rw [mem_supp_iff] at ha hb ⊢
  exact (stalkValue v).vle_add ha hb

/-- Under the shrink claim, the maximal ideal is the support of the stalk
valuation (the `val_supp` field of the `VPreObj` packaging). -/
theorem maximalIdeal_stalk_eq_supp {v : ↥(Spa A A⁺)} (hs : StalkShrink v) :
    @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk_of_shrink hs)
      = (stalkValue v).supp := by
  refine Ideal.ext fun x => ?_
  rw [@IsLocalRing.mem_maximalIdeal _ _ (isLocalRing_stalk_of_shrink hs)]
  exact mem_nonunits_iff_vle_zero hs x

/-! ### Reduction of the shrink claim to the rational level -/

variable (A) in
/-- **The rational shrink claim** (the rational-level core of Wedhorn 8.14):
an element of a completed rational localization with nonzero point value
becomes a unit on a smaller valid rational neighbourhood of the point. -/
def RationalShrink : Prop :=
  ∀ (D : RationalLocData A) (_hD : D.IsRational) (v' : Spv A)
    (hv : v' ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
    (b : presheafValue D), ¬ (pointValue D hv).vle b 0 →
    ∃ (D' : RationalLocData A) (_hD' : D'.IsRational)
      (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s),
      v' ∈ rationalOpen D'.T D'.s ∧ IsUnit (restrictionMapHom D D' h b)

/-- **Reduction of the stalk shrink claim to the rational one**: representing
a nonzero-value germ over a rational neighbourhood, shrinking by
`RationalShrink`, and transporting the unit through the rational-open
comparison `limitEval`. -/
theorem stalkShrink_of_rationalShrink (hRS : RationalShrink A)
    (v : ↥(Spa A A⁺)) : StalkShrink v := by
  intro x hx
  obtain ⟨U, hvU, f, rfl⟩ := (spaRingPresheaf A).exists_germ_eq x
  -- the section has nonzero value
  have hnz : ¬ (openValue U hvU).vle f 0 := by
    intro hcon
    refine hx ⟨U, hvU, f, 0, rfl, germ_zero U hvU, hcon⟩
  -- compute at the defining rational index
  set i := (exists_rationalIndex_mem hvU).choose with hidef
  have hi := (exists_rationalIndex_mem hvU).choose_spec
  have hnzD : ¬ (pointValue i.D hi).vle (limitEvalHom i f) 0 :=
    fun hcon => hnz hcon
  -- rational shrink
  obtain ⟨D', hD', hsub, hvD', hunit⟩ := hRS i.D i.isRational
    (v : Spv A) hi (limitEvalHom i f) hnzD
  -- the smaller rational open, as an open of the subtype
  have hW'U : spaOpens D' ≤ U :=
    (spaOpen_subset_of_rationalOpen_subset hsub).trans i.subset
  have hvW' : v ∈ spaOpens D' := mem_spaOpen.mpr hvD'
  -- the restricted section is a unit via the rational-open comparison
  have hcomp : limitEval hD' (limitRestrict hW'U f)
      = restrictionMapHom i.D D' hsub (limitEvalHom i f) :=
    (f.2 i ((RationalIndex.self D' hD').mono hW'U) hsub).symm
  have hfunit : IsUnit (limitRestrict hW'U f) := by
    have h1 : IsUnit (limitEval hD' (limitRestrict hW'U f)) := by
      rw [hcomp]
      exact hunit
    have h2 := h1.map (limitEval hD').symm.toRingHom
    rwa [show (limitEval hD').symm.toRingHom (limitEval hD'
        (limitRestrict hW'U f)) = limitRestrict hW'U f from
      (limitEval hD').symm_apply_apply _] at h2
  have hgerm : (spaRingPresheaf A).germ (spaOpens D') v hvW'
      (limitRestrict hW'U f) = (spaRingPresheaf A).germ U v hvU f :=
    germ_limitRestrict hW'U hvW' f
  rw [← hgerm]
  exact isUnit_germ_of_isUnit hvW' hfunit

end StalkValue


/-! ### The shrink claim holds (Wedhorn 8.14, unconditional) -/

section ShrinkHolds

open TopologicalSpace CategoryTheory TopCat

variable [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A]

noncomputable local instance : DecidableEq A := Classical.decEq _

/-- **The rational shrink claim holds** (Wedhorn 8.14, the substantive step):
an element `b` of a completed rational localization with nonzero point value
becomes a unit on a smaller valid rational neighbourhood. The proof scales `b`
to `c := u^{-k}·b` of value `≥ 1` (cofinality of the topologically nilpotent
unit), captures the condition `|1| ≤ |c| ≠ 0` on a base open via
`exists_A_level_open_presentation`, shrinks to a valid rational `D'` inside,
and detects the unit by Wedhorn 7.52(2) at `presheafValue D'` — every
Spa-point of the smaller value pulls back (plus functoriality) to a captured
point, so `b` is nonvanishing there. -/
theorem rationalShrink_holds : RationalShrink A := by
  intro D hD v' hv b hnz
  haveI hTate : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  have hwspa := pointValue_mem_spa D hv
  have hwcont := pointValue_isContinuous D hv
  obtain ⟨u, hu⟩ := presheafValue_topNilUnit D
  obtain ⟨k, hk⟩ := exists_pow_vle_of_isContinuous hwcont hu hnz
  set c : presheafValue D := ((u⁻¹ : _ˣ) : presheafValue D) ^ k * b with hcdef
  have h1c : (pointValue D hv).vle 1 c := by
    have h1 := (pointValue D hv).mul_vle_mul_left hk (((u⁻¹ : _ˣ) : presheafValue D) ^ k)
    rw [show ((u : presheafValue D) ^ k * ((u⁻¹ : _ˣ) : presheafValue D) ^ k) = 1 from by
        rw [← mul_pow, Units.mul_inv, one_pow],
      show b * ((u⁻¹ : _ˣ) : presheafValue D) ^ k = c from by
        rw [hcdef]; ring] at h1
    exact h1
  have hc0 : ¬ (pointValue D hv).vle c 0 := by
    intro hcon
    refine hnz ?_
    have h2 := (pointValue D hv).mul_vle_mul_left hcon ((u : presheafValue D) ^ k)
    rw [zero_mul, show c * (u : presheafValue D) ^ k = b from by
      rw [hcdef, mul_comm _ b, mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]] at h2
    exact h2
  obtain ⟨W, hWopen, hvW, hcapture⟩ := exists_A_level_open_presentation D
    hwspa (ι := Unit) (fam := {()}) (F := fun _ => (1 : presheafValue D))
    (G := fun _ => c) (fun i _ => ⟨h1c, hc0⟩)
  rw [comap_pointValue D hv] at hvW
  obtain ⟨D', hD', hvD', hD'sub⟩ := exists_isRational_spaOpen_subset
    (V := Subtype.val ⁻¹' W ∩ spaOpen D)
    (IsOpen.inter (hWopen.preimage continuous_subtype_val) (isOpen_spaOpen D))
    (v := ⟨v', hv.2⟩) ⟨hvW, mem_spaOpen.mpr hv.1⟩
  have hsub : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s :=
    spaOpen_subset_iff.mp (hD'sub.trans Set.inter_subset_right)
  refine ⟨D', hD', hsub, mem_spaOpen.mp hvD', ?_⟩
  haveI hTate' : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
  haveI : IsHuberRing (presheafValue D') := presheafValue_isHuberRing_huber D'
  letI P_B : PairOfDefinition (presheafValue D') := presheafValue_concretePair D'
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete D'
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B]
  intro w'' hw'' hcon
  have hwPD := comap_restrictionMapHom_mem_spa D D' hsub hw''
  have hbase' := comap_canonicalMap_mem_rationalOpen_inter_spa D' ⟨w'', hw''⟩
  have hbaseEq : comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'')
      = comap D'.canonicalMap w'' := by
    rw [show comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'')
        = comap ((restrictionMapHom D D' hsub).comp D.canonicalMap) w'' from
      by rw [comap_comp]; rfl]
    have hcomp : (restrictionMapHom D D' hsub).comp D.canonicalMap = D'.canonicalMap :=
      RingHom.ext (restrictionMapHom_canonicalMap_generic D D' hsub)
    rw [hcomp]
  have hW' : comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'') ∈ W := by
    rw [hbaseEq]
    exact (hD'sub (show (⟨comap D'.canonicalMap w'', hbase'.2⟩
      : ↥(Spa A A⁺)) ∈ spaOpen D' from hbase'.1)).1
  have hcap := hcapture (comap (restrictionMapHom D D' hsub) w'') hwPD hW'
    () (Finset.mem_singleton_self ())
  -- transport `vle (σ b) 0` to `vle c 0` at the pulled-back point
  refine hcap.2 ?_
  show (comap (restrictionMapHom D D' hsub) w'').vle c 0
  have hcb : (comap (restrictionMapHom D D' hsub) w'').vle b 0 := by
    show w''.vle (restrictionMapHom D D' hsub b) (restrictionMapHom D D' hsub 0)
    rw [map_zero]
    exact hcon
  have h3 := (comap (restrictionMapHom D D' hsub) w'').mul_vle_mul_left hcb
    (((u⁻¹ : _ˣ) : presheafValue D) ^ k)
  rw [zero_mul, show b * ((u⁻¹ : _ˣ) : presheafValue D) ^ k = c from by
    rw [hcdef]; ring] at h3
  exact h3

/-- **The stalk shrink claim holds.** -/
theorem stalkShrink_holds (v : ↥(Spa A A⁺)) : StalkShrink v :=
  stalkShrink_of_rationalShrink rationalShrink_holds v

/-- **Wedhorn 8.14, unconditional**: the stalk of the structure presheaf at
any point of `Spa (A, A⁺)` is a local ring. -/
theorem isLocalRing_stalk (v : ↥(Spa A A⁺)) :
    IsLocalRing (ToType ((spaRingPresheaf A).stalk v)) :=
  isLocalRing_stalk_of_shrink (stalkShrink_holds v)

/-- **Wedhorn 8.14, the maximal ideal**: it is the support of the stalk
valuation. -/
theorem maximalIdeal_stalk (v : ↥(Spa A A⁺)) :
    @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk v)
      = (stalkValue v).supp :=
  maximalIdeal_stalk_eq_supp (stalkShrink_holds v)

/-! ### S5: `Spa` as the first object of Wedhorn's category `𝒱` -/

section SpaVObj

variable (A)

/-- **`Spa (A, A⁺)` as a presheafed space of complete topological rings.** -/
noncomputable def spaPresheafedSpace : TopRingPresheafedSpace.{u} where
  carrier := SpaTop A
  presheaf := structurePresheaf A

/-- **`Spa (A, A⁺)` as an object of `𝒱^pre`** (Wedhorn Definition 8.5): the
structure presheaf with its local stalks (Wedhorn 8.14) and stalk valuations,
the support being the maximal ideal. The first inhabitant of the category. -/
noncomputable def spaVPreObj : VPreObj.{u} where
  toPresheafedSpace := spaPresheafedSpace A
  isLocalRing_stalk := fun x => isLocalRing_stalk (A := A) x
  val := fun x => stalkValue (A := A) x
  val_supp := fun x => (maximalIdeal_stalk (A := A) x).symm

/-- **`Spa (A, A⁺)` of a sheafy pair as an object of `𝒱`** (Wedhorn Remark
8.20): the structure presheaf is a sheaf of topological rings. -/
noncomputable def spaVObj (h : IsLimitSheaf A) : VObj.{u} where
  toVPreObj := spaVPreObj A
  isSheafTopRings := structurePresheaf_isSheafOfTopologicalRings (A := A) h

/-- The sheafy-pair form. -/
noncomputable def spaVObj_of_isSheafy [IsSheafy A] : VObj.{u} :=
  spaVObj A (isLimitSheaf_of_isSheafy (A := A))

end SpaVObj
end ShrinkHolds

end ValuationSpectrum

end
