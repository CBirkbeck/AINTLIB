/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RestrictedLaurent
import «Adic spaces».JetDualNumberNorm
import «Adic spaces».ExampleUnitDisc

/-!
# The finite-jet pinching square: the rings 𝓐, 𝓑, 𝓒, 𝓓 and the strict Milnor row

Source: [FJP] §1.4–§2 over the base field `K := LaurentSeries F` (complete, discretely
valued — the project's standard witness field). Following [FJP] (1.4):

* `L  = K⟨W, W⁻¹⟩` — `RestrictedLaurent K` (file `RestrictedLaurent.lean`);
* `𝓑 = K⟨W, Q⟩/(Q²)` — realised norm-faithfully as `DualNumber (K⟨W⟩)` (max norm,
  [FJP] Lemma 2.2's quotient-norm computation is definitional in this model);
* `𝓒 = L⟨Q⟩` — `PowerSeries.Restricted (L F) 1` (vendored Gauss stack over base `L`);
* `𝓓 = L⟨Q⟩/(Q²)` — `DualNumber (L F)`;
* `𝓐 = 𝓑 ×_𝓓 𝓒` — **not** a new type: by [FJP] Lemma 2.2 ("Projection to 𝒞 is an isometric
  embedding of 𝒜 with image (1.7)"), 𝓐 is the closed subring of 𝓒 of series whose `Q⁰`- and
  `Q¹`-coefficients have nonnegative `W`-support ([FJP] (1.8): support
  `S = {(a,b) ∈ ℤ × ℕ : b ≤ 1 ⇒ a ≥ 0}`).

The maps ([FJP] (1.5), (5.1)): `ρB : 𝓑 → 𝓓` (componentwise `K⟨W⟩ ↪ L`), `ρC : 𝓒 → 𝓓`
(2-jet truncation, with the norm-one linear section `f₀ + Qf₁ ↦ f₀ + Qf₁`), `ιC : 𝓐 ↪ 𝓒`,
`jB : 𝓐 → 𝓑`. The strict Milnor row ([FJP] Prop 2.1, (2.1b)):
`0 → 𝓐 → 𝓑 ⊕ 𝓒 → 𝓓 → 0` is exact with **all norm constants 1**.

This file also builds the Huber-theoretic instance stack for each ring (pair of definition,
`IsTateRing`, maximal plus ring, `IsRingOfIntegralElements`, completeness w.r.t. the right
uniformity) in the pattern of `ExampleUnitDisc.lean`.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### The four rings -/

/-- `L = K⟨W,W⁻¹⟩`, the radius-one Laurent algebra over `K` ([FJP] (1.4)). -/
abbrev L : Type _ := RestrictedLaurent K

/-- The discrete value group of `K`: every nonzero norm is an integer power of `2`
(the `RankOne` normalisation of `ExampleUnitDisc.lean`). -/
theorem norm_K_discrete : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n := by sorry

/-- `𝓒 = L⟨Q⟩` ([FJP] (1.4)). -/
abbrev JetC : Type _ := PowerSeries.Restricted (L F) (1 : ℝ)

/-- `𝓑 = K⟨W,Q⟩/(Q²)`, modelled as dual numbers over `K⟨W⟩` ([FJP] (1.4) with
Lemma 2.2's isometric max-norm decomposition `k⟨W⟩ ⊕ Q·k⟨W⟩`). -/
abbrev JetB : Type _ := DualNumber (PowerSeries.Restricted K (1 : ℝ))

/-- `𝓓 = L⟨Q⟩/(Q²)`, modelled as dual numbers over `L` ([FJP] (1.4), (2.1d):
`𝓓 = L ⊕ QL` with max norm). -/
abbrev JetD : Type _ := DualNumber (L F)

/-! ### The comparison maps of the square ([FJP] (1.5), (5.1)) -/

/-- The `Q`-coefficient of index `n` of an element of `𝓒`. -/
noncomputable def qCoeff (n : ℕ) (f : JetC F) : L F := PowerSeries.coeff n f.1

/-- `ρC : 𝓒 → 𝓓`, reduction modulo `Q²` = 2-jet truncation ([FJP] (1.5): "the second is
reduction modulo `Q²`"). -/
noncomputable def rhoC : JetC F →+* JetD F where
  toFun f := ⟨qCoeff F 0 f, qCoeff F 1 f⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (1 : JetC F).1 = (1 : JetD F).fst
      rw [show (1 : JetC F).1 = 1 from rfl, TrivSqZeroExt.fst_one, PowerSeries.coeff_zero_one]
    · show PowerSeries.coeff 1 (1 : JetC F).1 = (1 : JetD F).snd
      rw [show (1 : JetC F).1 = 1 from rfl, TrivSqZeroExt.snd_one, PowerSeries.coeff_one,
        if_neg one_ne_zero]
  map_mul' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (f * g : JetC F).1 = _
      rw [show (f * g : JetC F).1 = f.1 * g.1 from rfl, TrivSqZeroExt.fst_mul]
      show _ = qCoeff F 0 f * qCoeff F 0 g
      rw [PowerSeries.coeff_mul]
      simp [qCoeff]
    · show PowerSeries.coeff 1 (f * g : JetC F).1 = _
      rw [show (f * g : JetC F).1 = f.1 * g.1 from rfl, TrivSqZeroExt.snd_mul, smul_eq_mul,
        op_smul_eq_mul]
      show _ = qCoeff F 0 f * qCoeff F 1 g + qCoeff F 1 f * qCoeff F 0 g
      rw [PowerSeries.coeff_mul]
      rw [show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} from rfl]
      rw [Finset.sum_insert (by simp), Finset.sum_singleton]
      rfl
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (0 : JetC F).1 = (0 : JetD F).fst
      rw [show (0 : JetC F).1 = 0 from rfl, TrivSqZeroExt.fst_zero, map_zero]
    · show PowerSeries.coeff 1 (0 : JetC F).1 = (0 : JetD F).snd
      rw [show (0 : JetC F).1 = 0 from rfl, TrivSqZeroExt.snd_zero, map_zero]
  map_add' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (f + g : JetC F).1 = ((⟨_, _⟩ + ⟨_, _⟩ : JetD F)).fst
      rw [show (f + g : JetC F).1 = f.1 + g.1 from rfl, map_add, TrivSqZeroExt.fst_add]
      rfl
    · show PowerSeries.coeff 1 (f + g : JetC F).1 = ((⟨_, _⟩ + ⟨_, _⟩ : JetD F)).snd
      rw [show (f + g : JetC F).1 = f.1 + g.1 from rfl, map_add, TrivSqZeroExt.snd_add]
      rfl

/-- `ρB : 𝓑 → 𝓓`, componentwise restriction from the disc to the annulus ([FJP] (1.5):
"the first is restriction from the `W`-disc to its radius-one boundary"). -/
noncomputable def rhoB : JetB F →+* JetD F :=
  JetNorm.mapHom (ofRestricted (R := K))

/-- The norm-one linear truncation section `𝓓 → 𝓒`, `f₀ + Qf₁ ↦ f₀ + Qf₁`
([FJP] Prop 2.1: "Reduction modulo `Q²` has the norm-preserving linear section
`f₀ + Qf₁ ↦ f₀ + Qf₁`"). -/
noncomputable def sectionD (x : JetD F) : JetC F :=
  ⟨PowerSeries.mk fun n => if n = 0 then x.fst else if n = 1 then x.snd else 0, by
    show PowerSeries.IsRestricted (1 : ℝ) _
    rw [Restricted.isRestricted_iff_cofinite]
    simp only [PowerSeries.coeff_mk, one_pow, mul_one]
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_singleton 0).union (Set.finite_singleton 1)).subset fun n hn => ?_
    rw [Set.mem_setOf_eq] at hn
    by_contra hmem
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hmem
    exact hn (by rw [if_neg hmem.1, if_neg hmem.2, norm_zero])⟩

theorem qCoeff_sectionD (x : JetD F) (n : ℕ) :
    qCoeff F n (sectionD F x) = if n = 0 then x.fst else if n = 1 then x.snd else 0 := by
  show PowerSeries.coeff n (PowerSeries.mk fun m =>
    if m = 0 then x.fst else if m = 1 then x.snd else 0) = _
  rw [PowerSeries.coeff_mk]

@[simp] theorem rhoC_sectionD (x : JetD F) : rhoC F (sectionD F x) = x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show qCoeff F 0 (sectionD F x) = x.fst
    rw [qCoeff_sectionD, if_pos rfl]
  · show qCoeff F 1 (sectionD F x) = x.snd
    rw [qCoeff_sectionD, if_neg one_ne_zero, if_pos rfl]

theorem sectionD_add (x y : JetD F) : sectionD F (x + y) = sectionD F x + sectionD F y := by
  apply Subtype.ext
  ext n
  rw [show PowerSeries.coeff n (sectionD F (x + y)).1 =
      qCoeff F n (sectionD F (x + y)) from rfl, qCoeff_sectionD,
    show (sectionD F x + sectionD F y).1 = (sectionD F x).1 + (sectionD F y).1 from rfl,
    map_add,
    show PowerSeries.coeff n (sectionD F x).1 = qCoeff F n (sectionD F x) from rfl,
    show PowerSeries.coeff n (sectionD F y).1 = qCoeff F n (sectionD F y) from rfl,
    qCoeff_sectionD, qCoeff_sectionD]
  rcases eq_or_ne n 0 with rfl | h0
  · simp [TrivSqZeroExt.fst_add]
  · rw [if_neg h0, if_neg h0, if_neg h0]
    rcases eq_or_ne n 1 with rfl | h1
    · simp [TrivSqZeroExt.snd_add]
    · rw [if_neg h1, if_neg h1, if_neg h1, add_zero]

theorem norm_sectionD (x : JetD F) : ‖sectionD F x‖ = ‖x‖ := by
  rw [Restricted.norm_eq, JetNorm.norm_def]
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun n => ?_) (le_max_of_le_left (norm_nonneg _))
    rw [one_pow, mul_one]
    show ‖PowerSeries.coeff n (sectionD F x).1‖ ≤ _
    rw [show PowerSeries.coeff n (sectionD F x).1 = qCoeff F n (sectionD F x) from rfl,
      qCoeff_sectionD]
    rcases eq_or_ne n 0 with rfl | h0
    · rw [if_pos rfl]; exact le_max_left _ _
    · rw [if_neg h0]
      rcases eq_or_ne n 1 with rfl | h1
      · rw [if_pos rfl]; exact le_max_right _ _
      · rw [if_neg h1, norm_zero]
        exact le_max_of_le_left (norm_nonneg _)
  · refine max_le ?_ ?_
    · have h := PowerSeries.le_gaussNorm norm 1 (sectionD F x).1
        (Restricted.hasGaussNorm (R := L F) 1 (sectionD F x)) 0
      rw [one_pow, mul_one, show PowerSeries.coeff 0 (sectionD F x).1 =
        qCoeff F 0 (sectionD F x) from rfl, qCoeff_sectionD, if_pos rfl] at h
      exact h
    · have h := PowerSeries.le_gaussNorm norm 1 (sectionD F x).1
        (Restricted.hasGaussNorm (R := L F) 1 (sectionD F x)) 1
      rw [one_pow, mul_one, show PowerSeries.coeff 1 (sectionD F x).1 =
        qCoeff F 1 (sectionD F x) from rfl, qCoeff_sectionD, if_neg one_ne_zero,
        if_pos rfl] at h
      exact h

/-- `ρC` is norm-nonincreasing. -/
theorem norm_rhoC_le (f : JetC F) : ‖rhoC F f‖ ≤ ‖f‖ := by
  rw [JetNorm.norm_def]
  refine max_le ?_ ?_
  · have h := PowerSeries.le_gaussNorm norm 1 f.1
      (Restricted.hasGaussNorm (R := L F) 1 f) 0
    rw [one_pow, mul_one] at h
    exact h.trans (le_of_eq (Restricted.norm_eq 1 f).symm)
  · have h := PowerSeries.le_gaussNorm norm 1 f.1
      (Restricted.hasGaussNorm (R := L F) 1 f) 1
    rw [one_pow, mul_one] at h
    exact h.trans (le_of_eq (Restricted.norm_eq 1 f).symm)

/-- `ρB` is an isometry (componentwise `ofRestricted` is norm-preserving). -/
theorem norm_rhoB (b : JetB F) : ‖rhoB F b‖ = ‖b‖ :=
  JetNorm.norm_mapHom _ (fun a => ofRestricted_norm a) b

theorem rhoB_injective : Function.Injective (rhoB F) :=
  JetNorm.mapHom_injective _ (ofRestricted_injective (R := K))

/-- `ρC` is surjective ([FJP] Prop 2.1: `𝒞 → 𝒟` is a strict surjection). -/
theorem rhoC_surjective : Function.Surjective (rhoC F) :=
  fun x => ⟨sectionD F x, rhoC_sectionD F x⟩

/-! ### The pinching algebra 𝓐 ([FJP] Definition 1.2 via Lemma 2.2 / (1.7) / (1.8)) -/

/-- The support subring: elements of `𝒞` whose `Q⁰`- and `Q¹`-coefficients lie in the
nonnegative-support subring `K⟨W⟩ ⊂ L` — [FJP] (1.7):
`𝒜 = {f₀(W) + Qf₁(W) + Q²h : f₀, f₁ ∈ k⟨W⟩, h ∈ L⟨Q⟩}`. -/
noncomputable def jetSupport : Subring (JetC F) where
  carrier := {f | qCoeff F 0 f ∈ nonnegSubring K ∧ qCoeff F 1 f ∈ nonnegSubring K}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

/-- `𝓐`, the finite-jet pinching algebra ([FJP] Definition 1.2), realised as the support
subring of `𝒞` with the restricted norm ([FJP] Lemma 2.2). -/
abbrev JetA : Type _ := ↥(jetSupport F)

/-- The support subring is closed in `𝒞` ([FJP] Lemma 2.2: "Imposing the preceding closed
condition on the `Q⁰`- and `Q¹`-coefficients therefore cuts out a closed subspace of 𝒞"). -/
theorem isClosed_jetSupport : IsClosed ((jetSupport F : Set (JetC F))) := by sorry

/-- `𝓐` inherits `NormedCommRing` and `IsUltrametricDist` from `𝒞` through the mathlib
`SubringClass` instances (the norm is the restriction — [FJP] Lemma 2.2's isometry is
definitional). Completeness holds because the subring is closed. -/
instance : CompleteSpace (JetA F) := by sorry

/-- The inclusion `ιC : 𝓐 → 𝓒` (an isometry by construction; [FJP] Lemma 2.2). -/
noncomputable def iotaC : JetA F →+* JetC F := (jetSupport F).subtype

@[simp] theorem norm_iotaC (a : JetA F) : ‖iotaC F a‖ = ‖a‖ := rfl

/-- `jB : 𝓐 → 𝓑`, the 2-jet of an element of 𝓐, with coefficients in `K⟨W⟩`
([FJP] (5.1): `ι_B : 𝒜 → ℬ`). -/
noncomputable def jB : JetA F →+* JetB F where
  toFun a :=
    ⟨(nonnegEquiv (R := K)).symm ⟨qCoeff F 0 (a : JetC F), a.2.1⟩,
     (nonnegEquiv (R := K)).symm ⟨qCoeff F 1 (a : JetC F), a.2.2⟩⟩
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

theorem norm_jB_le (a : JetA F) : ‖jB F a‖ ≤ ‖a‖ := by sorry

/-! ### The strict Milnor row ([FJP] Prop 2.1, Lemma 2.2, (2.1b))

`0 → 𝓐 →(jB, ιC) 𝓑 ⊕ 𝓒 →(ρB − ρC) 𝓓 → 0` is exact with all constants 1:
* the square commutes on 𝓐,
* an element of 𝓒 lies in 𝓐 iff its 2-jet comes from 𝓑,
* the difference map is strictly surjective via the norm-one section,
* the pullback (max) norm of `(jB a, ιC a)` equals `‖a‖` ([FJP] Lemma 2.2:
  "the maximum pullback norm of `(b, c)` equals `‖c‖_𝒞`"). -/

theorem square_commutes (a : JetA F) : rhoB F (jB F a) = rhoC F (iotaC F a) := by sorry

/-- Cartesianness, membership form: `c ∈ 𝓐 ↔ ρC c ∈ range ρB` ([FJP] (1.6)/(1.7)). -/
theorem mem_jetSupport_iff_jet_in_range (c : JetC F) :
    c ∈ jetSupport F ↔ rhoC F c ∈ Set.range (rhoB F) := by sorry

/-- Exactness in the middle with uniqueness: a compatible pair `(b, c)` comes from a unique
element of 𝓐 ([FJP] Prop 2.1: "Its kernel is the algebraic pullback (1.6)"). -/
theorem milnorRow_exact (b : JetB F) (c : JetC F) (h : rhoB F b = rhoC F c) :
    ∃! a : JetA F, jB F a = b ∧ iotaC F a = c := by sorry

/-- The pullback norm identity ([FJP] Lemma 2.2): for `a ∈ 𝓐`,
`max ‖jB a‖ ‖ιC a‖ = ‖a‖`. -/
theorem max_norm_eq (a : JetA F) : max ‖jB F a‖ ‖iotaC F a‖ = ‖a‖ := by sorry

/-- Strict surjectivity of the difference map with constant 1 ([FJP] Prop 2.1 and (2.1b):
"the two denominator losses in the defining square are zero"). -/
theorem difference_strict_surjective (d : JetD F) :
    ∃ c : JetC F, rhoC F c = d ∧ ‖c‖ = ‖d‖ := by sorry

/-! ### Pseudouniformizers and scalar embeddings -/

/-- The constant embedding `K →+* 𝒞` (through `RestrictedLaurent.C` and the power-series
constants). -/
noncomputable def constC : K →+* JetC F := by sorry

theorem norm_constC (a : K) : ‖constC F a‖ = ‖a‖ := by sorry

/-- The constants land in 𝓐 (support `(0,0)`). -/
theorem constC_mem_jetSupport (a : K) : constC F a ∈ jetSupport F := by sorry

/-- The constant embedding `K →+* 𝓐`. -/
noncomputable def constA : K →+* JetA F := by sorry

/-- The pseudouniformizer `ϖ` of each jet ring: the image of `t ∈ K`. -/
noncomputable def tA : JetA F := constA F (LaurentSeriesExample.t F)

theorem norm_tA_lt_one : ‖tA F‖ < 1 := by sorry

theorem isUnit_tA : IsUnit (tA F) := by sorry

/-! ### Huber instance stacks (pattern of `ExampleUnitDisc.lean`)

Each of 𝓐, 𝓑, 𝓒, 𝓓 is a complete Tate ring; the chosen plus ring is the **maximal** one,
the full power-bounded subring ([FJP] §5 (5.2) and the sentence before it: "Give every ring
its maximal plus ring of power-bounded elements"). For 𝓑 and 𝓓 this subring is *unbounded*
([FJP] (2.1d): "the summand `kQ` is an unbounded line. These two rings are valid maximal
plus rings"), which `IsRingOfIntegralElements` permits (no boundedness field). -/

section InstanceStack

variable (E : Type*) [NormedCommRing E] [IsUltrametricDist E]

/-- The closed unit ball of a nonarchimedean normed ring, as a subring. -/
noncomputable def unitBall : Subring E where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

theorem mem_unitBall_iff (x : E) : x ∈ unitBall E ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem isOpen_unitBall : IsOpen ((unitBall E : Set E)) := by sorry

end InstanceStack

instance : IsHuberRing (JetA F) := by sorry
instance : IsHuberRing (JetB F) := by sorry
instance : IsHuberRing (JetC F) := by sorry
instance : IsHuberRing (JetD F) := by sorry

instance : IsTateRing (JetA F) := by sorry
instance : IsTateRing (JetB F) := by sorry
instance : IsTateRing (JetC F) := by sorry
instance : IsTateRing (JetD F) := by sorry

noncomputable instance : ValuationSpectrum.PlusSubring (JetA F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetA F)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetB F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetB F)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetC F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetC F)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetD F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetD F)⟩

/-- The maximal plus ring is a ring of integral elements ([FJP] §5, the integral-closedness
argument after (5.2): `E°` is open, integrally closed, and power-bounded — boundedness is
not required). Stated once per ring; the integral-closedness core is the [FJP] monic-equation
argument. -/
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetA F) : Subring (JetA F))) := by sorry
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetB F) : Subring (JetB F))) := by sorry
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetC F) : Subring (JetC F))) := by sorry
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetD F) : Subring (JetD F))) := by sorry

instance : IsUniformAddGroup (JetA F) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetB F) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetC F) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetD F) := SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (JetA F) (IsTopologicalAddGroup.rightUniformSpace (JetA F)) := by
  sorry
instance : @CompleteSpace (JetB F) (IsTopologicalAddGroup.rightUniformSpace (JetB F)) := by
  sorry
instance : @CompleteSpace (JetC F) (IsTopologicalAddGroup.rightUniformSpace (JetC F)) := by
  sorry
instance : @CompleteSpace (JetD F) (IsTopologicalAddGroup.rightUniformSpace (JetD F)) := by
  sorry

end FiniteJet
