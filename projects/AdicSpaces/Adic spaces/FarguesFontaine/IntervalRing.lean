/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

import «Adic spaces».FarguesFontaine.Groebner

/-!
# The interval rings `B^I` (Kedlaya §4)

Kedlaya (*Noetherian properties of Fargues–Fontaine curves*, Definition 4.2) defines,
for a closed subinterval `I = [s, r] ⊂ (0, ∞)`, the norm `λ_I = max {λ_s, λ_r}` on
`B_{L,E}` and the ring `B^I_{L,E}` as the completion of `B_{L,E}` for `λ_I`.

In the campaign specialization the interval is recorded by its two endpoint radii
`ρ₁, ρ₂ ∈ (0,1)` (decision AD-4), and — following the same pattern that produced `A^r`
in `ArCompletion.lean` — the completion is realized concretely as the **closure of the
diagonal image of `Bloc` in the product of the two completed fraction fields**
(decision AD-7). This avoids constructing a seminormed-ring structure by hand: the
product of two complete valued fields is complete, the diagonal image carries exactly
the `max`-of-two-valuations uniformity, and its closure is therefore the completion.

## Main definitions

* `FarguesFontaine.BIProd` : the diagonal map `Bloc → hatK ρ₁ × hatK ρ₂`.
* `FarguesFontaine.BISub` : the interval ring `B^I` as a closed subring of the product.
* `FarguesFontaine.wI` : the interval norm `max {λ_{ρ₁}, λ_{ρ₂}}`.
* `FarguesFontaine.BIPlus` : the integral subring `B^{I,+}` of norm-`≤ 1` elements.
* `FarguesFontaine.resI` : the restriction map to an intermediate radius.
* `FarguesFontaine.resIHom` : the restriction ring homomorphism `B^I → B^{I'}`.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Definition 4.2, Lemma 4.4, Corollary 4.5.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **The diagonal map** of `Bloc` into the two completed fraction fields attached to
the endpoints of the interval. -/
def BIProd {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) :
    Bloc p F ϖ →+* (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  (BlocToHatK p F ϖ hρ₁0 hρ₁1).prod (BlocToHatK p F ϖ hρ₂0 hρ₂1)

@[simp]
theorem BIProd_fst {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) (x : Bloc p F ϖ) :
    (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).1 = BlocToHatK p F ϖ hρ₁0 hρ₁1 x := rfl

@[simp]
theorem BIProd_snd {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) (x : Bloc p F ϖ) :
    (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).2 = BlocToHatK p F ϖ hρ₂0 hρ₂1 x := rfl

/-- **The interval ring `B^I`** (Kedlaya Definition 4.2, realized per AD-7): the
closure of the diagonal `Bloc`-image inside the product of the two completions. -/
def BISub {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) :
    Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :=
  (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range.topologicalClosure

/-- `B^I` is closed in the product. -/
theorem isClosed_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsClosed (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := by
  have hcarrier : (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      = closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := rfl
  rw [hcarrier]
  exact isClosed_closure

/-- The diagonal image lies in `B^I`. -/
theorem BIProd_mem_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (x : Bloc p F ϖ) :
    BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
  Subring.le_topologicalClosure _ ⟨x, rfl⟩

/-- **The interval norm** `λ_I = max {λ_{ρ₁}, λ_{ρ₂}}` (Kedlaya Definition 4.2). -/
def wI {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) : NNReal :=
  max (Valued.v z.1) (Valued.v z.2)

@[simp]
theorem wI_zero {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 0 = 0 := by
  rw [wI]
  simp

@[simp]
theorem wI_one {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 1 = 1 := by
  rw [wI]
  simp

/-- The interval norm is ultrametric. -/
theorem wI_add_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (z w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z + w)
      ≤ max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z)
        (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w) := by
  refine max_le ?_ ?_
  · refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_right (le_max_left _ _)
  · refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_right _ _)

/-- The interval norm is submultiplicative (in fact each factor is multiplicative). -/
theorem wI_mul_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (z w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z * w)
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w := by
  refine max_le ?_ ?_
  · rw [show (z * w).1 = z.1 * w.1 from rfl, Valuation.map_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_left _ _) zero_le zero_le
  · rw [show (z * w).2 = z.2 * w.2 from rfl, Valuation.map_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _) zero_le zero_le

/-- The interval norm of a negation. -/
@[simp]
theorem wI_neg {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (-z) = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z := by
  rw [wI, wI]
  have h1 : Valued.v ((-z).1) = Valued.v z.1 := by
    rw [show (-z).1 = -z.1 from rfl, Valuation.map_neg]
  have h2 : Valued.v ((-z).2) = Valued.v z.2 := by
    rw [show (-z).2 = -z.2 from rfl, Valuation.map_neg]
  rw [h1, h2]

/-- The interval norm vanishes only at `0`. -/
theorem wI_eq_zero_iff {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [wI] at h
    have h1 : Valued.v z.1 = 0 :=
      le_antisymm (le_trans (le_max_left _ _) h.le) zero_le
    have h2 : Valued.v z.2 = 0 :=
      le_antisymm (le_trans (le_max_right _ _) h.le) zero_le
    refine Prod.ext ?_ ?_
    · exact (Valuation.zero_iff _).mp h1
    · exact (Valuation.zero_iff _).mp h2
  · rintro rfl
    exact wI_zero p F

/-- The interval norm restricted to `Bloc`: the max of the two Gauss values. -/
theorem wI_BIProd {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (x : Bloc p F ϖ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
      = max (Valued.v (BlocToHatK p F ϖ hρ₁0 hρ₁1 x))
        (Valued.v (BlocToHatK p F ϖ hρ₂0 hρ₂1 x)) := rfl

/-- **The first coordinate of an interval-ring element lies in the endpoint ring**. -/
theorem BISub_fst_mem {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    z.1 ∈ BrSub p F ϖ hρ₁0 hρ₁1 := by
  have hz' : z ∈ closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := hz
  have himg : Prod.fst '' (closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))))
      ⊆ closure (Prod.fst '' ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))) :=
    image_closure_subset_closure_image continuous_fst
  have hsub : Prod.fst '' ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      ⊆ ((BlocToHatK p F ϖ hρ₁0 hρ₁1).range : Set (hatK p F hρ₁0 hρ₁1)) := by
    rintro w ⟨q, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hmem : z.1 ∈ closure ((BlocToHatK p F ϖ hρ₁0 hρ₁1).range
      : Set (hatK p F hρ₁0 hρ₁1)) :=
    closure_mono hsub (himg ⟨z, hz', rfl⟩)
  exact hmem

/-- **The second coordinate of an interval-ring element lies in the endpoint ring**. -/
theorem BISub_snd_mem {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    z.2 ∈ BrSub p F ϖ hρ₂0 hρ₂1 := by
  have hz' : z ∈ closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := hz
  have himg : Prod.snd '' (closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))))
      ⊆ closure (Prod.snd '' ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))) :=
    image_closure_subset_closure_image continuous_snd
  have hsub : Prod.snd '' ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      ⊆ ((BlocToHatK p F ϖ hρ₂0 hρ₂1).range : Set (hatK p F hρ₂0 hρ₂1)) := by
    rintro w ⟨q, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  exact closure_mono hsub (himg ⟨z, hz', rfl⟩)

/-- Value balls around a point are neighborhoods. -/
theorem valued_ball_mem_nhds {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (z : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) :
    {w : hatK p F hρ0 hρ1 | Valued.v (w - z) ≤ ε} ∈ nhds z := by
  have hcont : ContinuousAt (fun w : hatK p F hρ0 hρ1 => w - z) z :=
    (continuous_id.sub continuous_const).continuousAt
  have h0 : {y : hatK p F hρ0 hρ1 | Valued.v y ≤ ε}
      ∈ nhds ((fun w : hatK p F hρ0 hρ1 => w - z) z) := by
    rw [show (fun w : hatK p F hρ0 hρ1 => w - z) z = 0 from sub_self z]
    exact valued_ball_mem_nhds_zero p F (hρ0 := hρ0) (hρ1 := hρ1) hε
  exact hcont h0

/-- **Quantitative density**: every element of `B^I` is `wI`-approximated by the image
of `Bloc`. -/
theorem exists_BIProd_wI_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) {ε : NNReal} (hε : 0 < ε) :
    ∃ x : Bloc p F ϖ,
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z) ≤ ε := by
  have hz' : z ∈ closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := hz
  have hball : {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (w - z) ≤ ε} ∈ nhds z := by
    have h1 : ((fun w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => w.1)
        ⁻¹' {w : hatK p F hρ₁0 hρ₁1 | Valued.v (w - z.1) ≤ ε}) ∈ nhds z :=
      continuous_fst.continuousAt (valued_ball_mem_nhds p F z.1 hε)
    have h2 : ((fun w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => w.2)
        ⁻¹' {w : hatK p F hρ₂0 hρ₂1 | Valued.v (w - z.2) ≤ ε}) ∈ nhds z :=
      continuous_snd.continuousAt (valued_ball_mem_nhds p F z.2 hε)
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro w ⟨hw1, hw2⟩
    have hb1 : Valued.v (w.1 - z.1) ≤ ε := hw1
    have hb2 : Valued.v (w.2 - z.2) ≤ ε := hw2
    exact max_le hb1 hb2
  obtain ⟨w, hwball, hwrange⟩ := mem_closure_iff_nhds.mp hz' _ hball
  obtain ⟨x, rfl⟩ := hwrange
  exact ⟨x, hwball⟩

/-- **Three circles, termwise** (Kedlaya Lemma 4.4, the single-term equality). -/
theorem gaussTerm_rpow_interpolate {ρ₁ ρ₂ : NNReal} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F (ρ₁ ^ θ * ρ₂ ^ (1 - θ)) x n
      = (gaussTerm p F ρ₁ x n) ^ θ * (gaussTerm p F ρ₂ x n) ^ (1 - θ) := by
  rw [gaussTerm, gaussTerm, gaussTerm, NNReal.mul_rpow, NNReal.mul_rpow]
  rcases eq_or_ne (perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) 0
    with hz | hz
  · rw [hz]
    rcases eq_or_ne θ 0 with rfl | hθne
    · simp
    · rcases eq_or_ne (1 - θ) 0 with h1 | h1ne
      · rw [h1]
        simp [NNReal.zero_rpow hθne]
      · rw [NNReal.zero_rpow hθne, NNReal.zero_rpow h1ne]
        simp
  · have hsplit : perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)
        = (perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) ^ θ
          * (perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) ^ (1 - θ) := by
      rw [← NNReal.rpow_add hz]
      simp
    have hpow : ((ρ₁ ^ θ * ρ₂ ^ (1 - θ)) : NNReal) ^ n
        = (ρ₁ ^ n) ^ θ * (ρ₂ ^ n) ^ (1 - θ) := by
      rw [mul_pow, ← NNReal.rpow_natCast (ρ₁ ^ θ) n, ← NNReal.rpow_natCast (ρ₂ ^ (1 - θ)) n,
        ← NNReal.rpow_natCast ρ₁ n, ← NNReal.rpow_natCast ρ₂ n,
        ← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
      ring_nf
    calc ((ρ₁ ^ θ * ρ₂ ^ (1 - θ)) : NNReal) ^ n
          * perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)
        = ((ρ₁ ^ n) ^ θ * (ρ₂ ^ n) ^ (1 - θ))
          * ((perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) ^ θ
            * (perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) ^ (1 - θ)) := by
          rw [← hpow, ← hsplit]
      _ = ((ρ₁ ^ n) ^ θ
            * (perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) ^ θ)
          * ((ρ₂ ^ n) ^ (1 - θ)
            * (perfectoidValuation p F ((teichCoeff p F x n : OF F) : F)) ^ (1 - θ)) := by
          ring

/-- **Three circles** (Kedlaya Lemma 4.4): the Gauss value at an interpolated radius
is bounded by the interpolated product of the endpoint values. -/
theorem gaussValue_rpow_interpolate {ρ₁ ρ₂ : NNReal} (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : Ainf p F) :
    gaussValue p F (ρ₁ ^ θ * ρ₂ ^ (1 - θ)) x
      ≤ (gaussValue p F ρ₁ x) ^ θ * (gaussValue p F ρ₂ x) ^ (1 - θ) := by
  have hmid : (ρ₁ ^ θ * ρ₂ ^ (1 - θ) : NNReal) ≤ 1 := by
    have h1 : (ρ₁ : NNReal) ^ θ ≤ 1 := by
      simpa using NNReal.rpow_le_rpow hρ₁1 hθ0
    have h2 : (ρ₂ : NNReal) ^ (1 - θ) ≤ 1 := by
      simpa using NNReal.rpow_le_rpow hρ₂1 (by linarith)
    calc (ρ₁ : NNReal) ^ θ * ρ₂ ^ (1 - θ) ≤ 1 * 1 :=
          mul_le_mul h1 h2 zero_le zero_le
      _ = 1 := one_mul 1
  refine ciSup_le fun n => ?_
  rw [gaussTerm_rpow_interpolate p F hθ0 hθ1 x n]
  exact mul_le_mul
    (NNReal.rpow_le_rpow (gaussTerm_le_gaussValue p F hρ₁1 x n) hθ0)
    (NNReal.rpow_le_rpow (gaussTerm_le_gaussValue p F hρ₂1 x n) (by linarith))
    zero_le zero_le

/-- Interpolated radii are again admissible. -/
theorem rpow_interpolate_lt_one {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ) ∧ ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1 := by
  constructor
  · exact mul_pos (NNReal.rpow_pos hρ₁0) (NNReal.rpow_pos hρ₂0)
  · rcases eq_or_lt_of_le hθ0 with hθ | hθ
    · rw [← hθ]
      simp only [NNReal.rpow_zero, one_mul, sub_zero, NNReal.rpow_one]
      exact hρ₂1
    · have h1 : (ρ₁ : NNReal) ^ θ < 1 := by
        rw [show (1 : NNReal) = 1 ^ θ from (NNReal.one_rpow θ).symm]
        exact NNReal.rpow_lt_rpow hρ₁1 hθ
      have h2 : (ρ₂ : NNReal) ^ (1 - θ) ≤ 1 := by
        simpa using NNReal.rpow_le_rpow hρ₂1.le (by linarith)
      calc (ρ₁ : NNReal) ^ θ * ρ₂ ^ (1 - θ) ≤ ρ₁ ^ θ * 1 :=
            mul_le_mul_of_nonneg_left h2 zero_le
        _ = ρ₁ ^ θ := mul_one _
        _ < 1 := h1

/-- **Three circles on `Bloc`** (Kedlaya Lemma 4.4): the extended Gauss valuation at
an interpolated radius is bounded by the interpolated endpoint values. -/
theorem wLoc_rpow_interpolate {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (x : Bloc p F ϖ) :
    wLoc p F ϖ hmid0 hmid1 x
      ≤ (wLoc p F ϖ hρ₁0 hρ₁1 x) ^ θ * (wLoc p F ϖ hρ₂0 hρ₂1 x) ^ (1 - θ) := by
  obtain ⟨⟨a, y⟩, hx⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  change x * algebraMap (Ainf p F) (Bloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Bloc p F ϖ) a at hx
  obtain ⟨k, hk⟩ := y.2
  have hk' : ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) := hk
  set c : NNReal := perfectoidValuation p F
    ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hc
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  -- the denominator values
  have hden : ∀ {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1),
      gaussValue p F σ (y : Ainf p F) = (σ * c) ^ k := by
    intro σ hσ0 hσ1
    rw [← hk', show gaussValue p F σ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = (gaussValue p F σ ((p : Ainf p F) * teichPi p F ϖ)) ^ k from
        map_pow (gaussVal p F hσ0 hσ1) _ k, gaussValue_p_teichPi p F ϖ hσ1]
  -- the value equations
  have hval : ∀ {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1),
      wLoc p F ϖ hσ0 hσ1 x * (σ * c) ^ k = gaussValue p F σ a := by
    intro σ hσ0 hσ1
    have happ := congrArg (wLoc p F ϖ hσ0 hσ1) hx
    rw [map_mul, wLoc_algebraMap, wLoc_algebraMap, hden hσ0 hσ1] at happ
    exact happ
  -- the denominator interpolates exactly
  have hdenint : ((ρ₁ ^ θ * ρ₂ ^ (1 - θ)) * c) ^ k
      = ((ρ₁ * c) ^ k) ^ θ * ((ρ₂ * c) ^ k) ^ (1 - θ) := by
    have hcsplit : c = c ^ θ * c ^ (1 - θ) := by
      rw [← NNReal.rpow_add hc0.ne']
      simp
    have hbase : (ρ₁ ^ θ * ρ₂ ^ (1 - θ)) * c
        = (ρ₁ * c) ^ θ * (ρ₂ * c) ^ (1 - θ) := by
      rw [NNReal.mul_rpow, NNReal.mul_rpow]
      calc (ρ₁ ^ θ * ρ₂ ^ (1 - θ)) * c
          = (ρ₁ ^ θ * ρ₂ ^ (1 - θ)) * (c ^ θ * c ^ (1 - θ)) := by rw [← hcsplit]
        _ = ρ₁ ^ θ * c ^ θ * (ρ₂ ^ (1 - θ) * c ^ (1 - θ)) := by ring
    rw [hbase, mul_pow, ← NNReal.rpow_natCast ((ρ₁ * c) ^ θ) k,
      ← NNReal.rpow_natCast ((ρ₂ * c) ^ (1 - θ)) k,
      ← NNReal.rpow_natCast ((ρ₁ * c)) k, ← NNReal.rpow_natCast ((ρ₂ * c)) k,
      ← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
    ring_nf
  -- combine
  have hdenne : ((ρ₁ ^ θ * ρ₂ ^ (1 - θ)) * c) ^ k ≠ 0 :=
    pow_ne_zero k (mul_pos hmid0 hc0).ne'
  refine le_of_mul_le_mul_right ?_ (pos_iff_ne_zero.mpr hdenne)
  rw [hval hmid0 hmid1]
  calc gaussValue p F (ρ₁ ^ θ * ρ₂ ^ (1 - θ)) a
      ≤ (gaussValue p F ρ₁ a) ^ θ * (gaussValue p F ρ₂ a) ^ (1 - θ) :=
        gaussValue_rpow_interpolate p F hρ₁1.le hρ₂1.le hθ0 hθ1 a
    _ = (wLoc p F ϖ hρ₁0 hρ₁1 x * (ρ₁ * c) ^ k) ^ θ
        * (wLoc p F ϖ hρ₂0 hρ₂1 x * (ρ₂ * c) ^ k) ^ (1 - θ) := by
        rw [hval hρ₁0 hρ₁1, hval hρ₂0 hρ₂1]
    _ = ((wLoc p F ϖ hρ₁0 hρ₁1 x) ^ θ * (wLoc p F ϖ hρ₂0 hρ₂1 x) ^ (1 - θ))
        * (((ρ₁ * c) ^ k) ^ θ * ((ρ₂ * c) ^ k) ^ (1 - θ)) := by
        rw [NNReal.mul_rpow, NNReal.mul_rpow]
        ring
    _ = ((wLoc p F ϖ hρ₁0 hρ₁1 x) ^ θ * (wLoc p F ϖ hρ₂0 hρ₂1 x) ^ (1 - θ))
        * ((ρ₁ ^ θ * ρ₂ ^ (1 - θ)) * c) ^ k := by rw [hdenint]

/-- **Corollary 4.5, usable form**: the interval norm dominates every intermediate
radius. -/
theorem wLoc_le_max_of_interpolate {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (x : Bloc p F ϖ) :
    wLoc p F ϖ hmid0 hmid1 x
      ≤ max (wLoc p F ϖ hρ₁0 hρ₁1 x) (wLoc p F ϖ hρ₂0 hρ₂1 x) := by
  refine le_trans (wLoc_rpow_interpolate p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0 hθ1 hmid0 hmid1 x) ?_
  set M := max (wLoc p F ϖ hρ₁0 hρ₁1 x) (wLoc p F ϖ hρ₂0 hρ₂1 x) with hM
  calc (wLoc p F ϖ hρ₁0 hρ₁1 x) ^ θ * (wLoc p F ϖ hρ₂0 hρ₂1 x) ^ (1 - θ)
      ≤ M ^ θ * M ^ (1 - θ) :=
        mul_le_mul (NNReal.rpow_le_rpow (le_max_left _ _) hθ0)
          (NNReal.rpow_le_rpow (le_max_right _ _) (by linarith)) zero_le zero_le
    _ = M := by
        rcases eq_or_ne M 0 with h0 | h0
        · rw [h0]
          rcases eq_or_ne θ 0 with rfl | hθne
          · simp
          · rw [NNReal.zero_rpow hθne, zero_mul]
        · rw [← NNReal.rpow_add h0]
          simp

/-- **`B^I` is complete**: it is closed in a product of complete valued fields. -/
theorem isComplete_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsComplete (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) :=
  (isClosed_BISub p F ϖ).isComplete

/-- A `wI`-Cauchy criterion in the ambient product. -/
theorem cauchySeq_of_wI_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (s : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    (h : ∀ ε : NNReal, 0 < ε → ∃ N₀ : ℕ, ∀ m n : ℕ, N₀ ≤ m → N₀ ≤ n →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (s m - s n) ≤ ε) :
    CauchySeq s := by
  have h1 : CauchySeq (fun n => (s n).1) := by
    refine cauchySeq_of_valued_le p F (hρ0 := hρ₁0) (hρ1 := hρ₁1)
      (fun n => (s n).1) fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := h ε hε
    exact ⟨N₀, fun m n hm hn => le_trans (le_max_left _ _) (hN₀ m n hm hn)⟩
  have h2 : CauchySeq (fun n => (s n).2) := by
    refine cauchySeq_of_valued_le p F (hρ0 := hρ₂0) (hρ1 := hρ₂1)
      (fun n => (s n).2) fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := h ε hε
    exact ⟨N₀, fun m n hm hn => le_trans (le_max_right _ _) (hN₀ m n hm hn)⟩
  exact CauchySeq.prodMk h1 h2

set_option maxHeartbeats 1000000 in
/-- **Series converge in `B^I`**: a sequence of interval-ring elements with vanishing
norm bounds has a limit in `B^I`, with the expected tail estimates. -/
theorem exists_BI_series_limit {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {u : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hu : ∀ l, u l ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    {C : ℕ → NNReal} (hC : ∀ l, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (u l) ≤ C l)
    (hC0 : Filter.Tendsto C Filter.atTop (nhds 0)) :
    ∃ S : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1),
      S ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ∧ Filter.Tendsto (fun n => ∑ l ∈ Finset.range n, u l)
        Filter.atTop (nhds S) := by
  set s : ℕ → (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
    fun n => ∑ l ∈ Finset.range n, u l with hs
  have hsmem : ∀ n, s n ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
    intro n
    exact Subring.sum_mem _ fun l _ => hu l
  have hdiff : ∀ m n : ℕ, n ≤ m → ∀ b : NNReal, (∀ l, n ≤ l → C l ≤ b) →
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (s m - s n) ≤ b := by
    intro m n hnm b hb
    have hIco : s m - s n = ∑ l ∈ Finset.Ico n m, u l := by
      rw [hs, Finset.sum_Ico_eq_sub _ hnm]
    rw [hIco, wI]
    have hfst : (∑ l ∈ Finset.Ico n m, u l).1
        = ∑ l ∈ Finset.Ico n m, (u l).1 := Prod.fst_sum
    have hsnd : (∑ l ∈ Finset.Ico n m, u l).2
        = ∑ l ∈ Finset.Ico n m, (u l).2 := Prod.snd_sum
    rw [hfst, hsnd]
    refine max_le ?_ ?_
    · refine Valuation.map_sum_le (Valued.v : Valuation (hatK p F hρ₁0 hρ₁1) NNReal) ?_
      intro l hl
      exact le_trans (le_trans (le_max_left _ _) (hC l))
        (hb l (Finset.mem_Ico.mp hl).1)
    · refine Valuation.map_sum_le (Valued.v : Valuation (hatK p F hρ₂0 hρ₂1) NNReal) ?_
      intro l hl
      exact le_trans (le_trans (le_max_right _ _) (hC l))
        (hb l (Finset.mem_Ico.mp hl).1)
  have hcauchy : CauchySeq s := by
    refine cauchySeq_of_wI_le p F s fun ε hε => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hC0.eventually_lt_const hε)
    refine ⟨N, fun m n hm hn => ?_⟩
    rcases le_total n m with hle | hle
    · exact hdiff m n hle ε fun l hl => (hN l (le_trans hn hl)).le
    · have hswap : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (s m - s n)
          = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (s n - s m) := by
        rw [← wI_neg p F (s m - s n)]
        congr 1
        ring
      rw [hswap]
      exact hdiff n m hle ε fun l hl => (hN l (le_trans hm hl)).le
  obtain ⟨S, hSmem, hS⟩ := cauchySeq_tendsto_of_isComplete
    (isComplete_BISub p F ϖ) hsmem hcauchy
  exact ⟨S, hSmem, hS⟩

/-- The extended Gauss valuation is nonzero off zero. -/
theorem wLoc_ne_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {x : Bloc p F ϖ}
    (hx : x ≠ 0) : wLoc p F ϖ hρ0 hρ1 x ≠ 0 := by
  obtain ⟨⟨a, y⟩, hxy⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  change x * algebraMap (Ainf p F) (Bloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Bloc p F ϖ) a at hxy
  intro h0
  have hval : gaussValue p F ρ a = 0 := by
    have happ := congrArg (wLoc p F ϖ hρ0 hρ1) hxy
    rw [map_mul, wLoc_algebraMap, wLoc_algebraMap, h0, zero_mul] at happ
    exact happ.symm
  have ha0 : a = 0 := by
    by_contra hane
    exact absurd hval (gaussValue_pos_of_ne_zero p F hρ0 hρ1.le hane).ne'
  have hxzero : x * algebraMap (Ainf p F) (Bloc p F ϖ) (y : Ainf p F) = 0 := by
    rw [hxy, ha0, map_zero]
  have hyunit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (y : Ainf p F)) := by
    obtain ⟨k, hk⟩ := y.2
    have hk' : ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) := hk
    rw [← hk', map_pow]
    exact (isUnit_p_teichPi_image p F ϖ).pow k
  obtain ⟨u, hu⟩ := hyunit
  refine hx ?_
  have : x * (u : Bloc p F ϖ) = 0 := by rw [hu]; exact hxzero
  calc x = x * (u : Bloc p F ϖ) * ((u⁻¹ : (Bloc p F ϖ)ˣ) : Bloc p F ϖ) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = 0 := by rw [this, zero_mul]

/-- The completed-field valuation restricts to `wLoc` on `Bloc`-images. -/
theorem valued_BlocToHatK {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (x : Bloc p F ϖ) :
    Valued.v (BlocToHatK p F ϖ hρ0 hρ1 x) = wLoc p F ϖ hρ0 hρ1 x := by
  obtain ⟨⟨a, y⟩, hx⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  change x * algebraMap (Ainf p F) (Bloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Bloc p F ϖ) a at hx
  have hyne : gaussValue p F ρ (y : Ainf p F) ≠ 0 := by
    obtain ⟨k, hk⟩ := y.2
    have hk' : ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) := hk
    rw [← hk', show gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = (gaussValue p F ρ ((p : Ainf p F) * teichPi p F ϖ)) ^ k from
        map_pow (gaussVal p F hρ0 hρ1) _ k]
    exact pow_ne_zero k (gaussValue_p_teichPi_ne_zero p F ϖ hρ0 hρ1)
  have hB : BlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ)
      (y : Ainf p F)) = toHatK p F hρ0 hρ1 (y : Ainf p F) :=
    IsLocalization.lift_eq _ _
  have hB' : BlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ) a)
      = toHatK p F hρ0 hρ1 a := IsLocalization.lift_eq _ _
  have h1 : Valued.v (BlocToHatK p F ϖ hρ0 hρ1 x) * gaussValue p F ρ (y : Ainf p F)
      = gaussValue p F ρ a := by
    have happ := congrArg (fun z => Valued.v (BlocToHatK p F ϖ hρ0 hρ1 z)) hx
    simp only [map_mul, hB, hB'] at happ
    rw [valued_toHatK, valued_toHatK] at happ
    exact happ
  have h2 : wLoc p F ϖ hρ0 hρ1 x * gaussValue p F ρ (y : Ainf p F)
      = gaussValue p F ρ a := by
    have happ := congrArg (wLoc p F ϖ hρ0 hρ1) hx
    rw [map_mul, wLoc_algebraMap, wLoc_algebraMap] at happ
    exact happ
  exact mul_right_cancel₀ hyne (h1.trans h2.symm)

/-- **Injectivity of the endpoint map** (the engine of Kedlaya Corollary 4.6). -/
theorem BlocToHatK_injective {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} :
    Function.Injective (BlocToHatK p F ϖ hρ0 hρ1) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  by_contra hne
  refine absurd (valued_BlocToHatK p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) x) ?_
  rw [hx, Valuation.map_zero]
  exact fun heq => (wLoc_ne_zero p F ϖ hne) heq.symm

/-- The diagonal map into the product is injective. -/
theorem BIProd_injective {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    Function.Injective (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) := by
  intro x y hxy
  exact BlocToHatK_injective p F ϖ (congrArg Prod.fst hxy)

/-- **The integral interval ring `B^{I,+}`** (Kedlaya Definition 4.2): the elements of
`B^I` of interval norm at most `1`. -/
def BIPlus {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) :
    Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) where
  carrier := {z | z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
    ∧ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ 1}
  zero_mem' := by
    refine ⟨zero_mem _, ?_⟩
    rw [wI_zero p F]
    exact zero_le_one
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    rw [wI_one p F]
  add_mem' := fun {a b} ha hb => by
    refine ⟨add_mem ha.1 hb.1, ?_⟩
    exact le_trans (wI_add_le p F a b) (max_le ha.2 hb.2)
  neg_mem' := fun {a} ha => by
    refine ⟨neg_mem ha.1, ?_⟩
    rw [wI_neg p F]
    exact ha.2
  mul_mem' := fun {a b} ha hb => by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    refine le_trans (wI_mul_le p F a b) ?_
    calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 a * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 b
        ≤ 1 * 1 := mul_le_mul ha.2 hb.2 zero_le zero_le
      _ = 1 := one_mul 1

/-- Membership in `B^{I,+}` unfolds to the two conditions. -/
theorem mem_BIPlus_iff {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)} :
    z ∈ BIPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ↔ z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ∧ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ 1 := Iff.rfl

/-- `B^{I,+}` sits inside `B^I`. -/
theorem BIPlus_le_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    BIPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ≤ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
  fun _ hz => hz.1

/-- Power-boundedness: elements of `B^{I,+}` have bounded powers. -/
theorem wI_pow_le_one {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ 1) (n : ℕ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z ^ n) ≤ 1 := by
  induction n with
  | zero =>
    rw [pow_zero, wI_one p F]
  | succ m ih =>
    rw [pow_succ]
    refine le_trans (wI_mul_le p F _ _) ?_
    calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z ^ m) * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z
        ≤ 1 * 1 := mul_le_mul ih hz zero_le zero_le
      _ = 1 := one_mul 1

/-- **The interval norm dominates every intermediate endpoint map** (Corollary 4.5,
in the form the restriction maps consume): for an interpolated radius, the value of
the endpoint image of a `Bloc`-element is at most its interval norm. -/
theorem valued_BlocToHatK_le_wI {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (x : Bloc p F ϖ) :
    Valued.v (BlocToHatK p F ϖ hmid0 hmid1 x)
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) := by
  rw [valued_BlocToHatK, wI_BIProd, valued_BlocToHatK, valued_BlocToHatK]
  exact wLoc_le_max_of_interpolate p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0 hθ1 hmid0 hmid1 x

/-- The endpoint maps are `wI`-Lipschitz on differences, hence uniformly continuous
for the interval uniformity. -/
theorem valued_BlocToHatK_sub_le_wI {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (x y : Bloc p F ϖ) :
    Valued.v (BlocToHatK p F ϖ hmid0 hmid1 x - BlocToHatK p F ϖ hmid0 hmid1 y)
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
        - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y) := by
  have hsub : BlocToHatK p F ϖ hmid0 hmid1 x - BlocToHatK p F ϖ hmid0 hmid1 y
      = BlocToHatK p F ϖ hmid0 hmid1 (x - y) := (map_sub _ _ _).symm
  have hsub2 : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
      - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (x - y) := (map_sub _ _ _).symm
  rw [hsub, hsub2]
  exact valued_BlocToHatK_le_wI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0 hθ1 hmid0 hmid1 (x - y)

/-- The approximant filter of a point of `B^I` is nontrivial. -/
theorem neBot_comap_of_mem_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)).NeBot := by
  rw [Filter.comap_neBot_iff]
  intro t ht
  have hz' : z ∈ closure (Set.range (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := hz
  obtain ⟨y, hyt, hyr⟩ := mem_closure_iff_nhds.mp hz' t ht
  obtain ⟨x, rfl⟩ := hyr
  exact ⟨x, hyt⟩

/-- **Pairs of approximants are eventually `wI`-close.** -/
theorem eventually_pair_wI_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) {ε : NNReal} (hε : 0 < ε) :
    ∀ᶠ q in (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
        (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)),
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.2
        - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.1) ≤ ε := by
  -- the ball around `z` in the product
  have hball : {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (w - z) ≤ ε / 2} ∈ nhds z := by
    have hhalf : (0 : NNReal) < ε / 2 := by
      simpa using div_pos hε (by norm_num : (0 : NNReal) < 2)
    have h1 : ((fun w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => w.1)
        ⁻¹' {w : hatK p F hρ₁0 hρ₁1 | Valued.v (w - z.1) ≤ ε / 2}) ∈ nhds z :=
      continuous_fst.continuousAt (valued_ball_mem_nhds p F z.1 hhalf)
    have h2 : ((fun w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => w.2)
        ⁻¹' {w : hatK p F hρ₂0 hρ₂1 | Valued.v (w - z.2) ≤ ε / 2}) ∈ nhds z :=
      continuous_snd.continuousAt (valued_ball_mem_nhds p F z.2 hhalf)
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro w ⟨hw1, hw2⟩
    have hb1 : Valued.v (w.1 - z.1) ≤ ε / 2 := hw1
    have hb2 : Valued.v (w.2 - z.2) ≤ ε / 2 := hw2
    exact max_le hb1 hb2
  have hhalfle : (ε : NNReal) / 2 ≤ ε := by
    exact div_le_self zero_le (by norm_num)
  have hcomap : ∀ᶠ x in Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z),
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z) ≤ ε / 2 := by
    refine Filter.eventually_comap.mpr (Filter.Eventually.mono hball ?_)
    intro w hw x hx
    rw [hx]
    exact hw
  refine Filter.Eventually.mono (Filter.prod_mem_prod hcomap hcomap) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hsplit : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y
      - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
      = (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y - z)
        - (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z) := by ring
  rw [hsplit]
  have hneg : (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y - z)
      - (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z)
      = (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 y - z)
        + (-(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z)) := by ring
  rw [hneg]
  refine le_trans (wI_add_le p F _ _) (max_le ?_ ?_)
  · exact le_trans hy hhalfle
  · rw [wI_neg p F]
    exact le_trans hx hhalfle

/-- Every value-group unit dominates a positive `NNReal` threshold. -/
theorem exists_nnreal_lt_gamma {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ) :
    ∃ ε : NNReal, 0 < ε ∧ ∀ w : hatK p F hρ0 hρ1,
      Valued.v w ≤ ε → (Valued.v).restrict w < γ.1 := by
  have hγpos : (0 : NNReal) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine pos_iff_ne_zero.mpr fun h0 => ?_
    have hinj := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      (f := MonoidWithZeroHom.ofClass (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal))).injective
    have h00 : MonoidWithZeroHom.ValueGroup₀.embedding (0 :
        MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v :
          Valuation (hatK p F hρ0 hρ1) NNReal))) = 0 := map_zero _
    exact γ.ne_zero (hinj (h0.trans h00.symm))
  obtain ⟨N, hN⟩ := _root_.exists_pow_lt_of_lt_one hγpos hρ1
  refine ⟨ρ ^ (N + 1), pow_pos hρ0 (N + 1), fun w hw => ?_⟩
  have hlt : Valued.v w < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine lt_of_le_of_lt hw (lt_of_lt_of_le ?_ hN.le)
    exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 (Nat.lt_succ_self N)
  have hsm := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
    (f := MonoidWithZeroHom.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))
  refine hsm.lt_iff_lt.mp ?_
  rw [Valuation.embedding_restrict]
  exact hlt

/-- **The restriction map to an intermediate radius**, defined as the limit of the
endpoint images along the approximant filter. -/
def resI {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) : hatK p F hσ0 hσ1 :=
  Filter.limUnder (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
    (fun x => BlocToHatK p F ϖ hσ0 hσ1 x)

set_option maxHeartbeats 1000000 in
/-- **The restriction map is the limit of the approximants** (Kedlaya Cor 4.5 made
into a map): for `z ∈ B^I` and an intermediate radius, the endpoint images of the
approximants converge to `resI z`. -/
theorem tendsto_resI {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    Filter.Tendsto (fun x => BlocToHatK p F ϖ hmid0 hmid1 x)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z)) := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  set L := Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z) with hL
  set g : Bloc p F ϖ → hatK p F hmid0 hmid1 :=
    fun x => BlocToHatK p F ϖ hmid0 hmid1 x with hg
  have hcauchy : Cauchy (Filter.map g L) := by
    refine ⟨hne.map _, ?_⟩
    rw [Filter.prod_map_map_eq]
    intro V hV
    obtain ⟨γ, -, hγV⟩ :=
      (Valued.hasBasis_uniformity (hatK p F hmid0 hmid1) NNReal).mem_iff.mp hV
    obtain ⟨ε, hε0, hεγ⟩ := exists_nnreal_lt_gamma p F γ
    have hpairs := eventually_pair_wI_le p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) z hε0
    rw [← hL] at hpairs
    rw [Filter.mem_map]
    refine Filter.mem_of_superset hpairs ?_
    rintro ⟨x, y⟩ hxy
    refine hγV ?_
    refine hεγ (g y - g x) ?_
    exact le_trans (valued_BlocToHatK_sub_le_wI p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0 hθ1 hmid0 hmid1 y x) hxy
  obtain ⟨w, hw⟩ := CompleteSpace.complete hcauchy
  have hty : Filter.Tendsto g L (nhds w) := hw
  have heq : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z = w := hty.limUnder_eq
  rw [heq]
  exact hty

/-- Interval-norm balls are neighborhoods in the product. -/
theorem wI_ball_mem_nhds {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) {ε : NNReal} (hε : 0 < ε) :
    {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (w - z) ≤ ε} ∈ nhds z := by
  have h1 : ((fun w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => w.1)
      ⁻¹' {w : hatK p F hρ₁0 hρ₁1 | Valued.v (w - z.1) ≤ ε}) ∈ nhds z :=
    continuous_fst.continuousAt (valued_ball_mem_nhds p F z.1 hε)
  have h2 : ((fun w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => w.2)
      ⁻¹' {w : hatK p F hρ₂0 hρ₂1 | Valued.v (w - z.2) ≤ ε}) ∈ nhds z :=
    continuous_snd.continuousAt (valued_ball_mem_nhds p F z.2 hε)
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro w ⟨hw1, hw2⟩
  have hb1 : Valued.v (w.1 - z.1) ≤ ε := hw1
  have hb2 : Valued.v (w.2 - z.2) ≤ ε := hw2
  exact max_le hb1 hb2

set_option maxHeartbeats 1000000 in
/-- **The restriction map extends the endpoint map**: on `Bloc`-images it is the
endpoint map itself. -/
theorem resI_BIProd {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (x : Bloc p F ϖ) :
    resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
      = BlocToHatK p F ϖ hmid0 hmid1 x := by
  have hmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := BIProd_mem_BISub p F ϖ x
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hmem
  have hlim := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 hmem
  have hlim2 : Filter.Tendsto (fun y => BlocToHatK p F ϖ hmid0 hmid1 y)
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        (nhds (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)))
      (nhds (BlocToHatK p F ϖ hmid0 hmid1 x)) := by
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (R := hatK p F hmid0 hmid1)).mp hU
    obtain ⟨ε, hε0, hεγ⟩ := exists_nnreal_lt_gamma p F γ
    refine Filter.mem_of_superset
      (Filter.preimage_mem_comap (wI_ball_mem_nhds p F
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) hε0)) ?_
    intro y hy
    refine hγ ?_
    refine hεγ _ ?_
    exact le_trans (valued_BlocToHatK_sub_le_wI p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0 hθ1 hmid0 hmid1 y x) hy
  exact tendsto_nhds_unique hlim hlim2

/-- Approximants of a sum are sums of approximants (filter form). -/
theorem map_add_comap_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (z z' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    Filter.map (fun q : Bloc p F ϖ × Bloc p F ϖ => q.1 + q.2)
        ((Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
          (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z')))
      ≤ Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds (z + z')) := by
  rw [← Filter.map_le_iff_le_comap, Filter.map_map]
  have h1 : Filter.Tendsto (fun q : Bloc p F ϖ × Bloc p F ϖ =>
      BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.1)
      ((Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
        (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z'))) (nhds z) :=
    Filter.tendsto_comap.comp Filter.tendsto_fst
  have h2 : Filter.Tendsto (fun q : Bloc p F ϖ × Bloc p F ϖ =>
      BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.2)
      ((Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
        (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z'))) (nhds z') :=
    Filter.tendsto_comap.comp Filter.tendsto_snd
  have hsum := h1.add h2
  have hcongr : (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        ∘ (fun q : Bloc p F ϖ × Bloc p F ϖ => q.1 + q.2)
      = fun q : Bloc p F ϖ × Bloc p F ϖ =>
        BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.1
          + BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.2 := by
    funext q
    exact map_add _ _ _
  rw [hcongr]
  exact hsum

/-- Approximants of a product are products of approximants (filter form). -/
theorem map_mul_comap_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (z z' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    Filter.map (fun q : Bloc p F ϖ × Bloc p F ϖ => q.1 * q.2)
        ((Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
          (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z')))
      ≤ Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds (z * z')) := by
  rw [← Filter.map_le_iff_le_comap, Filter.map_map]
  have h1 : Filter.Tendsto (fun q : Bloc p F ϖ × Bloc p F ϖ =>
      BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.1)
      ((Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
        (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z'))) (nhds z) :=
    Filter.tendsto_comap.comp Filter.tendsto_fst
  have h2 : Filter.Tendsto (fun q : Bloc p F ϖ × Bloc p F ϖ =>
      BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.2)
      ((Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z)) ×ˢ
        (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z'))) (nhds z') :=
    Filter.tendsto_comap.comp Filter.tendsto_snd
  have hmul := h1.mul h2
  have hcongr : (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        ∘ (fun q : Bloc p F ϖ × Bloc p F ϖ => q.1 * q.2)
      = fun q : Bloc p F ϖ × Bloc p F ϖ =>
        BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.1
          * BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 q.2 := by
    funext q
    exact map_mul _ _ _
  rw [hcongr]
  exact hmul

set_option maxHeartbeats 1000000 in
/-- **The restriction map is additive.** -/
theorem resI_add {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    {z z' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hz' : z' ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 (z + z')
      = resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z
        + resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z' := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  haveI hne' := neBot_comap_of_mem_BISub p F ϖ hz'
  have h1 := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 hz
  have h2 := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 hz'
  have hsum := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 (add_mem hz hz')
  have ha := (h1.comp Filter.tendsto_fst).add (h2.comp Filter.tendsto_snd)
  have hb := hsum.comp (map_add_comap_le p F ϖ z z')
  have hcongr : (fun y => BlocToHatK p F ϖ hmid0 hmid1 y)
        ∘ (fun q : Bloc p F ϖ × Bloc p F ϖ => q.1 + q.2)
      = fun q : Bloc p F ϖ × Bloc p F ϖ =>
        BlocToHatK p F ϖ hmid0 hmid1 q.1 + BlocToHatK p F ϖ hmid0 hmid1 q.2 := by
    funext q
    exact map_add _ _ _
  rw [hcongr] at hb
  exact tendsto_nhds_unique hb ha

set_option maxHeartbeats 1000000 in
/-- **The restriction map is multiplicative.** -/
theorem resI_mul {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    {z z' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hz' : z' ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 (z * z')
      = resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z
        * resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z' := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  haveI hne' := neBot_comap_of_mem_BISub p F ϖ hz'
  have h1 := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 hz
  have h2 := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 hz'
  have hprod := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 (mul_mem hz hz')
  have ha := (h1.comp Filter.tendsto_fst).mul (h2.comp Filter.tendsto_snd)
  have hb := hprod.comp (map_mul_comap_le p F ϖ z z')
  have hcongr : (fun y => BlocToHatK p F ϖ hmid0 hmid1 y)
        ∘ (fun q : Bloc p F ϖ × Bloc p F ϖ => q.1 * q.2)
      = fun q : Bloc p F ϖ × Bloc p F ϖ =>
        BlocToHatK p F ϖ hmid0 hmid1 q.1 * BlocToHatK p F ϖ hmid0 hmid1 q.2 := by
    funext q
    exact map_mul _ _ _
  rw [hcongr] at hb
  exact tendsto_nhds_unique hb ha

set_option maxHeartbeats 1000000 in
/-- **The restriction lands in the sub-interval ring**: for `z ∈ B^I` and two
intermediate radii, the pair of restrictions lies in the corresponding interval ring
`B^{I'}`. -/
theorem resI_pair_mem {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ η : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (hσ₂0 : 0 < ρ₁ ^ η * ρ₂ ^ (1 - η)) (hσ₂1 : ρ₁ ^ η * ρ₂ ^ (1 - η) < 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 z,
        resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₂0 hσ₂1 z)
      ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  have h1 := tendsto_resI p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 hz
  have h2 := tendsto_resI p F ϖ hη0 hη1 hσ₂0 hσ₂1 hz
  have hpair : Filter.Tendsto (fun x => (BlocToHatK p F ϖ hσ₁0 hσ₁1 x,
        BlocToHatK p F ϖ hσ₂0 hσ₂1 x))
      (Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z))
      (nhds (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 z,
        resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₂0 hσ₂1 z)) :=
    Filter.Tendsto.prodMk_nhds h1 h2
  have hmem : ∀ᶠ x in Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z),
      (BlocToHatK p F ϖ hσ₁0 hσ₁1 x, BlocToHatK p F ϖ hσ₂0 hσ₂1 x)
        ∈ (Set.range (BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)) :=
    Filter.Eventually.of_forall fun x => ⟨x, rfl⟩
  exact mem_closure_of_tendsto hpair hmem

set_option maxHeartbeats 1000000 in
/-- **The restriction ring homomorphism** `B^I → B^{I'}` (Kedlaya Corollary 4.6): the
unique continuous ring map extending the identity on `Bloc`. -/
def resIHom {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ η : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (hσ₂0 : 0 < ρ₁ ^ η * ρ₂ ^ (1 - η)) (hσ₂1 : ρ₁ ^ η * ρ₂ ^ (1 - η) < 1) :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) where
  toFun z := ⟨(resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 (z : _),
      resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₂0 hσ₂1 (z : _)),
    resI_pair_mem p F ϖ hθ0 hθ1 hη0 hη1 hσ₁0 hσ₁1 hσ₂0 hσ₂1 z.2⟩
  map_one' := by
    have hone : ((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 1 := by
      rw [map_one]
      rfl
    have e1 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
        ((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 1 := by
      rw [hone, resI_BIProd p F ϖ hθ0 hθ1 hσ₁0 hσ₁1, map_one]
    have e2 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₂0 hσ₂1
        ((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 1 := by
      rw [hone, resI_BIProd p F ϖ hη0 hη1 hσ₂0 hσ₂1, map_one]
    refine Subtype.ext ?_
    rw [show ((1 : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) = (1, 1) from rfl]
    exact Prod.ext e1 e2
  map_mul' := fun z z' => by
    have hcoe : ((z * z' : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) * (z' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := rfl
    have e1 := resI_mul p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2 z'.2
    have e2 := resI_mul p F ϖ hη0 hη1 hσ₂0 hσ₂1 z.2 z'.2
    refine Subtype.ext ?_
    exact Prod.ext e1 e2
  map_zero' := by
    have hzero : ((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 0 := by
      rw [map_zero]
      rfl
    have e1 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
        ((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 0 := by
      rw [hzero, resI_BIProd p F ϖ hθ0 hθ1 hσ₁0 hσ₁1, map_zero]
    have e2 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₂0 hσ₂1
        ((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 0 := by
      rw [hzero, resI_BIProd p F ϖ hη0 hη1 hσ₂0 hσ₂1, map_zero]
    refine Subtype.ext ?_
    rw [show ((0 : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)) = (0, 0) from rfl]
    exact Prod.ext e1 e2
  map_add' := fun z z' => by
    have hcoe : ((z + z' : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) + (z' : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := rfl
    have e1 := resI_add p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2 z'.2
    have e2 := resI_add p F ϖ hη0 hη1 hσ₂0 hσ₂1 z.2 z'.2
    refine Subtype.ext ?_
    exact Prod.ext e1 e2

/-- **The interval norm is power-multiplicative** (Kedlaya Definition 4.2): it is the
maximum of two multiplicative valuations, and taking maxima commutes with powers. -/
theorem wI_pow {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) (n : ℕ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z ^ n) = (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ^ n := by
  rw [wI, wI]
  have h1 : (z ^ n).1 = z.1 ^ n := rfl
  have h2 : (z ^ n).2 = z.2 ^ n := rfl
  rw [h1, h2, Valuation.map_pow, Valuation.map_pow]
  rcases le_total (Valued.v z.1) (Valued.v z.2) with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ zero_le h n)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ zero_le h n)]

/-- The interval norm of a natural power of a `B^{I,+}` element stays bounded by one
(restated through `wI_pow`). -/
theorem wI_pow_eq_one_iff {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) {n : ℕ} (hn : n ≠ 0) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z ^ n) ≤ 1
      ↔ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ 1 := by
  rw [wI_pow]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hlt : (1 : NNReal) < (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ^ n := by
      calc (1 : NNReal) = 1 ^ n := (one_pow n).symm
        _ < (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ^ n :=
            pow_lt_pow_left₀ hcon zero_le hn
    exact absurd (lt_of_lt_of_le hlt h) (lt_irrefl _)
  · intro h
    calc (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ^ n ≤ 1 ^ n :=
          pow_le_pow_left₀ zero_le h n
      _ = 1 := one_pow n

/-- The Gauss value of `p` is the radius. -/
theorem gaussValue_p {ρ : NNReal} (hρ1 : ρ ≤ 1) :
    gaussValue p F ρ ((p : Ainf p F)) = ρ := by
  calc gaussValue p F ρ ((p : Ainf p F))
      = gaussValue p F ρ ((p : Ainf p F) * 1) := by rw [mul_one]
    _ = ρ * gaussValue p F ρ 1 := gaussValue_p_mul p F hρ1 1
    _ = ρ := by rw [gaussValue_one p F hρ1, mul_one]

/-- **The interval norm of `p`** is the larger endpoint radius. -/
theorem wI_p_image {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
    {hρ₂1 : ρ₂ < 1} :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)))
      = max ρ₁ ρ₂ := by
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK, wLoc_algebraMap,
    wLoc_algebraMap, gaussValue_p p F hρ₁1.le, gaussValue_p p F hρ₂1.le]

/-- **`p` is a unit in the interval ring.** -/
theorem isUnit_p_BIProd {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsUnit (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F))) :=
  (isUnit_p_image p F ϖ).map (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)

/-- **`p` is topologically nilpotent in the interval ring**: its powers have vanishing
interval norm. -/
theorem tendsto_wI_p_pow {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    Filter.Tendsto (fun n : ℕ => wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F))) ^ n))
      Filter.atTop (nhds 0) := by
  have hval : ∀ n : ℕ, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F))) ^ n)
      = (max ρ₁ ρ₂) ^ n := by
    intro n
    rw [wI_pow, wI_p_image]
  have hmax1 : max ρ₁ ρ₂ < 1 := max_lt hρ₁1 hρ₂1
  refine Filter.Tendsto.congr (fun n => (hval n).symm) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hmax1

/-- **Closed value balls are closed** in the completed field. -/
theorem isClosed_valued_ball {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal}
    (hc : 0 < c) : IsClosed {w : hatK p F hρ0 hρ1 | Valued.v w ≤ c} := by
  set G : AddSubgroup (hatK p F hρ0 hρ1) :=
    { carrier := {w : hatK p F hρ0 hρ1 | Valued.v w ≤ c}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Valuation.map_zero]
        exact zero_le
      add_mem' := fun {a b} ha hb => by
        have h1 : Valued.v a ≤ c := ha
        have h2 : Valued.v b ≤ c := hb
        show Valued.v (a + b) ≤ c
        exact le_trans (Valuation.map_add _ a b) (max_le h1 h2)
      neg_mem' := fun {a} ha => by
        simpa only [Set.mem_setOf_eq, Valuation.map_neg] using ha } with hG
  have hopen : IsOpen (G : Set (hatK p F hρ0 hρ1)) := by
    refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
    exact valued_ball_mem_nhds_zero p F (hρ0 := hρ0) (hρ1 := hρ1) hc
  exact AddSubgroup.isClosed_of_isOpen G hopen

/-- **Interval-norm balls are closed** in the product. -/
theorem isClosed_wI_ball {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {c : NNReal} (hc : 0 < c) :
    IsClosed {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c} := by
  have hset : {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
        wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c}
      = ((fun z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => z.1)
          ⁻¹' {w : hatK p F hρ₁0 hρ₁1 | Valued.v w ≤ c})
        ∩ ((fun z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => z.2)
          ⁻¹' {w : hatK p F hρ₂0 hρ₂1 | Valued.v w ≤ c}) := by
    ext z
    constructor
    · intro hz
      have hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c := hz
      refine ⟨?_, ?_⟩
      · show Valued.v z.1 ≤ c
        exact le_trans (le_max_left _ _) hb
      · show Valued.v z.2 ≤ c
        exact le_trans (le_max_right _ _) hb
    · rintro ⟨h1, h2⟩
      have hb1 : Valued.v z.1 ≤ c := h1
      have hb2 : Valued.v z.2 ≤ c := h2
      show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c
      exact max_le hb1 hb2
  rw [hset]
  exact IsClosed.inter (isClosed_valued_ball p F hc |>.preimage continuous_fst)
    (isClosed_valued_ball p F hc |>.preimage continuous_snd)

/-- **Norm bounds pass to limits**: an element approximated by `Bloc`-elements of
interval norm at most `c` has interval norm at most `c`. -/
theorem wI_le_of_approx {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) {c : NNReal} (hc : 0 < c)
    (hall : ∀ x : Bloc p F ϖ,
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) ≤ c) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c := by
  have hz' : z ∈ closure (Set.range (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := hz
  have hsub : (Set.range (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      ⊆ {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
        wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ c} := by
    rintro w ⟨x, rfl⟩
    exact hall x
  have hcl := closure_mono hsub hz'
  rwa [(isClosed_wI_ball p F hc).closure_eq] at hcl

/-- **`B^{I,+}` is closed**, hence complete. -/
theorem isClosed_BIPlus {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsClosed (BIPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := by
  have hcarrier : (BIPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      = (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
        ∩ {z | wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ 1} := rfl
  rw [hcarrier]
  exact IsClosed.inter (isClosed_BISub p F ϖ) (isClosed_wI_ball p F zero_lt_one)

/-- `B^{I,+}` is complete. -/
theorem isComplete_BIPlus {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsComplete (BIPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) :=
  (isClosed_BIPlus p F ϖ).isComplete

set_option maxHeartbeats 1000000 in
/-- **The restriction map is norm-nonincreasing** (Kedlaya Corollary 4.5 at the level
of the completion). -/
theorem valued_resI_le_wI {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmid0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hmid1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z)
      ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  have hlim := tendsto_resI p F ϖ hθ0 hθ1 hmid0 hmid1 hz
  -- for every ε, the approximant images sit in the (wI z ⊔ ε)-ball
  have hstep : ∀ ε : NNReal, 0 < ε →
      Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmid0 hmid1 z)
        ≤ max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ε := by
    intro ε hε
    set c : NNReal := max (wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ε with hcdef
    have hc0 : 0 < c := lt_of_lt_of_le hε (le_max_right _ _)
    refine (isClosed_valued_ball p F hc0).mem_of_tendsto hlim ?_
    have hcomap : ∀ᶠ x in Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (nhds z),
        wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z) ≤ ε := by
      refine Filter.eventually_comap.mpr
        (Filter.Eventually.mono (wI_ball_mem_nhds p F z hε) ?_)
      intro w hw x hx
      rw [hx]
      exact hw
    refine Filter.Eventually.mono hcomap ?_
    intro x hx
    have hball : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z) ≤ ε := hx
    have hxnorm : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) ≤ c := by
      have hsplit : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          = (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x - z) + z := by ring
      rw [hsplit]
      refine le_trans (wI_add_le p F _ _) ?_
      exact max_le (le_trans hball (le_max_right _ _)) (le_max_left _ _)
    exact le_trans (valued_BlocToHatK_le_wI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0 hθ1 hmid0 hmid1 x) hxnorm
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hd1, hd2⟩ := exists_between hcon
  have hdpos : 0 < d := lt_of_le_of_lt zero_le hd1
  have hle := hstep d hdpos
  rw [max_eq_right hd1.le] at hle
  exact absurd (lt_of_le_of_lt hle hd2) (lt_irrefl _)

/-- The image of `p` in the product, as an element. -/
def pImage {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
    (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F))

/-- The two coordinates of `p` have the endpoint radii as values. -/
theorem valued_pImage_fst {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    Valued.v (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1 = ρ₁ := by
  rw [pImage, BIProd_fst, valued_BlocToHatK, wLoc_algebraMap,
    gaussValue_p p F hρ₁1.le]

theorem valued_pImage_snd {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    Valued.v (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2 = ρ₂ := by
  rw [pImage, BIProd_snd, valued_BlocToHatK, wLoc_algebraMap,
    gaussValue_p p F hρ₂1.le]

/-- **Scaling up**: multiplying by `pⁿ` shrinks the norm by at least `(max ρ₁ ρ₂)ⁿ`. -/
theorem wI_p_pow_mul_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (n : ℕ)
    (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * z)
      ≤ (max ρ₁ ρ₂) ^ n * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z := by
  refine le_trans (wI_mul_le p F _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  rw [wI_pow, pImage, wI_p_image]

/-- **Scaling down**: an element of norm at most `(min ρ₁ ρ₂)ⁿ` is `pⁿ` times an
element of the unit ball — the second half of the adic sandwich. -/
theorem exists_eq_p_pow_mul {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (n : ℕ)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz1 : Valued.v z.1 ≤ ρ₁ ^ n) (hz2 : Valued.v z.2 ≤ ρ₂ ^ n) :
    ∃ w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1),
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ 1
        ∧ z = (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * w := by
  obtain ⟨u, hu⟩ := isUnit_p_BIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
  have hupow : IsUnit ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n) := by
    rw [pImage, ← hu]
    exact (u.isUnit).pow n
  obtain ⟨v, hv⟩ := hupow
  set V : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) := (v : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) with hVdef
  set W : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) := ((v⁻¹ : ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))ˣ) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) with hWdef
  have hVW : V * W = 1 := v.mul_inv
  have hc1 : V.1 * W.1 = 1 := congrArg Prod.fst hVW
  have hc2 : V.2 * W.2 = 1 := congrArg Prod.snd hVW
  have hV1 : Valued.v V.1 = ρ₁ ^ n := by
    have hproj : V.1 = (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1 ^ n := by
      rw [hVdef]
      exact congrArg Prod.fst hv
    rw [hproj, Valuation.map_pow, valued_pImage_fst]
  have hV2 : Valued.v V.2 = ρ₂ ^ n := by
    have hproj : V.2 = (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2 ^ n := by
      rw [hVdef]
      exact congrArg Prod.snd hv
    rw [hproj, Valuation.map_pow, valued_pImage_snd]
  have hW1 : Valued.v W.1 = (ρ₁ ^ n)⁻¹ := by
    have hmul := congrArg (fun t => Valued.v t) hc1
    simp only [Valuation.map_mul, Valuation.map_one, hV1] at hmul
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  have hW2 : Valued.v W.2 = (ρ₂ ^ n)⁻¹ := by
    have hmul := congrArg (fun t => Valued.v t) hc2
    simp only [Valuation.map_mul, Valuation.map_one, hV2] at hmul
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  refine ⟨W * z, ?_, ?_⟩
  · refine max_le ?_ ?_
    · rw [show (W * z).1 = W.1 * z.1 from rfl, Valuation.map_mul, hW1]
      rw [inv_mul_le_iff₀ (pow_pos hρ₁0 n), mul_one]
      exact hz1
    · rw [show (W * z).2 = W.2 * z.2 from rfl, Valuation.map_mul, hW2]
      rw [inv_mul_le_iff₀ (pow_pos hρ₂0 n), mul_one]
      exact hz2
  · have h : (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * W = 1 := by
      rw [← hv]
      exact hVW
    calc z = 1 * z := (one_mul z).symm
      _ = ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * W) * z := by rw [h]
      _ = (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * (W * z) := by rw [mul_assoc]

/-- **Closed value balls are open** in the completed field (they are additive
subgroups containing a neighborhood of `0`). -/
theorem isOpen_valued_ball {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal}
    (hc : 0 < c) : IsOpen {w : hatK p F hρ0 hρ1 | Valued.v w ≤ c} := by
  set G : AddSubgroup (hatK p F hρ0 hρ1) :=
    { carrier := {w : hatK p F hρ0 hρ1 | Valued.v w ≤ c}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Valuation.map_zero]
        exact zero_le
      add_mem' := fun {a b} ha hb => by
        have h1 : Valued.v a ≤ c := ha
        have h2 : Valued.v b ≤ c := hb
        show Valued.v (a + b) ≤ c
        exact le_trans (Valuation.map_add _ a b) (max_le h1 h2)
      neg_mem' := fun {a} ha => by
        simpa only [Set.mem_setOf_eq, Valuation.map_neg] using ha } with hG
  refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
  exact valued_ball_mem_nhds_zero p F (hρ0 := hρ0) (hρ1 := hρ1) hc

/-- **Interval-norm balls are open** in the product. -/
theorem isOpen_wI_ball {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {c : NNReal} (hc : 0 < c) :
    IsOpen {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c} := by
  have hset : {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
        wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c}
      = ((fun z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => z.1)
          ⁻¹' {w : hatK p F hρ₁0 hρ₁1 | Valued.v w ≤ c})
        ∩ ((fun z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => z.2)
          ⁻¹' {w : hatK p F hρ₂0 hρ₂1 | Valued.v w ≤ c}) := by
    ext z
    constructor
    · intro hz
      have hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c := hz
      exact ⟨le_trans (le_max_left _ _) hb, le_trans (le_max_right _ _) hb⟩
    · rintro ⟨h1, h2⟩
      have hb1 : Valued.v z.1 ≤ c := h1
      have hb2 : Valued.v z.2 ≤ c := h2
      show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ c
      exact max_le hb1 hb2
  rw [hset]
  exact IsOpen.inter ((isOpen_valued_ball p F hc).preimage continuous_fst)
    ((isOpen_valued_ball p F hc).preimage continuous_snd)

/-- **The `pⁿ`-multiples of the unit ball are exactly the two-coordinate ball**
(the set-level heart of the adic sandwich). -/
theorem p_pow_smul_ball_eq {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (n : ℕ) :
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
        ∃ w, wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ 1
          ∧ z = (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * w}
      = {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
        Valued.v z.1 ≤ ρ₁ ^ n ∧ Valued.v z.2 ≤ ρ₂ ^ n} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : Valued.v w.1 ≤ 1 := le_trans (le_max_left _ _) hw
    have h2 : Valued.v w.2 ≤ 1 := le_trans (le_max_right _ _) hw
    constructor
    · rw [show ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * w).1
        = ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1) ^ n * w.1 from rfl,
        Valuation.map_mul, Valuation.map_pow, valued_pImage_fst]
      calc ρ₁ ^ n * Valued.v w.1 ≤ ρ₁ ^ n * 1 :=
            mul_le_mul_of_nonneg_left h1 zero_le
        _ = ρ₁ ^ n := mul_one _
    · rw [show ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n * w).2
        = ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2) ^ n * w.2 from rfl,
        Valuation.map_mul, Valuation.map_pow, valued_pImage_snd]
      calc ρ₂ ^ n * Valued.v w.2 ≤ ρ₂ ^ n * 1 :=
            mul_le_mul_of_nonneg_left h2 zero_le
        _ = ρ₂ ^ n := mul_one _
  · rintro ⟨h1, h2⟩
    exact exists_eq_p_pow_mul p F ϖ n h1 h2

/-- **`B^{I,+}` as a subring of `B^I`** — the ring of definition. -/
def BIPlusIn {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : Subring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  Subring.comap (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).subtype
    (BIPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)

theorem mem_BIPlusIn_iff {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)} :
    z ∈ BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ↔ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ 1 :=
  ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩

/-- **The ring of definition is open**: `B^{I,+}` is the unit ball of `λ_I`, hence open. -/
theorem isOpen_BIPlusIn {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsOpen (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      : Set ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  have hset : (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        : Set ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = (fun z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) =>
          (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
        ⁻¹' {z | wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ 1} := by
    ext z
    exact mem_BIPlusIn_iff p F ϖ
  rw [hset]
  exact (isOpen_wI_ball p F zero_lt_one).preimage continuous_subtype_val

/-- The inverse of `p` in the interval ring. -/
def pInvImage {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) :=
  BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ↑(isUnit_p_image p F ϖ).unit⁻¹

theorem pImage_mul_pInvImage {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 * pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 = 1 := by
  rw [pImage, pInvImage, ← map_mul]
  have hmul : algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)
      * ↑(isUnit_p_image p F ϖ).unit⁻¹ = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.mul_inv
    rwa [(isUnit_p_image p F ϖ).unit_spec] at h
  rw [hmul]
  exact map_one _

theorem valued_pInvImage_fst {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    Valued.v (pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1 = ρ₁⁻¹ := by
  rw [pInvImage, BIProd_fst, valued_BlocToHatK]
  exact wLoc_p_inv p F ϖ hρ₁0 hρ₁1

theorem valued_pInvImage_snd {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    Valued.v (pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2 = ρ₂⁻¹ := by
  rw [pInvImage, BIProd_snd, valued_BlocToHatK]
  exact wLoc_p_inv p F ϖ hρ₂0 hρ₂1

theorem pInvImage_mem_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
  BIProd_mem_BISub p F ϖ _


/-- `p`, as an element of `B^I`. -/
def pEltB {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  ⟨pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1, BIProd_mem_BISub p F ϖ _⟩

theorem pEltB_mem_BIPlusIn {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ∈ BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  rw [mem_BIPlusIn_iff]
  show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ≤ 1
  rw [pImage, wI_p_image]
  exact max_le hρ₁1.le hρ₂1.le

/-- `p`, as an element of the ring of definition `B^{I,+}`. -/
def pEltPlus {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  ⟨pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1, pEltB_mem_BIPlusIn p F ϖ⟩

/-- **The ideal of definition** `(p) ⊆ B^{I,+}`. -/
def pIdeal {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : Ideal ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  Ideal.span {pEltPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1}

theorem pIdeal_fg {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    (pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).FG :=
  ⟨{pEltPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1}, by rw [pIdeal, Finset.coe_singleton]⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The powers of the ideal of definition are exactly the balls**: `y ∈ (p)ⁿ` iff both
coordinates of `y` have value at most `ρᵢⁿ`. This is the identification of the `p`-adic
topology on `B^{I,+}` with its subspace topology. -/
theorem mem_pIdeal_pow_iff {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (n : ℕ)
    (y : ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    y ∈ (pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
      ↔ Valued.v ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 ≤ ρ₁ ^ n
        ∧ Valued.v ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 ≤ ρ₂ ^ n := by
  have hspan : (pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
      = Ideal.span {pEltPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ n} := by
    rw [pIdeal, Ideal.span_singleton_pow]
  rw [hspan, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, rfl⟩
    have hcoe : (((b * pEltPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ n :
          ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
          (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = ((b : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n := by
      push_cast
      rfl
    have hb1 : Valued.v ((b : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 ≤ 1 :=
      le_trans (le_max_left _ _) ((mem_BIPlusIn_iff p F ϖ).mp b.2)
    have hb2 : Valued.v ((b : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 ≤ 1 :=
      le_trans (le_max_right _ _) ((mem_BIPlusIn_iff p F ϖ).mp b.2)
    rw [hcoe]
    constructor
    · show Valued.v (_ * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1 ^ n) ≤ ρ₁ ^ n
      rw [Valuation.map_mul, Valuation.map_pow, valued_pImage_fst]
      calc Valued.v ((b : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
              (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 * ρ₁ ^ n
          ≤ 1 * ρ₁ ^ n := mul_le_mul_of_nonneg_right hb1 zero_le
        _ = ρ₁ ^ n := one_mul _
    · show Valued.v (_ * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2 ^ n) ≤ ρ₂ ^ n
      rw [Valuation.map_mul, Valuation.map_pow, valued_pImage_snd]
      calc Valued.v ((b : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
              (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 * ρ₂ ^ n
          ≤ 1 * ρ₂ ^ n := mul_le_mul_of_nonneg_right hb2 zero_le
        _ = ρ₂ ^ n := one_mul _
  · rintro ⟨h1, h2⟩
    have hmemS : (pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
        * ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
      mul_mem (pow_mem (pInvImage_mem_BISub p F ϖ) n)
        (y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)).2
    have hw1 : Valued.v (((pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
        * ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))).1) ≤ 1 := by
      show Valued.v ((pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1 ^ n * _) ≤ 1
      rw [Valuation.map_mul, Valuation.map_pow, valued_pInvImage_fst]
      calc (ρ₁⁻¹) ^ n * Valued.v ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
              (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
          ≤ (ρ₁⁻¹) ^ n * ρ₁ ^ n := mul_le_mul_of_nonneg_left h1 zero_le
        _ = 1 := by
            rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero n hρ₁0.ne')]
    have hw2 : Valued.v (((pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
        * ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
            (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))).2) ≤ 1 := by
      show Valued.v ((pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2 ^ n * _) ≤ 1
      rw [Valuation.map_mul, Valuation.map_pow, valued_pInvImage_snd]
      calc (ρ₂⁻¹) ^ n * Valued.v ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
              (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
          ≤ (ρ₂⁻¹) ^ n * ρ₂ ^ n := mul_le_mul_of_nonneg_left h2 zero_le
        _ = 1 := by
            rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero n hρ₂0.ne')]
    refine ⟨⟨⟨_, hmemS⟩, ?_⟩, ?_⟩
    · rw [mem_BIPlusIn_iff]
      exact max_le hw1 hw2
    · refine Subtype.ext (Subtype.ext ?_)
      show (pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
          * ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
              (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n = _
      calc (pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
            * ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
                (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ n
          = ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
              * (pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) ^ n
            * ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
                (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
            rw [mul_pow]; ring
        _ = _ := by rw [pImage_mul_pInvImage, one_pow, one_mul]


/-- Every neighbourhood of `0` in the product contains an interval-norm ball. -/
theorem exists_wI_ball_subset {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {s : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
    (hs : s ∈ nhds (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) :
    ∃ ε : NNReal, 0 < ε ∧ {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ ε} ⊆ s := by
  rw [show (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = (0, 0) from rfl,
    nhds_prod_eq] at hs
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.mp hs
  obtain ⟨ε₁, hε₁, hball₁⟩ := exists_valued_ball_subset p F ht₁
  obtain ⟨ε₂, hε₂, hball₂⟩ := exists_valued_ball_subset p F ht₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz => ?_⟩
  have hz' : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z ≤ min ε₁ ε₂ := hz
  refine hsub ⟨hball₁ ?_, hball₂ ?_⟩
  · exact le_trans (le_trans (le_max_left _ _) hz') (min_le_left _ _)
  · exact le_trans (le_trans (le_max_right _ _) hz') (min_le_right _ _)

/-- The two-coordinate closed ball is open in the product. -/
theorem isOpen_coord_ball {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {c₁ c₂ : NNReal} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    IsOpen {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      Valued.v z.1 ≤ c₁ ∧ Valued.v z.2 ≤ c₂} := by
  have hset : {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
        Valued.v z.1 ≤ c₁ ∧ Valued.v z.2 ≤ c₂}
      = ((fun z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => z.1)
          ⁻¹' {w : hatK p F hρ₁0 hρ₁1 | Valued.v w ≤ c₁})
        ∩ ((fun z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) => z.2)
          ⁻¹' {w : hatK p F hρ₂0 hρ₂1 | Valued.v w ≤ c₂}) := rfl
  rw [hset]
  exact IsOpen.inter ((isOpen_valued_ball p F hc₁).preimage continuous_fst)
    ((isOpen_valued_ball p F hc₂).preimage continuous_snd)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The subspace topology on `B^{I,+}` is the `p`-adic topology** — the key property
of the pair of definition `(B^{I,+}, (p))`. -/
theorem isAdic_pIdeal {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsAdic (pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) := by
  rw [isAdic_iff]
  constructor
  · intro n
    have hset : ((pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ n :
          Ideal ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : Set ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        = (fun y : ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) =>
            ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
              (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
          ⁻¹' {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
            Valued.v z.1 ≤ ρ₁ ^ n ∧ Valued.v z.2 ≤ ρ₂ ^ n} := by
      ext y
      exact mem_pIdeal_pow_iff p F ϖ n y
    rw [hset]
    exact (isOpen_coord_ball p F (pow_pos hρ₁0 n) (pow_pos hρ₂0 n)).preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  · intro s hs
    obtain ⟨u, hu, husub⟩ := mem_nhds_subtype _
      (0 : ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) s |>.mp hs
    obtain ⟨w, hw, hwsub⟩ := mem_nhds_subtype _
      (0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) u |>.mp hu
    obtain ⟨ε, hε, hεsub⟩ := exists_wI_ball_subset p F (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hw
    obtain ⟨N, hN⟩ := _root_.exists_pow_lt_of_lt_one hε (max_lt hρ₁1 hρ₂1)
    refine ⟨N, fun y hy => ?_⟩
    obtain ⟨hy1, hy2⟩ := (mem_pIdeal_pow_iff p F ϖ N y).mp hy
    have hball : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((y : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
          (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ ε := by
      refine max_le (le_trans hy1 ?_) (le_trans hy2 ?_)
      · exact le_trans (pow_le_pow_left₀ zero_le (le_max_left _ _) N) hN.le
      · exact le_trans (pow_le_pow_left₀ zero_le (le_max_right _ _) N) hN.le
    exact husub (hwsub (hεsub hball))

/-- **The pair of definition `(B^{I,+}, (p))` for the interval ring `B^I`**
(Kedlaya Definition 4.2 / Lemma 4.4). -/
def BIPairOfDefinition {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : PairOfDefinition ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  A₀ := BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  I := pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  isOpen := isOpen_BIPlusIn p F ϖ
  fg := pIdeal_fg p F ϖ
  isAdic := isAdic_pIdeal p F ϖ

/-- **`B^I` is a Huber ring.** -/
instance isHuberRing_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsHuberRing ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  exists_pairOfDefinition := ⟨BIPairOfDefinition p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1⟩

/-- `p` is a unit of `B^I`. -/
def pUnit {ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂)
    (hρ₂1 : ρ₂ < 1) : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ where
  val := pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  inv := ⟨pInvImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1, pInvImage_mem_BISub p F ϖ⟩
  val_inv := Subtype.ext (pImage_mul_pInvImage p F ϖ)
  inv_val := Subtype.ext (by
    rw [mul_comm]
    exact pImage_mul_pInvImage p F ϖ)

/-- **`B^I` is a Tate ring**: `p` is a topologically nilpotent unit. -/
instance isTateRing_BISub {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
    {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} :
    IsTateRing ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  exists_topologicallyNilpotent_unit := by
    refine ⟨pUnit p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1, ?_⟩
    exact (BIPairOfDefinition p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).isTopologicallyNilpotent_of_mem
      (a := pEltPlus p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (Ideal.mem_span_singleton_self _)

end FarguesFontaine

end
