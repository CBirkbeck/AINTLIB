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

end FarguesFontaine

end
