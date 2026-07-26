/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

open TopologicalRing ValuationSpectrum WittVector

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

end FarguesFontaine

end
