/-
Copyright (c) 2026 the AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.UniformizerEquivariance
import Mathlib.RingTheory.WittVector.InitTail

/-!
# Splitting and endpoint projections for the interval rings

The two halves of the split fiber-product theorem for `B^I` (the sheaf
condition of the `Y`-presheaf on a split interval, Kedlaya-style):

* **Endpoint projections** `biFstQ`/`biSndQ` of the rational-exponent interval
  ring `BIQ q₁ q₂` into the completed endpoint fields, with the dense-layer
  identities and the three restriction laws (shared-left, shared-right, middle
  match). Consequence: `biResQ_split_injective` — an element of `B^{[q₁,q₂]}`
  is determined by its restrictions to the two halves `[q₁,r]`, `[r,q₂]`.

* **The Mittag-Leffler splitting** `exists_wLoc_split`: every element of
  `Bloc` splits at a threshold radius `τ` as `zP + zM` where the tail part
  `zP` is `τ`-controlled at all radii `σ ≤ τ` and the principal part `zM` at
  all radii `σ ≥ τ` (via `WittVector.init`/`tail` truncation of a numerator
  and per-term comparison of the Gauss sup-norms).

* **The glued element** `biGlue` with `biResQ_split_surjective`: together
  with the separation above, the split fiber-product theorem
  `B^{[q₁,q₂]} ≅ B^{[q₁,r]} ×_{hatK τ} B^{[r,q₂]}` — the sheaf axiom of the
  interval presheaf on a two-piece closed cover.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- Teichmüller coordinates of the tail truncation. -/
theorem teichCoeff_tail (x : Ainf p F) (k n : ℕ) :
    teichCoeff p F (WittVector.tail k x) n
      = if k ≤ n then teichCoeff p F x n else 0 := by
  by_cases hn : k ≤ n <;>
    simp [teichCoeff, WittVector.tail, WittVector.select, hn]

/-- Teichmüller coordinates of the initial truncation. -/
theorem teichCoeff_init (x : Ainf p F) (k n : ℕ) :
    teichCoeff p F (WittVector.init k x) n
      = if n < k then teichCoeff p F x n else 0 := by
  by_cases hn : n < k <;>
    simp [teichCoeff, WittVector.init, WittVector.select, hn]

/-- **The tail bound** (Mittag-Leffler positive part): for radii `σ ≤ τ`, the
`σ`-Gauss value of the `k`-tail is controlled by the `τ`-Gauss value, with the
radius-ratio factor in multiplied form. -/
theorem pow_mul_gaussValue_tail_le {σ τ : NNReal} (hστ : σ ≤ τ) (hτ1 : τ ≤ 1)
    (x : Ainf p F) (k : ℕ) :
    τ ^ k * gaussValue p F σ (WittVector.tail k x)
      ≤ σ ^ k * gaussValue p F τ x := by
  rw [gaussValue, NNReal.mul_iSup]
  refine ciSup_le fun n => ?_
  by_cases hn : k ≤ n
  · have hterm : gaussTerm p F σ (WittVector.tail k x) n
        = σ ^ n * perfectoidValuation p F ((teichCoeff p F x n : F)) := by
      rw [gaussTerm, teichCoeff_tail, if_pos hn]
    rw [hterm]
    have hcore : τ ^ k * σ ^ n ≤ σ ^ k * τ ^ n := by
      have h1 : σ ^ n = σ ^ k * σ ^ (n - k) := by
        rw [← pow_add]
        congr 1
        omega
      have h2 : τ ^ n = τ ^ k * τ ^ (n - k) := by
        rw [← pow_add]
        congr 1
        omega
      calc τ ^ k * σ ^ n = σ ^ k * (τ ^ k * σ ^ (n - k)) := by rw [h1]; ring
        _ ≤ σ ^ k * (τ ^ k * τ ^ (n - k)) :=
            mul_le_mul_right (mul_le_mul_right (pow_le_pow_left' hστ _) _) _
        _ = σ ^ k * τ ^ n := by rw [h2]
    calc τ ^ k * (σ ^ n * perfectoidValuation p F ((teichCoeff p F x n : F)))
        = (τ ^ k * σ ^ n) * perfectoidValuation p F ((teichCoeff p F x n : F)) := by
          ring
      _ ≤ (σ ^ k * τ ^ n) * perfectoidValuation p F ((teichCoeff p F x n : F)) :=
          mul_le_mul_left hcore _
      _ = σ ^ k * gaussTerm p F τ x n := by rw [gaussTerm]; ring
      _ ≤ σ ^ k * gaussValue p F τ x :=
          mul_le_mul_right (le_ciSup (bddAbove_range_gaussTerm p F hτ1 x) n) _
  · have hterm : gaussTerm p F σ (WittVector.tail k x) n = 0 := by
      rw [gaussTerm, teichCoeff_tail, if_neg hn]
      simp
    rw [hterm, mul_zero]
    exact zero_le

/-- **The initial bound** (Mittag-Leffler principal part): for radii `τ ≤ σ`,
the `σ`-Gauss value of the `k`-initial part is controlled by the `τ`-Gauss
value. -/
theorem pow_mul_gaussValue_init_le {σ τ : NNReal} (hτσ : τ ≤ σ) (_hσ1 : σ ≤ 1)
    (hτ1 : τ ≤ 1) (x : Ainf p F) (k : ℕ) :
    τ ^ k * gaussValue p F σ (WittVector.init k x)
      ≤ σ ^ k * gaussValue p F τ x := by
  rw [gaussValue, NNReal.mul_iSup]
  refine ciSup_le fun n => ?_
  by_cases hn : n < k
  · have hterm : gaussTerm p F σ (WittVector.init k x) n
        = σ ^ n * perfectoidValuation p F ((teichCoeff p F x n : F)) := by
      rw [gaussTerm, teichCoeff_init, if_pos hn]
    rw [hterm]
    have hcore : τ ^ k * σ ^ n ≤ σ ^ k * τ ^ n := by
      have h1 : σ ^ k = σ ^ n * σ ^ (k - n) := by
        rw [← pow_add]
        congr 1
        omega
      have h2 : τ ^ k = τ ^ n * τ ^ (k - n) := by
        rw [← pow_add]
        congr 1
        omega
      calc τ ^ k * σ ^ n = (τ ^ (k - n) * σ ^ n) * τ ^ n := by rw [h2]; ring
        _ ≤ (σ ^ (k - n) * σ ^ n) * τ ^ n :=
            mul_le_mul_left (mul_le_mul_left (pow_le_pow_left' hτσ _) _) _
        _ = σ ^ k * τ ^ n := by rw [h1]; ring
    calc τ ^ k * (σ ^ n * perfectoidValuation p F ((teichCoeff p F x n : F)))
        = (τ ^ k * σ ^ n) * perfectoidValuation p F ((teichCoeff p F x n : F)) := by
          ring
      _ ≤ (σ ^ k * τ ^ n) * perfectoidValuation p F ((teichCoeff p F x n : F)) :=
          mul_le_mul_left hcore _
      _ = σ ^ k * gaussTerm p F τ x n := by rw [gaussTerm]; ring
      _ ≤ σ ^ k * gaussValue p F τ x :=
          mul_le_mul_right (le_ciSup (bddAbove_range_gaussTerm p F hτ1 x) n) _
  · have hterm : gaussTerm p F σ (WittVector.init k x) n = 0 := by
      rw [gaussTerm, teichCoeff_init, if_neg hn]
      simp
    rw [hterm, mul_zero]
    exact zero_le

/-- The two halves of the interval split obey the same estimate: if the numerator's Gauss
value satisfies `τᵏ·|w|_σ ≤ σᵏ·|x|_τ`, then `mk' w y` is `wLoc`-dominated by `mk' x y`.
Applied once with `w = tail k x` and once with `w = init k x`. -/
private lemma wLoc_mk'_le_of_pow_mul_le {τ σ : NNReal} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (x w : Ainf p F)
    (y : ↥(Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))) (k : ℕ)
    (hy : (y : Ainf p F) = ((p : Ainf p F) * teichPi p F ϖ) ^ k)
    (hbound : τ ^ k * gaussValue p F σ w ≤ σ ^ k * gaussValue p F τ x) :
    wLoc p F ϖ hσ0 hσ1 (IsLocalization.mk' (Bloc p F ϖ) w y)
      ≤ wLoc p F ϖ hτ0 hτ1 (IsLocalization.mk' (Bloc p F ϖ) x y) := by
  have hgy : ∀ (ν : NNReal) (hν0 : 0 < ν) (hν1 : ν < 1),
      gaussValue p F ν (y : Ainf p F)
        = (ν * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
    intro ν hν0 hν1
    rw [hy, show gaussValue p F ν (((p : Ainf p F) * teichPi p F ϖ) ^ k)
        = gaussVal p F hν0 hν1 (((p : Ainf p F) * teichPi p F ϖ) ^ k) from
      (gaussVal_apply p F hν0 hν1 _).symm, Valuation.map_pow, gaussVal_apply,
      gaussValue_p_teichPi p F ϖ hν1]
  have hgy_ne : ∀ (ν : NNReal) (hν0 : 0 < ν) (hν1 : ν < 1),
      gaussValue p F ν (y : Ainf p F) ≠ 0 := by
    intro ν hν0 hν1
    rw [hy, show gaussValue p F ν (((p : Ainf p F) * teichPi p F ϖ) ^ k)
        = gaussVal p F hν0 hν1 (((p : Ainf p F) * teichPi p F ϖ) ^ k) from
      (gaussVal_apply p F hν0 hν1 _).symm, Valuation.map_pow]
    exact pow_ne_zero k (by
      rw [gaussVal_apply]
      exact gaussValue_p_teichPi_ne_zero p F ϖ hν0 hν1)
  rw [wLoc_mk', wLoc_mk', hgy σ hσ0 hσ1, hgy τ hτ0 hτ1,
    ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff₀ (pos_iff_ne_zero.mpr (by
      rw [← hgy σ hσ0 hσ1]
      exact hgy_ne σ hσ0 hσ1)) (pos_iff_ne_zero.mpr (by
      rw [← hgy τ hτ0 hτ1]
      exact hgy_ne τ hτ0 hτ1))]
  rw [mul_pow, mul_pow]
  calc gaussValue p F σ w
        * (τ ^ k * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k)
      = (τ ^ k * gaussValue p F σ w)
          * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k := by ring
    _ ≤ (σ ^ k * gaussValue p F τ x)
          * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k :=
        mul_le_mul_left hbound _
    _ = gaussValue p F τ x
          * (σ ^ k * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k) := by ring


/-- **The Mittag-Leffler splitting of `Bloc`** at a threshold radius `τ`: every
`z` splits as `z = zP + zM` where `zP` is `τ`-controlled at all smaller radii
and `zM` at all larger radii. This is the analytic core of the interval-ring
gluing (Kedlaya-style decomposition of a Laurent-type element into its
`p`-positive tail and its principal part). -/
theorem exists_wLoc_split {τ : NNReal} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (z : Bloc p F ϖ) :
    ∃ zP zM : Bloc p F ϖ, z = zP + zM
      ∧ (∀ (σ : NNReal) (hσ0 : 0 < σ) (hσ1 : σ < 1), σ ≤ τ →
          wLoc p F ϖ hσ0 hσ1 zP ≤ wLoc p F ϖ hτ0 hτ1 z)
      ∧ (∀ (σ : NNReal) (hσ0 : 0 < σ) (hσ1 : σ < 1), τ ≤ σ →
          wLoc p F ϖ hσ0 hσ1 zM ≤ wLoc p F ϖ hτ0 hτ1 z) := by
  obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) z
  obtain ⟨k, hk⟩ := y.2
  have hzmk : z = IsLocalization.mk' (Bloc p F ϖ) x y :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hz
  have hy : (y : Ainf p F) = ((p : Ainf p F) * teichPi p F ϖ) ^ k := hk.symm
  refine ⟨IsLocalization.mk' (Bloc p F ϖ) (WittVector.tail k x) y,
    IsLocalization.mk' (Bloc p F ϖ) (WittVector.init k x) y, ?_, ?_, ?_⟩
  · rw [hzmk]
    rw [show IsLocalization.mk' (Bloc p F ϖ) (WittVector.tail k x) y
          + IsLocalization.mk' (Bloc p F ϖ) (WittVector.init k x) y
        = IsLocalization.mk' (Bloc p F ϖ)
            (WittVector.tail k x * ↑y + WittVector.init k x * ↑y) (y * y) from
      (IsLocalization.mk'_add _ _ _ _).symm]
    rw [show WittVector.tail k x * ↑y + WittVector.init k x * ↑y
        = x * ↑y by
      rw [← add_mul, add_comm, WittVector.init_add_tail],
      IsLocalization.mk'_cancel]
  · intro σ hσ0 hσ1 hστ
    rw [hzmk]
    exact wLoc_mk'_le_of_pow_mul_le p F ϖ hτ0 hτ1 hσ0 hσ1 x (WittVector.tail k x) y k hy
      (pow_mul_gaussValue_tail_le p F hστ hτ1.le x k)
  · intro σ hσ0 hσ1 hτσ
    rw [hzmk]
    exact wLoc_mk'_le_of_pow_mul_le p F ϖ hτ0 hτ1 hσ0 hσ1 x (WittVector.init k x) y k hy
      (pow_mul_gaussValue_init_le p F hτσ hσ1.le hτ1.le x k)
/-- **The left-endpoint projection** of the rational-exponent interval ring:
the component in the completed field at radius `|ϖ|^{q₁}`. -/
noncomputable def biFstQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)
      →+* hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁) where
  toFun w := (w : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
    × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂))).1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The right-endpoint projection** of the rational-exponent interval ring. -/
noncomputable def biSndQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)
      →+* hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) where
  toFun w := (w : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
    × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂))).2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem biFstQ_continuous (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    Continuous (biFstQ p F ϖ q₁ q₂ h₁ h₂) :=
  continuous_fst.comp continuous_subtype_val

theorem biSndQ_continuous (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    Continuous (biSndQ p F ϖ q₁ q₂ h₁ h₂) :=
  continuous_snd.comp continuous_subtype_val

/-- The left projection restricts to the completion map on the dense layer. -/
theorem biFstQ_blocToBI (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (z : Bloc p F ϖ) :
    biFstQ p F ϖ q₁ q₂ h₁ h₂
        (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z)
      = BlocToHatK p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁) z := by
  show (BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
      (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z).1 = _
  rw [BIProd_fst]

/-- The right projection restricts to the completion map on the dense layer. -/
theorem biSndQ_blocToBI (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (z : Bloc p F ϖ) :
    biSndQ p F ϖ q₁ q₂ h₁ h₂
        (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z)
      = BlocToHatK p F ϖ (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z := by
  show (BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
      (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z).2 = _
  rw [BIProd_snd]

/-- **Restriction preserves a shared left endpoint**: the `q₁`-component of the
restriction to `[q₁, r]` is the original `q₁`-component. -/
theorem biFstQ_biResQ_left (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) :
    (biFstQ p F ϖ q₁ r h₁ hr).comp
        (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm)
      = biFstQ p F ϖ q₁ q₂ h₁ h₂ := by
  have hfun : ⇑((biFstQ p F ϖ q₁ r h₁ hr).comp
      (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm))
      = ⇑(biFstQ p F ϖ q₁ q₂ h₁ h₂) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biFstQ_continuous p F ϖ q₁ r h₁ hr).comp
        (biResQ_continuous p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt
          ⟨hlt.le, le_rfl⟩ hrm))
      (biFstQ_continuous p F ϖ q₁ q₂ h₁ h₂) (funext fun z => ?_)
    show biFstQ p F ϖ q₁ r h₁ hr
        (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
          (blocToBI p F ϖ _ _ _ _ z))
      = biFstQ p F ϖ q₁ q₂ h₁ h₂ (blocToBI p F ϖ _ _ _ _ z)
    rw [biResQ_blocToBI, biFstQ_blocToBI, biFstQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **Restriction preserves a shared right endpoint**: the `q₂`-component of the
restriction to `[r, q₂]` is the original `q₂`-component. -/
theorem biSndQ_biResQ_right (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) :
    (biSndQ p F ϖ r q₂ hr h₂).comp
        (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩)
      = biSndQ p F ϖ q₁ q₂ h₁ h₂ := by
  have hfun : ⇑((biSndQ p F ϖ r q₂ hr h₂).comp
      (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩))
      = ⇑(biSndQ p F ϖ q₁ q₂ h₁ h₂) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biSndQ_continuous p F ϖ r q₂ hr h₂).comp
        (biResQ_continuous p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm
          ⟨le_rfl, hlt.le⟩))
      (biSndQ_continuous p F ϖ q₁ q₂ h₁ h₂) (funext fun z => ?_)
    show biSndQ p F ϖ r q₂ hr h₂
        (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
          (blocToBI p F ϖ _ _ _ _ z))
      = biSndQ p F ϖ q₁ q₂ h₁ h₂ (blocToBI p F ϖ _ _ _ _ z)
    rw [biResQ_blocToBI, biSndQ_blocToBI, biSndQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **The middle components match**: the `r`-component of the restriction to
`[q₁, r]` equals the `r`-component of the restriction to `[r, q₂]`. -/
theorem biSndQ_biResQ_middle (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) :
    (biSndQ p F ϖ q₁ r h₁ hr).comp
        (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm)
      = (biFstQ p F ϖ r q₂ hr h₂).comp
          (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩) := by
  have hfun : ⇑((biSndQ p F ϖ q₁ r h₁ hr).comp
      (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm))
      = ⇑((biFstQ p F ϖ r q₂ hr h₂).comp
        (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩)) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biSndQ_continuous p F ϖ q₁ r h₁ hr).comp
        (biResQ_continuous p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt
          ⟨hlt.le, le_rfl⟩ hrm))
      ((biFstQ_continuous p F ϖ r q₂ hr h₂).comp
        (biResQ_continuous p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm
          ⟨le_rfl, hlt.le⟩))
      (funext fun z => ?_)
    show biSndQ p F ϖ q₁ r h₁ hr
        (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
          (blocToBI p F ϖ _ _ _ _ z))
      = biFstQ p F ϖ r q₂ hr h₂
          (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
            (blocToBI p F ϖ _ _ _ _ z))
    rw [biResQ_blocToBI, biResQ_blocToBI, biSndQ_blocToBI, biFstQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **Separation for a split interval**: an interval-ring element is determined
by its restrictions to the two halves (its endpoint components are recovered by
the shared-endpoint laws). -/
theorem biResQ_split_injective (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    {x y : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)}
    (hL : biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm x
      = biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm y)
    (hR : biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ x
      = biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ y) :
    x = y := by
  have hfst : biFstQ p F ϖ q₁ q₂ h₁ h₂ x = biFstQ p F ϖ q₁ q₂ h₁ h₂ y := by
    rw [← RingHom.congr_fun
        (biFstQ_biResQ_left p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) x,
      ← RingHom.congr_fun
        (biFstQ_biResQ_left p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) y,
      RingHom.comp_apply, RingHom.comp_apply, hL]
  have hsnd : biSndQ p F ϖ q₁ q₂ h₁ h₂ x = biSndQ p F ϖ q₁ q₂ h₁ h₂ y := by
    rw [← RingHom.congr_fun
        (biSndQ_biResQ_right p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) x,
      ← RingHom.congr_fun
        (biSndQ_biResQ_right p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) y,
      RingHom.comp_apply, RingHom.comp_apply, hR]
  exact Subtype.ext (Prod.ext hfst hsnd)

/-- **The joint approximation step**: a matching pair of half-interval elements
is jointly `ε`-approximated by a single `Bloc` element, via the Mittag-Leffler
splitting of the discrepancy at the split radius. -/
theorem exists_blocApprox_pair (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂)
    {ε : NNReal} (hε : 0 < ε) :
    ∃ h : Bloc p F ϖ,
      wI p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁) (vpiQ_pos p F ϖ r)
        (vpiQ_lt_one p F ϖ hr)
        ((g₁ : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
            × (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)))
          - BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
              (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) h) ≤ ε
      ∧ wI p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) (vpiQ_pos p F ϖ q₂)
          (vpiQ_lt_one p F ϖ h₂)
          ((g₂ : (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr))
              × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))
            - BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
                (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) h) ≤ ε := by
  -- approximate each half from the closure description of `BISub`
  have hg₁cl : (g₁ : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
      × (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)))
      ∈ closure ((BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
        (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)).range
          : Set ((hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
            × (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)))) := g₁.2
  have hg₂cl : (g₂ : (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr))
      × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))
      ∈ closure ((BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
        (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)).range
          : Set ((hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr))
            × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))) := g₂.2
  obtain ⟨w₁, hw₁ball, z₁, hz₁⟩ := mem_closure_iff_nhds.mp hg₁cl _
    (wI_ball_mem_nhds p F (hρ₁0 := vpiQ_pos p F ϖ q₁)
      (hρ₁1 := vpiQ_lt_one p F ϖ h₁) (hρ₂0 := vpiQ_pos p F ϖ r)
      (hρ₂1 := vpiQ_lt_one p F ϖ hr) _ hε)
  obtain ⟨w₂, hw₂ball, z₂, hz₂⟩ := mem_closure_iff_nhds.mp hg₂cl _
    (wI_ball_mem_nhds p F (hρ₁0 := vpiQ_pos p F ϖ r)
      (hρ₁1 := vpiQ_lt_one p F ϖ hr) (hρ₂0 := vpiQ_pos p F ϖ q₂)
      (hρ₂1 := vpiQ_lt_one p F ϖ h₂) _ hε)
  rw [← hz₁] at hw₁ball
  rw [← hz₂] at hw₂ball
  have hb₁ : wI p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
      (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
      (BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
        (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₁ - (g₁ : _ × _)) ≤ ε :=
    hw₁ball
  have hb₂ : wI p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
      (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)
      (BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
        (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z₂ - (g₂ : _ × _)) ≤ ε :=
    hw₂ball
  -- the discrepancy is small at the split radius
  have hmid₁ : Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ r)
      (vpiQ_lt_one p F ϖ hr) z₁ - biSndQ p F ϖ q₁ r h₁ hr g₁) ≤ ε := by
    refine le_trans ?_ hb₁
    rw [wI]
    refine le_max_of_le_right (le_of_eq ?_)
    rfl
  have hmid₂ : Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ r)
      (vpiQ_lt_one p F ϖ hr) z₂ - biFstQ p F ϖ r q₂ hr h₂ g₂) ≤ ε := by
    refine le_trans ?_ hb₂
    rw [wI]
    refine le_max_of_le_left (le_of_eq ?_)
    rfl
  have hdisc : wLoc p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
      (z₁ - z₂) ≤ ε := by
    rw [← valued_BlocToHatK p F ϖ, map_sub]
    calc Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₁
          - BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₂)
        = Valued.v ((BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₁
            - biSndQ p F ϖ q₁ r h₁ hr g₁)
          + (biFstQ p F ϖ r q₂ hr h₂ g₂
            - BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₂)) := by
          rw [hmatch]
          ring_nf
      _ ≤ max (Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ r)
            (vpiQ_lt_one p F ϖ hr) z₁ - biSndQ p F ϖ q₁ r h₁ hr g₁))
          (Valued.v (biFstQ p F ϖ r q₂ hr h₂ g₂
            - BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₂)) :=
          Valuation.map_add _ _ _
      _ ≤ ε := by
          refine max_le hmid₁ ?_
          rw [← Valuation.map_neg, neg_sub]
          exact hmid₂
  -- split the discrepancy
  obtain ⟨dP, dM, hd, hP, hM⟩ := exists_wLoc_split p F ϖ
    (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) (z₁ - z₂)
  refine ⟨z₁ - dP, ?_, ?_⟩
  · have hsplit : (g₁ : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
          × (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)))
        - BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
            (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) (z₁ - dP)
        = ((g₁ : _ × _) - BIProd p F ϖ (vpiQ_pos p F ϖ q₁)
            (vpiQ_lt_one p F ϖ h₁) (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₁)
          + BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
              (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) dP := by
      rw [map_sub]
      ring
    rw [hsplit]
    refine le_trans (wI_add_le p F _ _) (max_le ?_ ?_)
    · rw [show (g₁ : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
            × (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)))
          - BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
              (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₁
          = -(BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
              (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) z₁ - (g₁ : _ × _)) by
        ring, wI_neg]
      exact hb₁
    · rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK]
      refine max_le ?_ ?_
      · exact le_trans (hP _ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_antitone p F ϖ hrq₁)) hdisc
      · exact le_trans (hP _ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
          le_rfl) hdisc
  · have hzM : z₁ - dP = z₂ + dM := by
      have h' := hd
      rw [sub_eq_iff_eq_add] at h'
      rw [h']
      ring
    rw [hzM]
    have hsplit : (g₂ : (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr))
          × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))
        - BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
            (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) (z₂ + dM)
        = ((g₂ : _ × _) - BIProd p F ϖ (vpiQ_pos p F ϖ r)
            (vpiQ_lt_one p F ϖ hr) (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z₂)
          + (- BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
              (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) dM) := by
      rw [map_add]
      ring
    rw [hsplit]
    refine le_trans (wI_add_le p F _ _) (max_le ?_ ?_)
    · rw [show (g₂ : (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr))
            × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))
          - BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
              (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z₂
          = -(BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
              (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z₂ - (g₂ : _ × _)) by
        ring, wI_neg]
      exact hb₂
    · rw [wI_neg, wI_BIProd, valued_BlocToHatK, valued_BlocToHatK]
      refine max_le ?_ ?_
      · exact le_trans (hM _ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
          le_rfl) hdisc
      · exact le_trans (hM _ (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)
          (vpiQ_antitone p F ϖ hq₂r)) hdisc

/-- Convergence in the completed field from termwise valuation bounds. -/
theorem tendsto_hatK_of_valued_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {u : ℕ → hatK p F hρ0 hρ1} {L : hatK p F hρ0 hρ1} {ε : ℕ → NNReal}
    (hb : ∀ n, Valued.v (u n - L) ≤ ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds L) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (R := hatK p F hρ0 hρ1)).mp hU
  obtain ⟨δ, hδ0, hδγ⟩ := exists_nnreal_lt_gamma p F γ
  have hev : ∀ᶠ n in Filter.atTop, ε n < δ :=
    hε.eventually_lt_const hδ0
  refine hev.mono fun n hn => ?_
  exact hγ (hδγ _ ((hb n).trans hn.le))

/-- Convergence of diagonal images from two termwise endpoint bounds. -/
theorem tendsto_BIProd_of_valued_le {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁}
    {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {h : ℕ → Bloc p F ϖ} {a : hatK p F hρ₁0 hρ₁1} {b : hatK p F hρ₂0 hρ₂1}
    {ε : ℕ → NNReal}
    (h1 : ∀ n, Valued.v (BlocToHatK p F ϖ hρ₁0 hρ₁1 (h n) - a) ≤ ε n)
    (h2 : ∀ n, Valued.v (BlocToHatK p F ϖ hρ₂0 hρ₂1 (h n) - b) ≤ ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (h n))
      Filter.atTop (nhds (a, b)) := by
  have hfst := tendsto_hatK_of_valued_le p F h1 hε
  have hsnd := tendsto_hatK_of_valued_le p F h2 hε
  exact hfst.prodMk_nhds hsnd

/-- Recognition of a left-half restriction from a joint approximating
sequence: if `f` has the correct outer component and the sequence converges to
`f` jointly and to `g₁`'s middle component at the split radius, then the left
restriction of `f` is `g₁`. -/
theorem biResQ_eq_left_of_tendsto (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂))
    (h : ℕ → Bloc p F ϖ)
    (hfst : biFstQ p F ϖ q₁ q₂ h₁ h₂ f = biFstQ p F ϖ q₁ r h₁ hr g₁)
    (htof : Filter.Tendsto (fun n => blocToBI p F ϖ (vpiQ_pos p F ϖ q₁)
      (vpiQ_lt_one p F ϖ h₁) (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) (h n))
      Filter.atTop (nhds f))
    (hmid : Filter.Tendsto (fun n => BlocToHatK p F ϖ (vpiQ_pos p F ϖ r)
      (vpiQ_lt_one p F ϖ hr) (h n)) Filter.atTop
      (nhds (biSndQ p F ϖ q₁ r h₁ hr g₁))) :
    biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm f = g₁ := by
  have hA : Filter.Tendsto
      (fun n => (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
        (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) (h n)
          : ↥(BIQ p F ϖ q₁ r h₁ hr)))
      Filter.atTop
      (nhds (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
        f)) := by
    refine Filter.Tendsto.congr
      (fun n => biResQ_blocToBI p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt
        ⟨hlt.le, le_rfl⟩ hrm (h n)) ?_
    exact ((biResQ_continuous p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt
      ⟨hlt.le, le_rfl⟩ hrm).tendsto _).comp htof
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact (RingHom.congr_fun
      (biFstQ_biResQ_left p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) f).trans hfst
  · have hm1 : Filter.Tendsto
        (fun n => BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
          (h n)) Filter.atTop
        (nhds (biSndQ p F ϖ q₁ r h₁ hr
          (biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
            f))) := by
      refine Filter.Tendsto.congr
        (fun n => biSndQ_blocToBI p F ϖ q₁ r h₁ hr (h n))
        (((biSndQ_continuous p F ϖ q₁ r h₁ hr).tendsto _).comp hA)
    exact tendsto_nhds_unique hm1 hmid

/-- Mirror of `biResQ_eq_left_of_tendsto` for the right half. -/
theorem biResQ_eq_right_of_tendsto (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂)) (f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂))
    (h : ℕ → Bloc p F ϖ)
    (hsnd : biSndQ p F ϖ q₁ q₂ h₁ h₂ f = biSndQ p F ϖ r q₂ hr h₂ g₂)
    (htof : Filter.Tendsto (fun n => blocToBI p F ϖ (vpiQ_pos p F ϖ q₁)
      (vpiQ_lt_one p F ϖ h₁) (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) (h n))
      Filter.atTop (nhds f))
    (hmid : Filter.Tendsto (fun n => BlocToHatK p F ϖ (vpiQ_pos p F ϖ r)
      (vpiQ_lt_one p F ϖ hr) (h n)) Filter.atTop
      (nhds (biFstQ p F ϖ r q₂ hr h₂ g₂))) :
    biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ f = g₂ := by
  have hA : Filter.Tendsto
      (fun n => (blocToBI p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
        (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) (h n)
          : ↥(BIQ p F ϖ r q₂ hr h₂)))
      Filter.atTop
      (nhds (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
        f)) := by
    refine Filter.Tendsto.congr
      (fun n => biResQ_blocToBI p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm
        ⟨le_rfl, hlt.le⟩ (h n)) ?_
    exact ((biResQ_continuous p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm
      ⟨le_rfl, hlt.le⟩).tendsto _).comp htof
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have hm1 : Filter.Tendsto
        (fun n => BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
          (h n)) Filter.atTop
        (nhds (biFstQ p F ϖ r q₂ hr h₂
          (biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
            f))) := by
      refine Filter.Tendsto.congr
        (fun n => biFstQ_blocToBI p F ϖ r q₂ hr h₂ (h n))
        (((biFstQ_continuous p F ϖ r q₂ hr h₂).tendsto _).comp hA)
    exact tendsto_nhds_unique hm1 hmid
  · exact (RingHom.congr_fun
      (biSndQ_biResQ_right p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) f).trans hsnd

/-- **The joint approximating sequence** of a matching pair, at accuracy
`2⁻¹ ^ n`. -/
noncomputable def glueSeq (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    ℕ → Bloc p F ϖ := fun n =>
  (exists_blocApprox_pair p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch
    (pow_pos (by norm_num : (0 : NNReal) < 2⁻¹) n)).choose

theorem glueSeq_specL (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂)
    (n : ℕ) :
    wI p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁) (vpiQ_pos p F ϖ r)
      (vpiQ_lt_one p F ϖ hr)
      ((g₁ : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
          × (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)))
        - BIProd p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
            (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
            (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n))
      ≤ 2⁻¹ ^ n :=
  (exists_blocApprox_pair p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch
    (pow_pos (by norm_num : (0 : NNReal) < 2⁻¹) n)).choose_spec.1

theorem glueSeq_specR (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂)
    (n : ℕ) :
    wI p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr) (vpiQ_pos p F ϖ q₂)
      (vpiQ_lt_one p F ϖ h₂)
      ((g₂ : (hatK p F (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr))
          × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))
        - BIProd p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
            (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)
            (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n))
      ≤ 2⁻¹ ^ n :=
  (exists_blocApprox_pair p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch
    (pow_pos (by norm_num : (0 : NNReal) < 2⁻¹) n)).choose_spec.2

/-- The per-component form of the approximation bounds. -/
theorem glueSeq_valued_le (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂)
    (n : ℕ) :
    Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
        (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n)
        - biFstQ p F ϖ q₁ r h₁ hr g₁) ≤ 2⁻¹ ^ n
      ∧ Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
        (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n)
        - biSndQ p F ϖ q₁ r h₁ hr g₁) ≤ 2⁻¹ ^ n
      ∧ Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ r) (vpiQ_lt_one p F ϖ hr)
        (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n)
        - biFstQ p F ϖ r q₂ hr h₂ g₂) ≤ 2⁻¹ ^ n
      ∧ Valued.v (BlocToHatK p F ϖ (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)
        (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n)
        - biSndQ p F ϖ r q₂ hr h₂ g₂) ≤ 2⁻¹ ^ n := by
  have hbL := glueSeq_specL p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n
  have hbR := glueSeq_specR p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n
  rw [wI] at hbL hbR
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Valuation.map_sub_swap]
    exact le_trans (le_max_left _ _) hbL
  · rw [Valuation.map_sub_swap]
    exact le_trans (le_max_right _ _) hbL
  · rw [Valuation.map_sub_swap]
    exact le_trans (le_max_left _ _) hbR
  · rw [Valuation.map_sub_swap]
    exact le_trans (le_max_right _ _) hbR

/-- The accuracy sequence tends to zero. -/
theorem glueSeq_eps_tendsto :
    Filter.Tendsto (fun n : ℕ => (2⁻¹ : NNReal) ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)

/-- **The glued element** of a matching pair: the interval-ring element whose
components are the two outer endpoint components. -/
noncomputable def biGlue (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) :=
  ⟨(biFstQ p F ϖ q₁ r h₁ hr g₁, biSndQ p F ϖ r q₂ hr h₂ g₂),
    mem_closure_of_tendsto
      (tendsto_BIProd_of_valued_le p F ϖ
        (fun n => (glueSeq_valued_le p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂
          hmatch n).1)
        (fun n => (glueSeq_valued_le p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂
          hmatch n).2.2.2)
        (glueSeq_eps_tendsto))
      (Filter.Eventually.of_forall fun n =>
        ⟨glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n, rfl⟩)⟩

/-- The glued element's underlying pair. -/
theorem biGlue_coe (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch
        : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
          × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)))
      = (biFstQ p F ϖ q₁ r h₁ hr g₁, biSndQ p F ϖ r q₂ hr h₂ g₂) := rfl

/-- The outer-left component of the glued element. -/
theorem biGlue_fst (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    biFstQ p F ϖ q₁ q₂ h₁ h₂
        (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch)
      = biFstQ p F ϖ q₁ r h₁ hr g₁ := by
  show (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch
      : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
        × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂))).1 = _
  rw [biGlue_coe]

/-- The outer-right component of the glued element. -/
theorem biGlue_snd (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    biSndQ p F ϖ q₁ q₂ h₁ h₂
        (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch)
      = biSndQ p F ϖ r q₂ hr h₂ g₂ := by
  show (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch
      : (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
        × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂))).2 = _
  rw [biGlue_coe]

/-- The approximating sequence converges to the glued element. -/
theorem tendsto_glueSeq_biGlue (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    Filter.Tendsto (fun n => blocToBI p F ϖ (vpiQ_pos p F ϖ q₁)
      (vpiQ_lt_one p F ϖ h₁) (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)
      (glueSeq p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch n))
      Filter.atTop
      (nhds (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂ hmatch)) :=
  tendsto_subtype_rng.mpr (tendsto_BIProd_of_valued_le p F ϖ
    (fun n => (glueSeq_valued_le p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂
      hmatch n).1)
    (fun n => (glueSeq_valued_le p F ϖ q₁ q₂ r h₁ h₂ hr hq₂r hrq₁ g₁ g₂
      hmatch n).2.2.2)
    (glueSeq_eps_tendsto))

/-- **The left restriction of the glued element.** -/
theorem biResQ_biGlue_left (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
      (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch) = g₁ :=
  biResQ_eq_left_of_tendsto p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm g₁ _ _
    (biGlue_fst p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch)
    (tendsto_glueSeq_biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch)
    (tendsto_hatK_of_valued_le p F
      (fun n => (glueSeq_valued_le p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂
        hmatch n).2.1)
      (glueSeq_eps_tendsto))

/-- **The right restriction of the glued element.** -/
theorem biResQ_biGlue_right (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
      (biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch) = g₂ :=
  biResQ_eq_right_of_tendsto p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm g₂ _ _
    (biGlue_snd p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch)
    (tendsto_glueSeq_biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch)
    (tendsto_hatK_of_valued_le p F
      (fun n => (glueSeq_valued_le p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂
        hmatch n).2.2.1)
      (glueSeq_eps_tendsto))

/-- **Gluing surjectivity for a split interval**: every matching pair of
half-interval elements is the pair of restrictions of an interval-ring
element. -/
theorem biResQ_split_surjective (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    ∃ f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂),
      biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm f = g₁
      ∧ biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ f = g₂ :=
  ⟨biGlue p F ϖ q₁ q₂ r h₁ h₂ hr hrm.1 hrm.2 g₁ g₂ hmatch,
    biResQ_biGlue_left p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm g₁ g₂ hmatch,
    biResQ_biGlue_right p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm g₁ g₂ hmatch⟩


/-! ### Power-boundedness in the interval ring (the plus-reconciliation
substrate): the unit ball `BIPlusIn` is exactly the power-bounded subring. -/

variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
  {hρ₂1 : ρ₂ < 1}

/-- The interval norm is multiplicative on powers. -/
theorem wI_coe_pow (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (n : ℕ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z ^ n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ^ n := by
  rw [show ((z ^ n : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    = ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ^ n from
    SubmonoidClass.coe_pow z n]
  show max (Valued.v (((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))).1 ^ n))
      (Valued.v (((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))).2 ^ n))
    = _
  rw [map_pow, map_pow]
  rcases le_total (Valued.v ((z : (hatK p F hρ₁0 hρ₁1)
      × (hatK p F hρ₂0 hρ₂1)).1))
    (Valued.v ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)) with h | h
  · rw [show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
        = Valued.v ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
      from max_eq_right h]
    exact max_eq_right (pow_le_pow_left' h n)
  · rw [show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
        = Valued.v ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)
      from max_eq_left h]
    exact max_eq_left (pow_le_pow_left' h n)

/-- **Power-boundedness in the interval ring is the unit ball**: `wI` is
multiplicative on powers, so an element is power-bounded iff `wI ≤ 1`
(i.e. iff it lies in `BIPlusIn`). -/
theorem isPowerBounded_iff_wI_le_one
    (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    TopologicalRing.IsPowerBounded z ↔
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ≤ 1 :=
  ⟨wI_le_one_of_isPowerBounded p F ϖ,
    fun hle => BIPlusIn_subset_powerBounded p F ϖ ((mem_BIPlusIn_iff p F ϖ).mpr hle)⟩

end FarguesFontaine

end
