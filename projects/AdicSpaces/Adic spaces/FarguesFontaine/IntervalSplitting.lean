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
  match). Consequence: `biResQ'_split_injective` — an element of `B^{[q₁,q₂]}`
  is determined by its restrictions to the two halves `[q₁,r]`, `[r,q₂]`.

* **The Mittag-Leffler splitting** `exists_wLoc_split`: every element of
  `Bloc` splits at a threshold radius `τ` as `zP + zM` where the tail part
  `zP` is `τ`-controlled at all radii `σ ≤ τ` and the principal part `zM` at
  all radii `σ ≥ τ` (via `WittVector.init`/`tail` truncation of a numerator
  and per-term comparison of the Gauss sup-norms).

These feed the gluing bijection
`B^{[q₁,q₂]} ≅ B^{[q₁,r]} ×_{hatK τ} B^{[r,q₂]}`.
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
theorem pow_mul_gaussValue_init_le {σ τ : NNReal} (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1)
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
  have hgy : ∀ (σ : NNReal) (hσ0 : 0 < σ) (hσ1 : σ < 1),
      gaussValue p F σ (y : Ainf p F)
        = (σ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
    intro σ hσ0 hσ1
    rw [hy, show gaussValue p F σ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
        = gaussVal p F hσ0 hσ1 (((p : Ainf p F) * teichPi p F ϖ) ^ k) from
      (gaussVal_apply p F hσ0 hσ1 _).symm, Valuation.map_pow, gaussVal_apply,
      gaussValue_p_teichPi p F ϖ hσ1]
  have hgy_ne : ∀ (σ : NNReal) (hσ0 : 0 < σ) (hσ1 : σ < 1),
      gaussValue p F σ (y : Ainf p F) ≠ 0 := by
    intro σ hσ0 hσ1
    rw [hy]
    rw [show gaussValue p F σ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
        = gaussVal p F hσ0 hσ1 (((p : Ainf p F) * teichPi p F ϖ) ^ k) from
      (gaussVal_apply p F hσ0 hσ1 _).symm, Valuation.map_pow]
    exact pow_ne_zero k (by
      rw [gaussVal_apply]
      exact gaussValue_p_teichPi_ne_zero p F ϖ hσ0 hσ1)
  refine ⟨IsLocalization.mk' (Bloc p F ϖ) (WittVector.tail k x) y,
    IsLocalization.mk' (Bloc p F ϖ) (WittVector.init k x) y, ?_, ?_, ?_⟩
  · rw [hzmk]
    rw [show IsLocalization.mk' (Bloc p F ϖ) (WittVector.tail k x) y
          + IsLocalization.mk' (Bloc p F ϖ) (WittVector.init k x) y
        = IsLocalization.mk' (Bloc p F ϖ)
            (WittVector.tail k x * ↑y + WittVector.init k x * ↑y) (y * y) from
      (IsLocalization.mk'_add _ _ _ _).symm]
    rw [show WittVector.tail k x * ↑y + WittVector.init k x * ↑y
        = x * ↑y from by
      rw [← add_mul, add_comm, WittVector.init_add_tail],
      IsLocalization.mk'_cancel]
  · intro σ hσ0 hσ1 hστ
    rw [hzmk, wLoc_mk', wLoc_mk', hgy σ hσ0 hσ1, hgy τ hτ0 hτ1,
      ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ (pos_iff_ne_zero.mpr (by
        rw [← hgy σ hσ0 hσ1]
        exact hgy_ne σ hσ0 hσ1)) (pos_iff_ne_zero.mpr (by
        rw [← hgy τ hτ0 hτ1]
        exact hgy_ne τ hτ0 hτ1))]
    rw [mul_pow, mul_pow]
    calc gaussValue p F σ (WittVector.tail k x)
          * (τ ^ k * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k)
        = (τ ^ k * gaussValue p F σ (WittVector.tail k x))
            * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k := by ring
      _ ≤ (σ ^ k * gaussValue p F τ x)
            * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k :=
          mul_le_mul_left
            (pow_mul_gaussValue_tail_le p F hστ hτ1.le x k) _
      _ = gaussValue p F τ x
            * (σ ^ k * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k) := by ring
  · intro σ hσ0 hσ1 hτσ
    rw [hzmk, wLoc_mk', wLoc_mk', hgy σ hσ0 hσ1, hgy τ hτ0 hτ1,
      ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ (pos_iff_ne_zero.mpr (by
        rw [← hgy σ hσ0 hσ1]
        exact hgy_ne σ hσ0 hσ1)) (pos_iff_ne_zero.mpr (by
        rw [← hgy τ hτ0 hτ1]
        exact hgy_ne τ hτ0 hτ1))]
    rw [mul_pow, mul_pow]
    calc gaussValue p F σ (WittVector.init k x)
          * (τ ^ k * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k)
        = (τ ^ k * gaussValue p F σ (WittVector.init k x))
            * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k := by ring
      _ ≤ (σ ^ k * gaussValue p F τ x)
            * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k :=
          mul_le_mul_left
            (pow_mul_gaussValue_init_le p F hτσ hσ1.le hτ1.le x k) _
      _ = gaussValue p F τ x
            * (σ ^ k * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k) := by ring

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
theorem biFstQ_biResQ'_left (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) :
    (biFstQ p F ϖ q₁ r h₁ hr).comp
        (biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm)
      = biFstQ p F ϖ q₁ q₂ h₁ h₂ := by
  have hfun : ⇑((biFstQ p F ϖ q₁ r h₁ hr).comp
      (biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm))
      = ⇑(biFstQ p F ϖ q₁ q₂ h₁ h₂) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biFstQ_continuous p F ϖ q₁ r h₁ hr).comp
        (biResQ'_continuous p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt
          ⟨hlt.le, le_rfl⟩ hrm))
      (biFstQ_continuous p F ϖ q₁ q₂ h₁ h₂) (funext fun z => ?_)
    show biFstQ p F ϖ q₁ r h₁ hr
        (biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
          (blocToBI p F ϖ _ _ _ _ z))
      = biFstQ p F ϖ q₁ q₂ h₁ h₂ (blocToBI p F ϖ _ _ _ _ z)
    rw [biResQ'_blocToBI, biFstQ_blocToBI, biFstQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **Restriction preserves a shared right endpoint**: the `q₂`-component of the
restriction to `[r, q₂]` is the original `q₂`-component. -/
theorem biSndQ_biResQ'_right (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) :
    (biSndQ p F ϖ r q₂ hr h₂).comp
        (biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩)
      = biSndQ p F ϖ q₁ q₂ h₁ h₂ := by
  have hfun : ⇑((biSndQ p F ϖ r q₂ hr h₂).comp
      (biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩))
      = ⇑(biSndQ p F ϖ q₁ q₂ h₁ h₂) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biSndQ_continuous p F ϖ r q₂ hr h₂).comp
        (biResQ'_continuous p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm
          ⟨le_rfl, hlt.le⟩))
      (biSndQ_continuous p F ϖ q₁ q₂ h₁ h₂) (funext fun z => ?_)
    show biSndQ p F ϖ r q₂ hr h₂
        (biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
          (blocToBI p F ϖ _ _ _ _ z))
      = biSndQ p F ϖ q₁ q₂ h₁ h₂ (blocToBI p F ϖ _ _ _ _ z)
    rw [biResQ'_blocToBI, biSndQ_blocToBI, biSndQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **The middle components match**: the `r`-component of the restriction to
`[q₁, r]` equals the `r`-component of the restriction to `[r, q₂]`. -/
theorem biSndQ_biResQ'_middle (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) :
    (biSndQ p F ϖ q₁ r h₁ hr).comp
        (biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm)
      = (biFstQ p F ϖ r q₂ hr h₂).comp
          (biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩) := by
  have hfun : ⇑((biSndQ p F ϖ q₁ r h₁ hr).comp
      (biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm))
      = ⇑((biFstQ p F ϖ r q₂ hr h₂).comp
        (biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩)) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biSndQ_continuous p F ϖ q₁ r h₁ hr).comp
        (biResQ'_continuous p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt
          ⟨hlt.le, le_rfl⟩ hrm))
      ((biFstQ_continuous p F ϖ r q₂ hr h₂).comp
        (biResQ'_continuous p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm
          ⟨le_rfl, hlt.le⟩))
      (funext fun z => ?_)
    show biSndQ p F ϖ q₁ r h₁ hr
        (biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm
          (blocToBI p F ϖ _ _ _ _ z))
      = biFstQ p F ϖ r q₂ hr h₂
          (biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩
            (blocToBI p F ϖ _ _ _ _ z))
    rw [biResQ'_blocToBI, biResQ'_blocToBI, biSndQ_blocToBI, biFstQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **Separation for a split interval**: an interval-ring element is determined
by its restrictions to the two halves (its endpoint components are recovered by
the shared-endpoint laws). -/
theorem biResQ'_split_injective (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    {x y : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)}
    (hL : biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm x
      = biResQ' p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm y)
    (hR : biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ x
      = biResQ' p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ y) :
    x = y := by
  have hfst : biFstQ p F ϖ q₁ q₂ h₁ h₂ x = biFstQ p F ϖ q₁ q₂ h₁ h₂ y := by
    rw [← RingHom.congr_fun
        (biFstQ_biResQ'_left p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) x,
      ← RingHom.congr_fun
        (biFstQ_biResQ'_left p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) y,
      RingHom.comp_apply, RingHom.comp_apply, hL]
  have hsnd : biSndQ p F ϖ q₁ q₂ h₁ h₂ x = biSndQ p F ϖ q₁ q₂ h₁ h₂ y := by
    rw [← RingHom.congr_fun
        (biSndQ_biResQ'_right p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) x,
      ← RingHom.congr_fun
        (biSndQ_biResQ'_right p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm) y,
      RingHom.comp_apply, RingHom.comp_apply, hR]
  exact Subtype.ext (Prod.ext hfst hsnd)

end FarguesFontaine

end
