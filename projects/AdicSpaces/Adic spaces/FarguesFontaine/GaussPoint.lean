/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.GaussNorm
import «Adic spaces».FarguesFontaine.YSpace

/-!
# The Gauss point: `𝒴` is nonempty

The weighted Gauss value `w_ρ` (`GaussNorm.lean`) is bundled as a rank-1
`Valuation (Ainf p F) NNReal`; it is `≤ 1` everywhere, continuous for the
`(p,[ϖ])`-adic topology (elements of `Iinf^n` have value at most
`max ρ |ϖ|^n`, and `max ρ |ϖ| < 1`), and does not vanish on `p·[ϖ]`
(its value there is `ρ·|ϖ| > 0`). Its class in `Spv (A_inf)` therefore lies in
`Spa(A_inf, A_inf)` and in the basic open `{v : v(p[ϖ]) ≠ 0}` — that is, in `𝒴`.

## Main results

* `FarguesFontaine.gaussVal` : the bundled Gauss valuation.
* `FarguesFontaine.gaussVal_isContinuous` : continuity in the sense of Wedhorn 7.7.
* `FarguesFontaine.gaussPoint_mem_Y` / `FarguesFontaine.Y_nonempty` : the Gauss point
  lies in `𝒴`.

## Sources

* [Kedlaya, *New methods for (φ,Γ)-modules*][kedlaya-new-methods], Lemma 4.1 and
  Theorem 4.5 (continuity of `λ`).
* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Definition 2.2 and Lemma 2.3.
* [Fargues–Fontaine, *Courbes et fibrés vectoriels*], §1.4 (the Gauss points of `𝒴`).
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

omit [CharP F p] in
/-- The rank-1 valuation of `F` is strictly below `1` on a pseudo-uniformizer:
otherwise its inverse would be power-bounded, making `ϖ` a unit of `O_F`,
contradicting `PseudoUniformizer.not_isUnit_toOF`. -/
theorem perfectoidValuation_toOF_lt_one (ϖ : PseudoUniformizer F) :
    perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) < 1 := by
  refine lt_of_le_of_ne (perfectoidValuation_le_one p F _) fun h1 => ?_
  have hne : (((ϖ.val : Fˣ) : F)) ≠ 0 := (ϖ.val : Fˣ).ne_zero
  have hcoe : ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ((ϖ.val : Fˣ) : F) := rfl
  rw [hcoe] at h1
  have hinv : perfectoidValuation p F (((ϖ.val : Fˣ) : F))⁻¹ ≤ 1 := by
    have hmul : perfectoidValuation p F (((ϖ.val : Fˣ) : F)) *
        perfectoidValuation p F (((ϖ.val : Fˣ) : F))⁻¹ = 1 := by
      rw [← Valuation.map_mul, mul_inv_cancel₀ hne, Valuation.map_one]
    rw [h1, one_mul] at hmul
    exact hmul.le
  obtain ⟨u, hu⟩ := (perfectoidValuation_integers p F).exists_of_le_one hinv
  have hmul2 : PseudoUniformizer.toOF F ϖ * u = 1 := by
    refine Subtype.ext ?_
    have hu' : ((u : OF F) : F) = (((ϖ.val : Fˣ) : F))⁻¹ := hu
    have : ((PseudoUniformizer.toOF F ϖ * u : OF F) : F)
        = ((ϖ.val : Fˣ) : F) * (((ϖ.val : Fˣ) : F))⁻¹ := by
      rw [show ((PseudoUniformizer.toOF F ϖ * u : OF F) : F)
        = ((PseudoUniformizer.toOF F ϖ : OF F) : F) * ((u : OF F) : F) from rfl, hcoe, hu']
    rw [this, mul_inv_cancel₀ hne]
    rfl
  exact PseudoUniformizer.not_isUnit_toOF (p := p) (F := F) ϖ
    ⟨Units.mkOfMulEqOne _ _ hmul2, rfl⟩

/-- **The Gauss valuation** on `A_inf`, bundled: `w_ρ(Σ pⁿ[aₙ]) = sup ρⁿ|aₙ|`.
Multiplicativity is `gaussValue_mul` (Kedlaya 1004.0466, Lemma 4.1). -/
def gaussVal {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Valuation (Ainf p F) NNReal where
  toFun := gaussValue p F ρ
  map_zero' := gaussValue_zero p F ρ
  map_one' := gaussValue_one p F hρ1.le
  map_mul' := gaussValue_mul p F hρ0 hρ1
  map_add_le_max' := gaussValue_add_le p F hρ1.le

@[simp]
theorem gaussVal_apply {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) :
    gaussVal p F hρ0 hρ1 x = gaussValue p F ρ x := rfl

variable (ϖ : PseudoUniformizer F)

/-- Generators of `Iinf` have Gauss value at most `max ρ |ϖ|`. -/
theorem gaussValue_le_max_of_mem_Iinf {ρ : NNReal} (hρ1 : ρ < 1) {a : Ainf p F}
    (ha : a ∈ Iinf p F ϖ) :
    gaussValue p F ρ a
      ≤ max ρ (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)) := by
  rw [Iinf] at ha
  obtain ⟨u, t, hut⟩ := Ideal.mem_span_pair.mp ha
  rw [← hut]
  refine (gaussValue_add_le p F hρ1.le _ _).trans (max_le ?_ ?_)
  · rw [mul_comm, gaussValue_p_mul p F hρ1.le]
    exact le_max_of_le_left
      (mul_le_of_le_one_right zero_le (gaussValue_le_one p F hρ1.le u))
  · rw [mul_comm]
    refine le_max_of_le_right ?_
    refine (gaussValue_mul_le p F hρ1 _ _).trans ?_
    rw [teichPi, gaussValue_teichmuller p F hρ1.le]
    exact mul_le_of_le_one_right zero_le (gaussValue_le_one p F hρ1.le t)

/-- Elements of `Iinf^n` have Gauss value at most `(max ρ |ϖ|)^n`
([Kedlaya-new-methods], Theorem 4.5: the uniform continuity estimate). -/
theorem gaussValue_le_max_pow_of_mem_Iinf_pow {ρ : NNReal} (hρ1 : ρ < 1) (n : ℕ)
    {z : Ainf p F} (hz : z ∈ Iinf p F ϖ ^ n) :
    gaussValue p F ρ z
      ≤ max ρ (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ n := by
  induction n generalizing z with
  | zero =>
    simpa using gaussValue_le_one p F hρ1.le z
  | succ m ih =>
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [pow_succ]
      exact (gaussValue_mul_le p F hρ1 a b).trans
        (mul_le_mul (ih ha) (gaussValue_le_max_of_mem_Iinf p F ϖ hρ1 hb) zero_le zero_le)
    · exact (gaussValue_add_le p F hρ1.le x y).trans (max_le hx hy)

/-- **Continuity of the Gauss valuation** (Wedhorn 7.7 sense; Kedlaya 1004.0466,
Theorem 4.5): every value set `{a : w_ρ(a) < γ}` is open in the `(p,[ϖ])`-adic
topology. -/
theorem gaussVal_isContinuous {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (gaussVal p F hρ0 hρ1).IsContinuous := by
  set ϖ₀ : PseudoUniformizer F := IsTateRing.pseudoUniformizer (A := F) with hϖ₀
  intro γ
  rcases eq_or_ne γ 0 with rfl | hγ
  · convert isOpen_empty
    refine Set.eq_empty_iff_forall_notMem.mpr fun a ha => ?_
    simp only [Set.mem_setOf_eq] at ha
    exact not_lt_zero ha
  have hq1 : max ρ (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ₀ : OF F) : F))
      < 1 := max_lt hρ1 (perfectoidValuation_toOF_lt_one p F ϖ₀)
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr hγ) hq1
  have hadic := (isAdic_iff.mp (isAdic_Iinf p F ϖ₀)).1 n
  rw [← map_add_left_nhds_zero a, Filter.mem_map]
  refine Filter.mem_of_superset (hadic.mem_nhds (zero_mem _)) fun z hz => ?_
  have hz' : gaussValue p F ρ z
      ≤ max ρ (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ₀ : OF F) : F)) ^ n :=
    gaussValue_le_max_pow_of_mem_Iinf_pow p F ϖ₀ hρ1 n hz
  have hmem : gaussValue p F ρ (a + z) < γ :=
    lt_of_le_of_lt (gaussValue_add_le p F hρ1.le a z)
      (max_lt ha (lt_of_le_of_lt hz' hn))
  exact hmem

/-- The Gauss value of `p·[ϖ]` is `ρ·|ϖ| ≠ 0`. -/
theorem gaussValue_p_teichPi_ne_zero {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    gaussValue p F ρ ((p : Ainf p F) * teichPi p F ϖ) ≠ 0 := by
  rw [gaussValue_p_mul p F hρ1.le, teichPi, gaussValue_teichmuller p F hρ1.le]
  refine (mul_pos hρ0 ?_).ne'
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  exact PseudoUniformizer.toOF_ne_zero F ϖ
    (Subtype.ext ((Valuation.zero_iff (perfectoidValuation p F)).mp h0))

/-- **The Gauss point lies in `𝒴`** ([BFHHLWY, Def 2.1.1]; [Fargues–Fontaine, §1.4]). -/
theorem gaussPoint_mem_Y {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ofValuation (gaussVal p F hρ0 hρ1) ∈ Y p F ϖ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact isContinuous_ofValuation_of _ (gaussVal_isContinuous p F hρ0 hρ1)
  · intro f hf
    have hbr : (ofValuation (gaussVal p F hρ0 hρ1)).vle f 1
        ↔ gaussVal p F hρ0 hρ1 f ≤ gaussVal p F hρ0 hρ1 1 := Iff.rfl
    rw [hbr, gaussVal_apply, gaussVal_apply, gaussValue_one p F hρ1.le]
    exact gaussValue_le_one p F hρ1.le f
  · intro hle
    have hbr : (ofValuation (gaussVal p F hρ0 hρ1)).vle ((p : Ainf p F) * teichPi p F ϖ) 0
        ↔ gaussVal p F hρ0 hρ1 ((p : Ainf p F) * teichPi p F ϖ)
          ≤ gaussVal p F hρ0 hρ1 0 := Iff.rfl
    rw [hbr, gaussVal_apply, gaussVal_apply, gaussValue_zero p F ρ] at hle
    exact gaussValue_p_teichPi_ne_zero p F ϖ hρ0 hρ1 (le_antisymm hle zero_le)

/-- **`𝒴` is nonempty** (equivalently, the curve is nonempty): the `ρ = 1/2` Gauss point
`w_ρ(Σ pⁿ[aₙ]) = sup ρⁿ|aₙ|` is a continuous multiplicative valuation on `A_inf`
with `w(p·[ϖ]) = ρ·|ϖ| ≠ 0` (Fargues–Fontaine, *Courbes et fibrés vectoriels*,
§1.4; Kedlaya 1004.0466, Lemma 4.1 for multiplicativity). -/
theorem Y_nonempty : (Y p F ϖ).Nonempty := by
  have h0 : (0 : NNReal) < 2⁻¹ := by norm_num
  have h1 : (2⁻¹ : NNReal) < 1 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  exact ⟨ofValuation (gaussVal p F h0 h1), gaussPoint_mem_Y p F ϖ h0 h1⟩

end FarguesFontaine

end
