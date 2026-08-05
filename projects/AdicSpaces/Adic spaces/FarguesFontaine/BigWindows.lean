/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.UniformizerTwist
import «Adic spaces».FarguesFontaine.YSpace
import «Adic spaces».FarguesFontaine.ChartData
import «Adic spaces».SpaRationalOpenComparison

/-!
# The Big-window covering of `Y` by twisted charts (ID3b)

The windows `bigWindow n = {v : κ(v) ∈ [p^n, p^{n+1}]}`:

* `FarguesFontaine.bigWindow_eq_union` : `bigWindow n = U_n ∪ V_n` (split at
  `c·p^n`);
* `FarguesFontaine.Y_eq_iUnion_bigWindow` : the Big windows cover `Y`;
* `FarguesFontaine.bigWindow_eq_rationalOpen_ofNat` / `_neg` : each Big window
  is the `κ' ∈ [1, p]` rational chart `R({p^{p+1}, [ϖ']²}/(p[ϖ']))` of the
  twisted pseudo-uniformizer `ϖ' = ϖ^{p^{∓n}}` — the datum
  `chartData-in-ϖ' 1 1 p 1`, whose presheaf value is sheafy by
  `isSheafy_presheafChart` (exact endpoints `ρ₁ = |ϖ'|`, `ρ₂^p = |ϖ'|`).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The Teichmüller power identity of the Frobenius root:
`[ϖ^{1/p^s}]^{p^s} = [ϖ]`. -/
theorem teichPi_frobRoot_pow (s : ℕ) :
    teichPi p F (PseudoUniformizer.frobRoot p F ϖ s) ^ p ^ s = teichPi p F ϖ := by
  rw [teichPi_pow, PseudoUniformizer.toOF_frobRoot, frobRootOF_pow]
  rfl

/-- A `ℤ`-power of a natural number, rewritten in the `T / s` shape the chart-membership
lemmas expect: `a ^ z = (a ^ m : ℕ) / (1 : ℕ)` whenever the exponent `z` is the cast of `m`.

The `hz` hypothesis is what lets one lemma serve every call site: the exponents appearing in
the window lemmas are `(n : ℤ)`, `(n : ℤ) + 1` and `(n : ℤ) + k + 1`, each a natural cast,
discharged by `rfl` or `by push_cast; ring`. -/
theorem natCast_zpow_eq_natCast_div_one (a m : ℕ) (z : ℤ) (hz : z = (m : ℤ)) :
    (a : ℚ) ^ z = ((a ^ m : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
  subst hz
  push_cast
  rw [zpow_natCast]
  ring

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- The Teichmüller identity of the power: `[ϖ^m] = [ϖ]^m`. -/
theorem teichPi_pPow (m : ℕ) (hm : 0 < m) :
    teichPi p F (PseudoUniformizer.pPow F ϖ m hm) = teichPi p F ϖ ^ m := by
  rw [teichPi_pow]
  show WittVector.teichmuller p
    (PseudoUniformizer.toOF F (PseudoUniformizer.pPow F ϖ m hm)) = _
  rw [PseudoUniformizer.toOF_pPow]

omit [CharP F p] in
/-- **`Y` does not depend on the pseudo-uniformizer through powers**: two
pseudo-uniformizers whose Teichmüller lifts are related by powers cut out the
same locus. -/
theorem Y_eq_of_teichPi_pow {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) :
    Y p F ϖ' = Y p F ϖ := by
  ext v
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hbridge : ∀ s t : Ainf p F, v.vle s t ↔
      ValuativeRel.valuation (Ainf p F) s ≤ ValuativeRel.valuation (Ainf p F) t :=
    fun s t => (ValuativeRel.valuation (Ainf p F)).vle_iff_le
  set w := ValuativeRel.valuation (Ainf p F) with hw
  have hzero : ∀ x : Ainf p F, v.vle x 0 ↔ w x = 0 := by
    intro x
    rw [hbridge, map_zero, le_zero_iff]
  have hzeq : (w ((p : Ainf p F) * teichPi p F ϖ') = 0)
      ↔ (w ((p : Ainf p F) * teichPi p F ϖ) = 0) := by
    rw [map_mul, map_mul, mul_eq_zero, mul_eq_zero, ← h, map_pow,
      pow_eq_zero_iff hk.ne']
  constructor
  · rintro ⟨hspa, hne⟩
    refine ⟨hspa, fun hcon => hne ?_⟩
    rw [hzero] at hcon ⊢
    exact hzeq.mpr hcon
  · rintro ⟨hspa, hne⟩
    refine ⟨hspa, fun hcon => hne ?_⟩
    rw [hzero] at hcon ⊢
    exact hzeq.mp hcon


variable {p F ϖ} in
omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- Power-congruence for `vle`. -/
theorem vle_pow_iff {v : Spv (Ainf p F)} {k : ℕ} (hk : 0 < k) (x y : Ainf p F) :
    v.vle (x ^ k) (y ^ k) ↔ v.vle x y := by
  letI : ValuativeRel (Ainf p F) := v.toValuativeRel
  have hbridge : ∀ s t : Ainf p F, v.vle s t ↔
      ValuativeRel.valuation (Ainf p F) s ≤ ValuativeRel.valuation (Ainf p F) t :=
    fun s t => (ValuativeRel.valuation (Ainf p F)).vle_iff_le
  rw [hbridge, hbridge, map_pow, map_pow]
  exact pow_le_pow_iff_left₀ zero_le zero_le hk.ne'

/-- **The Big windows** `{v : κ(v) ∈ [p^n, p^{n+1}]}`. -/
def bigWindow (n : ℤ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ ((p : ℚ) ^ n) v ∧ KLE p F ϖ ((p : ℚ) ^ (n + 1)) v}

/-- The Big window splits at `c·p^n` into the two Kedlaya windows. -/
theorem bigWindow_eq_union (n : ℤ) (hp : 1 < p) :
    bigWindow p F ϖ n = windowU p F ϖ n ∪ windowV p F ϖ n := by
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < p := zero_lt_one.trans hpQ
  have hc1 : 1 < cFF p := one_lt_cFF hp
  have hc0 : (0 : ℚ) < cFF p := zero_lt_one.trans hc1
  have hcp : cFF p ≤ (p : ℚ) := by
    rw [cFF, div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]
    linarith [hpQ]
  ext v
  constructor
  · rintro ⟨hY, hge, hle⟩
    rcases KGE_or_KLE hY (mul_pos hc0 (zpow_pos hp0 n))
      (q := cFF p * (p : ℚ) ^ n) with hg | hl
    · exact Or.inr ⟨hY, hg, hle⟩
    · exact Or.inl ⟨hY, hge, hl⟩
  · rintro (⟨hY, hge, hle⟩ | ⟨hY, hge, hle⟩)
    · refine ⟨hY, hge, KLE_mono p F ϖ hY (mul_pos hc0 (zpow_pos hp0 n)) ?_ hle⟩
      calc cFF p * (p : ℚ) ^ n ≤ (p : ℚ) * (p : ℚ) ^ n :=
            mul_le_mul_of_nonneg_right hcp (zpow_pos hp0 n).le
        _ = (p : ℚ) ^ (n + 1) := by
            rw [zpow_add_one₀ hp0.ne']
            ring
    · refine ⟨hY, KGE_mono p F ϖ hY (zpow_pos hp0 n) ?_ hge, hle⟩
      calc (p : ℚ) ^ n = 1 * (p : ℚ) ^ n := (one_mul _).symm
        _ ≤ cFF p * (p : ℚ) ^ n :=
            mul_le_mul_of_nonneg_right hc1.le (zpow_pos hp0 n).le

/-- **The Big windows cover `Y`.** -/
theorem Y_eq_iUnion_bigWindow (hp : 1 < p) :
    Y p F ϖ = ⋃ n : ℤ, bigWindow p F ϖ n := by
  rw [Y_eq_iUnion_windows]
  rw [show (⋃ n : ℤ, bigWindow p F ϖ n)
      = ⋃ n : ℤ, (windowU p F ϖ n ∪ windowV p F ϖ n) from
    Set.iUnion_congr fun n => bigWindow_eq_union p F ϖ n hp]
  rw [Set.iUnion_union_distrib]


/-- **The Big window is a rational subset (nonnegative side)**: for `n : ℕ`,
`bigWindow n` is the `κ' ∈ [1, p]` chart of the `p^n`-th root uniformizer. -/
theorem bigWindow_eq_rationalOpen_ofNat (n : ℕ) (hp : 1 < p) :
    bigWindow p F ϖ (n : ℤ)
      = rationalOpen (chartT p F (PseudoUniformizer.frobRoot p F ϖ n) p 1)
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ n := pow_pos hppos n
  set ϖ' := PseudoUniformizer.frobRoot p F ϖ n with hϖ'def
  have hteich : teichPi p F ϖ' ^ p ^ n = teichPi p F ϖ :=
    teichPi_frobRoot_pow p F ϖ n
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    Y_eq_of_teichPi_pow p F ϖ hpk hteich
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 1 p 1
    one_pos one_pos hppos one_pos v
  rw [show 1 + p - 1 = p by omega, show 1 + 1 - 1 = 1 by omega] at hiff
  rw [hiff, hYeq]
  have hq1 : (0 : ℚ) < (p : ℚ) ^ (n : ℤ) := zpow_pos hp0 _
  have hq2 : (0 : ℚ) < (p : ℚ) ^ ((n : ℤ) + 1) := zpow_pos hp0 _
  have hab1 := natCast_zpow_eq_natCast_div_one p n (n : ℤ) rfl
  have hab2 := natCast_zpow_eq_natCast_div_one p (n + 1) ((n : ℤ) + 1) (by push_cast; ring)
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq1 one_pos hab1).mp hge
    have hlev := (KLE_iff hY hq2 one_pos hab2).mp hle
    rw [pow_one] at hgev hlev
    refine ⟨hY, ?_, ?_⟩
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich]
      exact hgev
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich, ← pow_mul, show p * p ^ n = p ^ (n + 1) by
        rw [pow_succ]
        ring]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq1 one_pos hab1).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hge
      rw [hteich] at h
      rw [pow_one]
      exact h
    · refine (KLE_iff hY hq2 one_pos hab2).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hle
      rw [hteich, ← pow_mul, show p * p ^ n = p ^ (n + 1) by
        rw [pow_succ]
        ring] at h
      rw [pow_one]
      exact h


/-- **The Big window is a rational subset (negative side)**: for `m > 0`,
`bigWindow (-m)` is the `κ' ∈ [1, p]` chart of the `p^m`-th power uniformizer. -/
theorem bigWindow_eq_rationalOpen_neg (m : ℕ) (hp : 1 < p) :
    bigWindow p F ϖ (-(m : ℤ))
      = rationalOpen
          (chartT p F (PseudoUniformizer.pPow F ϖ (p ^ m)
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) p 1)
          (chartS p F (PseudoUniformizer.pPow F ϖ (p ^ m)
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ m := pow_pos hppos m
  set ϖ' := PseudoUniformizer.pPow F ϖ (p ^ m) (pow_pos hppos m) with hϖ'def
  have hteich : teichPi p F ϖ' = teichPi p F ϖ ^ p ^ m :=
    teichPi_pPow p F ϖ (p ^ m) (pow_pos hppos m)
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    (Y_eq_of_teichPi_pow p F ϖ' hpk hteich.symm).symm
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 1 p 1
    one_pos one_pos hppos one_pos v
  rw [show 1 + p - 1 = p by omega, show 1 + 1 - 1 = 1 by omega] at hiff
  rw [hiff, hYeq]
  have hq1 : (0 : ℚ) < (p : ℚ) ^ (-(m : ℤ)) := zpow_pos hp0 _
  have hq2 : (0 : ℚ) < (p : ℚ) ^ (-(m : ℤ) + 1) := zpow_pos hp0 _
  have hab1 : (p : ℚ) ^ (-(m : ℤ)) = ((1 : ℕ) : ℚ) / ((p ^ m : ℕ) : ℚ) := by
    rw [zpow_neg, zpow_natCast]
    push_cast
    rw [one_div]
  have hab2 : (p : ℚ) ^ (-(m : ℤ) + 1) = ((p : ℕ) : ℚ) / ((p ^ m : ℕ) : ℚ) := by
    rw [show -(m : ℤ) + 1 = 1 - (m : ℤ) by ring, zpow_sub₀ hp0.ne',
      zpow_one, zpow_natCast]
    push_cast
    ring
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq1 hpk hab1).mp hge
    have hlev := (KLE_iff hY hq2 hpk hab2).mp hle
    rw [pow_one] at hgev
    refine ⟨hY, ?_, ?_⟩
    · simp only [pow_one]
      rw [hteich]
      exact hgev
    · simp only [pow_one]
      rw [hteich]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    rw [hteich] at hge hle
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq1 hpk hab1).mpr ?_
      rw [pow_one]
      exact hge
    · exact (KLE_iff hY hq2 hpk hab2).mpr hle

/-- **The overlap of consecutive Big windows is the `κ = p^{n+1}` circle.** -/
theorem bigWindow_inter_succ (n : ℤ) (hp : 1 < p) :
    bigWindow p F ϖ n ∩ bigWindow p F ϖ (n + 1)
      = {v ∈ Y p F ϖ | KGE p F ϖ ((p : ℚ) ^ (n + 1)) v
          ∧ KLE p F ϖ ((p : ℚ) ^ (n + 1)) v} := by
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < p := zero_lt_one.trans hpQ
  ext v
  constructor
  · rintro ⟨⟨hY, -, hle⟩, ⟨-, hge, -⟩⟩
    exact ⟨hY, hge, hle⟩
  · rintro ⟨hY, hge, hle⟩
    have hple : (p : ℚ) ^ n ≤ (p : ℚ) ^ (n + 1) :=
      zpow_le_zpow_right₀ hpQ.le (by omega)
    have hple2 : (p : ℚ) ^ (n + 1) ≤ (p : ℚ) ^ (n + 1 + 1) :=
      zpow_le_zpow_right₀ hpQ.le (by omega)
    exact ⟨⟨hY, KGE_mono p F ϖ hY (zpow_pos hp0 n) hple hge, hle⟩,
      ⟨hY, hge, KLE_mono p F ϖ hY (zpow_pos hp0 (n + 1)) hple2 hle⟩⟩

/-- **The overlap circle is a rational subset (nonnegative side)**: the
`κ' = p` edge of the `n`-th chart, i.e. the datum
`R({p^{2p}, [ϖ']²}/(p^p·[ϖ']))` at `ϖ' = ϖ^{1/p^n}`. -/
theorem bigWindow_inter_succ_eq_rationalOpen_ofNat (n : ℕ) (hp : 1 < p) :
    bigWindow p F ϖ (n : ℤ) ∩ bigWindow p F ϖ ((n : ℤ) + 1)
      = rationalOpen
          (chartT p F (PseudoUniformizer.frobRoot p F ϖ n) (2 * p - 1) 1)
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ n) p 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ n := pow_pos hppos n
  set ϖ' := PseudoUniformizer.frobRoot p F ϖ n with hϖ'def
  have hteich : teichPi p F ϖ' ^ p ^ n = teichPi p F ϖ := teichPi_frobRoot_pow p F ϖ n
  have hYeq : Y p F ϖ' = Y p F ϖ := Y_eq_of_teichPi_pow p F ϖ hpk hteich
  rw [bigWindow_inter_succ p F ϖ (n : ℤ) hp]
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' p 1 p 1
    hppos one_pos hppos one_pos v
  rw [show p + p - 1 = 2 * p - 1 by omega, show 1 + 1 - 1 = 1 by omega]
    at hiff
  rw [hiff, hYeq]
  have hq : (0 : ℚ) < (p : ℚ) ^ ((n : ℤ) + 1) := zpow_pos hp0 _
  have hab := natCast_zpow_eq_natCast_div_one p (n + 1) ((n : ℤ) + 1) (by push_cast; ring)
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq one_pos hab).mp hge
    have hlev := (KLE_iff hY hq one_pos hab).mp hle
    rw [pow_one] at hgev hlev
    refine ⟨hY, ?_, ?_⟩
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich, ← pow_mul, show p * p ^ n = p ^ (n + 1) by
        rw [pow_succ]
        ring]
      exact hgev
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich, ← pow_mul, show p * p ^ n = p ^ (n + 1) by
        rw [pow_succ]
        ring]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq one_pos hab).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hge
      rw [hteich, ← pow_mul, show p * p ^ n = p ^ (n + 1) by
        rw [pow_succ]
        ring] at h
      rw [pow_one]
      exact h
    · refine (KLE_iff hY hq one_pos hab).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hle
      rw [hteich, ← pow_mul, show p * p ^ n = p ^ (n + 1) by
        rw [pow_succ]
        ring] at h
      rw [pow_one]
      exact h


/-- **The overlap circle is a rational subset (negative side)**: the `κ' = p`
edge at the `p^m`-th power uniformizer (circle `κ = p^{-m+1}`). -/
theorem bigWindow_inter_succ_eq_rationalOpen_neg (m : ℕ) (hp : 1 < p) :
    bigWindow p F ϖ (-(m : ℤ)) ∩ bigWindow p F ϖ (-(m : ℤ) + 1)
      = rationalOpen
          (chartT p F (PseudoUniformizer.pPow F ϖ (p ^ m)
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) (2 * p - 1) 1)
          (chartS p F (PseudoUniformizer.pPow F ϖ (p ^ m)
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) p 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ m := pow_pos hppos m
  set ϖ' := PseudoUniformizer.pPow F ϖ (p ^ m) (pow_pos hppos m) with hϖ'def
  have hteich : teichPi p F ϖ' = teichPi p F ϖ ^ p ^ m :=
    teichPi_pPow p F ϖ (p ^ m) (pow_pos hppos m)
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    (Y_eq_of_teichPi_pow p F ϖ' hpk hteich.symm).symm
  rw [bigWindow_inter_succ p F ϖ (-(m : ℤ)) hp]
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' p 1 p 1
    hppos one_pos hppos one_pos v
  rw [show p + p - 1 = 2 * p - 1 by omega, show 1 + 1 - 1 = 1 by omega]
    at hiff
  rw [hiff, hYeq]
  have hq : (0 : ℚ) < (p : ℚ) ^ (-(m : ℤ) + 1) := zpow_pos hp0 _
  have hab : (p : ℚ) ^ (-(m : ℤ) + 1) = ((p : ℕ) : ℚ) / ((p ^ m : ℕ) : ℚ) := by
    rw [show -(m : ℤ) + 1 = 1 - (m : ℤ) by ring, zpow_sub₀ hp0.ne',
      zpow_one, zpow_natCast]
    push_cast
    ring
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq hpk hab).mp hge
    have hlev := (KLE_iff hY hq hpk hab).mp hle
    refine ⟨hY, ?_, ?_⟩
    · simp only [pow_one]
      rw [hteich]
      exact hgev
    · simp only [pow_one]
      rw [hteich]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    rw [hteich] at hge hle
    exact ⟨hY, (KGE_iff hY hq hpk hab).mpr hge, (KLE_iff hY hq hpk hab).mpr hle⟩

noncomputable local instance instDecEqAinfBigWindows : DecidableEq (Ainf p F) :=
  Classical.decEq _

/-- **The `n`-th Big-window chart equivalence (nonnegative side)**: `Spa` of the
chart presheaf value is in bijection with the trace of `bigWindow n` on
`Spa (A_inf, A_inf)` (Wedhorn 8.2 over the Huber — non-Tate — base `A_inf`,
composed with the window identification). -/
noncomputable def spaChartEquivBigWindow (n : ℕ) (hp : 1 < p) :
    ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))))
      ≃ ↥(bigWindow p F ϖ (n : ℤ) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  (spaPresheafValueEquivRationalOpen
    (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)).trans
    (Equiv.setCongr (by
      rw [bigWindow_eq_rationalOpen_ofNat p F ϖ n hp]
      rfl))


/-- **The `-m`-th Big-window chart equivalence (negative side).** -/
noncomputable def spaChartEquivBigWindowNeg (m : ℕ) (hp : 1 < p) :
    ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.pPow F ϖ (p ^ m)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.pPow F ϖ (p ^ m)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))))
      ≃ ↥(bigWindow p F ϖ (-(m : ℤ)) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  (spaPresheafValueEquivRationalOpen
    (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1)).trans
    (Equiv.setCongr (by
      rw [bigWindow_eq_rationalOpen_neg p F ϖ m hp]
      rfl))

end FarguesFontaine

end
