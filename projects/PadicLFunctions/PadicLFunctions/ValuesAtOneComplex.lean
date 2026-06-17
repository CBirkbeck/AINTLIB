/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.GenBernoulliComplex
import PadicLFunctions.Interpolation.Characters
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# The classical value L(θ,1) (RJW §6.1, Thm 6.1(i), decomposition C6)

RJW Thm 6.1(i) (TeX 1989–1991), following Washington Thm 4.9: for `θ`
non-trivial of conductor `N` and `ε` a primitive `N`-th root of unity,
`L(θ,1) = −G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε^c)`. Complex-analysis
quarantine file (the §4 `ZetaValuesComplex` pattern), stated against
mathlib's `DirichletCharacter.LFunction` per the mathlib-linking directive.

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster C6.
-/

open Complex DirichletCharacter

namespace PadicLFunctions

namespace ValuesAtOneComplex

variable {N : ℕ} [NeZero N]

/-- Gauss sums factor over coprime levels (CRT): for `θ` the product of `η`
(level `D`) and `χ` (level `M`) at level `DM` and the **split** additive
character `ε = εD·εM`, `G(θ) = G(η)·G(χ)`. -/
theorem gaussSum_mul_coprime {R : Type*} [CommRing R] [IsDomain R]
    {D M : ℕ} [NeZero D] [NeZero M] (hco : Nat.Coprime D M)
    (η : DirichletCharacter R D) (χ : DirichletCharacter R M)
    {θ : DirichletCharacter R (D * M)}
    (hθ : θ = DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)
    {εD εM : R} (hεD : IsPrimitiveRoot εD D) (hεM : IsPrimitiveRoot εM M) :
    gaussSum θ (AddChar.zmodChar (D * M)
        (show (εD * εM) ^ (D * M) = 1 from by
          rw [mul_pow, pow_mul, hεD.pow_eq_one, one_pow, one_mul,
            mul_comm D M, pow_mul, hεM.pow_eq_one, one_pow]))
      = gaussSum η (AddChar.zmodChar D hεD.pow_eq_one)
        * gaussSum χ (AddChar.zmodChar M hεM.pow_eq_one) := by
  classical
  set e := ZMod.chineseRemainder hco with he
  set ψ := AddChar.zmodChar (D * M)
    (show (εD * εM) ^ (D * M) = 1 from by
      rw [mul_pow, pow_mul, hεD.pow_eq_one, one_pow, one_mul,
        mul_comm D M, pow_mul, hεM.pow_eq_one, one_pow]) with hψ
  set ψD := AddChar.zmodChar D hεD.pow_eq_one with hψD
  set ψM := AddChar.zmodChar M hεM.pow_eq_one with hψM
  have hfst : ∀ a : ZMod (D * M), (e a).1 = (ZMod.cast a : ZMod D) := fun a => Prod.fst_zmod_cast a
  have hsnd : ∀ a : ZMod (D * M), (e a).2 = (ZMod.cast a : ZMod M) := fun a => Prod.snd_zmod_cast a
  have hθfac : ∀ a : ZMod (D * M),
      θ a = η (ZMod.cast a : ZMod D) * χ (ZMod.cast a : ZMod M) := by
    intro a
    rw [hθ, MulChar.mul_apply]
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      rw [changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd]
    · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, zero_mul]
      have hunit : ¬ (IsUnit (ZMod.cast a : ZMod D) ∧ IsUnit (ZMod.cast a : ZMod M)) := by
        rw [← hfst a, ← hsnd a, ← Prod.isUnit_iff,
          MulEquiv.isUnit_map (f := e) (x := a)]
        exact ha
      rw [not_and_or] at hunit
      rcases hunit with h | h
      · rw [MulChar.map_nonunit _ h, zero_mul]
      · rw [MulChar.map_nonunit _ h, mul_zero]
  have hψfac : ∀ a : ZMod (D * M),
      ψ a = ψD (ZMod.cast a : ZMod D) * ψM (ZMod.cast a : ZMod M) := by
    intro a
    have hcD : (ZMod.cast a : ZMod D) = ((a.val : ℕ) : ZMod D) := (ZMod.natCast_val a).symm
    have hcM : (ZMod.cast a : ZMod M) = ((a.val : ℕ) : ZMod M) := (ZMod.natCast_val a).symm
    rw [hψ, hψD, hψM, AddChar.zmodChar_apply, hcD, hcM, AddChar.zmodChar_apply',
      AddChar.zmodChar_apply', mul_pow]
  rw [gaussSum]
  have hsummand : ∀ a : ZMod (D * M), θ a * ψ a
      = (fun p : ZMod D × ZMod M => η p.1 * χ p.2 * (ψD p.1 * ψM p.2)) (e.toEquiv a) := by
    intro a
    rw [hθfac, hψfac]
    simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hfst, hsnd]
  simp_rw [hsummand]
  rw [Equiv.sum_comp e.toEquiv
      (fun p : ZMod D × ZMod M => η p.1 * χ p.2 * (ψD p.1 * ψM p.2)),
    ← Finset.univ_product_univ, Finset.sum_product, gaussSum, gaussSum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- For `z` on the unit circle, `z ≠ 1`, the logarithm series converges at
the boundary: the partial sums `Σ_{n<N} zⁿ⁺¹/(n+1)` tend to `−log(1−z)`. -/
theorem tendsto_sum_pow_div_eq_neg_log {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / (n + 1))
      Filter.atTop (nhds (-Complex.log (1 - z))) := by
  classical
  have hzlt : z.re < 1 := by
    have hle : z.re ≤ 1 := by simpa [hz] using Complex.re_le_norm z
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · refine absurd (Complex.ext h ?_) hz1
      have hns : z.re * z.re + z.im * z.im = 1 := by
        have := Complex.normSq_eq_norm_sq z
        rw [Complex.normSq_apply, hz] at this
        simpa using this
      have him : z.im * z.im = 0 := by nlinarith [hns, h]
      simpa using (mul_self_eq_zero.mp him)
  set a : ℕ → ℂ := fun k => z ^ k / k with ha
  have hz0 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr fun h => hz1 h.symm
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr hz0
  have hbound : ∀ n, ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ ≤ 2 / ‖1 - z‖ := by
    intro n
    have hsplit : ∑ i ∈ Finset.range n, z ^ (i + 1) = z * ∑ i ∈ Finset.range n, z ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, geom_sum_eq hz1 n, norm_mul, norm_div]
    have hzn : ‖z ^ n - 1‖ ≤ 2 := by
      calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
    have hzm1 : ‖z - 1‖ = ‖1 - z‖ := by rw [← norm_neg, neg_sub]
    rw [hzm1, hz, one_mul, div_le_div_iff_of_pos_right hpos]
    exact hzn
  have hSeq : (fun n => ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1))
      = fun n => ∑ i ∈ Finset.range n,
          (fun k : ℕ => (1 : ℝ) / (k + 1)) i • (fun k => z ^ (k + 1)) i := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
    rw [div_eq_inv_mul]
  have hcauchy : CauchySeq fun n => ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1) := by
    rw [hSeq]
    refine Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      (b := 2 / ‖1 - z‖) (fun m n hmn => ?_) ?_ hbound
    · refine one_div_le_one_div_of_le (by positivity) ?_
      exact_mod_cast Nat.add_le_add_right hmn 1
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  suffices hll : l = -Complex.log (1 - z) by rw [← hll]; exact hl
  have hla : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, a k) Filter.atTop (nhds l) := by
    have hreindex : ∀ n, ∑ k ∈ Finset.range (n + 1), a k
        = ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1) := by
      intro n
      rw [Finset.sum_range_succ']
      simp only [ha, pow_zero, Nat.cast_zero, div_zero, add_zero]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    have htail : Filter.Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k)
        Filter.atTop (nhds l) := by simpa only [hreindex] using hl
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp htail
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hla
  have hmem : (1 : ℂ) - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hcont : Filter.Tendsto (fun x : ℝ => -Complex.log (1 - (x : ℂ) * z))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (-Complex.log (1 - z))) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 : ℂ) - (x : ℂ) * z)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (1 - z)) := by
      have hc : Continuous (fun x : ℝ => (1 : ℂ) - (x : ℂ) * z) := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    exact (h1.clog hmem).neg
  have habel' : Filter.Tendsto (fun x : ℝ => -Complex.log (1 - (x : ℂ) * z))
      (nhdsWithin 1 (Set.Iio 1)) (nhds l) := by
    rw [Filter.tendsto_map'_iff] at habel
    refine habel.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx0
    have hx1 : x < 1 := Set.mem_Iio.mp hx
    have hxz : ‖(x : ℂ) * z‖ < 1 := by
      rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx1
    have heq := (Complex.hasSum_taylorSeries_neg_log hxz).tsum_eq
    simp only [Function.comp_apply]
    rw [← heq]
    refine tsum_congr fun n => ?_
    simp only [ha]
    rw [mul_pow]; ring
  exact tendsto_nhds_unique habel' hcont

omit [NeZero N] in
private lemma isPrimitive_inv {θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) :
    θ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive at hθ ⊢
  rwa [DirichletCharacter.conductor_inv]

private lemma gaussSum_inv_ne_zero {θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive)
    {ε : ℂ} (hε : IsPrimitiveRoot ε N) :
    gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one) ≠ 0 := by
  intro h
  have hprod := gaussSum_mul_gaussSum_inv (R := ℂ) (χ := θ⁻¹) (isPrimitive_inv hθ)
    (e := AddChar.zmodChar N hε.pow_eq_one)
    (AddChar.zmodChar_primitive_of_primitive_root N hε)
  rw [h, zero_mul] at hprod
  exact (NeZero.ne (N : ℂ)) hprod.symm

/-- The Gauss-sum/Fourier rearrangement of the L-series of a primitive `θ` for
`Re s > 1`: `L(θ, s) = G(θ⁻¹)⁻¹ · Σ_c θ⁻¹(c)·L(n ↦ εⁿᶜ, s)`. -/
theorem LSeries_eq_gaussSum_inv_mul_sum {θ : DirichletCharacter ℂ N}
    (hθ : θ.IsPrimitive) (_hθ1 : θ ≠ 1) {ε : ℂ}
    (hε : IsPrimitiveRoot ε N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => θ n) s
      = (gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹
        * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N)
          * LSeries (fun n => ε ^ (n * ((c : ZMod N)).val)) s := by
  classical
  set ψ := AddChar.zmodChar N hε.pow_eq_one with hψ
  set G := gaussSum θ⁻¹ ψ with hG
  have hGne : G ≠ 0 := gaussSum_inv_ne_zero hθ hε
  have hfourier : ∀ m : ZMod N,
      θ m * G = ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N) * ε ^ ((m * (c : ZMod N)).val) := by
    intro m
    have hkey := gaussSum_mulShift_of_isPrimitive ψ (isPrimitive_inv hθ) m
    rw [inv_inv, gaussSum] at hkey
    rw [hG, ← hkey, ← Finset.sum_subset (Finset.subset_univ
        ((Finset.univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩))]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Function.Embedding.coeFn_mk, AddChar.mulShift_apply, hψ,
        AddChar.zmodChar_apply]
    · intro a _ ha
      rw [Finset.mem_map] at ha
      have hnu : ¬ IsUnit a := fun hu => ha ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
      rw [MulChar.map_nonunit _ hnu, zero_mul]
  have hsummand : ∀ c : (ZMod N)ˣ,
      LSeriesSummable (fun n : ℕ => ε ^ (n * ((c : ZMod N)).val)) s := by
    intro c
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hs
    rw [norm_pow, IsPrimitiveRoot.norm'_eq_one hε (NeZero.ne N), one_pow]
  have hpow : ∀ (n : ℕ) (c : (ZMod N)ˣ),
      ε ^ (n * ((c : ZMod N)).val) = ε ^ (((n : ZMod N) * (c : ZMod N)).val) := by
    intro n c
    rw [pow_eq_pow_mod (n * ((c : ZMod N)).val) hε.pow_eq_one,
      pow_eq_pow_mod (((n : ZMod N) * (c : ZMod N)).val) hε.pow_eq_one]
    congr 1
    rw [ZMod.val_mul, ZMod.val_natCast]
    simp [Nat.mul_mod]
  have hcoeff : (fun n : ℕ => θ n)
      = G⁻¹ • ∑ c : (ZMod N)ˣ,
          θ⁻¹ (c : ZMod N) • fun n : ℕ => ε ^ (n * ((c : ZMod N)).val) := by
    funext n
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hGne, mul_comm,
      hfourier (n : ZMod N)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hpow n c]
  rw [hcoeff, LSeries_smul]
  congr 1
  rw [LSeries_sum (fun c _ => (hsummand c).smul (θ⁻¹ (c : ZMod N)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LSeries_smul]

private lemma rpow_neg_sub_le {a s : ℝ} (ha : 0 < a) (hs : 1 ≤ s) :
    a ^ (-s) - (a + 1) ^ (-s) ≤ s * a ^ (-s - 1) := by
  have hf : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt (fun x : ℝ => x ^ (-s))
      (-s * x ^ (-s - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    simpa [neg_mul] using Real.hasDerivAt_rpow_const (x := x) (p := -s) (Or.inl hx0)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun x => x ^ (-s))
    (fun x => -s * x ^ (-s - 1)) (by linarith)
    (by have := hf; fun_prop (disch := intro x hx; nlinarith [hx.1, ha]))
    (fun x hx => hf x ⟨hx.1.le, hx.2.le⟩)
  rw [show (a + 1) - a = 1 by ring, div_one] at hξeq
  have hξ0 : 0 < ξ := lt_trans ha hξ.1
  have hmono : ξ ^ (-s - 1) ≤ a ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos ha hξ.1.le (by linarith)
  have hcast : a ^ (-s) - (a + 1) ^ (-s) = s * ξ ^ (-s - 1) := by
    have : -s * ξ ^ (-s - 1) = (a + 1) ^ (-s) - a ^ (-s) := hξeq
    nlinarith [this]
  rw [hcast]
  exact mul_le_mul_of_nonneg_left hmono (by linarith)

private lemma tendsto_LSeries_pow_boundary {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    Filter.Tendsto (fun s : ℝ => LSeries (fun n => w ^ n) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-Complex.log (1 - w))) := by
  classical
  have hw0 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr fun h => hw1 h.symm
  have hpos : 0 < ‖1 - w‖ := norm_pos_iff.mpr hw0
  set B : ℕ → ℂ := fun n => ∑ i ∈ Finset.range n, w ^ (i + 1) with hB
  have hBbound : ∀ n, ‖B n‖ ≤ 2 / ‖1 - w‖ := by
    intro n
    have hsplit : B n = w * ∑ i ∈ Finset.range n, w ^ i := by
      rw [hB, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, geom_sum_eq hw1 n, norm_mul, norm_div]
    have hzn : ‖w ^ n - 1‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [norm_pow, hw, one_pow, norm_one]; norm_num)
    rw [show ‖w - 1‖ = ‖1 - w‖ by rw [← norm_neg, neg_sub], hw, one_mul,
      div_le_div_iff_of_pos_right hpos]
    exact hzn
  set d : ℝ → ℕ → ℝ := fun s n => (↑(n + 1) : ℝ) ^ (-s) - (↑(n + 2) : ℝ) ^ (-s) with hd
  set g : ℝ → ℂ := fun s => ∑' n : ℕ, (d s n : ℂ) * B (n + 1) with hg
  have hterm : ∀ (s : ℝ) (n : ℕ),
      LSeries.term (fun n => w ^ n) (s : ℂ) (n + 1)
        = w ^ (n + 1) * (((↑(n + 1) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro s n
    have hbase : (((↑(n + 1) : ℝ) ^ (-s) : ℝ) : ℂ) = (((↑(n + 1) : ℂ)) ^ (s : ℂ))⁻¹ := by
      rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast, Complex.ofReal_neg,
        Complex.cpow_neg]
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), hbase, div_eq_mul_inv]
  have hd_nonneg : ∀ {s : ℝ}, 0 < s → ∀ n, 0 ≤ d s n := by
    intro s hs n
    rw [hd]
    have : (↑(n + 2) : ℝ) ^ (-s) ≤ (↑(n + 1) : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.le_succ _) (by linarith)
    linarith
  have hbase1 : ∀ n : ℕ, (1 : ℝ) ≤ (↑(n + 1) : ℝ) := fun n => by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hd_le : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 → ∀ n, d s n ≤ 2 * (↑(n + 1) : ℝ) ^ (-(2 : ℝ)) := by
    intro s hs1 hs2 n
    have hmvt := rpow_neg_sub_le (a := (↑(n + 1) : ℝ)) (s := s) (by positivity) hs1
    have hcast : ((↑(n + 1) : ℝ) + 1) = (↑(n + 2) : ℝ) := by push_cast; ring
    rw [hcast] at hmvt
    calc d s n ≤ s * (↑(n + 1) : ℝ) ^ (-s - 1) := hmvt
      _ ≤ 2 * (↑(n + 1) : ℝ) ^ (-(2 : ℝ)) :=
            mul_le_mul hs2 (Real.rpow_le_rpow_of_exponent_le (hbase1 n) (by linarith))
              (Real.rpow_nonneg (by positivity) _) (by norm_num)
  have hrpow_summable : Summable (fun n : ℕ => (↑(n + 1) : ℝ) ^ (-(2 : ℝ))) := by
    have hf : Summable (fun n : ℕ => (↑n : ℝ) ^ (-(2 : ℝ))) := by
      refine ((Real.summable_nat_rpow_inv (p := 2)).mpr one_lt_two).congr fun n => ?_
      rw [Real.rpow_neg (by positivity)]
    exact (summable_nat_add_iff 1).mpr hf
  set u : ℕ → ℝ := fun n => 2 * (↑(n + 1) : ℝ) ^ (-(2 : ℝ)) * (2 / ‖1 - w‖) with hu
  have hu_summable : Summable u :=
    ((hrpow_summable.mul_left 2).mul_right (2 / ‖1 - w‖))
  have hsummand_le : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 → ∀ n,
      ‖(d s n : ℂ) * B (n + 1)‖ ≤ u n := by
    intro s hs1 hs2 n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hd_nonneg (by linarith) n), hu]
    exact mul_le_mul (hd_le hs1 hs2 n) (hBbound (n + 1)) (norm_nonneg _) (by positivity)
  have hg_summable : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 → Summable (fun n => (d s n : ℂ) * B (n + 1)) :=
    fun hs1 hs2 => Summable.of_norm_bounded hu_summable (hsummand_le hs1 hs2)
  set f : ℝ → ℕ → ℂ := fun s i => (((↑(i + 1) : ℝ) ^ (-s) : ℝ) : ℂ) with hf
  have hSBP : ∀ (s : ℝ) (N : ℕ),
      ∑ i ∈ Finset.range N, LSeries.term (fun n => w ^ n) (s : ℂ) (i + 1)
        = f s (N - 1) * B N + ∑ i ∈ Finset.range (N - 1), (d s i : ℂ) * B (i + 1) := by
    intro s N
    have hrw : ∀ i ∈ Finset.range N,
        LSeries.term (fun n => w ^ n) (s : ℂ) (i + 1) = f s i • w ^ (i + 1) := by
      intro i _; rw [hterm s i, hf, smul_eq_mul, mul_comm]
    have hsumeq : ∑ i ∈ Finset.range (N - 1),
        (f s (i + 1) - f s i) • (∑ j ∈ Finset.range (i + 1), w ^ (j + 1))
          = -∑ i ∈ Finset.range (N - 1), (d s i : ℂ) * B (i + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcast : (d s i : ℂ) = f s i - f s (i + 1) := by
        simp only [hf, hd]
        rw [show (i + 1 + 1) = i + 2 from rfl, Complex.ofReal_sub]
      rw [hcast, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hrw, Finset.sum_range_by_parts (f s) (fun i => w ^ (i + 1)) N,
      smul_eq_mul, hsumeq, sub_neg_eq_add]
  have hpartial : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 →
      Filter.Tendsto (fun N => ∑ i ∈ Finset.range N,
        LSeries.term (fun n => w ^ n) (s : ℂ) (i + 1)) Filter.atTop (nhds (g s)) := by
    intro s hs1 hs2
    simp_rw [hSBP s]
    rw [show g s = 0 + g s by ring]
    refine Filter.Tendsto.add ?_ ?_
    · refine squeeze_zero_norm (f := fun N => f s (N - 1) * B N)
        (a := fun N => (↑N : ℝ) ^ (-s) * (2 / ‖1 - w‖)) (fun N => ?_) ?_
      · rw [norm_mul, hf, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp only [hB, Finset.range_zero, Finset.sum_empty, mul_zero, norm_zero]
          positivity
        · rw [show (N - 1 + 1) = N from Nat.succ_pred_eq_of_pos hN]
          exact mul_le_mul_of_nonneg_left (hBbound N) (Real.rpow_nonneg (by positivity) _)
      · rw [show (0 : ℝ) = 0 * (2 / ‖1 - w‖) by ring]
        refine Filter.Tendsto.mul_const _ ?_
        exact (tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < s)).comp
          tendsto_natCast_atTop_atTop
    · rw [hg]
      exact ((hg_summable hs1 hs2).hasSum.tendsto_sum_nat).comp (Filter.tendsto_sub_atTop_nat 1)
  have hreindex : ∀ (s : ℝ) (N : ℕ),
      ∑ i ∈ Finset.range N, LSeries.term (fun n => w ^ n) (s : ℂ) (i + 1)
        = ∑ m ∈ Finset.range (N + 1), LSeries.term (fun n => w ^ n) (s : ℂ) m := by
    intro s N
    rw [Finset.sum_range_succ' (LSeries.term (fun n => w ^ n) (s : ℂ)) N, LSeries.term_zero,
      add_zero]
  have hg_eq : ∀ {s : ℝ}, 1 < s → s ≤ 2 → g s = LSeries (fun n => w ^ n) (s : ℂ) := by
    intro s hs1 hs2
    have hLs : LSeriesSummable (fun n => w ^ n) (s : ℂ) := by
      refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) (by simpa using hs1)
      rw [norm_pow, hw, one_pow]
    refine tendsto_nhds_unique (hpartial hs1.le hs2) ?_
    simp_rw [hreindex s]
    exact (hLs.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hg_one : g 1 = -Complex.log (1 - w) := by
    refine tendsto_nhds_unique (hpartial le_rfl one_le_two) ?_
    refine (tendsto_sum_pow_div_eq_neg_log hw hw1).congr fun N => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero i), Complex.ofReal_one, Complex.cpow_one,
      pow_succ]
    push_cast
    ring
  have hg_cont : ContinuousOn g (Set.Icc 1 2) := by
    rw [hg]
    refine continuousOn_tsum (fun n => ?_) hu_summable (fun n s hs => ?_)
    · refine Continuous.continuousOn ?_
      refine ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      rw [hd]
      exact ((Real.continuous_const_rpow (by positivity)).comp continuous_neg).sub
        ((Real.continuous_const_rpow (by positivity)).comp continuous_neg)
    · exact hsummand_le hs.1 hs.2 n
  rw [← hg_one]
  have hmem : Set.Icc (1 : ℝ) 2 ∈ nhdsWithin 1 (Set.Ioi 1) := by
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _ (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))) ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨le_of_lt hx1, le_of_lt hx2⟩
  refine Filter.Tendsto.congr' ?_
    ((hg_cont.continuousWithinAt (Set.left_mem_Icc.mpr one_le_two)).mono_left
      (nhdsWithin_le_iff.mpr hmem))
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))]
    with s hs hs2
  exact hg_eq hs (le_of_lt hs2)

/-- **RJW Theorem 6.1(i)** (`s=1 theorem`(i), TeX 1989–1991): "We have
`L(θ,1) = −G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε_N^c)`." -/
theorem LFunction_one_eq {θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive)
    (hθ1 : θ ≠ 1) {ε : ℂ} (hε : IsPrimitiveRoot ε N) :
    LFunction θ 1
      = -(gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹
        * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N)
          * Complex.log (1 - ε ^ ((c : ZMod N)).val) := by
  classical
  have hN : 1 < N := by
    rcases Nat.lt_or_ge 1 N with h | h
    · exact h
    · exact absurd (DirichletCharacter.level_one' θ
        (by have := NeZero.pos N; lia)) hθ1
  haveI : Fact (1 < N) := ⟨hN⟩
  set G := gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one) with hG
  have hwc : ∀ c : (ZMod N)ˣ, ‖ε ^ ((c : ZMod N)).val‖ = 1 := fun c => by
    rw [norm_pow, IsPrimitiveRoot.norm'_eq_one hε (NeZero.ne N), one_pow]
  have hwc1 : ∀ c : (ZMod N)ˣ, ε ^ ((c : ZMod N)).val ≠ 1 := by
    intro c hc
    rw [hε.pow_eq_one_iff_dvd] at hc
    have hpos : 0 < ((c : ZMod N)).val := ZMod.val_pos.mpr (Units.ne_zero c)
    exact absurd (Nat.le_of_dvd hpos hc) (by have := ZMod.val_lt (c : ZMod N); lia)
  have hbdry : Filter.Tendsto
      (fun s : ℝ => G⁻¹ * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N)
        * LSeries (fun n => ε ^ (n * ((c : ZMod N)).val)) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (G⁻¹ * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N)
        * (-Complex.log (1 - ε ^ ((c : ZMod N)).val)))) := by
    refine Filter.Tendsto.const_mul _ (tendsto_finsetSum _ fun c _ => ?_)
    have hpow : (fun n => ε ^ (n * ((c : ZMod N)).val))
        = (fun n => (ε ^ ((c : ZMod N)).val) ^ n) := by
      funext n; rw [mul_comm, pow_mul]
    rw [hpow]
    exact (tendsto_LSeries_pow_boundary (hwc c) (hwc1 c)).const_mul (θ⁻¹ (c : ZMod N))
  have hcont : Filter.Tendsto (fun s : ℝ => LFunction θ (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (LFunction θ 1)) := by
    have hc : Continuous (fun s : ℝ => LFunction θ (s : ℂ)) :=
      (differentiable_LFunction hθ1).continuous.comp Complex.continuous_ofReal
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Ioi 1))
    simpa using this
  have heq : (fun s : ℝ => LFunction θ (s : ℂ))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun s : ℝ => G⁻¹ * ∑ c : (ZMod N)ˣ,
        θ⁻¹ (c : ZMod N) * LSeries (fun n => ε ^ (n * ((c : ZMod N)).val)) (s : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsre : 1 < (s : ℂ).re := by simpa using (Set.mem_Ioi.mp hs)
    rw [LFunction_eq_LSeries θ hsre, LSeries_eq_gaussSum_inv_mul_sum hθ hθ1 hε hsre, hG]
  rw [tendsto_nhds_unique hcont (hbdry.congr' heq.symm), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end ValuesAtOneComplex

end PadicLFunctions
