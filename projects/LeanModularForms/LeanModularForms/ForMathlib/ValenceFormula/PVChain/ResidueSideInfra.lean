/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.PVChain.OnCurveCapture
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase
import LeanModularForms.ForMathlib.ModularInvariance
import LeanModularForms.ForMathlib.ValenceFormula.Boundary.Smooth

/-!
# Residue-Side Infrastructure for the PV Chain

Infrastructure lemmas needed to apply `generalizedResidueTheorem'` to
`logDeriv (modularFormCompOfComplex f)` on `fdBoundary_H H`.

## Main Results

* `hasSimplePoleAt_logDeriv_of_zero'` — logDeriv f has `HasSimplePoleAt` at zeros
* `hasSimplePoleAt_logDeriv_at_nonzero` — trivial `HasSimplePoleAt` at non-zeros
* `fdBox_isOpen`, `fdBox_convex` — fdBox properties
* `fdBoundary_H_mem_fdBox'` — curve is inside fdBox
* `residueSimplePole_logDeriv_eq_order` — residue = order at zeros
* `residueSimplePole_logDeriv_eq_zero_at_nonzero` — residue = 0 at non-zeros
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

private instance : IsScalarTower ℝ ℂ ℂ := inferInstance

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The box `fdBox M` is open as an intersection of open half-planes. -/
lemma fdBox_isOpen (M : ℝ) : IsOpen (fdBox M) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter <|
    (isOpen_lt Complex.continuous_re continuous_const).inter <|
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)

/-- The box `fdBox M` is convex, being an intersection of open half-planes. -/
lemma fdBox_convex (M : ℝ) : Convex ℝ (fdBox M) := by
  have h_inter : fdBox M = {c | -1 < c.re} ∩ {c | c.re < 1} ∩
      {c : ℂ | (1:ℝ)/2 < c.im} ∩ {c | c.im < M} := by
    ext z; simp only [fdBox, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h_inter]
  exact (((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
    (convex_halfSpace_im_gt _)).inter (convex_halfSpace_im_lt _)

/-- The finite set of zeros of `f` lying in `fdBox M`. -/
noncomputable def allZerosInFdBox {M : ℝ} (hM : (1:ℝ)/2 < M) : Finset ℂ :=
  (modularForm_finitely_many_zeros_in_fdBox f hf hM).toFinset

/-- Membership in `allZerosInFdBox` unfolds to membership in `fdBox M` together with the
zero condition. -/
lemma mem_allZerosInFdBox_iff {M : ℝ} (hM : (1:ℝ)/2 < M) {z : ℂ} :
    z ∈ allZerosInFdBox f hf hM ↔ z ∈ fdBox M ∧ modularFormCompOfComplex f z = 0 := by
  simp only [allZerosInFdBox, Set.Finite.mem_toFinset, Set.mem_sep_iff]

private lemma analyticAt_modform (z : ℂ) (hz : 0 < z.im) :
    AnalyticAt ℂ (modularFormCompOfComplex f) z :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)

/-- `logDeriv f` is analytic at any point of the upper half-plane where `f` does not vanish. -/
lemma analyticAt_logDeriv_off_zeros' (z : ℂ) (hz : 0 < z.im)
    (hfz : modularFormCompOfComplex f z ≠ 0) :
    AnalyticAt ℂ (logDeriv (modularFormCompOfComplex f)) z :=
  (analyticAt_modform f z hz).deriv.fun_div (analyticAt_modform f z hz) hfz

include hf in
private lemma modform_not_locally_zero (s : ℍ) :
    analyticOrderAt (modularFormCompOfComplex f) (s : ℂ) ≠ ⊤ := by
  intro h_top
  rw [analyticOrderAt_eq_top] at h_top
  have h_analOn : AnalyticOnNhd ℂ (modularFormCompOfComplex f) {w | 0 < w.im} :=
    fun w hw ↦ (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    (Complex.isConnected_of_upperHalfPlane (r := 0)
      (fun w (hw : 0 < w.im) ↦ hw) (fun w (hw : 0 < w.im) ↦ le_of_lt hw)).isPreconnected
  have h_zero_on := h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    h_preconn s.im_pos (h_top.filter_mono nhdsWithin_le_nhds).frequently
  apply hf
  ext z
  simpa only [ModularForm.coe_zero, Pi.zero_apply, modularFormCompOfComplex,
    Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h_zero_on z.im_pos

include hf in
/-- logDeriv of a modular form has a simple pole at each zero, with the factorization
`logDeriv F(z) = n/(z-s) + logDeriv g(z)` where `n` is the vanishing order and
`g` is analytic with `g(s) ≠ 0`. -/
theorem hasSimplePoleAt_logDeriv_of_zero_full (s : ℍ) (hs : f s = 0) :
    ∃ (n : ℤ) (g : ℂ → ℂ), n > 0 ∧ AnalyticAt ℂ g (s : ℂ) ∧ g (s : ℂ) ≠ 0 ∧
      n = analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) ∧
      ∀ᶠ z in 𝓝 (s : ℂ), z ≠ (s : ℂ) →
        logDeriv (modularFormCompOfComplex f) z =
          n / (z - (s : ℂ)) + logDeriv g z := by
  have h_analytic := analyticAt_modform f (s : ℂ) s.im_pos
  have h_order_ne_zero : analyticOrderAt (modularFormCompOfComplex f) (s : ℂ) ≠ 0 := by
    rw [h_analytic.analyticOrderAt_ne_zero]
    simpa [modularFormCompOfComplex, UpperHalfPlane.ofComplex_apply] using hs
  obtain ⟨g, hg_analytic, hg_ne_zero, hg_eq⟩ :=
    h_analytic.analyticOrderAt_ne_top.mp (modform_not_locally_zero f hf s)
  set n : ℕ := analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) with hn_def
  have hn_pos : (n : ℤ) > 0 := by
    have : n ≠ 0 := fun h_eq_zero ↦ h_order_ne_zero (by
      rw [← Nat.cast_analyticOrderNatAt (modform_not_locally_zero f hf s), ← hn_def, h_eq_zero,
        Nat.cast_zero])
    omega
  refine ⟨n, g, hn_pos, hg_analytic, hg_ne_zero, rfl, ?_⟩
  have h_all : ∀ᶠ z in 𝓝 (s : ℂ), ((modularFormCompOfComplex f) z = (z - (s : ℂ)) ^ n • g z) ∧
      AnalyticAt ℂ g z ∧ g z ≠ 0 := by
    filter_upwards [hg_eq, hg_analytic.eventually_analyticAt,
      hg_analytic.continuousAt.eventually_ne hg_ne_zero] with z hz hza hzne using ⟨hz, hza, hzne⟩
  obtain ⟨U, hU_mem, hU_cond⟩ := Filter.eventually_iff_exists_mem.mp h_all
  obtain ⟨V, hV_sub, hV_open, hs_in_V⟩ := mem_nhds_iff.mp hU_mem
  filter_upwards [IsOpen.mem_nhds hV_open hs_in_V] with z hz_in_V hz_ne_s
  have ⟨hz, hz_analytic, hz_ne_zero⟩ := hU_cond z (hV_sub hz_in_V)
  have h_eq_mul : modularFormCompOfComplex f z = (z - (s : ℂ)) ^ n * g z := hz
  have hzs : z - (s : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne_s
  have h_pow_ne_zero : (z - (s : ℂ)) ^ n ≠ 0 := pow_ne_zero _ hzs
  have h_logDeriv_pow :
      logDeriv (fun w ↦ (w - (s : ℂ)) ^ n) z = ↑↑n / (z - (s : ℂ)) := by
    have h_hd : HasDerivAt (fun w ↦ (w - (s : ℂ)) ^ n) (↑n * (z - (s : ℂ)) ^ (n - 1)) z := by
      convert ((hasDerivAt_id z).sub (hasDerivAt_const z (s : ℂ))).pow n using 1
      all_goals first | rfl | simp
    rw [logDeriv_apply, h_hd.deriv, div_eq_div_iff h_pow_ne_zero hzs, mul_assoc, ← pow_succ,
      show n - 1 + 1 = n from by omega]
  have h_eq_at_z : (modularFormCompOfComplex f) =ᶠ[𝓝 z]
      (fun w ↦ (w - (s : ℂ)) ^ n * g w) :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨V, IsOpen.mem_nhds hV_open hz_in_V, fun w hw ↦ (hU_cond w (hV_sub hw)).1⟩
  calc logDeriv (modularFormCompOfComplex f) z
      = logDeriv (fun w ↦ (w - (s : ℂ)) ^ n * g w) z := by
        unfold logDeriv
        simp only [Pi.div_apply, h_eq_at_z.deriv_eq, h_eq_mul]
    _ = logDeriv (fun w ↦ (w - (s : ℂ)) ^ n) z + logDeriv g z :=
        logDeriv_mul z h_pow_ne_zero hz_ne_zero
          ((differentiableAt_id.sub (differentiableAt_const _)).pow _) hz_analytic.differentiableAt
    _ = ↑↑n / (z - (s : ℂ)) + logDeriv g z := by rw [h_logDeriv_pow]

include hf in
/-- logDeriv of a modular form has `HasSimplePoleAt` at each zero. -/
theorem hasSimplePoleAt_logDeriv_of_zero' (s : ℍ) (hs : f s = 0) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) (s : ℂ) := by
  obtain ⟨n, g, _, hg_analytic, hg_ne_zero, _, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero_full f hf s hs
  refine ⟨(n : ℂ), logDeriv g, hg_analytic.deriv.fun_div hg_analytic hg_ne_zero, ?_⟩
  rw [eventually_nhdsWithin_iff]
  simpa using h_formula

omit hf in
/-- `HasSimplePoleAt` of logDeriv at a non-zero point (trivial: c = 0, g = logDeriv f). -/
lemma hasSimplePoleAt_logDeriv_at_nonzero (z : ℂ) (hz_im : 0 < z.im)
    (hz_nz : modularFormCompOfComplex f z ≠ 0) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z :=
  ⟨0, logDeriv (modularFormCompOfComplex f),
    analyticAt_logDeriv_off_zeros' f z hz_im hz_nz, by filter_upwards with _; simp⟩

include hf in
/-- `HasSimplePoleAt` for any point with positive imaginary part. -/
lemma hasSimplePoleAt_logDeriv_at_point (z : ℂ) (hz_im : 0 < z.im) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z := by
  by_cases hz : modularFormCompOfComplex f z = 0
  · refine hasSimplePoleAt_logDeriv_of_zero' f hf ⟨z, hz_im⟩ ?_
    simpa [modularFormCompOfComplex, UpperHalfPlane.ofComplex_apply_of_im_pos hz_im] using hz
  · exact hasSimplePoleAt_logDeriv_at_nonzero f z hz_im hz

include hf in
private lemma orderOfVanishingAt'_eq_analyticOrderNatAt (s : ℍ) (_hs : f s = 0) :
    orderOfVanishingAt' (⇑f) s = (analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) : ℤ) := by
  unfold orderOfVanishingAt'
  set g₁ := fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0
  set g₂ := modularFormCompOfComplex f
  have h_eq : g₁ =ᶠ[𝓝[≠] (s : ℂ)] g₂ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds s.im_pos] with w hw
    simp only [g₁, g₂, modularFormCompOfComplex, Function.comp_apply, dif_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rw [meromorphicOrderAt_congr h_eq,
    (analyticAt_modform f (s : ℂ) s.im_pos).meromorphicOrderAt_eq]
  cases h : analyticOrderAt g₂ (s : ℂ) with
  | top => exact absurd h (modform_not_locally_zero f hf s)
  | coe n =>
    simp only [analyticOrderNatAt, h, ENat.toNat_coe]
    norm_cast

include hf in
/-- At a zero `s` of `f`, `residueSimplePole(logDeriv f, s) = orderOfVanishingAt'(f, s)`. -/
theorem residueSimplePole_logDeriv_eq_order (s : ℍ) (hs : f s = 0) :
    residueSimplePole (logDeriv (modularFormCompOfComplex f)) (s : ℂ) =
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
  obtain ⟨n, g, _, hg_analytic, hg_ne_zero, hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero_full f hf s hs
  have h_decomp : ∀ᶠ z in 𝓝[≠] (s : ℂ),
      logDeriv (modularFormCompOfComplex f) z = (n : ℂ) / (z - (s : ℂ)) + logDeriv g z := by
    rw [eventually_nhdsWithin_iff]
    simpa using h_formula
  rw [residue_simple_pole_eq_laurent _ (s : ℂ) (n : ℂ) (logDeriv g)
    (hg_analytic.deriv.fun_div hg_analytic hg_ne_zero) h_decomp, hn_eq]
  exact_mod_cast (orderOfVanishingAt'_eq_analyticOrderNatAt f hf s hs).symm

omit hf in
/-- At a non-zero point, `residueSimplePole(logDeriv f, z) = 0`. -/
lemma residueSimplePole_logDeriv_eq_zero_at_nonzero (z : ℂ) (hz_im : 0 < z.im)
    (hz_nz : modularFormCompOfComplex f z ≠ 0) :
    residueSimplePole (logDeriv (modularFormCompOfComplex f)) z = 0 := by
  have h_prod : Tendsto (fun w ↦ (w - z) * logDeriv (modularFormCompOfComplex f) w)
      (𝓝[≠] z) (𝓝 (0 * logDeriv (modularFormCompOfComplex f) z)) := by
    refine Tendsto.mul ?_ ((analyticAt_logDeriv_off_zeros' f z hz_im hz_nz).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
    rw [show (0 : ℂ) = z - z from (sub_self z).symm]
    exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [zero_mul] at h_prod
  exact h_prod.limUnder_eq

omit f hf in
/-- For `H ≥ 1` and `M > H`, `fdBoundary_H H t ∈ fdBox M` for `t ∈ [0, 5]`. -/
lemma fdBoundary_H_mem_fdBox' {H M : ℝ} (hH : 1 ≤ H) (hM : H < M)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) : fdBoundary_H H t ∈ fdBox M := by
  have h_re_abs := abs_le.mp (fdBoundary_H_re_abs_le_half H t ht)
  have hH_sqrt3 : Real.sqrt 3 / 2 ≤ H := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have h_half_lt_sqrt3 : (1:ℝ)/2 < Real.sqrt 3 / 2 := by
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num),
      Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
  exact ⟨by linarith, by linarith,
    lt_of_lt_of_le h_half_lt_sqrt3 (fdBoundary_H_im_ge_sqrt3_div_2 H hH_sqrt3 t ht),
    lt_of_le_of_lt (fdBoundary_H_im_le_H hH t ht) hM⟩

omit f hf in
/-- A finite set of complex numbers is discrete: each point has a positive distance to every
other point. -/
lemma finset_discrete (S0 : Finset ℂ) :
    ∀ s ∈ (↑S0 : Set ℂ), ∃ ε > 0, ∀ s' ∈ (↑S0 : Set ℂ), s' ≠ s → ε ≤ ‖s' - s‖ := by
  intro s _
  rcases (S0.erase s).eq_empty_or_nonempty with h_empty | h_ne
  · exact ⟨1, one_pos, fun s' hs' hne ↦
      absurd (h_empty ▸ Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hs'⟩ : s' ∈ (∅ : Finset ℂ))
        (Finset.notMem_empty _)⟩
  · set img := (S0.erase s).image (fun s' ↦ ‖s' - s‖)
    refine ⟨img.min' (h_ne.image _), ?_, fun s' hs' hne ↦ Finset.min'_le _ _ <|
      Finset.mem_image.mpr ⟨s', Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hs'⟩, rfl⟩⟩
    obtain ⟨s', hs', hs'_eq⟩ := Finset.mem_image.mp (Finset.min'_mem img (h_ne.image _))
    rw [← hs'_eq]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_erase.mp hs').1)

omit f hf in
/-- CPV of `c/(z - s)` exists when the curve avoids `s` (limit is just the regular integral). -/
lemma cpvExists_of_off_curve (γ : ℝ → ℂ) (hγ_cont : Continuous γ) (a b : ℝ) (s : ℂ)
    (c : ℂ) (hab : a ≤ b) (h_off : ∀ t ∈ Icc a b, γ t ≠ s) :
    CauchyPrincipalValueExists' (fun z ↦ c / (z - s)) γ a b s :=
  cauchyPrincipalValueExists'_of_avoidance hγ_cont.continuousOn hab h_off

omit f hf in
/-- CPV of `c · (z - s)⁻¹` from CPV of `(z - s)⁻¹` by scaling. -/
lemma cpvExists_scale (γ : ℝ → ℂ) (a b : ℝ) (s c : ℂ)
    (h : CauchyPrincipalValueExists' (fun z ↦ (z - s)⁻¹) γ a b s) :
    CauchyPrincipalValueExists' (fun z ↦ c / (z - s)) γ a b s := by
  obtain ⟨L, hL⟩ := h
  exact ⟨c * L, (hL.const_mul c).congr_along_curve fun t ↦ by
    rw [div_eq_mul_inv]⟩

omit f hf in
private lemma residueSimplePole_congr_local (F G : ℂ → ℂ) (z₀ : ℂ)
    (h : F =ᶠ[𝓝[≠] z₀] G) : residueSimplePole F z₀ = residueSimplePole G z₀ := by
  unfold residueSimplePole
  exact congrArg lim (Filter.map_congr (h.mono fun z hz ↦ congr_arg _ hz))

omit f hf in
/-- Patched `logDeriv` for `ContinuousAt` at zeros.

At zeros of `f`, Lean's `div_zero` convention makes `logDeriv f(z) = 0/0 = 0`,
but the limit from the punctured neighborhood is `g(z) ≠ 0`. This breaks the
`ContinuousAt` hypothesis of `generalizedResidueTheorem'`.

The fix: define `logDerivPatched F S0` which equals `F` away from `S0` and
equals the regular part `g(z)` at each `z ∈ S0` (from the `HasSimplePoleAt`
decomposition). This makes the `ContinuousAt` hypothesis hold. -/
noncomputable def logDerivPatched (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) : ℂ → ℂ := fun z ↦
  if h : z ∈ S0 then
    Classical.choose (Classical.choose_spec (hsp z h)) z
  else F z

omit f hf in
/-- Off the patching set `S0`, `logDerivPatched F S0 = F`. -/
lemma logDerivPatched_eq_raw_off (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) {z : ℂ} (hz : z ∉ S0) :
    logDerivPatched F S0 hsp z = F z :=
  dif_neg hz

omit f hf in
private lemma logDerivPatched_eventuallyEq_raw_punctured (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (_hs : s ∈ S0) :
    logDerivPatched F S0 hsp =ᶠ[𝓝[≠] s] F := by
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [(S0.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds
    (by simp [Set.mem_compl_iff] : s ∈ ((↑(S0.erase s) : Set ℂ)ᶜ))] with z hz hzne
  exact dif_neg (fun habs ↦ hz (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzne, habs⟩)))

omit f hf in
/-- The patched logDeriv still has a simple pole at every point of `S0`. -/
lemma hasSimplePoleAt_logDerivPatched (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    HasSimplePoleAt (logDerivPatched F S0 hsp) s := by
  obtain ⟨c, g, hg_an, hF_eq⟩ := hsp s hs
  refine ⟨c, g, hg_an, ?_⟩
  filter_upwards [logDerivPatched_eventuallyEq_raw_punctured F S0 hsp s hs, hF_eq] with z h1 h2
  rw [h1]; exact h2

omit f hf in
/-- The residue of the patched logDeriv matches the residue of `F` itself. -/
lemma residue_logDerivPatched_eq_raw (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    residueSimplePole (logDerivPatched F S0 hsp) s = residueSimplePole F s :=
  residueSimplePole_congr_local _ _ _ (logDerivPatched_eventuallyEq_raw_punctured F S0 hsp s hs)

omit f hf in
/-- The patched logDeriv satisfies `ContinuousAt` for `generalizedResidueTheorem'`. -/
lemma logDerivPatched_hf_ext (F : ℂ → ℂ) (S0 : Finset ℂ) (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) :
    ∀ s ∈ S0, ContinuousAt (fun z ↦ logDerivPatched F S0 hsp z -
        residueSimplePole (logDerivPatched F S0 hsp) s / (z - s)) s := by
  intro s hs
  set c := (hsp s hs).choose
  set g := (hsp s hs).choose_spec.choose
  have hg_an : AnalyticAt ℂ g s := (hsp s hs).choose_spec.choose_spec.1
  have hF_eq : ∀ᶠ z in 𝓝[≠] s, F z = c / (z - s) + g z := (hsp s hs).choose_spec.choose_spec.2
  rw [show residueSimplePole (logDerivPatched F S0 hsp) s = c by
    rw [residue_logDerivPatched_eq_raw F S0 hsp s hs]
    exact residue_simple_pole_eq_laurent _ _ _ _ hg_an hF_eq]
  refine ContinuousAt.congr hg_an.continuousAt ?_
  rw [eventually_nhdsWithin_iff] at hF_eq
  rw [Filter.EventuallyEq]
  filter_upwards [hF_eq, (S0.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds
    (Set.mem_compl_iff _ _ |>.mpr (Finset.notMem_erase s S0))] with z hz_F hz_compl
  by_cases hzs : z = s
  · subst hzs
    simp only [sub_self, div_zero, sub_zero]
    unfold logDerivPatched
    rw [dif_pos hs]
  · rw [logDerivPatched_eq_raw_off F S0 hsp
      (fun habs ↦ hz_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzs, habs⟩))),
      show F z = c / (z - s) + g z from hz_F hzs]
    ring

omit f hf in
/-- On the arc segments (1 < t ≤ 3), `fdBoundary_H H = fdBoundary`. -/
private lemma fdBoundary_H_eq_fdBoundary_on_13 (H : ℝ) {t : ℝ}
    (ht1 : ¬(t ≤ 1)) (ht3 : t ≤ 3) :
    fdBoundary_H H t = fdBoundary t := by
  unfold fdBoundary_H fdBoundary
  simp only [ht1, ↓reduceIte, ht3]

omit f hf in
private lemma norm_ge_one_of_normSq_ge_one {w : ℂ} (h : normSq w ≥ 1) : ‖w‖ ≥ 1 :=
  calc ‖w‖ = Real.sqrt (normSq w) := rfl
    _ ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

omit f hf in
/-- `‖fdBoundary_H H t‖ ≥ 1` for `t ∈ [0, 5]` when `H ≥ 1`. -/
lemma fdBoundary_H_norm_ge_one {H : ℝ} (hH : 1 ≤ H) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    ‖fdBoundary_H H t‖ ≥ 1 := by
  have hH_sqrt3 : Real.sqrt 3 / 2 ≤ H := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have side : ∀ (w : ℂ), |w.re| = 1/2 → w.im ≥ Real.sqrt 3 / 2 → ‖w‖ ≥ 1 := by
    intro w hre him
    have h_re_sq : w.re ^ 2 = 1/4 := by
      have : |w.re| ^ 2 = (1/2 : ℝ) ^ 2 := by rw [hre]
      nlinarith [sq_abs w.re]
    refine norm_ge_one_of_normSq_ge_one ?_
    rw [normSq_apply, show w.re * w.re = w.re ^ 2 from by ring, h_re_sq]
    nlinarith [mul_self_le_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) him,
               Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num)]
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1]
    apply side _ (by simp [fdBoundary_seg1_H, mul_re, I_re, I_im, ofReal_re, ofReal_im, div_ofNat])
    have := fdBoundary_H_im_ge_sqrt3_div_2 H hH_sqrt3 t ht
    rwa [fdBoundary_H_eq_seg1_H h1] at this
  · push Not at h1
    by_cases h3 : t ≤ 3
    · rw [fdBoundary_H_eq_fdBoundary_on_13 H (by linarith) h3]
      suffices ‖fdBoundary t‖ = 1 by linarith
      simp only [fdBoundary, show ¬(t ≤ 1) from by linarith, ↓reduceIte]
      split_ifs
      · change ‖fdBoundary_seg2 t‖ = 1
        unfold fdBoundary_seg2
        rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
            ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      · change ‖fdBoundary_seg3 t‖ = 1
        unfold fdBoundary_seg3
        rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
            ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
    · push Not at h3
      by_cases h4 : t ≤ 4
      · rw [fdBoundary_H_eq_seg4_H h3 h4]
        apply side _ (by
          simp [fdBoundary_seg4_H, mul_re, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
          ring)
        have := fdBoundary_H_im_ge_sqrt3_div_2 H hH_sqrt3 t ht
        rwa [fdBoundary_H_eq_seg4_H h3 h4] at this
      · push Not at h4
        rw [fdBoundary_H_eq_seg5_H h4]
        have him : (fdBoundary_seg5_H H t).im = H := by
          simp [fdBoundary_seg5_H, add_im, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
            div_ofNat]
        have him_ge : (fdBoundary_seg5_H H t).im ≥ 1 := by rw [him]; linarith
        refine norm_ge_one_of_normSq_ge_one ?_
        rw [normSq_apply]
        nlinarith [mul_self_nonneg (fdBoundary_seg5_H H t).re,
          mul_self_le_mul_self (by linarith : (0:ℝ) ≤ 1) him_ge]

omit f hf in
/-- The boundary `fdBoundary_H H` avoids every point NOT in the closed FD. -/
lemma off_curve_of_not_in_fd_H {H : ℝ} (hH : 1 ≤ H) (z₀ : ℂ)
    (hz₀_not_fd : ¬ (|z₀.re| ≤ 1/2 ∧ ‖z₀‖ ≥ 1)) :
    ∀ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t ≠ z₀ := by
  push Not at hz₀_not_fd
  intro t ht heq
  by_cases h_re : |z₀.re| ≤ 1/2
  · have h_norm_lt : ‖z₀‖ < 1 := hz₀_not_fd h_re
    linarith [heq ▸ fdBoundary_H_norm_ge_one hH t ht]
  · push Not at h_re
    linarith [heq ▸ fdBoundary_H_re_abs_le_half H t ht]

omit f hf in
/-- FTC: integral = 0 for a closed curve with slit-plane avoidance. -/
lemma ftc_integral_zero_of_closed_slit {γ : ℝ → ℂ} {z₀ : ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hγ_cont : Continuous γ) (hγ_closed : γ 0 = γ 5) (h_off : ∀ t ∈ Icc (0:ℝ) 5, γ t ≠ z₀)
    (h_slit : ∀ t ∈ Icc (0:ℝ) 5, ω * (γ t - z₀) ∈ Complex.slitPlane)
    (hγ_diff : ∀ t, t ∉ (fdBoundaryFullPartition : Finset ℝ) →
      DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo (0:ℝ) 5, t ∉ (fdBoundaryFullPartition : Finset ℝ) →
      ContinuousAt (deriv γ) t)
    (hγ_deriv_bdd : ∃ Mγ : ℝ, ∀ t ∈ Icc (0:ℝ) 5, ‖deriv γ t‖ ≤ Mγ) :
    ∫ t in (0:ℝ)..5, (γ t - z₀)⁻¹ * deriv γ t = 0 := by
  set F : ℝ → ℂ := fun t ↦ Complex.log (ω * (γ t - z₀)) with hF_def
  set F' : ℝ → ℂ := fun t ↦ (γ t - z₀)⁻¹ * deriv γ t with hF'_def
  have hF_cont : ContinuousOn F (Icc 0 5) :=
    ContinuousOn.clog (continuousOn_const.mul (hγ_cont.continuousOn.sub continuousOn_const)) h_slit
  have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 5 \ (↑fdBoundaryFullPartition : Set ℝ),
      HasDerivAt F (F' t) t := by
    intro t ⟨ht_ioo, ht_not_P⟩
    have h_inner : HasDerivAt (fun u ↦ ω * (γ u - z₀)) (ω * deriv γ t) t := by
      convert ((hγ_diff t (Finset.mem_coe.not.mp ht_not_P)).hasDerivAt.sub_const z₀).const_mul ω
        using 1
    convert (@HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ IsScalarTower.right _ _ _ _
      (Complex.hasDerivAt_log (h_slit t (Ioo_subset_Icc_self ht_ioo))) h_inner) using 1
    all_goals try rfl
    rw [smul_eq_mul]
    have hωne : ω * (γ t - z₀) ≠ 0 :=
      mul_ne_zero hω (sub_ne_zero.mpr (h_off t (Ioo_subset_Icc_self ht_ioo)))
    simp only [hF'_def]
    field_simp
  have hF'_int : IntervalIntegrable F' volume 0 5 := by
    obtain ⟨Mγ, hMγ⟩ := hγ_deriv_bdd
    have hg_cont : ContinuousOn (fun z ↦ (z - z₀)⁻¹) (γ '' Icc 0 5) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun _ ⟨t, ht, hzt⟩ ↦ hzt ▸
        sub_ne_zero.mpr (h_off t ht)
    obtain ⟨Mg, hMg⟩ := continuousOn_image_bounded hγ_cont.continuousOn hg_cont
    have h_cont : ContinuousOn F' (Icc 0 5 \ fdBoundaryFullPartition) := by
      intro t ⟨ht_Icc, ht_not_P⟩
      change ContinuousWithinAt (fun t ↦ (γ t - z₀)⁻¹ * deriv γ t) _ t
      have ht_Ioo : t ∈ Ioo (0:ℝ) 5 :=
        ⟨lt_of_le_of_ne ht_Icc.1 fun h ↦ ht_not_P (by rw [← h]; simp [fdBoundaryFullPartition]),
         lt_of_le_of_ne ht_Icc.2 fun h ↦ ht_not_P (by rw [h]; simp [fdBoundaryFullPartition])⟩
      exact ((hγ_cont.continuousAt.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (h_off t ht_Icc))).continuousWithinAt.mul
        (hγ_deriv_cont t ht_Ioo (Finset.mem_coe.not.mp ht_not_P)).continuousWithinAt
    have h_bound : ∀ t ∈ Icc (0:ℝ) 5, ‖F' t‖ ≤ Mg * Mγ := fun t ht ↦ by
      change ‖(γ t - z₀)⁻¹ * deriv γ t‖ ≤ Mg * Mγ
      rw [norm_mul]
      exact mul_le_mul (hMg _ ⟨t, ht, rfl⟩) (hMγ t ht) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hMg _ ⟨t, ht, rfl⟩))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
    exact (integrableOn_of_bounded_aeMeasurable (Mg * Mγ)
      (aEStronglyMeasurable_of_continuousOn_off_finite h_cont) h_bound).mono_set
      Ioc_subset_Icc_self
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F' (by norm_num : (0:ℝ) ≤ 5)
    fdBoundaryFullPartition.countable_toSet hF_cont hF_deriv hF'_int]
  change F 5 - F 0 = 0
  simp only [hF_def, hγ_closed]
  ring

include hf in
/-- Winding number = 0 for points in `fdBox` but NOT in the fundamental domain. -/
lemma winding_zero_for_non_fd_point_H_geo (S : Finset UpperHalfPlane)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH : 1 ≤ H) (z₀ : ℂ)
    (hz₀_zero : z₀ ∈ allZerosInFdBox f hf (show (1:ℝ)/2 < H + 1 by linarith))
    (hz₀_not_S : ∀ s ∈ S, (s : ℂ) ≠ z₀) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = 0 := by
  have hz₀_box := ((mem_allZerosInFdBox_iff f hf _).mp hz₀_zero).1
  have hz₀_im_pos : 0 < z₀.im := fdBox_im_pos hz₀_box
  have hz₀_not_fd : ¬ (|z₀.re| ≤ 1/2 ∧ ‖z₀‖ ≥ 1) := by
    intro ⟨h_re, h_norm⟩
    set s : ℍ := ⟨z₀, hz₀_im_pos⟩
    have h_fs : f s = 0 := by
      have := ((mem_allZerosInFdBox_iff f hf _).mp hz₀_zero).2
      change (f ∘ UpperHalfPlane.ofComplex) z₀ = 0 at this
      rwa [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz₀_im_pos] at this
    have h_fd : s ∈ 𝒟 := by
      refine ⟨?_, h_re⟩
      change 1 ≤ Complex.normSq z₀
      have h_sq := Complex.sq_norm z₀
      rw [Complex.normSq_apply] at h_sq ⊢
      nlinarith [h_sq]
    exact hz₀_not_S s (hS_complete s h_fd
      (orderOfVanishingAt'_ne_zero_of_eq_zeroFM f hf s h_fs)) rfl
  have h_off : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t ≠ z₀ :=
    off_curve_of_not_in_fd_H hH z₀ hz₀_not_fd
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have h_classical := generalizedWindingNumber_eq_classical_away (fdBoundary_HCurve H) z₀ h_off
  simp only [fdBoundary_HCurve, PiecewiseC1Curve.ofIccPartition_toFun,
    PiecewiseC1Curve.ofIccPartition_a, PiecewiseC1Curve.ofIccPartition_b] at h_classical
  rw [h_classical]
  suffices h_int : ∫ t in (0:ℝ)..5, (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t = 0 by
    erw [h_int]; simp
  push Not at hz₀_not_fd
  have hγ_diff : ∀ t, t ∉ (fdBoundaryFullPartition : Finset ℝ) →
      DifferentiableAt ℝ (fdBoundary_H H) t := fun t ht ↦
    fdBoundary_H_differentiableAt_off_partition H _ (fun habs ↦ ht (by
      simp only [fdBoundaryFullPartition, fdBoundary_H_partition, Finset.mem_insert,
        Finset.mem_singleton] at habs ⊢
      tauto))
  have hγ_deriv_cont := (fdBoundary_HCurve H).deriv_continuous_off_partition
  have hγ_deriv_bdd := piecewiseC1Immersion_deriv_bounded (fdBoundary_HImmersion H hH_sqrt3)
  have go : ∀ {ω : ℂ}, ω ≠ 0 → (∀ t ∈ Icc (0:ℝ) 5, ω * (fdBoundary_H H t - z₀) ∈ Complex.slitPlane) →
      ∫ t in (0:ℝ)..5, (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t = 0 := fun hω hslit ↦
    ftc_integral_zero_of_closed_slit hω (fdBoundary_H_continuous H) (fdBoundary_H_closed H)
      h_off hslit hγ_diff hγ_deriv_cont hγ_deriv_bdd
  by_cases h_re_half : |z₀.re| ≤ 1/2
  · have h_norm_lt : ‖z₀‖ < 1 := hz₀_not_fd h_re_half
    refine go (ω := -I) (by simp [Complex.ext_iff, I_re, I_im]) (fun t ht ↦ ?_)
    rw [Complex.mem_slitPlane_iff]
    by_contra h_not_slit
    push Not at h_not_slit
    have h_re_neg_I : ((-I) * (fdBoundary_H H t - z₀)).re = (fdBoundary_H H t).im - z₀.im := by
      simp [mul_re, neg_re, I_re, I_im, sub_re, sub_im]
    have h_im_neg_I : ((-I) * (fdBoundary_H H t - z₀)).im = -((fdBoundary_H H t).re - z₀.re) := by
      simp [mul_im, neg_im, I_re, I_im, sub_re, sub_im]
    have h1 : (fdBoundary_H H t).im ≤ z₀.im := by linarith [h_re_neg_I ▸ h_not_slit.1]
    have h2 : (fdBoundary_H H t).re = z₀.re := by
      have := h_not_slit.2; rw [h_im_neg_I] at this; linarith
    have h_sq_norm_z₀ := Complex.sq_norm z₀
    rw [Complex.normSq_apply] at h_sq_norm_z₀
    have h_sq_norm_curve := Complex.sq_norm (fdBoundary_H H t)
    rw [Complex.normSq_apply, h2] at h_sq_norm_curve
    have h_curve_sq_ge : ‖fdBoundary_H H t‖ ^ 2 ≥ 1 := by
      nlinarith [norm_nonneg (fdBoundary_H H t), fdBoundary_H_norm_ge_one hH t ht]
    have h_im_pos : 0 < (fdBoundary_H H t).im := fdBoundary_H_im_pos H hH_sqrt3 t ht
    nlinarith [mul_nonneg (show z₀.im - (fdBoundary_H H t).im ≥ 0 from by linarith)
      (show z₀.im + (fdBoundary_H H t).im ≥ 0 from by linarith),
      (show ‖z₀‖ ^ 2 < 1 from by nlinarith [norm_nonneg z₀])]
  · push Not at h_re_half
    by_cases h_re_pos : z₀.re > 1/2
    · refine go (ω := -1) (by norm_num) (fun t ht ↦ ?_)
      rw [Complex.mem_slitPlane_iff]
      left
      simp only [neg_one_mul, neg_re, sub_re]
      linarith [abs_le.mp (fdBoundary_H_re_abs_le_half H t ht)]
    · have h_re_neg : z₀.re < -1/2 := by
        cases abs_cases z₀.re with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1, h_re_pos]
      refine go (ω := 1) one_ne_zero (fun t ht ↦ ?_)
      rw [Complex.mem_slitPlane_iff]
      left
      simp only [one_mul, sub_re]
      linarith [abs_le.mp (fdBoundary_H_re_abs_le_half H t ht)]

end
