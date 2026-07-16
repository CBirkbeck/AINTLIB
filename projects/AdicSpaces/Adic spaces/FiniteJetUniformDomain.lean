/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetRings
import «Adic spaces».Uniform

/-!
# 𝓐 is a uniform domain and is not noetherian ([FJP] Propositions 2.3, 2.4, and (5.2))

* **Prop 2.3**: the Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative; `𝓐° = 𝓐₀` is the unit ball;
  hence `𝓐` is a complete uniform Tate ring and an integral domain.
* **(5.2)**: the maximal plus rings of 𝓑 and 𝓓 are `k°⟨W⟩ ⊕ Qk⟨W⟩` resp. `L° ⊕ QL` —
  power-boundedness depends only on the constant-jet component (`(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`).
* **Prop 2.4**: `𝓐` is not noetherian: the ideal `J = Q²𝒞 = ker(jB)` is not finitely
  generated, since `J/KJ ≅ L` over `𝓐/K ≅ k⟨W⟩` and `W⁻¹` is not integral over `k⟨W⟩`.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent TopologicalRing

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### Norm multiplicativity and the domain property ([FJP] Prop 2.3) -/

/-- The Gauss norm on `L = K⟨W,W⁻¹⟩` is multiplicative (specialisation of
`RestrictedLaurent.norm_mul_eq` to the discretely valued `K`). -/
theorem norm_L_mul (f g : L F) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  RestrictedLaurent.norm_mul_eq (norm_K_discrete F) f g

theorem norm_L_eq_zero {f : L F} (hf : ‖f‖ = 0) : f = 0 :=
  norm_eq_zero.mp hf

/-- Coefficient decay of an element of `𝒞`, super-level-set form. -/
theorem finite_setOf_le_norm_qCoeff (f : JetC F) {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | ε ≤ ‖qCoeff F n f‖}.Finite := by
  have h := (Restricted.isRestricted_iff_cofinite (R := L F) 1).mp f.2
  simp only [one_pow, mul_one] at h
  have hev := h.eventually (eventually_lt_nhds hε (a := (0 : ℝ)))
  rw [Filter.eventually_cofinite] at hev
  exact hev.subset fun n hn => by simpa using not_lt.mpr hn

/-- The Gauss norm of a nonzero element of `𝒞` is attained. -/
theorem exists_norm_qCoeff_eq (f : JetC F) (hf : f ≠ 0) :
    ∃ n : ℕ, ‖f‖ = ‖qCoeff F n f‖ ∧ qCoeff F n f ≠ 0 := by
  have hne : ∃ n, qCoeff F n f ≠ 0 := by
    by_contra h
    push Not at h
    refine hf (Subtype.ext (PowerSeries.ext fun n => ?_))
    rw [show (0 : JetC F).1 = (0 : PowerSeries (L F)) from rfl, map_zero]
    exact h n
  obtain ⟨n₀, hn₀⟩ := hne
  have hpos : 0 < ‖qCoeff F n₀ f‖ := norm_pos_iff.mpr hn₀
  obtain ⟨n, hnS, hnmax⟩ := Set.exists_max_image _ (fun n => ‖qCoeff F n f‖)
    (finite_setOf_le_norm_qCoeff F f hpos)
    ⟨n₀, show ‖qCoeff F n₀ f‖ ≤ ‖qCoeff F n₀ f‖ from le_rfl⟩
  refine ⟨n, le_antisymm ?_ (norm_qCoeff_le F f n), ?_⟩
  · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun m => ?_) (norm_nonneg _)
    rw [one_pow, mul_one]
    by_cases hm : ‖qCoeff F n₀ f‖ ≤ ‖qCoeff F m f‖
    · exact hnmax m hm
    · exact ((not_le.mp hm).le.trans hnS)
  · exact norm_pos_iff.mp (lt_of_lt_of_le hpos hnS)

/-- The Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm
on 𝒞 = L⟨Q⟩ is multiplicative"). Proved by the minimal-achiever argument through the
vendored `PowerSeries.gaussNorm_mul_eq_mul`, with base-norm multiplicativity from
`norm_L_mul`. -/
theorem norm_JetC_mul (f g : JetC F) : ‖f * g‖ = ‖f‖ * ‖g‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  -- minimal-degree achievers
  obtain ⟨nf, hnf_eq, hnf_ne⟩ := exists_norm_qCoeff_eq F f hf
  obtain ⟨ng, hng_eq, hng_ne⟩ := exists_norm_qCoeff_eq F g hg
  have hposf : 0 < ‖f‖ := hnf_eq ▸ norm_pos_iff.mpr hnf_ne
  have hposg : 0 < ‖g‖ := hng_eq ▸ norm_pos_iff.mpr hng_ne
  have hAf : {n : ℕ | ‖qCoeff F n f‖ = ‖f‖}.Finite :=
    (finite_setOf_le_norm_qCoeff F f hposf).subset fun n hn => by
      rw [Set.mem_setOf_eq] at hn ⊢; rw [hn]
  have hAg : {n : ℕ | ‖qCoeff F n g‖ = ‖g‖}.Finite :=
    (finite_setOf_le_norm_qCoeff F g hposg).subset fun n hn => by
      rw [Set.mem_setOf_eq] at hn ⊢; rw [hn]
  obtain ⟨i, hiA, himin⟩ := Set.exists_min_image _ (fun n : ℕ => n) hAf ⟨nf, hnf_eq.symm⟩
  obtain ⟨j, hjA, hjmin⟩ := Set.exists_min_image _ (fun n : ℕ => n) hAg ⟨ng, hng_eq.symm⟩
  rw [Set.mem_setOf_eq] at hiA hjA
  rw [Restricted.norm_eq (R := L F) 1 (f * g), Restricted.norm_eq (R := L F) 1 f,
    Restricted.norm_eq (R := L F) 1 g,
    show (f * g : JetC F).1 = f.1 * g.1 from rfl]
  refine PowerSeries.gaussNorm_mul_eq_mul (v := (norm : L F → ℝ)) (c := 1) f.1 g.1
    (Restricted.hasGaussNorm 1 f) (Restricted.hasGaussNorm 1 g)
    (Restricted.hasGaussNorm 1 (f * g)) norm_nonneg norm_zero
    (fun a b => IsUltrametricDist.norm_add_le_max a b) (norm_L_mul F)
    norm_neg (fun x hx => norm_L_eq_zero F hx) one_pos ⟨i, j, ?_, ?_, ?_⟩
  · rw [PowerSeries.achievesGaussNorm_iff]
    show ‖qCoeff F i f‖ * (1 : ℝ) ^ i = _
    rw [one_pow, mul_one, hiA, Restricted.norm_eq]
  · rw [PowerSeries.achievesGaussNorm_iff]
    show ‖qCoeff F j g‖ * (1 : ℝ) ^ j = _
    rw [one_pow, mul_one, hjA, Restricted.norm_eq]
  · intro p hp hpne
    rw [Finset.mem_antidiagonal] at hp
    show ‖qCoeff F p.1 f * qCoeff F p.2 g‖ < ‖qCoeff F i f‖ * ‖qCoeff F j g‖
    rw [norm_L_mul, hiA, hjA]
    rcases lt_or_gt_of_ne (show p.1 ≠ i from fun h => hpne (by
      refine Prod.ext h ?_
      omega)) with hlt | hgt
    · -- `p.1 < i`: the `f`-side is strictly submaximal
      have hf1 : ‖qCoeff F p.1 f‖ < ‖f‖ := by
        rcases lt_or_eq_of_le (norm_qCoeff_le F f p.1) with h | h
        · exact h
        · have := himin p.1 h
          omega
      calc ‖qCoeff F p.1 f‖ * ‖qCoeff F p.2 g‖
          ≤ ‖qCoeff F p.1 f‖ * ‖g‖ :=
            mul_le_mul_of_nonneg_left (norm_qCoeff_le F g p.2) (norm_nonneg _)
        _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_right hf1 hposg
    · -- `p.1 > i`, hence `p.2 < j`: the `g`-side is strictly submaximal
      have hg1 : ‖qCoeff F p.2 g‖ < ‖g‖ := by
        rcases lt_or_eq_of_le (norm_qCoeff_le F g p.2) with h | h
        · exact h
        · have := hjmin p.2 h
          omega
      calc ‖qCoeff F p.1 f‖ * ‖qCoeff F p.2 g‖
          ≤ ‖f‖ * ‖qCoeff F p.2 g‖ :=
            mul_le_mul_of_nonneg_right (norm_qCoeff_le F f p.1) (norm_nonneg _)
        _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_left hg1 hposf

instance : Nontrivial (JetC F) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (norm : JetC F → ℝ) h
  rw [norm_zero, norm_one] at this
  exact zero_ne_one this

instance : NoZeroDivisors (JetC F) := by
  refine ⟨fun {f g} hfg => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hf, hg⟩ := hcon
  have h := norm_JetC_mul F f g
  rw [hfg, norm_zero] at h
  have hposf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hposg : 0 < ‖g‖ := norm_pos_iff.mpr hg
  nlinarith

/-- `𝒞` is an integral domain ([FJP] Prop 2.3: "also that 𝒞 is a domain"). -/
instance : IsDomain (JetC F) := NoZeroDivisors.to_isDomain _

instance : Nontrivial (JetA F) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (norm : JetA F → ℝ) h
  rw [norm_zero, norm_one] at this
  exact zero_ne_one this

instance : NoZeroDivisors (JetA F) := by
  refine ⟨fun {a b} hab => ?_⟩
  have h : (a : JetC F) * (b : JetC F) = 0 := by
    rw [show (a : JetC F) * (b : JetC F) = ((a * b : JetA F) : JetC F) from rfl, hab]
    rfl
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

/-- `𝓐` is an integral domain ([FJP] Prop 2.3: "𝒜 is a domain because it is a subring
of 𝒞"). -/
instance : IsDomain (JetA F) := NoZeroDivisors.to_isDomain _

/-! ### The power-bounded subring of 𝓐 is the unit ball ([FJP] Prop 2.3) -/

/-- Power-boundedness in 𝓐 is having norm at most one ([FJP] Prop 2.3: "If `v(a) < 0` …
`a` is not power-bounded. If `v(a) ≥ 0`, all powers of `a` lie in 𝒜₀. Thus the valuation
formulation gives directly `𝒜° = 𝒜₀`"). -/
theorem isPowerBounded_JetA_iff (a : JetA F) :
    TopologicalRing.IsPowerBounded a ↔ ‖a‖ ≤ 1 := by sorry

/-- The power-bounded subring of 𝓐 is bounded — **𝓐 is uniform**
([FJP] Prop 2.3: "The ring 𝒜 is a complete uniform Tate k-algebra"). -/
theorem isUniform_JetA : TopologicalRing.IsUniform (JetA F) := by sorry

/-! ### The plus rings of the jet vertices ([FJP] (5.2)) -/

/-- Power-boundedness in `𝓑` depends only on the constant-jet component
([FJP] (5.2): `ℬ° = k°⟨W⟩ ⊕ Qk⟨W⟩`, via `(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`). -/
theorem isPowerBounded_JetB_iff (x : JetB F) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 := by sorry

/-- Power-boundedness in `𝓓` depends only on the constant-jet component
([FJP] (5.2): `𝒟° = L° + QL`). -/
theorem isPowerBounded_JetD_iff (x : JetD F) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 := by sorry

/-- `𝓑` is **not** uniform: the square-zero line `K·ε` is power-bounded and unbounded
([FJP] (2.1d): "the summand `kQ` is an unbounded line"). -/
theorem not_isUniform_JetB : ¬ TopologicalRing.IsUniform (JetB F) := by sorry

/-! ### 𝓐 is not noetherian ([FJP] Prop 2.4) -/

/-- The scalars `K⟨W⟩` act on `L` through the norm-preserving embedding. -/
noncomputable instance : Algebra (PowerSeries.Restricted K (1 : ℝ)) (L F) :=
  (ofRestricted (R := K)).toAlgebra

/-- `W⁻¹ ∈ L` is not integral over `K⟨W⟩` ([FJP] Prop 2.4: multiplying a monic equation
`(W⁻¹)ⁿ + a_{n-1}(W)(W⁻¹)^{n-1} + ⋯ + a₀(W) = 0` by `Wⁿ` and evaluating at `W = 0`
gives `1 = 0`). -/
theorem winv_not_integral :
    ¬ IsIntegral (PowerSeries.Restricted K (1 : ℝ)) ((Wu (R := K))⁻¹ : (L F)ˣ).val := by
  sorry

/-- `L` is not module-finite over `K⟨W⟩` ([FJP] Prop 2.4: "It would follow that `L` is a
finite `R_W`-module. A module-finite algebra is integral, so `W⁻¹` would satisfy a monic
equation"). -/
theorem not_moduleFinite_L : ¬ Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L F) := by
  sorry

/-- If the ideal `J = ker(jB) = Q²𝒞` of 𝓐 were finitely generated, `L` would be
module-finite over `K⟨W⟩` ([FJP] Prop 2.4: `KJ = Q³𝒞`, `J/KJ ≅ 𝒞/Q𝒞 = L` as
`𝒜/K ≅ R_W`-modules, and generators of `J` generate `J/KJ`). -/
theorem moduleFinite_of_ker_jB_fg (h : (RingHom.ker (jB F)).FG) :
    Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L F) := by sorry

/-- The ideal `Q²𝒞 ⊂ 𝓐` is not finitely generated ([FJP] Prop 2.4). -/
theorem ker_jB_not_fg : ¬ (RingHom.ker (jB F)).FG := by sorry

/-- **𝓐 is not noetherian** ([FJP] Prop 2.4: "The underlying ring 𝒜 is not noetherian"). -/
theorem not_isNoetherianRing_JetA : ¬ IsNoetherianRing (JetA F) := by sorry

end FiniteJet
