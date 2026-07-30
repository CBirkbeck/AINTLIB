/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.Presentation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Injectivity of the restriction maps (Kedlaya Corollary 4.6)

For a closed subinterval `I' ⊆ I` the restriction homomorphism
`resIHom : B^I → B^{I'}` is injective. Kedlaya's proof has two steps, both here:

* **three circles with the weight on the vanishing point**
  (`valued_resI_rpow_interpolate` + `resI_eq_zero_of_interior`): if the value of
  `z ∈ B^I` vanishes at one interior radius, it vanishes at every interior radius —
  interpolate the vanishing radius against either endpoint parameter;
* **endpoint continuity** (`wLoc_le_of_interior_bound`): the value at an endpoint
  radius is controlled by the values at interior radii, per Teichmüller term of an
  approximating `Bloc`-element; combined with the density of `Bloc` in `B^I` this
  transfers the interior vanishing to the two endpoint coordinates
  (`resIHom_injective`).

Intervals are parametrized as in `IntervalRing.lean`: the intermediate radius with
parameter `θ ∈ [0,1]` is `ρ₁^θ·ρ₂^(1-θ)` (so `θ = 0` is the right endpoint `ρ₂` and
`θ = 1` the left endpoint `ρ₁`).

## Main results

* `FarguesFontaine.valued_resI_rpow_interpolate` : three circles for `resI`-values.
* `FarguesFontaine.wLoc_le_of_interior_bound` : endpoint values from interior bounds.
* `FarguesFontaine.resI_eq_zero_of_interior` : vanishing propagates to all interior
  radii.
* `FarguesFontaine.resIHom_injective` : **Kedlaya Corollary 4.6**.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Corollary 4.6.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

universe u

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- Interpolating two interpolated radii is interpolation at the combined weight. -/
theorem rpow_mid_interpolate (hρ₁0 : 0 < ρ₁) (hρ₂0 : 0 < ρ₂) (θ' θ'' c : ℝ) :
    (ρ₁ ^ θ' * ρ₂ ^ (1 - θ')) ^ c * (ρ₁ ^ θ'' * ρ₂ ^ (1 - θ'')) ^ (1 - c)
      = ρ₁ ^ (c * θ' + (1 - c) * θ'') * ρ₂ ^ (1 - (c * θ' + (1 - c) * θ'')) := by
  rw [NNReal.mul_rpow, NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul,
    ← NNReal.rpow_mul, ← NNReal.rpow_mul, mul_mul_mul_comm,
    ← NNReal.rpow_add (ne_of_gt hρ₁0), ← NNReal.rpow_add (ne_of_gt hρ₂0),
    show θ' * c + θ'' * (1 - c) = c * θ' + (1 - c) * θ'' from by ring,
    show (1 - θ') * c + (1 - θ'') * (1 - c)
      = 1 - (c * θ' + (1 - c) * θ'') from by ring]

/-- **Three circles for the intermediate values of `B^I`** (Kedlaya Cor 4.5 upgraded
to the completed setting): the `resI`-value at the combined weight is bounded by the
interpolated product of the two `resI`-values. -/
theorem valued_resI_rpow_interpolate {θ' θ'' c : ℝ}
    (hθ'0 : 0 ≤ θ') (hθ'1 : θ' ≤ 1) (hθ''0 : 0 ≤ θ'') (hθ''1 : θ'' ≤ 1)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hm'0 : 0 < ρ₁ ^ θ' * ρ₂ ^ (1 - θ')) (hm'1 : ρ₁ ^ θ' * ρ₂ ^ (1 - θ') < 1)
    (hm''0 : 0 < ρ₁ ^ θ'' * ρ₂ ^ (1 - θ'')) (hm''1 : ρ₁ ^ θ'' * ρ₂ ^ (1 - θ'') < 1)
    (hmc0 : 0 < ρ₁ ^ (c * θ' + (1 - c) * θ'')
      * ρ₂ ^ (1 - (c * θ' + (1 - c) * θ'')))
    (hmc1 : ρ₁ ^ (c * θ' + (1 - c) * θ'')
      * ρ₂ ^ (1 - (c * θ' + (1 - c) * θ'')) < 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :
    Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmc0 hmc1 z)
      ≤ Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z) ^ c
        * Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z) ^ (1 - c) := by
  haveI hne := neBot_comap_of_mem_BISub p F ϖ hz
  have hθc0 : (0 : ℝ) ≤ c * θ' + (1 - c) * θ'' := by nlinarith
  have hθc1 : c * θ' + (1 - c) * θ'' ≤ 1 := by nlinarith
  have hlim' := tendsto_resI p F ϖ hθ'0 hθ'1 hm'0 hm'1 hz
  have hlim'' := tendsto_resI p F ϖ hθ''0 hθ''1 hm''0 hm''1 hz
  have hlimc := tendsto_resI p F ϖ hθc0 hθc1 hmc0 hmc1 hz
  set v' := Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z) with hv'def
  set v'' := Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z) with hv''def
  -- the pointwise three-circles inequality on the dense layer
  have hpt : ∀ x : Bloc p F ϖ,
      Valued.v (BlocToHatK p F ϖ hmc0 hmc1 x)
        ≤ Valued.v (BlocToHatK p F ϖ hm'0 hm'1 x) ^ c
          * Valued.v (BlocToHatK p F ϖ hm''0 hm''1 x) ^ (1 - c) := by
    intro x
    have key : ∀ (A : NNReal) (hA0 : 0 < A) (hA1 : A < 1),
        A = (ρ₁ ^ θ' * ρ₂ ^ (1 - θ')) ^ c * (ρ₁ ^ θ'' * ρ₂ ^ (1 - θ'')) ^ (1 - c) →
        wLoc p F ϖ hA0 hA1 x
          ≤ (wLoc p F ϖ hm'0 hm'1 x) ^ c * (wLoc p F ϖ hm''0 hm''1 x) ^ (1 - c) := by
      rintro A hA0 hA1 rfl
      exact wLoc_rpow_interpolate p F ϖ (hρ₁0 := hm'0) (hρ₁1 := hm'1)
        (hρ₂0 := hm''0) (hρ₂1 := hm''1) hc0.le hc1.le hA0 hA1 x
    have h0 := key _ hmc0 hmc1
      (rpow_mid_interpolate hρ₁0 hρ₂0 θ' θ'' c).symm
    rw [valued_BlocToHatK, valued_BlocToHatK, valued_BlocToHatK]
    exact h0
  -- the padded bound, one ε at a time
  have hpad : ∀ ε : NNReal, 0 < ε →
      Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmc0 hmc1 z)
        ≤ (max v' ε) ^ c * (max v'' ε) ^ (1 - c) := by
    intro ε hε
    have hC0 : 0 < (max v' ε) ^ c * (max v'' ε) ^ (1 - c) :=
      mul_pos (NNReal.rpow_pos (lt_of_lt_of_le hε (le_max_right _ _)))
        (NNReal.rpow_pos (lt_of_lt_of_le hε (le_max_right _ _)))
    refine (isClosed_valued_ball p F hC0).mem_of_tendsto hlimc ?_
    have hev' := hlim' (valued_ball_mem_nhds p F
      (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z) hε)
    have hev'' := hlim'' (valued_ball_mem_nhds p F
      (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z) hε)
    filter_upwards [hev', hev''] with x hx' hx''
    have hb' : Valued.v (BlocToHatK p F ϖ hm'0 hm'1 x) ≤ max v' ε := by
      have hd : Valued.v (BlocToHatK p F ϖ hm'0 hm'1 x
          - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z) ≤ ε := hx'
      have hsplit : BlocToHatK p F ϖ hm'0 hm'1 x
          = resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z
            + (BlocToHatK p F ϖ hm'0 hm'1 x
              - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z) := by ring
      calc Valued.v (BlocToHatK p F ϖ hm'0 hm'1 x)
          = Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z
            + (BlocToHatK p F ϖ hm'0 hm'1 x
              - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z)) := by rw [← hsplit]
        _ ≤ max v' (Valued.v (BlocToHatK p F ϖ hm'0 hm'1 x
              - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm'0 hm'1 z)) :=
            Valuation.map_add _ _ _
        _ ≤ max v' ε := max_le_max le_rfl hd
    have hb'' : Valued.v (BlocToHatK p F ϖ hm''0 hm''1 x) ≤ max v'' ε := by
      have hd : Valued.v (BlocToHatK p F ϖ hm''0 hm''1 x
          - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z) ≤ ε := hx''
      have hsplit : BlocToHatK p F ϖ hm''0 hm''1 x
          = resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z
            + (BlocToHatK p F ϖ hm''0 hm''1 x
              - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z) := by ring
      calc Valued.v (BlocToHatK p F ϖ hm''0 hm''1 x)
          = Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z
            + (BlocToHatK p F ϖ hm''0 hm''1 x
              - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z)) := by rw [← hsplit]
        _ ≤ max v'' (Valued.v (BlocToHatK p F ϖ hm''0 hm''1 x
              - resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm''0 hm''1 z)) :=
            Valuation.map_add _ _ _
        _ ≤ max v'' ε := max_le_max le_rfl hd
    calc Valued.v (BlocToHatK p F ϖ hmc0 hmc1 x)
        ≤ Valued.v (BlocToHatK p F ϖ hm'0 hm'1 x) ^ c
          * Valued.v (BlocToHatK p F ϖ hm''0 hm''1 x) ^ (1 - c) := hpt x
      _ ≤ (max v' ε) ^ c * (max v'' ε) ^ (1 - c) :=
          mul_le_mul (NNReal.rpow_le_rpow hb' hc0.le)
            (NNReal.rpow_le_rpow hb'' (by linarith)) zero_le zero_le
  -- let ε → 0 along the geometric sequence
  have hseq : Filter.Tendsto
      (fun m : ℕ => (max v' ((2⁻¹ : NNReal) ^ m)) ^ c
        * (max v'' ((2⁻¹ : NNReal) ^ m)) ^ (1 - c))
      Filter.atTop (nhds (v' ^ c * v'' ^ (1 - c))) := by
    have h2 : Filter.Tendsto (fun m : ℕ => ((2 : NNReal)⁻¹) ^ m)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hmax' : Filter.Tendsto (fun m : ℕ => max v' (((2 : NNReal)⁻¹) ^ m))
        Filter.atTop (nhds v') := by
      have h := (tendsto_const_nhds (x := v')
        (f := Filter.atTop (α := ℕ))).max h2
      rwa [max_eq_left zero_le] at h
    have hmax'' : Filter.Tendsto (fun m : ℕ => max v'' (((2 : NNReal)⁻¹) ^ m))
        Filter.atTop (nhds v'') := by
      have h := (tendsto_const_nhds (x := v'')
        (f := Filter.atTop (α := ℕ))).max h2
      rwa [max_eq_left zero_le] at h
    exact (hmax'.nnrpow tendsto_const_nhds (Or.inr hc0)).mul
      (hmax''.nnrpow tendsto_const_nhds (Or.inr (by linarith)))
  exact ge_of_tendsto hseq (Filter.Eventually.of_forall fun m =>
    hpad _ (pow_pos (by norm_num) m))

/-- **Endpoint values from interior bounds** (the continuity input to Kedlaya
Cor 4.6): if the Gauss value of `x ∈ Bloc` is at most `ε` at every interior radius,
it is at most `ε` at any radius reachable as a limit of interior radii. The proof is
per Teichmüller term: each `σⁿ·|aₙ|` is continuous in `σ`. -/
theorem wLoc_le_of_interior_bound (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (θseq : ℕ → ℝ) (hθs0 : ∀ m, 0 < θseq m) (hθs1 : ∀ m, θseq m < 1)
    (hτ : Filter.Tendsto (fun m => ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m))
      Filter.atTop (nhds σ))
    (x : Bloc p F ϖ) {ε : NNReal}
    (h : ∀ (θ : ℝ), 0 < θ → θ < 1 →
      ∀ (hm0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hm1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1),
      wLoc p F ϖ hm0 hm1 x ≤ ε) :
    wLoc p F ϖ hσ0 hσ1 x ≤ ε := by
  obtain ⟨⟨a, y⟩, hxy⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) x
  change x * algebraMap (Ainf p F) (Bloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Bloc p F ϖ) a at hxy
  obtain ⟨k, hk⟩ := y.2
  set cϖ : NNReal := perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hcϖ
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
  have hcϖ0 : 0 < cϖ := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  have hval : ∀ (τ : NNReal) (hτ0 : 0 < τ) (hτ1 : τ < 1),
      wLoc p F ϖ hτ0 hτ1 x * (τ * cϖ) ^ k = gaussValue p F τ a := by
    intro τ hτ0 hτ1
    have h1 : x * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k)
        = algebraMap (Ainf p F) (Bloc p F ϖ) a := by
      rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) from hk]
      exact hxy
    have h2 := congrArg (wLoc p F ϖ hτ0 hτ1) h1
    rwa [Valuation.map_mul, map_pow, Valuation.map_pow, wLoc_algebraMap,
      wLoc_algebraMap, gaussValue_p_teichPi p F ϖ hτ1] at h2
  -- per-term limit bound at the target radius
  have hterm2 : ∀ n : ℕ,
      σ ^ n * perfectoidValuation p F ((teichCoeff p F a n : OF F) : F) ≤ ε * (σ * cϖ) ^ k := by
    intro n
    have hL : Filter.Tendsto
        (fun m => (ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m)) ^ n
          * perfectoidValuation p F ((teichCoeff p F a n : OF F) : F))
        Filter.atTop
        (nhds (σ ^ n * perfectoidValuation p F ((teichCoeff p F a n : OF F) : F))) :=
      (hτ.pow n).mul_const _
    have hR : Filter.Tendsto (fun m => ε * ((ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m)) * cϖ) ^ k)
        Filter.atTop (nhds (ε * (σ * cϖ) ^ k)) := (((hτ.mul_const cϖ).pow k).const_mul ε)
    refine le_of_tendsto_of_tendsto' hL hR fun m => ?_
    obtain ⟨hm0, hm1⟩ := rpow_interpolate_lt_one hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hθs0 m).le (hθs1 m).le
    have hle1 : (ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m)) ^ n
        * perfectoidValuation p F ((teichCoeff p F a n : OF F) : F)
        ≤ gaussValue p F (ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m)) a := by
      have h0 := gaussTerm_le_gaussValue p F hm1.le a n
      rwa [gaussTerm] at h0
    have hle2 : gaussValue p F (ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m)) a
        ≤ ε * ((ρ₁ ^ (θseq m) * ρ₂ ^ (1 - θseq m)) * cϖ) ^ k := by
      rw [← hval _ hm0 hm1]
      exact mul_le_mul_of_nonneg_right (h (θseq m) (hθs0 m) (hθs1 m) hm0 hm1) zero_le
    exact le_trans hle1 hle2
  have hsup : gaussValue p F σ a ≤ ε * (σ * cϖ) ^ k := by
    rw [gaussValue]
    exact ciSup_le fun n => by
      have := hterm2 n
      rwa [gaussTerm]
  have hfinal := hval σ hσ0 hσ1
  rw [← hfinal] at hsup
  exact le_of_mul_le_mul_right hsup (pow_pos (mul_pos hσ0 hcϖ0) k)

/-- The interior radii converge to the right endpoint (`θ → 0`). -/
theorem tendsto_interior_radius_right (hρ₁0 : 0 < ρ₁) (hρ₂0 : 0 < ρ₂) :
    Filter.Tendsto
      (fun m : ℕ => ρ₁ ^ ((1 : ℝ) / (m + 2)) * ρ₂ ^ (1 - (1 : ℝ) / (m + 2)))
      Filter.atTop (nhds ρ₂) := by
  have hθ : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m + 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 2))
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact h1.inv_tendsto_atTop.congr fun m => (one_div _).symm
  have h1 : Filter.Tendsto (fun m : ℕ => ρ₁ ^ ((1 : ℝ) / (m + 2)))
      Filter.atTop (nhds 1) := by
    have h := Filter.Tendsto.nnrpow (tendsto_const_nhds (x := ρ₁)) hθ
      (Or.inl (ne_of_gt hρ₁0))
    rwa [NNReal.rpow_zero] at h
  have h2 : Filter.Tendsto (fun m : ℕ => ρ₂ ^ (1 - (1 : ℝ) / (m + 2)))
      Filter.atTop (nhds ρ₂) := by
    have hexp : Filter.Tendsto (fun m : ℕ => 1 - (1 : ℝ) / (m + 2))
        Filter.atTop (nhds 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))
        (f := Filter.atTop (α := ℕ))).sub hθ
      rwa [sub_zero] at h
    have h := Filter.Tendsto.nnrpow (tendsto_const_nhds (x := ρ₂)) hexp
      (Or.inl (ne_of_gt hρ₂0))
    rwa [NNReal.rpow_one] at h
  have h := h1.mul h2
  rwa [one_mul] at h

/-- The interior radii converge to the left endpoint (`θ → 1`). -/
theorem tendsto_interior_radius_left (hρ₁0 : 0 < ρ₁) (hρ₂0 : 0 < ρ₂) :
    Filter.Tendsto
      (fun m : ℕ => ρ₁ ^ (1 - (1 : ℝ) / (m + 2)) * ρ₂ ^ (1 - (1 - (1 : ℝ) / (m + 2))))
      Filter.atTop (nhds ρ₁) := by
  have hθ : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m + 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 2))
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact h1.inv_tendsto_atTop.congr fun m => (one_div _).symm
  have hexp : Filter.Tendsto (fun m : ℕ => 1 - (1 : ℝ) / (m + 2))
      Filter.atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))
      (f := Filter.atTop (α := ℕ))).sub hθ
    rwa [sub_zero] at h
  have h1 : Filter.Tendsto (fun m : ℕ => ρ₁ ^ (1 - (1 : ℝ) / (m + 2)))
      Filter.atTop (nhds ρ₁) := by
    have h := Filter.Tendsto.nnrpow (tendsto_const_nhds (x := ρ₁)) hexp
      (Or.inl (ne_of_gt hρ₁0))
    rwa [NNReal.rpow_one] at h
  have h2 : Filter.Tendsto (fun m : ℕ => ρ₂ ^ (1 - (1 - (1 : ℝ) / (m + 2))))
      Filter.atTop (nhds 1) := by
    have hexp2 : Filter.Tendsto (fun m : ℕ => 1 - (1 - (1 : ℝ) / (m + 2)))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))
        (f := Filter.atTop (α := ℕ))).sub hexp
      rwa [sub_self] at h
    have h := Filter.Tendsto.nnrpow (tendsto_const_nhds (x := ρ₂)) hexp2
      (Or.inl (ne_of_gt hρ₂0))
    rwa [NNReal.rpow_zero] at h
  have h := h1.mul h2
  rwa [mul_one] at h

/-- **Vanishing at one interior radius propagates to every interior radius**
(Kedlaya Cor 4.6, the three-circles step with the weight on the vanishing point). -/
theorem resI_eq_zero_of_interior {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    {z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (h0 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1 z = 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hm0 : 0 < ρ₁ ^ α * ρ₂ ^ (1 - α)) (hm1 : ρ₁ ^ α * ρ₂ ^ (1 - α) < 1) :
    resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm0 hm1 z = 0 := by
  have transport : ∀ (β γ : ℝ), β = γ →
      ∀ (hb0 : 0 < ρ₁ ^ β * ρ₂ ^ (1 - β)) (hb1 : ρ₁ ^ β * ρ₂ ^ (1 - β) < 1)
        (hg0 : 0 < ρ₁ ^ γ * ρ₂ ^ (1 - γ)) (hg1 : ρ₁ ^ γ * ρ₂ ^ (1 - γ) < 1),
      resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hb0 hb1 z = 0 →
      resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hg0 hg1 z = 0 := by
    rintro β γ rfl hb0 hb1 hg0 hg1 h
    exact h
  rcases lt_trichotomy α θ with hlt | heq | hgt
  · -- interpolate the vanishing point `θ` with the parameter `0` (radius `ρ₂`-side)
    set c : ℝ := α / θ with hcdef
    have hc0 : 0 < c := div_pos hα0 hθ0
    have hc1 : c < 1 := (div_lt_one hθ0).mpr hlt
    obtain ⟨h00, h01⟩ := rpow_interpolate_lt_one hρ₁0 hρ₁1 hρ₂0 hρ₂1
      le_rfl zero_le_one
    have hcomb : c * θ + (1 - c) * 0 = α := by
      rw [mul_zero, add_zero, hcdef, div_mul_cancel₀ _ (ne_of_gt hθ0)]
    obtain ⟨hmc0, hmc1⟩ := rpow_interpolate_lt_one hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (by nlinarith : (0:ℝ) ≤ c * θ + (1 - c) * 0)
      (by nlinarith : c * θ + (1 - c) * 0 ≤ 1)
    have hint := valued_resI_rpow_interpolate p F ϖ hθ0.le hθ1.le le_rfl
      zero_le_one hc0 hc1 hσ₁0 hσ₁1 h00 h01 hmc0 hmc1 hz
    rw [h0, Valuation.map_zero, NNReal.zero_rpow (ne_of_gt hc0), zero_mul] at hint
    have hval0 : Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmc0 hmc1 z) = 0 :=
      le_antisymm hint zero_le
    exact transport _ _ hcomb hmc0 hmc1 hm0 hm1 ((Valuation.zero_iff _).mp hval0)
  · exact transport _ _ heq.symm hσ₁0 hσ₁1 hm0 hm1 h0
  · -- interpolate the vanishing point `θ` with the parameter `1` (radius `ρ₁`-side)
    set c : ℝ := (1 - α) / (1 - θ) with hcdef
    have h1θ : (0:ℝ) < 1 - θ := by linarith
    have hc0 : 0 < c := div_pos (by linarith) h1θ
    have hc1 : c < 1 := (div_lt_one h1θ).mpr (by linarith)
    obtain ⟨h10, h11⟩ := rpow_interpolate_lt_one hρ₁0 hρ₁1 hρ₂0 hρ₂1
      zero_le_one le_rfl
    have hcomb : c * θ + (1 - c) * 1 = α := by
      rw [hcdef]
      field_simp
      ring
    obtain ⟨hmc0, hmc1⟩ := rpow_interpolate_lt_one hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (by nlinarith : (0:ℝ) ≤ c * θ + (1 - c) * 1)
      (by nlinarith : c * θ + (1 - c) * 1 ≤ 1)
    have hint := valued_resI_rpow_interpolate p F ϖ hθ0.le hθ1.le zero_le_one
      le_rfl hc0 hc1 hσ₁0 hσ₁1 h10 h11 hmc0 hmc1 hz
    rw [h0, Valuation.map_zero, NNReal.zero_rpow (ne_of_gt hc0), zero_mul] at hint
    have hval0 : Valued.v (resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hmc0 hmc1 z) = 0 :=
      le_antisymm hint zero_le
    exact transport _ _ hcomb hmc0 hmc1 hm0 hm1 ((Valuation.zero_iff _).mp hval0)

/-- **Kedlaya Corollary 4.6**: the restriction homomorphism `B^I → B^{I'}` is
injective when the target interval is interior. -/
theorem resIHom_injective {θ η : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ * ρ₂ ^ (1 - θ)) (hσ₁1 : ρ₁ ^ θ * ρ₂ ^ (1 - θ) < 1)
    (hσ₂0 : 0 < ρ₁ ^ η * ρ₂ ^ (1 - η)) (hσ₂1 : ρ₁ ^ η * ρ₂ ^ (1 - η) < 1) :
    Function.Injective (resIHom p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ0.le hθ1.le hη0 hη1
      hσ₁0 hσ₁1 hσ₂0 hσ₂1) := by
  suffices hker : ∀ z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      resIHom p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
        hθ0.le hθ1.le hη0 hη1 hσ₁0 hσ₁1 hσ₂0 hσ₂1 z = 0 → z = 0 by
    intro a b hab
    have hd := hker (a - b) (by rw [RingHom.map_sub, hab, sub_self])
    exact sub_eq_zero.mp hd
  intro z hz0
  have h1 : resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hσ₁0 hσ₁1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = 0 :=
    congrArg (fun w : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) =>
      ((w : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)).1)) hz0
  have hkey : ∀ (ε : NNReal), 0 < ε →
      Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ≤ ε
        ∧ Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ ε := by
    intro ε hε
    obtain ⟨x, hx⟩ := exists_BIProd_approx p F ϖ z.2 hε
    have hxint : ∀ (α : ℝ), 0 < α → α < 1 →
        ∀ (hm0 : 0 < ρ₁ ^ α * ρ₂ ^ (1 - α)) (hm1 : ρ₁ ^ α * ρ₂ ^ (1 - α) < 1),
        wLoc p F ϖ hm0 hm1 x ≤ ε := by
      intro α hα0 hα1 hm0 hm1
      have hres0 := resI_eq_zero_of_interior p F ϖ hθ0 hθ1 hσ₁0 hσ₁1 z.2 h1
        hα0 hα1 hm0 hm1
      have hmemsub : (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          - (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
          ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
        sub_mem (BIProd_mem_BISub p F ϖ x) z.2
      have hsplit : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          = (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
            - (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
            + (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by ring
      have hadd := resI_add p F ϖ hα0.le hα1.le hm0 hm1 hmemsub z.2
      have hres : BlocToHatK p F ϖ hm0 hm1 x
          = resI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hm0 hm1
            (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
              - (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := by
        rw [← resI_BIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) hα0.le hα1.le hm0 hm1 x]
        conv_lhs => rw [hsplit]
        rw [hadd, hres0, add_zero]
      rw [← valued_BlocToHatK, hres]
      refine le_trans (valued_resI_le_wI p F ϖ hα0.le hα1.le hm0 hm1 hmemsub) ?_
      have hswap : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x
          - (z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          = -((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x) := by ring
      rw [hswap, wI_neg]
      exact hx
    have hend2 : wLoc p F ϖ hρ₂0 hρ₂1 x ≤ ε := by
      refine wLoc_le_of_interior_bound p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hρ₂0 hρ₂1
        (fun m => (1 : ℝ) / (m + 2)) (fun m => by positivity)
        (fun m => ?_) (tendsto_interior_radius_right hρ₁0 hρ₂0) x hxint
      rw [div_lt_one (by positivity)]
      have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hend1 : wLoc p F ϖ hρ₁0 hρ₁1 x ≤ ε := by
      refine wLoc_le_of_interior_bound p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hρ₁0 hρ₁1
        (fun m => 1 - (1 : ℝ) / (m + 2)) (fun m => ?_)
        (fun m => ?_) (tendsto_interior_radius_left hρ₁0 hρ₂0) x hxint
      · have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hlt : (1 : ℝ) / (m + 2) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        linarith
      · have hpos : (0:ℝ) < 1 / (m + 2) := by positivity
        linarith
    constructor
    · have hsplit1 : ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
          = (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
            - BlocToHatK p F ϖ hρ₁0 hρ₁1 x) + BlocToHatK p F ϖ hρ₁0 hρ₁1 x := by
        ring
      have hcomp : Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
            - BlocToHatK p F ϖ hρ₁0 hρ₁1 x) ≤ ε := by
        refine le_trans (le_max_left _ (Valued.v
          (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
            - BlocToHatK p F ϖ hρ₂0 hρ₂1 x))) ?_
        exact hx
      calc Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)
          ≤ max (Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
              - BlocToHatK p F ϖ hρ₁0 hρ₁1 x))
            (Valued.v (BlocToHatK p F ϖ hρ₁0 hρ₁1 x)) := by
            conv_lhs => rw [hsplit1]
            exact Valuation.map_add _ _ _
        _ ≤ ε := by
            refine max_le hcomp ?_
            rw [valued_BlocToHatK]
            exact hend1
    · have hsplit2 : ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
          = (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
            - BlocToHatK p F ϖ hρ₂0 hρ₂1 x) + BlocToHatK p F ϖ hρ₂0 hρ₂1 x := by
        ring
      have hcomp : Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
            - BlocToHatK p F ϖ hρ₂0 hρ₂1 x) ≤ ε := by
        refine le_trans (le_max_right (Valued.v
          (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1
            - BlocToHatK p F ϖ hρ₁0 hρ₁1 x)) _) ?_
        exact hx
      calc Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
            : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
          ≤ max (Valued.v (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
              : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2
              - BlocToHatK p F ϖ hρ₂0 hρ₂1 x))
            (Valued.v (BlocToHatK p F ϖ hρ₂0 hρ₂1 x)) := by
            conv_lhs => rw [hsplit2]
            exact Valuation.map_add _ _ _
        _ ≤ ε := by
            refine max_le hcomp ?_
            rw [valued_BlocToHatK]
            exact hend2
  have hzero : ∀ w : hatK p F hρ₁0 hρ₁1, (∀ ε : NNReal, 0 < ε → Valued.v w ≤ ε) →
      Valued.v w = 0 := by
    intro w hw
    rcases eq_or_ne (Valued.v w) 0 with h | h
    · exact h
    · have hv0 : 0 < Valued.v w := pos_iff_ne_zero.mpr h
      have hhalf : 0 < Valued.v w / 2 := by positivity
      have := hw _ hhalf
      exact absurd this (not_le.mpr (NNReal.half_lt_self h))
  have hzero2 : ∀ w : hatK p F hρ₂0 hρ₂1, (∀ ε : NNReal, 0 < ε → Valued.v w ≤ ε) →
      Valued.v w = 0 := by
    intro w hw
    rcases eq_or_ne (Valued.v w) 0 with h | h
    · exact h
    · have hv0 : 0 < Valued.v w := pos_iff_ne_zero.mpr h
      have hhalf : 0 < Valued.v w / 2 := by positivity
      have := hw _ hhalf
      exact absurd this (not_le.mpr (NNReal.half_lt_self h))
  have hfst : ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1 = 0 :=
    (Valuation.zero_iff _).mp (hzero _ fun ε hε => (hkey ε hε).1)
  have hsnd : ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2 = 0 :=
    (Valuation.zero_iff _).mp (hzero2 _ fun ε hε => (hkey ε hε).2)
  refine Subtype.ext ?_
  exact Prod.ext hfst hsnd

end FarguesFontaine

end
