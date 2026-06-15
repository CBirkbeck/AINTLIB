import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonDescentClose

/-!
# [FLT37-CASEII-R2-L5c] Discharging the integer-witness packaging of the §9.1 propagation data

This is the sub-ticket `T-R2-L5c` (parent `T-R2-L5`): we reduce the §9.1 propagation residual
`CaseIIWashingtonLemma96PropagationData37` (`CaseIIWashingtonDescentClose.lean`) to a **strictly
smaller** residual `CaseIIWashingtonLemma96EllOnly37` that **drops** the integer-witness existence,
the σ-fixed descent unit `δ'`, the reality of `ω, θ`, and the integer descended Fermat equation,
keeping (besides the 𝔭-coprimality geometry) **only** the Lemma-9.6/9.7 `ℓ`-propagation.

## The key insight (the factor units `η_a, η_b` are integral)

The §9.1 factor equation `algebraMap(x+ζ·y) = (1−ζ)·η_a·ρ_a³⁷` (with the factor unit `η_a`) gives
`ρ_a³⁷ = algebraMap(x+ζ·y)·(1−ζ)⁻¹·η_a⁻¹`.  Now `(ζ−1) ∣ (x+ζ·y)` in `𝓞 K`
(`caseII_zetaSubOne_dvd_x_add_y_mul`), so `(x+ζ·y)/(ζ−1) ∈ 𝓞 K`, and **when the factor unit `η_a`
is the `algebraMap` of an integral unit `u_a : (𝓞 K)ˣ`** (which it is — the proven product half
sets `η_a = Units.map (algebraMap) u`), `ρ_a³⁷ = algebraMap(integer)` is integral.  Since `𝓞 K` is
integrally closed, `ρ_a ∈ 𝓞 K` (it is a root of the monic `T³⁷ − ρ_a³⁷` over `𝓞 K`).  Then the
conjugate norm `ρ_a·σρ_a`, the descended block `ω = v²·ρ_a·σρ_a`, and `θ = −ρ_b·σρ_b` are all
integral, the σ-fixed descent unit `δ' = u₀²·θ'·u_b⁻²` is an integral unit, and the integer
descended equation `ω³⁷ + θ³⁷ = δ'·Λ^{2e−1}·(ρ₀²)³⁷` descends from the field reassembly by
injectivity of `algebraMap`.

## Soundness (B2-checked)

The factor units `η_a, η_b` are **genuinely** integral (the proven product half `η' = Units.map
(algebraMap) u`), so carrying the integral-unit witnesses `u_a, u_b` in the reduced residual is the
**true minimal content** that makes the integer witnesses exist.  This is *necessary*: the
propagation residual quantifies over **field** units `η_a, η_b : Kˣ`, and for a non-integral real
field unit (e.g. `η_a = 2·η_a⁰`) the descended block `v²ρ_aσρ_a` is *not* integral, so no integer
`ω` with `algebraMap ω = v²ρ_aσρ_a` exists — the integer-witness existence is **not** derivable from
the field factor equations alone.  Carrying the integral-unit witnesses (and *not* the integer
witnesses themselves, nor `δ'`, nor the equation, nor reality) is the sound, strictly smaller
residual.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), p. 172;
  Lemma 9.6 (p. 179).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The factor generator `ρ_a` is integral when the factor unit is integral -/

/-- **[L5c — `ρ_a` integral]** From the §9.1 positive factor equation at a root `η ≠ η₀`,
`algebraMap(x) + algebraMap(η)·algebraMap(y) = (1−algebraMap η)·η_a·ρ_a³⁷`, **with the factor unit
`η_a = algebraMap u_a` integral** (`u_a : (𝓞 K)ˣ`), the generator `ρ_a` is the `algebraMap`-image of
an integer `r_a : 𝓞 K`.

The mechanism: `(ζ−1) ∣ (x+η·y)` (`caseII_zetaSubOne_dvd_x_add_y_mul`), so writing
`x+η·y = (ζ−1)·M`, cancelling the `(1−η) ≠ 0` factor gives `ρ_a³⁷ = algebraMap(−M·u_a⁻¹)`, an
integer; `𝓞 K` integrally closed then yields `ρ_a ∈ 𝓞 K`. -/
theorem caseII_factorGenerator_integral_of_unitInt
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (ηa : (CyclotomicField 37 ℚ)ˣ) (ρa : CyclotomicField 37 ℚ) (ua : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) :
    ∃ ra : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ra = ρa := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- `(ζ−1) ∣ (x + η·y)`, giving `x + η·y = (ζ−1)·M`.
  obtain ⟨M, hM⟩ := caseII_zetaSubOne_dvd_x_add_y_mul D hp η
  -- `(1 − algebraMap η) ≠ 0`.
  have hden_ne : (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _))
      ≠ 0 := by
    have := caseII_section91_one_sub_eta_ne_zero D η hη
    rwa [map_sub, map_one] at this
  -- The LHS of the factor equation rewritten via `x + η·y = (ζ−1)·M`.
  have hLHS : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _) *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger - 1)) *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) M := by
    have h1 : D.x + D.y * (η : 𝓞 (CyclotomicField 37 ℚ)) = (D.hζ.toInteger - 1) * M := hM
    have h2 := congrArg (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) h1
    rw [map_add, map_mul, map_mul] at h2
    linear_combination h2
  -- `(ζ−1) = −(1 − ζ)` and `(1 − algebraMap ζ) = (1 − algebraMap η)` for `η ≠ η₀`...
  -- but `η` here is the *general* adjacent root: the divisibility uses `D.hζ.toInteger − 1`,
  -- which we relate to the denominator `1 − algebraMap η` via the cancellation below.
  -- Cancel: `(1 − algebraMap η)·η_a·ρ_a³⁷ = (algebraMap(ζ−1))·algebraMap M`.
  have hkey : (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
        ((ηa : CyclotomicField 37 ℚ) * ρa ^ 37) =
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger - 1)) *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) M := by
    rw [show (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
        ((ηa : CyclotomicField 37 ℚ) * ρa ^ 37) =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37 from by ring, ← hfa, hLHS]
  -- The clean route: `ρ_a³⁷ = algebraMap(M · N · u_a⁻¹)`, `(ζ−1) = (1−η)·N` for an integer `N`.
  -- `(1 − η) ∣ (ζ − 1)`: both are `𝔭`-uniformizers, `Associated`.
  obtain ⟨N, hN⟩ : (1 - (η : 𝓞 (CyclotomicField 37 ℚ))) ∣ (D.hζ.toInteger - 1) := by
    -- `Associated (ζ − 1) (η − 1)` from the pairwise root-difference associatedness (`η ≠ 1`).
    have hmem_eta : (η : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) := η.2
    have hmem_one : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
      one_mem_nthRootsFinset (by norm_num)
    have hne : (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ (1 : 𝓞 (CyclotomicField 37 ℚ)) := by
      have h1 : (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) :=
        fun h => hη (Subtype.ext h)
      rwa [caseII_etaZero_eq_one D hp] at h1
    have hpair := D.hζ.toInteger_isPrimitiveRoot
      |>.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        (by decide : Nat.Prime 37) hmem_eta hmem_one hne
    -- `hpair : Associated (ζ − 1) (η − 1)`.  `(1 − η) = −(η − 1) ~ (η − 1)`, so `(1−η) ∣ (ζ−1)`.
    have hassoc : Associated (1 - (η : 𝓞 (CyclotomicField 37 ℚ))) (D.hζ.toInteger - 1) := by
      have hneg : Associated (1 - (η : 𝓞 (CyclotomicField 37 ℚ)))
          ((η : 𝓞 (CyclotomicField 37 ℚ)) - 1) := by
        refine ⟨-1, ?_⟩; rw [Units.val_neg, Units.val_one]; ring
      exact hneg.trans hpair.symm
    exact hassoc.dvd
  -- `ρ_a³⁷ = algebraMap(M·N·u_a⁻¹)`.
  have hρa37 : ρa ^ 37 =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (M * N * ((ua⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) := by
    have hηa_ne : (ηa : CyclotomicField 37 ℚ) ≠ 0 := ηa.ne_zero
    -- `(ζ−1) = (1−η)·N`, so `algebraMap(ζ−1) = (1−algebraMap η)·algebraMap N`.
    have hNeq : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger - 1) =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) N := by
      have := congrArg (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) hN
      rw [map_mul, map_sub, map_one] at this
      exact this
    -- From `hkey`: `(1−η)·η_a·ρ_a³⁷ = (1−η)·algebraMap N·algebraMap M`; cancel `(1−η)`.
    have hkey2 : (ηa : CyclotomicField 37 ℚ) * ρa ^ 37 =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) N *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) M := by
      have h3 : (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
          ((ηa : CyclotomicField 37 ℚ) * ρa ^ 37) =
          (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) N *
              algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) M) := by
        rw [hkey, hNeq]; ring
      exact mul_left_cancel₀ hden_ne h3
    -- Divide by `η_a = algebraMap u_a`.
    have huinv : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((ua⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
        (ηa : CyclotomicField 37 ℚ)⁻¹ := by
      rw [show ((ua⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
        (((ua : (𝓞 (CyclotomicField 37 ℚ))ˣ))⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) from rfl,
        map_units_inv, hua]
    rw [map_mul, map_mul, huinv]
    field_simp
    linear_combination hkey2
  -- Integral closure: `ρ_a ∈ 𝓞 K`.
  exact IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := 𝓞 (CyclotomicField 37 ℚ)) (K := CyclotomicField 37 ℚ)
    (by decide : 0 < 37) (by rw [hρa37]; exact isIntegral_algebraMap)

/-! ## 2. The Assumption-II unit `v` is integral when the factor units are integral -/

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[L5c — Assumption-II unit integral]** When the factor units `η_a, η_b` are `algebraMap` of
integral units `u_a, u_b : (𝓞 K)ˣ`, the Assumption-II `37`-th root `v` (`η_a = v³⁷·η_b`) is the
`algebraMap`-image of an **integral unit** `vU : (𝓞 K)ˣ`.

`v³⁷ = η_a·η_b⁻¹ = algebraMap(u_a·u_b⁻¹)` is integral, so `v ∈ 𝓞 K` (integral closure), and
`v` is a unit because `v³⁷` is. -/
theorem caseII_assumptionII_unit_integral
    (ηa ηb v : (CyclotomicField 37 ℚ)ˣ) (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hII : (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb) :
    ∃ vU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (vU : 𝓞 _) =
        (v : CyclotomicField 37 ℚ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  -- `(v : K)³⁷ = algebraMap(↑(u_a·u_b⁻¹))`.
  have hv37 : (v : CyclotomicField 37 ℚ) ^ 37 =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((ua * ub⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
    have hv37' : (v : CyclotomicField 37 ℚ) ^ 37 =
        (ηa : CyclotomicField 37 ℚ) * (ηb : CyclotomicField 37 ℚ)⁻¹ := by
      have h := congrArg (fun w : (CyclotomicField 37 ℚ)ˣ => (w : CyclotomicField 37 ℚ)) hII
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
      rw [h, mul_assoc, mul_inv_cancel₀ ηb.ne_zero, mul_one]
    rw [hv37', Units.val_mul, map_mul, hua,
      show ((ub⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
        (((ub : (𝓞 (CyclotomicField 37 ℚ))ˣ))⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) from rfl,
      map_units_inv, hub]
  -- `v ∈ 𝓞 K`.
  obtain ⟨vi, hvi⟩ : ∃ vi : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) vi =
        (v : CyclotomicField 37 ℚ) :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := 𝓞 (CyclotomicField 37 ℚ)) (K := CyclotomicField 37 ℚ)
      (by decide : 0 < 37) (by rw [hv37]; exact isIntegral_algebraMap)
  -- `vi³⁷ = ↑(u_a·u_b⁻¹)` in `𝓞 K`, a unit; hence `vi` is a unit.
  have hvi37 : vi ^ 37 = ((ua * ub⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
      𝓞 (CyclotomicField 37 ℚ)) := by
    apply hinj; rw [map_pow, hvi, hv37]
  have hvi_unit : IsUnit vi := by
    refine IsUnit.of_mul_eq_one (a := vi) (vi ^ 36 *
      (((ua * ub⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ)⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
        𝓞 (CyclotomicField 37 ℚ))) ?_
    rw [← mul_assoc, ← pow_succ', hvi37, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact ⟨hvi_unit.unit, by rw [IsUnit.unit_spec, hvi]⟩

/-! ## 3. The negative factor equation from the positive one (by complex conjugation) -/

/-- **[L5c — conjugate factor equation]** Applying `σ = complexConj` to the positive §9.1 factor
equation `algebraMap(x) + algebraMap(η)·algebraMap(y) = (1−algebraMap η)·η_a·ρ_a³⁷` (with `x, y`
real and `η_a` real) gives the conjugate factor equation
`algebraMap(x) + algebraMap(η³⁶)·algebraMap(y) = (1−algebraMap η³⁶)·η_a·(σρ_a)³⁷`. -/
theorem caseII_factorEq_neg_of_pos
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (ηa : (CyclotomicField 37 ℚ)ˣ) (ρa : CyclotomicField 37 ℚ)
    (hηa : complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
      (ηa : CyclotomicField 37 ℚ))
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) :
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36)) *
        (ηa : CyclotomicField 37 ℚ) * (complexConj (CyclotomicField 37 ℚ) ρa) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 = 1 :=
    (mem_nthRootsFinset (by norm_num) _).mp η.2
  -- `σ(algebraMap η) = algebraMap η³⁶` (root of unity, `σζ = ζ⁻¹ = ζ³⁶`).
  have hση : complexConj (CyclotomicField 37 ℚ)
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36) := by
    rw [← coe_ringOfIntegersComplexConj]
    congr 1
    exact caseII_ringOfIntegersComplexConj_root_of_unity h37
  -- `σ(algebraMap x) = algebraMap x`, `σ(algebraMap y) = algebraMap y` (real).
  have hσx : complexConj (CyclotomicField 37 ℚ)
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x := by
    rw [← coe_ringOfIntegersComplexConj, D.x_real]
  have hσy : complexConj (CyclotomicField 37 ℚ)
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y := by
    rw [← coe_ringOfIntegersComplexConj, D.y_real]
  -- Apply `σ` to the positive factor equation.
  have h := congrArg (complexConj (CyclotomicField 37 ℚ)) hfa
  rw [map_add, map_mul, hσx, hσy, hση, map_mul, map_mul, map_sub, map_one, hση, hηa] at h
  -- `h` now has `algebraMap(η³⁶)` and `complexConj(ρa³⁷)`; align the goal's `(σρa)³⁷` and the
  -- `algebraMap(η³⁶)` powers (both via `map_pow`).
  rw [map_pow (complexConj (CyclotomicField 37 ℚ)) ρa 37] at h
  exact h

/-! ## 4. The integer descended equation with the σ-fixed descent unit `δ'` constructed -/

/-- **[L5c — packaged conclusion]** The integer-witness output of the §9.1 descent: integer
conjugate-norm blocks `ω, θ`, a σ-fixed descent unit `δ'`, the `algebraMap` specs, reality, and the
integer descended Fermat equation.  Wrapped as a named `def` so that the (heavy) producer
`caseII_integer_descended_equation_of_unitInt` returns a *def-headed* type — the call-site argument
unification then sees only the explicit hypothesis types, not this dependent `∃`, avoiding the
`whnf` blow-up. -/
def CaseIIIntDescOutput37 {m : ℕ} (_D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (e : ℕ)
    (ρ0 : 𝓞 (CyclotomicField 37 ℚ)) (v : (CyclotomicField 37 ℚ)ˣ)
    (ρa ρb : CyclotomicField 37 ℚ) : Prop :=
  ∃ (ω θ : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
      (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
      -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
    NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
    NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
    ω ^ 37 + θ ^ 37 =
      (δ' : 𝓞 (CyclotomicField 37 ℚ)) *
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ (2 * e - 1) *
        (ρ0 ^ 2) ^ 37

open scoped Classical in
/-- **[L5c — integer descended equation, `δ'` constructed]** From the §9.1 positive factor equations
at `ζ`, `ζ²` (real factor units `η_a = algebraMap u_a`, `η_b = algebraMap u_b`), the real anchor
equation `algebraMap(x+y) = algebraMap(u₀)·Λ^e·algebraMap(ρ₀)³⁷` (`u₀ : (𝓞 K)ˣ` real), and real
Assumption II `η_a = v³⁷·η_b` (`v : Kˣ` real), the conjugate-norm blocks have integer witnesses and
the integer descended Fermat equation holds with a **constructed** σ-fixed descent unit
`δ' = u₀²·θ'·u_b⁻² : (𝓞 K)ˣ`:
```
ω³⁷ + θ³⁷ = δ' · Λ^{2e-1} · (ρ₀²)³⁷,    ω = v²·ρ_a·σρ_a, θ = -ρ_b·σρ_b,  Λ = (1−ζ)(1−ζ³⁶).
```
The integer witnesses `ω, θ` exist because `η_a, η_b` are integral (`ρ_a, ρ_b ∈ 𝓞 K` via integral
closure, `caseII_factorGenerator_integral_of_unitInt`) and `v` is integral
(`caseII_assumptionII_unit_integral`); `δ'` is constructed from the §9.1 crux unit `θ'` and the
integral anchor/factor units. -/
theorem caseII_integer_descended_equation_of_unitInt
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (e : ℕ) (he : 1 ≤ e) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ))
    (hanchor : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
            (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37)
    (ηa ηb v : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
    (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hηa : complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
      (ηa : CyclotomicField 37 ℚ))
    (hηb : complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
      (ηb : CyclotomicField 37 ℚ))
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37)
    (hfb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37)
    (hv_real : complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
      (v : CyclotomicField 37 ℚ))
    (hII : (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb) :
    CaseIIIntDescOutput37 D e ρ0 v ρa ρb := by
  rw [CaseIIIntDescOutput37]
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set σR := NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
  -- The two roots `ζ`, `ζ²`, with the root-of-unity / distinctness facts.
  set ζ : 𝓞 (CyclotomicField 37 ℚ) := D.hζ.toInteger with hζ_def
  have hζ37 : ζ ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hζ1 : ζ ≠ 1 := D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hζ2_37 : (ζ ^ 2) ^ 37 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ37, one_pow]
  have hζ2_1 : ζ ^ 2 ≠ 1 := by
    intro h
    have : (37 : ℕ) ∣ 2 := (D.hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd 2).mp h
    omega
  have hAB : ζ ≠ ζ ^ 2 := by
    intro h
    have := D.hζ.toInteger_isPrimitiveRoot.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num)
      (by rw [pow_one]; exact h)
    omega
  have hABp : ζ * ζ ^ 2 ≠ 1 := by
    rw [show ζ * ζ ^ 2 = ζ ^ 3 from by ring]
    intro h
    have : (37 : ℕ) ∣ 3 := (D.hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd 3).mp h
    omega
  -- `η₀ = 1` (`caseII_etaZero_eq_one`).
  have hetaZero : (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) = 1 := by
    rw [caseII_etaZero_eq_one D hp]
  -- `ρ_a, ρ_b ∈ 𝓞 K` (factor generators integral, the key insight).
  have hηOne_ne : (⟨ζ, D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)⟩ :
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) ≠ D.etaZero := by
    intro h
    exact hζ1 (by have := Subtype.ext_iff.mp h; rw [hetaZero] at this; exact this)
  obtain ⟨ra, hra⟩ := caseII_factorGenerator_integral_of_unitInt D
    ⟨ζ, D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)⟩ hηOne_ne ηa ρa ua
    hua hfa
  have hmem2 : ζ ^ 2 ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    (mem_nthRootsFinset (by norm_num) _).mpr hζ2_37
  have hηTwo_ne : (⟨ζ ^ 2, hmem2⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) ≠
      D.etaZero := by
    intro h
    exact hζ2_1 (by have := Subtype.ext_iff.mp h; rw [hetaZero] at this; exact this)
  obtain ⟨rb, hrb⟩ := caseII_factorGenerator_integral_of_unitInt D ⟨ζ ^ 2, hmem2⟩ hηTwo_ne ηb ρb ub
    hub (by
      rw [show ((⟨ζ ^ 2, hmem2⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
        𝓞 (CyclotomicField 37 ℚ)) = ζ ^ 2 from rfl]; exact hfb)
  -- `v ∈ 𝓞 K` (Assumption-II unit integral).
  obtain ⟨vU, hvU⟩ := caseII_assumptionII_unit_integral ηa ηb v ua ub hua hub hII
  set am := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) with ham
  have hinj : Function.Injective am := FaithfulSMul.algebraMap_injective _ _
  -- `algebraMap (σR z) = complexConj (algebraMap z)`.
  have hσRcoe : ∀ z : 𝓞 (CyclotomicField 37 ℚ),
      am (σR z) = complexConj (CyclotomicField 37 ℚ) (am z) := fun z => by
    rw [ham, ← coe_ringOfIntegersComplexConj]
  -- `algebraMap (σR ra) = complexConj ρa`, similarly `σR rb`.
  have hσra : am (σR ra) = complexConj (CyclotomicField 37 ℚ) ρa := by rw [hσRcoe, hra]
  have hσrb : am (σR rb) = complexConj (CyclotomicField 37 ℚ) ρb := by rw [hσRcoe, hrb]
  -- `σR vU = vU` (real), `σR ra` involutive, etc.
  have hσRvU : σR (vU : 𝓞 (CyclotomicField 37 ℚ)) = (vU : 𝓞 _) := by
    apply hinj; rw [hσRcoe, hvU, hv_real]
  have hσRinv : ∀ z : 𝓞 (CyclotomicField 37 ℚ), σR (σR z) = z := fun z => by
    apply hinj; rw [hσRcoe, hσRcoe, complexConj_apply_apply]
  -- The §9.1 crux unit `θ'_int : (𝓞 K)ˣ` (real) at the roots `ζ`, `ζ²`.
  obtain ⟨θ'_int, hθ'_real, hθ'_id⟩ :=
    washington_section91_crux_unit (K := CyclotomicField 37 ℚ) hζ37 hζ2_37 hζ1 hζ2_1 hAB hABp
  -- The descent unit `δ' = u₀²·θ'·u_b⁻²`.
  set δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ := u0 ^ 2 * θ'_int * ub⁻¹ ^ 2 with hδ'_def
  -- Nonzero facts.
  have hζ36_37 : (ζ ^ 36) ^ 37 = 1 := by
    rw [← pow_mul, show 36 * 37 = 37 * 36 from by norm_num, pow_mul, hζ37, one_pow]
  have hζ36_ne1 : ζ ^ 36 ≠ 1 := by
    intro h
    have : ζ ^ 37 = ζ ^ 36 * ζ := by rw [← pow_succ]
    rw [hζ37, h, one_mul] at this; exact hζ1 this.symm
  have hζ2_36_ne1 : (ζ ^ 2) ^ 36 ≠ 1 := by
    intro h
    have : (ζ ^ 2) ^ 37 = (ζ ^ 2) ^ 36 * ζ ^ 2 := by rw [← pow_succ]
    rw [hζ2_37, h, one_mul] at this; exact hζ2_1 this.symm
  have hroot_ne : ∀ w : 𝓞 (CyclotomicField 37 ℚ), w ≠ 1 → (1 : CyclotomicField 37 ℚ) - am w ≠ 0 :=
    fun w hw h => hw (hinj (by rw [map_one]; linear_combination -h))
  have h1ζ_ne := hroot_ne ζ hζ1
  have h1ζ36_ne := hroot_ne (ζ ^ 36) hζ36_ne1
  have h1ζ2_ne := hroot_ne (ζ ^ 2) hζ2_1
  have h1ζ2_36_ne := hroot_ne ((ζ ^ 2) ^ 36) hζ2_36_ne1
  -- `Λ` (anchor uniformizer) `≠ 0` and `ρ₀ ≠ 0`.
  set ζs : 𝓞 (CyclotomicField 37 ℚ) := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
    with hζs_def
  have hζs37 : ζs ^ 37 = 1 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
  have hζs1 : ζs ≠ 1 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hζs36_ne1 : ζs ^ 36 ≠ 1 := by
    intro h
    have : ζs ^ 37 = ζs ^ 36 * ζs := by rw [← pow_succ]
    rw [hζs37, h, one_mul] at this; exact hζs1 this.symm
  have hΛint_ne : (1 - ζs) * (1 - ζs ^ 36) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr fun h => hζs1 h.symm) (sub_ne_zero.mpr fun h => hζs36_ne1 h.symm)
  have hΛam_ne : am ((1 - ζs) * (1 - ζs ^ 36)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hΛint_ne
  have hρ0_ne : ρ0 ≠ 0 := by
    intro h0
    have hxy_ne : D.x + D.y ≠ 0 := caseII_data_x_add_y_ne_zero D hp
    apply hxy_ne
    apply hinj
    rw [map_zero, hanchor, h0]
    rw [map_zero, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero]
  -- The field descended equation, via `washington_section91_reassembly`.
  have hfield :
      ((v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
          (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
        am (δ' : 𝓞 _) * (am ((1 - ζs) * (1 - ζs ^ 36))) ^ (2 * e - 1) * ((am ρ0) ^ 2) ^ 37 := by
    have hmapη0 : ((Units.map (am : 𝓞 (CyclotomicField 37 ℚ) →* CyclotomicField 37 ℚ) u0 :
        (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) = am (u0 : 𝓞 _) := by
      rw [Units.coe_map]; rfl
    have hmapθ' : ((Units.map (am : 𝓞 (CyclotomicField 37 ℚ) →* CyclotomicField 37 ℚ) θ'_int :
        (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) = am (θ'_int : 𝓞 _) := by
      rw [Units.coe_map]; rfl
    have hΛacoe : ((Units.mk0 ((1 - am ζ) * (1 - am (ζ ^ 36))) (mul_ne_zero h1ζ_ne h1ζ36_ne) :
        (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) = (1 - am ζ) * (1 - am (ζ ^ 36)) := rfl
    have hΛbcoe : ((Units.mk0 ((1 - am (ζ ^ 2)) * (1 - am ((ζ ^ 2) ^ 36)))
        (mul_ne_zero h1ζ2_ne h1ζ2_36_ne) : (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) =
        (1 - am (ζ ^ 2)) * (1 - am ((ζ ^ 2) ^ 36)) := rfl
    have hΛcoe : ((Units.mk0 (am ((1 - ζs) * (1 - ζs ^ 36))) hΛam_ne :
        (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) = am ((1 - ζs) * (1 - ζs ^ 36)) := rfl
    -- the descent unit `η0²·θ'·ηb⁻²` (with the *field* `ηb`) equals `am δ'`.
    have hδ'coe : ((Units.map (am : 𝓞 (CyclotomicField 37 ℚ) →* CyclotomicField 37 ℚ) u0 ^ 2 *
          Units.map (am : 𝓞 (CyclotomicField 37 ℚ) →* CyclotomicField 37 ℚ) θ'_int *
          ηb⁻¹ ^ 2 : (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) = am (δ' : 𝓞 _) := by
      have hηbinv : ((ηb⁻¹ : (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) =
          am ((ub⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 _) := by
        rw [Units.val_inv_eq_inv_val, ← hub, map_units_inv]
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        hmapη0, hmapθ', hηbinv, hδ'_def, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, map_mul, map_mul, map_pow, map_pow]
    rw [← hδ'coe]
    refine washington_section91_reassembly (x := am D.x) (y := am D.y)
      (ρa := ρa) (ρb := ρb) (ρ0 := am ρ0)
      (zpa := am ζ) (zna := am (ζ ^ 36)) (zpb := am (ζ ^ 2)) (znb := am ((ζ ^ 2) ^ 36))
      (ηa := ηa) (ηb := ηb)
      (η0 := Units.map (am : 𝓞 (CyclotomicField 37 ℚ) →* CyclotomicField 37 ℚ) u0)
      (u := v) (θ' := Units.map (am : 𝓞 (CyclotomicField 37 ℚ) →* CyclotomicField 37 ℚ) θ'_int)
      (Λa := Units.mk0 ((1 - am ζ) * (1 - am (ζ ^ 36))) (mul_ne_zero h1ζ_ne h1ζ36_ne))
      (Λb := Units.mk0 ((1 - am (ζ ^ 2)) * (1 - am ((ζ ^ 2) ^ 36)))
        (mul_ne_zero h1ζ2_ne h1ζ2_36_ne))
      (Λ := Units.mk0 (am ((1 - ζs) * (1 - ζs ^ 36))) hΛam_ne)
      (e := e) he ?_ ?_ hΛacoe hΛbcoe ?_ ?_ ?_ ?_ ?_ hII ?_
    · rw [← map_mul, show ζ * ζ ^ 36 = ζ ^ 37 from by ring, hζ37, map_one]
    · rw [← map_mul, show ζ ^ 2 * (ζ ^ 2) ^ 36 = (ζ ^ 2) ^ 37 from by ring, hζ2_37, map_one]
    · exact hfa
    · exact caseII_factorEq_neg_of_pos D
        ⟨ζ, D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)⟩ ηa ρa hηa hfa
    · exact hfb
    · have hneg := caseII_factorEq_neg_of_pos D ⟨ζ ^ 2, hmem2⟩ ηb ρb hηb (by
        rw [show ((⟨ζ ^ 2, hmem2⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
          𝓞 (CyclotomicField 37 ℚ)) = ζ ^ 2 from rfl]; exact hfb)
      rwa [show ((⟨ζ ^ 2, hmem2⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
        𝓞 (CyclotomicField 37 ℚ)) = ζ ^ 2 from rfl] at hneg
    · -- `hanchor`.
      rw [hmapη0, hΛcoe, ← map_add]
      convert hanchor using 2
    · -- `hcrux`.
      rw [hΛacoe, hΛbcoe, hmapθ', hΛcoe,
        show (1 - am ζ) * (1 - am (ζ ^ 36)) = am ((1 - ζ) * (1 - ζ ^ 36)) from by
          rw [map_mul, map_sub, map_sub, map_one],
        show (1 - am (ζ ^ 2)) * (1 - am ((ζ ^ 2) ^ 36)) =
          am ((1 - ζ ^ 2) * (1 - (ζ ^ 2) ^ 36)) from by rw [map_mul, map_sub, map_sub, map_one]]
      exact hθ'_id
  -- The integer-witness `algebraMap` specs (the conjugate-norm blocks).
  have hωspec : am (vU ^ 2 * (ra * σR ra)) =
      (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) := by
    rw [map_mul, map_pow, hvU, map_mul, hra, hσra]
  have hθspec : am (-(rb * σR rb)) = -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) := by
    rw [map_neg, map_mul, hrb, hσrb]
  -- The integer conjugate-norm blocks and the assembled bundle.
  refine ⟨vU ^ 2 * (ra * σR ra), -(rb * σR rb), δ', hωspec, hθspec, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow, hσRvU, map_mul, hσRinv ra, mul_comm (σR ra) ra]
  · rw [map_neg, map_mul, hσRinv rb, mul_comm (σR rb) rb]
  · -- the integer descended equation (descend `hfield` by injectivity).
    apply hinj
    rw [map_add, map_pow, map_pow, hωspec, hθspec, map_mul, map_mul, map_pow, map_pow]
    exact hfield

/-! ## 5. The strictly smaller `ℓ`-only residual and the reduction to the propagation data -/

open scoped Classical in
/-- **[FLT37-CASEII-§9.1 LEMMA 9.6/9.7 `ℓ`-ONLY DATA] The carried §9.1 content reduced to the
integral-unit witnesses + the `ℓ`-propagation** (a `def … : Prop`, **not** an axiom).

Identical antecedent to `CaseIIWashingtonLemma96PropagationData37` (real `ℓ ∣ z` datum `D`,
coprimality, the L1 anchor data, the L2 factor outputs, the real Assumption-II unit `v`) **plus**
the integral-unit witnesses `u_a, u_b : (𝓞 K)ˣ` for the factor units (`algebraMap u_a = η_a`,
`algebraMap u_b = η_b` — genuinely available from the proven product half).  Its **conclusion** is
reduced to:

* the descended-variable `𝔭`-coprimality `(ζ−1) ∤ ρ₀²`;
* the `𝔭`-coprimality of `θ`, stated as `∀ θ, algebraMap θ = −ρ_bσρ_b → (ζ−1) ∤ θ` (no existence);
* the Lemma-9.6/9.7 `ℓ`-propagation `ρ₀² ∈ 𝔩`, and `∀ ω, algebraMap ω = v²ρ_aσρ_a → ω ∉ 𝔩`,
  `∀ θ, algebraMap θ = −ρ_bσρ_b → θ ∉ 𝔩` (no existence).

Compared to `CaseIIWashingtonLemma96PropagationData37`, the **integer-witness existence**, the
σ-fixed descent unit `δ'`, the **integer descended Fermat equation**, and the **reality** of `ω, θ`
are **dropped** — they are *derived* in the reduction below (`ρ_a, ρ_b, v` integral via integral
closure, given `u_a, u_b`; `δ'` from the §9.1 crux; the equation via the field reassembly).
Only the genuine carried content remains: the factor units are integral (`u_a, u_b`), the
`𝔭`-geometry of the descended blocks, and the aux-prime `ℓ`-propagation. -/
def CaseIIWashingtonLemma96EllOnly37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 →
    ∀ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) →
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) →
    ∀ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
          (v : CyclotomicField 37 ℚ) →
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb →
      -- the integral-unit witnesses for the factor units (the genuine carried content), together
      -- with the `𝔭`-geometry and the `ℓ`-propagation (stated as conditionals, no integer-witness
      -- existence for `ω, θ`):
      ∃ (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
            (ηa : CyclotomicField 37 ℚ) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
            (ηb : CyclotomicField 37 ℚ) ∧
        -- the descended-variable `𝔭`-coprimality `(ζ−1) ∤ ρ₀²`:
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ ρ0 ^ 2 ∧
        -- `(ζ−1) ∤ θ` for the integer `θ` (conditional, no existence):
        (∀ θ : 𝓞 (CyclotomicField 37 ℚ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
              -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) →
          ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ) ∧
        -- the Lemma-9.6/9.7 `ℓ`-propagation (conditionals + `ρ₀² ∈ 𝔩`):
        ρ0 ^ 2 ∈ lv149 ∧
        (∀ ω : 𝓞 (CyclotomicField 37 ℚ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
              (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) →
          ω ∉ lv149) ∧
        (∀ θ : 𝓞 (CyclotomicField 37 ℚ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
              -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) →
          θ ∉ lv149)

-- The bumped `maxHeartbeats` is needed because `intro` must unfold the very large
-- `CaseIIWashingtonLemma96PropagationData37` / `CaseIIWashingtonLemma96EllOnly37` defs (each a long
-- chain of `∀`/`→` over the §9.1 datum), and the final `exact` reassembles the equally large
-- propagation conclusion; the unfolding/`whnf` of these big `def … : Prop`s exceeds the default.
set_option maxHeartbeats 800000 in
/-- **[T-R2-L5c — THE INTEGER-WITNESS PACKAGING DISCHARGE] The propagation data follows from the
`ℓ`-only data** (proven, axiom-clean): `CaseIIWashingtonLemma96EllOnly37 →
CaseIIWashingtonLemma96PropagationData37`.

The propagation bundle's **integer witnesses** `ω, θ`, the **σ-fixed descent unit** `δ'`, the
**reality** `σω = ω`, `σθ = θ`, and the **integer descended Fermat equation** are all **derived**
from the `ℓ`-only data's integral-unit witnesses `u_a, u_b`:

* `ρ_a, ρ_b ∈ 𝓞 K` (factor generators integral, `caseII_factorGenerator_integral_of_unitInt`) and
  `v ∈ 𝓞 K` (`caseII_assumptionII_unit_integral`), so the conjugate-norm blocks
  `ω = v²·ρ_a·σρ_a`, `θ = −ρ_b·σρ_b` have integer witnesses;
* `δ' = u₀²·θ'·u_b⁻²` is the §9.1 crux descent unit, and the integer descended equation descends
  from the field reassembly by injectivity — all packaged by
  `caseII_integer_descended_equation_of_unitInt`.

The remaining conjuncts (the `𝔭`-coprimalities `(ζ−1) ∤ θ, ρ₀²`, the `ℓ`-propagation `ω, θ ∉ 𝔩`,
`ρ₀² ∈ 𝔩`) are read off from the `ℓ`-only data, applied to the **constructed** `ω, θ` via their
`algebraMap` specs.  This fully closes the integer-witness packaging of the R2 geometry. -/
theorem caseIIWashingtonLemma96PropagationData37_of_lemma96EllOnly
    (h_ellOnly : CaseIIWashingtonLemma96EllOnly37) :
    CaseIIWashingtonLemma96PropagationData37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb v hv_real hII
  -- The `ℓ`-only data: the integral-unit witnesses `u_a, u_b` for the factor units, the
  -- `𝔭`-geometry, and the `ℓ`-propagation conditionals.
  have hell := h_ellOnly D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb v hv_real hII
  obtain ⟨ua, ub, hua, hub, hz'_cop, hθ_cop, hz'_mem, hω_notMem, hθ_notMem⟩ := hell
  -- The integer descended equation: produces `ω, θ, δ'`, reality, and the integer equation, from
  -- the integral-unit witnesses (the key integral-closure insight).
  have hbig : CaseIIIntDescOutput37 D.toRealCaseIIData37 e ρ0 v ρa ρb :=
    caseII_integer_descended_equation_of_unitInt D.toRealCaseIIData37 e he u0 ρ0 hanchor ηa ηb v
      ρa ρb ua ub hua hub hηa hηb hfa hfb hv_real hII
  rw [CaseIIIntDescOutput37] at hbig
  obtain ⟨ω, θ, δ', hω, hθ, hω_real, hθ_real, hint_eq⟩ := hbig
  -- The σ-fixed-unit clause `hδ'`, derived from the integer equation + the `algebraMap` specs:
  -- any `δ` satisfying the field descended equation is `algebraMap δ'` (cancellation).
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hδ' : ∀ δ : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
          (δ : CyclotomicField 37 ℚ) →
      ((v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
          (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
        (δ : CyclotomicField 37 ℚ) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
          ((algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0) ^ 2) ^ 37 →
      (δ : CyclotomicField 37 ℚ) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _) := by
    intro δ _ hδ_eq
    -- `am (ω³⁷+θ³⁷) = (v²ρaσρa)³⁷ + (-ρbσρb)³⁷` (via the specs), `= am δ'·Λ^{2e-1}(ρ0²)³⁷`.
    have hLHS : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ω ^ 37 + θ ^ 37) =
        ((v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
          (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 := by
      rw [map_add, map_pow, map_pow, hω, hθ]
    have hRHS := congrArg (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) hint_eq
    rw [hLHS, map_mul, map_mul, map_pow, map_pow] at hRHS
    -- `δ·Λ^{2e-1}·X = am δ'·Λ^{2e-1}·X` (left-assoc); cancel `X` then `Λ^{2e-1}`.
    have hΛ_ne : (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, map_eq_zero_iff _ hinj]
      refine mul_ne_zero (sub_ne_zero.mpr fun h => ?_) (sub_ne_zero.mpr fun h => ?_)
      · exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one
          (by decide : 1 < 37) h.symm
      · have hp37 : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 37 = 1 :=
          (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
        have heq : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 37 =
            (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 *
              (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger := by rw [← pow_succ]
        rw [hp37, ← h, one_mul] at heq
        exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one
          (by decide : 1 < 37) heq.symm
    have hX_ne : ((algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0) ^ 2) ^ 37
        ≠ 0 := by
      refine pow_ne_zero _ (pow_ne_zero _ ?_)
      rw [Ne, map_eq_zero_iff _ hinj]
      intro h0
      refine caseII_data_x_add_y_ne_zero D.toRealCaseIIData37 (by decide : (37 : ℕ) ≠ 2) ?_
      apply hinj
      rw [map_zero, hanchor, h0, map_zero, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero]
    -- `δ·Λ^{2e-1}·X = am δ'·Λ^{2e-1}·X` from the two field equations.
    have hcancel := hδ_eq.symm.trans hRHS
    exact mul_right_cancel₀ hΛ_ne (mul_right_cancel₀ hX_ne hcancel)
  exact ⟨ω, θ, δ', hω, hθ, hδ', hθ_cop θ hθ, hint_eq, hz'_cop, hω_real, hθ_real, hz'_mem,
    hω_notMem ω hω, hθ_notMem θ hθ⟩

/-! ## 6. The FLT37 Case-II endpoint, on the `ℓ`-only residual (integer-witness packaging proven) -/

/-- **[T-R2-L5c] Fermat's Last Theorem for `37`, with the integer-witness packaging PROVEN**
(proven, axiom-clean *given* the named inputs + carried Kellner) — **the R2 geometry fully closed**.

Identical to `fermatLastTheoremFor_thirtyseven_of_washingtonDescent_lemma96Propagation`, **except**
the §9.1 propagation residual `CaseIIWashingtonLemma96PropagationData37` is replaced by the strictly
smaller `CaseIIWashingtonLemma96EllOnly37`: the **integer witnesses** `ω, θ`, the **σ-fixed descent
unit** `δ'`, the **reality** of `ω, θ`, and the **integer descended Fermat equation** are **no
longer carried** — they are *derived*
(`caseIIWashingtonLemma96PropagationData37_of_lemma96EllOnly`) from the
integral-unit witnesses `u_a, u_b` of the factor units (the key integral-closure insight:
`ρ_a, ρ_b, v ∈ 𝓞 K`, so the conjugate-norm blocks are integral), the §9.1 crux descent unit, and the
field reassembly.

So the FLT37 Case-II residual now rests on:
* `h_assumptionII` (`CaseIIWashingtonAssumptionIIReal37`): the real Assumption II;
* `h_ellOnly` (`CaseIIWashingtonLemma96EllOnly37`): the integral-unit witnesses `u_a, u_b`, the
  `𝔭`-geometry `(ζ−1) ∤ θ, ρ₀²`, and the aux-prime Lemma-9.6/9.7 `ℓ`-propagation — but **not** the
  integer witnesses, `δ'`, the equation, or reality;
* `h_cop`, `h_lemma96`, `noSecondOrderIrregular` (Kellner): unchanged.

This is the L5c deliverable: the **full integer-witness packaging** of the descended conjugate-norm
building blocks is **proven**, leaving only the genuine carried content (factor units integral,
`𝔭`-geometry, aux-prime `ℓ`-propagation) and the analytic Assumption II + Kellner inputs. -/
theorem fermatLastTheoremFor_thirtyseven_of_washingtonDescent_lemma96EllOnly
    (h_assumptionII : CaseIIWashingtonAssumptionIIReal37)
    (h_ellOnly : CaseIIWashingtonLemma96EllOnly37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_washingtonDescent_lemma96Propagation h_assumptionII
    (caseIIWashingtonLemma96PropagationData37_of_lemma96EllOnly h_ellOnly)
    h_cop h_lemma96 noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end
