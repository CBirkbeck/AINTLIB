import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonLemma96EllOnly

/-!
# [T-R2-L5d] The FINAL R2 geometry closure: FLT37 Case-II on the clean residual

This file is the **final R2 geometry wiring**.  Building on the proven L1
(`caseII_anchor_real_rho0_genuineUnit`) and the proven L2 product half
(`caseII_productHalf_field_eq`), it produces the **strengthened factor equations** that ALSO carry
the **integral-unit witnesses** `u_a, u_b : (𝓞 K)ˣ` for the factor units `η_a, η_b` (`η_a = η'^19`
with `η' = algebraMap u`, so `u_a = u^19`), and then discharges the entire integer-witness +
sharp-`𝔭`-geometry packaging of Washington's §9.1 descent **from a single clean residual**:

```
CaseIIWashingtonCaseII37 : real Assumption II (`η_a = v³⁷·η_b`, `v` real)
                          + the aux-prime Lemma-9.6/9.7 `ℓ`-propagation
                            (`ρ₀² ∈ 𝔩`, `ω ∉ 𝔩`, `θ ∉ 𝔩`, in conditional form)
                          + per-datum coprimality.
```

Everything else — the integer witnesses `ω, θ`, the σ-fixed descent unit `δ'`, the reality of
`ω, θ`, the integer descended Fermat equation, the sharp `𝔭`-valuation invariants `hxy'`/`hdenom'`,
the `𝔭`-coprimality `(ζ−1) ∤ θ, z'`, and the anchor-support `(z') = 𝔞₀²` — is **derived** (the L1
anchor, the strengthened L2 factor units, the integral-closure integer witnesses, and the proven
sharp root-ideal arithmetic), **not carried**.  So the FLT37 Case-II endpoint rests on the analytic
**real Assumption II**, the aux-prime **`ℓ`-membership**, **Kellner**, and the threaded
**coprimality** only — with the **full §9.1 geometry proven**.

## What L1/L2 do here (the geometry is PROVEN, not carried)

* **L1** is applied **internally** (`caseII_anchor_real_rho0_genuineUnit`): it supplies the anchor
  equation, the integral anchor unit `u₀`, the real generator `ρ₀` of `B₀`, and — crucially — the
  span `(ρ₀) = B₀`, whence `(ζ−1) ∤ ρ₀²` and the anchor-support `(z') = 𝔞₀²`.
* **L2** is applied **internally** in its strengthened form
  (`caseII_section91_factorEquations_etaOne_etaTwo_withUnits`): it supplies the factor equations at
  `ζ, ζ²` **together with** the integral units `u_a, u_b`.  These make `ρ_a, ρ_b ∈ 𝓞 K`
  (integral closure), so the conjugate-norm blocks `ω = v²ρ_aσρ_a`, `θ = −ρ_bσρ_b` have integer
  witnesses, and `(ζ−1) ∤ ρ_b` (from the sharp `v_𝔭(x+ζ²y) = 1`,
  `caseII_zeta_sub_one_sq_not_dvd_x_add_y_root`) gives `(ζ−1) ∤ θ`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 169–172, 179–180.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The strengthened squared form `X² = (algebraMap u)·W³⁷`, `u : (𝓞 K)ˣ` integral

`caseII_section91_squaredForm` takes the product half as an **opaque**
`CaseIISection91ProductHalf37` hypothesis, so its real unit `η'` is only a `Kˣ`.  We instead route
through the **proven** field
equation `caseII_productHalf_field_eq`, whose `η' = algebraMap u` for an **integral** unit
`u : (𝓞 K)ˣ`.  This retains the integrality that L2's abstract `η_a` discards. -/

/-- **[L5d — strengthened squared form, integral unit]** The §9.1 squared form
`X² = (algebraMap u)·W³⁷` with the real unit exposed as `algebraMap` of an **integral** unit
`u : (𝓞 K)ˣ`.

Identical to `caseII_section91_squaredForm` but the unit is `algebraMap u` (`u` integral): from the
proven quotient half `X/X̄ = β³⁷` (`caseII_section91_factorRatio_isPthPower`) and the proven product
**field** equation `X·X̄ = (algebraMap u)·(algebraMap γ₀)³⁷` (`caseII_productHalf_field_eq`,
`u : (𝓞 K)ˣ`), `X² = (X/X̄)·(X·X̄) = (algebraMap u)·(β·algebraMap γ₀)³⁷`. -/
theorem caseII_section91_squaredForm_withUnit
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (W : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ)
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _)) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) ∧
      caseII_section91_factor D η ^ 2 =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) * W ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- Proven quotient half: `X/X̄ = β³⁷`.
  obtain ⟨β, hβ⟩ := caseII_section91_factorRatio_isPthPower D η hη
  -- Proven product FIELD equation `X·X̄ = (algebraMap u)·γ₀³⁷` (`u : (𝓞 K)ˣ` integral, `γ₀` real).
  obtain ⟨u, γ₀, hγ₀_real, hprod⟩ := caseII_productHalf_field_eq D hp η hη hcop
  -- Fold both into the `caseII_section91_factor`/`factorConj` notation.
  rw [show (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (D.x + D.y * (η : 𝓞 _)) /
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))) /
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (D.x + D.y * ((η : 𝓞 _) ^ 36)) /
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36)) =
      caseII_section91_factor D η / caseII_section91_factorConj D η from rfl] at hβ
  rw [show (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (D.x + D.y * (η : 𝓞 _)) /
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))) *
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (D.x + D.y * ((η : 𝓞 _) ^ 36)) /
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36)) =
      caseII_section91_factor D η * caseII_section91_factorConj D η from rfl] at hprod
  refine ⟨u, β * algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀, ?_, ?_⟩
  · -- reality of `algebraMap u`: `(algebraMap u) = (X·X̄)/γ³⁷`, both real.
    have hreal_prod : complexConj (CyclotomicField 37 ℚ) (caseII_section91_factor D η *
        caseII_section91_factorConj D η) =
        caseII_section91_factor D η * caseII_section91_factorConj D η :=
      caseII_section91_product_real D η
    have hγ_real : complexConj (CyclotomicField 37 ℚ)
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ := by
      rw [← coe_ringOfIntegersComplexConj, hγ₀_real]
    have hprod_ne : caseII_section91_factor D η * caseII_section91_factorConj D η ≠ 0 :=
      mul_ne_zero (caseII_section91_factor_ne_zero D η hη)
        (caseII_section91_factorConj_ne_zero D η hη)
    have hγ_ne : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ ≠ 0 := by
      intro h0
      apply hprod_ne
      rw [hprod, h0, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero]
    have hγ37_real : complexConj (CyclotomicField 37 ℚ)
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ ^ 37) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ ^ 37 := by
      rw [map_pow, hγ_real]
    have hγ37_ne : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ ^ 37 ≠ 0 :=
      pow_ne_zero 37 hγ_ne
    have hu_eq : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) =
        (caseII_section91_factor D η * caseII_section91_factorConj D η) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ ^ 37 := by
      rw [hprod, mul_div_assoc, div_self hγ37_ne, mul_one]
    rw [hu_eq, map_div₀, hreal_prod, hγ37_real]
  · -- `X² = (X/X̄)·(X·X̄) = β³⁷·(algebraMap u)·γ³⁷`.
    have hXc_ne : caseII_section91_factorConj D η ≠ 0 := caseII_section91_factorConj_ne_zero D η hη
    have hsplit : caseII_section91_factor D η ^ 2 =
        (caseII_section91_factor D η / caseII_section91_factorConj D η) *
        (caseII_section91_factor D η * caseII_section91_factorConj D η) := by
      have hgen : ∀ a b : CyclotomicField 37 ℚ, b ≠ 0 → a ^ 2 = (a / b) * (a * b) := by
        intro a b hb; field_simp
      exact hgen _ _ hXc_ne
    rw [hsplit, hβ, hprod, mul_pow]; ring

/-! ## 2. The strengthened factor equations with the integral unit `u_a : (𝓞 K)ˣ`

Mirroring `caseII_section91_factorEquations`, but feeding the **strengthened** squared form
`caseII_section91_squaredForm_withUnit` (real unit `η' = algebraMap u`, `u : (𝓞 K)ˣ`) into
`washington_factor_of_squared_pair`.  The factor unit is `η_a = η'^19 = algebraMap (u^19)`, so we
expose the integral unit `u_a = u^19` with `algebraMap u_a = η_a`. -/

/-- **[L5d — strengthened factor equations, integral unit]** The §9.1 conjugate-paired factor
equations at an adjacent root `η ≠ η₀`, **together with the integral-unit witness** `u_a : (𝓞 K)ˣ`
for the factor unit (`algebraMap u_a = η_a`).

Identical to `caseII_section91_factorEquations`, except the real unit `η_a` is exposed as
`algebraMap u_a` for `u_a = u^19` (`u` the integral unit of the strengthened squared form
`caseII_section91_squaredForm_withUnit`).  This is what makes the factor generators `ρ_a, ρ_b`
integral downstream (`caseII_factorGenerator_integral_of_unitInt`). -/
theorem caseII_section91_factorEquations_withUnit
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (η_a : (CyclotomicField 37 ℚ)ˣ) (ρ_a : CyclotomicField 37 ℚ)
      (u_a : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      complexConj (CyclotomicField 37 ℚ) (η_a : CyclotomicField 37 ℚ) =
          (η_a : CyclotomicField 37 ℚ) ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u_a : 𝓞 _) =
          (η_a : CyclotomicField 37 ℚ) ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
          (η_a : CyclotomicField 37 ℚ) * ρ_a ^ 37 ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36)) *
          (η_a : CyclotomicField 37 ℚ) *
          (complexConj (CyclotomicField 37 ℚ) ρ_a) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The strengthened squared form `X² = (algebraMap u)·W³⁷`, `u : (𝓞 K)ˣ`.
  obtain ⟨u, W, hu_real, hsq⟩ := caseII_section91_squaredForm_withUnit D η hη hcop
  -- Set `η' = Units.map algebraMap u`, so `(η' : K) = algebraMap u` and `σ η' = η'`.
  set η' : (CyclotomicField 37 ℚ)ˣ :=
    Units.map (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)).toMonoidHom u
    with hη'_def
  have hη'_val : (η' : CyclotomicField 37 ℚ) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) := by
    rw [hη'_def, Units.coe_map]; rfl
  have hη'real : complexConj (CyclotomicField 37 ℚ) (η' : CyclotomicField 37 ℚ) =
      (η' : CyclotomicField 37 ℚ) := by rw [hη'_val]; exact hu_real
  -- The squared form / conjugate squared form in `η'`-terms.
  have hsq' : caseII_section91_factor D η ^ 2 = (η' : CyclotomicField 37 ℚ) * W ^ 37 := by
    rw [hη'_val]; exact hsq
  have hsqConj : caseII_section91_factorConj D η ^ 2 =
      (η' : CyclotomicField 37 ℚ) * (complexConj (CyclotomicField 37 ℚ) W) ^ 37 := by
    have hc := congrArg (complexConj (CyclotomicField 37 ℚ)) hsq'
    rw [map_pow, caseII_section91_factor_complexConj, map_mul, hη'real, map_pow] at hc
    exact hc
  -- `washington_factor_of_squared_pair` (37 odd).
  obtain ⟨hXeq, hXconjEq⟩ := washington_factor_of_squared_pair
    (K := CyclotomicField 37 ℚ) (by decide : Odd 37)
    (caseII_section91_factor_ne_zero D η hη)
    (caseII_section91_factorConj_ne_zero D η hη)
    (caseII_section91_factor_complexConj D η)
    hsq' hsqConj
  -- `η_a = η'^19 = algebraMap (u^19)`, `ρ_a = W^19·X⁻¹`, `u_a = u^19`.
  refine ⟨η' ^ ((37 + 1) / 2), W ^ ((37 + 1) / 2) * (caseII_section91_factor D η)⁻¹,
    u ^ ((37 + 1) / 2), washington_factorUnit_real hη'real, ?_, ?_, ?_⟩
  · -- `algebraMap (u^19) = η'^19`.
    simp only [Units.val_pow_eq_pow_val, map_pow, hη'_val]
  · -- `X = η_a·ρ_a³⁷` ⟹ clear `1-η`.
    have hden_ne : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))
        ≠ 0 := caseII_section91_one_sub_eta_ne_zero D η hη
    have hX : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (D.x + D.y * (η : 𝓞 _)) =
        ((η' ^ ((37 + 1) / 2) : (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) *
          (W ^ ((37 + 1) / 2) * (caseII_section91_factor D η)⁻¹) ^ 37 *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _)) := by
      have h := hXeq
      rw [caseII_section91_factor, div_eq_iff hden_ne] at h
      exact h
    rw [map_add, map_mul] at hX
    rw [map_sub, map_one] at hX
    linear_combination hX
  · -- `X̄ = η_a·(σρ_a)³⁷` ⟹ clear `1-η³⁶`.
    have hden_ne : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (1 - (η : 𝓞 _) ^ 36) ≠ 0 := caseII_section91_one_sub_etaPow_ne_zero D η hη
    have hXc : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (D.x + D.y * ((η : 𝓞 _) ^ 36)) =
        ((η' ^ ((37 + 1) / 2) : (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) *
          (complexConj (CyclotomicField 37 ℚ)
            (W ^ ((37 + 1) / 2) * (caseII_section91_factor D η)⁻¹)) ^ 37 *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36) := by
      have h := hXconjEq
      rw [caseII_section91_factorConj, div_eq_iff hden_ne] at h
      exact h
    rw [map_add, map_mul] at hXc
    rw [map_sub, map_one] at hXc
    linear_combination hXc

/-- **[L5d — strengthened factor equations at `ζ`, `ζ²`, with integral units]** The two
positive factor equations at the roots `ζ`, `ζ²` (the capstone's `ηA = ζ`, `ηB = ζ²` shape),
**with the integral-unit witnesses** `u_a, u_b : (𝓞 K)ˣ` for the factor units.

This is the strengthened L2 the clean descent step consumes: it supplies, beyond the real factor
units `η_a, η_b` and generators `ρ_a, ρ_b`, the integral units `u_a, u_b` (`algebraMap u_a = η_a`,
`algebraMap u_b = η_b`).  Mirrors `caseII_section91_factorEquations_etaOne_etaTwo` (positive
equations only). -/
theorem caseII_section91_factorEquations_etaOne_etaTwo_withUnits
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
      (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) ∧
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
          (ηa : CyclotomicField 37 ℚ) ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
          (ηb : CyclotomicField 37 ℚ) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  obtain ⟨ηa, ρa, ua, hηa_real, hua, hfa_pos, _⟩ :=
    caseII_section91_factorEquations_withUnit D D.etaOne
      D.toCaseIIData37.etaOne_ne_etaZero hcop
  obtain ⟨ηb, ρb, ub, hηb_real, hub, hfb_pos, _⟩ :=
    caseII_section91_factorEquations_withUnit D D.etaTwo
      D.toCaseIIData37.etaTwo_ne_etaZero hcop
  have hηOne : (D.etaOne : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger :=
    caseII_etaOne_coe_eq_zeta D hp
  have hηTwo : (D.etaTwo : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 := by
    rw [caseII_etaTwo_coe_eq_zeta_sq D hp, pow_two]
  refine ⟨ηa, ηb, ρa, ρb, ua, ub, hηa_real, hηb_real, hua, hub, ?_, ?_⟩
  · rw [← hηOne]; exact hfa_pos
  · rw [← hηTwo]; exact hfb_pos

/-! ## 4. The `𝔭`-coprimality `(ζ−1) ∤ ρ_b` of the factor generator, and `(ζ−1) ∤ θ`

From the **sharp** non-anchor valuation `v_𝔭(x+yη) = 1` (`(ζ−1)² ∤ (x+yη)`,
`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root`) and the integral factor equation
`x+yη = (1−η)·u_a·r_a³⁷`, the factor generator `r_a` is `𝔭`-coprime: `(ζ−1) ∤ r_a`.  Hence the
conjugate-norm block `θ = −ρ_bσρ_b` is `𝔭`-coprime: `(ζ−1) ∤ θ` (both `r_b` and its conjugate are,
and `σ` preserves the real prime `𝔭`). -/

/-- **[L5d — factor generator `𝔭`-coprime]** From the positive factor equation at `η ≠ η₀` with the
factor unit integral (`algebraMap u_a = η_a`) and `ρ_a = algebraMap r_a` integral, the integer
factor generator `r_a` satisfies `(ζ−1) ∤ r_a`.

The integer factor equation `x + y·η = (1−η)·u_a·r_a³⁷` (`algebraMap`-injectivity), with
`(1−η) ~ (ζ−1)` (both `𝔭`-uniformisers) and the sharp `(ζ−1)² ∤ (x+yη)`
(`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root`), forces `(ζ−1) ∤ r_a` (else `(ζ−1)² ∣ x+yη`). -/
theorem caseII_zeta_sub_one_not_dvd_factorGenerator
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (ηa : (CyclotomicField 37 ℚ)ˣ) (ρa : CyclotomicField 37 ℚ)
    (ua : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ra : 𝓞 (CyclotomicField 37 ℚ))
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hra : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ra = ρa)
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) :
    ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ra := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  -- The integer factor equation `x + y·η = (1−η)·u_a·r_a³⁷`.
  have hint : D.x + D.y * (η : 𝓞 (CyclotomicField 37 ℚ)) =
      (1 - (η : 𝓞 (CyclotomicField 37 ℚ))) * (ua : 𝓞 _) * ra ^ 37 := by
    apply hinj
    push_cast [map_add, map_mul, map_sub, map_one, map_pow, hua, hra]
    linear_combination hfa
  -- `(1−η) ~ (ζ−1)`: write `1−η = N·(ζ−1)` for a UNIT `N` (both are `𝔭`-uniformisers, `η ≠ η₀`).
  -- We only need: if `(ζ−1) ∣ r_a` then `(ζ−1)² ∣ x+yη`, contradicting the sharp valuation.
  intro hdvd
  refine caseII_zeta_sub_one_sq_not_dvd_x_add_y_root D hp η hη ?_
  -- `(ζ−1) ∣ (1−η)` (associated), so `(ζ−1)² ∣ (1−η)·(ζ−1) ∣ (1−η)·u_a·r_a³⁷ = x+yη`.
  obtain ⟨k, hk⟩ := hdvd
  -- `(1 − η) = (η − 1)·(−1)`, and `(η−1) ~ (ζ−1)`: `(ζ−1) ∣ (1−η)`.
  obtain ⟨N, hN⟩ : (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      (1 - (η : 𝓞 (CyclotomicField 37 ℚ))) := by
    have hmem_eta : (η : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) := η.2
    have hmem_one : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
      one_mem_nthRootsFinset (by norm_num)
    have hne : (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ (1 : 𝓞 (CyclotomicField 37 ℚ)) := by
      have h1 : (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) :=
        fun h ↦ hη (Subtype.ext h)
      rwa [caseII_etaZero_eq_one D hp] at h1
    have hpair :=
      D.hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        (by decide : Nat.Prime 37) hmem_eta hmem_one hne
    have hassoc : Associated (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))
        (1 - (η : 𝓞 (CyclotomicField 37 ℚ))) := by
      refine hpair.trans ⟨-1, ?_⟩
      rw [Units.val_neg, Units.val_one]; ring
    exact hassoc.dvd
  -- `x+yη = (1−η)·u_a·r_a³⁷ = (N·(ζ−1))·u_a·((ζ−1)·k)³⁷`, divisible by `(ζ−1)²`.
  exact ⟨N * (ua : 𝓞 _) * (D.hζ.toInteger - 1) ^ 36 * k ^ 37, by
    rw [hint, hN, hk]; ring⟩

/-- **[L5d — `σ` preserves `𝔭`-coprimality]** `(ζ−1) ∤ w ⟹ (ζ−1) ∤ σ_int w` (`σ` the integer
complex conjugation): `σ_int(ζ−1) = ζ³⁶−1 ~ (ζ−1)`, and `σ_int` is a ring automorphism, so
`(ζ−1) ∣ σ_int w ⟹ σ_int(ζ−1) ∣ w ⟹ (ζ−1) ∣ w`. -/
theorem caseII_zeta_sub_one_not_dvd_complexConj
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {w : 𝓞 (CyclotomicField 37 ℚ)} (hw : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ w) :
    ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set σ := NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) with hσ
  have h37 : (D.hζ.toInteger : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 = 1 :=
    D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  -- `σ(ζ−1) = ζ³⁶−1`, `Associated (ζ³⁶−1) (ζ−1)` via the unit `-ζ`.
  have hσζ : σ (D.hζ.toInteger - 1) = D.hζ.toInteger ^ 36 - 1 := by
    rw [hσ, map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity h37]
  have hassoc : Associated (D.hζ.toInteger ^ 36 - 1 : 𝓞 (CyclotomicField 37 ℚ))
      (D.hζ.toInteger - 1) :=
    ⟨⟨-D.hζ.toInteger, -(D.hζ.toInteger ^ 36), by linear_combination h37,
        by linear_combination h37⟩, by linear_combination -h37⟩
  intro hdvd
  apply hw
  -- apply `σ` to `(ζ−1) ∣ σ w`: `σ(ζ−1) ∣ σ(σ w) = w`.
  have hσσ : σ (σ w) = w := by rw [hσ]; apply RingOfIntegers.ext; simp
  have hdvd0 : σ (D.hζ.toInteger - 1) ∣ σ (σ w) := map_dvd σ hdvd
  rw [hσσ, hσζ] at hdvd0
  exact (hassoc.dvd_iff_dvd_left).mp hdvd0

/-- **[L5d — `(ζ−1) ∤ θ`]** The conjugate-norm block `θ` (`algebraMap θ = −ρ_bσρ_b`) is
`𝔭`-coprime: `(zeta_spec−1) ∤ θ`.

From `(D.hζ−1) ∤ r_b` (`caseII_zeta_sub_one_not_dvd_factorGenerator`, `ρ_b = algebraMap r_b`) and
`(D.hζ−1) ∤ σ_int r_b` (`caseII_zeta_sub_one_not_dvd_complexConj`), the integer `θ = −r_b·σ_int r_b`
is `𝔭`-coprime; bridge `D.hζ−1 ~ zeta_spec−1` to land in the `zeta_spec`-form. -/
theorem caseII_zeta_sub_one_not_dvd_theta
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (ηb : (CyclotomicField 37 ℚ)ˣ) (ρb : CyclotomicField 37 ℚ)
    (ub : (𝓞 (CyclotomicField 37 ℚ))ˣ) (rb : 𝓞 (CyclotomicField 37 ℚ))
    (θ : 𝓞 (CyclotomicField 37 ℚ))
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hrb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) rb = ρb)
    (hθ : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
      -(ρb * complexConj (CyclotomicField 37 ℚ) ρb))
    (hfb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) :
    ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  set σ := NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) with hσ
  -- `θ = −r_b·σ_int r_b` (integer form): `algebraMap θ = −ρ_bσρ_b = algebraMap(−r_b·σ_int r_b)`.
  have hσrb_coe : complexConj (CyclotomicField 37 ℚ)
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) rb) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (σ rb) := by
    rw [hσ]; exact (coe_ringOfIntegersComplexConj (K := CyclotomicField 37 ℚ) rb).symm
  have hθ_int : θ = -(rb * σ rb) := by
    apply hinj
    rw [hθ, map_neg, map_mul, ← hrb, hσrb_coe]
  -- `etaTwo = ζ²`; the factor eqn at `ζ²` gives `(D.hζ−1) ∤ r_b`.
  -- Use `caseII_zeta_sub_one_not_dvd_factorGenerator` at `η = etaTwo`.
  have hηTwo : (D.etaTwo : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 := by
    rw [caseII_etaTwo_coe_eq_zeta_sq D hp, pow_two]
  have hfb' : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.etaTwo : 𝓞 _) *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.etaTwo : 𝓞 _)) *
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37 := by rw [hηTwo]; exact hfb
  have hrb_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ rb :=
    caseII_zeta_sub_one_not_dvd_factorGenerator D D.etaTwo
      D.toCaseIIData37.etaTwo_ne_etaZero ηb ρb ub rb hub hrb hfb'
  have hσrb_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ σ rb :=
    caseII_zeta_sub_one_not_dvd_complexConj D hrb_cop
  -- `(D.hζ−1) ∤ θ = −r_b·σ_int r_b` (prime, doesn't divide either factor).
  have hθ_cop_dζ : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ θ := by
    rw [hθ_int]
    have hprime : Prime (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) :=
      D.hζ.zeta_sub_one_prime'
    intro hdvd
    rw [dvd_neg] at hdvd
    rcases hprime.dvd_mul.mp hdvd with h | h
    · exact hrb_cop h
    · exact hσrb_cop h
  -- Bridge `D.hζ−1 ~ zeta_spec−1`.
  have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec D
  intro hdvd
  exact hθ_cop_dζ ((hassoc.dvd_iff_dvd_left).mpr hdvd)

/-! ## 5. The CLEAN residual `CaseIIWashingtonCaseII37` (real Assumption II + `ℓ`-propagation only)

The final R2 residual.  Receives the proven L2 factor outputs (`η_a, η_b, ρ_a, ρ_b`) and the proven
L1 anchor data (`e, u₀, ρ₀`, anchor equation), and supplies ONLY:
* **real Assumption II** `η_a = v³⁷·η_b` (`v : Kˣ` real) — the Kummer–Furtwängler unit-power step;
* the aux-prime **Lemma-9.6/9.7 `ℓ`-propagation**: `ρ₀² ∈ 𝔩`, and (conditional, no integer-witness
  existence) `ω ∉ 𝔩`, `θ ∉ 𝔩` for the conjugate-norm blocks.

It carries NO integer witnesses, NO `δ'`, NO descended equation, NO sharp `𝔭`-geometry, and NO
integral-unit witnesses — all derived (L1 anchor, strengthened L2 factor units, integral-closure
integer witnesses, proven sharp root-ideal arithmetic). -/

open scoped Classical in
/-- **[T-R2-L5d — THE CLEAN CASE-II RESIDUAL] real Assumption II + aux-prime `ℓ`-propagation** (a
`def … : Prop`, **not** an axiom).

For a real `ℓ ∣ z` datum `D` with coprime Fermat variables, **every** choice of the proven L2 factor
outputs `η_a, η_b : Kˣ` (real), `ρ_a, ρ_b : K`, and the proven L1 anchor data (`e ≥ 1`, `u₀`, `ρ₀`,
anchor equation), there is a **real** unit `v : Kˣ` with `η_a = v³⁷·η_b` (real Assumption II) such
that the conjugate-norm blocks obey the aux-prime `ℓ`-propagation:
`ρ₀² ∈ 𝔩`; and `ω ∉ 𝔩` for every integer witness `ω` of `v²ρ_aσρ_a`; `θ ∉ 𝔩` for every integer
witness `θ` of `−ρ_bσρ_b`. -/
def CaseIIWashingtonCaseII37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
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
    ∀ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 →
    ∃ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
          (v : CyclotomicField 37 ℚ) ∧
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb ∧
      ρ0 ^ 2 ∈ lv149 ∧
      (∀ ω : 𝓞 (CyclotomicField 37 ℚ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
            (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) →
        ω ∉ lv149) ∧
      (∀ θ : 𝓞 (CyclotomicField 37 ℚ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
            -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) →
        θ ∉ lv149)

/-! ## 6. The `p`-content extraction data WITH integral-unit witnesses, from the clean residual

`CaseIISection91PContentExtractionDataWithUnits37` is the `p`-content extraction data
`CaseIISection91PContentExtractionData37` with the **integral-unit witnesses** `u_a, u_b` (and their
`algebraMap` specs) added to the `∀`-antecedent — supplied by the strengthened producer
`caseII_section91_factorEquations_etaOne_etaTwo_withUnits` at the descent step.  From the clean
residual we DERIVE its full output: the integer witnesses, `δ'`, the sharp invariants, the
anchor-support, and the `ℓ`-membership. -/

/-- **[T-R2-L5d — `p`-content extraction data with integral units]** (a `def … : Prop`).
Identical to `CaseIISection91PContentExtractionData37`, but the `∀`-antecedent additionally receives
the integral-unit witnesses `u_a, u_b : (𝓞 K)ˣ` for the factor units. -/
def CaseIISection91PContentExtractionDataWithUnits37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
      (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) →
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
          (ηa : CyclotomicField 37 ℚ) →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
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
      ∃ (e k : ℕ) (η0 u : (CyclotomicField 37 ℚ)ˣ) (ρ0 : CyclotomicField 37 ℚ)
        (ω θ z' : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        1 ≤ e ∧ 1 ≤ k ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
          (η0 : CyclotomicField 37 ℚ) *
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
              ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37 ∧
        (ηa : (CyclotomicField 37 ℚ)ˣ) = u ^ 37 * ηb ∧
        complexConj (CyclotomicField 37 ℚ) (η0 : CyclotomicField 37 ℚ) =
          (η0 : CyclotomicField 37 ℚ) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (u : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) z' = ρ0 ^ 2 ∧
        (∀ δ : (CyclotomicField 37 ℚ)ˣ,
          complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
              (δ : CyclotomicField 37 ℚ) →
          ((u : CyclotomicField 37 ℚ) ^ 2 *
                (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
              (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
            (δ : CyclotomicField 37 ℚ) *
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                  (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
              (ρ0 ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
        (∃ c : 𝓞 (CyclotomicField 37 ℚ),
          ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
              ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
            ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) ∧
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k ∧
        -- the **integer descended Fermat equation** in `(1-ζ)(1-ζ³⁶)`-form (the §9.1 output,
        -- supplied directly — derived from the integral-unit conjugate-norm reassembly):
        ω ^ 37 + θ ^ 37 =
          (δ' : 𝓞 (CyclotomicField 37 ℚ)) *
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ (2 * e - 1) *
            z' ^ 37 ∧
        z' ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149 ∧
        ∃ m'' : ℕ, 2 * (2 * e - 1) = 37 * (m'' + 1)

set_option maxHeartbeats 1600000 in
-- The bumped `maxHeartbeats` is needed because `intro` must unfold the very large
-- `CaseIISection91PContentExtractionDataWithUnits37` def (a long `∀`/`→`/`∃` chain over the §9.1
-- datum) and the final `refine` reassembles the equally large extraction conclusion (24 conjuncts);
-- the `whnf` of these big `def … : Prop`s exceeds the default.
/-- **[T-R2-L5d — THE CLEAN RESIDUAL DISCHARGES THE WITH-UNITS EXTRACTION DATA]** (proven,
axiom-clean): `CaseIIWashingtonCaseII37 → CaseIISection91PContentExtractionDataWithUnits37`.

Given the integral-unit witnesses `u_a, u_b` (received), L1 is applied internally
(`caseII_anchor_real_rho0_genuineUnit`) for the anchor data + `(ρ₀) = B₀`, the clean residual
supplies real Assumption II `v` + the aux-prime `ℓ`-propagation, and the integer witnesses `ω, θ`,
the σ-fixed unit `δ'`, the descended equation, the sharp invariants `hxy'`/`hdenom'`, the
`𝔭`-coprimalities, the anchor-support `(z') = 𝔞₀²`, and the `p`-content-of-output condition are all
DERIVED. -/
theorem caseIISection91PContentExtractionDataWithUnits37_of_caseII
    (h_clean : CaseIIWashingtonCaseII37) :
    CaseIISection91PContentExtractionDataWithUnits37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D hcop ηa ηb ρa ρb ua ub hηa hηb hua hub hfa hfb
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  -- L1 (genuine integral unit): the anchor, `(ρ₀) = B₀`, `u₀` real.
  obtain ⟨e, u0, ρ0, he, hρ0_real, hρ0_span, hu0_real, hanchor⟩ :=
    caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
  -- The clean residual: real `v` + `ℓ`-propagation, fed L2 outputs + L1 anchor data.
  obtain ⟨v, hv_real, hII, hz'_mem, hω_notMem_cond, hθ_notMem_cond⟩ :=
    h_clean D hcop ηa ηb ρa ρb hηa hηb hfa hfb e u0 ρ0 he hanchor
  -- The integer descended equation: ω, θ, δ', reality, equation (from u_a, u_b, v integral).
  have hbig : CaseIIIntDescOutput37 D.toRealCaseIIData37 e ρ0 v ρa ρb :=
    caseII_integer_descended_equation_of_unitInt D.toRealCaseIIData37 e he u0 ρ0 hanchor ηa ηb v
      ρa ρb ua ub hua hub hηa hηb hfa hfb hv_real hII
  rw [CaseIIIntDescOutput37] at hbig
  obtain ⟨ω, θ, δ', hω, hθ, hω_real, hθ_real, hint_eq⟩ := hbig
  -- `(ζ−1) ∤ ρ₀²` from `(ρ₀) = B₀` (`𝔭`-coprime anchor), in `D.hζ`- and `zeta_spec`-terms.
  have hz'_cop_dζ : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ρ0 ^ 2 := by
    have hnot : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({ρ0 ^ 2} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [← Ideal.span_singleton_pow, hρ0_span]
      intro hdvd
      exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz
        ((Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ ρ0 ^ 2 := by
    have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec D.toRealCaseIIData37
    intro hdvd; exact hz'_cop_dζ ((hassoc.dvd_iff_dvd_left).mpr hdvd)
  -- `(ζ−1) ∤ θ` (conjugate-norm block `𝔭`-coprime).
  obtain ⟨rb, hrb⟩ := caseII_factorGenerator_integral_of_unitInt D.toRealCaseIIData37
    ⟨D.hζ.toInteger ^ 2, (mem_nthRootsFinset (by norm_num) _).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, D.hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow])⟩ (by
      intro h
      have h2 : (D.hζ.toInteger ^ 2 : 𝓞 (CyclotomicField 37 ℚ)) =
          (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) := by
        have := Subtype.ext_iff.mp h; exact this
      rw [caseII_etaZero_eq_one D.toRealCaseIIData37 hp] at h2
      exact D.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt
        (by omega) (by decide : 2 < 37) h2)
    ηb ρb ub hub (by
      rw [show ((⟨D.hζ.toInteger ^ 2, _⟩ :
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
          𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 from rfl]; exact hfb)
  have hθ_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ :=
    caseII_zeta_sub_one_not_dvd_theta D.toRealCaseIIData37 ηb ρb ub rb θ hub hrb hθ hfb
  -- `algebraMap (ρ₀²) = (algebraMap ρ₀)²` (the `z'`-spec; `z' = ρ₀²` integer).
  have hz'_spec : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ρ0 ^ 2) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 2 := map_pow _ _ _
  -- The anchor-exponent identity `2e = 37m+1`, and the sharp invariants `hxy'`, `hdenom'`.
  have h2e : 2 * e = 37 * m + 1 :=
    caseII_anchor_exponent_eq D.toRealCaseIIData37 hp
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor hz'_spec hz'_cop_dζ
  obtain ⟨hxy', hdenom'⟩ :=
    caseII_descended_hxy_hdenom (m := m) (D.toCaseIIData37.one_le_m) h2e hint_eq hω_real hθ_real
      hθ_cop hz'_cop
  -- The anchor-support `(z') = 𝔞₀²` (`k = 2`).
  have hz'_span2 : Ideal.span ({ρ0 ^ 2} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ 2 := by
    rw [← Ideal.span_singleton_pow, hρ0_span]
  -- The `p`-content-of-output condition `2·(2e−1) = 37·((2m−1)+1)`.
  have hcontent : ∃ m'' : ℕ, 2 * (2 * e - 1) = 37 * (m'' + 1) := by
    refine ⟨2 * m - 1, ?_⟩
    have hcon := caseII_descended_content_eq D.toRealCaseIIData37 hp
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor hz'_spec hz'_cop_dζ
    rw [hcon]; have := D.toCaseIIData37.one_le_m; congr 1; omega
  -- `η₀ = algebraMap u₀` as a `Kˣ`-unit, ρ₀ promoted to `K`, and the `δ'`-clause derivation.
  refine ⟨e, 2, (IsUnit.map (algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ)).toMonoidHom u0.isUnit).unit, v,
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0, ω, θ, ρ0 ^ 2, δ',
    he, by norm_num, ?_, hII, ?_, hω, hθ, hz'_spec, ?_, hω_real, hθ_real, hθ_cop,
    hxy', hdenom', hz'_span2, hint_eq, hz'_mem, hω_notMem_cond ω hω, hθ_notMem_cond θ hθ,
    hcontent⟩
  · -- anchor equation with `η₀ = algebraMap u₀`, ρ₀ = algebraMap ρ₀.
    rw [IsUnit.unit_spec]; exact hanchor
  · -- reality of `η₀ = algebraMap u₀`.
    rw [IsUnit.unit_spec]
    change complexConj (CyclotomicField 37 ℚ)
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _)) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _)
    rw [← coe_ringOfIntegersComplexConj (K := CyclotomicField 37 ℚ), hu0_real]
  · -- the `δ'`-clause (the σ-fixed-unit characterisation), via injectivity + cancellation.
    intro δ _ hδ_eq
    have hLHS : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ω ^ 37 + θ ^ 37) =
        ((v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
          (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 := by
      rw [map_add, map_pow, map_pow, hω, hθ]
    have hRHS := congrArg (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) hint_eq
    rw [hLHS, map_mul, map_mul, map_pow, map_pow] at hRHS
    have hΛ_ne : (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, map_eq_zero_iff _ hinj]
      refine mul_ne_zero (sub_ne_zero.mpr fun h ↦ ?_) (sub_ne_zero.mpr fun h ↦ ?_)
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
    have hcancel := hδ_eq.symm.trans hRHS
    exact mul_right_cancel₀ hΛ_ne (mul_right_cancel₀ hX_ne hcancel)

/-! ## 7. The clean `p`-content descent step, the well-founded closure, and the FLT37 endpoint

The descent step runs the **strengthened** producer
`caseII_section91_factorEquations_etaOne_etaTwo_withUnits` (supplying `u_a, u_b`) and applies the
with-units extraction data; the well-founded factor-count minimisation and the FLT37 endpoint then
follow as in the existing chain, but on the **clean residual**. -/

set_option maxRecDepth 4000 in
/-- **[T-R2-L5d — the clean `p`-content descent step]** (proven, axiom-clean *given* the with-units
extraction data + coprimality): the combined `ℓ ∣ z` descent step at content `37·(m+1)` with
`p`-content output, running the strengthened L2 producer (so the integral-unit witnesses `u_a, u_b`
are supplied, not carried). -/
theorem freeContentCaseIIDvdZData37_pContent_descend_withUnits
    (h_data : CaseIISection91PContentExtractionDataWithUnits37)
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1)))
    (hcop : IsCoprime
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
        Set (𝓞 (CyclotomicField 37 ℚ)))))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (m' : ℕ) (D' : FreeContentCaseIIDvdZData37 (37 * (m' + 1))),
      caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set Dr := freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37 with hDr
  let Drz : RealCaseIIDvdZData37 m :=
    { toRealCaseIIData37 := Dr, z_mem := D.z_mem, x_notMem := D.x_notMem, y_notMem := D.y_notMem }
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical Dr Dr.etaOne (caseII_correctionUnit Dr.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← caseIIFree_correctedRadical_eq_real D.toFreeContentCaseIIData37]; exact hnonterm
  -- The STRENGTHENED factor equations at `ζ`, `ζ²`, with integral units `u_a, u_b`.
  obtain ⟨ηa, ηb, ρa, ρb, ua, ub, hηa_real, hηb_real, hua, hub, hfa_pos, hfb_pos⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo_withUnits Dr hcop
  -- The with-units extraction data: §9.1 outputs + integer equation + `ℓ`-propagation + the
  -- `p`-content condition.  (The `δ'`-clause is unused here — the equation is supplied direct.)
  obtain ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      _hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hint_eq, hz'_mem, hω_notMem,
      hθ_notMem, hpc⟩ :=
    h_data Drz hcop ηa ηb ρa ρb ua ub hηa_real hηb_real hua hub hfa_pos hfb_pos
  -- `¬ (zeta_spec − 1) ∣ z'`.
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z' := by
    have hnot : ¬ Ideal.span ({((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 :
        𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec Dr
      rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm, hz'_span]; intro hdvd
      exact not_p_div_a_zero hp Dr.hζ Dr.equation Dr.hy Dr.hz
        ((Ideal.prime_span_singleton_iff.mpr Dr.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  -- **The descended content is `p`-content** (the carried sharp non-`p`-content-gap condition).
  obtain ⟨m'', hcontent⟩ := hpc
  -- Build the descended datum at the *explicit* content `2·(2e−1)` from the integer equation.
  obtain ⟨Dnew, hDnew_x, hDnew_y, hDnew_z⟩ :=
    freeContentCaseIIData37_of_descended_equation_xyz_explicit
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) he
      hint_eq hω_real hθ_real hθ_cop hz'_cop hxy' hdenom'
  -- Package as a combined datum at content `2·(2e−1)`.
  let Dcomb0 : FreeContentCaseIIDvdZData37 (2 * (2 * e - 1)) :=
    { toFreeContentCaseIIData37 := Dnew,
      z_mem := by rw [hDnew_z]; exact hz'_mem,
      x_notMem := by rw [hDnew_x]; exact hω_notMem,
      y_notMem := by rw [hDnew_y]; exact hθ_notMem }
  -- the strict factor drop at content `2·(2e−1)`.
  have hdrop : caseIIFreeDvdZFactorCount Dcomb0 < caseIIFreeDvdZFactorCount D := by
    change caseIIFreeFactorCount Dnew < caseIIFreeFactorCount D.toFreeContentCaseIIData37
    rw [caseIIFreeFactorCount, hDnew_z, caseIIFreeFactorCount_toReal D.toFreeContentCaseIIData37]
    have hsupp := caseII_anchorSupported_of_span_eq_anchorPow Dr hk hz'_span
    exact caseIIZFactorCount_strict_of_anchor_supported Dr hp hnonterm' hsupp
  -- transport across `2·(2e−1) = 37·(m''+1)` (the carried `p`-content condition; `m' = m''`).
  refine ⟨m'', ?_⟩
  rw [show 37 * (m'' + 1) = 2 * (2 * e - 1) from hcontent.symm]
  exact ⟨Dcomb0, hdrop⟩

/-- **No `p`-content combined `ℓ ∣ z` datum exists, from the with-units extraction data** (proven,
axiom-clean — no non-`p`-content gap).  Well-founded minimality on `caseIIFreeDvdZFactorCount`, over
the `p`-content combined data only, using the clean `p`-content descent step. -/
theorem no_pContent_freeContentCaseIIDvdZData37_withUnits
    (h_data : CaseIISection91PContentExtractionDataWithUnits37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ¬ ∃ m : ℕ, Nonempty (FreeContentCaseIIDvdZData37 (37 * (m + 1))) := by
  classical
  rintro ⟨m₀, ⟨D₀⟩⟩
  let P : ℕ → Prop := fun k ↦
    ∃ (m : ℕ) (E : FreeContentCaseIIDvdZData37 (37 * (m + 1))), caseIIFreeDvdZFactorCount E = k
  have hP : ∃ k, P k := ⟨_, m₀, D₀, rfl⟩
  obtain ⟨mmin, Dmin, hk⟩ := Nat.find_spec hP
  by_cases hunit : ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      Dmin.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))
  · obtain ⟨αU, hαU⟩ := hunit
    exact caseIIFreeFirstLayer_false Dmin.toFreeContentCaseIIData37 αU hαU
  · obtain ⟨m', D', hlt⟩ :=
      freeContentCaseIIDvdZData37_pContent_descend_withUnits h_data Dmin (h_cop Dmin) hunit
    rw [hk] at hlt
    exact Nat.find_min hP hlt ⟨m', D', rfl⟩

/-- **No `ℓ ∣ z`-restricted real Case-II datum exists, from the with-units descent** (proven,
axiom-clean). -/
theorem no_realCaseIIDvdZData37_of_withUnitsDescent
    (h_data : CaseIISection91PContentExtractionDataWithUnits37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  rintro ⟨m, ⟨D⟩⟩
  exact no_pContent_freeContentCaseIIDvdZData37_withUnits h_data h_cop
    ⟨m, ⟨FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37 D⟩⟩

/-! ## 8. The clean Case-II bridge and the FLT37 endpoint, on the CLEAN residual -/

/-- **The public Case-II bridge from the clean residual** (proven, axiom-clean *given* the named
inputs + Washington Lemma 9.6).  `CaseIIBridge 37 K 32` from the with-units `p`-content extraction
data (discharged by the clean residual `CaseIIWashingtonCaseII37`), the per-datum coprimality, and
Washington Lemma 9.6. -/
theorem caseIIBridge_thirtyseven_of_caseII_withUnits
    (h_data : CaseIISection91PContentExtractionDataWithUnits37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  exact (no_realCaseIIDvdZData37_of_withUnitsDescent h_data h_cop)
    (exists_realCaseIIDvdZData37_of_caseII_int_solution hprod hgcd hcase hEq
      (h_lemma96 a b c hprod hgcd hcase hEq))

/-- **[T-R2-L5d — THE FINAL R2 GEOMETRY CLOSURE] Fermat's Last Theorem for `37`, on the clean
residual** (proven, axiom-clean *given* the named inputs + carried Kellner).

`FermatLastTheoremFor 37` from:
* `h_clean` (`CaseIIWashingtonCaseII37`): the **clean** Case-II residual — **real Assumption II**
  `η_a = v³⁷·η_b` (`v` real) + the aux-prime **Lemma-9.6/9.7 `ℓ`-propagation** (`ρ₀² ∈ 𝔩`, `ω ∉ 𝔩`,
  `θ ∉ 𝔩`).  The **full §9.1 geometry is PROVEN**, not carried: L1 (anchor) and the strengthened L2
  (factor equations **with integral units**) are applied internally, and the integer
  witnesses `ω, θ`, the σ-fixed unit `δ'`, the descended Fermat equation, the sharp `𝔭`-invariants,
  the `𝔭`-coprimalities `(ζ−1) ∤ θ, ρ₀²`, and the anchor-support `(z') = 𝔞₀²` are all DERIVED;
* `h_cop`: the per-datum coprimality of the promoted Fermat variables (threaded — the universal is
  provably false);
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): the `ℓ ∣ ξ` domain non-emptiness;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

This is the final R2 geometry closure: FLT37 Case-II rests on the analytic **real Assumption II**,
the aux-prime **`ℓ`-membership**, **Kellner**, and the threaded **coprimality** only — the anchor
(L1) and factor equations (L2) are **fully consumed** (proven, supplied internally). -/
theorem fermatLastTheoremFor_thirtyseven_of_washington_caseII
    (h_clean : CaseIIWashingtonCaseII37)
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
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact BernoulliRegular.fermatLastTheoremFor_thirtyseven_of_remaining
    (BernoulliRegular.cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_caseII_withUnits
      (caseIISection91PContentExtractionDataWithUnits37_of_caseII h_clean) h_cop h_lemma96)

/-! ## 9. Non-vacuity of the clean residual (the antecedent is genuinely inhabited) -/

/-- **Non-vacuity of `CaseIIWashingtonCaseII37` (antecedent inhabited).**

The clean residual's antecedent — for a real `ℓ ∣ z` datum `D` with coprime Fermat variables, the
proven L2 factor outputs (`η_a, η_b : Kˣ` real, `ρ_a, ρ_b : K`) at `ζ, ζ²` **and** the proven L1
anchor data (`e ≥ 1`, `u₀`, `ρ₀`, anchor equation) — is genuinely inhabited: the factor outputs are
the **proven** strengthened L2 (`caseII_section91_factorEquations_etaOne_etaTwo_withUnits`, dropping
`u_a, u_b`) and the anchor data is the **proven** L1 (`caseII_anchor_real_rho0_genuineUnit`).
So the residual consumes inhabited input — its conclusion (real Assumption II + the aux-prime
`ℓ`-propagation) is the genuine remaining §9.1/Furtwängler content, not a vacuous hypothesis. -/
theorem caseIIWashingtonCaseII37_antecedent_inhabited
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    -- L2 factor outputs at `ζ`, `ζ²`:
    (∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) ∧
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37)) ∧
    -- L1 anchor data:
    (∃ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨ηa, ηb, ρa, ρb, _ua, _ub, hηa, hηb, _hua, _hub, hfa, hfb⟩ :=
      caseII_section91_factorEquations_etaOne_etaTwo_withUnits D.toRealCaseIIData37 hcop
    exact ⟨ηa, ηb, ρa, ρb, hηa, hηb, hfa, hfb⟩
  · obtain ⟨e, u0, ρ0, he, _, _, _, hanchor⟩ :=
      caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
    exact ⟨e, u0, ρ0, he, hanchor⟩

end BernoulliRegular.FLT37.Eichler

end

end
