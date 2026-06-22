import BernoulliRegular.FLT37.Eichler.CaseII.Section91.FactorRatioIsPthPower

/-!
# [FLT37-CASEII-R2] Washington §9.1 factor-equation producer (squared form ⟹ factor equations)

This file composes the three proven halves of Washington's §9.1 factor-equation extraction (GTM 83,
2nd ed., pp. 170–171) into the **factor equations** the capstone
`freeContentCaseIIData37_of_factorEquations` consumes:

* the **quotient half** `X/X̄ = β³⁷` — *proven* (`caseII_section91_factorRatio_isPthPower`,
  `CaseIISection91SquaredForm.lean`, Lemma 9.2 via the proven ideal-form Lemma 9.1 + Hilbert 94);
* the **product half** `X·X̄ = η'·γ³⁷` (`η'` a real unit, `γ ∈ K`) — Washington's B₀-style
  real-generator argument for the conjugate norm `N_{K/K⁺}(X) = X·X̄`, taken here as the named input
  `CaseIISection91ProductHalf37` (the *remaining* analytic content);
* the **squared-form → factor-equation algebra** — *proven, unconditional*
  (`washington_factor_of_squared_pair`, `CaseIISection91FactorExtraction.lean`).

Multiplying the quotient and product halves gives the **squared form**
```
X² = (X/X̄)·(X·X̄) = β³⁷·η'·γ³⁷ = η'·(βγ)³⁷,    η' a REAL unit,
```
and `washington_factor_of_squared_pair` turns it into the **conjugate-paired factor equations**
```
X = (ω+ζ^a θ)/(1-ζ^a) = η_a·ρ_a³⁷,    X̄ = (ω+ζ^{-a}θ)/(1-ζ^{-a}) = η_a·(σρ_a)³⁷,
```
with `η_a = (η')^{(p+1)/2}` a real unit and `ρ_a, σρ_a` conjugate generators.

Clearing the `(1-ζ^{±a})` denominators yields exactly the `hfa_pos`/`hfa_neg` shape of the capstone:
`x + ζ^a y = (1-ζ^a)·η_a·ρ_a³⁷`.

## Why the product half is genuinely the remaining content

The quotient `X/X̄` is **anti-fixed** (`σ(X/X̄) = (X/X̄)⁻¹`) and its pth-power-ness is the proven
Lemma 9.2 (Hilbert-94 on the anti-Kummer extension).  The product `X·X̄` is **real**; its
pth-power-times-real-unit form is Washington's B₀ argument: the σ-fixed `𝔭`-coprime ideal
`C = 𝔞(η)·𝔞(η³⁶)` descends to `K⁺` and `p∤h⁺` forces `C` principal with a *real* generator, whence
`X·X̄ = η'·γ³⁷`.  This is a *different* mechanism (real-subfield principalization, not Hilbert 94),
and it additionally needs the gcd `𝔪 = gcd((x),(y))` to be trivial (coprimality of `x, y`) so that
`(X·X̄) = C^p` is a perfect `p`-th power; we record both as the hypotheses of
`CaseIISection91ProductHalf37`.

## What this file proves (real, axiom-clean Lean — no `sorry`, no `axiom`)

* `CaseIISection91ProductHalf37` — the named product-half input (a `def … : Prop`, not an axiom).
* `caseII_section91_squaredForm` — the squared form `X² = η'·(βγ)³⁷` with real unit `η'`, from the
  proven quotient half and the product half.
* `caseII_section91_factorEquations` — **the conjugate-paired factor equations** at an adjacent root
  `η ≠ η₀`, in the cleared-denominator shape `x + algebraMap η·y = (1 - algebraMap η)·η_a·ρ_a³⁷` and
  its conjugate, from the squared form via `washington_factor_of_squared_pair`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 169–171.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The product half (named input) -/

/-- **[PRODUCT HALF] Washington's B₀ argument for the conjugate norm `X·X̄`** (a `def … : Prop`, NOT
an axiom).

For a real Case-II datum `D` and an adjacent root `η ≠ η₀`, with the gcd `𝔪 = gcd((x),(y))` trivial
(coprimality of the Fermat variables, `IsCoprime`), the conjugate norm of the adjacent factor
`X·X̄ = [(x+yη)/(1-η)]·[(x+yη³⁶)/(1-η³⁶)]` is a **real unit** times a `37`-th power:
```
X·X̄ = (η' : K)·γ³⁷,    η' : Kˣ with σ(η') = η',   γ : K.
```

This is the B₀ / real-subfield principalization half of the §9.1 squared form (Washington p. 170,
"by the same reasoning as B₀"): the σ-fixed `𝔭`-coprime ideal `C = 𝔞(η)·𝔞(η³⁶)` descends to `K⁺`,
and `¬ 37 ∣ h⁺` (proven `Sinnott.flt37_not_dvd_hPlus`) forces `C` principal with a *real* generator
`γ`, so `(X·X̄) = (γ³⁷)` and `X·X̄ = η'·γ³⁷` with `η'` real.  Coprimality `𝔪 = (1)` is what makes
`(X·X̄) = C³⁷` a perfect `37`-th power (else `(X·X̄) = 𝔪²·C³⁷` carries the square `𝔪²`).  These
are Washington's standing assumptions (the original FLT solution has coprime `x, y`).

It is a *genuine* implication, not vacuous: its hypothesis (coprimality + adjacency) is exactly
Washington's standing data, and its conclusion the real-unit-times-`p`-th-power form he derives. -/
def CaseIISection91ProductHalf37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
    η ≠ D.etaZero →
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∃ (η' : (CyclotomicField 37 ℚ)ˣ) (γ : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (η' : CyclotomicField 37 ℚ) =
          (η' : CyclotomicField 37 ℚ) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y * (η : 𝓞 _)) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (D.x + D.y * ((η : 𝓞 _) ^ 36)) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36)) =
        (η' : CyclotomicField 37 ℚ) * γ ^ 37

/-! ## 2. The adjacent factor `X` and its conjugate `X̄`, and their basic properties -/

/-- The adjacent factor `X = (x+yη)/(1-η) ∈ K`. -/
def caseII_section91_factor
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) : CyclotomicField 37 ℚ :=
  algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y * (η : 𝓞 _)) /
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))

/-- The conjugate factor `X̄ = (x+yη³⁶)/(1-η³⁶) ∈ K`. -/
def caseII_section91_factorConj
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) : CyclotomicField 37 ℚ :=
  algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y * ((η : 𝓞 _) ^ 36)) /
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36)

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- `η = 1` is excluded for an adjacent root `η ≠ η₀ = 1`. -/
theorem caseII_section91_eta_ne_one
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero) :
    (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro h1
  refine absurd hη (not_not.mpr (Subtype.ext ?_))
  rw [caseII_etaZero_eq_one D (by decide : (37 : ℕ) ≠ 2)]; exact h1

/-- `algebraMap (1 - η) ≠ 0`. -/
theorem caseII_section91_one_sub_eta_ne_zero
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero) :
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _)) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  intro h0
  exact caseII_section91_eta_ne_one D η hη (by linear_combination -h0)

/-- `algebraMap (1 - η³⁶) ≠ 0`. -/
theorem caseII_section91_one_sub_etaPow_ne_zero
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero) :
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36) ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 = 1 :=
    (mem_nthRootsFinset (by norm_num) _).mp η.2
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  intro h0
  have hη36 : (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 36 = 1 := by linear_combination -h0
  refine caseII_section91_eta_ne_one D η hη ?_
  have hps : (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
      (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 36 * (η : 𝓞 (CyclotomicField 37 ℚ)) := pow_succ _ _
  rw [h37, hη36, one_mul] at hps; exact hps.symm

/-- `X ≠ 0` (numerator `x+yη ≠ 0`). -/
theorem caseII_section91_factor_ne_zero
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero) :
    caseII_section91_factor D η ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [caseII_section91_factor]
  exact div_ne_zero (caseII_algebraMap_x_add_y_eta_ne_zero D (by decide : (37 : ℕ) ≠ 2) η)
    (caseII_section91_one_sub_eta_ne_zero D η hη)

/-- `X̄ ≠ 0` (numerator `x+yη³⁶ ≠ 0`). -/
theorem caseII_section91_factorConj_ne_zero
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero) :
    caseII_section91_factorConj D η ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [caseII_section91_factorConj]
  exact div_ne_zero (caseII_algebraMap_x_add_y_etaInv_ne_zero D (by decide : (37 : ℕ) ≠ 2) η)
    (caseII_section91_one_sub_etaPow_ne_zero D η hη)

/-- **`σX = X̄`** (the conjugate factor is the complex conjugate of `X`).  Over real `x, y`,
`σ(x+yη) = x+yη³⁶` and `σ(1-η) = 1-η³⁶`, so the ratio conjugates to `X̄`. -/
theorem caseII_section91_factor_complexConj
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
    complexConj (CyclotomicField 37 ℚ) (caseII_section91_factor D η) =
      caseII_section91_factorConj D η := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 = 1 :=
    (mem_nthRootsFinset (by norm_num) _).mp η.2
  have h36 : ((η : 𝓞 (CyclotomicField 37 ℚ)) ^ 36) ^ 37 = 1 := by
    rw [← pow_mul, show 36 * 37 = 37 * 36 from by norm_num, pow_mul, h37, one_pow]
  rw [caseII_section91_factor, caseII_section91_factorConj, map_div₀]
  -- `σ(x+yη) = x+yη³⁶`.
  have hnum : complexConj (CyclotomicField 37 ℚ)
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (D.x + D.y * (η : 𝓞 _))) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (D.x + D.y * ((η : 𝓞 _) ^ 36)) := by
    rw [← coe_ringOfIntegersComplexConj]
    congr 1
    have h := caseII_ringOfIntegersComplexConj_x_add_y_mul (K := CyclotomicField 37 ℚ)
      D.x_real D.y_real (η : 𝓞 _)
    rwa [caseII_ringOfIntegersComplexConj_root_of_unity h37] at h
  -- `σ(1-η) = 1-η³⁶`.
  have hden : complexConj (CyclotomicField 37 ℚ)
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36) := by
    rw [← coe_ringOfIntegersComplexConj]
    congr 1
    rw [map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity h37]
  rw [hnum, hden]

/-! ## 3. The squared form `X² = η'·(βγ)³⁷` (quotient half × product half) -/

/-- **[SQUARED FORM] `X² = η'·(βγ)³⁷` with `η'` a real unit** (Washington p. 170).

For a real Case-II datum `D`, adjacent root `η ≠ η₀`, and the coprimality `IsCoprime ((x)) ((y))`,
multiplying the **proven** quotient half `X/X̄ = β³⁷` (`caseII_section91_factorRatio_isPthPower`) by
the product half `X·X̄ = η'·γ³⁷` (`CaseIISection91ProductHalf37`) gives
```
X² = (X/X̄)·(X·X̄) = β³⁷·η'·γ³⁷ = (η' : K)·(β·γ)³⁷,
```
with `η' : Kˣ` a **real** unit (`σ η' = η'`).  This is the input to
`washington_factor_of_squared_pair`. -/
theorem caseII_section91_squaredForm
    (h_prod : CaseIISection91ProductHalf37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (η' : (CyclotomicField 37 ℚ)ˣ) (W : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (η' : CyclotomicField 37 ℚ) =
          (η' : CyclotomicField 37 ℚ) ∧
      caseII_section91_factor D η ^ 2 = (η' : CyclotomicField 37 ℚ) * W ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Proven quotient half: `X/X̄ = β³⁷`.
  obtain ⟨β, hβ⟩ := caseII_section91_factorRatio_isPthPower D η hη
  -- Product half: `X·X̄ = η'·γ³⁷`.
  obtain ⟨η', γ, hη'real, hprod⟩ := h_prod D η hη hcop
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
  refine ⟨η', β * γ, hη'real, ?_⟩
  -- `X² = (X/X̄)·(X·X̄) = β³⁷·(η'·γ³⁷) = η'·(βγ)³⁷`.
  have hXc_ne : caseII_section91_factorConj D η ≠ 0 := caseII_section91_factorConj_ne_zero D η hη
  have hsplit : caseII_section91_factor D η ^ 2 =
      (caseII_section91_factor D η / caseII_section91_factorConj D η) *
      (caseII_section91_factor D η * caseII_section91_factorConj D η) := by
    have hgen : ∀ a b : CyclotomicField 37 ℚ, b ≠ 0 → a ^ 2 = (a / b) * (a * b) := by
      intro a b hb; field_simp
    exact hgen _ _ hXc_ne
  rw [hsplit, hβ, hprod, mul_pow]; ring

/-! ## 4. The conjugate-paired factor equations (the capstone shape) -/

/-- **[FACTOR EQUATIONS] The conjugate-paired §9.1 factor equations at an adjacent root** (Wash.
p. 171).

For a real Case-II datum `D`, an adjacent root `η ≠ η₀`, and coprimality `IsCoprime ((x)) ((y))`,
there is a **real** unit `η_a : Kˣ` and a generator `ρ_a : K` with the two factor equations in
**cleared-denominator** form (the exact `hfa_pos`/`hfa_neg` shape of
`freeContentCaseIIData37_of_factorEquations`):
```
algebraMap x + algebraMap η · algebraMap y = (1 - algebraMap η)   · η_a · ρ_a³⁷,
algebraMap x + algebraMap η³⁶ · algebraMap y = (1 - algebraMap η³⁶) · η_a · (σρ_a)³⁷,
```
with `σ η_a = η_a` (`η_a = η'^{(p+1)/2}` real) and the conjugate generator `σρ_a` of `ρ_a`.

Proof: the squared form `X² = η'·W³⁷` (`caseII_section91_squaredForm`, real unit `η'`) and its
conjugate `X̄² = η'·(σW)³⁷` (from `σX = X̄`, `σ η' = η'`) feed `washington_factor_of_squared_pair`,
giving `X = η_a·ρ_a³⁷`, `X̄ = η_a·(σρ_a)³⁷` with `η_a = η'^{(p+1)/2}` real; multiplying by the
denominator `1 - algebraMap η` (resp. `1 - algebraMap η³⁶`) clears it.  The product half
`CaseIISection91ProductHalf37` is the only non-proven input. -/
theorem caseII_section91_factorEquations
    (h_prod : CaseIISection91ProductHalf37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (η_a : (CyclotomicField 37 ℚ)ˣ) (ρ_a : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (η_a : CyclotomicField 37 ℚ) =
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
  set K := CyclotomicField 37 ℚ with hK
  -- The squared form `X² = η'·W³⁷`, `η'` real.
  obtain ⟨η', W, hη'real, hsq⟩ := caseII_section91_squaredForm h_prod D η hη hcop
  -- The conjugate squared form `X̄² = η'·(σW)³⁷`.
  have hsqConj : caseII_section91_factorConj D η ^ 2 = (η' : K) * (complexConj K W) ^ 37 := by
    have hc := congrArg (complexConj K) hsq
    rw [map_pow, caseII_section91_factor_complexConj, map_mul, hη'real, map_pow] at hc
    exact hc
  -- `washington_factor_of_squared_pair` (37 odd).
  obtain ⟨hXeq, hXconjEq⟩ := washington_factor_of_squared_pair (K := K) (by decide : Odd 37)
    (caseII_section91_factor_ne_zero D η hη)
    (caseII_section91_factorConj_ne_zero D η hη)
    (caseII_section91_factor_complexConj D η)
    hsq hsqConj
  -- Name `η_a = η'^{(p+1)/2} = η'^19` (real) and `ρ_a = W^19·X⁻¹`.
  refine ⟨η' ^ ((37 + 1) / 2), W ^ ((37 + 1) / 2) * (caseII_section91_factor D η)⁻¹,
    washington_factorUnit_real hη'real, ?_, ?_⟩
  · -- `X = η_a·ρ_a³⁷` ⟹ clear `1-η`: `algebraMap(x+yη) = (1-η)·η_a·ρ_a³⁷`.
    have hden_ne : algebraMap (𝓞 K) K (1 - (η : 𝓞 _)) ≠ 0 :=
      caseII_section91_one_sub_eta_ne_zero D η hη
    -- `hXeq : X = η_a·ρ_a³⁷`; clear the denominator of `X = N/(1-η)`.
    have hX : algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 _)) =
        ((η' ^ ((37 + 1) / 2) : Kˣ) : K) *
          (W ^ ((37 + 1) / 2) * (caseII_section91_factor D η)⁻¹) ^ 37 *
          algebraMap (𝓞 K) K (1 - (η : 𝓞 _)) := by
      have h := hXeq
      rw [caseII_section91_factor, div_eq_iff hden_ne] at h
      exact h
    -- Goal: `algebraMap x + algebraMap η·algebraMap y = (1-algebraMap η)·η_a·ρ_a³⁷`.
    rw [map_add, map_mul] at hX
    rw [map_sub, map_one] at hX
    linear_combination hX
  · -- `X̄ = η_a·(σρ_a)³⁶` ⟹ clear `1-η³⁶`.
    have hden_ne : algebraMap (𝓞 K) K (1 - (η : 𝓞 _) ^ 36) ≠ 0 :=
      caseII_section91_one_sub_etaPow_ne_zero D η hη
    have hXc : algebraMap (𝓞 K) K (D.x + D.y * ((η : 𝓞 _) ^ 36)) =
        ((η' ^ ((37 + 1) / 2) : Kˣ) : K) *
          (complexConj K (W ^ ((37 + 1) / 2) * (caseII_section91_factor D η)⁻¹)) ^ 37 *
          algebraMap (𝓞 K) K (1 - (η : 𝓞 _) ^ 36) := by
      have h := hXconjEq
      rw [caseII_section91_factorConj, div_eq_iff hden_ne] at h
      exact h
    rw [map_add, map_mul] at hXc
    rw [map_sub, map_one] at hXc
    linear_combination hXc

/-! ## 5. Non-vacuity of the product half (it is a genuine implication, not degenerate) -/

/-- **The conjugate norm `X·X̄` is real** (`σ(X·X̄) = X·X̄`), certifying the `σ η' = η'` constraint of
`CaseIISection91ProductHalf37` is the *natural* shape — not an artificial restriction.

Since `σX = X̄` (`caseII_section91_factor_complexConj`), `σ(X·X̄) = X̄·X = X·X̄`.  So the product is
genuinely a real number, and its B₀-form `X·X̄ = η'·γ³⁷` with `η'` **real** is exactly the form a
real `𝔭`-coprime element whose ideal is a `37`-th power must take (the product-half conclusion is
*reachable*, not vacuous). -/
theorem caseII_section91_product_real
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
    complexConj (CyclotomicField 37 ℚ)
        (caseII_section91_factor D η * caseII_section91_factorConj D η) =
      caseII_section91_factor D η * caseII_section91_factorConj D η := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `σ(X·X̄) = σX·σX̄`.  `σX = X̄`, and `σX̄ = σσX = X`.
  rw [map_mul, caseII_section91_factor_complexConj]
  -- `σX̄ = X`: `X̄ = σX`, so `σX̄ = σσX = X` (involution).
  have hconjConj : complexConj (CyclotomicField 37 ℚ) (caseII_section91_factorConj D η) =
      caseII_section91_factor D η := by
    rw [← caseII_section91_factor_complexConj, complexConj_apply_apply]
  rw [hconjConj, mul_comm]

end BernoulliRegular.FLT37.Eichler

end

end
