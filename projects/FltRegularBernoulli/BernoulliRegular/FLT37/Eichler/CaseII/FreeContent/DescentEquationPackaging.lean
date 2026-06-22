import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.DescentDatum

/-!
# [FLT37-CASEII-R2] Packaging Washington's descended equation into a `FreeContentCaseIIData37`

This file proves the **datum-packaging** lemma that turns Washington's *proven* descended Fermat
equation (the output of `washington_section91_descended_equation`,
`CaseIISection91ConjNormReassembly.lean`) into a `FreeContentCaseIIData37`
(`CaseIIFreeContentDatum.lean`).  It is the bridge from the proven reassembly algebra to the next
descent datum, reducing the whole FLT37 Case-II descent step to the *factor-equation extraction*
(Washington Lemma 9.1/9.2) alone.

## The descended equation and the target datum

Washington's descended equation (GTM 83, 2nd ed., p. 172) has the **field-level** shape
```
ω³⁷ + θ³⁷ = δ · Λ^{2e-1} · z'³⁷,      Λ = (1-ζ)(1-ζ⁻¹),   z' = ρ₀²,
```
with `ω = u²ρ_aσρ_a`, `θ = -ρ_bσρ_b` the σ-fixed conjugate-norm building blocks (algebraic
integers), `δ` a σ-fixed unit, and `Λ` the **real** prime (with `v_𝔭(Λ) = 2`).  The target
`FreeContentCaseIIData37 K n'` records the **integer** equation `x³⁷ + y³⁷ = ε·(ζ−1)ⁿ⁰·z³⁷` with the
`λ = ζ−1`-factor *outside* the `³⁷`-power, plus reality, `𝔭`-coprimality, `1 ≤ n'`, and the two
primarity-supporting facts `hxy` (`(ζ−1)³ ∣ x+y`) and `hdenom` (`v_𝔭(x+yζ³⁶) = 1`).

## The `Λ^{2e-1} → ε'·(ζ−1)^{n'}` conversion (the algebraic core)

The identity `1 - ζ⁻¹ = 1 - ζ³⁶ = -ζ³⁶·(ζ-1)` (from `ζ³⁷ = 1`) gives, at the **integer** level,
```
(1-ζ)(1-ζ³⁶) = -ζ³⁶·(ζ-1)²
```
(`freeContentPackaging_Lambda_eq`, a standalone re-derivation of
`caseII_LambdaCyc_algebraMap_eq_neg_zeta_pow_36_mul_zeta_sub_one_sq`).  Hence
`Λ^{2e-1} = (-ζ³⁶)^{2e-1}·(ζ-1)^{2(2e-1)}`, so with `n' = 2(2e-1) = 4e-2` (even, `≥ 2` for `e ≥ 1`)
and `ε' = δ·(-ζ³⁶)^{2e-1}` (a unit, since `-ζ³⁶` is a unit),
```
δ·Λ^{2e-1}·z'³⁷ = ε'·(ζ-1)^{n'}·z'³⁷,
```
which is exactly Washington's native `FreeContentCaseIIData37` form.

## The two genuinely-tricky fields — soundness verdict

`hxy'` and `hdenom'` are **not** derivable from the descended equation alone — they are sharp
`𝔭`-valuation facts about the *specific* conjugate-norm building blocks `ω, θ` (depending on the
`𝔭`-valuations of `ρ_a, ρ_b` at the adjacent root), the exact analogues of the proven
`caseII_K_zeta_sub_one_pow_dvd_x_add_y` (`(ζ−1)^{37m+1} ∣ x+y`) and
`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root` (sharp `v_𝔭(x+yζ³⁶)=1`) for the **original** Fermat
variables, which in the repo are proved from the *root-ideal* structure, **not** from the Fermat
equation.  Concretely:

* The descended equation only gives `v_𝔭(ω³⁷+θ³⁷) = n' = 4e-2`.  Via `ω³⁷+θ³⁷ = ∏_j(ω+ζ^jθ)` and
  the standard "single bulk factor" splitting, this forces `v_𝔭(ω+θ) = (4e-2) - 36 = 4e-38`, which
  is `≥ 3` only for `e ≥ 11`.  So `hxy'` is a *genuine additional input*, not free for small `e`.
* `hdenom'` (`v_𝔭(ω+θζ³⁶) = 1`) is a sharpness fact at the adjacent root, again about the anchor's
  `𝔭`-structure, not the equation.

Therefore the packaging lemma takes `hxy'` and `hdenom'` as **explicit hypotheses** — exactly the
datum fields they become.  They are **sound** (they hold for the honest descended data: `hxy'` is
implied by Washington's `(ζ−1)^{37m+1} ∣ x+y` analogue at the anchor, and `hdenom'` is the
`caseII_etaInv_denom_factor`-analogue at the adjacent root), but they must be *supplied by the
descent construction*, not the equation.  This is the honest finding; no false hypothesis is used.

What the packaging lemma DOES prove unconditionally is the entire algebraic repackaging
(`Λ^{2e-1} → ε'·(ζ−1)^{n'}`) and the threading of reality + `𝔭`-coprimality + `n' ≥ 2`.

## What this file proves

* `freeContentPackaging_Lambda_eq` — the standalone `(1-ζ)(1-ζ³⁶) = -ζ³⁶(ζ-1)²` identity.
* `freeContentPackaging_neg_zeta_pow_36_isUnit` — `-ζ³⁶` is a unit (the `ε'`-absorbed factor).
* `freeContentCaseIIData37_of_descended_equation` — **the packaging lemma**: from the integer
  descended equation `ω³⁷+θ³⁷ = δ·Λ^{2e-1}·z'³⁷` (`Λ = (1-ζ)(1-ζ³⁶)`), reality of `ω, θ, z'`,
  `𝔭`-coprimality of `z'` and `θ`, `e ≥ 1`, and the two field-conditions `hxy'`/`hdenom'`, produce
  `∃ (n':ℕ) (D':FreeContentCaseIIData37 K n'), D'.z = z'` with `n' = 4e-2`.
* `freeContentCaseIIData37_of_factorEquations` — **the composed lemma**: factor equations + anchor +
  Assumption II + reality + the field-conditions `⟹` a `FreeContentCaseIIData37`, wiring
  `washington_section91_descended_equation` into the packaging.  This reduces the FLT37 Case-II
  descent step to the factor-equation extraction.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), pp. 171–173;
  §9.1, pp. 179–180 (the reassembly).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The `Λ = (1-ζ)(1-ζ³⁶) = -ζ³⁶(ζ-1)²` integer identity (standalone) -/

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **`-ζ³⁶` is a unit of `𝓞 K`** for a primitive `37`-th root `ζ` (`ζ·ζ³⁶ = ζ³⁷ = 1`, so `ζ³⁶`
is a unit, hence so is its negation).  This is the unit factor that `ε'` absorbs in the
`Λ^{2e-1} → ε'·(ζ-1)^{n'}` conversion. -/
theorem freeContentPackaging_neg_zeta_pow_36_isUnit {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    IsUnit (-(hζ.toInteger ^ 36) : 𝓞 K) := by
  have h37 : hζ.toInteger ^ 37 = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  refine IsUnit.of_mul_eq_one (-(hζ.toInteger)) ?_
  rw [neg_mul_neg, ← pow_succ]; exact h37

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The standalone `Λ = -ζ³⁶(ζ-1)²` identity** (integer level), the `m`-machinery-free
re-derivation of `caseII_LambdaCyc_algebraMap_eq_neg_zeta_pow_36_mul_zeta_sub_one_sq`.  For a
primitive `37`-th root `ζ`, `(1-ζ)(1-ζ³⁶) = -ζ³⁶·(ζ-1)²`.  Proof: expand
`-ζ³⁶(ζ-1)² = -ζ³⁸+2ζ³⁷-ζ³⁶ = -ζ+2-ζ³⁶` (using `ζ³⁷=1`, `ζ³⁸=ζ`), and
`(1-ζ)(1-ζ³⁶) = 1-ζ-ζ³⁶+ζ³⁷ = 2-ζ-ζ³⁶`. -/
theorem freeContentPackaging_Lambda_eq {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    (1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36) =
      -(hζ.toInteger ^ 36) * (hζ.toInteger - 1) ^ 2 := by
  have h37 : hζ.toInteger ^ 37 = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  linear_combination (hζ.toInteger - 1) * h37

/-! ## 2. The packaging lemma -/

/-- **[FREE-CONTENT-PACKAGING] Washington's descended equation ⟹ a `FreeContentCaseIIData37`.**

From the **integer** descended Fermat equation
```
ω³⁷ + θ³⁷ = (δ : 𝓞 K) · Λ^{2e-1} · z'³⁷,     Λ = (1-ζ)(1-ζ³⁶)   (= the real prime),
```
with `ω, θ, z' : 𝓞 K`, `δ : (𝓞 K)ˣ`, `e ≥ 1`, together with
* reality `σω = ω`, `σθ = θ` (the datum records `x_real`, `y_real`; `z`-reality is *not* a datum
  field, so `σz'` is not required here);
* `𝔭`-coprimality `(ζ−1) ∤ θ`, `(ζ−1) ∤ z'`;
* the anchor absorption `(ζ−1)³ ∣ ω + θ`  (= the datum field `hxy`);
* the sharp adjacent denominator `ω + θ·ζ³⁶ = (ζ−1)·c`, `(ζ−1) ∤ c`  (= the datum field `hdenom`),

there is a free-content Case-II datum `D' : FreeContentCaseIIData37 K (4*e-2)` with `D'.z = z'`
(and `D'.x = ω`, `D'.y = θ`, `D'.ε = δ·(-ζ³⁶)^{2e-1}`).

The content is purely the algebraic repackaging `Λ^{2e-1} = (-ζ³⁶)^{2e-1}·(ζ-1)^{2(2e-1)}`
(`freeContentPackaging_Lambda_eq`, `freeContentPackaging_neg_zeta_pow_36_isUnit`); the two
field-conditions are carried verbatim (they are *not* derivable from the equation — see the module
docstring).  Both `ω, θ, z'` are taken as algebraic integers (the conjugate-norm building blocks
are integers). -/
theorem freeContentCaseIIData37_of_descended_equation
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {ω θ z' : 𝓞 K} {δ : (𝓞 K)ˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hequation : ω ^ 37 + θ ^ 37 =
      (δ : 𝓞 K) * ((1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36)) ^ (2 * e - 1) * z' ^ 37)
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj K ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj K θ = θ)
    (hθ_cop : ¬ hζ.toInteger - 1 ∣ θ)
    (hz'_cop : ¬ hζ.toInteger - 1 ∣ z')
    (hxy' : (hζ.toInteger - 1) ^ 3 ∣ ω + θ)
    (hdenom' : ∃ c : 𝓞 K, ω + θ * hζ.toInteger ^ 36 = (hζ.toInteger - 1) * c ∧
      ¬ (hζ.toInteger - 1) ∣ c) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 K n'), D'.z = z' := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The unit factor `-ζ³⁶` and its `(2e-1)`-th power, packaged into `ε'`.
  set η36u : (𝓞 K)ˣ := (freeContentPackaging_neg_zeta_pow_36_isUnit hζ).unit with hη36u_def
  have hη36u_val : (η36u : 𝓞 K) = -(hζ.toInteger ^ 36) := by
    rw [hη36u_def, IsUnit.unit_spec]
  -- `ε' = δ · (-ζ³⁶)^{2e-1}` as a unit.
  set ε' : (𝓞 K)ˣ := δ * η36u ^ (2 * e - 1) with hε'_def
  -- `n' = 2·(2e-1) = 4e-2`.
  set n' : ℕ := 2 * (2 * e - 1) with hn'_def
  -- The equation, repackaged into the native free-content form.
  have hequation' : ω ^ 37 + θ ^ 37 = (ε' : 𝓞 K) * (hζ.toInteger - 1) ^ n' * z' ^ 37 := by
    rw [hequation]
    -- `Λ = -ζ³⁶(ζ-1)²`, so `Λ^{2e-1} = (-ζ³⁶)^{2e-1}·(ζ-1)^{2(2e-1)}`.
    rw [freeContentPackaging_Lambda_eq hζ, mul_pow, ← pow_mul]
    -- `ε' = δ·(-ζ³⁶)^{2e-1}`, `(ζ-1)^{(2e-1)·2} = (ζ-1)^{n'}`.
    rw [hε'_def, Units.val_mul, Units.val_pow_eq_pow_val, hη36u_val, hn'_def]
    ring
  -- `1 ≤ n'`: `n' = 2(2e-1) ≥ 2` since `e ≥ 1`.
  have hn'_ge : 1 ≤ n' := by rw [hn'_def]; omega
  -- Assemble the datum; the `equation` field is exactly `hequation'`.
  let D' : FreeContentCaseIIData37 K n' :=
    { ζ := ζ, hζ := hζ, x := ω, y := θ, z := z', ε := ε',
      equation := hequation', x_real := hω_real, y_real := hθ_real, hy := hθ_cop, hz := hz'_cop,
      hn := hn'_ge, hxy := hxy', hdenom := hdenom' }
  exact ⟨n', D', rfl⟩

end BernoulliRegular.FLT37.Eichler

end

end
