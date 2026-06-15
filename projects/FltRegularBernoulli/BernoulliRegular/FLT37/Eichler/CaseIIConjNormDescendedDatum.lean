import BernoulliRegular.FLT37.Eichler.CaseIISection91DescendedDatum

/-!
# [FLT37-CASEII-R2] The **conjugate-norm** descended free-content datum (ξ-side reconciliation)

This file supplies the genuine new unblock of Washington's §9.1 / Theorem 9.4 conjugate-norm
descent: the **ξ-side reconciliation** that lets the descended Fermat variable be the *real*
conjugate norm `ξ₁ = ρ₀·σρ₀` — Washington's actual new variable (GTM 83, 2nd ed., p. 172) — rather
than the non-real `ρ₀²`.

## The ξ-side reconciliation (the new content)

`washington_section91_descended_equation` (`CaseIISection91ConjNormReassembly.lean`) produces the
descended Fermat equation with RHS `δ·Λ^{2e-1}·(ρ₀²)³⁷`, i.e. with the Fermat variable `ξ = ρ₀²`,
which is **not** σ-fixed in general (`ρ₀` itself is not real — only `ρ₀³⁷` is).  Washington's actual
new variable is the **conjugate norm** `ξ₁ = ρ₀·σρ₀`, which **is** real (`σ(ρ₀σρ₀) = σρ₀·ρ₀`).  The
two agree after the `³⁷`-power:

* `washington_rho0_pow_real_of_anchor` — **`ρ₀³⁷` is real** (`σ(ρ₀³⁷) = ρ₀³⁷`): from the anchor
  equation `x+y = η₀·Λ^e·ρ₀³⁷` with `x+y`, `η₀`, `Λ` all real and `η₀·Λ^e ≠ 0`, since
  `ρ₀³⁷ = (x+y)·(η₀·Λ^e)⁻¹` is a quotient of σ-fixed elements.

* `washington_xi_reconciliation` — **`(ρ₀²)³⁷ = (ρ₀·σρ₀)³⁷`**: from `σ(ρ₀³⁷) = ρ₀³⁷` (so
  `(σρ₀)³⁷ = ρ₀³⁷`, i.e. `(ρ₀/σρ₀)³⁷ = 1` — `ρ₀/σρ₀` is a `37`-th root of unity), both sides equal
  `ρ₀⁷⁴`: `(ρ₀σρ₀)³⁷ = ρ₀³⁷·(σρ₀)³⁷ = ρ₀³⁷·ρ₀³⁷ = (ρ₀²)³⁷`.  This is the genuine reconciliation of
  the documented `ρ₀²`-vs-`ρ₀σρ₀` mismatch **at the element level** (the ideal-level statement
  `span(ρ₀²) = span(ρ₀σρ₀) = 𝔞₀²` is in `CaseIISection91ExtractionProducer.lean`).  We do **not**
  assert `ρ₀² = ρ₀σρ₀` as elements — that is false; only their `³⁷`-powers agree.

## What this buys (the conjugate-norm packaging)

* `washington_section91_integer_descended_equation_conjNorm` — the integer descended equation in
  **conjugate-norm form**: from the §9.1 factor/anchor/Assumption-II data (reality of `x+y`, `η₀`,
  `Λ`, `η_b`) and an integer witness `w : 𝓞 K` for the **real** conjugate norm `ρ₀·σρ₀`
  (`algebraMap w = ρ₀σρ₀`), the equation
  `ω³⁷ + θ³⁷ = δ'·((1−ζ)(1−ζ³⁶))^{2e-1}·w³⁷` holds in `𝓞 K`.  The RHS uses `w³⁷ = (ρ₀σρ₀)³⁷ =
  (ρ₀²)³⁷` (the reconciliation), so the variable is the conjugate norm.

* `freeContentCaseIIData37_conjNorm_of_factorEquations` — the descended **conjugate-norm**
  free-content datum: the same factor/anchor/Assumption-II/invariant data, with `w` real,
  `𝔭`-coprime, yields a `FreeContentCaseIIData37` whose Fermat variable `D'.z` **is** `w`
  (Washington's real `ξ₁ = ρ₀σρ₀`), at the doubled content `2·(2e−1)`.  Unlike
  `freeContentCaseIIData37_of_factorEquations` (whose `D'.z = z' = ρ₀²` is not real), this delivers
  the *real* conjugate-norm variable.

## Soundness

The reconciliation `(ρ₀²)³⁷ = (ρ₀σρ₀)³⁷` is proven **only at the `³⁷`-power** (never as
`ρ₀² = ρ₀σρ₀`).  The integer witness `w` with `algebraMap w = ρ₀σρ₀` is **threaded as a hypothesis**
— it is Washington's conjugate-norm generator (proven to exist with `(w) = 𝔞₀^{2k'}`, real,
`𝔭`-coprime, in `caseII_anchorPow_conjNorm_real_span`), supplied where the §9.1 construction
provides it, never asserted abstractly.  The frame is the free-content / doubled-measure one (the
`RealCaseIIData37` linear-measure form is obstructed; see `CaseIIRealAnchorDatumAssembly.lean`).  No
`sorry`, no `axiom`; imports only — modifies nothing.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), pp. 171–173
  (the conjugate-norm new variable `ξ₁ = ρ₀σρ₀`, `(ξ₁) = B₀²`, real, doubled measure `λ^{2m−p}`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37 BernoulliRegular

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]

/-! ## 1. The ξ-side reconciliation (field level, general CM field) -/

/-- **[ξ-RECONCILIATION] `(ρ₀²)³⁷ = (ρ₀·σρ₀)³⁷`** when `ρ₀³⁷` is real (general CM field).

From `σ(ρ₀³⁷) = ρ₀³⁷` we get `(σρ₀)³⁷ = σ(ρ₀³⁷) = ρ₀³⁷` (`map_pow`), so
`(ρ₀·σρ₀)³⁷ = ρ₀³⁷·(σρ₀)³⁷ = ρ₀³⁷·ρ₀³⁷ = ρ₀⁷⁴ = (ρ₀²)³⁷`.  This is the element-level reconciliation
of the descended Fermat variable `ξ = ρ₀²` with Washington's **real** conjugate norm `ξ₁ = ρ₀σρ₀`:
they are **not** equal as elements (`ρ₀` is not real), but their `³⁷`-powers agree — which is what
the descended Fermat equation (an identity between `³⁷`-powers) needs. -/
theorem washington_xi_reconciliation {ρ0 : K}
    (hρ0pow : complexConj K (ρ0 ^ 37) = ρ0 ^ 37) :
    (ρ0 ^ 2) ^ 37 = (ρ0 * complexConj K ρ0) ^ 37 := by
  -- `(σρ₀)³⁷ = σ(ρ₀³⁷) = ρ₀³⁷`.
  have hconj_pow : (complexConj K ρ0) ^ 37 = ρ0 ^ 37 := by
    rw [← map_pow]; exact hρ0pow
  -- `(ρ₀σρ₀)³⁷ = ρ₀³⁷·(σρ₀)³⁷ = ρ₀³⁷·ρ₀³⁷ = (ρ₀²)³⁷`.
  rw [mul_pow, hconj_pow, ← pow_add, ← pow_mul]

/-- **`ρ₀³⁷` is real** (σ-fixed) from a **real anchor equation** (general CM field).

From `x+y = η₀·Λ^e·ρ₀³⁷` with `x+y`, `η₀`, `Λ` all σ-fixed and the prefactor `η₀·Λ^e` nonzero,
`ρ₀³⁷ = (x+y)·(η₀·Λ^e)⁻¹` is a quotient of σ-fixed elements, hence σ-fixed.  (In the §9.1 setting
`x+y` is real because the datum is real, and `η₀`, `Λ` are the real anchor unit and the real prime
`(1−ζ)(1−ζ³⁶)`.) -/
theorem washington_rho0_pow_real_of_anchor {x y ρ0 ηΛ : K}
    (hanchor : x + y = ηΛ * ρ0 ^ 37)
    (hxy_real : complexConj K (x + y) = x + y)
    (hηΛ_real : complexConj K ηΛ = ηΛ)
    (hηΛ_ne : ηΛ ≠ 0) :
    complexConj K (ρ0 ^ 37) = ρ0 ^ 37 := by
  -- `ρ₀³⁷ = (x+y)·ηΛ⁻¹`.
  have hρ0pow : ρ0 ^ 37 = (x + y) * ηΛ⁻¹ := by
    rw [hanchor]; field_simp
  rw [hρ0pow, map_mul, map_inv₀, hxy_real, hηΛ_real]

/-! ## 2. The `ρ₀`-FREE descended equation: the anchor *quotient* `R = (x+y)/(η₀·Λ^e)`

The crucial structural fact about Washington's reassembly is that the generator `ρ₀` enters **only**
through the combination `(ρ₀²)³⁷ = (ρ₀³⁷)²` — i.e. only through `R := ρ₀³⁷`, never through `ρ₀`
itself (or any genuine `37`-th root).  And `R = (x+y)·(η₀·Λ^e)⁻¹` is a field element that **always
exists** (no `37`-th-root / `𝔞₀`-principal requirement).  So the descended equation can be stated
with the anchor in the **quotient** form `x+y = η₀·Λ^e·R` (`R` a bare field element), concluding
`ω³⁷ + θ³⁷ = δ·Λ^{2e-1}·R²` — *avoiding* the over-strong single-`ρ₀` anchor entirely.  This is the
genuine value-add: it sidesteps the `𝔞₀`-principal obstruction (`R` is not required to be a `37`-th
power), and `R²` is the field element `(x+y)²·(η₀·Λ^e)⁻²` — controllable by ideal arithmetic. -/

/-- **[ρ₀-FREE `xy`-elimination]** Washington §9.1 steps 1–3 at one index, with the anchor in
quotient form `x+y = η₀·Λ^e·R`.  Identical to `washington_xy_eq` but with `R` a bare field element
(morally `R = ρ₀³⁷`, so `(ρ₀²)³⁷ = R²`); the conclusion has `R²` in place of `(ρ₀²)³⁷`. -/
theorem washington_xy_eq_free
    {x y ρc R zpc znc : K} {ηc η0 Λc Λ : Kˣ} {e : ℕ}
    (hzc : zpc * znc = 1)
    (hΛc : (Λc : K) = (1 - zpc) * (1 - znc))
    (hfc_pos : x + zpc * y = (1 - zpc) * (ηc : K) * ρc ^ 37)
    (hfc_neg : x + znc * y = (1 - znc) * (ηc : K) * (complexConj K ρc) ^ 37)
    (hanchor : x + y = (η0 : K) * (Λ : K) ^ e * R) :
    x * y =
      (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * R ^ 2 * ((Λc : K)⁻¹) -
        (ηc : K) ^ 2 * (ρc * complexConj K ρc) ^ 37 := by
  have hΛc_ne : (Λc : K) ≠ 0 := Λc.ne_zero
  have key : (Λc : K) * (x * y) =
      (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * R ^ 2 -
        (Λc : K) * ((ηc : K) ^ 2 * (ρc * complexConj K ρc) ^ 37) := by
    have hPc : (x + zpc * y) * (x + znc * y) =
        (Λc : K) * ((ηc : K) ^ 2 * (ρc * complexConj K ρc) ^ 37) := by
      rw [hfc_pos, hfc_neg, hΛc]; ring
    have hS : (x + y) ^ 2 = (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * R ^ 2 := by
      rw [hanchor]; ring
    have hsub : (x + y) ^ 2 - (x + zpc * y) * (x + znc * y) = (Λc : K) * (x * y) := by
      rw [hΛc]; linear_combination -(x * y + y ^ 2) * hzc
    rw [← hsub, hPc, hS]
  field_simp at key ⊢
  linear_combination key

/-- **[ρ₀-FREE reassembly]** Washington §9.1 steps 1–4, 6, with the anchor in quotient form
`x+y = η₀·Λ^e·R`.  Identical to `washington_section91_reassembly` but with `R` a bare field element;
the conclusion has `R²` in place of `(ρ₀²)³⁷`.  **No `37`-th-root / `𝔞₀`-principal requirement** on
`R`. -/
theorem washington_section91_reassembly_free
    {x y ρa ρb R zpa zna zpb znb : K} {ηa ηb η0 u θ' Λa Λb Λ : Kˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hza : zpa * zna = 1) (hzb : zpb * znb = 1)
    (hΛa : (Λa : K) = (1 - zpa) * (1 - zna))
    (hΛb : (Λb : K) = (1 - zpb) * (1 - znb))
    (hfa_pos : x + zpa * y = (1 - zpa) * (ηa : K) * ρa ^ 37)
    (hfa_neg : x + zna * y = (1 - zna) * (ηa : K) * (complexConj K ρa) ^ 37)
    (hfb_pos : x + zpb * y = (1 - zpb) * (ηb : K) * ρb ^ 37)
    (hfb_neg : x + znb * y = (1 - znb) * (ηb : K) * (complexConj K ρb) ^ 37)
    (hanchor : x + y = (η0 : K) * (Λ : K) ^ e * R)
    (hII : (ηa : Kˣ) = u ^ 37 * ηb)
    (hcrux : (Λa : K)⁻¹ - (Λb : K)⁻¹ = (θ' : K) * (Λ : K)⁻¹) :
    ((u : K) ^ 2 * (ρa * complexConj K ρa)) ^ 37 +
        (-(ρb * complexConj K ρb)) ^ 37 =
      (η0 ^ 2 * θ' * ηb⁻¹ ^ 2 : Kˣ) * (Λ : K) ^ (2 * e - 1) * R ^ 2 := by
  have hxyA := washington_xy_eq_free hza hΛa hfa_pos hfa_neg hanchor
  have hxyB := washington_xy_eq_free hzb hΛb hfb_pos hfb_neg hanchor
  set S : K := (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * R ^ 2 with hS_def
  have hstep4 : (ηa : K) ^ 2 * (ρa * complexConj K ρa) ^ 37 -
      (ηb : K) ^ 2 * (ρb * complexConj K ρb) ^ 37 = S * ((Λa : K)⁻¹ - (Λb : K)⁻¹) := by
    have h := hxyA.symm.trans hxyB
    linear_combination -h
  rw [hcrux] at hstep4
  have hΛpow : (Λ : K) ^ (2 * e) * (Λ : K)⁻¹ = (Λ : K) ^ (2 * e - 1) := by
    have hpow : (Λ : K) ^ (2 * e) = (Λ : K) ^ (2 * e - 1) * (Λ : K) := by
      conv_lhs => rw [show 2 * e = (2 * e - 1) + 1 from by omega]
      rw [pow_succ]
    rw [hpow, mul_assoc, mul_inv_cancel₀ Λ.ne_zero, mul_one]
  have hstep5 : (ηa : K) ^ 2 * (ρa * complexConj K ρa) ^ 37 -
      (ηb : K) ^ 2 * (ρb * complexConj K ρb) ^ 37 =
      (η0 : K) ^ 2 * (θ' : K) * (Λ : K) ^ (2 * e - 1) * R ^ 2 := by
    rw [hstep4, hS_def]
    rw [show (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * R ^ 2 * ((θ' : K) * (Λ : K)⁻¹) =
      (η0 : K) ^ 2 * (θ' : K) * ((Λ : K) ^ (2 * e) * (Λ : K)⁻¹) * R ^ 2 from by ring,
      hΛpow]
  have hηa_sq : (ηa : K) ^ 2 = ((u : K) ^ 2) ^ 37 * (ηb : K) ^ 2 := by
    have hII' : (ηa : K) = (u : K) ^ 37 * (ηb : K) := by
      rw [show (ηa : K) = ((ηa : Kˣ) : K) from rfl, hII]; push_cast; ring
    rw [hII']; ring
  have hδ_coe : ((η0 ^ 2 * θ' * ηb⁻¹ ^ 2 : Kˣ) : K) =
      (η0 : K) ^ 2 * (θ' : K) * ((ηb : K) ^ 2)⁻¹ := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
  rw [hδ_coe]
  have hηb_ne : (ηb : K) ^ 2 ≠ 0 := pow_ne_zero 2 ηb.ne_zero
  rw [hηa_sq] at hstep5
  have key : ((u : K) ^ 2) ^ 37 * (ρa * complexConj K ρa) ^ 37 -
      (ρb * complexConj K ρb) ^ 37 =
      (η0 : K) ^ 2 * (θ' : K) * ((ηb : K) ^ 2)⁻¹ * (Λ : K) ^ (2 * e - 1) * R ^ 2 := by
    field_simp
    field_simp at hstep5
    linear_combination hstep5
  rw [mul_pow, Odd.neg_pow (by decide : Odd 37)]
  linear_combination key

variable {K' : Type} [Field K'] [NumberField K'] [IsCyclotomicExtension {37} ℚ K']
  [NumberField.IsCMField K']

/-- **[ρ₀-FREE descended equation]** Washington §9.1 descended Fermat equation in anchor-quotient
form (`K'` cyclotomic conductor `37`), the crux discharged internally.  From the four factor
equations, the **quotient** anchor `x+y = η₀·Λ^e·R` (`R` a bare field element, *no* `37`-th-root /
`𝔞₀`-principal requirement), and Assumption II, the descended equation
```
ω³⁷ + θ³⁷ = δ · Λ^{2e-1} · R²,    ω = u²ρ_aσρ_a, θ = -ρ_bσρ_b,
```
holds for a **σ-fixed** unit `δ : K'ˣ`.  This is the genuine §9.1 descended equation with the
over-strong single-`ρ₀` anchor *removed*: `R = (x+y)·(η₀·Λ^e)⁻¹` always exists (no `37`-th-root /
`𝔞₀`-principal requirement), and `R²` (the Fermat-variable `³⁷`-power: morally `R = ρ₀³⁷`, so
`R² = (ρ₀²)³⁷ = ξ₁³⁷`) is the controllable field element `(x+y)²·(η₀·Λ^e)⁻²`. -/
theorem washington_section91_descended_equation_free
    {x y ρa ρb R : K'} {ηa ηb η0 u : K'ˣ} {ηA ηB : 𝓞 K'}
    {Λa Λb Λ : K'ˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hA : ηA ^ 37 = 1) (hB : ηB ^ 37 = 1)
    (hA1 : ηA ≠ 1) (hB1 : ηB ≠ 1) (hAB : ηA ≠ ηB) (hABp : ηA * ηB ≠ 1)
    (hΛa : (Λa : K') = algebraMap (𝓞 K') K' ((1 - ηA) * (1 - ηA ^ 36)))
    (hΛb : (Λb : K') = algebraMap (𝓞 K') K' ((1 - ηB) * (1 - ηB ^ 36)))
    (hΛ : (Λ : K') = algebraMap (𝓞 K') K'
      ((1 - (zeta_spec 37 ℚ K').toInteger) * (1 - (zeta_spec 37 ℚ K').toInteger ^ 36)))
    (hfa_pos : x + algebraMap (𝓞 K') K' ηA * y =
      (1 - algebraMap (𝓞 K') K' ηA) * (ηa : K') * ρa ^ 37)
    (hfa_neg : x + algebraMap (𝓞 K') K' (ηA ^ 36) * y =
      (1 - algebraMap (𝓞 K') K' (ηA ^ 36)) * (ηa : K') * (complexConj K' ρa) ^ 37)
    (hfb_pos : x + algebraMap (𝓞 K') K' ηB * y =
      (1 - algebraMap (𝓞 K') K' ηB) * (ηb : K') * ρb ^ 37)
    (hfb_neg : x + algebraMap (𝓞 K') K' (ηB ^ 36) * y =
      (1 - algebraMap (𝓞 K') K' (ηB ^ 36)) * (ηb : K') * (complexConj K' ρb) ^ 37)
    (hanchor : x + y = (η0 : K') * (Λ : K') ^ e * R)
    (hII : (ηa : K'ˣ) = u ^ 37 * ηb)
    (hη0real : complexConj K' (η0 : K') = (η0 : K'))
    (hηbreal : complexConj K' (ηb : K') = (ηb : K')) :
    ∃ δ : K'ˣ, complexConj K' (δ : K') = (δ : K') ∧
      ((u : K') ^ 2 * (ρa * complexConj K' ρa)) ^ 37 +
          (-(ρb * complexConj K' ρb)) ^ 37 =
        (δ : K') * (Λ : K') ^ (2 * e - 1) * R ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨θ', hθ'real, hθ'id⟩ := washington_section91_crux_unit hA hB hA1 hB1 hAB hABp
  set θ'_field : K'ˣ := Units.map (algebraMap (𝓞 K') K' : 𝓞 K' →* K') θ' with hθ'f_def
  have hθ'f_coe : (θ'_field : K') = algebraMap (𝓞 K') K' (θ' : 𝓞 K') := by
    rw [hθ'f_def, Units.coe_map, MonoidHom.coe_coe]
  have hθ'f_real : complexConj K' (θ'_field : K') = (θ'_field : K') := by
    rw [hθ'f_coe]
    rw [show algebraMap (𝓞 K') K' (θ' : 𝓞 K') = ((θ' : 𝓞 K') : K') from rfl,
      ← coe_ringOfIntegersComplexConj, hθ'real]
  have hcrux : (Λa : K')⁻¹ - (Λb : K')⁻¹ = (θ'_field : K') * (Λ : K')⁻¹ := by
    rw [hΛa, hΛb, hΛ, hθ'f_coe]; exact hθ'id
  have hza : algebraMap (𝓞 K') K' ηA * algebraMap (𝓞 K') K' (ηA ^ 36) = 1 := by
    rw [← map_mul, mul_comm, ← pow_succ, hA, map_one]
  have hzb : algebraMap (𝓞 K') K' ηB * algebraMap (𝓞 K') K' (ηB ^ 36) = 1 := by
    rw [← map_mul, mul_comm, ← pow_succ, hB, map_one]
  have hΛa' : (Λa : K') = (1 - algebraMap (𝓞 K') K' ηA) * (1 - algebraMap (𝓞 K') K' (ηA ^ 36)) := by
    rw [hΛa, map_mul, map_sub, map_sub, map_one]
  have hΛb' : (Λb : K') = (1 - algebraMap (𝓞 K') K' ηB) * (1 - algebraMap (𝓞 K') K' (ηB ^ 36)) := by
    rw [hΛb, map_mul, map_sub, map_sub, map_one]
  refine ⟨η0 ^ 2 * θ'_field * ηb⁻¹ ^ 2, ?_, ?_⟩
  · have hcoe : ((η0 ^ 2 * θ'_field * ηb⁻¹ ^ 2 : K'ˣ) : K') =
        (η0 : K') ^ 2 * (θ'_field : K') * ((ηb : K') ^ 2)⁻¹ := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
    rw [hcoe, map_mul, map_mul, map_pow, map_inv₀, map_pow, hη0real, hθ'f_real, hηbreal]
  · exact washington_section91_reassembly_free he hza hzb hΛa' hΛb'
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor hII hcrux

/-- **[SECTION-91-CONJNORM-INTEGER-DESCENT] The integer descended equation in conjugate-norm form.**

Identical to `washington_section91_integer_descended_equation`
(`CaseIISection91IntegerDescent.lean`), but with the Fermat variable taken to be Washington's
**real** conjugate norm `ξ₁ = ρ₀·σρ₀`: instead of an integer witness `z'` for `ρ₀²`, we take an
integer witness `w : 𝓞 K'` for the conjugate norm (`algebraMap w = ρ₀·σρ₀`) and supply the reality
data (`x+y`, `η₀`, `Λ` real) to run the ξ-reconciliation `(ρ₀²)³⁷ = (ρ₀σρ₀)³⁷`.  The resulting
integer equation
```
ω³⁷ + θ³⁷ = (δ' : 𝓞 K') · ((1−ζ)(1−ζ³⁶))^{2e−1} · w³⁷
```
holds in `𝓞 K'` with `w` the conjugate norm.

Proof: the field descended equation (`washington_section91_descended_equation`) has RHS
`δ·Λ^{2e−1}·(ρ₀²)³⁷`; the anchor equation + reality give `σ(ρ₀³⁷) = ρ₀³⁷`
(`washington_rho0_pow_real_of_anchor`), so `(ρ₀²)³⁷ = (ρ₀σρ₀)³⁷` (`washington_xi_reconciliation`),
and `algebraMap (w³⁷) = (ρ₀σρ₀)³⁷ = (ρ₀²)³⁷`.  Then both sides are `algebraMap` of the integer
expressions, and injectivity of `algebraMap (𝓞 K') K'` descends the equation. -/
theorem washington_section91_integer_descended_equation_conjNorm
    {x y ρa ρb ρ0 : K'} {ηa ηb η0 u : K'ˣ} {ηA ηB : 𝓞 K'}
    {Λa Λb Λ : K'ˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hA : ηA ^ 37 = 1) (hB : ηB ^ 37 = 1)
    (hA1 : ηA ≠ 1) (hB1 : ηB ≠ 1) (hAB : ηA ≠ ηB) (hABp : ηA * ηB ≠ 1)
    (hΛa : (Λa : K') = algebraMap (𝓞 K') K' ((1 - ηA) * (1 - ηA ^ 36)))
    (hΛb : (Λb : K') = algebraMap (𝓞 K') K' ((1 - ηB) * (1 - ηB ^ 36)))
    (hΛ : (Λ : K') = algebraMap (𝓞 K') K'
      ((1 - (zeta_spec 37 ℚ K').toInteger) * (1 - (zeta_spec 37 ℚ K').toInteger ^ 36)))
    (hfa_pos : x + algebraMap (𝓞 K') K' ηA * y =
      (1 - algebraMap (𝓞 K') K' ηA) * (ηa : K') * ρa ^ 37)
    (hfa_neg : x + algebraMap (𝓞 K') K' (ηA ^ 36) * y =
      (1 - algebraMap (𝓞 K') K' (ηA ^ 36)) * (ηa : K') * (complexConj K' ρa) ^ 37)
    (hfb_pos : x + algebraMap (𝓞 K') K' ηB * y =
      (1 - algebraMap (𝓞 K') K' ηB) * (ηb : K') * ρb ^ 37)
    (hfb_neg : x + algebraMap (𝓞 K') K' (ηB ^ 36) * y =
      (1 - algebraMap (𝓞 K') K' (ηB ^ 36)) * (ηb : K') * (complexConj K' ρb) ^ 37)
    (hanchor : x + y = (η0 : K') * (Λ : K') ^ e * ρ0 ^ 37)
    (hII : (ηa : K'ˣ) = u ^ 37 * ηb)
    (hη0real : complexConj K' (η0 : K') = (η0 : K'))
    (hηbreal : complexConj K' (ηb : K') = (ηb : K'))
    -- reality of `x+y` (the datum is real), used to run the ξ-reconciliation:
    (hxy_real : complexConj K' (x + y) = x + y)
    -- integer witnesses for the blocks, the σ-fixed field unit, and the conjugate norm `w`:
    {ω θ w : 𝓞 K'} {δ' : (𝓞 K')ˣ}
    (hω : algebraMap (𝓞 K') K' ω = (u : K') ^ 2 * (ρa * complexConj K' ρa))
    (hθ : algebraMap (𝓞 K') K' θ = -(ρb * complexConj K' ρb))
    (hw : algebraMap (𝓞 K') K' w = ρ0 * complexConj K' ρ0)
    (hδ' : ∀ δ : K'ˣ, complexConj K' (δ : K') = (δ : K') →
      ((u : K') ^ 2 * (ρa * complexConj K' ρa)) ^ 37 +
          (-(ρb * complexConj K' ρb)) ^ 37 =
        (δ : K') * (Λ : K') ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 →
      (δ : K') = algebraMap (𝓞 K') K' (δ' : 𝓞 K')) :
    ω ^ 37 + θ ^ 37 =
      (δ' : 𝓞 K') *
        ((1 - (zeta_spec 37 ℚ K').toInteger) * (1 - (zeta_spec 37 ℚ K').toInteger ^ 36)) ^
          (2 * e - 1) *
        w ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- §9.1: the field descended equation, with a σ-fixed field unit `δ`.
  obtain ⟨δ, hδ_real, hδ_eq⟩ :=
    washington_section91_descended_equation he hA hB hA1 hB1 hAB hABp hΛa hΛb hΛ
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor hII hη0real hηbreal
  -- The field unit descends to `algebraMap δ'`.
  have hδ_coe : (δ : K') = algebraMap (𝓞 K') K' (δ' : 𝓞 K') := hδ' δ hδ_real hδ_eq
  -- The ξ-reconciliation: `(ρ₀²)³⁷ = (ρ₀σρ₀)³⁷`.
  -- `ηΛ := η₀·Λ^e` is real and nonzero (`η₀`, `Λ` units, `Λ` real).
  have hΛ_real : complexConj K' (Λ : K') = (Λ : K') := by
    rw [hΛ, show algebraMap (𝓞 K') K' ((1 - (zeta_spec 37 ℚ K').toInteger) *
        (1 - (zeta_spec 37 ℚ K').toInteger ^ 36)) =
      ((((1 - (zeta_spec 37 ℚ K').toInteger) *
        (1 - (zeta_spec 37 ℚ K').toInteger ^ 36)) : 𝓞 K') : K') from rfl,
      ← coe_ringOfIntegersComplexConj,
      washington_L_real (zeta_spec 37 ℚ K').toInteger_isPrimitiveRoot.pow_eq_one]
  have hηΛ_real : complexConj K' ((η0 : K') * (Λ : K') ^ e) = (η0 : K') * (Λ : K') ^ e := by
    rw [map_mul, map_pow, hη0real, hΛ_real]
  have hηΛ_ne : (η0 : K') * (Λ : K') ^ e ≠ 0 :=
    mul_ne_zero η0.ne_zero (pow_ne_zero _ Λ.ne_zero)
  have hρ0pow_real : complexConj K' (ρ0 ^ 37) = ρ0 ^ 37 :=
    washington_rho0_pow_real_of_anchor (ηΛ := (η0 : K') * (Λ : K') ^ e)
      hanchor hxy_real hηΛ_real hηΛ_ne
  have hxi : (ρ0 ^ 2) ^ 37 = (ρ0 * complexConj K' ρ0) ^ 37 :=
    washington_xi_reconciliation hρ0pow_real
  -- Descend the field equation to `𝓞 K'` by injectivity, with `w³⁷ = (ρ₀σρ₀)³⁷ = (ρ₀²)³⁷`.
  apply FaithfulSMul.algebraMap_injective (𝓞 K') K'
  rw [map_add, map_pow, map_pow, hω, hθ]
  rw [map_mul, map_mul, map_pow, map_pow, hw, ← hxi, ← hΛ, ← hδ_coe]
  exact hδ_eq

/-! ## 3. The conjugate-norm descended free-content datum (`D'.z = ρ₀σρ₀`, REAL) -/

/-- **[FLT37-CASEII-CONJNORM-DESCENDED-DATUM] The descended Washington datum with the *real*
conjugate-norm Fermat variable `ξ₁ = ρ₀σρ₀`.**

Identical input to `freeContentCaseIIData37_of_factorEquations`
(`CaseIISection91DescendedDatum.lean`) — factor equations at two distinct indices `a, b`, the anchor
equation, Assumption II, the integer witnesses `ω, θ` and the descent invariants — **except** the
descended Fermat variable is the **conjugate norm** `w` (`algebraMap w = ρ₀·σρ₀`, the *real*
Washington `ξ₁`) rather than `ρ₀²`.  Supplying the reality of `x+y` (the datum is real) lets the
ξ-reconciliation `(ρ₀²)³⁷ = (ρ₀σρ₀)³⁷` rewrite the descended equation to conjugate-norm form, and
the resulting free-content datum has `D'.z = w` — Washington's actual real new variable.

The `𝔭`-coprimality `hw_cop` and the invariants `hxy'`, `hdenom'` are about `w` and `ω, θ` (the
conjugate-norm building blocks): they are the proven data of `caseII_anchorPow_conjNorm_real_span`
(`w` real, `𝔭`-coprime, `(w) = 𝔞₀^{2k'}`) and the §9.1 sharp invariants, threaded as hypotheses.

This is the conjugate-norm strengthening of `freeContentCaseIIData37_of_factorEquations`: its
descended variable is the **real** `ξ₁ = ρ₀σρ₀` (not the non-real `ρ₀²`), exactly the variable
Washington's §9.1 / Theorem 9.4 descent actually constructs (GTM 83 p. 172). -/
theorem freeContentCaseIIData37_conjNorm_of_factorEquations
    {x y ρa ρb ρ0 : K'} {ηa ηb η0 u : K'ˣ} {ηA ηB : 𝓞 K'}
    {Λa Λb Λ : K'ˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hA : ηA ^ 37 = 1) (hB : ηB ^ 37 = 1)
    (hA1 : ηA ≠ 1) (hB1 : ηB ≠ 1) (hAB : ηA ≠ ηB) (hABp : ηA * ηB ≠ 1)
    (hΛa : (Λa : K') = algebraMap (𝓞 K') K' ((1 - ηA) * (1 - ηA ^ 36)))
    (hΛb : (Λb : K') = algebraMap (𝓞 K') K' ((1 - ηB) * (1 - ηB ^ 36)))
    (hΛ : (Λ : K') = algebraMap (𝓞 K') K'
      ((1 - (zeta_spec 37 ℚ K').toInteger) * (1 - (zeta_spec 37 ℚ K').toInteger ^ 36)))
    (hfa_pos : x + algebraMap (𝓞 K') K' ηA * y =
      (1 - algebraMap (𝓞 K') K' ηA) * (ηa : K') * ρa ^ 37)
    (hfa_neg : x + algebraMap (𝓞 K') K' (ηA ^ 36) * y =
      (1 - algebraMap (𝓞 K') K' (ηA ^ 36)) * (ηa : K') * (complexConj K' ρa) ^ 37)
    (hfb_pos : x + algebraMap (𝓞 K') K' ηB * y =
      (1 - algebraMap (𝓞 K') K' ηB) * (ηb : K') * ρb ^ 37)
    (hfb_neg : x + algebraMap (𝓞 K') K' (ηB ^ 36) * y =
      (1 - algebraMap (𝓞 K') K' (ηB ^ 36)) * (ηb : K') * (complexConj K' ρb) ^ 37)
    (hanchor : x + y = (η0 : K') * (Λ : K') ^ e * ρ0 ^ 37)
    (hII : (ηa : K'ˣ) = u ^ 37 * ηb)
    (hη0real : complexConj K' (η0 : K') = (η0 : K'))
    (hηbreal : complexConj K' (ηb : K') = (ηb : K'))
    (hxy_real : complexConj K' (x + y) = x + y)
    {ω θ w : 𝓞 K'} {δ' : (𝓞 K')ˣ}
    (hω : algebraMap (𝓞 K') K' ω = (u : K') ^ 2 * (ρa * complexConj K' ρa))
    (hθ : algebraMap (𝓞 K') K' θ = -(ρb * complexConj K' ρb))
    (hw : algebraMap (𝓞 K') K' w = ρ0 * complexConj K' ρ0)
    (hδ' : ∀ δ : K'ˣ, complexConj K' (δ : K') = (δ : K') →
      ((u : K') ^ 2 * (ρa * complexConj K' ρa)) ^ 37 +
          (-(ρb * complexConj K' ρb)) ^ 37 =
        (δ : K') * (Λ : K') ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 →
      (δ : K') = algebraMap (𝓞 K') K' (δ' : 𝓞 K'))
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj K' ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj K' θ = θ)
    (hθ_cop : ¬ (zeta_spec 37 ℚ K').toInteger - 1 ∣ θ)
    (hw_cop : ¬ (zeta_spec 37 ℚ K').toInteger - 1 ∣ w)
    (hxy' : ((zeta_spec 37 ℚ K').toInteger - 1) ^ 3 ∣ ω + θ)
    (hdenom' : ∃ c : 𝓞 K',
      ω + θ * (zeta_spec 37 ℚ K').toInteger ^ 36 = ((zeta_spec 37 ℚ K').toInteger - 1) * c ∧
        ¬ ((zeta_spec 37 ℚ K').toInteger - 1) ∣ c) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 K' n'), D'.z = w :=
  freeContentCaseIIData37_of_descended_equation (zeta_spec 37 ℚ K') he
    (washington_section91_integer_descended_equation_conjNorm he hA hB hA1 hB1 hAB hABp hΛa hΛb hΛ
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor hII hη0real hηbreal hxy_real hω hθ hw hδ')
    hω_real hθ_real hθ_cop hw_cop hxy' hdenom'

/-- **The conjugate-norm descended datum's Fermat variable is *real*** — `σ(D'.z) = D'.z` — when the
conjugate-norm witness `w` is real.  (For Washington's `ξ₁ = ρ₀σρ₀`, reality is automatic:
`σ(ρ₀σρ₀) = σρ₀·ρ₀ = ρ₀σρ₀`, the conjugate-norm reality `complexConj_norm_mul_self`; supplied here
as the hypothesis `hw_real`, since the integer witness `w` carries it from
`caseII_anchorPow_conjNorm_real_span`.)  This is the distinguishing feature of the conjugate-norm
packaging over `freeContentCaseIIData37_of_factorEquations` (whose `D'.z = z' = ρ₀²` is **not**
real). -/
theorem freeContentCaseIIData37_conjNorm_z_real
    {n' : ℕ} (D' : FreeContentCaseIIData37 K' n') {w : 𝓞 K'}
    (hDz : D'.z = w)
    (hw_real : NumberField.IsCMField.ringOfIntegersComplexConj K' w = w) :
    NumberField.IsCMField.ringOfIntegersComplexConj K' D'.z = D'.z := by
  rw [hDz]; exact hw_real

/-! ## 4. The precise obstruction: in the REAL frame `𝔞₀²` principal forces `𝔞₀` principal

The conjugate-norm packaging (§3) requires an **integer** witness `w` for the conjugate norm
`ξ₁ = ρ₀σρ₀`, equivalently an integer generator of the descended Fermat variable's ideal
`(z') = 𝔞₀²` (proven `caseII_genuineUnit_anchor_span_z_eq_anchorSq`).  We prove here,
soundness-first, that this is **not** freely available in the real datum frame: `𝔞₀²` principal
**forces** `𝔞₀` principal — but `𝔞₀` is *not* principal in Case II (it carries the non-trivial
anchored class; the descent exists precisely to drop its non-anchor support).

The mechanism: in the **real** frame the anchor root is `η₀ = 1`, so `σ𝔞₀ = 𝔞₀`
(`caseII_map_a_eta_zero`) and the "conjugate norm" `𝔞₀·σ𝔞₀` degenerates to `𝔞₀²`.  The anchor
factorization `span(x+y) = 𝔭^{37m+1}·𝔞₀³⁷` (proven `caseII_span_x_add_y_eq_anchorCube`, under
coprimality) shows `[𝔞₀]` is **`37`-torsion** in `Cl(𝓞 K)` (the principal `span(x+y)` and `𝔭` make
`[𝔞₀]³⁷ = 1`).  Then `[𝔞₀]² = 1` together with `[𝔞₀]³⁷ = 1` gives `[𝔞₀]^{gcd(2,37)} = [𝔞₀] = 1`.
So the only principal power of `𝔞₀` is via `𝔞₀^{37}` (or `𝔞₀^{|Cl|}`), **never** `𝔞₀²`: the
conjugate-norm generator sits at the **doubled measure** `𝔞₀^{2k'}` with `2k' ∈ {37·(…), 2|Cl|}`, a
large even exponent, not `2`.  This is the documented doubling obstruction, and it shows the
descended Fermat variable is an integer **iff** the anchored class is `2`-torsion — the open
Washington-9.4 / II1 second-order content (`CaseIIAdjacentAnchoredClassTwoTorsion37`,
`CaseIISingleRootDescent.lean`), which needs the Kellner condition.  So the conjugate-norm route
does **not** discharge the assembly for free; the genuine residual is precisely the `2`-torsion. -/

section Obstruction

open scoped nonZeroDivisors

variable {K'' : Type} [Field K''] [NumberField K'']

/-- **`[𝔞₀]` is `37`-torsion in `Cl(𝓞 K)`** (proven, axiom-clean) — from the anchor-cube
factorization.

Given `span(x+y) = 𝔭^{37m+1}·𝔞₀³⁷` (the proven `caseII_span_x_add_y_eq_anchorCube`, under
coprimality — supplied here as the hypothesis `hfact`, so this lemma is import-light), with `𝔭`,
`𝔞₀ ≠ 0`, the anchor class is `37`-torsion: `[𝔞₀]³⁷ = 1`.  Applying the class-group hom
`ClassGroup.mk0` to `hfact` and using that `span(x+y)` and `𝔭 = span(s)` are principal (`[·] = 1`)
gives `1 = [𝔭]^{37m+1}·[𝔞₀]³⁷ = [𝔞₀]³⁷`. -/
theorem caseII_anchorClass_pow37_eq_one_of_anchorCube {m : ℕ}
    {xpy s : 𝓞 K''} {𝔞₀ : Ideal (𝓞 K'')}
    (hfact : Ideal.span ({xpy} : Set (𝓞 K'')) =
      Ideal.span ({s} : Set (𝓞 K'')) ^ (37 * m + 1) * 𝔞₀ ^ 37)
    (hs_ne : s ≠ 0) (hxpy_ne : xpy ≠ 0) (h𝔞₀_ne : 𝔞₀ ≠ 0) :
    ClassGroup.mk0 ⟨𝔞₀, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞₀_ne⟩ ^ 37 = 1 := by
  set 𝔭 : Ideal (𝓞 K'') := Ideal.span ({s} : Set (𝓞 K'')) with h𝔭_def
  have h𝔭_ne : 𝔭 ≠ 0 := by
    rw [h𝔭_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hs_ne
  have hxy_ne : Ideal.span ({xpy} : Set (𝓞 K'')) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hxpy_ne
  have hxy_mem : Ideal.span ({xpy} : Set (𝓞 K'')) ∈ (Ideal (𝓞 K''))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hxy_ne
  have h𝔭_mem : 𝔭 ∈ (Ideal (𝓞 K''))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr h𝔭_ne
  have h𝔞₀_mem : 𝔞₀ ∈ (Ideal (𝓞 K''))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞₀_ne
  have hmk_xy : ClassGroup.mk0 ⟨_, hxy_mem⟩ = 1 :=
    (ClassGroup.mk0_eq_one_iff hxy_mem).mpr ⟨⟨xpy, rfl⟩⟩
  have hmk_𝔭 : ClassGroup.mk0 ⟨𝔭, h𝔭_mem⟩ = 1 :=
    (ClassGroup.mk0_eq_one_iff h𝔭_mem).mpr ⟨⟨s, rfl⟩⟩
  have hmk_eq : ClassGroup.mk0 ⟨Ideal.span ({xpy} : Set (𝓞 K'')), hxy_mem⟩ =
      ClassGroup.mk0 ⟨𝔭, h𝔭_mem⟩ ^ (37 * m + 1) * ClassGroup.mk0 ⟨𝔞₀, h𝔞₀_mem⟩ ^ 37 := by
    rw [← map_pow, ← map_pow, ← map_mul]
    congr 1
    exact Subtype.ext (by
      rw [Submonoid.coe_mul, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]; exact hfact)
  rw [hmk_xy, hmk_𝔭, one_pow, one_mul] at hmk_eq
  exact hmk_eq.symm

/-- **[OBSTRUCTION] In the real frame, `𝔞₀²` principal forces `𝔞₀` principal** (axiom-clean).

Given the anchor-cube factorization `span(x+y) = 𝔭^{37m+1}·𝔞₀³⁷` (proven
`caseII_span_x_add_y_eq_anchorCube`; threaded as `hfact`), if the **square** `𝔞₀²` of the `𝔭`-free
anchor is principal, then `𝔞₀` itself is principal.  Mechanism: `[𝔞₀]² = 1` (the hypothesis) and
`[𝔞₀]³⁷ = 1` (`caseII_anchorClass_pow37_eq_one_of_anchorCube`) force `[𝔞₀]^{gcd(2,37)} = [𝔞₀]¹ = 1`,
i.e. `𝔞₀` principal.

**This is the precise obstruction to the conjugate-norm assembly in the real frame.** Washington's
new variable `ξ₁ = ρ₀σρ₀` has `(ξ₁) = 𝔞₀·σ𝔞₀ = 𝔞₀²` (real frame: `η₀ = 1` so `σ𝔞₀ = 𝔞₀`,
`caseII_map_a_eta_zero`); for `ξ₁` to be an **integer** (so the descended free-content datum is
valid) `𝔞₀²` must be principal — which, by this lemma, forces `𝔞₀` principal.  But `𝔞₀` is *not*
principal in Case II (it carries the non-trivial anchored class; the descent exists to drop its
non-anchor support).  So the conjugate norm does **not** supply an integer Fermat variable at the
**single** measure `𝔞₀²`: the only principal power is at the **doubled** measure `𝔞₀^{2k'}`
(`2k' = 2|Cl|`, `caseII_anchorPow_conjNorm_real_span`).  Equivalently, the descended Fermat variable
is an integer **iff** the anchored class is `2`-torsion — the open Washington-9.4 / II1 second-order
content (`CaseIIAdjacentAnchoredClassTwoTorsion37`, `CaseIISingleRootDescent.lean`; needs Kellner).
**Soundness-critical**: this *refutes* the claim that `𝔞₀·σ𝔞₀ = 𝔞₀²` is "freely principal via
`37 ∤ h⁺`" in the real frame (it is principal iff the `2`-torsion content holds). -/
theorem caseII_anchorSq_principal_imp_principal_of_anchorCube {m : ℕ}
    {xpy s : 𝓞 K''} {𝔞₀ : Ideal (𝓞 K'')}
    (hfact : Ideal.span ({xpy} : Set (𝓞 K'')) =
      Ideal.span ({s} : Set (𝓞 K'')) ^ (37 * m + 1) * 𝔞₀ ^ 37)
    (hs_ne : s ≠ 0) (hxpy_ne : xpy ≠ 0) (h𝔞₀_ne : 𝔞₀ ≠ 0)
    (hsq : (𝔞₀ ^ 2).IsPrincipal) :
    𝔞₀.IsPrincipal := by
  have h𝔞₀_mem : 𝔞₀ ∈ (Ideal (𝓞 K''))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞₀_ne
  set c := ClassGroup.mk0 (⟨𝔞₀, h𝔞₀_mem⟩ : (Ideal (𝓞 K''))⁰) with hc_def
  have hc2 : c ^ 2 = 1 := by
    rw [hc_def, ← map_pow]
    refine (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 2 h𝔞₀_ne))).mpr ?_
    -- the coercion `↑(⟨𝔞₀,_⟩^2) = (↑⟨𝔞₀,_⟩)^2 = 𝔞₀^2`.
    have hcoe : ((⟨𝔞₀, h𝔞₀_mem⟩ : (Ideal (𝓞 K''))⁰) ^ 2 : Ideal (𝓞 K'')) = 𝔞₀ ^ 2 :=
      SubmonoidClass.coe_pow _ 2
    rw [hcoe]; exact hsq
  have hc37 : c ^ 37 = 1 := caseII_anchorClass_pow37_eq_one_of_anchorCube hfact hs_ne hxpy_ne h𝔞₀_ne
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hc37)
  rw [show Nat.gcd 2 37 = 1 from by decide] at hdvd
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  exact (ClassGroup.mk0_eq_one_iff h𝔞₀_mem).mp hc1

end Obstruction

end BernoulliRegular.FLT37.Eichler

end

end
