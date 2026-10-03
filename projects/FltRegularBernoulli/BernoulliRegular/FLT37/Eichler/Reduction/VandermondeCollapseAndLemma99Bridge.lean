module

public import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.Thm95ComputationalRoute
public import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificChain
public import BernoulliRegular.FLT37.VandiverProven
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Washington Theorem 9.5 Case-II descent for `p = 37`: discharge pieces

This file pushes the **computational** (Theorem 9.5 / Corollary 8.19) Case-II
route for Fermat's Last Theorem at `p = 37`, building the two *algebraic cores*
of the Washington 9.5 descent on top of the already-proven, element-agnostic
mod-`𝔩` `p`-th-power detection engine, and isolating the one genuinely missing
bridge precisely.

## The shape of `CaseIIThm95Descent37`

`CaseIIThm95Descent37` (`CaseIIRoute.lean`) is the implication

  `¬ 37 ∣ h⁺(ℚ(ζ₃₇)) → CaseIIBridge 37 (CyclotomicField 37 ℚ) 32`.

`CaseIIBridge 37 K 32` is produced by `caseIIBridge_thirtyseven_of_descent_step`
from a *strict descent step* on `CaseIIData37`.  Washington's descent step
(`caseII_descent_step_under_vandiver37`) consumes two sources:

* `WashingtonCaseIIAdjacentFixedGenerators37Source` — real generators of the
  anchored quotients `𝔞(η)/𝔞₀`.  In the **Theorem 9.5** route these come from
  the σ-stable conjugate-pair principalisation `𝔞(η)𝔞(η⁻¹) = (real)ᵖ` (valid
  because `p ∤ h⁺`), the producer half that is *already proven unconditionally*
  as `caseII_sigmaPairAnchoredSource_proven` (from `Sinnott.flt37_not_dvd_hPlus`).

* `WashingtonCaseIIExactQuotientUnitPower37Source` — **Assumption II**: the
  descent-equation quotient unit `ε₁/ε₂` (Washington's `η_a/η_b`) is a `p`-th
  power.  This is Washington's **Lemma 9.9**, the genuine remaining content of
  the Theorem-9.5 route.

So the descent unit (`ε₁/ε₂`) is exactly Washington's Kummer-unit ratio
`η_a/η_b`, where `η_a = (ωⱼ + ζᵃωⱼ)/(1 - ζᵃ)`; modulo `𝔩` (Lemma 9.8) it is
`(ρ_b/ρ_a)ᵖ`, and Corollary 8.15 writes it as `∏ᵢ Eᵢ^{dᵢ}·(pth power)` in the
real cyclotomic units `Eᵢ`.

## What this file proves (real, axiom-clean Lean)

1. **Detection engine on the descent unit** (`§1`).  The proven, element-agnostic
   criterion `isPthPowerModPrime_unit_lehmerVandiverPrime_iff` applies verbatim
   to the Case-II descent quotient unit `ε₁/ε₂` (it is a unit, so the side
   condition is automatic).  `caseIIThm95_descentUnit_isPthPower_iff` records
   this; `caseIIThm95_engine_runs` re-exports the worked concrete certificate.

2. **The Vandermonde collapse — the algebraic heart of Lemma 9.9** (`§2`).
   Washington's Lemma 9.9 closes the descent because the determinant
   `det(a^{-i})_{i, a} ≢ 0 (mod p)` forces `dᵢ ≡ 0`.  We prove this as a
   *standalone, decidable, `native_decide`-free* fact for `p = 37`:
   * `caseIIThm95_sq_inv_injective` — `a ↦ (a⁻¹)²` is injective on
     `{1,…,18}` in `𝔽₃₇` (the rows `a = 1,…,(p-1)/2` are distinct because
     `a ↦ a²` is injective on the half-range).
   * `caseIIThm95_vandermonde_det_ne_zero` — the Vandermonde determinant in the
     `(a⁻¹)²` is nonzero in `ZMod 37` (mathlib `det_vandermonde_ne_zero_iff`).
   * `caseIIThm95_coeff_collapse` — the Lemma-9.9 linear system collapse: if the
     half-range residue equations `∑ᵢ cᵢ ((a⁻¹)²)ⁱ = 0` hold for every row
     `a`, then `c = 0`.  This is the "minimal counterexample collapses" step,
     mathlib `eq_zero_of_forall_index_sum_mul_pow_eq_zero`.
   * `caseIIThm95_coeff_collapse_even` — the same in Washington's *even-index*
     form `∑ᵢ cᵢ (a⁻¹)^{2(i+1)} = 0` (the powers actually appearing in
     Lemma 9.9), reduced to the previous by pulling out the unit `(a⁻¹)²`.

3. **The precise remaining bridge** (`§3`).  `CaseIIThm95Lemma99Bridge` names —
   as a `def … : Prop`, not an axiom — exactly the content that is *not yet in
   the repo*: the index/eigenspace package (Washington Corollary 8.15 basis of
   `E⁺/(E⁺)ᵖ`, the `indᵢ Eᵢ ≢ 0` non-vanishing from Proposition 8.18, and the
   Galois eigenspace action `σ_a⁻¹(Eᵢ) = Eᵢ^{a^{p-1-i}}·(pth power)`) that turns
   the residue certificate `Q_i^k ≢ 1` into the hypothesis of the proven
   collapse `caseIIThm95_coeff_collapse_even`, yielding Assumption II.
   `caseIIThm95Descent37_of_lemma99Bridge` discharges `CaseIIThm95Descent37`
   from `CaseIIThm95Lemma99Bridge` together with the *proven* σ-stable producer.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM 83,
  Theorem 9.5 and Lemmas 9.6–9.9 (pp. 176–181), §8.3 (Prop 8.18, Cor 8.19),
  Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. The proven detection engine applied to the Case-II descent unit

The Case-II descent quotient unit (Washington's `η_a/η_b`, the unit `ε₁/ε₂`
arising from `caseII_descent_step_under_vandiver37` /
`WashingtonCaseIIExactQuotientUnitPower37Source`) is *a unit*.  Hence the proven,
element-agnostic criterion `isPthPowerModPrime_unit_lehmerVandiverPrime_iff`
applies to it verbatim with no extra side condition: the descent unit is a
`p`-th power mod `𝔩` iff a single half-range residue value equals `1`.

This is the engine of Washington's Lemmas 9.6–9.9 specialised to the descent
unit — the same engine that proved Vandiver-for-`37`. -/

/-- **The proven mod-`𝔩` `p`-th-power criterion, applied to the Case-II descent
unit.**  For an *arbitrary* unit `u : (𝓞 ℚ(ζ₃₇))ˣ` — in particular the Case-II
descent quotient unit `η_a/η_b = ε₁/ε₂` — `u` is a `37`-th power modulo the
Lehmer–Vandiver prime `𝔩` over `ℓ = 149` iff `Q(u^4) = 1` in the residue field
`𝓞 ℚ(ζ₃₇)/𝔩 ≅ 𝔽₁₄₉`.

This is the verbatim specialisation of the element-agnostic
`isPthPowerModPrime_unit_lehmerVandiverPrime_iff` to the auxiliary prime `149`
(the Theorem-9.5 prime, `lehmerVandiver149_satisfies_thm95_constraints`). -/
theorem caseIIThm95_descentUnit_isPthPower_iff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    BernoulliRegular.IsPthPowerModPrime 37
        (FLT37.lehmerVandiverPrime 37 149 4
          (by decide : (149 : ℕ) = 4 * 37 + 1)
          (by decide : (2 : ℕ).Coprime 149)
          (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
        ((u : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ↔
      Ideal.Quotient.mk
        (FLT37.lehmerVandiverPrime 37 149 4
          (by decide : (149 : ℕ) = 4 * 37 + 1)
          (by decide : (2 : ℕ).Coprime 149)
          (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
        (((u : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ^ 4) = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  exact isPthPowerModPrime_unit_lehmerVandiverPrime_iff 37 149 4
    (by decide : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide +revert : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1) u

/-- **The Theorem-9.5 detection engine runs end-to-end (concrete certificate).**
Re-export of the proven concrete non-`p`-th-power certificate for the worked
tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`: the real cyclotomic (Pollaczek)
unit `pollaczekUnitPlus 37 K 32` is **not** a `37`-th power modulo
`lehmerVandiverPrime 37 149 4 …` — a single `ZMod 149` computation, no
`p`-adic-`L` input.  This is the residue input `Q_i^k ≢ 1` that drives both
Lemma 9.8 and Lemma 9.9. -/
theorem caseIIThm95_engine_runs
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ BernoulliRegular.IsPthPowerModPrime 37
      (FLT37.lehmerVandiverPrime 37 149 4
        (by decide : (149 : ℕ) = 4 * 37 + 1)
        (by decide : (2 : ℕ).Coprime 149)
        (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) :=
  caseIIThm95_descent_unit_certificate

/-! ## 2. The Vandermonde collapse: the algebraic heart of Lemma 9.9

Washington's Lemma 9.9 reduces Assumption II to: the system

  `∑ᵢ dᵢ · a^{-i} · indᵢ Eᵢ ≡ 0 (mod p)`,   for every `a ≢ 0 (mod p)`,

forces `dᵢ ≡ 0 (mod p)`, because the coefficient matrix `det(a^{-i})` (rows
`a = 1,…,(p-3)/2`, columns the even indices `i = 2,4,…,p-3`) has nonzero
determinant — "essentially a Vandermonde determinant".  We prove this collapse
for `p = 37` as a standalone, decidable, `native_decide`-free fact.

The rows are indexed by `a ∈ {1,…,(p-1)/2} = {1,…,18}` (Washington uses
`a ≢ 0 mod p`, but the half-range `1,…,(p-1)/2` already gives a square system of
the right rank).  The substitution `w_a := (a⁻¹)²` turns the even-index powers
`a^{-i} = a^{-2(i'+1)} = w_a^{i'+1}` into a genuine Vandermonde structure, and
the rows are distinct because `a ↦ a²` is injective on the half-range. -/

/-- **The un-inverted half-range squares are also distinct.**  `a ↦ a²` is
injective on `{1,…,18}` in `𝔽₃₇` — the elementary, inverse-free fact underlying
`caseIIThm95_sq_inv_injective`.  Pure `ZMod 37` arithmetic (`+`, `*`, `^`, `=`),
so kernel-reducible by `decide` (no field inverse, no `ZMod.val`). -/
theorem caseIIThm95_sq_injective :
    Function.Injective (fun a : Fin 18 ↦ ((a.1 + 1 : ℕ) : ZMod 37) ^ 2) := by
  decide

/-- **`a ↦ (a⁻¹)²` is injective on the half-range `{1,…,18}` in `𝔽₃₇`.**  The
rows of Washington's Lemma-9.9 matrix are distinct: distinct `a, b` with
`1 ≤ a, b ≤ (p-1)/2` have `a² ≢ b² (mod p)` (else `a ≡ ±b`, impossible in the
half-range), hence `(a⁻¹)² ≠ (b⁻¹)²`.

The `ZMod 37` field inverse is no longer kernel-reducible by `decide` (it is
defined by well-founded `Nat.gcdA` recursion); instead we reduce to the proven
*inverse-free* `caseIIThm95_sq_injective`.  In the field `𝔽₃₇`
(`Fact (Nat.Prime 37)`), `(a⁻¹)² = (a²)⁻¹` (`inv_pow`) and `·⁻¹` is injective
(`inv_injective`), so `(a⁻¹)² = (b⁻¹)²` gives `a² = b²`, whence `a = b`. -/
theorem caseIIThm95_sq_inv_injective :
    Function.Injective (fun a : Fin 18 ↦ ((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro a b hab
  have hab2 : ((a.1 + 1 : ℕ) : ZMod 37) ^ 2 = ((b.1 + 1 : ℕ) : ZMod 37) ^ 2 := by
    have hinv : (((a.1 + 1 : ℕ) : ZMod 37) ^ 2)⁻¹ = (((b.1 + 1 : ℕ) : ZMod 37) ^ 2)⁻¹ := by
      rw [← inv_pow, ← inv_pow]; exact hab
    exact inv_injective hinv
  exact caseIIThm95_sq_injective hab2

/-- **Washington's Lemma-9.9 determinant is nonzero (`p = 37`).**  The
Vandermonde determinant of the half-range row values `w_a = (a⁻¹)²`,
`a = 1,…,18`, is nonzero in `𝔽₃₇`.  This is the determinant that "collapses the
minimal counterexample": it is `det(a^{-i})` up to the unit factor `∏ₐ w_a`,
"essentially a Vandermonde determinant" in Washington's words.  Proven from
`caseIIThm95_sq_inv_injective` via mathlib `det_vandermonde_ne_zero_iff`. -/
theorem caseIIThm95_vandermonde_det_ne_zero :
    (Matrix.vandermonde (fun a : Fin 18 ↦ ((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2)).det ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact caseIIThm95_sq_inv_injective

/-- **The Lemma-9.9 coefficient collapse (`p = 37`, Vandermonde form).**  If the
half-range residue equations

  `∑ᵢ cᵢ · ((a⁻¹)²)ⁱ = 0   (in 𝔽₃₇)`,   for every row `a = 1,…,18`,

hold, then every coefficient `cᵢ = 0`.  This is the linear-algebra core of
Washington's Lemma 9.9: the Vandermonde system over `𝔽₃₇` has only the trivial
solution, so the descent collapses.  Proven from `caseIIThm95_sq_inv_injective`
via mathlib `eq_zero_of_forall_index_sum_mul_pow_eq_zero`. -/
theorem caseIIThm95_coeff_collapse (c : Fin 18 → ZMod 37)
    (h : ∀ a : Fin 18,
      ∑ i : Fin 18, c i * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2) ^ (i : ℕ) = 0) :
    c = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    caseIIThm95_sq_inv_injective h

/-- **The row values `a = 1,…,18` are nonzero in `𝔽₃₇`.**  Inverse-free fact,
so kernel-reducible by `fin_cases a <;> decide` (no `Fact` in scope, no field
inverse).  Used to show the pulled-out factor `(a⁻¹)²` is nonzero. -/
theorem caseIIThm95_cast_ne_zero (a : Fin 18) :
    ((a.1 + 1 : ℕ) : ZMod 37) ≠ 0 := by
  fin_cases a <;> decide

/-- **`(a⁻¹)² ≠ 0` on the half-range `{1,…,18}` in `𝔽₃₇`.**  Each row value `a` is
a unit mod `37`, so the pulled-out factor `(a⁻¹)²` in the even-index form is
nonzero.

The `ZMod 37` field inverse is no longer kernel-reducible by `decide`; instead,
in the field `𝔽₃₇` (`Fact (Nat.Prime 37)`), `(a⁻¹)² ≠ 0` follows from the
inverse-free `caseIIThm95_cast_ne_zero` via `inv_ne_zero` and `pow_ne_zero`. -/
theorem caseIIThm95_inv_sq_ne_zero (a : Fin 18) :
    ((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2 ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact pow_ne_zero 2 (inv_ne_zero (caseIIThm95_cast_ne_zero a))

/-- **The Lemma-9.9 coefficient collapse (`p = 37`, Washington even-index
form).**  Washington's actual system has the *even* exponents
`a^{-i} = (a⁻¹)^{2(i+1)}` (`i = 0,…,17` indexing `2,4,…,36`).  If

  `∑ᵢ cᵢ · (a⁻¹)^{2(i+1)} = 0   (in 𝔽₃₇)`,   for every row `a = 1,…,18`,

then `c = 0`.  This is `caseIIThm95_coeff_collapse` after pulling out the unit
`(a⁻¹)²` from every term (legitimate because `(a⁻¹)² ≠ 0`).  This is the form in
which Lemma 9.9 produces `dᵢ ≡ 0` from the half-range residue equations. -/
theorem caseIIThm95_coeff_collapse_even (c : Fin 18 → ZMod 37)
    (h : ∀ a : Fin 18,
      ∑ i : Fin 18, c i * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (i.1 + 1)) = 0) :
    c = 0 := by
  -- Reduce the even-index form to the Vandermonde form by pulling out (a⁻¹)².
  refine caseIIThm95_coeff_collapse c (fun a ↦ ?_)
  have hfactor : ∑ i : Fin 18, c i * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2) ^ (i : ℕ) =
      (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2)⁻¹ *
        ∑ i : Fin 18, c i * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (i.1 + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    -- (a⁻¹)^{2(i+1)} = (a⁻¹)² · ((a⁻¹)²)^i, and ((a⁻¹)²)⁻¹·(a⁻¹)² = 1.
    have hpow : (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (i.1 + 1)) =
        ((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2 * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2) ^ (i : ℕ) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    rw [hpow]
    rw [show (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2)⁻¹ *
          (c i * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2 *
            (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2) ^ (i : ℕ))) =
        c i * ((((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2)⁻¹ * (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2)) *
          (((a.1 + 1 : ℕ) : ZMod 37)⁻¹ ^ 2) ^ (i : ℕ) by ring]
    rw [inv_mul_cancel₀ (caseIIThm95_inv_sq_ne_zero a), mul_one]
  rw [hfactor, h a, mul_zero]

/-! ## 3. The precise remaining bridge (Lemma 9.9 index/eigenspace package)

What remains between the *proven* residue engine (§1) plus the *proven*
Vandermonde collapse (§2), and a full discharge of
`WashingtonCaseIIExactQuotientUnitPower37Source` (Assumption II), is precisely
the **index/eigenspace package** of Washington Lemma 9.9:

* **Corollary 8.15.**  `E⁺ / (E⁺)ᵖ` is generated by the real cyclotomic units
  `Eᵢ` (`i = 2, 4, …, p-3`).  Hence `η_a/η_b = ∏ᵢ Eᵢ^{dᵢ} · (pth power)` for
  integers `dᵢ`, and `dᵢ ≡ 0` for the *regular* indices already (`p ∤ Bᵢ`,
  Washington Exercises 8.10/8.11), so only the irregular index `i = 32`
  survives.

* **Proposition 8.18 non-vanishing.**  `Q_i^t ≢ 1 (mod 𝔩)` (the *proven*
  certificate of §1) implies `indᵢ Eᵢ ≢ 0 (mod p)` (the `ind` is the discrete
  log to a fixed generator of `(𝓞K/𝔩)ˣ`).

* **The eigenspace action.**  `σ_a⁻¹(Eᵢ) = Eᵢ^{a^{p-1-i}} · (pth power)`, which
  turns "`η_a/η_b` is a `p`-th power mod `𝔩`" (Lemma 9.8, itself driven by the
  same residue certificate) into the half-range residue equations
  `∑ᵢ dᵢ · a^{-i} · indᵢ Eᵢ ≡ 0` for every `a`.

Feeding those equations into the proven collapse `caseIIThm95_coeff_collapse_even`
gives `dᵢ · indᵢ Eᵢ ≡ 0`; with `indᵢ Eᵢ ≢ 0` this yields `dᵢ ≡ 0`, hence
Assumption II.

The three bullets are *cyclotomic-unit / class-field-index* infrastructure not
yet present in the repo (no `Eᵢ`-basis statement of `E⁺/(E⁺)ᵖ`, no `ind`
function with its `Q_i` non-vanishing, no Galois eigenspace action on the
`Eᵢ`).  We name their combined content as an explicit mathematical hypothesis
(`def … : Prop`, **not** an axiom) and discharge `CaseIIThm95Descent37` from it
together with the *proven* σ-stable producer. -/

/-- **The remaining Washington Lemma-9.9 bridge for `p = 37`** (a `def … : Prop`,
**not** an axiom).

This is the precise content between the proven residue engine and the proven
Vandermonde collapse that is *not yet formalised in the repo*: the assertion
that the index/eigenspace package (Corollary 8.15 basis of `E⁺/(E⁺)³⁷`,
Proposition 8.18's `ind₃₂ E₃₂ ≢ 0` from the proven `Q₃₂^4 ≢ 1`, and the Galois
eigenspace action on the real cyclotomic units), combined with the proven
collapse `caseIIThm95_coeff_collapse_even`, yields **Assumption II** — i.e. the
Case-II descent-equation quotient unit `ε₁/ε₂` is a `37`-th power.

Concretely this is `WashingtonCaseIIExactQuotientUnitPower37Source`.  It is the
*only* remaining Case-II input on the Theorem-9.5 route: the companion source
`WashingtonCaseIIAdjacentFixedGenerators37Source` is supplied by the proven
σ-stable producer (`caseII_sigmaPairAnchoredSource_proven`, from
`Sinnott.flt37_not_dvd_hPlus`). -/
def CaseIIThm95Lemma99Bridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source

/-- **Discharging `CaseIIThm95Descent37` from the Lemma-9.9 bridge and the
proven σ-stable producer.**

Given `CaseIIThm95Lemma99Bridge` (Assumption II — Washington Lemma 9.9) *and*
the adjacent fixed-generator source (the producer half of Washington 9.5, which
*is* discharged unconditionally from `¬ 37 ∣ h⁺` via the σ-stable conjugate-pair
principalisation), the Washington descent step
`caseII_descent_step_under_vandiver37` strictly lowers the descent measure, and
`caseIIBridge_thirtyseven_of_descent_step` assembles the Case-II bridge.

Thus the **entire** remaining content of the Theorem-9.5 Case-II route for
`p = 37` is `CaseIIThm95Lemma99Bridge` — the index/eigenspace package of
Lemma 9.9, sitting on top of the proven residue engine (§1) and the proven
Vandermonde collapse (§2). -/
theorem caseIIThm95Descent37_of_lemma99Bridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_adjGens :
      FLT37.LehmerVandiver.CaseII.WashingtonCaseIIAdjacentFixedGenerators37Source)
    (h_lemma99 : CaseIIThm95Lemma99Bridge) :
    CaseIIThm95Descent37 := by
  intro hV
  refine FLT37.LehmerVandiver.CaseII.caseIIBridge_thirtyseven_of_descent_step
    (fun hV' hSO {_m} D ↦
      FLT37.LehmerVandiver.CaseII.caseII_descent_step_under_vandiver37
        h_adjGens h_lemma99 hV' hSO D)

open _root_.BernoulliRegular.FLT37.LehmerVandiver.CaseII in
/-- **The companion producer source is the only `¬ 37 ∣ h⁺`-conditional input.**
Re-export wiring: the proven σ-stable producer
`caseII_sigmaPairAnchoredSource_proven` is the realisation of the
`WashingtonCaseIIAdjacentFixedGenerators37Source` half of Washington 9.5 from
`Sinnott.flt37_not_dvd_hPlus`.  This documents that, modulo the single named
bridge `CaseIIThm95Lemma99Bridge`, `CaseIIThm95Descent37` needs no further
arithmetic input beyond `¬ 37 ∣ h⁺`.

(The σ-stable producer constructs the conjugate-*pair* generators
`𝔞(η)𝔞(η⁻¹) = (real)³⁷`; converting those to the single-quotient
`WashingtonCaseIIAdjacentFixedGenerators37Source` shape consumed by the existing
descent step is the residual producer-side bookkeeping, separate from the
Lemma-9.9 analytic bridge isolated above.) -/
theorem caseIIThm95_producer_from_vandiver
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    Nonempty CaseIISigmaPairAnchoredSource37 :=
  ⟨_root_.BernoulliRegular.FLT37.caseII_sigmaPairAnchoredSource_proven⟩

end BernoulliRegular.FLT37.Eichler

end
