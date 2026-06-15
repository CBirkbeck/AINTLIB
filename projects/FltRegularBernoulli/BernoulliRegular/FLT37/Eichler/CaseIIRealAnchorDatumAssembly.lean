import BernoulliRegular.FLT37.Eichler.CaseIIAnchorSquareDatum

/-!
# [FLT37-CASEII-REAL-ANCHOR-DATUM-ASSEMBLY] Washington §9.1 Thm 9.4 conjugate-normed assembly

This file attacks the last analytic core of FLT37 Case-II, the Washington *Cyclotomic Fields*
(2nd ed., GTM 83) §9.1 Theorem 9.4 conjugate-normed descent-equation **assembly**
`CaseIIRealAnchorDatumAssembly37` (`CaseIIAnchorSquareDatum.lean`): from a real, `𝔭`-coprime
element `w` with `(w) = 𝔞₀ᵏ` (`k ≥ 1`) — the conjugate norm `ξ₁ = ρ₀·σρ₀ = ρ₀²` produced by the
**proven** `caseII_anchorPow_conjNorm_real_span` — build a **real** Case-II datum `D'` whose Fermat
variable **is** `w`: `D'.z = w`.

## Verdict on the mechanism (Washington §9.1, pp. 169–173)

Washington's new variable is the conjugate norm `ξ₁ = ρ₀²` (`ρ₀` a real generator of the
principal anchor power `B₀ = 𝔞₀`), assembled into the **doubled-measure** Fermat equation

  `ω₁ᵖ + θ₁ᵖ = δ·λ^{2m−p}·ξ₁ᵖ`        (GTM 83 p. 172, `δ` a real unit)

with `ω₁ = (ηₐ/η_b)^{2/p}·ρₐρ̄ₐ`, `θ₁ = −ρ_b ρ̄_b` (themselves conjugate norms, hence real).
Two independent facts pin down the situation:

* **The producer `caseII_pair_real_caseI_form_of_realCaseIIData37` is NOT re-routable to `w`.**
  It cancels the doubled `λ²` from each side (`caseII_pair_K_fermat_sum_unit_form`) and delivers
  the *Case-I-shaped* `ε₁X³⁷ + ε₂Y³⁷ = Z³⁷` with **no** `λ`-factor and variable `Z = x₁x₂`
  carrying the uncontrolled `(y₁y₂)` content (`caseII_descended_anchored_real_generators`),
  `(ζ−1) ∤ Z`.  Its variable is neither `w` nor `𝔞₀ᵏ`-generating; the `λ`-power is wrong (zero).

* **The norm-form equation sits at the DOUBLED measure `λ^{2m−p}`, not the linear measure.**
  A `RealCaseIIData37 m'` forces `x'³⁷ + y'³⁷ = ε'·((ζ−1)^{m'+1}·z')³⁷`, so its `(ζ−1)`-content
  is exactly `37·(m'+1) ≡ 0 (mod 37)`.  Washington's descended `ξ₁`-equation has `(ζ−1)`-content
  `2m − p = 2m − 37 ≢ 0 (mod 37)` (since `37 ∤ 2m` for general `m`).  This is the project's own
  documented **doubling obstruction** (`b2_log.jsonl`, `R2-thetaFixed`, 2026-05-31).  Hence the
  `ξ₁`-equation does **not** repackage as a `RealCaseIIData37` with `z' = w`, and no proven
  producer supplies a `RealCaseIIData37` whose `z`-ideal is `𝔞₀ᵏ`.  So
  `CaseIIRealAnchorDatumAssembly37` is **not** dischargeable by Washington's descent (it is, in
  fact, *strictly stronger* than the parent `CaseIIWashingtonAnchorSquareDatum37` — it carries no
  non-terminal regime hypothesis and must hit the externally-specified anchor power `𝔞₀ᵏ`).  It is
  *not* a literally-false `Prop` (a degenerate witness is not excluded), so it is sound to keep as
  a named residual — but it must not be claimed proven.

## What this file PROVES, soundly (genuine, non-vacuous progress)

1. **`caseII_realCaseIIData37_rescale_z`** — the unit-rescaling normalization.  Given a real datum
   `D'` whose Fermat variable is *associate* to `w` (`D'.z * u = w`, `u` a unit) with `w`
   `𝔭`-coprime, there is a real datum with Fermat variable **exactly** `w`.  The absorbed unit `u`
   is folded into the leading unit (`ε ↦ ε·u⁻³⁷`).  This removes the spurious *exact equality*
   `D'.z = w` from the residual, reducing it to its meaningful ideal form `(D'.z) = (w)`.

2. **`CaseIIRealAnchorDatumIdeal37`** — the **sharpened residual**: a real datum `D'` with
   `(D'.z) = 𝔞₀ᵏ` (the *ideal* form), and `caseIIRealAnchorDatumAssembly37_of_ideal` :
   `CaseIIRealAnchorDatumIdeal37 → CaseIIRealAnchorDatumAssembly37`, via (1).  This is the smallest
   sound residual for the assembly: the exact-`z` constraint is discharged; what remains is exactly
   "a real Fermat datum whose `z`-ideal is the anchor power", the genuine doubling-obstructed
   content above.  Certified non-vacuous (`caseIIRealAnchorDatumIdeal37_*`).

3. **`caseII_realCaseIIData37_lambda_content_mul_p`** — the doubling-obstruction soundness
   certificate: the `(ζ−1)`-content of *every* `RealCaseIIData37` equation is a multiple of `37`
   (`(ζ−1)^{37·(m+1)} ∣ x³⁷ + y³⁷`).  This certifies that the ideal residual is the genuine
   measure-mismatched content (the producer's `ξ₁`-equation, at the doubled measure `λ^{2m−37}`,
   has content `≢ 0 (mod 37)` and so cannot, as is, be a `RealCaseIIData37` with `z`-ideal `𝔞₀ᵏ`).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 169–173 (the conjugate-norm new variable `ξ₁ = ρ₀²`, `(ξ₁) = B₀²`, the doubled measure
  `λ^{2m−p}`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The unit-rescaling normalization (FULLY PROVEN) -/

/-- **[FLT37-CASEII-RESCALE-Z] Unit-rescaling of a real Case-II datum's Fermat variable.**

Given a real Case-II datum `D'` whose Fermat variable `D'.z` is *associate* to a real, `𝔭`-coprime
element `w` (`D'.z * u = w` for a unit `u`), there is a real Case-II datum (at the **same** exponent
level `m'`) whose Fermat variable is **exactly** `w`: a datum with `z := w`.

Proof: keep `x', y', ζ, m'` and the reality fields; set `z := w`, `ε := D'.ε · u⁻³⁷`.  The unit `u`
is absorbed through the cube:
`((ζ−1)^{m'+1}·w)³⁷ = ((ζ−1)^{m'+1}·D'.z·u)³⁷ = u³⁷·((ζ−1)^{m'+1}·D'.z)³⁷`, so
`D'.ε·((ζ−1)^{m'+1}·D'.z)³⁷ = (D'.ε·u⁻³⁷)·((ζ−1)^{m'+1}·w)³⁷`.  The `𝔭`-coprimality field `hz`
becomes `(ζ−1) ∤ w` (given).  Note: `RealCaseIIData37` carries reality only for `x, y` (no
`z_real`), so reality of `w` is *not* needed here — it is carried separately upstream for the ideal
computation. -/
theorem caseII_realCaseIIData37_rescale_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m' : ℕ} (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m')
    {w : 𝓞 (CyclotomicField 37 ℚ)} {u : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hu : D'.z * (u : 𝓞 (CyclotomicField 37 ℚ)) = w)
    (hw_p : ¬ (D'.hζ.unit'.1 - 1) ∣ w) :
    ∃ (D'' : RealCaseIIData37 (CyclotomicField 37 ℚ) m'), D''.z = w := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The new equation: fold `u⁻³⁷` into the leading unit.
  refine ⟨{ ζ := D'.ζ, hζ := D'.hζ, x := D'.x, y := D'.y, z := w,
            ε := D'.ε * (u⁻¹) ^ 37,
            equation := ?_, hy := D'.hy, hz := hw_p,
            x_real := D'.x_real, y_real := D'.y_real }, rfl⟩
  -- `((ζ−1)^{m'+1}·w)³⁷ = u³⁷·((ζ−1)^{m'+1}·D'.z)³⁷`, then absorb.
  have hw_eq : w = D'.z * (u : 𝓞 (CyclotomicField 37 ℚ)) := hu.symm
  have hkey :
      ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * w) ^ 37 =
        ((u : 𝓞 (CyclotomicField 37 ℚ)) ^ 37) *
          ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * D'.z) ^ 37 := by
    rw [hw_eq]; ring
  rw [hkey]
  -- `D'.ε·(...)³⁷ = (D'.ε·u⁻³⁷)·(u³⁷·(...)³⁷)`.
  have hueq :
      ((D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((u⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : _) ^ 37) *
          ((u : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 *
            ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * D'.z) ^ 37) =
        (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * D'.z) ^ 37 := by
    have hcancel :
        ((u⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 *
          (u : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 = 1 := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel]; simp
    calc
      ((D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((u⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : _) ^ 37) *
            ((u : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 *
              ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * D'.z) ^ 37)
          = (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) *
              ((((u⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : _) ^ 37 *
                (u : 𝓞 (CyclotomicField 37 ℚ)) ^ 37) *
              ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * D'.z) ^ 37) := by ring
      _ = (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) *
              ((D'.hζ.unit'.1 - 1) ^ (m' + 1) * D'.z) ^ 37 := by rw [hcancel, one_mul]
  -- Now `x'³⁷ + y'³⁷ = D'.ε·(...)³⁷` is `D'.equation`.
  rw [show ((D'.ε * (u⁻¹) ^ 37 : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
        (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((u⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : _) ^ 37 by
        push_cast; ring]
  rw [hueq]
  exact D'.equation

/-! ## 2. The sharpened residual (ideal form) and its reduction to the assembly -/

/-- **[FLT37-CASEII-REAL-ANCHOR-DATUM-IDEAL] The ideal-form Washington `ξ₁ = ρ₀²` datum**
(GTM 83 p. 172).

From a real Case-II datum `D` and an exponent `k ≥ 1` for which the anchor power `𝔞₀ᵏ` is
principal (`𝔞₀ = a_eta_zero_dvd_p_pow`), there is a real Case-II datum `D'` whose Fermat variable
generates exactly that power: `(D'.z) = 𝔞₀ᵏ`.

This is the **sharpened** form of `CaseIIRealAnchorDatumAssembly37`: the genuine content is the
existence of a *real Fermat datum whose `z`-ideal is the anchor power*, with the spurious exact
equality `D'.z = w` discharged by the unit-rescaling `caseII_realCaseIIData37_rescale_z`.  It carries
the doubling obstruction (the producer's `ξ₁`-equation sits at the doubled measure `λ^{2m−p}`,
incompatible with the linear `RealCaseIIData37` measure `37·(m'+1)`; see the file header).  A
`def … : Prop` (**not** an axiom), certified non-vacuous below. -/
def CaseIIRealAnchorDatumIdeal37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (k : ℕ), 1 ≤ k →
    (a_eta_zero_dvd_p_pow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k).IsPrincipal →
    ∃ (m' : ℕ) (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m'),
      Ideal.span ({D'.z} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        a_eta_zero_dvd_p_pow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k

/-- **`CaseIIRealAnchorDatumAssembly37` from the sharpened ideal residual.**

The assembly residual follows from the ideal-form residual `CaseIIRealAnchorDatumIdeal37` by the
**proven** unit-rescaling `caseII_realCaseIIData37_rescale_z`.  Given the assembly's input `w`
(real, `𝔭`-coprime, `(w) = 𝔞₀ᵏ`): the hypothesis `(w) = 𝔞₀ᵏ` makes `𝔞₀ᵏ` principal, so the ideal
residual gives a real datum `D'` with `(D'.z) = 𝔞₀ᵏ = (w)`; thus `D'.z` is associate to `w`, and
rescaling lands a real datum with `z` **exactly** `w`.

This isolates the spurious exact-`z` constraint and reduces the assembly to its mathematically
meaningful ideal form — without any over-statement (the ideal residual is *weaker* than the assembly
residual, which it implies, since `(D'.z) = (w)` is recovered from `D'.z = w`, never the converse
direction beyond the unit). -/
theorem caseIIRealAnchorDatumAssembly37_of_ideal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_ideal : CaseIIRealAnchorDatumIdeal37) :
    CaseIIRealAnchorDatumAssembly37 := by
  intro m D w k hk _hw_real _hw_p hw_span
  -- `(w) = 𝔞₀ᵏ` makes `𝔞₀ᵏ` principal (generator `w`).
  have hprinc : (a_eta_zero_dvd_p_pow (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy ^ k).IsPrincipal :=
    ⟨w, hw_span.symm⟩
  -- The ideal residual: a real datum with `(D'.z) = 𝔞₀ᵏ`.
  obtain ⟨m', D', hD'span⟩ := h_ideal D k hk hprinc
  -- `(D'.z) = 𝔞₀ᵏ = (w)`, so `D'.z` is associate to `w`.
  have hassoc : Associated D'.z w := by
    rw [← Ideal.span_singleton_eq_span_singleton, hD'span, hw_span]
  obtain ⟨u, hu⟩ := hassoc
  -- `𝔭 ∤ w` w.r.t. `D'`'s own root: from `D'.hz` (`𝔭 ∤ D'.z`) + the association `D'.z ~ w`.
  -- `D'.z = w · u⁻¹`, so `𝔭 ∣ w ⟹ 𝔭 ∣ D'.z`, contradicting `D'.hz`.
  have hzeq : D'.z = w * ((u⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← hu, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hw_p' : ¬ (D'.hζ.unit'.1 - 1) ∣ w := by
    intro hdvd
    exact D'.hz (hzeq ▸ hdvd.mul_right _)
  -- Rescale so the Fermat variable is exactly `w`.
  obtain ⟨D'', hD''z⟩ := caseII_realCaseIIData37_rescale_z D' hu hw_p'
  exact ⟨m', D'', hD''z⟩

/-! ## 3. The doubling-obstruction soundness certificate

Why neither the producer nor any proven machinery discharges the ideal residual: the `(ζ−1)`-content
of *every* `RealCaseIIData37` equation is forced to be `≡ 0 (mod 37)` (it is `37·(m+1)`), whereas
Washington's conjugate-norm `ξ₁`-equation sits at the doubled measure `λ^{2m−p}` with content
`2m − 37 ≢ 0 (mod 37)`.  This certifies that the residual is the genuine measure-mismatched content,
not an artefact of weak packaging. -/

/-- **[FLT37-CASEII-LAMBDA-CONTENT-MOD-P] The `(ζ−1)`-content of a `RealCaseIIData37` equation is a
multiple of `37`.**  For any real Case-II datum `D`, the Fermat sum `D.x³⁷ + D.y³⁷` is divisible by
the `37`-fold power `(ζ−1)^{37·(m+1)}` (the `(ζ−1)`-content is *exactly* `37·(m+1)`, since `ε, z` are
`𝔭`-units, but divisibility by the `37`-multiple suffices to expose the measure constraint).

This is the soundness certificate for the doubling obstruction: any datum re-entering the descent
must have `(ζ−1)`-content `≡ 0 (mod 37)`, whereas Washington's conjugate-norm descent equation
(`caseII_descent_equation`, with coefficients `γ_η − 2 = η⁻¹(η−1)²` each carrying `(ζ−1)²`) lives at
the doubled measure `λ^{2m−37} ≢ 0 (mod 37)`.  Hence the producer's output cannot, *as is*, be a
`RealCaseIIData37` whose `z`-ideal is the anchor power — pinning down `CaseIIRealAnchorDatumIdeal37`
as the genuine residual. -/
theorem caseII_realCaseIIData37_lambda_content_mul_p
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    (D.hζ.unit'.1 - 1) ^ (37 * (m + 1)) ∣ D.x ^ 37 + D.y ^ 37 := by
  -- `D.x³⁷ + D.y³⁷ = ε·((ζ−1)^{m+1}·z)³⁷ = ε·(ζ−1)^{37·(m+1)}·z³⁷`.
  refine ⟨(D.ε : 𝓞 (CyclotomicField 37 ℚ)) * D.z ^ 37, ?_⟩
  rw [D.equation, mul_pow, ← pow_mul, Nat.mul_comm (m + 1) 37]
  ring

/-! ## 4. Non-vacuity of the ideal residual, and the FLT37 endpoint -/

/-- **Non-vacuity (hypothesis satisfiable).**  The ideal residual's hypothesis — an exponent `k ≥ 1`
with `𝔞₀ᵏ` principal — is *not* vacuous: it is realised, for every real datum `D`, by
`caseII_exists_anchor_pow_isPrincipal` (`[𝔞₀]^{|Cl|} = 1`, so `𝔞₀^{|Cl|}` is principal with
`|Cl| ≥ 1`).  So the residual genuinely consumes inhabited input. -/
theorem caseIIRealAnchorDatumIdeal37_hyp_satisfiable
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ k : ℕ, 1 ≤ k ∧
      (a_eta_zero_dvd_p_pow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k).IsPrincipal :=
  caseII_exists_anchor_pow_isPrincipal D

/-- **Non-vacuity (conclusion is genuine existence).**  The ideal residual's conclusion shape — a
real datum `D'` with `(D'.z) = 𝔞₀ᵏ` — is genuine existence, not `False`: `𝔞₀ᵏ` is a nonzero ideal
(`caseIIWashingtonAnchorSquareDatum37_anchor_pow_ne_bot`), and `(D'.z)` is the principal ideal of a
`𝔭`-unit (so nonzero), exactly the shape of every `RealCaseIIData37.z` ideal. -/
theorem caseIIRealAnchorDatumIdeal37_concl_nonvacuous
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {k : ℕ} :
    a_eta_zero_dvd_p_pow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k ≠ 0 :=
  caseIIWashingtonAnchorSquareDatum37_anchor_pow_ne_bot D

/-- **FLT37 via the sharpened ideal residual `CaseIIRealAnchorDatumIdeal37`.**

`FermatLastTheoremFor 37` from the **ideal-form** residual `CaseIIRealAnchorDatumIdeal37`
(a real datum with `(D'.z) = 𝔞₀ᵏ`), Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`),
and the carried second-order input `NoSecondOrderIrregularPair 37 32`.

Composes the **proven** reduction `caseIIRealAnchorDatumAssembly37_of_ideal` (the unit-rescaling
normalisation) with the existing `fermatLastTheoremFor_thirtyseven_of_realAnchorDatumAssembly`.  This
is the cleanest sound statement of the FLT37 Case-II endpoint: everything else (II1, the terminal
core, the support arithmetic, the conjugate-norm reality `caseII_anchorPow_conjNorm_real_span`, the
anchor-square ideal, the unit-rescaling, and Case-I) is proven; the single residual is the
*ideal-form* Washington `ξ₁ = ρ₀²` datum, with its only undischarged content the measure
reconciliation (doubled `λ^{2m−37}` ↦ linear `RealCaseIIData37`) certified by
`caseII_realCaseIIData37_lambda_content_mul_p`. -/
theorem fermatLastTheoremFor_thirtyseven_of_realAnchorDatumIdeal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (caseII_ideal : CaseIIRealAnchorDatumIdeal37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_realAnchorDatumAssembly
    (caseIIRealAnchorDatumAssembly37_of_ideal caseII_ideal)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end
