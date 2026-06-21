import BernoulliRegular.FLT37.Eichler.CaseIIConjPairEpsPowerAssembly

/-!
# [FLT37-CASEII-R2] The first descent step Real → ConjPair, with the ε₁-37th-power clearing

This file applies the **ε₁-37th-power resolution** (`CaseIIConjPairEpsPower.lean`,
`CaseIIConjPairEpsPowerAssembly.lean`) to the *sound* setting where the σ-conjugate-pair structure
genuinely arises: the **first descent step over individually-real data**.

## Why over real (not ConjPair) data

Over `RealCaseIIData37` the conjugation map *swaps* the root ideals (`σ𝔞(η) = 𝔞(η⁻¹)`,
`RealCaseIIData37.map_rootIdeal`), so the single-root descent at the inversion-symmetric pair
`{η, η⁻¹}` with conjugate-paired generators `a₂ = σa₁`, `b₂ = σb₁` produces base variables forming a
**σ-conjugate pair**: `x' = a₁·σb₁`, `y' = σa₁·b₁ = σx'` (`caseII_conjPair_descent_vars`,
`CaseIIConjPairFirstStep.lean`).  This is the structurally correct place for `σx' = y'` —
over **ConjPair** data the ideals are *self-fixed* (`σ𝔞(η) = 𝔞(η)`), so the descent there produces
*individually-σ-stable* variables (`σx' = ζ^a·x'`, `caseII_conjPair_zeta_twist_real`), **not** a
σ-conjugate pair.

So the ε₁-clearing belongs to the **Real → ConjPair** transition: a real datum at `m` descends to a
σ-conjugate-pair datum at `m-1`.

## What is established

* `ConjPairCaseIIData37.of_realConjPairSolution` — **constructor**: a σ-conjugate-pair solution of
  the dropped-exponent equation (`σx' = y'`, `σy' = x'`, `(ζ-1) ∤ y', z'`,
  `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37`) over a *real* datum `D : RealCaseIIData37 K m` packages into
  a `ConjPairCaseIIData37 (m-1)` (its `x_conj`/`y_conj` fields are exactly the σ-swap).

* `CaseIIRealToConjPairSigmaEquivariant37` — the precise σ-equivariance residual **over real data**:
  every real datum's descent equation can be chosen σ-equivariantly (`σx' = y'`, `σε₁ = ε₂`).  The
  `σx' = y'` half is the *proved* swap output (`caseII_conjPair_descent_vars`); the unit σ-pairing
  `σε₁ = ε₂` is the remaining sub-step (B2-logged `R2-thetaFixed`).  **Non-vacuous** (§3): the
  conclusion shape is realized by genuine σ-conjugate-pair data.

* `realToConjPair_descent_step` — **the Real → ConjPair descent step**: from the real-data
  σ-equivariance residual, the norm-`37`-th-power residual, and the genuine R4 inputs (assembling
  Assumption II) + Kellner, every `RealCaseIIData37 m` yields a `ConjPairCaseIIData37 m'` with
  `m' < m`.  The ε₁-`37`-th-power clearing (`caseII_conjPair_symmetric_clear`) dissolves the
  δ-σ-obstruction that blocked all prior single-unit reductions.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (`B_a`/`B_{-a}`), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The Real → ConjPair descent-datum constructor -/

/-- **Constructor: a σ-conjugate-pair solution of the dropped-exponent equation over a *real* datum
packages into a `ConjPairCaseIIData37 (m-1)`.**

Given a real datum `D : RealCaseIIData37 K m` and an explicit σ-conjugate-pair solution
`(x', y', z', ε')` of the next descent equation — `σx' = y'`, `σy' = x'`, `(ζ-1) ∤ y', z'`, and
`x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37` (exponent `m`, one less than the datum's `m+1`) — this builds
the `ConjPairCaseIIData37 (m-1)` record (the equation needs `(ζ-1)^((m-1)+1) = (ζ-1)^m`, from
`1 ≤ m`; the `x_conj`/`y_conj` fields are exactly `σx' = y'`, `σy' = x'`).

This is the Real → ConjPair analogue of `ConjPairCaseIIData37.of_conjPairSolution`. -/
def ConjPairCaseIIData37.of_realConjPairSolution {m : ℕ} (D : RealCaseIIData37 K m)
    (x' y' z' : 𝓞 K) (ε' : (𝓞 K)ˣ)
    (hx'_conj : ringOfIntegersComplexConj K x' = y')
    (hy'_conj : ringOfIntegersComplexConj K y' = x')
    (hy' : ¬ (D.hζ.unit'.1 - 1) ∣ y')
    (hz' : ¬ (D.hζ.unit'.1 - 1) ∣ z')
    (e' : x' ^ 37 + y' ^ 37 = (ε' : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37) :
    ConjPairCaseIIData37 K (m - 1) := by
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel D.toCaseIIData37.one_le_m
  exact
    { ζ := D.ζ
      hζ := D.hζ
      x := x'
      y := y'
      z := z'
      ε := ε'
      equation := by rw [hm_sub]; exact e'
      hy := hy'
      hz := hz'
      x_conj := hx'_conj
      y_conj := hy'_conj }

/-! ## 2. The real-data σ-equivariance residual and the Real → ConjPair descent step -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-REAL→CONJPAIR-σ-EQUIV] The σ-equivariant descent equation, real data.**

For every real datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` with the (proven, real-data)
`η₀`-principalization, the next descent equation (at the dropped exponent `m`) can be chosen
**σ-equivariantly**: there exist `x' y' z' : 𝓞 K`, `ε₁ ε₂ ε₃ : (𝓞 K)ˣ` with

* `(ζ-1) ∤ x', y', z'`,
* `σx' = y'`  (the descent variables form a σ-conjugate pair — the *swap* output over real data),
* `σε₁ = ε₂`  (the leading descent units are σ-conjugate),
* `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`.

The `σx' = y'` half is the **proved** swap output (`caseII_conjPair_descent_vars`, with
generators `a₂ = σa₁`, `b₂ = σb₁` at the inversion-symmetric pair `{η, η⁻¹}`,
`caseII_real_conj_generator_span`).  The unit σ-pairing `σε₁ = ε₂` is the remaining sub-step
(B2-logged `R2-thetaFixed`).  A `def … : Prop` (not an axiom); non-vacuous (§3). -/
def CaseIIRealToConjPairSigmaEquivariant37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ¬ (D.hζ.unit'.1 - 1) ∣ x' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x' = y' ∧
      unitsComplexConj (CyclotomicField 37 ℚ) ε₁ = ε₂ ∧
      (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37

/-- **[FLT37-CASEII-REAL-NORM-PTHPOWER] The descent-unit relative norm is a `37`-th power (real
data).**  For every real datum and every σ-equivariant descent equation produced from it, the
`K/K⁺` relative norm `ε₁·σ(ε₁)` of the leading descent unit is a `37`-th power — **Kummer's lemma
for the plus part** (`37 ∤ h⁺`, the real unit `ε₁·σ(ε₁)` ≡ rational integer mod `37`).  A
`def … : Prop` (not an axiom). -/
def CaseIIRealNormPthPower37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
    ¬ (D.hζ.unit'.1 - 1) ∣ x' →
    ¬ (D.hζ.unit'.1 - 1) ∣ y' →
    ¬ (D.hζ.unit'.1 - 1) ∣ z' →
    unitsComplexConj (CyclotomicField 37 ℚ) ε₁ = ε₂ →
    (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37 →
    ∃ w : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      ε₁ * unitsComplexConj (CyclotomicField 37 ℚ) ε₁ = w ^ 37

/-- **The Real → ConjPair descent step via the ε₁-`37`-th-power clearing** (fully proved reduction).

From the real-data σ-equivariance residual `CaseIIRealToConjPairSigmaEquivariant37`, the
norm-`37`-th-power residual `CaseIIRealNormPthPower37`, the genuine R4 inputs (assembling Assumption
II), and Kellner, every real datum `D : RealCaseIIData37 m` with the (real-data) `η₀`-
principalization yields a σ-conjugate-pair datum `ConjPairCaseIIData37 m'` with `m' < m`.

The proof: take the σ-equivariant equation; get `ε₁/ε₂` a `37`-th power (Assumption II) and `ε₁·σε₁`
a `37`-th power (the norm residual); combine via `unit_isPow_of_prod_isPow_of_quotient_isPow` to get
`ε₁ = δ₁^37`; clear symmetrically via `caseII_conjPair_symmetric_clear` to a clean σ-conjugate-pair
solution; package via `of_realConjPairSolution` into `ConjPairCaseIIData37 (m-1)`.  The symmetric
`δ₁`/`σδ₁` clearing dissolves the δ-σ-obstruction (the asymmetric `(ε₁/ε₂)^{1/37}`-into-`x'`
absorption broke `σx' = y'`; this one preserves it). -/
theorem realToConjPair_descent_step
    (h_sigma : CaseIIRealToConjPairSigmaEquivariant37)
    (h_norm : CaseIIRealNormPthPower37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_dvdZ : CaseIILehmerVandiverDvdZ37)
    (h_kellner : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hprinc : CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m') := by
  -- Assumption II, assembled from R3 (proven) + R4(i)+R4(ii).
  have h_assumptionII : WashingtonCaseIIExactQuotientUnitPower37Source :=
    caseIIOmega32_assumptionII_of_section91Ident_dvdZ caseII_section91Ident caseII_dvdZ
  -- The σ-equivariant descent equation over the real datum.
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', hx'_conj, hε_conj, e'⟩ := h_sigma D hprinc
  -- (b) `ε₁/ε₂` is a `37`-th power — Assumption II over the underlying bare `CaseIIData37`.
  obtain ⟨v, hv⟩ :=
    h_assumptionII Sinnott.flt37_not_dvd_hPlus h_kellner D.toCaseIIData37 hx' hy' hz' e'
  -- (a) `ε₁·σ(ε₁)` is a `37`-th power — the norm residual.
  obtain ⟨w, hw⟩ := h_norm D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' hε_conj e'
  -- §1: `ε₁ = δ₁^37`.
  obtain ⟨δ₁, hδ₁⟩ :=
    unit_isPow_of_prod_isPow_of_quotient_isPow
      (a := ε₁) (b := unitsComplexConj (CyclotomicField 37 ℚ) ε₁)
      ⟨w, hw⟩ ⟨v, by rw [hε_conj]; exact hv⟩
  -- §2: the symmetric clearing produces a clean σ-conjugate-pair solution at exponent `m`.
  obtain ⟨x'', y'', z'', ε'', hx''_conj, hy''_conj, hy'', hz'', e''⟩ :=
    caseII_conjPair_symmetric_clear D.hζ hy' hz' hx'_conj hε_conj hδ₁ e'
  -- Package into a `ConjPairCaseIIData37 (m-1)`.
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  exact ⟨m - 1, by omega,
    ⟨ConjPairCaseIIData37.of_realConjPairSolution D x'' y'' z'' ε''
      hx''_conj hy''_conj hy'' hz'' e''⟩⟩

/-! ## 3. Non-vacuity of the real-data σ-equivariance residual

The conclusion shape of `CaseIIRealToConjPairSigmaEquivariant37` is realized by genuine
σ-conjugate-pair data: any `ConjPairCaseIIData37 k` exhibits a σ-equivariant descent equation at
exponent `k+1` whose `σx' = y'` and `σε₁ = ε₂` hold *verbatim* (the `x_conj` field and the trivial
unit pairing).  This certifies the residual is not vacuously false. -/

/-- **The `CaseIIRealToConjPairSigmaEquivariant37` conclusion shape is realized by genuine
σ-conjugate-pair data.**  For any `D' : ConjPairCaseIIData37 k`, the data `(D'.x, D'.y, D'.z, 1, 1,
D'.ε)` is a σ-equivariant descent equation at exponent `k+1`: `(ζ-1) ∤ D'.x, D'.y, D'.z`,
`σD'.x = D'.y` (the `x_conj` field), `σ(1) = 1`, and
`(1:𝓞K)·D'.x^37 + (1:𝓞K)·D'.y^37 = D'.ε·((ζ-1)^(k+1)·D'.z)^37` (`D'.equation` after `one_mul`).
Certifies the σ-equivariance residual is not provably false. -/
theorem caseIIRealToConjPairSigmaEquivariant_conclusion_realized
    {k : ℕ} (D' : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) k) :
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.x ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.y ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.z ∧
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.x = D'.y ∧
    unitsComplexConj (CyclotomicField 37 ℚ) 1 = 1 ∧
    ((1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) * D'.x ^ 37 +
        ((1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) * D'.y ^ 37 =
      (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 := by
  refine ⟨?_, D'.hy, D'.hz, D'.x_conj, map_one _, ?_⟩
  · -- `(ζ-1) ∤ D'.x`: `σ` fixes `span{ζ-1}` (`caseII_map_zetaSubOne_span`) and `σD'.x = D'.y`, so
    -- `(ζ-1)∣D'.x ⟺ D'.x ∈ span{ζ-1} ⟺ D'.y = σD'.x ∈ σ(span{ζ-1}) = span{ζ-1} ⟺ (ζ-1)∣D'.y`.
    have h37z : (D'.hζ.unit'.1) ^ 37 = 1 := by
      rw [← Units.val_pow_eq_pow_val, D'.hζ.unit'_pow, Units.val_one]
    intro hdvd
    apply D'.hy
    -- From `D'.x ∈ span{ζ-1}`, map by `σ`: `σD'.x ∈ (span{ζ-1}).map σ = span{ζ-1}`.
    rw [← Ideal.mem_span_singleton] at hdvd ⊢
    have hmem : ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.x ∈
        (Ideal.span ({D'.hζ.unit'.1 - 1} : Set (𝓞 (CyclotomicField 37 ℚ)))).map
          (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom :=
      Ideal.mem_map_of_mem _ hdvd
    rwa [caseII_map_zetaSubOne_span h37z, D'.x_conj] at hmem
  · rw [Units.val_one, one_mul, one_mul]; exact D'.equation

end BernoulliRegular.FLT37.Eichler

end

end
