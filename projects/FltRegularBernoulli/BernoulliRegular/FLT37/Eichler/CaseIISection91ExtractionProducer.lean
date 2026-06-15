import BernoulliRegular.FLT37.Eichler.CaseIIModuloKellner
import BernoulliRegular.FLT37.Eichler.CaseIILemma98RealData
import BernoulliRegular.FLT37.Eichler.CaseIIAnchorSquareDatum

/-!
# [FLT37-CASEII-R2-PRODUCER] The §9.1 extraction-data producer, and the precise anchor obstruction

This file attacks the **R2 extraction-data producer** — Washington's §9.1 / Theorem 9.4 descent
assembly that produces the next-level §9.1 extraction data
`CaseIISection91DvdZGenuineUnitExtractionData37` (`CaseIIModuloKellner.lean`) for a **non-terminal**
`RealCaseIIDvdZData37` datum, the input that the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction` consumes.

It does two things, **soundness-first** (no `sorry`, no `axiom`; imports only — modifies nothing):

## 1. The proven ideal factorization (the `𝔍 ↔ 𝔞₀³⁷` step, PROVEN under coprimality)

`caseII_span_x_add_y_eq_anchorCube` — under the per-datum coprimality `IsCoprime ((x)) ((y))` of the
Fermat variables, the anchor ideal `𝔍` of the proven `caseII_span_x_add_y_eq_p_pow_mul`
(`span(x+y) = 𝔭^{37m+1}·𝔍`, `𝔍 = gcd((x),(y))·𝔞₀³⁷`) collapses to the **anchor cube** `𝔞₀³⁷`:
`span(x+y) = 𝔭^{37m+1}·𝔞₀³⁷` with `𝔞₀ = aEtaZeroDvdPPow` the `𝔭`-free anchor `B₀`.  The
task's `𝔍 ↔ 𝔞₀³⁷` anchor-cube step is therefore **proven** (the only extra ingredient over the
flt-regular root-ideal factorization is `gcd((x),(y)) = 1`, the threaded coprimality).

## 2. The PRECISE anchor obstruction (GAP A made exact and PROVEN, soundness-critical)

`caseII_genuineUnit_anchor_span_z_eq_anchorSq` — the §9.1 anchor equation with a **genuine
algebraic-integer unit** `η₀ = algebraMap u₀` and `z' = ρ₀²` (the exact shape of
`CaseIISection91DvdZGenuineUnitExtractionData37`), **together with** the coprimality and `¬𝔭 ∣ z'`,
**forces the descended Fermat variable `z'` to span the square of the `𝔭`-free anchor**:
`span(z') = 𝔞₀²`.

This is the documented hard point — the `ρ₀²` vs `ρ₀σρ₀` mismatch
(`project_flt37_freecontent_assembly_findings`) — made **exact** at the ideal level.  Taking
`(ζ−1)`-multiplicities of the squared integral anchor equation
`(x+y)² = u₀²·λ_int^{2e}·z'³⁷` (`caseII_anchor_sq_integral`) with the sharp `2e = 37m+1`
(`caseII_anchor_exponent_eq`) gives `(𝔞₀²)³⁷ = span(z')³⁷`; strip the `37`-th power
(`caseII_ideal_pow37_injective`) for `span(z') = 𝔞₀²`.

**Consequence (the soundness verdict).** `span(z') = 𝔞₀²` is **exactly** the ideal of the conjugate
norm `ξ₁ = ρ₀σρ₀` (`(ξ₁) = 𝔞₀^{2k'}`, `k' = 1`, `caseII_anchorPow_conjNorm_real_span`): the
`z' = ρ₀²` capstone form and the `ρ₀σρ₀` form give the **same** descended Fermat variable at the
**ideal** level.  But the anchor equation's *single* `ρ₀` additionally pins `(ρ₀) = 𝔞₀` (via
`2e = 37m+1`), which would need `𝔞₀` principal — **false** for the irregular prime `37` (its prime
support is the dropped non-anchor root ideals, `caseII_a_eta_zero_dvd_z` /
`caseII_coprime_a_eta_zero_rootIdeal`; the descent *exists* to drop them).  So the
genuine-integral-unit extraction data in its **single-`ρ₀`,
`z' = ρ₀²`** form is **not** producible: the producer target as written is over-strong.  The sound
Washington object is the conjugate norm at the **doubled** measure, whose ideal `𝔞₀·σ𝔞₀ = 𝔞₀²`
**is** principal (FULLY PROVEN).  The producer below therefore targets the **conjugate-norm** anchor
object, not the `ρ₀²` form.

## 3. The honest residual of the producer (the genuine open R2 content)

After the anchor-cube step (proven) and redirecting to the conjugate norm (proven ideal+reality),
the producer's remaining content is **exactly** Washington's §9.1 Fermat-equation assembly of the
conjugate-normed descent equation `ω₁³⁷ + θ₁³⁷ = ε·λ^{(2m−1)p}·ξ₁³⁷` realising `ξ₁ = ρ₀σρ₀` as the
next Fermat variable — i.e. the **already-isolated** single residual
`CaseIIRealAnchorDatumAssembly37`
(`CaseIIAnchorSquareDatum.lean`) — **plus** Assumption II (Kellner, `Cor815`/`Lemma98`) and the
descended-variable Lemma 9.6 (`ℓ ∤ ω, θ`).  The producer chains these into the factor-count frame,
re-deriving the FLT37 Case-II endpoint on those inputs.  **No** new `def … : Prop` is introduced for
the anchor object: the conjugate-norm `ξ₁` is the proven `caseII_anchorPow_conjNorm_real_span`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4),
  pp. 171–173 (the conjugate-norm new variable `ξ₁ = ρ₀σρ₀`, `(ξ₁) = B₀²`, real).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The anchor-cube ideal factorization under coprimality (the `𝔍 ↔ 𝔞₀³⁷` step, PROVEN) -/

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[ANCHOR CUBE] `span(x+y) = 𝔭^{37m+1}·𝔞₀³⁷` under coprimality** (proven, axiom-clean).

For a real Case-II datum `D` whose Fermat variables are coprime (`IsCoprime ((x)) ((y))`), the
anchor cofactor `𝔍` of `caseII_span_x_add_y_eq_p_pow_mul` (`span(x+y) = 𝔭^{37m+1}·𝔍`,
`𝔍 = gcd((x),(y))·𝔞₀³⁷`) collapses to the **anchor cube** `𝔞₀³⁷` because `gcd((x),(y)) = 1`:
```
span(x+y) = 𝔭^{37m+1} · 𝔞₀³⁷,    𝔞₀ = aEtaZeroDvdPPow         (the 𝔭-free anchor B₀).
```

This is the task's `𝔍 ↔ 𝔞₀³⁷` anchor-cube step.  It is the flt-regular root-ideal factorization
`caseII_span_x_add_y_eq_p_pow_mul` (`(x+y) = 𝔪·(𝔭^m·𝔞₀)³⁷·𝔭`) with the gcd `𝔪 = gcd((x),(y))`
killed by the threaded coprimality. -/
theorem caseII_span_x_add_y_eq_anchorCube {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))) :
    Ideal.span ({D.x + D.y} : Set (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (37 * m + 1) *
        aEtaZeroDvdPPow hp D.hζ D.equation D.hy ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  set 𝔭 : Ideal (𝓞 K) := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭
  -- Reproduce the flt-regular root-ideal factorization at the anchor root `η₀ = 1`, with the
  -- gcd `𝔪 = gcd((x),(y))` killed by coprimality.
  have hmcp := m_mul_c_mul_p hp D.hζ D.equation D.hy D.etaZero
  have hcspec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy D.etaZero
  have hηZ : zetaSubOneDvdRoot hp D.hζ D.equation D.hy = D.etaZero := rfl
  have ha0spec : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m *
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
    rw [← hηZ]; exact a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy
  have hη0 : (D.etaZero : 𝓞 K) = 1 := caseII_etaZero_eq_one D hp
  -- `gcd((x),(y)) = 1` from coprimality.
  have hgcd1 : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) = 1 := by
    rw [Ideal.isCoprime_iff_gcd] at hcop; exact hcop
  -- `span{x + y·η₀} = 𝔪·𝔞(η₀)³⁷·𝔭`, with `𝔪 = 1` and `𝔞(η₀) = 𝔭^m·𝔞₀`.
  have hbase : Ideal.span ({D.x + D.y * (D.etaZero : 𝓞 K)} : Set (𝓞 K)) =
      gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero ^ 37 * 𝔭 := by
    rw [← hmcp, hcspec]
  rw [hη0, mul_one, hgcd1, one_mul] at hbase
  rw [hbase, ← ha0spec, mul_pow, ← pow_mul, show 37 * m = m * 37 from by ring]
  ring

/-! ## 2. The real prime `λ` spans `𝔭²` -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **`span((1−ζ')(1−ζ'³⁶)) = 𝔭²`** for any two primitive `37`-th roots `ζ, ζ'`.

The real prime `λ = (1−ζ')(1−ζ'³⁶)` spans the square of `𝔭 = span(ζ−1)`: both factors `1−ζ'`,
`1−ζ'³⁶` are associates of `ζ−1` (all `1−ζ'^j`, `j ≢ 0`, are associates of `ζ−1` via
`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime` based at `ζ`), so each spans `𝔭`, and
`span(λ) = span(1−ζ')·span(1−ζ'³⁶) = 𝔭·𝔭 = 𝔭²`.  (Ideal-level form of `caseII_lambda_emultiplicity`
`v_𝔭(λ) = 2`.) -/
theorem caseII_span_lambda_eq_p_sq {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ 37)
    (hζ' : IsPrimitiveRoot ζ' 37) :
    Ideal.span ({(1 - hζ'.toInteger) * (1 - hζ'.toInteger ^ 36)} : Set (𝓞 K)) =
      Ideal.span ({(hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hmem1 : (1 : 𝓞 K) ∈ nthRootsFinset 37 (1 : 𝓞 K) := one_mem_nthRootsFinset (by norm_num)
  have hmemζ' : (hζ'.toInteger) ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
    hζ'.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
  have hmem36 : (hζ'.toInteger ^ 36) ∈ nthRootsFinset 37 (1 : 𝓞 K) := by
    rw [mem_nthRootsFinset (by norm_num)]
    rw [← pow_mul, show 36 * 37 = 37 * 36 from by norm_num, pow_mul,
      hζ'.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  -- `1 − ζ'` and `1 − ζ'³⁶` are associates of `ζ − 1`.
  have h1 : Associated (hζ.toInteger - 1 : 𝓞 K) (1 - hζ'.toInteger) := by
    have hne : (1 : 𝓞 K) ≠ hζ'.toInteger :=
      fun h => hζ'.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) h.symm
    exact hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem1 hmemζ' hne
  have h2 : Associated (hζ.toInteger - 1 : 𝓞 K) (1 - hζ'.toInteger ^ 36) := by
    have hne : (1 : 𝓞 K) ≠ hζ'.toInteger ^ 36 := by
      intro h
      have h37 : (hζ'.toInteger) ^ 37 = 1 := hζ'.toInteger_isPrimitiveRoot.pow_eq_one
      have : hζ'.toInteger = 1 := by
        have hps : hζ'.toInteger ^ 37 = hζ'.toInteger ^ 36 * hζ'.toInteger := pow_succ _ _
        rw [h37, ← h, one_mul] at hps; exact hps.symm
      exact hζ'.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) this
    exact hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem1 hmem36 hne
  -- `span(1−ζ') = 𝔭`, `span(1−ζ'³⁶) = 𝔭`, and `span(λ) = span(1−ζ')·span(1−ζ'³⁶) = 𝔭²`.
  have hspan1 : Ideal.span ({(1 - hζ'.toInteger : 𝓞 K)} : Set (𝓞 K)) =
      Ideal.span ({(hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
    (Ideal.span_singleton_eq_span_singleton.mpr h1).symm
  have hspan2 : Ideal.span ({(1 - hζ'.toInteger ^ 36 : 𝓞 K)} : Set (𝓞 K)) =
      Ideal.span ({(hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
    (Ideal.span_singleton_eq_span_singleton.mpr h2).symm
  rw [← Ideal.span_singleton_mul_span_singleton, hspan1, hspan2, sq]

/-! ## 3. `37`-th power injectivity of ideals, and the precise anchor obstruction (GAP A) -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K] in
/-- **Ideals of `𝓞 K` have `37`-th-power injectivity** (proven, axiom-clean).

`I³⁷ = J³⁷ ⟹ I = J` for ideals of the Dedekind domain `𝓞 K`.  Via `normalizedFactors`:
`normalizedFactors (I³⁷) = 37 • normalizedFactors I`, so `37 • nf I = 37 • nf J` cancels
(`nsmul_right_injective`) to `nf I = nf J`, and `(nf I).prod = normalize I = I`. -/
theorem caseII_ideal_pow37_injective (I J : Ideal (𝓞 K)) (h : I ^ 37 = J ^ 37) : I = J := by
  by_cases hI : I = 0
  · subst hI
    rw [zero_pow (by norm_num : 37 ≠ 0)] at h
    exact ((pow_eq_zero_iff (by norm_num : 37 ≠ 0)).mp h.symm).symm
  by_cases hJ : J = 0
  · subst hJ
    rw [zero_pow (by norm_num : 37 ≠ 0)] at h
    exact (pow_eq_zero_iff (by norm_num : 37 ≠ 0)).mp h
  have key : normalizedFactors (I ^ 37) = (37 : ℕ) • normalizedFactors I :=
    normalizedFactors_pow 37
  have key2 : normalizedFactors (J ^ 37) = (37 : ℕ) • normalizedFactors J :=
    normalizedFactors_pow 37
  have heq : (37 : ℕ) • normalizedFactors I = (37 : ℕ) • normalizedFactors J := by
    rw [← key, ← key2, h]
  have hnf : normalizedFactors I = normalizedFactors J :=
    nsmul_right_injective (by norm_num) heq
  have hI' : (normalizedFactors I).prod = normalize I := prod_normalizedFactors_eq hI
  have hJ' : (normalizedFactors J).prod = normalize J := prod_normalizedFactors_eq hJ
  have hnorm : normalize I = normalize J := by rw [← hI', ← hJ', hnf]
  rwa [normalize_eq, normalize_eq] at hnorm

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[ANCHOR OBSTRUCTION, the `ρ₀²` reconciliation] The genuine-unit anchor equation forces
`span(z') = 𝔞₀²`** (proven, axiom-clean) — the precise ideal content of the descended Fermat
variable `ξ₁ = z'`.

For a real Case-II datum `D` with **coprime** Fermat variables, the §9.1 anchor equation in its
genuine-integral-unit form
```
algebraMap(x+y) = algebraMap(u₀)·Λ^e·ρ₀³⁷,    u₀ : (𝓞 K)ˣ,  Λ = (1−ζ_spec)(1−ζ_spec³⁶),
```
together with `algebraMap z' = ρ₀²` and `¬𝔭 ∣ z'`, forces the descended Fermat variable `z'` to
generate the **square of the `𝔭`-free anchor** `𝔞₀ = aEtaZeroDvdPPow`:
```
span(z') = 𝔞₀².
```

This is the documented `ρ₀²` vs `ρ₀σρ₀` reconciliation made **exact at the ideal level**: the
`z' = ρ₀²` capstone form and the conjugate-norm `ξ₁ = ρ₀σρ₀` form
(`caseII_anchorPow_conjNorm_real_span`, `(ξ₁) = 𝔞₀^{2k'}`) give the **same ideal** `𝔞₀²` for the
descended variable (`k' = 1`).  They are interchangeable as the next Fermat variable at the
**ideal** level.

Proof: square the anchor equation to the integral form `(x+y)² = u₀²·λ_int^{2e}·z'³⁷`
(`caseII_anchor_sq_integral`); take `span`s, with `span(u₀²) = 1` (`u₀` a unit),
`span(x+y) = 𝔭^{37m+1}·𝔞₀³⁷` (`caseII_span_x_add_y_eq_anchorCube`, the coprimality),
`span(λ_int) = 𝔭²` (`caseII_span_lambda_eq_p_sq`) and the sharp `2e = 37m+1`
(`caseII_anchor_exponent_eq`); cancel the common `𝔭^{2(37m+1)}` to get `(𝔞₀²)³⁷ = span(z')³⁷`, and
strip the `37`-th power (`caseII_ideal_pow37_injective`). -/
theorem caseII_genuineUnit_anchor_span_z_eq_anchorSq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))))
    {z' : 𝓞 K} {u0 : (𝓞 K)ˣ} {ρ0 : K} {e : ℕ}
    (hanchor : algebraMap (𝓞 K) K (D.x + D.y) =
      algebraMap (𝓞 K) K (u0 : 𝓞 K) *
        (algebraMap (𝓞 K) K ((1 - (zeta_spec 37 ℚ K).toInteger) *
          (1 - (zeta_spec 37 ℚ K).toInteger ^ 36))) ^ e * ρ0 ^ 37)
    (hz' : algebraMap (𝓞 K) K z' = ρ0 ^ 2)
    (hz'_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ z') :
    Ideal.span ({z'} : Set (𝓞 K)) =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔭 : Ideal (𝓞 K) := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭
  set 𝔞₀ : Ideal (𝓞 K) := aEtaZeroDvdPPow hp D.hζ D.equation D.hy with h𝔞₀
  -- the sharp anchor exponent `2e = 37m+1`.
  have h2e : 2 * e = 37 * m + 1 :=
    caseII_anchor_exponent_eq D hp (zeta_spec 37 ℚ K) hanchor hz' hz'_cop
  -- the squared integral anchor equation `(x+y)² = u₀²·λ_int^{2e}·z'³⁷`.
  have hsq := caseII_anchor_sq_integral (zeta_spec 37 ℚ K) hanchor hz'
  -- take `span` of both sides (`span` of a product = product of spans).
  have hspan_sq : Ideal.span ({(D.x + D.y) ^ 2} : Set (𝓞 K)) =
      Ideal.span ({(u0 : 𝓞 K) ^ 2} : Set (𝓞 K)) *
        Ideal.span ({((1 - (zeta_spec 37 ℚ K).toInteger) *
          (1 - (zeta_spec 37 ℚ K).toInteger ^ 36))} : Set (𝓞 K)) ^ (2 * e) *
        Ideal.span ({z'} : Set (𝓞 K)) ^ 37 := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, hsq]
  -- `span(u₀²) = 1` (`u₀` a unit), `span(x+y)² = (𝔭^{37m+1}·𝔞₀³⁷)²`, `span(λ_int) = 𝔭²`.
  have hu0span : Ideal.span ({(u0 : 𝓞 K) ^ 2} : Set (𝓞 K)) = 1 := by
    rw [Ideal.one_eq_top, Ideal.span_singleton_eq_top]
    exact ⟨u0 ^ 2, by rw [Units.val_pow_eq_pow_val]⟩
  have hxyspan : Ideal.span ({(D.x + D.y) ^ 2} : Set (𝓞 K)) =
      (𝔭 ^ (37 * m + 1) * 𝔞₀ ^ 37) ^ 2 := by
    rw [← Ideal.span_singleton_pow, caseII_span_x_add_y_eq_anchorCube D hp hcop]
  have hlam_span : Ideal.span ({((1 - (zeta_spec 37 ℚ K).toInteger) *
      (1 - (zeta_spec 37 ℚ K).toInteger ^ 36))} : Set (𝓞 K)) = 𝔭 ^ 2 :=
    caseII_span_lambda_eq_p_sq D.hζ (zeta_spec 37 ℚ K)
  -- combine, cancel the common `𝔭^{2(37m+1)}`, strip the `37`-th power.
  rw [hu0span, one_mul, hxyspan, hlam_span, ← pow_mul] at hspan_sq
  -- LHS `(𝔭^{37m+1}·𝔞₀³⁷)² = 𝔭^{2(37m+1)}·𝔞₀^{74}`; RHS `𝔭^{2·(2e)}·span(z')³⁷ = 𝔭^{2(37m+1)}·…`.
  rw [mul_pow, ← pow_mul, ← pow_mul, show 2 * (2 * e) = 2 * (37 * m + 1) from by omega,
    show 37 * 2 = 2 * 37 from by ring] at hspan_sq
  -- cancel `𝔭^{2(37m+1)}` (nonzero).
  have hp_ne : 𝔭 ^ (2 * (37 * m + 1)) ≠ 0 := by
    apply pow_ne_zero; rw [h𝔭, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)
  have hcancel : 𝔞₀ ^ (2 * 37) = Ideal.span ({z'} : Set (𝓞 K)) ^ 37 := by
    have h : 𝔭 ^ (2 * (37 * m + 1)) * 𝔞₀ ^ (2 * 37) =
        𝔭 ^ (2 * (37 * m + 1)) * Ideal.span ({z'} : Set (𝓞 K)) ^ 37 := by
      rw [← hspan_sq, show (37 * m + 1) * 2 = 2 * (37 * m + 1) from by ring]
    exact mul_right_injective₀ hp_ne h
  -- `(𝔞₀²)³⁷ = span(z')³⁷`, strip the `37`.
  have hcube : (𝔞₀ ^ 2) ^ 37 = Ideal.span ({z'} : Set (𝓞 K)) ^ 37 := by
    rw [← pow_mul]; exact hcancel
  exact (caseII_ideal_pow37_injective (𝔞₀ ^ 2) (Ideal.span ({z'} : Set (𝓞 K))) hcube).symm

/-! ## 4. The `ρ₀²` ↔ `ρ₀σρ₀` reconciliation, and the producer reduction to the conjugate norm -/

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]

/-- **[RECONCILIATION] The genuine-unit extraction data's descended variable `z'` spans `𝔞₀²`** —
the *same* ideal as the conjugate norm `ξ₁ = ρ₀σρ₀` (proven, axiom-clean).

For every output of the genuine-integral-unit §9.1 extraction data
`CaseIISection91DvdZGenuineUnitExtractionData37`, applied to a coprime `ℓ ∣ z` real datum `D`, the
descended Fermat variable `z'` (the capstone's `ξ₁ = ρ₀²`) satisfies `span(z') = 𝔞₀²` — **exactly**
the ideal of the conjugate norm `ξ₁ = ρ₀σρ₀` (`caseII_anchorPow_conjNorm_real_span`,
`(ξ₁) = 𝔞₀^{2k'}`, here `k' = 1`).  So the `ρ₀²` capstone form and the `ρ₀σρ₀` conjugate-norm form
produce the **same** descended Fermat variable at the **ideal** level — the documented
`ρ₀²` vs `ρ₀σρ₀` reconciliation, made exact.

Consequently the genuine-unit data's own anchor-support field `(z') = 𝔞₀ᵏ` forces `k = 2` (the
conjugate-norm doubled measure): the data is self-consistent only at the doubled measure.

The hypothesis bundle is exactly the genuine-unit data's anchor outputs (anchor equation `hanchor`,
`hz' : algebraMap z' = ρ₀²`, and the anchor-support `(z') = 𝔞₀ᵏ`), plus the threaded coprimality. -/
theorem caseII_genuineUnit_extraction_z_eq_anchorSq {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))))
    {z' : 𝓞 (CyclotomicField 37 ℚ)} {u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    {ρ0 : CyclotomicField 37 ℚ} {e k : ℕ} (_hk : 1 ≤ k)
    (hanchor : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
            (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37)
    (hz' : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) z' = ρ0 ^ 2)
    (hz'_span : Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k) :
    Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `¬ 𝔭 ∣ z'` from the anchor-support `(z') = 𝔞₀ᵏ` (`𝔭 ∤ 𝔞₀`).
  have hz'_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ z' := by
    have hnot : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hz'_span]; intro hdvd
      exact not_p_div_a_zero (by decide) D.hζ D.equation D.hy D.hz
        ((Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  exact caseII_genuineUnit_anchor_span_z_eq_anchorSq D (by decide) hcop hanchor hz' hz'_cop

/-! ## 5. The FLT37 Case-II endpoint via the SOUND conjugate-norm R2 producer

The §4 obstruction shows the genuine-integral-unit extraction data's *single-`ρ₀`* anchor equation
is over-strong (it would need `𝔞₀` principal, false for irregular `37`); its descended variable
lives at the **doubled** ideal `𝔞₀²`, exactly the conjugate norm `ξ₁ = ρ₀σρ₀`.  The sound producer
therefore routes through the conjugate norm, whose ideal `𝔞₀·σ𝔞₀ = 𝔞₀²` **is** principal
(`caseII_anchorPow_conjNorm_real_span`, FULLY PROVEN).  The remaining §9.1 content is precisely
Washington's conjugate-normed Fermat-equation assembly `CaseIIRealAnchorDatumAssembly37`
(`CaseIIAnchorSquareDatum.lean`) — the *single* isolated R2 residual, reality + anchor-square ideal
already proven.  We re-export the FLT37 Case-II endpoint on it, eliminating the (over-strong)
genuine-unit extraction-data hypothesis in favour of the sound conjugate-norm one. -/

/-- **Fermat's Last Theorem for `37`, via the SOUND conjugate-norm R2 producer residual** (proven,
axiom-clean *given* the named inputs + carried Kellner).

`FermatLastTheoremFor 37` from:
* `h_assembly : CaseIIRealAnchorDatumAssembly37` — the **sound** R2 producer residual: Washington's
  §9.1 / Theorem 9.4 conjugate-normed Fermat-equation assembly realising the conjugate norm
  `ξ₁ = ρ₀σρ₀` (real, `𝔭`-coprime, `(ξ₁) = 𝔞₀²`, **all proven** in
  `caseII_anchorPow_conjNorm_real_span`) as the next-level real Fermat variable.  Unlike the
  genuine-unit extraction data (over-strong: §4 forces `𝔞₀` principal), this is satisfiable for the
  irregular prime `37` — its ideal is the **doubled** `𝔞₀²`, which *is* principal;
* `caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source` — Assumption II
  (`η_a = u³⁷·η_b`), the Lemma-9.9 unit-power step (Kellner / Cor 8.15 / Lemma 9.8 content);
* `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — the carried Kellner input.

Everything else is proven and supplied by
`fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum`
(via `caseIIWashingtonAnchorSquareDatum37_of_realAnchorDatumAssembly`, which feeds the proven
conjugate norm into the assembly residual): II1, the terminal first-layer contradiction, Case I
(Eichler), `¬ 37 ∣ h⁺`, the support-arithmetic strict factor drop.

This is the **R2 producer** in its sound form: the conjugate-norm assembly is the genuine open
content (the Hilbert-90-twisted descent `ω₁³⁷ + θ₁³⁷ = ε·λ^{(2m−1)p}·ξ₁³⁷`), and the anchor-cube
ideal factorization + conjugate-norm reality + anchor-square ideal are all proven. -/
theorem fermatLastTheoremFor_thirtyseven_of_conjNormAnchorAssembly
    (h_assembly : CaseIIRealAnchorDatumAssembly37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum
    (caseIIWashingtonAnchorSquareDatum37_of_realAnchorDatumAssembly h_assembly)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end
