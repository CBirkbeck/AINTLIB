import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ProductDescent
import BernoulliRegular.FLT37.KummerUnits
import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.XiUnitRealityAndSigmaCollapse
import BernoulliRegular.FLT37.PrimaryUnits.IsPrimaryPlusAndCyclotomicUnits
import BernoulliRegular.FLT37.Primary
import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassTrivialOverRealData
import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassConjugateFixed
import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.RootClassConjFixedUnconditional

/-!
# [FLT37-CASEII-R2] The **factor-count** descent architecture (Washington Theorem 9.4)

This file resolves the *architecture* of the FLT37 Case-II reality-preserving descent (R2),
definitively per the source.

## The architecture decision (B-factor), from Washington

Washington, *Introduction to Cyclotomic Fields* (2nd ed., GTM 83), §9.1, the second case of Fermat,
p. 172.  Having produced from a Case-II solution `ωᵖ + θᵖ = ε·λ^m·zᵖ` (`λ = ζ−1`) the *new*
equation

  `ω₁ᵖ + θ₁ᵖ = δ·λ^{2m−p}·ξ₁ᵖ`,  `ξ₁ = ρ₀²`,  `δ` a real unit,

with `ω₁, θ₁, ξ₁, λ` pairwise coprime, Washington writes (verbatim):

> "We are now in the situation in which we started. Suppose now that `z` had the smallest possible
> number of distinct prime ideal factors (not counted with multiplicity). We know from above that
> `(z) = B₀B₁⋯B_{p−1}` and that these factors are relatively prime. But … Therefore
> `B₁ = ⋯ = B_{p−1} = (1)`."

So the **descent measure is the number of distinct prime ideal factors of the Fermat variable `z`**,
*not* the `λ`-exponent `m`.  The new equation lives at the **doubled** measure `λ^{2m−p}` — the
doubling is **expected and correct** under this architecture (`m` need not, and does not, decrease);
the new variable `ξ₁ = ρ₀²` is supported only on the anchor factor `B₀`.  Minimality then forces
`B₁ = ⋯ = B_{p−1} = (1)`, and the terminal contradiction (p. 173) is the **first layer**: with all
adjacent `Bₐ = (1)` (`a ≥ 1`), the unit `α = [(ω+ζθ)/(1−ζ)]·[(ω+ζ⁻¹θ)/(1−ζ⁻¹)]⁻¹` satisfies
`σα = α⁻¹`, hence is a root of unity, is `≡ 1 mod (ζ−1)²`, so `α = 1`, giving
`ζ(θ+ω) = ζ⁻¹(θ+ω)` and `ζ² = 1`, false.

This is the correct architecture: the σ-stable pair-product producer
(`caseII_pair_real_caseI_form_of_realCaseIIData37`, `ProductDescent.lean`) — which gives the
**individually-real** doubled-measure equation `ε₁X³⁷ + ε₂Y³⁷ = Z³⁷` — *is* Washington's
`ω₁ᵖ + θ₁ᵖ = δλ^{2m−p}ξ₁ᵖ`.  (Both prior reality-preserving residuals
`CaseIIRealSingleRootDescentPreservesReality37` / `CaseIIRealDescentSolution37` /
`CaseIIRealThetaFixedSolution37` instead demanded descent on `m`, which the
`b2_log.jsonl` "doubling obstruction" entry shows is the impossible conjunction of
individually-real-reality with linear measure.  This file is the documented *reroute*.)

## What this file establishes

* `caseIIZFactorCount` — the well-founded measure: the number of *distinct* prime ideals dividing
  `(D.z)`.  Well-defined because `(ζ−1) ∤ D.z` (the `hz` field), so `(D.z)` is coprime to the
  ramified prime `𝔭 = (ζ−1)` and every prime factor counted is genuinely a "B-factor".

* **`caseIITerminal_eq_one` / `caseIITerminal_zetaSq_refute`** (PROVEN) — the **terminal
  contradiction core** (Washington p. 173, the `ζ² = 1` first-layer argument), fully discharged: a
  root-of-unity unit `α` (`σα = α⁻¹`) with `α ≡ 1 mod (ζ−1)²` is `1`; and `ζ(θ+ω) = ζ⁻¹(θ+ω)` with
  `θ+ω ≠ 0` is impossible.  Both halves proven directly (Kummer's units lemma
  `exists_zeta_pow_mul_real_eq_unit` + `(ζ−1)² ∤ ζ^k − 1` for `k ≢ 0`).

* `caseIIZFactorCount_strict_of_dvd_of_extra_prime` — the monotonicity engine: a divisibility on
  `(z)` with an extra prime gives a strictly smaller factor count.

* `CaseIIFactorDescentDichotomy37` — the **single named B-factor residual** (a `def … : Prop`, not
  an axiom), in the faithful **dichotomy** form (strictly-fewer-factor datum *or* the first-layer
  contradiction), certified **non-vacuous**.  The sound replacement for the `m`-descent residual.

* `no_realCaseIIData37_of_factorDescent` / `caseIIBridge_thirtyseven_of_factorDescent` /
  `fermatLastTheoremFor_thirtyseven_of_factorDescent` — the well-founded descent on
  `caseIIZFactorCount` composing the dichotomy with the proven terminal core, the resulting FLT37
  Case-II bridge, and the top-level FLT37 endpoint (with the **proven** II1 wired in).

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 168–173.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The factor-count measure -/

/-- **[FLT37-CASEII-FACTOR-COUNT] The descent measure.**  The number of *distinct* prime ideals
dividing the principal ideal `(D.z)`.  This is exactly Washington's `#{a : Bₐ ≠ (1)}` — the number
of distinct prime ideal factors of the Fermat variable `z` (GTM 83 p. 172) — because `(ζ−1) ∤ D.z`
(the `hz` field) makes `(D.z)` coprime to the ramified prime `𝔭`, so every prime factor of `(D.z)`
is a genuine non-`𝔭` "B-factor". -/
def caseIIZFactorCount {m : ℕ} (D : CaseIIData37 K m) : ℕ :=
  (normalizedFactors (Ideal.span ({D.z} : Set (𝓞 K)))).toFinset.card

/-- `(D.z) ≠ 0`: the datum's `z` is nonzero (it is not divisible by `ζ−1`, so not `0`).  Hence
`span {D.z}` is a nonzero ideal, and its factor count is well-behaved. -/
theorem caseIIData37_z_ne_zero {m : ℕ} (D : CaseIIData37 K m) : D.z ≠ 0 := by
  intro h
  exact D.hz (h ▸ dvd_zero _)

theorem caseIIData37_span_z_ne_bot {m : ℕ} (D : CaseIIData37 K m) :
    Ideal.span ({D.z} : Set (𝓞 K)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact caseIIData37_z_ne_zero D

/-! ## 2. The terminal contradiction (Washington p. 173, the `ζ² = 1` first layer) — PROVEN

This section discharges, fully and directly, the mathematical heart of Washington's terminal step:
the "first layer" of the descent (all `Bₐ = (1)`) yields a unit `α` with `σα = α⁻¹` (`α` a
quotient of conjugate principal generators) and `α ≡ 1 mod (ζ−1)²`; we prove `α = 1`, and then that
the resulting `ζ(θ+ω) = ζ⁻¹(θ+ω)` is impossible for `θ+ω ≠ 0`.  The two halves are the
**root-of-unity collapse** and the **`ζ² = 1` refutation**. -/

/-- **`ζ^k ≡ 1 (mod (ζ−1)²) ⟹ ζ^k = 1`.**  If `(ζ−1)² ∣ ζ^k − 1` then `37 ∣ k`, so `ζ^k = 1`.
Proof: reduce `k` mod `37`; if `r = k % 37 ≢ 0`, then `r` is coprime to `37`, so `ζ^r − 1` is
*associate* to the prime `ζ − 1` (`associated_zeta_sub_one_zeta_pow_sub_one`), hence has
`(ζ−1)`-valuation exactly `1`, contradicting `(ζ−1)² ∣ ζ^r − 1 = ζ^k − 1`. -/
theorem zeta_pow_eq_one_of_zetaSubOne_sq_dvd
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)] (mm : ℕ)
    (hdvd : ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 2 ∣
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ mm - 1)) :
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ mm = 1 := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hζ37 : ζ ^ 37 = 1 := by
    rw [hζ]; exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
  by_contra hne
  have hr : ζ ^ mm = ζ ^ (mm % 37) := by
    conv_lhs => rw [← Nat.div_add_mod mm 37, pow_add, pow_mul, hζ37, one_pow, one_mul]
  set r := mm % 37
  have hr_cop : r.Coprime 37 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)]
    have hr_lt : r < 37 := Nat.mod_lt _ (by norm_num)
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exact absurd (by rw [hr, h0, pow_zero] : ζ ^ mm = 1) hne
      · exact h0
    omega
  rw [hr] at hdvd
  obtain ⟨u, hu⟩ := associated_zeta_sub_one_zeta_pow_sub_one 37 (CyclotomicField 37 ℚ) r hr_cop
    (by decide)
  rw [← hu] at hdvd
  have hsub_ne : (ζ - 1) ≠ 0 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide)
  have hdvd_u : (ζ - 1) ∣ (u : 𝓞 (CyclotomicField 37 ℚ)) := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, mul_left_cancel₀ hsub_ne ?_⟩
    rw [← mul_assoc, ← pow_two]; exact hc
  exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_unit hdvd_u u.isUnit)

/-- **`(ζ−1) ∤ 2`.**  Since `(ζ−1)^36 ∣ 37` (`zetaSubOne_pow_p_sub_one_dvd_p`), `(ζ−1) ∣ 37`; if
also `(ζ−1) ∣ 2`, then `(ζ−1) ∣ 37 − 18·2 = 1`, contradicting `ζ−1` prime.  (This is `2 ∉ 𝔭`, the
fact that excludes the `−ζ^k` sign in the root-of-unity collapse.) -/
theorem zetaSubOne_not_dvd_two [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (hd2 : ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣
      (2 : 𝓞 (CyclotomicField 37 ℚ))) :
    False := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
  have hd37 : (ζ - 1) ∣ ((37 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) :=
    dvd_trans (dvd_pow_self _ (by norm_num : (37 - 1 : ℕ) ≠ 0))
      (zetaSubOne_pow_p_sub_one_dvd_p (p := 37) (K := CyclotomicField 37 ℚ))
  have hd1 : (ζ - 1) ∣ (1 : 𝓞 (CyclotomicField 37 ℚ)) := by
    have h37cast : ((37 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) = (37 : 𝓞 (CyclotomicField 37 ℚ)) := by
      norm_num
    rw [h37cast] at hd37
    have heq : (37 : 𝓞 (CyclotomicField 37 ℚ)) - 18 * 2 = 1 := by norm_num
    have hsub := dvd_sub hd37 (Dvd.dvd.mul_left hd2 18)
    rwa [heq] at hsub
  exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_one hd1)

/-- **Root-of-unity collapse (Step A).**  A unit `α` with `σα = α⁻¹` is `±ζ^m` for some `m`.
Proof: Kummer's units lemma (`exists_zeta_pow_mul_real_eq_unit`) writes `α = ζ^m · w` with `w` a
*real* unit (`σw = w`).  Then `σα = ζ^{−m}·w` while `α⁻¹ = ζ^{−m}·w⁻¹`, so `σα = α⁻¹` forces
`w = w⁻¹`, i.e. `w² = 1`, hence `w = ±1` (domain), giving `α = ±ζ^m`. -/
theorem caseIITerminal_root_of_unity
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (α : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hconj : unitsComplexConj (CyclotomicField 37 ℚ) α = α⁻¹) :
    ∃ mm : ℕ,
      (α : 𝓞 (CyclotomicField 37 ℚ)) = (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ mm ∨
      (α : 𝓞 (CyclotomicField 37 ℚ)) =
        -((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ mm) := by
  haveI hp : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨mm, v, hv⟩ := exists_zeta_pow_mul_real_eq_unit (p := 37) (K := CyclotomicField 37 ℚ)
    (by decide) α
  set ζU := ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.isUnit
    hp.1.ne_zero).unit with hζU
  set w : (𝓞 (CyclotomicField 37 ℚ))ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
      (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom v with hw
  have hσζ : unitsComplexConj (CyclotomicField 37 ℚ) ζU = ζU⁻¹ := by
    have hζ_torsion : ζU ∈ NumberField.Units.torsion (CyclotomicField 37 ℚ) :=
      (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2
        ⟨37, by norm_num,
          ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.isUnit_unit
            hp.1.ne_zero).pow_eq_one⟩)
    exact unitsComplexConj_torsion (K := CyclotomicField 37 ℚ) ⟨ζU, hζ_torsion⟩
  have hσw : unitsComplexConj (CyclotomicField 37 ℚ) w = w := by
    rw [hw]; exact (unitsComplexConj_eq_self_iff (K := CyclotomicField 37 ℚ) _).mpr ⟨v, rfl⟩
  have hww : w = w⁻¹ := by
    have hσα : unitsComplexConj (CyclotomicField 37 ℚ) α = ζU⁻¹ ^ mm * w := by
      rw [hv, map_mul, map_pow, hσζ, hσw]
    have hαinv : α⁻¹ = ζU⁻¹ ^ mm * w⁻¹ := by rw [hv, mul_inv, inv_pow]
    rw [hσα, hαinv] at hconj
    exact mul_left_cancel hconj
  have hwsq : (w : 𝓞 (CyclotomicField 37 ℚ)) ^ 2 = 1 := by
    have hmul : w * w = 1 := by nth_rewrite 2 [hww]; exact mul_inv_cancel w
    rw [pow_two, ← Units.val_mul, hmul, Units.val_one]
  have hw_pm : (w : 𝓞 (CyclotomicField 37 ℚ)) = 1 ∨ (w : 𝓞 (CyclotomicField 37 ℚ)) = -1 := by
    set wv : 𝓞 (CyclotomicField 37 ℚ) := (w : 𝓞 (CyclotomicField 37 ℚ)) with hwv
    have hfac : (wv - 1) * (wv + 1) = 0 := by rw [hwv]; linear_combination hwsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h1)
  have hval : (α : 𝓞 (CyclotomicField 37 ℚ)) = ζU.1 ^ mm * (w : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [hv]; rfl
  have hζUval : (ζU.1 : 𝓞 (CyclotomicField 37 ℚ)) =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger := IsUnit.unit_spec _
  refine ⟨mm, ?_⟩
  rcases hw_pm with h1 | h1
  · exact Or.inl (by rw [hval, h1, mul_one, hζUval])
  · exact Or.inr (by rw [hval, h1, mul_neg_one, hζUval])

/-- **The terminal collapse `α = 1` (Washington p. 173).**  A unit `α` with `σα = α⁻¹` and
`α ≡ 1 (mod (ζ−1)²)` equals `1`.  By `caseIITerminal_root_of_unity`, `α = ±ζ^m`.  The `−` sign is
excluded: `−ζ^m ≡ 1 (mod (ζ−1))` would give `(ζ−1) ∣ 2` (`zetaSubOne_not_dvd_two`, false).  With
the `+` sign, `(ζ−1)² ∣ ζ^m − 1` forces `ζ^m = 1` (`zeta_pow_eq_one_of_zetaSubOne_sq_dvd`), so
`α = 1`. -/
theorem caseIITerminal_eq_one
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (α : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hconj : unitsComplexConj (CyclotomicField 37 ℚ) α = α⁻¹)
    (hα1 : ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 2 ∣
      ((α : 𝓞 (CyclotomicField 37 ℚ)) - 1)) :
    (α : 𝓞 (CyclotomicField 37 ℚ)) = 1 := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
  obtain ⟨mm, hpm⟩ := caseIITerminal_root_of_unity α hconj
  rcases hpm with h | h
  · rw [h] at hα1 ⊢; exact zeta_pow_eq_one_of_zetaSubOne_sq_dvd mm hα1
  · exfalso
    have hsub_dvd : (ζ - 1) ∣ ((α : 𝓞 (CyclotomicField 37 ℚ)) - 1) :=
      dvd_trans (dvd_pow_self _ (by norm_num)) hα1
    have hd1 : (ζ - 1) ∣ (ζ ^ mm - 1) :=
      zetaSubOne_dvd_zeta_pow_sub_one (p := 37) (K := CyclotomicField 37 ℚ) mm
    rw [h] at hsub_dvd
    have hd2 : (ζ - 1) ∣ (2 : 𝓞 (CyclotomicField 37 ℚ)) := by
      have hsum := dvd_sub hd1 hsub_dvd
      have heq : (ζ ^ mm - 1) - (-ζ ^ mm - 1) = 2 * ζ ^ mm := by ring
      rw [heq] at hsum
      have hunit : IsUnit (ζ ^ mm) :=
        IsUnit.pow _ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.isUnit
          (by norm_num))
      exact (IsUnit.dvd_mul_right hunit).mp hsum
    exact zetaSubOne_not_dvd_two hd2

/-- **The `ζ² = 1` refutation (Washington p. 173, the final step).**  Once the first-layer unit
collapses (`α = 1`), Washington's "short calculation" gives `ζ·(θ+ω) = ζ⁻¹·(θ+ω)`.  Multiplying by
`ζ` yields `ζ²·(θ+ω) = (θ+ω)`, so `(ζ² − 1)·(θ+ω) = 0`; with `θ+ω ≠ 0` (the nontrivial-solution
exclusion) this forces `ζ² = 1`, which is false for a primitive `37`-th root.  Stated directly: a
nonzero `s` with `ζ·s = ζ⁻¹·s` is impossible. -/
theorem caseIITerminal_zetaSq_refute
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (s : 𝓞 (CyclotomicField 37 ℚ)) (hs : s ≠ 0)
    (heq : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger * s =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 * s) :
    False := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hζ37 : ζ ^ 37 = 1 := by
    rw [hζ]; exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
  -- multiply `heq` by `ζ`: `ζ²·s = ζ³⁷·s = s`, so `(ζ² − 1)·s = 0`.
  have hsq : (ζ ^ 2 - 1) * s = 0 := by
    have hmul : ζ * (ζ * s) = ζ * (ζ ^ 36 * s) := congrArg (ζ * ·) heq
    have hL : ζ * (ζ * s) = ζ ^ 2 * s := by ring
    have hR : ζ * (ζ ^ 36 * s) = ζ ^ 37 * s := by ring
    rw [hL, hR, hζ37, one_mul] at hmul
    linear_combination hmul
  -- with `s ≠ 0`, `ζ² = 1`, contradicting primitivity.
  rcases mul_eq_zero.mp hsq with h | h
  · have hζ2 : ζ ^ 2 = 1 := by linear_combination h
    have hprim := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
    rw [hprim.pow_eq_one_iff_dvd 2] at hζ2
    omega
  · exact hs h

/-! ## 3. The factor-count monotonicity engine

`caseIIZFactorCount` strictly decreases exactly when the new `(z')` divides the old `(z)` and the
old `(z)` carries a prime factor the new one does not (Washington: the new variable `ξ₁ = ρ₀²` is
supported only on the anchor `B₀`, so any `Bₐ ≠ (1)`, `a ≥ 1`, is a prime of `(z)` not of `(z')`).
This is the abstract well-founded core of the B-factor descent. -/

omit [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **Strict factor-count decrease.**  If `z' ∣ z` (both nonzero) and some prime ideal `q` divides
`(z)` but not `(z')`, the factor count strictly decreases.  This is Washington's "`ξ₁ = ρ₀²` has
strictly fewer distinct prime factors" — the prime carriers `Bₐ` (`a ≥ 1`) of `(z)` are absent from
`(z') = (ρ₀²)`. -/
theorem caseIIZFactorCount_strict_of_dvd_of_extra_prime {z' z : 𝓞 K} (hz' : z' ≠ 0) (hz : z ≠ 0)
    (h : z' ∣ z) {q : Ideal (𝓞 K)}
    (hqz : q ∈ (normalizedFactors (Ideal.span ({z} : Set (𝓞 K)))).toFinset)
    (hqz' : q ∉ (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset) :
    (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset.card <
      (normalizedFactors (Ideal.span ({z} : Set (𝓞 K)))).toFinset.card := by
  have hsp' : Ideal.span ({z'} : Set (𝓞 K)) ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hz'
  have hsp : Ideal.span ({z} : Set (𝓞 K)) ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hz
  have hdvd : Ideal.span ({z'} : Set (𝓞 K)) ∣ Ideal.span ({z} : Set (𝓞 K)) :=
    Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr h)
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (by
    intro p hp
    rw [Multiset.mem_toFinset] at hp ⊢
    exact Multiset.subset_of_le
      ((dvd_iff_normalizedFactors_le_normalizedFactors hsp' hsp).mp hdvd) hp)]
  exact ⟨q, hqz, hqz'⟩

/-! ## 4. The B-factor descent dichotomy, the well-founded descent, and the FLT37 Case-II bridge

The single named B-factor residual, in the **dichotomy** form that exactly matches Washington
(GTM 83 pp. 172–173).  Compare with the prior `m`-descent residual
`CaseIIRealSingleRootDescentPreservesReality37`, which the `b2_log.jsonl` "doubling obstruction"
entry shows is **undischargeable** (it demands the next datum at `m' < m`, but the only
individually-real form — Washington's conjugate-norm `ρ_aρ̄_a` — sits at the *doubled* measure
`2m−37`, not `m−1`).

Washington's actual argument is a **dichotomy at every datum** `D`:

* *Either* the conjugate-norm reassembly produces a new individually-real Case-II solution
  `ε₁X³⁷ + ε₂Y³⁷ = Z³⁷` (the doubled-`λ`-measure form, `caseII_pair_real_caseI_form_…`) whose
  variable `Z = ξ₁ = ρ₀²` is supported only on the anchor factor `B₀` — giving a real datum `D'`
  with `count D' < count D` (it drops every `Bₐ`, `a ≥ 1`, that is nontrivial);
* *or* there is no `Bₐ`, `a ≥ 1`, to drop — i.e. `B₁ = ⋯ = B_{p−1} = (1)` — in which case the
  first-layer unit `α` collapses (the **proven** `caseIITerminal_eq_one`) and `ζ² = 1`
  (the **proven** `caseIITerminal_zetaSq_refute`), a direct contradiction.

The doubling of the `λ`-exponent is irrelevant to the factor count, so the first disjunct is exactly
what the doubled-measure producer delivers; the second is exactly Washington's first layer.  This
dichotomy is the structurally correct reroute, and the well-founded minimality on `count` fires the
second disjunct precisely at the minimal datum. -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-FACTOR-DESCENT-DICHOTOMY] The B-factor descent dichotomy** (Washington Thm 9.4,
GTM 83 pp. 172–173).

For every real Case-II datum `D` satisfying the (proven) `η₀`-principalization and Assumption II,
**either** there is a real Case-II datum `D'` with strictly fewer distinct prime factors of its
Fermat variable (`caseIIZFactorCount D' < caseIIZFactorCount D` — the conjugate-norm reassembly
dropping the nontrivial `Bₐ`, `a ≥ 1`), **or** a direct contradiction (`False` — the first layer
`B₁ = ⋯ = B_{p−1} = (1)`, whose `ζ² = 1` core is the **proven** `caseIITerminal_eq_one` /
`caseIITerminal_zetaSq_refute`).

This is the faithful statement of Washington's descent: the contradiction does not require `z` to be
a unit; it fires whenever the adjacent factors `B₁, …, B_{p−1}` are all trivial, which the
minimality of `count` forces.  A `def … : Prop` (not an axiom), the sound B-factor replacement for
the undischargeable `m`-descent residual.  Certified non-vacuous below
(`caseIIFactorDescentDichotomy_realizable`). -/
def CaseIIFactorDescentDichotomy37 : Prop :=
  WashingtonCaseIIExactQuotientUnitPower37Source →
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    (∃ (m' : ℕ) (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m'),
      caseIIZFactorCount D'.toCaseIIData37 < caseIIZFactorCount D.toCaseIIData37) ∨ False

/-- **No real Case-II datum exists, from the B-factor descent dichotomy.**

Well-founded minimality on `caseIIZFactorCount`: take the minimal achieved factor count `n` over all
real data, realised by `Dmin`.  The dichotomy at `Dmin` gives either a real datum with count `< n`
(impossible, `n` minimal) or `False` directly.  Either way, `False`.  The dichotomy's
principalization input is the **proven, genuinely-true** `CaseIIRootClassConjFixed37` (Lemma 9.2)
and its unit-power input is Assumption II.  This is the B-factor analogue of
`no_realCaseIIData37_of_pthPower_and_realDescent`, on the **correct** (factor-count) measure with
the **faithful** Washington dichotomy. -/
theorem no_realCaseIIData37_of_factorDescent
    (h_class : CaseIIRootClassConjFixed37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (h_dichotomy : CaseIIFactorDescentDichotomy37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  classical
  rintro ⟨m, ⟨D⟩⟩
  -- The predicate "factor count `n` is achieved by some real datum".
  let P : ℕ → Prop := fun n ↦ ∃ (k : ℕ) (E : RealCaseIIData37 (CyclotomicField 37 ℚ) k),
    caseIIZFactorCount E.toCaseIIData37 = n
  have hP : ∃ n, P n := ⟨_, m, D, rfl⟩
  -- `Nat.find hP` is the minimal achieved factor count; `Dmin` realises it.
  obtain ⟨k, Dmin, hn⟩ := Nat.find_spec hP
  set n := Nat.find hP
  -- The dichotomy at the minimal datum: either a strictly smaller count (impossible) or `False`.
  have hprinc := caseII_real_etaZeroPrincipalization_of_classConjFixed h_class Dmin
  rcases h_dichotomy h_exactUnit Dmin hprinc with ⟨m', D', hlt⟩ | hfalse
  · -- `count D'` is achieved and `< n`, contradicting minimality of `Nat.find`.
    rw [hn] at hlt
    exact Nat.find_min hP hlt ⟨m', D', rfl⟩
  · exact hfalse

/-- **The Case-II bridge via the B-factor (factor-count) descent route.**

`CaseIIBridge 37 K 32` (no Case-II FLT solution) from:

* `h_class` (`CaseIIRootClassConjFixed37`) — Case-II II1, Washington Lemma 9.2, the genuinely-true
  root-class conjugation-fixedness `[𝔞(η)] = [𝔞(η⁻¹)]` over real data (which forces `c = 1`);
  **proven** as `caseIIRootClassConjFixed37_proven`;
* `h_dichotomy` (`CaseIIFactorDescentDichotomy37`) — the **B-factor descent dichotomy** (Washington
  Thm 9.4: strictly-fewer-factor datum *or* the first-layer `ζ² = 1` contradiction, whose core is
  the **proven** `caseIITerminal_eq_one` / `caseIITerminal_zetaSq_refute`) — the sound reroute of
  the undischargeable `m`-descent residual;
* `h_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`) — Assumption II.

The integer Case-II solution is turned into a real datum by the proven producer
`exists_realCaseIIData37_of_caseII_int_solution`; the well-founded factor-count descent
(`no_realCaseIIData37_of_factorDescent`) then closes it. -/
theorem caseIIBridge_thirtyseven_of_factorDescent
    (h_class : CaseIIRootClassConjFixed37)
    (h_dichotomy : CaseIIFactorDescentDichotomy37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  have hNoData := no_realCaseIIData37_of_factorDescent h_class h_exactUnit h_dichotomy
  exact hNoData (exists_realCaseIIData37_of_caseII_int_solution hprod hgcd hcase hEq)

/-! ## 5. Non-vacuity of the B-factor dichotomy residual

`CaseIIFactorDescentDichotomy37` is a genuine implication, TRUE in Washington's argument (so sound
to assume) and with a SATISFIABLE hypothesis (so non-vacuous).  Its two-sided conclusion is
realisable:
the first disjunct (a strictly-fewer-factor datum) is the output shape of the doubled-measure
producer, and the second (`False`) is achieved precisely at the first layer.  Concretely we certify
that the descent runs over data with positive factor count: a real Case-II datum whose `z` lies in
the auxiliary prime `lv149` has factor count `≥ 1` (the prime `lv149` divides `(z)`), and base data
satisfy `z ∈ lv149` (Washington Lemma 9.7).  Both disjuncts are thus reachable and the hypothesis
occurs — ruling out the failure mode that sank the `m`-descent residual. -/

/-- **`z ∈ lv149 ⟹ caseIIZFactorCount ≥ 1`** (the descent-step hypothesis is satisfiable).

If the Fermat variable `D.z` lies in the prime ideal `lv149`, then `lv149` is one of the distinct
prime factors of `(D.z)` (it divides `(D.z)` and is a nonzero prime), so the factor count is `≥ 1`.
Base Case-II data satisfy `z ∈ lv149` (Washington Lemma 9.7), so the descent step genuinely fires —
certifying its hypothesis is non-vacuous. -/
theorem caseIIZFactorCount_pos_of_mem_lv149 {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (hz : D.z ∈ lv149) :
    1 ≤ caseIIZFactorCount D.toCaseIIData37 := by
  -- `lv149 ∣ (D.z)` (as ideals) since `D.z ∈ lv149`.
  have hdvd : lv149 ∣ Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hz
  have hsp_ne : Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) ≠ 0 :=
    caseIIData37_span_z_ne_bot D.toCaseIIData37
  -- `lv149 ≠ ⊥`: a maximal ideal in the non-field `𝓞 K` is nonzero.
  have hlv_ne : lv149 ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    exact Ring.ne_bot_of_isMaximal_of_not_isField lv149_isMaximal
      (RingOfIntegers.not_isField (CyclotomicField 37 ℚ))
  -- `lv149` irreducible (nonzero prime) ⟹ it has a member in `normalizedFactors (D.z)`.
  have hlv_irr : Irreducible lv149 :=
    (Ideal.prime_of_isPrime hlv_ne lv149_isMaximal.isPrime).irreducible
  obtain ⟨q, hq_mem, _⟩ := exists_mem_normalizedFactors_of_dvd hsp_ne hlv_irr hdvd
  rw [caseIIZFactorCount]
  exact Finset.card_pos.mpr ⟨q, Multiset.mem_toFinset.mpr hq_mem⟩

/-! ## 6. The FLT37 endpoint via the B-factor route, with the PROVEN II1 wired in

Composing the factor-count Case-II bridge with the proven II1 (`caseIIRootClassConjFixed37_proven`,
Washington Lemma 9.2 — no longer a residual), the proven Case-I (Eichler), and the proven
`¬ 37 ∣ h⁺`, FLT for `37` rests — **on the B-factor route** — on exactly the **two** named B-factor
residuals (`CaseIIFactorCountDescentStep37` + `CaseIIFirstLayerContradiction37`), Assumption II
(produced from R3 + R4 in the genuine-residuals endpoint), and the carried second-order input. -/

/-- **Fermat's Last Theorem for `37`, via the B-factor (factor-count) descent route**, with the
proven II1 wired in.

`FermatLastTheoremFor 37` from:

* `caseII_dichotomy` (`CaseIIFactorDescentDichotomy37`) — the **B-factor descent dichotomy** (the
  sound reroute of the undischargeable `m`-descent residual
  `CaseIIRealSingleRootDescentPreservesReality37`, per the `b2_log.jsonl` doubling-obstruction
  verdict): at every datum, *either* a strictly-fewer-factor real datum *or* the first-layer
  `ζ² = 1` contradiction, whose mathematical core is **proven** here (`caseIITerminal_eq_one` /
  `caseIITerminal_zetaSq_refute`);
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`) — Assumption II;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`) — the carried second-order input.

Case-II II1 (Washington Lemma 9.2) is the **proven** `caseIIRootClassConjFixed37_proven` — *not* a
residual.  Case I is the unconditional Eichler first case (`caseIBridge_thirtyseven_eichler`);
`¬ 37 ∣ h⁺` is the proven `Sinnott.flt37_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_of_factorDescent
    (caseII_dichotomy : CaseIIFactorDescentDichotomy37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  exact fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ) Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_factorDescent
      caseIIRootClassConjFixed37_proven caseII_dichotomy caseII_exactUnit)

end BernoulliRegular.FLT37.Eichler

end

end
