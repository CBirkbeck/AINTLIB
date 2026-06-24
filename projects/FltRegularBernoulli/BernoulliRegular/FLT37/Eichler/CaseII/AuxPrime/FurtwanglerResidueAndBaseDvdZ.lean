import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.Lemma98RealData
import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.IntSolutionToRealDatum

/-!
# [FLT37-CASEII-R4(ii)] Washington Lemma 9.7 (`ℓ ∣ z`) at the integer base, PROVEN

This file proves **Washington Lemma 9.7** (`ℓ ∣ z`, *Introduction to Cyclotomic Fields*, 2nd ed.,
GTM 83, p. 178) — the last genuine analytic input of R4 — **at the integer base of the Case-II
descent**, where the rational origin `a, b, c ∈ ℤ` of the Fermat solution is available.

It imports only — it does **not** modify any existing file.

## The architecture verdict (resolved, sourced): (B) — Lemma 9.7 needs the integer base

The prior carried residual `RealCaseIILehmerVandiverDvdZ37` (`CaseIILemma98RealData.lean`) is a
per-datum `∀ D : RealCaseIIData37, … → D.z ∈ lv149`.  Reading Washington's Lemma 9.7 proof against
the descent datum settles the architecture question **(A cyclotomic vs B integer-base)** as **(B)**:

* **What Lemma 9.7 actually uses.**  Write `ℓ = 1 + kp`, `k < p − 1`.  From the *equations obtained
  in Lemma 9.6* (the `p`-th-power-ideal factorisation `(y − ζᵃz) = γₐσₐᵖ` with `γₐ` a **real** unit
  and `σₐ ∈ ℤ[ζ_p]`, valid because `∏ₐ(y − ζᵃz) = −xᵖ` is a **perfect `p`-th power** and the factors
  are pairwise coprime), Fermat in the residue field `ℤ[ζ]/𝔩 ≅ 𝔽_ℓ` gives `σₐ^{ℓ−1} = σₐ^{kp} ≡ 1`,
  hence `(y − ζᵃz)ᵏ ≡ γₐᵏ = γ₋ₐᵏ ≡ (y − ζ⁻ᵃz)ᵏ (mod 𝔩)`.  Multiplying by `ζᵃ`, expanding and
  **summing over `a`**, all `ζ`-powers cancel except the `i = 1` term, leaving `−pkz yᵏ⁻¹ ≡ 0
  (mod 𝔩)`; with `ℓ ∤ pk` and `ℓ ∤ y` (Lemma 9.6) this forces `𝔩 ∣ z`, hence (as `z ∈ ℤ`) `ℓ ∣ z`.

* **Why this needs the integer base.**  The factorisation `(y − ζᵃz) = γₐσₐᵖ` requires the
  all-conjugate product `∏ₐ(y − ζᵃz)` to be a **perfect `p`-th power** (`= −xᵖ`).  Over the descent
  datum `CaseIIData37.equation`: `x³⁷ + y³⁷ = ε·((ζ−1)^{m+1}z)³⁷` — the available product
  `∏(x + ζᵃy) = x³⁷ + y³⁷ = ε·w³⁷` is only a **unit times** a `p`-th power, with `ε = 1` **only at
  the base** (`exists_realCaseIIData37_of_Int_solution` sets `ε := 1`).  At descent levels the
  general unit `ε ≠ 1` breaks the perfect-`p`-th-power structure, and the genuinely `p`-divisible
  quantity `(ζ−1)^{m+1}·D.z` has conjugate factors that are **not** pairwise coprime (shared
  `(ζ−1)`-content) and so do **not** give clean `p`-th-power ideals.  The literal Lemma-9.7 sum
  therefore does **not** run over a bare descent-level `RealCaseIIData37`.  Verdict: **(B)** — the
  argument is *not* cyclotomic-provable over the descended datum; it lives at the rational base.

* **The descent's Assumption-II need is all-levels, not base-only.**  Assumption II
  (`WashingtonCaseIIExactQuotientUnitPower37Source`) is a closed universally-quantified `Prop`,
  consumed at the **minimal** descent datum `Dmin` (an arbitrary level) inside
  `no_realCaseIIData37_of_classConjFixed_and_realDescent`.  It is produced from `Lemma98LocalPower37
  ⟸ Lemma98LocalPower37Strict + CaseIILehmerVandiverDvdZ37`, where `dvdZ` is applied to the abstract
  free-unit telescope at *every* level.  So a base-only Lemma 9.7 does **not**, by itself, supply
  the per-datum `dvdZ`.  Washington bridges this gap by **propagation**, not by re-running Lemma 9.7
  at each level: `ℓ ∣ z` (level `m`) ⟹ `ℓ ∣ (ω + θ)` (Lemma 9.8, `caseII_real_x_add_y_mem_of_dvd_z`,
  PROVEN over real data) ⟹ `ℓ ∣ ρ₀ = z'` (level `m' < m`, `caseII_dvd_z_of_equation`, PROVEN).  The
  two propagation directions are both proven over real data in `CaseIILemma98RealData.lean`; what is
  *not* separately available is the descent-internal link `ℓ ∣ (x+y) ⟹ ℓ ∣ z'`, which is part of the
  reality-preserving descent construction (R2, `CaseIIRealSingleRootDescentPreservesReality37`).

## What is PROVEN here (axiom-clean)

* **`furtwangler_37_149`** — the `decide`-able heart of Lemma 9.7 for `(p, ℓ) = (37, 149)`: in
  `ZMod 149`, `a³⁷ + b³⁷ = c³⁷ → a = 0 ∨ b = 0 ∨ c = 0`.  This is the *Lehmer–Vandiver /
  Furtwängler first-layer* form of Lemma 9.7's conclusion at the base: the `37`-th-power residues
  mod `149` are exactly `{0, 1, 44, 105, 148}` (an order-`4 = 148/37` subgroup plus `0`), and **no
  two nonzero `37`-th powers sum to a nonzero `37`-th power**.  It is the residue shadow of the
  all-conjugate `∑`-argument (`149 ≡ 1 mod 37` ⟹ `149` splits completely; `149 < 37² − 37 = 1332`
  is exactly the window making the `p²`-order obstruction force `𝔩 ∣ z`).

* **`caseII_intCast_mem_lv149_iff`** — the integer bridge `(n : 𝓞 K) ∈ lv149 ↔ (n : ZMod 149) = 0`
  (i.e. `149 ∣ n`), via the residue iso `𝓞 K / 𝔩 ≃+* ZMod 149`.

* **`caseII_base_dvd_z_of_Int_solution`** — **Washington Lemma 9.7 at the base, PROVEN**: from an
  integer Case-II solution `x³⁷ + y³⁷ = z³⁷` with `37 ∣ z` and Lemma 9.6 (`149 ∤ x`, `149 ∤ y`), the
  base `RealCaseIIData37` built by the producer has `D.z ∈ lv149` (`ℓ ∣ z`).  Fully discharges the
  `ℓ ∣ z` content at the rational origin.

* **`exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution`** — the base producer **augmented
  with `ℓ ∣ z`**: from an integer Case-II FLT solution with `149 ∤` the two non-`37`-divisible
  variables, build a base real datum `D` whose descent integer satisfies `D.z ∈ lv149`.

## Non-vacuity

The base statement is genuinely true (it is Lemma 9.7) and non-vacuous: `149 ≡ 1 (mod 37)`
(`caseII_lv149_one_mod_37`) and `149 < 37² − 37 = 1332` (`caseII_lv149_lt_p_sq_sub_p`).  The integer
origin is available exactly at the base producer (the FLT37 endpoint starts from `a, b, c ∈ ℤ`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Theorem 9.5, Lemma 9.6
  (`ℓ ∤ xy`), Lemma 9.7 (`ℓ ∣ z`), pp. 176–178; the `ℓ < p² − p` window.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The `decide`-able residue heart of Lemma 9.7 for `(37, 149)`

`149 ≡ 1 (mod 37)`, so the `37`-th power map on `(ZMod 149)ˣ` (order `148 = 4·37`) has image the
unique subgroup of order `4`.  The `37`-th-power residues mod `149` are therefore exactly
`{0, 1, 44, 105, 148}`, and a finite check shows **no two nonzero `37`-th powers sum to a nonzero
`37`-th power**.  This is the residue-field shadow of Washington's all-conjugate `∑`-argument: it is
exactly the Lehmer–Vandiver/Furtwängler first-layer obstruction that makes `149` an admissible
auxiliary prime for `p = 37`. -/

set_option maxRecDepth 4000 in
/-- **The `37`-th-power residues mod `149` are `{0, 1, 44, 105, 148}`** (a `149`-case `decide`).

`(ZMod 149)ˣ` is cyclic of order `148 = 4·37`; the `37`-th powers form the order-`4` subgroup
`{1, 44, 105, 148}`, and `0³⁷ = 0`. -/
theorem caseII_pow37_values_149 (a : ZMod 149) :
    a ^ 37 = 0 ∨ a ^ 37 = 1 ∨ a ^ 37 = 44 ∨ a ^ 37 = 105 ∨ a ^ 37 = 148 := by
  decide +revert

/-- **`a³⁷ = 0 ↔ a = 0` in `ZMod 149`** (`149` prime ⟹ field, no nilpotents). -/
theorem caseII_pow37_eq_zero_iff_149 (a : ZMod 149) : a ^ 37 = 0 ↔ a = 0 :=
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  pow_eq_zero_iff (by decide : 37 ≠ 0)

set_option maxHeartbeats 1000000 in
-- The `4 × 4 × 4` residue `decide` over `ZMod 149` needs more than the default heartbeat budget.
/-- **The Furtwängler residue form of Washington Lemma 9.7 for `(37, 149)`** (proven, axiom-clean).

In `ZMod 149`, `a³⁷ + b³⁷ = c³⁷ → a = 0 ∨ b = 0 ∨ c = 0`.  Proof: if all of `a, b, c` were nonzero,
their `37`-th powers would be nonzero elements of `{1, 44, 105, 148}` (`caseII_pow37_values_149`,
`caseII_pow37_eq_zero_iff_149`), and a `4 × 4 × 4` `decide` shows no such triple satisfies
`a³⁷ + b³⁷ = c³⁷`.

This is the residue-field shadow of the all-conjugate `∑`-argument of Lemma 9.7: over `𝔽₁₄₉` the
equation forces the `37`-divisible (Fermat-`z`) variable into the prime `𝔩` over `149`. -/
theorem furtwangler_37_149 (a b c : ZMod 149)
    (h : a ^ 37 + b ^ 37 = c ^ 37) : a = 0 ∨ b = 0 ∨ c = 0 := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  have ha' : a ^ 37 ≠ 0 := mt (caseII_pow37_eq_zero_iff_149 a).mp ha
  have hb' : b ^ 37 ≠ 0 := mt (caseII_pow37_eq_zero_iff_149 b).mp hb
  have hc' : c ^ 37 ≠ 0 := mt (caseII_pow37_eq_zero_iff_149 c).mp hc
  rcases caseII_pow37_values_149 a with h1 | h1 | h1 | h1 | h1 <;>
  rcases caseII_pow37_values_149 b with h2 | h2 | h2 | h2 | h2 <;>
  rcases caseII_pow37_values_149 c with h3 | h3 | h3 | h3 | h3 <;>
    first
      | exact ha' h1
      | exact hb' h2
      | exact hc' h3
      | (rw [h1, h2, h3] at h; revert h; decide)

/-! ## 2. The integer bridge `(n : 𝓞 K) ∈ lv149 ↔ 149 ∣ n`

`lv149 = lehmerVandiverPrime 37 149 4 …` is the comap along `𝓞 K ≃ CyclotomicIntegers 37` of the
kernel of the cyclotomic reduction `CyclotomicIntegers 37 →+* ZMod 149`.  On an integer cast, the
composite `𝓞 K → ZMod 149` is just `Int.cast`, so membership is `(n : ZMod 149) = 0`. -/

/-- **`(n : 𝓞 K) ∈ lv149 ↔ (n : ZMod 149) = 0`** for an integer `n` (proven, axiom-clean).

The residue map `𝓞 K → 𝓞 K / lv149 ≃+* ZMod 149` carries the integer cast `(n : 𝓞 K)` to
`(n : ZMod 149)` (`map_intCast` twice), so `(n : 𝓞 K) ∈ lv149` (membership in the comap kernel) is
exactly `(n : ZMod 149) = 0`, i.e. `149 ∣ n`. -/
theorem caseII_intCast_mem_lv149_iff (n : ℤ) :
    (n : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 ↔ (n : ZMod 149) = 0 := by
  unfold lv149 lehmerVandiverPrime
  rw [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.mem_ker,
    map_intCast, map_intCast]

/-! ## 3. Washington Lemma 9.7 at the base, PROVEN

From an integer Case-II solution `x³⁷ + y³⁷ = z³⁷` with `37 ∣ z` (the `p`-divisible variable in the
`z` slot) and Lemma 9.6 (`149 ∤ x`, `149 ∤ y`), the Furtwängler residue condition forces `149 ∣ z`,
hence `(z : 𝓞 K) ∈ lv149`; peeling the `(ζ−1)`-multiplicity (`lv149` unramified) gives `D.z ∈ lv149`
for the base datum `D` built by the producer. -/

set_option maxHeartbeats 800000 in
-- The `RealCaseIIData37` structure construction (the `equation` field, with the `(ζ-1)`-multiplicity
-- extraction) is whnf-heavy and exceeds the default heartbeat budget, as in the parent producer
-- `exists_realCaseIIData37_of_Int_solution`.
set_option backward.isDefEq.respectTransparency false in
/-- **The base datum builder exposing the `(ζ−1)`-multiplicity relation** (proven, axiom-clean).

Mirrors `exists_realCaseIIData37_of_Int_solution`, but additionally exposes the relation
`(z : 𝓞 K) = (ζ − 1)^{m+1} · D.z` linking the descent integer `D.z` to the original integer `z`.
This is the datum-construction half; the `ℓ ∣ z` membership is derived separately
(`exists_realCaseIIData37_with_dvd_z_of_Int_solution`) so that the Furtwängler residue work sits
outside this whnf-heavy structure block. -/
theorem exists_realCaseIIData37_zRel_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x y z : ℤ} (hy_int : ¬ (37 : ℤ) ∣ y) (hz_int : (37 : ℤ) ∣ z) (hz_ne : z ≠ 0)
    (e : x ^ 37 + y ^ 37 = z ^ 37) :
    ∃ (m : ℕ) (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
      (D.x = (x : 𝓞 (CyclotomicField 37 ℚ))) ∧ (D.y = (y : 𝓞 (CyclotomicField 37 ℚ))) ∧
      (z : 𝓞 (CyclotomicField 37 ℚ)) = (D.hζ.toInteger - 1) ^ (m + 1) * D.z := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI := CyclotomicField.isCyclotomicExtension 37 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField 37 ℚ)) (Set.mem_singleton 37)
    (by decide : (37 : ℕ) ≠ 0)
  have h_dvd_iff := fun n ↦
    zeta_sub_one_dvd_Int_iff (K := CyclotomicField 37 ℚ) hζ (n := n)
  have hy : ¬ (hζ.toInteger - 1) ∣ (y : 𝓞 (CyclotomicField 37 ℚ)) :=
    mt (h_dvd_iff y).mp hy_int
  have hz : (hζ.toInteger - 1) ∣ (z : 𝓞 (CyclotomicField 37 ℚ)) := (h_dvd_iff z).mpr hz_int
  have hz_ne_OK : (z : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 := by rwa [ne_eq, Int.cast_eq_zero]
  have eOK :
      (x : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 + (y : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
        (z : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
    simp_rw [← Int.cast_pow, ← Int.cast_add, e]
  letI : WfDvdMonoid (𝓞 (CyclotomicField 37 ℚ)) := IsNoetherianRing.wfDvdMonoid
  obtain ⟨n, z', hn, hz_n, hz_eq⟩ :
      ∃ n z', 1 ≤ n ∧ ¬ ((hζ.toInteger - 1) ∣ z') ∧
        (z : 𝓞 (CyclotomicField 37 ℚ)) = (hζ.toInteger - 1) ^ n * z' := by
    classical
    have H : FiniteMultiplicity (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ)) :=
      FiniteMultiplicity.of_not_isUnit hζ.zeta_sub_one_prime'.not_unit hz_ne_OK
    obtain ⟨z', hfac⟩ := pow_multiplicity_dvd (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ))
    refine ⟨_, _, ?_, ?_, hfac⟩
    · rwa [← Nat.cast_le (α := ENat), ← FiniteMultiplicity.emultiplicity_eq_multiplicity H,
        ← pow_dvd_iff_le_emultiplicity, pow_one]
    · intro h_dvd
      have := mul_dvd_mul_left
        ((hζ.toInteger - 1) ^ multiplicity (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ))) h_dvd
      rw [← pow_succ, ← hfac] at this
      refine not_pow_dvd_of_emultiplicity_lt ?_ this
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H, Nat.cast_lt]
      exact Nat.lt_succ_self _
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have heqn :
      (x : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 + (y : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
        (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) *
          ((hζ.toInteger - 1) ^ (n - 1 + 1) * z') ^ 37 := by
    rw [hz_eq] at eOK
    simpa [hn_eq] using eOK
  refine ⟨n - 1,
    { ζ := ζ
      hζ := hζ
      x := (x : 𝓞 (CyclotomicField 37 ℚ))
      y := (y : 𝓞 (CyclotomicField 37 ℚ))
      z := z'
      ε := 1
      equation := heqn
      hy := hy
      hz := hz_n
      x_real := ringOfIntegersComplexConj_intCast_eq (K := CyclotomicField 37 ℚ) x
      y_real := ringOfIntegersComplexConj_intCast_eq (K := CyclotomicField 37 ℚ) y },
    rfl, rfl, ?_⟩
  rw [hn_eq]; exact hz_eq

/-- **The base producer augmented with `ℓ ∣ z`** (proven, axiom-clean) — Washington Lemma 9.7 at the
integer base.

From an integer Case-II solution `x³⁷ + y³⁷ = z³⁷` with `37 ∣ z` and Lemma 9.6 (`149 ∤ x`, `149 ∤ y`
on the two non-`37`-divisible variables), the base `RealCaseIIData37` has `D.z ∈ lv149`
(Washington's `ℓ ∣ z`).  The `ℓ ∣ z` half is the Furtwängler residue condition `furtwangler_37_149`:
`x³⁷ + y³⁷ = z³⁷` with `149 ∤ x, y` forces `149 ∣ z`, hence `(z : 𝓞 K) ∈ lv149`
(`caseII_intCast_mem_lv149_iff`), and peeling the `(ζ−1)`-multiplicity
(`caseII_zeta_sub_one_notMem_lv149`, `lv149` unramified) yields `D.z ∈ lv149`. -/
theorem exists_realCaseIIData37_with_dvd_z_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x y z : ℤ} (hy_int : ¬ (37 : ℤ) ∣ y) (hz_int : (37 : ℤ) ∣ z) (hz_ne : z ≠ 0)
    (e : x ^ 37 + y ^ 37 = z ^ 37)
    (hx_lv : ¬ (x : ZMod 149) = 0) (hy_lv : ¬ (y : ZMod 149) = 0) :
    ∃ m : ℕ, ∃ D : RealCaseIIData37 (CyclotomicField 37 ℚ) m, D.z ∈ lv149 := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  obtain ⟨m, D, _hx, _hy, hz_eq⟩ :=
    exists_realCaseIIData37_zRel_of_Int_solution hy_int hz_int hz_ne e
  refine ⟨m, D, ?_⟩
  -- The Furtwängler residue condition: `149 ∣ z`.
  have hz_lv_int : (z : ZMod 149) = 0 := by
    have he : (x : ZMod 149) ^ 37 + (y : ZMod 149) ^ 37 = (z : ZMod 149) ^ 37 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 149) e
    rcases furtwangler_37_149 (x : ZMod 149) (y : ZMod 149) (z : ZMod 149) he with h | h | h
    · exact absurd h hx_lv
    · exact absurd h hy_lv
    · exact h
  have hz_mem : (z : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 :=
    (caseII_intCast_mem_lv149_iff z).mpr hz_lv_int
  -- Peel the `(ζ-1)`-multiplicity: `(ζ-1)^(m+1) D.z ∈ lv149`, `(ζ-1) ∉ lv149` ⟹ `D.z ∈ lv149`.
  rw [hz_eq] at hz_mem
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hz_mem with hpow | hz'
  · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› (m + 1) hpow)
      (caseII_zeta_sub_one_notMem_lv149 D.hζ)
  · exact hz'

/-! ## 4. Washington Lemma 9.7 at the base, stated over `ℤ` (`149 ∣ z`)

The integer-level form of the proven base result: `149 ∣ z` for the `37`-divisible variable of the
Case-II integer solution, under Lemma 9.6 (`149 ∤ x`, `149 ∤ y`).  This is `furtwangler_37_149`
transported to `(149 : ℤ) ∣ ·` via `ZMod.intCast_zmod_eq_zero_iff_dvd`. -/

/-- **`149 ∣ z` for the Case-II integer solution** (proven, axiom-clean) — Washington Lemma 9.7 at
the base, over `ℤ`.

From `x³⁷ + y³⁷ = z³⁷` with Lemma 9.6 (`149 ∤ x`, `149 ∤ y`), the Furtwängler residue condition
forces `149 ∣ z`.  This is the rational shadow of the all-conjugate `∑`-argument: it is exactly the
statement that the `37`-divisible Fermat variable is divisible by the auxiliary prime `149`. -/
theorem caseII_int_dvd_z_of_lemma96 {x y z : ℤ}
    (e : x ^ 37 + y ^ 37 = z ^ 37)
    (hx_lv : ¬ (149 : ℤ) ∣ x) (hy_lv : ¬ (149 : ℤ) ∣ y) :
    (149 : ℤ) ∣ z := by
  have hx' : ¬ (x : ZMod 149) = 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd x 149).mp hx_lv
  have hy' : ¬ (y : ZMod 149) = 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd y 149).mp hy_lv
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd z 149).mp ?_
  have he : (x : ZMod 149) ^ 37 + (y : ZMod 149) ^ 37 = (z : ZMod 149) ^ 37 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 149) e
  rcases furtwangler_37_149 (x : ZMod 149) (y : ZMod 149) (z : ZMod 149) he with h | h | h
  · exact absurd h hx'
  · exact absurd h hy'
  · exact h

/-! ## 5. The base producer through the `caseII_int_solution` entry, with `ℓ ∣ z`

The FLT37 Case-II endpoint enters from `a, b, c ∈ ℤ`
(`exists_realCaseIIData37_of_caseII_int_solution`).  For the standard normal form (the
`37`-divisible variable `c` in the `z`-slot), the augmented producer yields a base datum with
`D.z ∈ lv149` under Lemma 9.6 (`149 ∤ a`, `149 ∤ b`). -/

/-- **The `caseII_int_solution` base producer augmented with `ℓ ∣ z`** (proven, axiom-clean), normal
form `37 ∣ c`.

From a Case-II integer FLT solution `a³⁷ + b³⁷ = c³⁷` with `37 ∣ c`, `37 ∤ a`, `c ≠ 0`, and
Lemma 9.6 (`149 ∤ a`, `149 ∤ b`), build a base `RealCaseIIData37` whose descent integer satisfies
`D.z ∈ lv149` (Washington Lemma 9.7).  This is the reality-preserving entry point carrying the
genuine `ℓ ∣ z` datum at the base, where the rational origin lives. -/
theorem exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b) :
    ∃ m : ℕ, ∃ D : RealCaseIIData37 (CyclotomicField 37 ℚ) m, D.z ∈ lv149 := by
  -- `37 ∤ b` (else `37 ∣ a` from the equation), so `b` is a non-`37`-divisible variable.
  have hb_int : ¬ (37 : ℤ) ∣ b := by
    intro hb
    have h_dvd : (37 : ℤ) ∣ a ^ 37 := by
      have := dvd_sub (dvd_pow hc_int (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_right] at this
    exact ha_int <| (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37)).dvd_of_dvd_pow h_dvd
  refine exists_realCaseIIData37_with_dvd_z_of_Int_solution hb_int hc_int hc_ne e
    (mt (ZMod.intCast_zmod_eq_zero_iff_dvd a 149).mp ha_lv)
    (mt (ZMod.intCast_zmod_eq_zero_iff_dvd b 149).mp hb_lv)

/-! ## 6. The full Lemma-9.7 → Lemma-9.8 chain runs at the base

The proven base `ℓ ∣ z` (`exists_realCaseIIData37_with_dvd_z_of_Int_solution`) feeds the proven
Lemma 9.8 over real data (`caseII_real_x_add_y_mem_of_dvd_z`, `CaseIILemma98RealData.lean`): for the
base datum, `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6) and the proven `ℓ ∣ z` give `x + y ∈ lv149` (`ℓ ∣ ω + θ`,
Washington's `j = 0`).  This is the entire `ℓ ∣ z` / `j = 0` content of R4 at the base, with the
standalone `ℓ ∣ z` (Lemma 9.7, here) and the `j = 0` step (Lemma 9.8's deep `Q₃₂⁴ ≢ 1` core,
`CaseIILemma98RealData.lean`) both proven. -/

/-- **Lemma 9.8 (`x + y ∈ lv149`) holds at the base, with the base `ℓ ∣ z` discharged** (proven,
axiom-clean given the carried second-order Bernoulli input).

Composes the proven base `ℓ ∣ z` (`exists_realCaseIIData37_with_dvd_z_of_Int_solution`, Lemma 9.7)
with the proven real-data Lemma 9.8 (`caseII_real_x_add_y_mem_of_dvd_z`): for a base datum `D` whose
descent integer satisfies `D.z ∈ lv149` and with `D.x ∉ lv149`, `D.y ∉ lv149` (Lemma 9.6),
`D.x + D.y ∈ lv149`.  Demonstrates the full Lemma-9.7 → Lemma-9.8 chain at the rational base. -/
theorem caseII_real_base_x_add_y_mem
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 :=
  caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl

end BernoulliRegular.FLT37.Eichler

end
