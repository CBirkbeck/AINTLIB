import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.XiUnitTelescoping

/-!
# Reality of the §8.1 units `ξ_b` and `E₃₂ = (∏ ξ)²`, for `p = 37`

Washington's Lemma 8.1 unit `ξ_b = ζ^{(1-b)/2}(1-ζ^b)/(1-ζ)` is **totally real**
(`ξ_b = ±sin(πb/p)/sin(π/p)`, Washington p. 144), i.e. fixed by complex conjugation `σ`.  This is
the input that completes Washington Lemma 9.8 step 8: the σ-symmetrised Pollaczek unit
`E₃₂ = pollaczekUnitPlus 37 K 32 = E·σ(E)` collapses to a **perfect square** `(∏_b ξ_b^{b⁴})²` of
real cyclotomic units, because the root-of-unity twist in `E = pollaczekUnit` is inverted by `σ` and
cancels.  Consequently `ind₃₇ E₃₂ = 2·∑_b b⁴·ind₃₇ ξ_b`, which the telescoping
(`caseII_xiIndZMod_eq_zero`) makes `0`.

## What this file proves (axiom-clean Lean)

* `caseII_complexConj_zetaPow` — `σ(ζ^e) = ζ^{-e}` (element level): complex conjugation inverts the
  root of unity (`σ(ζ) = ζ^{p-1} = ζ^{-1}`).
* `caseII_complexConj_cyclotomicUnit` — `σ((1-ζ^b)/(1-ζ)) = ζ^{1-b}·(1-ζ^b)/(1-ζ)` (the σ-twist of
  the cyclotomic unit, by reindexing the geometric sum).
* `caseII_unitsComplexConj_xiUnit` — **`σ(ξ_b) = ξ_b`** (reality of `ξ_b`): the half-power prefactor
  `ζ^{(1-b)/2}` exactly cancels the cyclotomic-unit σ-twist `ζ^{1-b}` (`2·(1-b)/2 = 1-b`).
* `caseII_cyclotomicUnitUnit_mul_conj` — `cyclotomicUnitUnit b · σ(cyclotomicUnitUnit b) = ξ_b²`.
* `caseII_pollaczekUnitPlus_eq_xiProd_sq` — **`E₃₂ = (∏_b ξ_b^{b⁴})²`** as units (the σ-collapse).
* `caseII_E32_isPthPower_of_rhoReality` — `E₃₂` is a `37`-th power mod `lv149` from the residual.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.1 (Lemma 8.1, real units,
  p. 144), §9.1–9.2 (Lemma 9.8 step 8, p. 179).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField Finset

namespace BernoulliRegular.FLT37.Eichler

open FLT37 BernoulliRegular

/-! ## 1. `σ(ζ^e) = ζ^{-e}` -/

/-- **`σ(ζ) = ζ^{36} = ζ^{-1}` at the unit level.**  `unitsComplexConj` inverts the root of unity:
its value is `ringOfIntegersComplexConj ζ = ζ^{p-1}` (`complexConj_apply_zeta`), and
`ζ^{37} = 1`. -/
theorem caseII_unitsComplexConj_zetaU :
    unitsComplexConj (CyclotomicField 37 ℚ) (zetaU 37 (CyclotomicField 37 ℚ)) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (36 : ℕ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  -- `(σ ζ).val = σ (ζ.val) = ζ.val^{p-1}`; `(zetaU).val = ζ.toInteger`.
  have hval : ((zetaU 37 (CyclotomicField 37 ℚ) : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
      𝓞 (CyclotomicField 37 ℚ)) = (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger :=
    IsUnit.unit_spec _
  rw [unitsComplexConj_val_eq_ringOfIntegersComplexConj, hval,
    complexConj_apply_zeta (p := 37) (K := CyclotomicField 37 ℚ)]

/-- **`σ(ζ^e) = ζ^{-e}` at the unit level.**  `unitsComplexConj` is a `MulEquiv`, so
`σ(ζ^e) = (σ ζ)^e = (ζ^{36})^e = ζ^{36e} = ζ^{-e}` (since `36e ≡ -e mod 37`). -/
theorem caseII_unitsComplexConj_zetaU_zpow (e : ℤ) :
    unitsComplexConj (CyclotomicField 37 ℚ) (zetaU 37 (CyclotomicField 37 ℚ) ^ e) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (-e) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [map_zpow, caseII_unitsComplexConj_zetaU, ← zpow_natCast
    (a := zetaU 37 (CyclotomicField 37 ℚ)) (n := 36), ← zpow_mul]
  apply unit'_zpow_congr
  -- `36·e - (-e) = 37·e`.
  refine ⟨e, ?_⟩
  push_cast
  ring

/-- `σ(ζ^e) = ζ^{-e}` at the element level (`ringOfIntegersComplexConj`). -/
theorem caseII_complexConj_zetaPow (e : ℤ) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (zetaPow 37 (CyclotomicField 37 ℚ) e) =
      zetaPow 37 (CyclotomicField 37 ℚ) (-e) := by
  rw [zetaPow, zetaPow, ← unitsComplexConj_val_eq_ringOfIntegersComplexConj,
    caseII_unitsComplexConj_zetaU_zpow]

/-! ## 2. The σ-twist of the cyclotomic unit, and reality of `ξ_b` -/

/-- `cyclotomicUnit 37 K b = ∑_{j<b} ζ^j` written via `zetaPow`. -/
theorem caseII_cyclotomicUnit_eq_sum_zetaPow (b : ℕ) :
    cyclotomicUnit 37 (CyclotomicField 37 ℚ) b =
      ∑ j ∈ range b, zetaPow 37 (CyclotomicField 37 ℚ) (j : ℤ) := by
  rw [cyclotomicUnit]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [zetaPow_natCast, IsUnit.unit_spec]

/-- **`σ((1-ζ^b)/(1-ζ)) = ζ^{1-b}·(1-ζ^b)/(1-ζ)`** (the σ-twist of the cyclotomic unit).

Proof: `σ(∑_{j<b} ζ^j) = ∑_{j<b} ζ^{-j}`, and reindexing `j ↦ b-1-j` (`Finset.sum_range_reflect`)
turns `∑_{j<b} ζ^{1-b+j}` (`= ζ^{1-b}·∑_{j<b} ζ^j`) into `∑_{j<b} ζ^{-j}`. -/
theorem caseII_complexConj_cyclotomicUnit (b : ℕ) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
        (cyclotomicUnit 37 (CyclotomicField 37 ℚ) b) =
      zetaPow 37 (CyclotomicField 37 ℚ) (1 - (b : ℤ)) *
        cyclotomicUnit 37 (CyclotomicField 37 ℚ) b := by
  rw [caseII_cyclotomicUnit_eq_sum_zetaPow, map_sum]
  -- `σ(∑ ζ^j) = ∑ ζ^{-j}`.
  have hlhs : ∀ j ∈ range b, ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
      (zetaPow 37 (CyclotomicField 37 ℚ) (j : ℤ)) =
      zetaPow 37 (CyclotomicField 37 ℚ) (-(j : ℤ)) := fun j _ ↦ caseII_complexConj_zetaPow _
  rw [Finset.sum_congr rfl hlhs]
  -- RHS: `ζ^{1-b}·∑ ζ^j = ∑ ζ^{1-b+j}`.
  rw [Finset.mul_sum]
  have hrhs : ∀ j ∈ range b,
      zetaPow 37 (CyclotomicField 37 ℚ) (1 - (b : ℤ)) * zetaPow 37 (CyclotomicField 37 ℚ) (j : ℤ) =
      zetaPow 37 (CyclotomicField 37 ℚ) (1 - (b : ℤ) + (j : ℤ)) := fun j _ ↦
    (zetaPow_add 37 (CyclotomicField 37 ℚ) _ _).symm
  rw [Finset.sum_congr rfl hrhs]
  -- Reindex `j ↦ b-1-j`: `∑_{j<b} ζ^{1-b+(b-1-j)} = ∑_{j<b} ζ^{-j}`.
  rw [← Finset.sum_range_reflect
    (fun j ↦ zetaPow 37 (CyclotomicField 37 ℚ) (1 - (b : ℤ) + (j : ℤ))) b]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  congr 1
  -- `1 - b + (b - 1 - j) = -j` (as integers, with `j < b`).
  have : ((b - 1 - j : ℕ) : ℤ) = (b : ℤ) - 1 - (j : ℤ) := by
    have h1 : 1 ≤ b := by omega
    push_cast [Nat.sub_sub]
    omega
  rw [this]
  ring

/-- **`σ(ξ_b) = ξ_b` — reality of Washington's Lemma 8.1 unit** (proven, axiom-clean).

The half-power prefactor `ζ^{(1-b)/2}` exactly cancels the cyclotomic-unit σ-twist `ζ^{1-b}`:
`σ(ξ_b) = σ(ζ^{halfExp b})·σ((1-ζ^b)/(1-ζ)) = ζ^{-halfExp b}·ζ^{1-b}·(1-ζ^b)/(1-ζ)`, and
`-halfExp b + (1-b) ≡ halfExp b (mod 37)` because `2·halfExp b = (1-b)·2·2⁻¹ ≡ 1-b`.  Hence `ξ_b` is
totally real (Washington p. 144). -/
theorem caseII_unitsComplexConj_xiUnit (b : ℕ) (hb : b.Coprime 37) :
    unitsComplexConj (CyclotomicField 37 ℚ) (xiUnit 37 (CyclotomicField 37 ℚ) b hb) =
      xiUnit 37 (CyclotomicField 37 ℚ) b hb := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply Units.ext
  rw [unitsComplexConj_val_eq_ringOfIntegersComplexConj, xiUnit_val']
  rw [map_mul, caseII_complexConj_zetaPow, caseII_complexConj_cyclotomicUnit]
  -- `ζ^{-Hb}·(ζ^{1-b}·cyc b) = ζ^{Hb}·cyc b`, using `ζ^{-Hb}·ζ^{1-b} = ζ^{Hb}`.
  rw [← mul_assoc, ← zetaPow_add]
  -- `-halfExp b + (1 - b) ≡ halfExp b (mod 37)`, so the `ζ`-powers agree.
  have hexp : zetaPow 37 (CyclotomicField 37 ℚ) (-halfExp (p := 37) (b : ℤ) + (1 - (b : ℤ))) =
      zetaPow 37 (CyclotomicField 37 ℚ) (halfExp (p := 37) (b : ℤ)) := by
    apply zetaPow_congr
    have h2 := two_mul_inv2_int (p := 37) (by decide)
    unfold halfExp
    -- `-(1-b)c + (1-b) - (1-b)c = (1-b)(1 - 2c) = (1-b)·(-37)`.
    refine ⟨-(1 - (b : ℤ)), ?_⟩
    linear_combination -(1 - (b : ℤ)) * h2
  rw [hexp]

/-! ## 3. The σ-collapse: `E₃₂ = (∏ ξ)²` -/

/-- `cyclotomicUnitUnit 37 K b = ζ^{-halfExp b}·ξ_b` (units): rearranging the definition
`ξ_b = ζ^{halfExp b}·cyclotomicUnitUnit b`. -/
theorem caseII_cyclotomicUnitUnit_eq (b : ℕ) (hb : b.Coprime 37) :
    cyclotomicUnitUnit 37 (CyclotomicField 37 ℚ) b hb (by decide) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (-halfExp (p := 37) (b : ℤ)) *
        xiUnit 37 (CyclotomicField 37 ℚ) b hb := by
  rw [xiUnit, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

/-- **Per-factor σ-symmetric collapse:**
`cyclotomicUnitUnit b · σ(cyclotomicUnitUnit b) = ξ_b²`.

The two `ζ`-power twists `ζ^{-halfExp b}` and `ζ^{+halfExp b}` (from `σ(ζ^{-halfExp b})`) cancel,
and
`σ(ξ_b) = ξ_b` (reality), leaving `ξ_b·ξ_b = ξ_b²`. -/
theorem caseII_cyclotomicUnitUnit_mul_conj (b : ℕ) (hb : b.Coprime 37) :
    cyclotomicUnitUnit 37 (CyclotomicField 37 ℚ) b hb (by decide) *
        unitsComplexConj (CyclotomicField 37 ℚ)
          (cyclotomicUnitUnit 37 (CyclotomicField 37 ℚ) b hb (by decide)) =
      xiUnit 37 (CyclotomicField 37 ℚ) b hb ^ 2 := by
  rw [caseII_cyclotomicUnitUnit_eq b hb, map_mul, caseII_unitsComplexConj_zetaU_zpow,
    caseII_unitsComplexConj_xiUnit b hb, neg_neg]
  -- `(ζ^{-H}·ξ)·(ζ^{H}·ξ) = ξ²`.
  rw [mul_mul_mul_comm, ← zpow_add, neg_add_cancel, zpow_zero, one_mul, sq]

/-- Coprimality of the index `b ∈ Ico 1 19` to `37` (each is in `[1, 18]`). -/
theorem caseII_pollaczek_index_coprime {b : ℕ} (hb : b ∈ Ico 1 ((37 - 1) / 2 + 1)) :
    b.Coprime 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [Finset.mem_Ico] at hb
  exact (Nat.coprime_of_lt_prime (by omega) (by omega) (by decide)).symm

/-- **The σ-collapse: `E₃₂ = (∏_b ξ_b^{b⁴})²`** (proven, axiom-clean).

`pollaczekUnitPlus 37 K 32 = pollaczekUnit · σ(pollaczekUnit)`, and termwise
`cyclotomicUnitUnit b · σ(cyclotomicUnitUnit b) = ξ_b²` (`caseII_cyclotomicUnitUnit_mul_conj`), so
the
product collapses to `∏_b (ξ_b²)^{b⁴} = (∏_b ξ_b^{b⁴})²`.  This is Washington Lemma 9.8 step 8: the
σ-symmetrised Pollaczek unit is a perfect square of real cyclotomic units. -/
theorem caseII_pollaczekUnitPlus_eq_xiProd_sq :
    pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 =
      (∏ b ∈ (Ico 1 ((37 - 1) / 2 + 1)).attach,
        xiUnit 37 (CyclotomicField 37 ℚ) b.1 (caseII_pollaczek_index_coprime b.2) ^
          (b.1 ^ 4)) ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `E₃₂ = E · σ(E)` (unit level).
  have hdef : pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 =
      pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 *
        unitsComplexConj (CyclotomicField 37 ℚ) (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32) := rfl
  rw [hdef, pollaczekUnit]
  -- `σ(∏ …) = ∏ σ(…)`, then combine the two products termwise.
  rw [map_prod, ← Finset.prod_mul_distrib]
  -- Termwise: `(cyc^{e})·(σ cyc)^{e} = (cyc·σcyc)^e = (ξ²)^e`; and `(∏ ξ^e)² = ∏ (ξ²)^e`.
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  -- `pollaczekFactor b.2 ^ e * σ(pollaczekFactor b.2 ^ e) = (ξ_{b.1} ^ e)^2`.
  rw [map_pow, ← mul_pow]
  -- `pollaczekFactor = cyclotomicUnitUnit`.
  have hpf : pollaczekFactor 37 (CyclotomicField 37 ℚ) b.2 =
      cyclotomicUnitUnit 37 (CyclotomicField 37 ℚ) b.1
        (caseII_pollaczek_index_coprime b.2) (by decide) := by
    rw [pollaczekFactor]
  rw [hpf, caseII_cyclotomicUnitUnit_mul_conj b.1 (caseII_pollaczek_index_coprime b.2), ← pow_mul,
    ← pow_mul, mul_comm 2 (b.1 ^ 4)]

/-! ## 4. `ind₃₇ E₃₂ = 0` from the telescoping, and `E₃₂` is a `37`-th power mod `lv149` -/

/-- `residueInd37 1 = 0`. -/
theorem caseII_residueInd37_one : residueInd37 (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) = 0 := by
  have := residueInd37_mul (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) 1
  rw [mul_one] at this
  linear_combination -this

/-- `residueInd37 (∏ x_i) = ∑ residueInd37 x_i` over a `Finset` (additivity of `ind₃₇`). -/
theorem caseII_residueInd37_prod {ι : Type*} (s : Finset ι)
    (f : ι → (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    residueInd37 (∏ i ∈ s, f i) = ∑ i ∈ s, residueInd37 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, caseII_residueInd37_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, residueInd37_mul, ih]

/-- `xiUnit` depends on its index only (the coprimality argument is proof-irrelevant):
`m = n → xiUnit p K m h₁ = xiUnit p K n h₂`. -/
theorem caseII_xiUnit_congr (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] {m n : ℕ} (hmn : m = n) (h₁ : m.Coprime 37)
    (h₂ : n.Coprime 37) :
    xiUnit 37 K m h₁ = xiUnit 37 K n h₂ := by
  subst hmn
  rfl

/-- **Bridge:** for `b` coprime to `37` with `b < 37`, `residueInd37 ξ_b = xiIndZMod (b : ZMod 37)`.
(`(b : ZMod 37).val = b`, and `xiUnit` depends on the index only up to the proof-irrelevant
coprimality argument.) -/
theorem caseII_residueInd37_xiUnit_eq_xiIndZMod {b : ℕ} (hb : b.Coprime 37) (hb_lt : b < 37)
    (hb_pos : 0 < b) :
    residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) b hb) = xiIndZMod ((b : ℕ) : ZMod 37) := by
  have hb_ne : ((b : ℕ) : ZMod 37) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    omega
  rw [xiIndZMod_of_ne hb_ne]
  -- `(↑b).val = b`, so the two `xiUnit` indices coincide.
  have hval : (((b : ℕ) : ZMod 37)).val = b := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt]
  rw [caseII_xiUnit_congr (CyclotomicField 37 ℚ) hval (caseII_val_coprime hb_ne) hb]

/-- **`E₃₂` is a `37`-th power mod `lv149`, from the telescoping** (proven, axiom-clean).

Given that every `ξ_b` (`b ≢ 0`) is a `37`-th power mod `lv149` (`∀ c ≠ 0, xiIndZMod c = 0`, the
telescoping conclusion `caseII_xiIndZMod_eq_zero`), the σ-collapse `E₃₂ = (∏ ξ_b^{b⁴})²`
(`caseII_pollaczekUnitPlus_eq_xiProd_sq`) gives `ind₃₇ E₃₂ = 2·∑_b b⁴·ind₃₇ ξ_b = 0`, i.e. `E₃₂`
is a
`37`-th power mod `lv149`.  This is the conclusion of Washington Lemma 9.8 step 8. -/
theorem caseII_E32_isPthPower_of_xiIndZero
    (hξ : ∀ c : ZMod 37, c ≠ 0 → xiIndZMod c = 0) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [isPthPowerModPrime_iff_residueInd37_eq_zero]
  -- `ind₃₇ E₃₂ = 2·∑ b⁴·ind₃₇ ξ_b = 0`.
  rw [caseII_pollaczekUnitPlus_eq_xiProd_sq, residueInd37_pow, caseII_residueInd37_prod]
  -- Each summand `ind₃₇(ξ_{b.1}^{b.1⁴}) = b.1⁴·ind₃₇ ξ_{b.1} = b.1⁴·xiIndZMod (b.1) = 0`.
  have hterm : ∀ b ∈ (Ico 1 ((37 - 1) / 2 + 1)).attach,
      residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) b.1 (caseII_pollaczek_index_coprime b.2) ^
        (b.1 ^ 4)) = 0 := by
    intro b _
    rw [residueInd37_pow]
    -- `ind₃₇ ξ_{b.1} = xiIndZMod (b.1 : ZMod 37) = 0` (telescoping); `b.1 ∈ [1,18]`.
    have hmem := b.2
    rw [Finset.mem_Ico] at hmem
    have hb_ne : ((b.1 : ℕ) : ZMod 37) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      omega
    rw [caseII_residueInd37_xiUnit_eq_xiIndZMod (caseII_pollaczek_index_coprime b.2)
        (by omega) (by omega), hξ _ hb_ne, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, mul_zero]

/-- **`E₃₂` is a `37`-th power mod `lv149` from the `ρ_a`-reality residual** (proven, axiom-clean).

Combining the telescoping (`caseII_xiIndZMod_eq_zero`: `MirimanoffRhoReality37 j` with `j ≠ 0`
makes every `ξ_b` a `37`-th power mod `lv149`) with the σ-collapse step 8
(`caseII_E32_isPthPower_of_xiIndZero`), the irregular Pollaczek unit `E₃₂` is a `37`-th power mod
`lv149`.  This is the full content of Washington Lemma 9.8 steps 5–8 *given* its step-5
`ρ_a`-reality
input. -/
theorem caseII_E32_isPthPower_of_rhoReality {j : ZMod 37}
    (hρ : MirimanoffRhoReality37 j) (hj : j ≠ 0) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) :=
  caseII_E32_isPthPower_of_xiIndZero (fun _ hc ↦ caseII_xiIndZMod_eq_zero hρ hj hc)

end BernoulliRegular.FLT37.Eichler

end
