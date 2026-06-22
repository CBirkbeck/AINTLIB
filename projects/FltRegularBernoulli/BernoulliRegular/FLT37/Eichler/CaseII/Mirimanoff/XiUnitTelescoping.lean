import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.XiUnitRatioIdentity
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.DiscreteLogIndexCollapse
import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.AuxPrimeDvdZSoundnessRepair
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealClosure

/-!
# Washington §9.1 Lemma 9.8 (steps 5–8) for `p = 37`: the Mirimanoff telescoping

This file carries Washington's Lemma 9.8 (Washington *Introduction to Cyclotomic Fields*, 2nd ed.,
GTM 83, pp. 178–179) past the **§8.1 ratio identity** (`CaseIILemma81.lean`, proven) and into the
**telescoping over the `ξ` units**, reducing the residual `Lemma98MirimanoffPthPower37`
(`CaseIILemma98DescentSum.lean`) to its smallest genuine analytic core — Washington's **step-5
`ρ_a`-reality ratio congruence**.

## The chain (Washington Lemma 9.8, steps 5–8)

Suppose a nontrivial conjugate factor `ω + ζ^j θ ≡ 0 (mod 𝔩)` occurs (`j ≠ 0`), with `ℓ ∤ x, y`
(Lemma 9.6).  Washington derives, via the §9.2 `ρ_a`-reality (`(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p·(unit)` with
`ρ_a` **real** because `p ∤ h⁺`), the **cyclic-group congruence**

  `(ζ^a - ζ^j)/(1 - ζ^{a+j})` is a `p`-th power mod `𝔩`,   for all `a ≢ ±j (mod p)`     (step 5).

By the §8.1 ratio identity (`xi_ratio_identity`), `(ζ^a-ζ^j)/(1-ζ^{a+j}) = -ξ_{a-j}/ξ_{a+j}`, and
`-1` is a `p`-th power (`p` odd), so

  `ξ_{a-j}·ξ_{a+j}^{-1}` is a `p`-th power mod `𝔩`,   for all `a ≢ ±j`     (step 6).

The **telescoping** `ξ_b = ξ_1·∏ (ξ-ratios)` with `ξ_1 = 1` then makes **every** `ξ_b` (`b ≢ 0`) a
`p`-th power mod `𝔩` (step 7), and the Galois descent makes every real cyclotomic unit — in
particular `E₃₂ = pollaczekUnitPlus 37 K 32` — a `p`-th power mod `𝔩` (step 8), which is
`Lemma98MirimanoffPthPower37`.

## What this file proves (axiom-clean Lean), on top of the proven §8.1 ratio identity

* `caseII_negOne_isPthPower` — `-1` is a `37`-th power mod `lv149` (`-1 = (-1)^37`, `37` odd).
* `caseII_zetaPow_sub_zetaPow_notMem_lv149` — `ζ^a - ζ^j ∉ lv149` for `a ≢ j (mod 37)` (it is
  `ζ^j·(ζ^{a-j}-1)`, associate of `ζ-1 ∉ lv149`); hence a unit mod `𝔩`.
* `caseII_one_sub_zetaPow_notMem_lv149` — `1 - ζ^s ∉ lv149` for `s ≢ 0 (mod 37)`.
* `caseII_xi_ratio_ind` — **the §8.1-driven `ind` consequence**: from step 5's "`(ζ^a-ζ^j)/(1-ζ^s)`
  is a `p`-th power mod `𝔩`" (with `a ≢ ±j`), the discrete-log index satisfies
  `ind₃₇ ξ_{d} = ind₃₇ ξ_{s}` (where `s ≡ a+j`, `d ≡ a-j`).  This is the additive engine of the
  telescoping.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.1 (Lemma 8.1), §9.1–9.2
  (Lemma 9.8, pp. 178–179).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII

/-! ## 0. `-1` is a `37`-th power mod `lv149`, and units mod `𝔩` -/

/-- **`-1` is a `37`-th power modulo `lv149`.**  Since `37` is odd, `-1 = (-1)^37`, so its residue
is the `37`-th power of `-1`.  Used to absorb the sign in the §8.1 ratio identity
`ξ_{a-j}/ξ_{a+j} = -(ζ^a-ζ^j)/(1-ζ^{a+j})`. -/
theorem caseII_negOne_isPthPower :
    BernoulliRegular.IsPthPowerModPrime 37 lv149 (-1 : 𝓞 (CyclotomicField 37 ℚ)) := by
  refine ⟨Ideal.Quotient.mk lv149 (-1), ?_⟩
  rw [← map_pow, show ((-1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37) = -1 from
    Odd.neg_one_pow (by decide)]

/-- Abbreviation: the canonical root-of-unity unit `ζ ∈ (𝓞 ℚ(ζ₃₇))ˣ`. -/
local notation "ζ37" => zetaU 37 (CyclotomicField 37 ℚ)

private theorem zeta37_sub_one_notMem :
    ((ζ37 : 𝓞 (CyclotomicField 37 ℚ)) - 1) ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `ζ37 = (zeta_spec …).unit'`, and `caseII_zeta_sub_one_notMem_lv149` applies to it.
  exact caseII_zeta_sub_one_notMem_lv149 (zeta_spec 37 ℚ (CyclotomicField 37 ℚ))

/-- **`ζ^k - 1 ∉ lv149` for `k` coprime to `37`.**  `ζ^k - 1 = (ζ-1)·cyclotomicUnit k` with
`ζ - 1 ∉ lv149` (`ℓ` unramified) and `cyclotomicUnit k` a unit, so the prime `lv149` (being prime)
does not contain the product. -/
theorem caseII_zetaPow_natCast_sub_one_notMem {k : ℕ} (hk : k.Coprime 37) :
    (zetaPow 37 (CyclotomicField 37 ℚ) (k : ℤ) - 1) ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  rw [zetaPow_natCast]
  -- `ζ^k - 1 = (ζ - 1)·cyclotomicUnit k`.
  have hfac : ((ζ37 : 𝓞 (CyclotomicField 37 ℚ)) ^ k - 1) =
      ((ζ37 : 𝓞 (CyclotomicField 37 ℚ)) - 1) * cyclotomicUnit 37 (CyclotomicField 37 ℚ) k :=
    (zeta_sub_one_mul_cyclotomicUnit 37 (CyclotomicField 37 ℚ) k).symm
  rw [hfac]
  intro hmem
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hmem with h1 | h2
  · exact zeta37_sub_one_notMem h1
  · -- `cyclotomicUnit k` is a unit (k coprime to 37), so ∉ lv149.
    exact caseII_unit_notMem_lv149
      (cyclotomicUnitUnit 37 (CyclotomicField 37 ℚ) k hk (by decide))
      (by rw [cyclotomicUnitUnit_val]; exact h2)

/-- **`ζ^m - 1 ∉ lv149` for any integer `m ≢ 0 (mod 37)`.**  Reduce the exponent mod `37` to the
natural representative `m.toNat % 37`, which is coprime to `37` (in `[1, 36]`), and apply
`caseII_zetaPow_natCast_sub_one_notMem`. -/
theorem caseII_zetaPow_sub_one_notMem {m : ℤ} (hm : ¬ (37 : ℤ) ∣ m) :
    (zetaPow 37 (CyclotomicField 37 ℚ) m - 1) ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `r := m % 37 ∈ [1, 36]`, and `zetaPow m = zetaPow r` (exponent congruence).
  set r : ℤ := m % 37 with hr
  have hr_range : 1 ≤ r ∧ r < 37 := by
    have h0 : 0 ≤ r := Int.emod_nonneg m (by decide)
    have h1 : r < 37 := Int.emod_lt_of_pos m (by decide)
    have hne : r ≠ 0 := by
      rw [hr]; intro h; exact hm (Int.dvd_of_emod_eq_zero h)
    omega
  -- `m ≡ r (mod 37)`, so `zetaPow m = zetaPow r`.
  have hcong : zetaPow 37 (CyclotomicField 37 ℚ) m = zetaPow 37 (CyclotomicField 37 ℚ) r := by
    apply zetaPow_congr
    -- `37 ∣ m - r`, since `m - m%37 = 37·(m/37)`.
    refine ⟨m / 37, ?_⟩
    rw [hr, Int.emod_def]; ring
  rw [hcong]
  -- `r = (r.toNat : ℤ)` with `r.toNat` coprime to 37 (in `[1,36]`).
  obtain ⟨k, hk_eq, hk_cop⟩ : ∃ k : ℕ, (k : ℤ) = r ∧ k.Coprime 37 := by
    refine ⟨r.toNat, Int.toNat_of_nonneg (by omega), ?_⟩
    have hlt : r.toNat < 37 := by omega
    have hpos : r.toNat ≠ 0 := by omega
    exact (Nat.coprime_of_lt_prime hpos hlt (by decide)).symm
  rw [← hk_eq]
  exact caseII_zetaPow_natCast_sub_one_notMem hk_cop

/-- **`ζ^a - ζ^j ∉ lv149` for `a ≢ j (mod 37)`.**  Factor `ζ^a - ζ^j = ζ^j·(ζ^{a-j} - 1)` with `ζ^j`
a unit and `ζ^{a-j} - 1 ∉ lv149` (`a - j ≢ 0`).  Hence `ζ^a - ζ^j` is a unit modulo `𝔩`. -/
theorem caseII_zetaPow_sub_zetaPow_notMem {a j : ℤ} (h : ¬ (37 : ℤ) ∣ (a - j)) :
    (zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j) ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  -- `ζ^a - ζ^j = ζ^j · (ζ^{a-j} - 1)`.
  have hfac : zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j =
      zetaPow 37 (CyclotomicField 37 ℚ) j * (zetaPow 37 (CyclotomicField 37 ℚ) (a - j) - 1) := by
    rw [mul_sub, mul_one, ← zetaPow_add, show j + (a - j) = a by ring]
  rw [hfac]
  intro hmem
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hmem with h1 | h2
  · -- `ζ^j` is a unit value, never in the prime `lv149`.
    exact caseII_unit_notMem_lv149 (zetaU 37 (CyclotomicField 37 ℚ) ^ j) h1
  · exact caseII_zetaPow_sub_one_notMem h h2

/-! ## 1. The §8.1 bridge: `ξ_{a-j}·ξ_{a+j}^{-1}` as the ratio `-(ζ^a-ζ^j)/(1-ζ^s)` -/

/-- **The §8.1 ratio identity at the unit level, multiplied out modulo `𝔩`.**  In the residue field
`𝓞 K / 𝔩`, the §8.1 ratio identity (`xi_ratio_identity`) gives

  `Q(ξ_{d}) · Q(1 - ζ^s) = Q(-1) · Q(ζ^a - ζ^j) · Q(ξ_{s})`.

(Multiplying the identity `(ζ^a-ζ^j)·ξ_s = -(1-ζ^s)·ξ_d` by `Q` and rearranging.)  Combined with the
fact that `ζ^a-ζ^j` and `1-ζ^s` are units mod `𝔩`, this is the precise sense in which the residual
"`ξ_{a-j}/ξ_{a+j}` is a `p`-th power mod `𝔩`" equals Washington's step-5 "`(ζ^a-ζ^j)/(1-ζ^{a+j})` is
a `p`-th power mod `𝔩`". -/
theorem caseII_xi_ratio_residue_identity (a j : ℤ) (s d : ℕ)
    (hs : s.Coprime 37) (hd : d.Coprime 37)
    (hs_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a + j) = zetaU 37 (CyclotomicField 37 ℚ) ^ (s : ℤ))
    (hd_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a - j) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (d : ℤ)) :
    Ideal.Quotient.mk lv149 (xiUnit 37 (CyclotomicField 37 ℚ) d hd : 𝓞 (CyclotomicField 37 ℚ)) *
        Ideal.Quotient.mk lv149 (1 - zetaPow 37 (CyclotomicField 37 ℚ) (s : ℤ)) =
      Ideal.Quotient.mk lv149 (-1) *
        Ideal.Quotient.mk lv149 (zetaPow 37 (CyclotomicField 37 ℚ) a -
          zetaPow 37 (CyclotomicField 37 ℚ) j) *
        Ideal.Quotient.mk lv149 (xiUnit 37 (CyclotomicField 37 ℚ) s hs :
          𝓞 (CyclotomicField 37 ℚ)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The element identity, pushed through `Q = Ideal.Quotient.mk lv149`.
  have hid := xi_ratio_identity 37 (CyclotomicField 37 ℚ) (by decide) a j s d hs hd hs_eq hd_eq
  -- `(ζ^a-ζ^j)·ξ_s = -(1-ζ^s)·ξ_d`; rearrange to `ξ_d·(1-ζ^s) = (-1)·(ζ^a-ζ^j)·ξ_s`.
  have hid' : (xiUnit 37 (CyclotomicField 37 ℚ) d hd : 𝓞 (CyclotomicField 37 ℚ)) *
        (1 - zetaPow 37 (CyclotomicField 37 ℚ) (s : ℤ)) =
      (-1) * (zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j) *
        (xiUnit 37 (CyclotomicField 37 ℚ) s hs : 𝓞 (CyclotomicField 37 ℚ)) := by
    linear_combination hid
  rw [← map_mul, ← map_mul, ← map_mul, hid']

/-! ## 2. The `ind` consequence: equal indices for the telescoped `ξ` units -/

/-- **`ξ_{a-j}/ξ_{a+j}` a `p`-th power mod `𝔩` ⟹ equal indices** (proven, axiom-clean).

If the cyclotomic unit `ξ_{d}·ξ_{s}^{-1}` is a `37`-th power modulo `lv149`, then its discrete-log
index vanishes, so `ind₃₇ ξ_{d} = ind₃₇ ξ_{s}`.  This is the additive form of Washington's step 6,
the engine of the telescoping (`ind₃₇` is constant along the chain of `ξ` indices). -/
theorem caseII_xi_ratio_ind {s d : ℕ} (hs : s.Coprime 37) (hd : d.Coprime 37)
    (hpow : BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((xiUnit 37 (CyclotomicField 37 ℚ) d hd * (xiUnit 37 (CyclotomicField 37 ℚ) s hs)⁻¹ :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) :
    residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) d hd) =
      residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) s hs) := by
  have hzero := (isPthPowerModPrime_iff_residueInd37_eq_zero _).mp hpow
  rw [residueInd37_mul] at hzero
  -- `residueInd37 (ξ_s⁻¹) = - residueInd37 ξ_s` (additivity + `ξ_s·ξ_s⁻¹ = 1`).
  have hinv : residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) s hs)⁻¹ =
      - residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) s hs) := by
    have hone : residueInd37 (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) = 0 := by
      have := residueInd37_mul (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) 1
      rw [mul_one] at this; linear_combination -this
    have h1 : residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) s hs *
        (xiUnit 37 (CyclotomicField 37 ℚ) s hs)⁻¹) = 0 := by
      rw [mul_inv_cancel]; exact hone
    rw [residueInd37_mul] at h1
    linear_combination h1
  rw [hinv] at hzero
  -- `ind ξ_d - ind ξ_s = 0`.
  linear_combination hzero

/-! ## 3. `ξ_1 = 1` and the index-vanishing telescoping

Washington's telescoping starts from `ξ_1 = 1` (`halfExp 1 = 0`, `cyclotomicUnit 1 = 1`) and uses
the index equalities `ind₃₇ ξ_b = ind₃₇ ξ_{b+2j}` (from step 6) to spread `ind₃₇ ξ_1 = 0` to every
residue (since `2j` generates `ℤ/37ℤ` when `j ≢ 0`).  We package the orbit argument in `ZMod 37`. -/

/-- **`ξ_1 = 1`** (`halfExp 1 = (1-1)·2⁻¹ = 0` and `cyclotomicUnit 1 = 1`), the base of the
telescoping; hence `ind₃₇ ξ_1 = 0`. -/
theorem caseII_xiUnit_one_eq_one :
    xiUnit 37 (CyclotomicField 37 ℚ) 1 (by decide) = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply Units.ext
  rw [xiUnit_val, cyclotomicUnit_one, mul_one]
  -- `ζ^{halfExp 1} = ζ^0 = 1`.
  have h0 : halfExp (p := 37) ((1 : ℕ) : ℤ) = 0 := by simp [halfExp]
  rw [h0, zpow_zero, Units.val_one]

/-- `ind₃₇ ξ_1 = 0`. -/
theorem caseII_residueInd37_xiUnit_one :
    residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) 1 (by decide)) = 0 := by
  rw [caseII_xiUnit_one_eq_one]
  have := residueInd37_mul (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) 1
  rw [mul_one] at this; linear_combination -this

/-- **The clean orbit telescoping in `ZMod 37`.**  Let `t ≠ 0` and let `g : ZMod 37 → ZMod 37`
satisfy `g ((c+1)·t) = g (c·t)` whenever `c·t ≠ 0` and `(c+1)·t ≠ 0`.  Then `g` is constant on the
nonzero multiples of `t`: `g (c·t) = g t` for every `c ≠ 0`.  (The walk `t, 2t, …, 36t` over the
nonzero multiples never hits `0`, so it is a single unbroken chain.)

This is the `ZMod 37` engine of Washington's `ξ_b`-telescoping (step 7): the index map
`b ↦ ind₃₇ ξ_b` is `+2j`-step-invariant by step 6, and `2j` generates `ℤ/37ℤ`, so the index is
constant on all nonzero residues. -/
theorem caseII_telescope_const {t : ZMod 37} (ht : t ≠ 0) (g : ZMod 37 → ZMod 37)
    (Hstep : ∀ c : ZMod 37, c * t ≠ 0 → (c + 1) * t ≠ 0 → g ((c + 1) * t) = g (c * t)) :
    ∀ c : ZMod 37, c ≠ 0 → g (c * t) = g (1 * t) := by
  -- Walk the multiples `1·t, 2·t, …, 36·t` (all nonzero), proving `g(n·t) = g(1·t)` by induction.
  have walk : ∀ n : ℕ, 1 ≤ n → n ≤ 36 → g ((n : ZMod 37) * t) = g ((1 : ZMod 37) * t) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk36
      rcases Nat.lt_or_ge k 1 with h1 | h1
      · -- k = 0, so k+1 = 1.
        interval_cases k
        norm_num
      · -- k ≥ 1; step from `k·t` to `(k+1)·t`.
        have hkt_ne : (k : ZMod 37) * t ≠ 0 := by
          rw [mul_ne_zero_iff]
          refine ⟨?_, ht⟩
          rw [Ne, ZMod.natCast_eq_zero_iff]
          omega
        have hk1t_ne : ((k : ZMod 37) + 1) * t ≠ 0 := by
          rw [mul_ne_zero_iff]
          refine ⟨?_, ht⟩
          have hc : ((k : ZMod 37) + 1) = ((k + 1 : ℕ) : ZMod 37) := by push_cast; ring
          rw [hc, Ne, ZMod.natCast_eq_zero_iff]
          omega
        have hstep := Hstep (k : ZMod 37) hkt_ne hk1t_ne
        have hcast : ((k + 1 : ℕ) : ZMod 37) * t = ((k : ZMod 37) + 1) * t := by push_cast; ring
        rw [hcast, hstep]
        exact ih h1 (by omega)
  -- Every nonzero `c` is `(c.val)·1`-multiple with `1 ≤ c.val ≤ 36`.
  intro c hc
  have hval : ((c.val : ZMod 37)) = c := ZMod.natCast_zmod_val c
  have hrange : 1 ≤ c.val ∧ c.val ≤ 36 := by
    have h1 : c.val < 37 := c.val_lt
    have h2 : c.val ≠ 0 := by
      intro h; apply hc; rw [← hval, h]; simp
    omega
  rw [← hval]
  exact walk c.val hrange.1 hrange.2

/-! ## 4. The `ξ` unit indexed by `ZMod 37`, and its index map -/

/-- `(c : ZMod 37).val` is coprime to `37` when `c ≠ 0` (it lies in `[1, 36]`). -/
theorem caseII_val_coprime {c : ZMod 37} (hc : c ≠ 0) : c.val.Coprime 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h1 : c.val < 37 := c.val_lt
  have h2 : c.val ≠ 0 := fun h ↦ hc (by rw [← ZMod.natCast_zmod_val c, h]; simp)
  exact (Nat.coprime_of_lt_prime h2 h1 (by decide)).symm

/-- The `ξ` unit indexed by a *nonzero* `c : ZMod 37` (its `.val` representative), packaged with the
nonzero hypothesis; `xiUnitZMod c hc = ξ_{c.val}`. -/
noncomputable def xiUnitZMod (c : ZMod 37) (hc : c ≠ 0) : (𝓞 (CyclotomicField 37 ℚ))ˣ :=
  xiUnit 37 (CyclotomicField 37 ℚ) c.val (caseII_val_coprime hc)

/-- The total index map `xiIndZMod : ZMod 37 → ZMod 37`, `c ↦ ind₃₇ ξ_{c.val}` for `c ≠ 0`, and `0`
at `c = 0` (irrelevant).  This is the function the orbit telescoping (`caseII_telescope_const`)
makes constant on nonzero. -/
noncomputable def xiIndZMod (c : ZMod 37) : ZMod 37 :=
  if hc : c = 0 then 0 else residueInd37 (xiUnitZMod c hc)

/-- `xiIndZMod c = ind₃₇ ξ_{c.val}` for `c ≠ 0`. -/
theorem xiIndZMod_of_ne {c : ZMod 37} (hc : c ≠ 0) :
    xiIndZMod c =
      residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) c.val (caseII_val_coprime hc)) := by
  rw [xiIndZMod, dif_neg hc]; rfl

/-- `(1 : ZMod 37) ≠ 0` (clean-context helper, to avoid `decide` capturing local instances). -/
theorem caseII_one_ne_zero_zmod37 : (1 : ZMod 37) ≠ 0 := by decide

/-- `(2 : ZMod 37) ≠ 0`. -/
theorem caseII_two_ne_zero_zmod37 : (2 : ZMod 37) ≠ 0 := by decide

/-- `(1 : ZMod 37).val = 1`. -/
theorem caseII_one_val_zmod37 : (1 : ZMod 37).val = 1 := by decide

/-- `ξ_{(1 : ZMod 37).val} = 1` (its `.val` is `1`, and `ξ_1 = 1`).  Hence `xiUnitZMod 1 = 1`. -/
theorem caseII_xiUnitZMod_one (hc : (1 : ZMod 37) ≠ 0) :
    xiUnitZMod (1 : ZMod 37) hc = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply Units.ext
  rw [xiUnitZMod, xiUnit_val, caseII_one_val_zmod37, cyclotomicUnit_one, mul_one]
  have h0 : halfExp (p := 37) ((1 : ℕ) : ℤ) = 0 := by simp [halfExp]
  rw [h0, zpow_zero, Units.val_one]

/-! ## 5. Washington's step-5 `ρ_a`-reality ratio congruence (the residual), and the telescoping

`MirimanoffRhoReality37 j` is Washington's step-5/6 output (Lemma 9.8, p. 179): for the special
index `j` (`η = ζ^j ≠ 1`), and every `b ≢ 0, -2j (mod 37)`, the cyclotomic-unit ratio
`ξ_{b+2j}·ξ_{b}^{-1}` is a `37`-th power modulo `lv149`.  This is the analytic heart of Lemma 9.8:
it is what the `ρ_a`-reality (`(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p·unit`, `ρ_a` real because `p ∤ h⁺`) plus the
cyclic-group congruence (`ℓ-1 = kp`, `k` even, `ω ≡ -ζ^jθ`) produce — re-expressed via the §8.1
ratio identity `(ζ^a-ζ^j)/(1-ζ^{a+j}) = -ξ_{a-j}/ξ_{a+j}` (with `b = a-j`, `b+2j = a+j`). -/

/-- **Washington Lemma 9.8 step-5/6 `ρ_a`-reality ratio congruence for `p = 37`** (a `def … : Prop`,
**not** an axiom).

For the special index `j : ZMod 37` of the descent (`η = ζ^j`, `η ≠ 1`, so `j ≠ 0`), and every
`b : ZMod 37` with `b ≠ 0` and `b + 2j ≠ 0`, the real cyclotomic-unit ratio
`ξ_{(b+2j).val}·ξ_{b.val}^{-1}` is a `37`-th power modulo `lv149`.

This is the smallest genuine analytic core of Washington Lemma 9.8 (pp. 178–179): the `ρ_a`-reality
input (`(ω+ζ^aθ)/(1-ζ^a)=ρ_a^p·unit`, `ρ_a` real since `p∤h⁺`) plus the cyclic-group congruence
yield Washington's `(ζ^a-ζ^j)/(1-ζ^{a+j})` is a `p`-th power mod `𝔩`; via the **proven** §8.1 ratio
identity (`xi_ratio_identity`) this is `-ξ_{a-j}/ξ_{a+j}`, and with `-1` a `37`-th power
(`caseII_negOne_isPthPower`) it becomes the ratio congruence stated here (with `b = a-j`). -/
def MirimanoffRhoReality37 (j : ZMod 37) : Prop :=
  ∀ b : ZMod 37, (hb : b ≠ 0) → (hb2 : b + 2 * j ≠ 0) →
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((xiUnitZMod (b + 2 * j) hb2 * (xiUnitZMod b hb)⁻¹ :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))

/-- **The single-step index equality from the residual.**  Under `MirimanoffRhoReality37 j`, for
`b ≠ 0` and `b + 2j ≠ 0`, `xiIndZMod (b + 2j) = xiIndZMod b` (via `caseII_xi_ratio_ind`). -/
theorem caseII_xiIndZMod_step {j : ZMod 37} (hρ : MirimanoffRhoReality37 j)
    {b : ZMod 37} (hb : b ≠ 0) (hb2 : b + 2 * j ≠ 0) :
    xiIndZMod (b + 2 * j) = xiIndZMod b := by
  rw [xiIndZMod_of_ne hb2, xiIndZMod_of_ne hb]
  exact caseII_xi_ratio_ind (caseII_val_coprime hb) (caseII_val_coprime hb2) (hρ b hb hb2)

/-- **The telescoped vanishing of `xiIndZMod`.**  Under `MirimanoffRhoReality37 j` with `j ≠ 0`,
`xiIndZMod c = 0` for every `c ≠ 0`.  This is Washington Lemma 9.8 step 7: every real cyclotomic
unit `ξ_b` (`b ≢ 0`) is a `37`-th power mod `lv149` (`ind₃₇ ξ_b = 0`).

Proof: with `t = 2j ≠ 0` (a generator of `ℤ/37ℤ`), `caseII_xiIndZMod_step` is exactly the orbit
hypothesis of `caseII_telescope_const`, so `xiIndZMod` is constant on nonzero multiples of `t`,
hence on all nonzero residues; and `xiIndZMod 1 = ind₃₇ ξ_1 = 0` (`caseII_residueInd37_xiUnit_one`,
`ξ_1 = 1`). -/
theorem caseII_xiIndZMod_eq_zero {j : ZMod 37} (hρ : MirimanoffRhoReality37 j) (hj : j ≠ 0)
    {c : ZMod 37} (hc : c ≠ 0) : xiIndZMod c = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `t = 2j ≠ 0`.
  have ht : 2 * j ≠ 0 := by
    intro h; apply hj
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' caseII_two_ne_zero_zmod37
    · exact h'
  -- The orbit constancy on nonzero multiples of `t`.
  have hconst : ∀ d : ZMod 37, d ≠ 0 → xiIndZMod (d * (2 * j)) = xiIndZMod (1 * (2 * j)) :=
    caseII_telescope_const ht xiIndZMod (fun e he1 he2 ↦ by
      -- `Hstep e : xiIndZMod ((e+1)·t) = xiIndZMod (e·t)`; from the step lemma at `b = e·t`.
      have hbe : e * (2 * j) + 2 * j = (e + 1) * (2 * j) := by ring
      rw [← hbe]
      exact caseII_xiIndZMod_step hρ he1 (by rw [hbe]; exact he2))
  -- `xiIndZMod 1 = 0` (base `ξ_1 = 1`), and `1 = (2j)⁻¹ · (2j)`.
  have hone : xiIndZMod (1 : ZMod 37) = 0 := by
    rw [xiIndZMod, dif_neg caseII_one_ne_zero_zmod37,
      caseII_xiUnitZMod_one caseII_one_ne_zero_zmod37]
    have := residueInd37_mul (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) 1
    rw [mul_one] at this; linear_combination -this
  -- Connect: `xiIndZMod 1 = xiIndZMod (1·t)`, and every nonzero `c = (c·t⁻¹)·t`.
  have hc1 : xiIndZMod (1 : ZMod 37) = xiIndZMod (1 * (2 * j)) := by
    have h := hconst ((2 * j)⁻¹) (inv_ne_zero ht)
    rwa [inv_mul_cancel₀ ht] at h
  -- Now `xiIndZMod c = xiIndZMod (1·t) = xiIndZMod 1 = 0`.
  have hceq : c = (c * (2 * j)⁻¹) * (2 * j) := by
    rw [mul_assoc, inv_mul_cancel₀ ht, mul_one]
  rw [hceq, hconst (c * (2 * j)⁻¹) (mul_ne_zero hc (inv_ne_zero ht)), ← hc1, hone]

end BernoulliRegular.FLT37.Eichler

end
