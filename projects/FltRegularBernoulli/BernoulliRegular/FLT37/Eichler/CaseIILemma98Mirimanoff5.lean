import BernoulliRegular.FLT37.Eichler.CaseIILemma98Mirimanoff

/-!
# Washington Lemma 9.8 step 5 (the `ρ_a`-reality ratio congruence) for `p = 37`

This file discharges `MirimanoffRhoRealityProducer37` (`CaseIILemma98Mirimanoff.lean`) —
Washington *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Lemma 9.8 **step 5**, the last
deep analytic piece of the irregular-index local power (R4) — down to its **single irreducible
reality core**, the Washington **step 6** cyclic-power congruence

  `(ω + ζ^a θ)^k ≡ (ζ^a ω + θ)^k  (mod 𝔩)`,    `a ≢ ±j (mod p)`, `k = (ℓ-1)/p = 4`,

and **proves everything else of step 5** (steps 7–9 and the §8.1 landing) from it together with
the producer's own hypotheses (`ω + ζ^j θ ∈ 𝔩`, `ℓ ∤ θ`).

## Washington's step-5 chain (pp. 178–179) and what is proved here

Suppose a nontrivial conjugate factor `ω + ζ^j θ ≡ 0 (mod 𝔩)` occurs (`η = ζ^j ≠ 1`, `j ≠ 0`),
with `ℓ ∤ x, y` (Lemma 9.6).  Washington derives, for `a ≢ ±j (mod p)`:

* **Steps 1–6** (the `ρ_a`-reality + cyclic-group input): from `(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p · unit`
  with `ρ_a` **real** (`η_a = η_{-a}`, because `p ∤ h⁺` ⟹ II1 `[𝔞(η)]=[𝔞(η⁻¹)]`) and
  `ρ_a^{kp} ≡ 1` (Fermat, `𝔩 ∤ ρ_a`), with `k = (ℓ-1)/p` **even**,

    `(ω + ζ^a θ)^k ≡ (ζ^a ω + θ)^k  (mod 𝔩)`.                                       (step 6)

  This is the **single irreducible reality core**, isolated below as `CaseIIMirimanoffStep6Cong37`
  (a `def … : Prop`, **not** an axiom).  It is the only place where the real generators `ρ_a`
  enter — and they exist as elements only over `RealCaseIIData37` (II1 / `c = 1`), **not** over a
  bare `CaseIIData37`; everything else is local arithmetic mod `𝔩` from the producer's hypotheses.

* **Step 7** (PROVEN here, `caseII_step7_of_step6`): substitute `ω ≡ -ζ^j θ (mod 𝔩)` (the
  producer's factor hypothesis) into step 6 and cancel `θ^k` (`ℓ ∤ θ`):

    `(ζ^a - ζ^j)^k ≡ (1 - ζ^{a+j})^k  (mod 𝔩)`.

* **Steps 8–9** (PROVEN here, `caseII_ratio_isPthPow_field`): since `(ℤ[ζ] mod 𝔩)^×` is cyclic
  of order `ℓ - 1 = kp = 4·37`, `r^4 ≡ 1 ⟹ r` is a `37`-th power mod `𝔩`; so
  `(ζ^a-ζ^j)/(1-ζ^{a+j})` is a `37`-th power mod `𝔩`.

* **§8.1 landing** (PROVEN here, `caseII_xiRatio_ind_of_step7`): via the proven Lemma 8.1 ratio
  identity (`xi_ratio_identity`, `(ζ^a-ζ^j)/(1-ζ^{a+j}) = -ξ_{a-j}/ξ_{a+j}`) and `-1` a `37`-th
  power (`caseII_negOne_isPthPower`), `ξ_{a-j}·ξ_{a+j}^{-1}` (equivalently `ξ_{a+j}·ξ_{a-j}^{-1}`)
  is a `37`-th power mod `𝔩` — which is exactly `MirimanoffRhoReality37 j`.

So `MirimanoffRhoRealityProducer37` is **proved given only** `CaseIIMirimanoffStep6Cong37`
(`caseII_mirimanoffRhoRealityProducer37_of_step6`).

## Non-vacuity of the step-6 core

`MirimanoffRhoReality37 j` (`j ≠ 0`) is **false** (`caseII_not_rhoReality_of_ne_zero`, via the
proven `caseIIThm95_engine_runs`, `Q₃₂⁴ ≢ 1`).  Since the producer derives it from
`CaseIIMirimanoffStep6Cong37` plus the factor hypothesis, the step-6 core genuinely asserts that
no nontrivial conjugate factor `ω + ζ^j θ ∈ 𝔩` (`j ≠ 0`) can occur — Washington's `j = 0`.  It is
neither vacuously true (its `ρ_a` reality conclusion is a real `(mod 𝔩)` constraint), nor trivially
false (a genuine consequence of the descent over real data).  See
`caseII_step6_no_nontrivial_factor`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.1 (Lemma 8.1), §9.1–9.2
  (Lemma 9.8, pp. 178–179, steps 1–9).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-! ## 0. `1 - ζ^s ∉ lv149`, and `-1` is a `37`-th power in the residue field -/

/-- **`1 - ζ^s ∉ lv149` for `s ≢ 0 (mod 37)`.**  `1 - ζ^s = -(ζ^s - 1)` and
`ζ^s - 1 ∉ lv149` (`caseII_zetaPow_sub_one_notMem`); membership of a prime ideal is closed
under negation, so the negative is also outside. -/
theorem caseII_one_sub_zetaPow_notMem_lv149 {s : ℤ} (hs : ¬ (37 : ℤ) ∣ s) :
    (1 - zetaPow 37 (CyclotomicField 37 ℚ) s) ∉ lv149 := by
  intro hmem
  have hneg : (zetaPow 37 (CyclotomicField 37 ℚ) s - 1) ∈ lv149 := by
    have : (zetaPow 37 (CyclotomicField 37 ℚ) s - 1) =
        -(1 - zetaPow 37 (CyclotomicField 37 ℚ) s) := by ring
    rw [this]; exact neg_mem hmem
  exact caseII_zetaPow_sub_one_notMem hs hneg

/-- **`residueInd37 u⁻¹ = - residueInd37 u`** (additivity of the discrete log).  From
`residueInd37 (u·u⁻¹) = residueInd37 1 = 0` and `residueInd37_mul`. -/
theorem caseII_residueInd37_inv (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    residueInd37 u⁻¹ = - residueInd37 u := by
  have h1 : residueInd37 (u * u⁻¹) = 0 := by rw [mul_inv_cancel]; exact caseII_residueInd37_one
  rw [residueInd37_mul] at h1; linear_combination h1

/-! ## 1. The cyclic-group `p`-th-power criterion at `lv149`: `u⁴ = 1 ⟹ u` a `37`-th power

`(𝓞 K / lv149)ˣ` is cyclic of order `ℓ - 1 = 148 = 4·37`.  Washington's step-8 fact
"`x^k ≡ 1 (mod 𝔩) ⟹ x` is a `p`-th power mod `𝔩`" is, in the unit group, exactly
`u^(card/p) = u^4 = 1 ⟹ u` is a `37`-th power, by `isPthPower_iff_pow_card_div_eq_one`. -/

/-- **The residue unit group is cyclic of order `148 = 4·37`, and `148 / 37 = 4`.**  Hence
Washington's `k = (ℓ-1)/p = 4` is exactly `Nat.card (𝓞 K / 𝔩)ˣ / 37`. -/
theorem caseII_lv149_unit_card_div :
    Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ / 37 = 4 := by
  rw [lv149_unit_card]

/-- **Washington step 8 (unit form): `u⁴ = 1 ⟹ u` is a `37`-th power mod `lv149`.**

In the cyclic group `(𝓞 K / lv149)ˣ` of order `148 = 4·37`, an element `u` with `u⁴ = 1` lies
in the unique subgroup of index `37` (the `37`-th powers): `isPthPower_iff_pow_card_div_eq_one`
with `Nat.card / 37 = 4` (`caseII_lv149_unit_card_div`) turns `u⁴ = 1` into `∃ v, u = v^37`. -/
theorem caseII_unit_isPthPow_of_fourthPow_one
    (u : (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) (hu : u ^ 4 = 1) :
    ∃ v : (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ, u = v ^ 37 := by
  have hp_dvd : (37 : ℕ) ∣ Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ := by
    rw [lv149_unit_card]; decide
  rw [isPthPower_iff_pow_card_div_eq_one hp_dvd u, caseII_lv149_unit_card_div]
  exact hu

/-! ## 2. The field ratio engine (Washington steps 8–9): a `4`-th-power-trivial ratio is a `37`-th
power

The residue field `F = 𝓞 K / lv149` is `𝔽₁₄₉`.  For `p, q : 𝓞 K` with `p, q ∉ 𝔩`, if their
residues satisfy `Q(p)⁴ = Q(q)⁴`, then the ratio `Q(p)·Q(q)⁻¹` is a `37`-th power in `F`: the
ratio is a unit with fourth power `1`, so §1 applies. -/

local notation "F37" => 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149

/-- **Washington steps 8–9: a ratio with trivial fourth power is a `37`-th power in the residue
field.**

For `p q : 𝓞 K` with `p, q ∉ lv149` and `Q(p)⁴ = Q(q)⁴` in `F = 𝓞 K / lv149`, the residue ratio
`Q(p)·Q(q)⁻¹` is a `37`-th power: `Q(p), Q(q)` are nonzero (units of the field `F`), the unit
ratio `u = Q(p)/Q(q)` has `u⁴ = Q(p)⁴/Q(q)⁴ = 1`, so `u = v^37`
(`caseII_unit_isPthPow_of_fourthPow_one`), hence `Q(p)·Q(q)⁻¹ = (v : F)^37`. -/
theorem caseII_ratio_isPthPow_field {p q : 𝓞 (CyclotomicField 37 ℚ)}
    (hp : p ∉ lv149) (hq : q ∉ lv149)
    (h4 : (Ideal.Quotient.mk lv149 p) ^ 4 = (Ideal.Quotient.mk lv149 q) ^ 4) :
    ∃ w : F37, (Ideal.Quotient.mk lv149 p) * (Ideal.Quotient.mk lv149 q)⁻¹ = w ^ 37 := by
  set Qp := Ideal.Quotient.mk lv149 p with hQp
  set Qq := Ideal.Quotient.mk lv149 q with hQq
  have hp0 : Qp ≠ 0 := fun h => hp ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  have hq0 : Qq ≠ 0 := fun h => hq ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  -- The unit ratio `u = Qp / Qq`, with underlying value `Qp · Qq⁻¹`.
  set u : (F37)ˣ := Units.mk0 Qp hp0 * (Units.mk0 Qq hq0)⁻¹ with hu_def
  have huval : (u : F37) = Qp * Qq⁻¹ := by
    rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  -- Its fourth power is `1`: `(Qp · Qq⁻¹)^4 = Qp^4 · (Qq^4)⁻¹ = Qq^4 · (Qq^4)⁻¹ = 1`.
  have hu4 : u ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, huval, Units.val_one, mul_pow, inv_pow, h4]
    exact mul_inv_cancel₀ (pow_ne_zero 4 hq0)
  obtain ⟨v, hv⟩ := caseII_unit_isPthPow_of_fourthPow_one u hu4
  refine ⟨(v : F37), ?_⟩
  -- `Qp · Qq⁻¹ = (u : F) = (v^37 : F) = (v : F)^37`.
  have hval37 : (u : F37) = (v : F37) ^ 37 := by
    rw [show (u : F37) = ((v ^ 37 : (F37)ˣ) : F37) from congrArg Units.val hv,
      Units.val_pow_eq_pow_val]
  rw [← huval]; exact hval37

/-! ## 3. The §8.1 landing: from step 7 to `residueInd37 ξ_s = residueInd37 ξ_d`

Combining §2 (the Washington ratio `(ζ^a-ζ^j)/(1-ζ^{a+j})` is a `37`-th power in `F`) with the
proven §8.1 residue identity (`caseII_xi_ratio_residue_identity`,
`Q(ξ_d)·Q(1-ζ^s) = Q(-1)·Q(ζ^a-ζ^j)·Q(ξ_s)`) and `-1` a `37`-th power
(`caseII_negOne_isPthPower`), the ratio of `ξ` units is a `37`-th power mod `𝔩`, hence their
indices agree. -/

/-- **`-1` is a `37`-th power in the residue field `F = 𝓞 K / lv149`.**  Unit form of
`caseII_negOne_isPthPower` (`-1 = (-1)^37`, `37` odd). -/
theorem caseII_negOne_residue_isPthPow :
    ∃ t : F37, (Ideal.Quotient.mk lv149 (-1 : 𝓞 (CyclotomicField 37 ℚ))) = t ^ 37 :=
  caseII_negOne_isPthPower

/-- **Step 7 ⟹ the `ξ`-ratio index equality** (proven, axiom-clean — Washington steps 8–9 + §8.1).

For `a ≢ ±j (mod 37)` realised by coprime naturals `s ≡ a+j`, `d ≡ a-j`, **if** the step-7
fourth-power congruence `Q((ζ^a-ζ^j)^4) = Q((1-ζ^s)^4)` holds, **then**
`residueInd37 ξ_s = residueInd37 ξ_d`.

Proof: §2 makes the ratio `Q(ζ^a-ζ^j)·Q(1-ζ^s)⁻¹` a `37`-th power `w^37` in `F`.  The §8.1
residue identity rearranges to `Q(ξ_s)·Q(ξ_d)⁻¹ = (w⁻¹)^37 · Q(-1)⁻¹`; with `Q(-1)` a `37`-th
power (`caseII_negOne_residue_isPthPow`), `ξ_s·ξ_d⁻¹` is a `37`-th power mod `𝔩`, so its index
vanishes, i.e. `residueInd37 ξ_s = residueInd37 ξ_d`. -/
theorem caseII_xiRatio_ind_of_step7 (a j : ℤ) (s d : ℕ)
    (hs : s.Coprime 37) (hd : d.Coprime 37)
    (hs_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a + j) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (s : ℤ))
    (hd_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a - j) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (d : ℤ))
    (haj : ¬ (37 : ℤ) ∣ (a - j)) (hsj : ¬ (37 : ℤ) ∣ s)
    (hstep7 :
      (Ideal.Quotient.mk lv149
          (zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j)) ^ 4 =
        (Ideal.Quotient.mk lv149 (1 - zetaPow 37 (CyclotomicField 37 ℚ) (s : ℤ))) ^ 4) :
    residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) s hs) =
      residueInd37 (xiUnit 37 (CyclotomicField 37 ℚ) d hd) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Abbreviations and non-membership facts.
  set zaj := zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j with hzaj
  set zs := (1 : 𝓞 (CyclotomicField 37 ℚ)) - zetaPow 37 (CyclotomicField 37 ℚ) (s : ℤ)
    with hzs
  have hzaj_notMem : zaj ∉ lv149 := caseII_zetaPow_sub_zetaPow_notMem haj
  have hzs_notMem : zs ∉ lv149 := caseII_one_sub_zetaPow_notMem_lv149 hsj
  -- §2: the Washington ratio is a `37`-th power in `F`.
  obtain ⟨w, hw⟩ := caseII_ratio_isPthPow_field hzaj_notMem hzs_notMem hstep7
  -- The §8.1 residue identity: `Q(ξ_d)·Q(zs) = Q(-1)·Q(zaj)·Q(ξ_s)`.
  have hid := caseII_xi_ratio_residue_identity a j s d hs hd hs_eq hd_eq
  -- It suffices to show `IsPthPowerModPrime 37 lv149 (ξ_s · ξ_d⁻¹)`.
  have hgoal : BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((xiUnit 37 (CyclotomicField 37 ℚ) s hs * (xiUnit 37 (CyclotomicField 37 ℚ) d hd)⁻¹ :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
    -- Work in the residue field.
    set Q := Ideal.Quotient.mk lv149 with hQ
    set Qξs := Q (xiUnit 37 (CyclotomicField 37 ℚ) s hs : 𝓞 (CyclotomicField 37 ℚ))
      with hQξs
    set Qξd := Q (xiUnit 37 (CyclotomicField 37 ℚ) d hd : 𝓞 (CyclotomicField 37 ℚ))
      with hQξd
    -- Residues of the `ξ`-units are nonzero (they are global units, never in the prime `𝔩`).
    have hξs0 : Qξs ≠ 0 := fun h => caseII_unit_notMem_lv149
      (xiUnit 37 (CyclotomicField 37 ℚ) s hs) ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    have hξd0 : Qξd ≠ 0 := fun h => caseII_unit_notMem_lv149
      (xiUnit 37 (CyclotomicField 37 ℚ) d hd) ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    have hzaj0 : Q zaj ≠ 0 := fun h => hzaj_notMem ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    have hzs0 : Q zs ≠ 0 := fun h => hzs_notMem ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    -- `-1` is a `37`-th power in `F`.
    obtain ⟨t, ht⟩ := caseII_negOne_residue_isPthPow
    have hneg0 : Q (-1 : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 := fun h0 =>
      caseII_unit_notMem_lv149 (-1) ((Ideal.Quotient.eq_zero_iff_mem).mp h0)
    -- The identity in `F`: `Qξd · Q(zs) = Q(-1) · Q(zaj) · Qξs`.
    have hidQ : Qξd * Q zs = Q (-1) * Q zaj * Qξs := hid
    have hw' : Q zaj * (Q zs)⁻¹ = w ^ 37 := hw
    -- Step A: field identity `Qξs·Qξd⁻¹ = (Q(-1))⁻¹·(Q zaj·(Q zs)⁻¹)⁻¹`, from `hidQ`.
    have hratio : Qξs * Qξd⁻¹ = (Q (-1))⁻¹ * (Q zaj * (Q zs)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      field_simp
      linear_combination -hidQ
    -- Step B: substitute `Q zaj · (Q zs)⁻¹ = w^37` and `Q(-1) = t^37`.
    rw [hw', ht] at hratio
    -- The witness `t⁻¹ · w⁻¹`; its `37`-th power matches `Qξs · Qξd⁻¹`.
    refine ⟨t⁻¹ * w⁻¹, ?_⟩
    rw [Units.val_mul, map_mul, map_units_inv, ← hQξs, ← hQξd, hratio]
    simp only [mul_pow, inv_pow]
  -- Convert `IsPthPowerModPrime` of the ratio to the index equality.
  rw [isPthPowerModPrime_iff_residueInd37_eq_zero, residueInd37_mul,
    caseII_residueInd37_inv] at hgoal
  linear_combination hgoal

/-! ## 4. Step 6 ⟹ step 7: substitute `ω ≡ -ζ^j θ (mod 𝔩)` and cancel `θ^k`

Washington's step 6 is `(ω + ζ^a θ)^k ≡ (ζ^a ω + θ)^k (mod 𝔩)`.  The producer's factor
hypothesis `ω + ζ^j θ ∈ 𝔩` gives `Q(ω) = -Q(ζ^j)·Q(θ)`; substituting,
`Q(ω + ζ^a θ) = Q(θ)·Q(ζ^a - ζ^j)` and `Q(ζ^a ω + θ) = Q(θ)·Q(1 - ζ^{a+j})`.  So step 6 reads
`Q(θ)^k·Q(ζ^a-ζ^j)^k = Q(θ)^k·Q(1-ζ^{a+j})^k`; with `ℓ ∤ θ` (`Q(θ) ≠ 0`), cancelling `Q(θ)^k`
gives step 7. -/

/-- **Step 6 ⟹ step 7** (proven, axiom-clean).

Given `x, y : 𝓞 K`, an integer `j`, the factor hypothesis `x + ζ^j·y ∈ lv149` (with
`ζ^j = ζ_p^j` realised via `zetaPow`), `y ∉ lv149`, and Washington's step-6 congruence
`Q((x + ζ^a y)^4) = Q((ζ^a x + y)^4)`, the step-7 congruence
`Q((ζ^a - ζ^j)^4) = Q((1 - ζ^{a+j})^4)` holds.

Proof: in the residue field, `Q(x) = -Q(ζ^j)·Q(y)` (factor hypothesis), so
`Q(x + ζ^a y) = Q(y)·Q(ζ^a - ζ^j)` and `Q(ζ^a x + y) = Q(y)·Q(1 - ζ^{a+j})`; step 6 becomes
`Q(y)^4·Q(ζ^a-ζ^j)^4 = Q(y)^4·Q(1-ζ^{a+j})^4`, and `Q(y) ≠ 0` cancels `Q(y)^4`. -/
theorem caseII_step7_of_step6 (x y : 𝓞 (CyclotomicField 37 ℚ)) (a j : ℤ)
    (hfac : x + zetaPow 37 (CyclotomicField 37 ℚ) j * y ∈ lv149)
    (hy : y ∉ lv149)
    (hstep6 :
      (Ideal.Quotient.mk lv149 (x + zetaPow 37 (CyclotomicField 37 ℚ) a * y)) ^ 4 =
        (Ideal.Quotient.mk lv149
          (zetaPow 37 (CyclotomicField 37 ℚ) a * x + y)) ^ 4) :
    (Ideal.Quotient.mk lv149
        (zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j)) ^ 4 =
      (Ideal.Quotient.mk lv149
        (1 - zetaPow 37 (CyclotomicField 37 ℚ) (a + j))) ^ 4 := by
  set Q := Ideal.Quotient.mk lv149 with hQ
  have hy0 : Q y ≠ 0 := fun h => hy ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  -- `Q(x) = -Q(ζ^j)·Q(y)` from the factor hypothesis.
  have hx_eq : Q x = -(Q (zetaPow 37 (CyclotomicField 37 ℚ) j) * Q y) := by
    have hmem : Q (x + zetaPow 37 (CyclotomicField 37 ℚ) j * y) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hfac
    rw [map_add, map_mul] at hmem
    linear_combination hmem
  -- `Q(ζ^{a+j}) = Q(ζ^a)·Q(ζ^j)`.
  have hzadd : Q (zetaPow 37 (CyclotomicField 37 ℚ) (a + j)) =
      Q (zetaPow 37 (CyclotomicField 37 ℚ) a) * Q (zetaPow 37 (CyclotomicField 37 ℚ) j) := by
    rw [zetaPow_add, map_mul]
  -- The two substituted residue forms.
  have hL : Q (x + zetaPow 37 (CyclotomicField 37 ℚ) a * y) =
      Q y * Q (zetaPow 37 (CyclotomicField 37 ℚ) a - zetaPow 37 (CyclotomicField 37 ℚ) j) := by
    rw [map_add, map_mul, map_sub, hx_eq]; ring
  have hR : Q (zetaPow 37 (CyclotomicField 37 ℚ) a * x + y) =
      Q y * Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) (a + j)) := by
    rw [map_add, map_mul, map_sub, map_one, hx_eq, hzadd]; ring
  -- Step 6 in substituted form, then cancel `Q(y)^4`.
  rw [hL, hR, mul_pow, mul_pow] at hstep6
  exact mul_left_cancel₀ (pow_ne_zero 4 hy0) hstep6

/-! ## 5. The step-6 reality core (the residual) and the discharge of the producer

`CaseIIMirimanoffStep6Cong37` is Washington Lemma 9.8 **step 6** over the Case-II descent: for a
nontrivial conjugate factor `ω + ζ^j θ ∈ lv149` (`η = ζ^j ≠ 1`, `ℓ ∤ ω, θ`) and every
`a ≢ ±j (mod 37)`,

  `(ω + ζ^a θ)^4 ≡ (ζ^a ω + θ)^4  (mod 𝔩)`.

This is the **single irreducible analytic core**: it is the only step requiring the real
generators `ρ_a` (`(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p·unit` with `ρ_a` real, `ρ_a^{kp} ≡ 1`, `k` even),
which exist as elements only over `RealCaseIIData37` (II1 / `c = 1`,
`caseIIRootClassConjFixed37_proven`), **not** over a bare `CaseIIData37`.  Everything around it
(steps 7–9, the §8.1 landing) is proved above. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8 step 6 over the Case-II descent for `p = 37`** (a `def … : Prop`,
**not** an axiom) — the smallest irreducible reality core.

For every Case-II descent instance with a *nontrivial* conjugate factor `D.x + η·D.y ∈ lv149`
(`η ∈ μ₃₇`, `η ≠ 1`, `ℓ ∤ D.x, D.y`), the index `j : ℤ` with `ζ^j = η`, and every integer `a`
with `a ≢ ±j (mod 37)`, Washington's step-6 cyclic-power congruence holds:

  `Q((D.x + ζ^a·D.y)^4) = Q((ζ^a·D.x + D.y)^4)`     in `𝓞 K / lv149`.

This is the `ρ_a`-reality input (`(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p·unit`, `ρ_a` **real** since
`p ∤ h⁺`, plus `ρ_a^{kp} ≡ 1` and `k = (ℓ-1)/p = 4` even).  The real generators `ρ_a` live over
`RealCaseIIData37` (II1 / `c = 1`), so this congruence is the genuine open content that is not
manufacturable from a bare `CaseIIData37`. -/
def CaseIIMirimanoffStep6Cong37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)},
    η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) →
    η ≠ 1 →
    D.x ∉ lv149 → D.y ∉ lv149 →
    D.x + η * D.y ∈ lv149 →
    ∀ (j : ℤ), zetaPow 37 (CyclotomicField 37 ℚ) j = η →
    ∀ (a : ℤ), ¬ (37 : ℤ) ∣ (a - j) → ¬ (37 : ℤ) ∣ (a + j) →
      (Ideal.Quotient.mk lv149
          (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y)) ^ 4 =
        (Ideal.Quotient.mk lv149
          (zetaPow 37 (CyclotomicField 37 ℚ) a * D.x + D.y)) ^ 4

/-! ### Exponent bookkeeping for the `ZMod 37 → ℤ` translation in the producer -/

/-- `zetaU^((c : ZMod 37).val) = zetaU^e` whenever `(e : ZMod 37) = c`, via the order-`37`
exponent congruence (`unit'_zpow_congr`). -/
theorem caseII_zetaU_zpow_val_eq {c : ZMod 37} {e : ℤ} (he : (e : ZMod 37) = c) :
    zetaU 37 (CyclotomicField 37 ℚ) ^ e =
      zetaU 37 (CyclotomicField 37 ℚ) ^ ((c.val : ℕ) : ℤ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply unit'_zpow_congr
  -- `37 ∣ e - c.val` since `(e : ZMod 37) = c = (c.val : ZMod 37)`.
  have h1 : ((e - (c.val : ℕ) : ℤ) : ZMod 37) = 0 := by
    push_cast
    rw [he, ZMod.natCast_val, ZMod.cast_id, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1

/-- `¬ (37 : ℤ) ∣ e` whenever `(e : ZMod 37) ≠ 0`. -/
theorem caseII_not_dvd_of_zmod_ne_zero {e : ℤ} (he : (e : ZMod 37) ≠ 0) :
    ¬ (37 : ℤ) ∣ e := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at he

/-! ### `xiUnitZMod` ↔ `xiUnit` at the `.val` index (proof-irrelevant coprimality) -/

/-- `xiUnitZMod c hc = xiUnit 37 K c.val h` for any coprimality proof `h` (the coprimality argument
of `xiUnit` is proof-irrelevant). -/
theorem caseII_xiUnitZMod_eq_xiUnit {c : ZMod 37} (hc : c ≠ 0) (h : c.val.Coprime 37) :
    xiUnitZMod c hc = xiUnit 37 (CyclotomicField 37 ℚ) c.val h :=
  caseII_xiUnit_congr (CyclotomicField 37 ℚ) rfl (caseII_val_coprime hc) h

/-! ## 6. The producer, discharged from the step-6 reality core -/

open FLT37.LehmerVandiver.CaseII in
/-- **`MirimanoffRhoRealityProducer37` from the step-6 reality core** (proven, axiom-clean *given*
`CaseIIMirimanoffStep6Cong37`).

This **discharges** Washington Lemma 9.8 step 5 down to its single irreducible reality core
`CaseIIMirimanoffStep6Cong37` (step 6).  For the producer's nontrivial conjugate factor
`D.x + η·D.y ∈ lv149` (`η = ζ^i`, `i ≠ 0`) and every `b ≠ 0`, `b + 2i ≠ 0`:

* translate `b` to Washington's exponent `a ≡ b + i (mod 37)` (so `a - i ≡ b`,
  `a + i ≡ b + 2i`, both `≢ 0`);
* feed step 6 (the residual) at `j = (i : ℤ)`, `a` into `caseII_step7_of_step6` to obtain step 7
  `Q((ζ^a-ζ^i)^4) = Q((1-ζ^{a+i})^4)`;
* feed step 7 into `caseII_xiRatio_ind_of_step7` (Washington steps 8–9 + §8.1) to get
  `residueInd37 ξ_{(b+2i).val} = residueInd37 ξ_{b.val}`;
* convert to `IsPthPowerModPrime 37 lv149 (ξ_{(b+2i).val}·ξ_{b.val}⁻¹)`, i.e.
  `MirimanoffRhoReality37 (i : ZMod 37)`. -/
theorem caseII_mirimanoffRhoRealityProducer37_of_step6
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_step6 : CaseIIMirimanoffStep6Cong37) :
    MirimanoffRhoRealityProducer37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hV hSO m D η hη_mem hη_ne hx hy hsum i hi
  -- The step-6 hypotheses, specialised once to `j = (i : ℤ)`.
  -- `zetaPow (i : ℤ) = η`.
  have hzη : zetaPow 37 (CyclotomicField 37 ℚ) ((i : ℕ) : ℤ) = η := by
    rw [zetaPow_natCast]; exact hi
  set iZ : ZMod 37 := (i : ZMod 37) with hiZ
  -- Goal: `MirimanoffRhoReality37 iZ`.
  intro b hb hb2
  -- Washington's exponent `aZ = b + iZ`; integer representative `a = aZ.val`.
  set aZ : ZMod 37 := b + iZ with haZ
  set a : ℤ := ((aZ.val : ℕ) : ℤ) with ha
  -- `s = (b + 2iZ).val`, `d = b.val`, and their coprimality.
  have hs_cop : ((b + 2 * iZ).val).Coprime 37 := caseII_val_coprime hb2
  have hd_cop : (b.val).Coprime 37 := caseII_val_coprime hb
  -- The `ZMod 37` images of `a ± j`.
  have ha_im : ((a : ℤ) : ZMod 37) = aZ := by
    rw [ha]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
  have hai_im : ((a + (i : ℤ) : ℤ) : ZMod 37) = b + 2 * iZ := by
    rw [show ((a + (i : ℤ) : ℤ) : ZMod 37)
        = ((a : ℤ) : ZMod 37) + ((i : ℕ) : ZMod 37) from by push_cast; ring, ha_im, haZ, hiZ]
    ring
  have hami_im : ((a - (i : ℤ) : ℤ) : ZMod 37) = b := by
    rw [show ((a - (i : ℤ) : ℤ) : ZMod 37)
        = ((a : ℤ) : ZMod 37) - ((i : ℕ) : ZMod 37) from by push_cast; ring, ha_im, haZ, hiZ]
    ring
  -- Exponent congruences for `xi_ratio_identity` (`s ≡ a+i`, `d ≡ a-i`).
  have hs_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a + (i : ℤ)) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ (((b + 2 * iZ).val : ℕ) : ℤ) :=
    caseII_zetaU_zpow_val_eq hai_im
  have hd_eq : zetaU 37 (CyclotomicField 37 ℚ) ^ (a - (i : ℤ)) =
      zetaU 37 (CyclotomicField 37 ℚ) ^ ((b.val : ℕ) : ℤ) :=
    caseII_zetaU_zpow_val_eq hami_im
  -- `a - i ≢ 0` and `a + i ≢ 0` (i.e. `s ≢ 0`).
  have haj : ¬ (37 : ℤ) ∣ (a - (i : ℤ)) :=
    caseII_not_dvd_of_zmod_ne_zero (by rw [hami_im]; exact hb)
  have haj' : ¬ (37 : ℤ) ∣ (a + (i : ℤ)) :=
    caseII_not_dvd_of_zmod_ne_zero (by rw [hai_im]; exact hb2)
  have hsj : ¬ (37 : ℤ) ∣ (((b + 2 * iZ).val : ℕ) : ℤ) := by
    apply caseII_not_dvd_of_zmod_ne_zero
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact hb2
  -- Step 6 (the residual) at `j = (i : ℤ)`, `a`.
  have hstep6 := h_step6 hV hSO D hη_mem hη_ne hx hy hsum ((i : ℕ) : ℤ) hzη a haj haj'
  -- Step 7 from step 6 + the factor hypothesis.
  have hfac : D.x + zetaPow 37 (CyclotomicField 37 ℚ) ((i : ℕ) : ℤ) * D.y ∈ lv149 := by
    rwa [hzη]
  have hstep7 := caseII_step7_of_step6 D.x D.y a ((i : ℕ) : ℤ) hfac hy hstep6
  -- Bridge `ζ^{a+i} = ζ^{(b+2i).val}` (`a + i ≡ b + 2i (mod 37)`) so step 7 matches the engine.
  have hzbridge : zetaPow 37 (CyclotomicField 37 ℚ) (a + ((i : ℕ) : ℤ)) =
      zetaPow 37 (CyclotomicField 37 ℚ) (((b + 2 * iZ).val : ℕ) : ℤ) := by
    apply zetaPow_congr
    have h0 : ((a + ((i : ℕ) : ℤ) - (((b + 2 * iZ).val : ℕ) : ℤ) : ℤ) : ZMod 37) = 0 := by
      rw [Int.cast_sub, hai_im,
        show ((((b + 2 * iZ).val : ℕ) : ℤ) : ZMod 37) = ((b + 2 * iZ).val : ZMod 37) from by
          push_cast; ring,
        ZMod.natCast_val, ZMod.cast_id, sub_self]
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  rw [hzbridge] at hstep7
  -- Apply Washington steps 8–9 + §8.1.
  have hind := caseII_xiRatio_ind_of_step7 a ((i : ℕ) : ℤ) (b + 2 * iZ).val b.val hs_cop hd_cop
    hs_eq hd_eq haj hsj hstep7
  -- Convert the index equality to the `IsPthPowerModPrime` ratio of `MirimanoffRhoReality37`,
  -- writing `ξ_{(b+2i).val}·ξ_{b.val}⁻¹` via `xiUnitZMod`.
  rw [caseII_xiUnitZMod_eq_xiUnit (c := b + 2 * iZ) hb2 hs_cop,
    caseII_xiUnitZMod_eq_xiUnit (c := b) hb hd_cop,
    isPthPowerModPrime_iff_residueInd37_eq_zero, residueInd37_mul, caseII_residueInd37_inv]
  linear_combination hind

/-! ## 7. Capstone wiring: the step-6 core discharges Lemma 9.8, and is non-vacuous

Given the step-6 reality core, the producer is proved (§6), which through the proven telescoping +
σ-collapse (`caseII_lemma98Mirimanoff_of_rhoReality`) discharges `Lemma98MirimanoffPthPower37`, and
through `caseII_lemma98_x_add_y_mem_of_dvd_z` (+ the proven `caseIIThm95_engine_runs`) gives the
full Washington Lemma 9.8 `ℓ ∣ (ω + θ)` (`j = 0`). -/

open FLT37.LehmerVandiver.CaseII in
/-- **`Lemma98MirimanoffPthPower37` from the step-6 reality core** (proven, axiom-clean *given*
`CaseIIMirimanoffStep6Cong37`).  Composes the producer discharge (§6) with the proven step-7
telescoping + step-8 σ-collapse (`caseII_lemma98Mirimanoff_of_rhoReality`). -/
theorem caseII_lemma98Mirimanoff_of_step6
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_step6 : CaseIIMirimanoffStep6Cong37) :
    Lemma98MirimanoffPthPower37 :=
  caseII_lemma98Mirimanoff_of_rhoReality
    (caseII_mirimanoffRhoRealityProducer37_of_step6 h_step6)

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8 for `p = 37` from the single step-6 reality core** (proven, axiom-clean
*given* `CaseIIMirimanoffStep6Cong37`).

With the standing `ℓ ∣ z` (Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x, y`), the descended sum
`x + y ∈ lv149` (Washington's `j = 0`).  The step-6 core feeds
`caseII_lemma98_x_add_y_mem_of_dvd_z`; the `j ≠ 0` case is refuted because the producer forces
`E₃₂` to be a `37`-th power mod `lv149`, contradicting the proven `caseIIThm95_engine_runs`
(`Q₃₂⁴ ≢ 1`). -/
theorem caseII_lemma98_x_add_y_mem_of_step6
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_step6 : CaseIIMirimanoffStep6Cong37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 :=
  caseII_lemma98_x_add_y_mem_of_dvd_z
    (caseII_lemma98Mirimanoff_of_step6 h_step6) hV hSO D hz hxl hyl

/-! ### Non-vacuity of the step-6 reality core

`CaseIIMirimanoffStep6Cong37` is neither vacuously true nor trivially false: through the producer it
forces `MirimanoffRhoReality37 (i : ZMod 37)`, whose `i ≠ 0` instance is **false**
(`caseII_not_rhoReality_of_ne_zero`, via the proven `caseIIThm95_engine_runs`).  Hence the step-6
congruence genuinely constrains the descent (it asserts no nontrivial conjugate factor
`D.x + η·D.y ∈ lv149` with `η ≠ 1` can occur).  We make this explicit: under the step-6 core,
**no** nontrivial conjugate factor can occur. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Non-vacuity, made explicit.**  Under `CaseIIMirimanoffStep6Cong37`, for every Case-II descent
no *nontrivial* conjugate factor `D.x + η·D.y ∈ lv149` (`η ≠ 1`, `ℓ ∤ x, y`) can occur.

This is the genuine content of the step-6 reality core: the producer turns step 6 into
`MirimanoffRhoReality37 (i : ZMod 37)` (`η = ζ^i`, `i ≠ 0`), which
`caseII_not_rhoReality_of_ne_zero` refutes via the proven `caseIIThm95_engine_runs`
(`Q₃₂⁴ ≢ 1`).  So the step-6 congruence is *not*
vacuously satisfiable over a descent that produces a nontrivial factor — it carries exactly
Washington's `j = 0` conclusion, neither more nor less. -/
theorem caseII_step6_no_nontrivial_factor
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_step6 : CaseIIMirimanoffStep6Cong37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)}
    (hη_mem : η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη_ne : η ≠ 1) (hx : D.x ∉ lv149) (hy : D.y ∉ lv149) :
    D.x + η * D.y ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  intro hsum
  -- `η = ζ^i` with `i ≠ 0`.
  have hη_pow : η ^ 37 = 1 := by
    rw [mem_nthRootsFinset (by decide : 0 < 37)] at hη_mem; exact hη_mem
  obtain ⟨i, _hi_lt, hi_eq⟩ :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hη_pow
  have hi_ne : (i : ZMod 37) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : i = 0 := by omega
    rw [this, pow_zero] at hi_eq
    exact hη_ne hi_eq.symm
  -- The producer gives the (false-for-`i ≠ 0`) reality, contradicting `Q₃₂⁴ ≢ 1`.
  exact caseII_not_rhoReality_of_ne_zero hi_ne
    (caseII_mirimanoffRhoRealityProducer37_of_step6
      h_step6 hV hSO D hη_mem hη_ne hx hy hsum i hi_eq)

end BernoulliRegular.FLT37.Eichler

end
