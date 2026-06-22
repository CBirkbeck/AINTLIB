import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealClosure
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main

/-!
# Case-II route decision: the Thm-9.5 (computational, Cor 8.19) bypass

This file scopes — and builds the first piece of — the **computational**
route to the second case of Fermat's Last Theorem for `p = 37`
(Washington GTM 83, Theorem 9.5, p. 176), as an alternative to the
deep Theorem 9.4 route (which goes through Corollary 8.23 and the
single-unit `p`-adic-`L` valuation, Proposition 8.12 — absent from
mathlib and the repo).

## The decisive fact (why Thm 9.5 bypasses the `p`-adic-`L` gap)

Both Washington routes need to establish **Assumption II**: the descent
unit `η_a / η_b` (the ratio of the two Kummer units attached to two
auxiliary indices `a`, `b`) is a `p`-th power.

* **Theorem 9.4** establishes it via **Corollary 8.23** (a unit
  `≡ rational mod p²` is a `p`-th power, under `p³ ∤ B_{pi}`), whose
  proof needs Proposition 8.12, the single-unit `p`-adic-log valuation
  `v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1, ω^i))`.  The repo has
  **no** Kubota–Leopoldt `L_p` and **no** single-unit `p`-adic-log
  valuation (the existing log infrastructure is multi-unit /
  regulator-determinant shaped), so this is a genuine deep gap.

* **Theorem 9.5** establishes it **computationally** via
  **Corollary 8.19** (Proposition 8.18): a cyclotomic unit is a `p`-th
  power iff it is a `p`-th power modulo a single auxiliary prime ideal
  `𝔩` over a rational prime `ℓ ≡ 1 (mod p)` with `ℓ < p² − p`.  This
  test is `IsPthPowerModPrime`, and its cyclic-group criterion
  (`isPthPowerModPrime_lehmerVandiverPrime_iff`,
  `BernoulliRegular.isPthPowerModPrime_iff_pow_card_div_p_eq_one`) is
  **already proven and is element-agnostic** — it tests an arbitrary
  ring element `x`, not only the Pollaczek unit.  So the same engine
  that proved Vandiver-for-`37` (`¬ 37 ∣ h⁺`) detects the Case-II
  descent unit, with **no `p`-adic-`L` layer**.

This is the exact Case-II analogue of how the first case of FLT37 was
closed by the tractable (analytic Eichler / Gauss-sum) route bypassing
the deep one (Gross–Koblitz).

## What this file contains (the first piece)

1. `unit_notMem_lehmerVandiverPrime` — **any** unit (in particular a
   Case-II descent unit `η_a / η_b`) avoids the auxiliary prime `𝔩`,
   so the detector's side condition `x ∉ 𝔩` is automatic for units.
   This is the generalisation of `pollaczekUnitPlus_notMem_…` from the
   Pollaczek unit to an arbitrary unit, which is what Thm 9.5 needs.

2. `isPthPowerModPrime_unit_lehmerVandiverPrime_iff` — the **reusable
   Thm-9.5 detection criterion** for an arbitrary unit: `u` is a `p`-th
   power mod `𝔩` iff `Q(u^k) = 1` in the residue field.  This is the
   engine of Washington Lemmas 9.6–9.9 applied to any descent unit.

3. `lehmerVandiver149_lt_p_sq_sub_p`,
   `lehmerVandiver149_one_mod_p`,
   `lehmerVandiver149_satisfies_thm95_constraints` — verification that
   the **already-used** auxiliary prime `ℓ = 149` satisfies
   Washington's Theorem 9.5 numerical constraints for `p = 37`:
   `149 ≡ 1 (mod 37)` and `149 < 37² − 37 = 1332`.  (Washington's bound
   `ℓ < p² − p` is what makes the half-range certificate
   `Q_i^k (mod ℓ)` a *complete* `p`-th-power test.)

4. `CaseIIThm95Descent37` — a named `Prop` (a `def … : Prop`, **not**
   an axiom) scoping precisely the remaining content of the Thm-9.5
   Case-II descent: the assertion that the proven non-`p`-th-power
   certificate for the descent unit yields the Case-II bridge.  This
   pins the next step and lets downstream code chain parametrically
   along the computational route.

5. `caseIIThm95_descent_unit_certificate` — re-export of the proven
   concrete certificate `flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete`
   as the worked Thm-9.5 detection input, demonstrating the engine
   runs end-to-end on the `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`
   tuple.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer
  GTM 83, §8.3 (Proposition 8.18, Corollary 8.19, p. 158), Ch. 9
  (Theorem 9.5, Lemmas 9.6–9.9, p. 176).
* Vandiver, "Fermat's last theorem and the second factor in the
  cyclotomic class number," Bull. AMS 40 (1934) 118–126.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. The detector side condition is automatic for units -/

/-- **Any unit avoids the Lehmer–Vandiver prime.** A unit of a ring can
never lie in a proper (in particular prime) ideal.  This generalises
`FLT37.pollaczekUnitPlus_notMem_lehmerVandiverPrime` from the Pollaczek
unit to an *arbitrary* unit, which is exactly what the Theorem-9.5
descent needs: the descent unit `η_a / η_b` is a unit, hence the
`x ∉ 𝔩` side condition of the `p`-th-power-mod-`𝔩` criterion holds for
free. -/
theorem unit_notMem_lehmerVandiverPrime
    (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (u : (𝓞 (CyclotomicField p ℚ))ˣ) :
    ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ∉
      FLT37.lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  intro hmem
  have htop := (FLT37.lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).eq_top_of_isUnit_mem
    hmem u.isUnit
  exact (FLT37.lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne).ne_top htop

/-! ## 2. The reusable Thm-9.5 detection criterion (element-agnostic) -/

/-- **Thm-9.5 detection criterion for an arbitrary unit.** For a unit
`u : (𝓞 ℚ(ζ_p))ˣ`, `u` is a `p`-th power modulo the auxiliary prime
`𝔩` (over `ℓ = k·p + 1`) iff `Q(u^k) = 1` in the residue field
`𝓞 ℚ(ζ_p) / 𝔩 ≅ 𝔽_ℓ`.

This is the engine of Washington's Theorem 9.5 (Lemmas 9.6–9.9): the
half-range residue test `Q(η^k) (mod ℓ)` applied to the **descent
unit** `η = η_a / η_b`.  The criterion is the proven, element-agnostic
`isPthPowerModPrime_lehmerVandiverPrime_iff`, with the side condition
`u ∉ 𝔩` discharged by `unit_notMem_lehmerVandiverPrime`.

Combined with the contrapositive lift `IsPthPowerModPrime.not_isPow`
(`PthPowerLift.lean`), a single computation `Q(η^k) ≠ 1` in `ZMod ℓ`
proves `η` is **not** a `p`-th power globally — the Case-II Assumption-II
content, with no `p`-adic-`L` input. -/
theorem isPthPowerModPrime_unit_lehmerVandiverPrime_iff
    (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1)
    (u : (𝓞 (CyclotomicField p ℚ))ˣ) :
    BernoulliRegular.IsPthPowerModPrime p
        (FLT37.lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ↔
      Ideal.Quotient.mk (FLT37.lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne)
        (((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ k) = 1 :=
  FLT37.isPthPowerModPrime_lehmerVandiverPrime_iff (p := p) ℓ k hℓ ht_coprime ht_ne
    (unit_notMem_lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne u)

/-! ## 3. The auxiliary prime `ℓ = 149` satisfies Washington's Thm-9.5 bounds -/

/-- **`149 ≡ 1 (mod 37)`** — the splitting condition `ℓ = k·p + 1` with
`k = 4`, so that the residue field is `𝔽_{149}` and `37 ∣ 149 − 1`. -/
theorem lehmerVandiver149_one_mod_p : (149 : ℕ) = 4 * 37 + 1 := by decide

/-- **`149 < 37² − 37 = 1332`** — Washington's Theorem 9.5 bound
`ℓ < p² − p`.  This bound is what makes the half-range certificate
`Q_i^k (mod ℓ)` a *complete* `p`-th-power test (a smaller-than-`p²−p`
prime forces the residue test to detect genuine `p`-th-power-ness, not
a false positive). -/
theorem lehmerVandiver149_lt_p_sq_sub_p : (149 : ℕ) < 37 ^ 2 - 37 := by decide

/-- **`149` satisfies all of Washington's Theorem-9.5 numerical
constraints for `p = 37`**: it is prime, `≡ 1 (mod 37)`, and
`< 37² − 37 = 1332`.  Hence `149` is a *valid* Theorem-9.5 auxiliary
prime, and it is precisely the prime already used by the proven
Vandiver-for-`37` certificate (`lehmerVandiverPrime 37 149 4 …`). -/
theorem lehmerVandiver149_satisfies_thm95_constraints :
    Nat.Prime 149 ∧ (149 : ℕ) = 4 * 37 + 1 ∧ (149 : ℕ) < 37 ^ 2 - 37 :=
  ⟨by decide, lehmerVandiver149_one_mod_p, lehmerVandiver149_lt_p_sq_sub_p⟩

/-! ## 4. Scoping the remaining Thm-9.5 Case-II descent content -/

/-- **Named boundary for the Theorem-9.5 Case-II descent** (a
`def … : Prop`, **not** an axiom).

This is the precise remaining content of the *computational* Case-II
route: the assertion that the Washington Theorem-9.5 Lehmer–Vandiver
descent (Lemmas 9.6–9.9 — express the Case-II descent unit `η_a / η_b`
via cyclotomic units, run the `Q_i^k (mod 𝔩)` residue test through the
proven detection criterion `isPthPowerModPrime_unit_lehmerVandiverPrime_iff`,
and feed the resulting non-`p`-th-power conclusion into the
minimal-counterexample / Vandermonde descent
`no_caseIIData37_of_descent_step`) yields the Case-II bridge for
`p = 37`, given Vandiver-for-`37` (`¬ 37 ∣ h⁺`, already proven).

Crucially, this boundary does **not** mention `NoSecondOrderIrregularPair`
/ `37³ ∤ B_{1184}` and does **not** mention Corollary 8.23 or the
`p`-adic-`L` layer: the Theorem-9.5 route is independent of the
second-order Bernoulli condition and of Proposition 8.12.  Discharging
it is the next step — it is the descent bookkeeping (Lemmas 9.6–9.9)
sitting on top of the *already proven* mod-`𝔩` detection engine. -/
def CaseIIThm95Descent37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32

/-! ## 5. The detection engine runs end-to-end on the concrete certificate -/

/-- **The Theorem-9.5 detection engine, demonstrated end-to-end.**
Re-export of the proven concrete certificate: for the worked tuple
`(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`, the (real) cyclotomic unit
`pollaczekUnitPlus 37 K 32` is **not** a `37`-th power modulo
`lehmerVandiverPrime 37 149 4 …` — a single `ZMod 149` computation,
established with **no `p`-adic-`L` input**.

This certifies that the mod-`𝔩` detection engine required by
Theorem 9.5 is fully operational in the repo; the Theorem-9.5 Case-II
descent (`CaseIIThm95Descent37`) reuses the *same* engine on the
Case-II descent unit `η_a / η_b`. -/
theorem caseIIThm95_descent_unit_certificate
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ BernoulliRegular.IsPthPowerModPrime 37
      (FLT37.lehmerVandiverPrime 37 149 4
        (by decide : (149 : ℕ) = 4 * 37 + 1)
        (by decide : (2 : ℕ).Coprime 149)
        (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) :=
  FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete

end BernoulliRegular.FLT37.Eichler

end
