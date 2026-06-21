import BernoulliRegular.FLT37.Eichler.CaseIIResidueProvenance
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ProductDescent

/-!
# Washington §9.1 Case-II descent: the descent unit `η_a/η_b = ε₁/ε₂` is real (Lemma 9.2 core)

This file builds the genuine Washington §9.1 Case-II descent piece feeding **piece (i)** of
`Cor815RealDescentResidueDataProvenance37` (`CaseIIResidueProvenance.lean`): the realness /
`K⁺`-descent of the Case-II descent unit `ε₁/ε₂` (Washington's `η_a/η_b`).  It imports only; it
does **not** modify any existing file.

## The math (Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 169-173)

The σ-anti **pair product** `𝔞(η)·𝔞(η⁻¹) = N_{K/K⁺}(…)` doubles `(ζ-1)`-valuations (`m → 2m`):
that is the descent wall, and the producer `caseII_sigmaPairAnchoredSource_proven` lands a *norm*
`K → K⁺` whose valuations double, so by itself it does **not** present `ε₁/ε₂` as a single real
unit at measure `< m`.  Washington's actual descent does **not** stop there.  From the σ-anti
`α = (B_a B_{-a})^p` with `ᾱ = α⁻¹` (σ-anti) and `α ≡ 1 (mod (1-ζ)^p)` — the **primarity**, which
in Case II is *free* — Lemma 9.1 (unramified at `(1-ζ)`) and Lemma 9.2 (σ-anti + unramified ⟹
`p`-th power, under `37 ∤ h⁺`) give `α = α₁^p`.  The `p`-th-root extraction *halves* the measure
(`2m → m`, then the descent gives `< m`), yielding `ω + ζ^aθ = (1-ζ^a) η_a ρ_a^p` with `η_a` a
**real** unit, and the descent unit `η_a/η_b` real.

### Why Case-II primarity is FREE (the key §9.1 insight)

This is the difference from Case I, where the analogous primarity was the hidden blocker.  In
Case II the relevant exponent `m` carries `p ∣ z`'s **high `λ`-valuation**: the descent equation
`ε₁ x'^p + ε₂ y'^p = ε₃ ((ζ-1)^m z')^p` has right-hand side divisible by `(ζ-1)^{pm}` with
`pm ≥ p > p - 1`, so `(ζ-1)^{p-1} ∼ p` already divides it.  Hence

* `(p : 𝓞 K) ∣ ε₁ x'^p + ε₂ y'^p`  — for **free**, from `m ≥ 1`;

which, by the flt-regular Kummer-congruence chain `exists_solution'_aux` +
`exists_dvd_pow_sub_Int_pow`, upgrades to the integer congruence

* `∃ n : ℤ, (p : 𝓞 K) ∣ (ε₁/ε₂ : 𝓞 K) - n`.

This **is** the primarity input of Lemma 9.2, and it is unconditional in Case II.  Feeding it to
the proven `caseII_discharge_unit_is_real` (the realness endpoint of the Kummer-unit
decomposition: a unit congruent to an integer mod `p` has trivial root-of-unity factor, so it is
real) discharges the realness of `ε₁/ε₂`: it descends to a unit of `𝓞 K⁺`.

## What this file proves (real, axiom-clean Lean)

* `caseIISigmaAntiDescent_quotient_int_congr` — **Case-II primarity is FREE.** From any Case-II
  Fermat descent equation `ε₁ x'^37 + ε₂ y'^37 = ε₃ ((ζ-1)^m z')^37` with `¬ (ζ-1) ∣ x'` and
  `m ≥ 1`, the descent quotient satisfies the integer congruence
  `∃ n : ℤ, (37 : 𝓞 K) ∣ (ε₁/ε₂ : 𝓞 K) - n`.

* `caseIISigmaAntiDescent_quotient_real` — **Realness (Lemma 9.2 endpoint).** That congruence
  feeds `caseII_discharge_unit_is_real`, so `ε₁/ε₂` descends: there is `u : (𝓞 K⁺)ˣ` with
  `algebraMap u = ε₁/ε₂`.

* `caseIISigmaAntiDescent_quotient_unitsMap` — the same realness in `Units.map` form:
  `Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom u = ε₁/ε₂`, the exact shape demanded by
  piece (i) of `Cor815RealDescentResidueDataProvenance37`.

* `caseIISigmaAntiDescent_descentUnit_freePart_zero` and `caseIISigmaAntiDescent_decomp_zero` and
  `caseIISigmaAntiDescent_residueEqns_of_exactUnit` — **Lemma 9.2 measure-halving, as a structural
  consistency result.** Under the exact-quotient-unit source (`ε₁/ε₂ = ε'^37`, the `p`-th-root
  extraction = Assumption II), the descent unit's mod-`37` free-part class vanishes
  (`realUnitToFreePartModP u = 0`, the `2m → m` compensation of the σ-pair measure-doubling), so
  its canonical decomposition is the zero vector and Lemma 9.8's residue equations hold.  This is a
  *consistency* check (the residue hypothesis is implied by Assumption II, hence demands nothing
  false); it is **not** a non-circular discharge of that hypothesis toward Assumption II.

* `caseIISigmaAntiDescent_realness_membership` — the realness/membership conjunct of piece (i):
  from the (scoped) Washington §9.1 cyclotomic-unit membership of the descent unit, there is
  `w ∈ caseIICPlus37` with `Units.map w = ε₁/ε₂`.  The **realness** is the unconditional §2 result;
  only the C⁺-membership is parametric.

* `caseIISigmaAntiDescent_residueDataProvenance` and `caseIISigmaAntiDescent_assumptionII` — the
  §5 wiring: the (scoped) cyclotomic-unit membership plus the (scoped) Lemma-9.8 residue equations
  on the **canonical** §2 descent unit discharge `Cor815RealDescentResidueDataProvenance37` (and,
  with `Lemma98LocalPower37`, **Assumption II**).  Realness is no longer an input.

## What remains for the *full* piece (i): the C⁺-membership (`w ∈ caseIICPlus37`)

Piece (i) of `Cor815RealDescentResidueDataProvenance37` asks for the real descent unit to lie in
the **cyclotomic-unit subgroup** `C⁺ = caseIICPlus37`, not merely in `(𝓞 K⁺)ˣ`.  Realness (above)
plus `37`-saturation (`caseIICor815_saturation_of_index_coprime`, proven under `37 ∤ h⁺`) reduce
this to the Washington §9.1 fact that the descent unit `η_a` is, up to `37`-th powers, the
**explicit cyclotomic unit** `(1 - ζ^a)/(1 - ζ)`-built unit of pp. 169-172 — i.e. its free part
already lies in the span of the Pollaczek family.  That identification (the concrete cyclotomic
form of `η_a`) is the precisely-scoped remaining content; it is recorded as
`caseIISigmaAntiDescent_quotient_in_CPlus` (a `def … : Prop`, **not** an axiom), and
`caseIISigmaAntiDescent_realness_membership` discharges the realness/membership conjunct of
piece (i) from it together with the unconditional realness proved here.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169-173), Lemma 9.1, Lemma 9.2, Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. Case-II primarity is FREE: the integer congruence on `ε₁/ε₂`

The descent quotient `ε₁/ε₂` is congruent to an integer modulo `37`.  This is the *primarity*
input of Lemma 9.2, and in Case II it is unconditional, coming straight from the descent
equation's high `(ζ-1)`-valuation on the right-hand side (`m ≥ 1` ⟹ `(ζ-1)^{37·m}` divisible by
`37`).  The upgrade from `37 ∣ ε₁ x'^37 + ε₂ y'^37` to the integer congruence is the standard
flt-regular Kummer-congruence chain. -/

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **Case-II primarity is FREE** (the key §9.1 insight, proven, axiom-clean).

For any Case-II Fermat descent equation
`ε₁ x'^37 + ε₂ y'^37 = ε₃ ((ζ-1)^m z')^37` with `¬ (ζ-1) ∣ x'` and `1 ≤ m`, the descent
quotient `ε₁/ε₂` is congruent to an integer modulo `37`:
`∃ n : ℤ, (37 : 𝓞 K) ∣ (ε₁/ε₂ : 𝓞 K) - n`.

This is the primarity hypothesis of Lemma 9.2.  In Case II it is free: the right-hand side is
divisible by `(ζ-1)^{37·m}`, and `37·m ≥ 37 > 36 = 37 - 1`, so `(ζ-1)^{37-1} ∼ 37` already
divides it, giving `37 ∣ ε₁ x'^37 + ε₂ y'^37`; the integer congruence then follows from
`exists_solution'_aux` + `exists_dvd_pow_sub_Int_pow`. -/
theorem caseIISigmaAntiDescent_quotient_int_congr
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {m : ℕ} (hm : 1 ≤ m)
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hx' : ¬ (hζ.toInteger - 1) ∣ x')
    (heq : (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
      (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ n : ℤ, (37 : 𝓞 K) ∣ ((ε₁ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) - (n : 𝓞 K) := by
  -- `(ζ-1)^{37-1}` divides the right-hand side because `37·m ≥ 37 - 1`.
  have hp_le : 37 - 1 ≤ m * 37 := by omega
  -- Rewrite the RHS to expose the `(ζ-1)^{37-1}` factor.
  have hmod := heq
  rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc,
    ← Nat.sub_add_cancel hp_le, add_comm _ (37 - 1), pow_add, mul_assoc] at hmod
  -- Pass to `𝓞 K / (37)`: the RHS vanishes (since `(ζ-1)^{37-1} ∼ 37`), so `37 ∣ LHS`.
  apply_fun Ideal.Quotient.mk (Ideal.span <| singleton ((37 : ℕ) : 𝓞 K)) at hmod
  rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime hζ).symm.dvd, zero_mul,
    Ideal.Quotient.eq_zero_iff_dvd] at hmod
  -- `37 ∣ ε₁ x'^37 + ε₂ y'^37` ⟹ `37 ∣ (ε₁/ε₂) - a^37` ⟹ `37 ∣ (ε₁/ε₂) - (b:ℤ)^37`.
  obtain ⟨a, ha⟩ :=
    exists_solution'_aux (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2) hζ hx' hmod
  obtain ⟨b, hb⟩ :=
    exists_dvd_pow_sub_Int_pow (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2) a
  have hcong := dvd_add ha hb
  rw [sub_add_sub_cancel, ← Int.cast_pow] at hcong
  exact ⟨b ^ 37, hcong⟩

/-! ## 2. Realness of the descent unit (Lemma 9.2 endpoint)

The free Case-II primarity congruence feeds the proven `caseII_discharge_unit_is_real`: a unit
congruent to an integer modulo `37` has trivial root-of-unity factor in its Kummer
decomposition, hence is fixed by complex conjugation, hence descends to `𝓞 K⁺`.  This is the
realness of Washington's descent unit `η_a/η_b`. -/

omit [NumberField.IsCMField K] in
/-- **The descent unit `ε₁/ε₂` is real (descends to `𝓞 K⁺`)** (proven, axiom-clean).

Combining the free Case-II primarity congruence (`caseIISigmaAntiDescent_quotient_int_congr`)
with the proven `caseII_discharge_unit_is_real`: there is a unit `u : (𝓞 K⁺)ˣ` with
`algebraMap u = ε₁/ε₂`.  This is the realness of Washington's descent unit `η_a/η_b` — the
endpoint of the Lemma-9.2 `p`-th-root extraction (the `p`-th-power structure compensating the
σ-pair measure-doubling). -/
theorem caseIISigmaAntiDescent_quotient_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {m : ℕ} (hm : 1 ≤ m)
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hx' : ¬ (hζ.toInteger - 1) ∣ x')
    (hy' : ¬ (hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
      (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ u : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (u : 𝓞 (NumberField.maximalRealSubfield K)) = ((ε₁ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) := by
  -- The descent-equation form consumed by `caseII_discharge_unit_is_real`
  -- (it only uses the integer congruence; the equation argument is along for typing).
  have h_descent :
      ((ε₁ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) * x' ^ 37 + y' ^ 37 =
        ((ε₃ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ 37 := by
    rw [← mul_right_inj' ε₂.isUnit.ne_zero, mul_add, ← mul_assoc,
      ← Units.val_mul, mul_div_cancel, ← mul_assoc, ← Units.val_mul, mul_div_cancel]
    exact heq
  exact FLT37.LehmerVandiver.CaseII.caseII_discharge_unit_is_real
    (p := 37) (K := K) (by decide : 2 < 37) hζ (ε₁ / ε₂)
    hx' hy' hz' h_descent
    (caseIISigmaAntiDescent_quotient_int_congr hζ hm hx' heq)

omit [NumberField.IsCMField K] in
/-- **Realness of `ε₁/ε₂` in `Units.map` form** (proven, axiom-clean).

The `(𝓞 K⁺)ˣ`-descent of `ε₁/ε₂` lifted to the unit homomorphism `Units.map`: there is
`u : (𝓞 K⁺)ˣ` with `Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom u = ε₁/ε₂`.  This is the
exact shape of the realness/membership conjunct demanded by piece (i) of
`Cor815RealDescentResidueDataProvenance37` (up to the `w ∈ caseIICPlus37` cyclotomic-unit
membership, scoped in §4). -/
theorem caseIISigmaAntiDescent_quotient_unitsMap
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {m : ℕ} (hm : 1 ≤ m)
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hx' : ¬ (hζ.toInteger - 1) ∣ x')
    (hy' : ¬ (hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
      (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ u : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom u =
        ε₁ / ε₂ := by
  obtain ⟨u, hu⟩ := caseIISigmaAntiDescent_quotient_real hζ hm hx' hy' hz' heq
  refine ⟨u, ?_⟩
  -- Both sides are units whose underlying ring elements agree (`hu`).
  apply Units.ext
  rw [Units.coe_map]
  exact hu

/-! ## 3. Lemma 9.2 measure-halving: the descent unit's mod-`37` free part vanishes

Washington's Lemma 9.2 (`p`-th-root extraction, the measure-halving `2m → m` that compensates the
σ-pair measure-doubling) is realised by the exact-quotient-unit source
`WashingtonCaseIIExactQuotientUnitPower37Source`: `ε₁/ε₂ = ε'^37`.  Because the mod-`37` free-part
map kills `37`-th powers (`cyclotomicUnitToFreePartModPMul_pow_eq_one`), the descent unit's free
part class is **zero**:

`realUnitToFreePartModP (Additive.ofMul u) = 0`  for the canonical `K⁺`-descent `u`.

This is the structural reason Washington Lemma 9.8's residue equations hold: the descent unit has
no surviving regular eigencomponent.  (Translating "free part `= 0`" into the explicit residue
equations of `Cor815RealDescentResidueDataProvenance37` additionally needs the linear independence
of the seventeen eigenvectors; that transport is left to the scoped residue input of §5.) -/

omit [NumberField.IsCMField K] in
/-- **The mod-`37` free-part class of a `37`-th power vanishes** (proven, axiom-clean).

`cyclotomicUnitToFreePartModPAdd (Additive.ofMul (v ^ 37)) = 0` for any `v : (𝓞 K)ˣ`: the
free-part map kills `37`-th powers (`37 • x = 0` in the mod-`37` reduction `ModN (·) 37`).  This is
the additive form of the proven `cyclotomicUnitToFreePartModPMul_pow_eq_one`. -/
theorem caseIISigmaAntiDescent_freePart_pow37
    [Fact (Nat.Prime 37)] (v : (𝓞 K)ˣ) :
    BernoulliRegular.cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (v ^ 37)) = 0 := by
  -- The multiplicative form kills `37`-th powers; transport it to the additive form.
  refine Multiplicative.ofAdd.injective ?_
  rw [ofAdd_zero]
  exact BernoulliRegular.cyclotomicUnitToFreePartModPMul_pow_eq_one (p := 37) (K := K) v

open FLT37.LehmerVandiver.CaseII in
/-- **The descent unit's mod-`37` free part vanishes** (proven, axiom-clean — Lemma 9.2 endpoint).

Under the exact-quotient-unit source (Lemma 9.2 realised: `ε₁/ε₂ = ε'^37`), any `K⁺`-descent `u`
of the descent quotient `ε₁/ε₂` has zero mod-`37` free-part class:
`realUnitToFreePartModP (Additive.ofMul u) = 0`.

This is the measure-halving `2m → m`: the σ-pair product doubles `(ζ-1)`-valuations, but the
`p`-th-root extraction of Lemma 9.2 sends the descent unit into the `37`-th powers, whose free
part is `0`.  It is the structural reason Washington Lemma 9.8's residue equations hold for the
descent unit. -/
theorem caseIISigmaAntiDescent_descentUnit_freePart_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)} {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37)
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hu : Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u = ε₁ / ε₂) :
    FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) = 0 := by
  -- Lemma 9.2 (realised): `ε₁/ε₂ = ε'^37`.
  obtain ⟨ε', hε'⟩ := h_exactUnit hV hSO D hx' hy' hz' heq
  -- `realUnitToFreePartModP u` factors through `Units.map u = ε₁/ε₂ = ε'^37`.
  rw [FLT37.realUnitToFreePartModP_apply, hu, hε']
  -- The free part of a `37`-th power is `0`.
  exact caseIISigmaAntiDescent_freePart_pow37 (K := CyclotomicField 37 ℚ) ε'

/-! ## 4. Discharging piece (i) of `Cor815RealDescentResidueDataProvenance37`

Piece (i) asks, for every Case-II descent instance, for a real cyclotomic unit `w ∈ caseIICPlus37`
with `Units.map (algebraMap (𝓞 K⁺) (𝓞 K)) w = ε₁/ε₂`.  §2 supplies the realness — a unit
`u : (𝓞 K⁺)ˣ` with `Units.map u = ε₁/ε₂` — *unconditionally* (free Case-II primarity).  What is
not yet supplied is the **cyclotomic-unit membership** `u ∈ caseIICPlus37 = C⁺`: that `u` lies in
the Sinnott cyclotomic-unit subgroup, not merely in `(𝓞 K⁺)ˣ`.

This is the Washington §9.1 fact that the descent unit `η_a` is, up to `37`-th powers, the
explicit cyclotomic unit `(1 - ζ^a)/(1 - ζ)`-built unit (pp. 169-172).  We name precisely this
remaining membership content and prove that, together with the unconditional realness of §2, it
discharges piece (i). -/

/-- **The Case-II descent unit lands in the cyclotomic-unit subgroup `C⁺`** (a `def … : Prop`,
**not** an axiom).

For every Case-II descent instance, the `(𝓞 K⁺)ˣ`-descent of `ε₁/ε₂` (the realness of which is
the *unconditional* `caseIISigmaAntiDescent_quotient_unitsMap` of §2) lies in
`C⁺ = caseIICPlus37`.

This is the *only* content of piece (i) not yet discharged: Washington §9.1's cyclotomic-unit
identification of the descent unit `η_a` (the explicit `(1 - ζ^a)/(1 - ζ)` form, pp. 169-172).  It
is **sound** — it is a membership assertion about the *specific* descent unit, never about an
arbitrary real unit.  The realness in `Units.map` form is supplied by §2, so the conjunct is
stated only about the canonical `K⁺`-descent. -/
def caseIISigmaAntiDescent_quotient_in_CPlus
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : FLT37.LehmerVandiver.CaseII.CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (_hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (_hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (_hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (_heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37)
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (_hu : Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u = ε₁ / ε₂),
    u ∈ caseIICPlus37

open FLT37.LehmerVandiver.CaseII in
/-- **Realness + membership of `η_a/η_b` from the cyclotomic-unit membership** (proven,
axiom-clean).

Given the Washington §9.1 cyclotomic-unit membership `caseIISigmaAntiDescent_quotient_in_CPlus`,
the realness/membership conjunct of piece (i) of `Cor815RealDescentResidueDataProvenance37` holds:
for every Case-II descent instance there is `w ∈ caseIICPlus37` with `Units.map w = ε₁/ε₂`.

The realness (`Units.map w = ε₁/ε₂`, the `(𝓞 K⁺)ˣ`-descent) is the **unconditional** §2 result —
free Case-II primarity (`caseIISigmaAntiDescent_quotient_int_congr`) feeding the proven
`caseII_discharge_unit_is_real`.  Only the cyclotomic-unit membership remains parametric, and it
is exactly the Washington §9.1 explicit form of the descent unit. -/
theorem caseIISigmaAntiDescent_realness_membership
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_mem : caseIISigmaAntiDescent_quotient_in_CPlus)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)} {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ w ∈ caseIICPlus37,
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂ := by
  -- §2: unconditional realness — the descent unit descends to `(𝓞 K⁺)ˣ`.
  obtain ⟨u, hu⟩ := caseIISigmaAntiDescent_quotient_unitsMap
    D.hζ D.one_le_m hx' hy' hz' heq
  -- Washington §9.1: that descent unit lies in `C⁺`.
  exact ⟨u, h_mem hV hSO D hx' hy' hz' heq u hu, hu⟩

/-! ## 5. Structural consistency: the residue equations follow from the Lemma-9.2 `p`-th-power

This section records a **consistency** fact about the residue-data approach, *not* a non-circular
step toward Assumption II.  §3 shows that **if** the descent unit is a `37`-th power
(`WashingtonCaseIIExactQuotientUnitPower37Source` = Assumption II) then its free part is `0`, hence
its canonical eigencomponent decomposition is the zero vector
(`caseIISigmaAntiDescent_decomp_zero`, proven from the seventeen-eigenvector linear independence
`pollaczekUnit_image_linearIndependent`), so Washington Lemma 9.8's residue equations hold.

This confirms the residue-data hypothesis of §6 is *sound* (it is implied by the very statement it
helps prove, so it demands nothing false), but it **cannot** be used to discharge that hypothesis
toward Assumption II: doing so would assume Assumption II to prove it.  The genuine *unconditional*
forward progress of this file is the **realness** of §1–§2; the residue equations and the
cyclotomic-unit membership remain genuine scoped inputs in §6. -/

/-- **The half-range residue equations on the canonical descent unit** (a `def … : Prop`, **not**
an axiom).

For each Case-II descent instance, the canonical `(𝓞 K⁺)ˣ`-descent `u` of `ε₁/ε₂` (produced
unconditionally by §2) has its mod-`37` free-part eigencomponents satisfying the half-range
Vandermonde residue equations of Washington Lemma 9.8 over all conjugates.

This is exactly the residue conjunct of `Cor815RealDescentResidueDataProvenance37`, but stated on
the **canonical** §2 descent unit rather than on an existentially-quantified `w`.  It is **sound**:
the equations are asserted for the *specific* descent unit's eigencomponents (and, as §5 shows, are
implied by Assumption II — so they demand nothing false). -/
def caseIISigmaAntiDescent_residueEqns
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : FLT37.LehmerVandiver.CaseII.CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (_hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (_hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (_hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (_heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37)
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (_hu : Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u = ε₁ / ε₂),
    ∀ a : Fin 18,
      ∑ j : Fin 18, caseIIConjugateResidue_regularPart
          (caseIIResidueProvenance_decomp
            (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u))) j *
        (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (j.1 + 1)) = 0

/-- **The canonical eigencomponent decomposition of the zero class is zero** (proven, axiom-clean).

`caseIIResidueProvenance_decomp 0 = 0`: the decomposition reproduces `0 = ∑_j c_j • [E_{2(j+1)}]`
with `c 17 = 0`; splitting off the `j = 17` principal term leaves a vanishing combination of the
seventeen linearly independent even Pollaczek eigenvectors (`pollaczekUnit_image_linearIndependent`
under `caseIIGaloisEigen_pollaczekClasses_ne_zero`), forcing every `c_j = 0`. -/
theorem caseIISigmaAntiDescent_decomp_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    caseIIResidueProvenance_decomp
        (0 : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) = 0 := by
  set c := caseIIResidueProvenance_decomp
    (0 : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) with hc
  -- The decomposition reproduces `0` and has vanishing principal coefficient.
  have hspec := caseIIResidueProvenance_decomp_spec
    (0 : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ))
  have hprin := caseIIResidueProvenance_decomp_principal_zero
    (0 : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ))
  rw [← hc] at hspec hprin
  -- Linear independence of the seventeen even-Pollaczek eigenvectors.
  have hli := pollaczekUnit_image_linearIndependent (K := CyclotomicField 37 ℚ)
    caseIIGaloisEigen_pollaczekClasses_ne_zero
  -- Split the `Fin 18` sum at the last index; the last term vanishes (`c 17 = 0`).
  rw [Fin.sum_univ_castSucc] at hspec
  have hlast : c (Fin.last 17) • caseIIConjugateResidue_eigenvector (Fin.last 17) = 0 := by
    rw [show c (Fin.last 17) = c 17 from rfl, hprin, zero_smul]
  rw [hlast, add_zero] at hspec
  -- The block sum over `Fin 17` is `∑ k, c (castSucc k) • familyMember k`.
  have hblock : ∑ k : Fin 17, c (Fin.castSucc k) •
        cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
            (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) (2 * (k : ℕ) + 2)))) = 0 := by
    refine Eq.trans (Finset.sum_congr rfl (fun k _ => ?_)) hspec.symm
    rw [show caseIIConjugateResidue_eigenvector (Fin.castSucc k) =
        cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
            (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) (2 * (k : ℕ) + 2)))) from by
      unfold caseIIConjugateResidue_eigenvector; congr 2]
  -- Linear independence forces every block coefficient to vanish.
  have hzero_block : ∀ k : Fin 17, c (Fin.castSucc k) = 0 :=
    (Fintype.linearIndependent_iff.mp hli) (fun k => c (Fin.castSucc k)) hblock
  -- Conclude `c = 0` on all of `Fin 18`.
  funext j
  rw [Pi.zero_apply]
  rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
  · exact hzero_block k
  · rw [show (Fin.last 17 : Fin 18) = 17 from rfl]; exact hprin

/-- **The residue equations follow from Assumption II** (proven, axiom-clean — a *consistency*
result, **not** a non-circular discharge).

If the descent unit is a `37`-th power (`WashingtonCaseIIExactQuotientUnitPower37Source` =
Assumption II), then Washington Lemma 9.8's half-range residue equations hold for *any* `K⁺`-descent
`u` of `ε₁/ε₂`: the descent unit's free part is zero (§3,
`caseIISigmaAntiDescent_descentUnit_freePart_zero`), so its canonical decomposition is the zero
vector (`caseIISigmaAntiDescent_decomp_zero`), whose regular part is `0`, making the residue sums
vanish.

This shows the scoped `caseIISigmaAntiDescent_residueEqns` is **sound** — it is implied by the
statement it helps prove, so it demands nothing false.  It **cannot** be fed to §6 to discharge the
residue input toward Assumption II (that would assume Assumption II to prove it). -/
theorem caseIISigmaAntiDescent_residueEqns_of_exactUnit
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_exactUnit : FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source) :
    caseIISigmaAntiDescent_residueEqns := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' heq u hu a
  -- §3: the descent unit's free part vanishes.
  have hfp : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) = 0 :=
    caseIISigmaAntiDescent_descentUnit_freePart_zero h_exactUnit hV hSO D hx' hy' hz' heq u hu
  -- The canonical decomposition of `0` is the zero vector, so its regular part is `0`.
  rw [hfp, caseIISigmaAntiDescent_decomp_zero]
  simp [caseIIConjugateResidue_regularPart]

/-! ## 6. Wiring: `Cor815RealDescentResidueDataProvenance37` from the canonical descent unit

`Cor815RealDescentResidueDataProvenance37` asks, for each instance, for a `w ∈ caseIICPlus37`
satisfying the half-range Vandermonde residue equations on its canonical eigencomponents **and**
`Units.map w = ε₁/ε₂`.  §2 produces the **canonical** descent unit `w = u` *unconditionally*
(realness), so the whole Prop reduces to two facts about that *specific* `u`:

* its cyclotomic-unit membership `u ∈ caseIICPlus37` (Washington §9.1, named
  `caseIISigmaAntiDescent_quotient_in_CPlus`); and
* the half-range residue equations on its canonical eigencomponents (Washington Lemma 9.8).

We keep the latter, applied to the §2-canonical descent unit, as the scoped input
`caseIISigmaAntiDescent_residueEqns`, and prove the two together discharge
`Cor815RealDescentResidueDataProvenance37`.  This makes explicit that the **realness** half of
piece (i) is no longer an input — it is the unconditional §2 result. -/

/-- **`Cor815RealDescentResidueDataProvenance37` from the canonical descent-unit data** (proven,
axiom-clean).

The realness of the descent unit `ε₁/ε₂` is the **unconditional** §2 result
(`caseIISigmaAntiDescent_quotient_unitsMap`), so `Cor815RealDescentResidueDataProvenance37` reduces
to the two facts about the *canonical* §2 descent unit `u`:

* `caseIISigmaAntiDescent_quotient_in_CPlus` — `u ∈ caseIICPlus37` (Washington §9.1, the
  cyclotomic-unit identification of `η_a`); and
* `caseIISigmaAntiDescent_residueEqns` — the half-range residue equations on `u`'s
  eigencomponents (Washington Lemma 9.8).

Composed with `caseIIResidueProvenance_assumptionII_of_residueData` (the proven engine), this
yields **Assumption II** from these two named inputs plus `Lemma98LocalPower37`.  In particular,
**piece (i)'s realness — `Units.map w = ε₁/ε₂` — is fully discharged here**; only the
cyclotomic-unit membership and the bare Lemma-9.8 residue equations remain. -/
theorem caseIISigmaAntiDescent_residueDataProvenance
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_mem : caseIISigmaAntiDescent_quotient_in_CPlus)
    (h_res : caseIISigmaAntiDescent_residueEqns) :
    Cor815RealDescentResidueDataProvenance37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' heq
  -- §2: the canonical descent unit `u` with `Units.map u = ε₁/ε₂` (unconditional realness).
  obtain ⟨u, hu⟩ := caseIISigmaAntiDescent_quotient_unitsMap
    D.hζ D.one_le_m hx' hy' hz' heq
  exact ⟨u, h_mem hV hSO D hx' hy' hz' heq u hu,
    h_res hV hSO D hx' hy' hz' heq u hu, hu⟩

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the canonical descent-unit data + Lemma 9.8** (proven, axiom-clean).

Composing `caseIISigmaAntiDescent_residueDataProvenance` with the proven engine
`caseIIResidueProvenance_assumptionII_of_residueData`: **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source`) follows from the three precisely-named inputs

* `caseIISigmaAntiDescent_quotient_in_CPlus` — Washington §9.1 cyclotomic-unit membership of `η_a`;
* `caseIISigmaAntiDescent_residueEqns` — Washington Lemma 9.8 residue equations on the canonical
  descent unit; and
* `Lemma98LocalPower37` — Washington Lemma 9.8's single-index mod-`𝔩` Kummer congruence.

The **realness** of the descent unit `η_a/η_b = ε₁/ε₂` is no longer an input: it is the
unconditional free-Case-II-primarity result of §2. -/
theorem caseIISigmaAntiDescent_assumptionII
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_mem : caseIISigmaAntiDescent_quotient_in_CPlus)
    (h_res : caseIISigmaAntiDescent_residueEqns)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIResidueProvenance_assumptionII_of_residueData
    (caseIISigmaAntiDescent_residueDataProvenance h_mem h_res) h_localPow

end BernoulliRegular.FLT37.Eichler

end
