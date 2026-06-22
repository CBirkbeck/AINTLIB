import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.DiscreteLogIndexCollapse
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PSaturation
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent

/-!
# Washington Corollary 8.15 and Lemma 9.8 for `p = 37`: the saturation/generation core

This file builds the **reusable saturation/generation core** of Washington
Corollary 8.15 for the Case-II descent of Fermat's Last Theorem at `p = 37`, and
isolates the two named structural Props of `CaseIIAssumptionII.lean`:

* `Cor815SingleIndexExpansion37` (Corollary 8.15) is **discharged** down to its
  *precise* remaining content (`SinnottIndexFormula 37` + the descent-unit data
  `Cor815RealDescentData37`), through the proven saturation/generation core below;
* `Lemma98LocalPower37` (Lemma 9.8) is *not* advanced here — it is a residue-level
  Kummer congruence on the cyclotomic numbers, with no cyclotomic-unit-index
  reduction, so it is consumed directly as a hypothesis (no re-wrapping).

It imports only — it does not modify any existing file.

## The Corollary-8.15 single-index expansion: structure of the argument

The descent unit `ε₁/ε₂` (Washington's `η_a/η_b`, arising from
`caseII_descent_equation`) is a **real** unit lying in the real cyclotomic-unit
group `C⁺ = ⟨family⟩ ⊔ torsion ⊆ (𝓞 K⁺)ˣ`.  Corollary 8.15 expands it over the
real cyclotomic units `Eᵢ` (even `i ∈ [2, 34]`), and the regular indices drop out
(Bernoulli table `flt37_bernoulli_table`), leaving the single irregular index
`i = 32`:

  `ε₁/ε₂ = E₃₂^d · α^{37}`.

The **key reusable structural core** (proven here) is the
`E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}` reduction:

* `[E⁺ : C⁺] = h⁺` (Sinnott, `SinnottIndexFormula`) is coprime to `37`
  (Vandiver, `Sinnott.flt37_not_dvd_hPlus`), so `C⁺` is **`37`-saturated** in
  `E⁺` — this is `mem_of_pow_mem_of_index_coprime` / the proven
  `isPthPower_iff_isPthPower_of_sinnott`;
* torsion of `(𝓞 K⁺)ˣ` is `{±1}` and `-1 = (-1)^{37}`, so torsion is killed
  modulo `37`-th powers (`caseIICor815_torsion_le_pow37`);
* the K⁺-side single-index expansion lifts to the K-side via `Units.map` of
  `algebraMap (𝓞 K⁺) (𝓞 K)`, using the proven
  `algebraMap pollaczekUnitPlusKplus = pollaczekUnitPlus`
  (`caseIICor815_algebraMap_W32`).

## What is built here (real, axiom-clean Lean)

* `caseIICor815_neg_one_isPow37` / `caseIICor815_torsion_le_pow37` — torsion of
  `(𝓞 K⁺)ˣ` is contained in the `37`-th powers (`-1 = (-1)^{37}`).

* `caseIICor815_saturation` — the **saturation step**: under
  `SinnottIndexFormula 37` and the *proven* `¬ 37 ∣ h⁺`, a real unit lying in
  `C⁺ = ⟨family⟩ ⊔ torsion` that is a `37`-th power in `(𝓞 K⁺)ˣ` is a `37`-th
  power **inside `C⁺`**.  (Direct specialisation of the proven
  `isPthPower_iff_isPthPower_of_sinnott`.)

* `caseIICor815_index_coprime` / `caseIICor815_saturation_of_index_coprime` — the
  isolated combinatorial heart: `[E⁺ : C⁺]` is coprime to `37` (from
  `SinnottIndexFormula 37` + the *proven* `¬ 37 ∣ h⁺`), and a real unit in `C⁺`
  that is a `37`-th power in `(𝓞 K⁺)ˣ` is one inside `C⁺` — depending *only* on
  `caseIICPlus37.index.Coprime 37` (the Bézout `mem_of_pow_mem_of_index_coprime`).

* `Cor815EigenCollapseAt` — the **per-unit** eigenspace predicate: `w`'s
  `37`-residue is an `E₃₂`-monomial (`w · (W₃₂^d)⁻¹` is a `37`-th power in
  `(𝓞 K⁺)ˣ`).  Asserted only for the descent unit (not for arbitrary `w ∈ C⁺`,
  which is false).

* `caseIICor815_singleIndexExpansion_of_eigenCollapse` — the **K⁺-side single-index
  collapse**: a real unit `w ∈ C⁺` with `Cor815EigenCollapseAt w` satisfies
  `w = W₃₂^d · γ^{37}` for `γ ∈ C⁺` — the step where the *proven* saturation is
  load-bearing (turning a global `37`-th power into one inside `C⁺`).

* `caseIICor815_algebraMap_singleIndexExpansion` /
  `caseIICor815_realUnit_algebraMap_singleIndexExpansion` — lifting the K⁺-side
  expansion to the K-side: `algebraMap w = E₃₂^d · α^{37}` in `(𝓞 K)ˣ` (with
  `E₃₂ = pollaczekUnitPlus 37 K 32`), the exact shape consumed by
  `caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`.

* `Cor815RealDescentData37` — the *precise* remaining content of
  `Cor815SingleIndexExpansion37` named as a `def … : Prop` (not an axiom): the
  descent-unit data giving `ε₁/ε₂` as the K-image of a real unit `w ∈ C⁺` with
  `Cor815EigenCollapseAt w`.
  `caseIICor815_singleIndexExpansion_of_realDescentData` discharges
  `Cor815SingleIndexExpansion37` from it, *given* `SinnottIndexFormula 37`,
  through the proven core above.

* `caseIICor815_assumptionII_of_reduced_inputs` — composes the §5 discharge of
  Corollary 8.15 with the proven `caseIIThm95_assumptionII_of_corollary815_lemma98`
  to reduce **Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) to
  `SinnottIndexFormula 37` + `Cor815RealDescentData37` + `Lemma98LocalPower37`
  (the last consumed directly — Washington Lemma 9.8's Kummer congruence
  `η_a/η_b ≡ (ρ_b/ρ_a)^{37} (mod 𝔩)` is not advanced here).

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM 83:
  Corollary 8.15 (p. 153), Proposition 8.18 / Corollary 8.19 (p. 158),
  Lemma 9.8 (p. 180), Lemma 9.9 (pp. 180–181), §8.2 (Theorem 8.2, Sinnott).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 0. Notation

Throughout, `K = CyclotomicField 37 ℚ` and `K⁺ = maximalRealSubfield K`.  We write
`C⁺` for the real cyclotomic-unit subgroup `⟨family⟩ ⊔ torsion` of `(𝓞 K⁺)ˣ` (the
group whose index in `(𝓞 K⁺)ˣ` is `[E⁺ : C⁺] = h⁺` by Sinnott). -/

/-- The real cyclotomic-unit subgroup `C⁺ = ⟨cyclotomicUnitFamilyKplus⟩ ⊔ torsion`
of `(𝓞 K⁺)ˣ`, the group appearing in Sinnott's index formula `[E⁺ : C⁺] = h⁺`. -/
def caseIICPlus37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    Subgroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ :=
  Subgroup.closure
      (Set.range (FLT37.Sinnott.cyclotomicUnitFamilyKplusFinRank 37
        (CyclotomicField 37 ℚ) (by decide) (by decide))) ⊔
    NumberField.Units.torsion (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))

/-! ## 1. Torsion is killed modulo `37`-th powers

The torsion subgroup of `(𝓞 K⁺)ˣ` for the totally real field `K⁺` is `{±1}`
(`maximalRealSubfield_torsion_eq_one_or_neg_one`).  Since `1 = 1^{37}` and
`-1 = (-1)^{37}` (37 odd), every torsion unit is a `37`-th power.  This is what
lets the torsion factor drop out of the Corollary-8.15 expansion modulo `37`-th
powers, leaving only the cyclotomic-unit (family) part. -/

/-- **`-1` is a `37`-th power in `(𝓞 K⁺)ˣ`.**  `(-1)^{37} = -1` since `37` is odd. -/
theorem caseIICor815_neg_one_isPow37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      (-1 : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) = v ^ 37 :=
  ⟨-1, by rw [show (37 : ℕ) = 2 * 18 + 1 from rfl, pow_add, pow_mul, neg_one_sq, one_pow,
    pow_one, one_mul]⟩

/-- **Torsion of `(𝓞 K⁺)ˣ` is contained in the `37`-th powers.**  Every torsion
unit is `±1` (`maximalRealSubfield_torsion_eq_one_or_neg_one`), and both `1` and
`-1` are `37`-th powers.  This is the torsion-killing input of Washington
Corollary 8.15: modulo `37`-th powers, the cyclotomic-unit group `C⁺` is
generated by the family `Eᵢ` alone. -/
theorem caseIICor815_torsion_le_pow37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (t : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (ht : t ∈ NumberField.Units.torsion
      (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))) :
    ∃ v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ, t = v ^ 37 := by
  rcases BernoulliRegular.maximalRealSubfield_torsion_eq_one_or_neg_one
      (K := CyclotomicField 37 ℚ) ⟨t, ht⟩ with h_one | h_neg
  · exact ⟨1, by rw [(by simpa using h_one : t = 1), one_pow]⟩
  · have ht_neg : t = -1 := by simpa using h_neg
    obtain ⟨v, hv⟩ := caseIICor815_neg_one_isPow37
    exact ⟨v, ht_neg.trans hv⟩

/-! ## 2. The saturation step: `C⁺` is `37`-saturated in `(𝓞 K⁺)ˣ`

Sinnott's index formula gives `[(𝓞 K⁺)ˣ : C⁺] = h⁺` (up to the `2`-power factor
recording the squared cyclotomic family), and Vandiver's conjecture for `37`
(`Sinnott.flt37_not_dvd_hPlus`, proven) gives `¬ 37 ∣ h⁺`.  Hence the index is
coprime to `37`, so `C⁺` is **`37`-saturated** in `(𝓞 K⁺)ˣ`: an element of `C⁺`
that is a `37`-th power in `(𝓞 K⁺)ˣ` is already a `37`-th power *inside* `C⁺`.

This is the heart of the `E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}` isomorphism (Corollary
8.15).  It is a direct specialisation of the proven
`isPthPower_iff_isPthPower_of_sinnott` to `p = 37`, with `¬ 37 ∣ h⁺` supplied by
the proven `flt37_not_dvd_hPlus`. -/

/-- **`C⁺` is `37`-saturated in `(𝓞 K⁺)ˣ`** (proven, axiom-clean *given*
`SinnottIndexFormula 37`).

Under Sinnott's index formula (the named analytic input `SinnottIndexFormula 37`)
and the *proven* Vandiver fact `¬ 37 ∣ h⁺` (`Sinnott.flt37_not_dvd_hPlus`), a real
unit `w ∈ C⁺ = ⟨family⟩ ⊔ torsion` that is a `37`-th power in `(𝓞 K⁺)ˣ` is a
`37`-th power **inside `C⁺`**: `∃ γ ∈ C⁺, γ^{37} = w`.

This is the `37`-saturation half of the Corollary-8.15 isomorphism
`E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}`, banked from the proven
`isPthPower_iff_isPthPower_of_sinnott`. -/
theorem caseIICor815_saturation
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide))
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37)
    (h_pow : ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      β ^ 37 = w) :
    ∃ γ ∈ caseIICPlus37, γ ^ 37 = w := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact FLT37.Sinnott.isPthPower_iff_isPthPower_of_sinnott 37 (CyclotomicField 37 ℚ)
    (by decide) (by decide) h_sinnott
    (BernoulliRegular.FLT37.Sinnott.flt37_not_dvd_hPlus) hw h_pow

/-- **`[E⁺ : C⁺]` is coprime to `37`** (proven, axiom-clean *given*
`SinnottIndexFormula 37`).

Sinnott's index formula gives `caseIICPlus37.index = 2^{17} · h⁺`; the `2`-power
factor is coprime to the odd prime `37`, and `h⁺` is coprime to `37` by the
*proven* Vandiver fact `¬ 37 ∣ h⁺` (`Sinnott.flt37_not_dvd_hPlus`).  Hence the
index `[E⁺ : C⁺]` is coprime to `37` — the precise combinatorial fact that makes
`C⁺` `37`-saturated in `(𝓞 K⁺)ˣ`.  This isolates the *only* dependency of the
saturation step on the analytic index formula. -/
theorem caseIICor815_index_coprime
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide)) :
    (caseIICPlus37.index).Coprime 37 := by
  -- `caseIICPlus37` is definitionally the Sinnott subgroup, so its index is `2^17 · h⁺`.
  have h_index : caseIICPlus37.index = 2 ^ ((37 - 3) / 2) * hPlus (CyclotomicField 37 ℚ) :=
    h_sinnott
  rw [h_index]
  -- `Coprime 37 (2^17 · h⁺)` from `Coprime 37 (2^17)` and `Coprime 37 h⁺`, then `.symm`.
  refine (Nat.Coprime.mul_right ?_ ?_).symm
  · -- `Coprime 37 (2^17)` ← `Coprime 37 2`.
    exact (((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)).pow_right _)
  · -- `Coprime 37 h⁺` ← `¬ 37 ∣ h⁺` (Vandiver).
    exact (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr
      BernoulliRegular.FLT37.Sinnott.flt37_not_dvd_hPlus

/-- **`C⁺` is `37`-saturated in `(𝓞 K⁺)ˣ`, from index-coprimality** (proven,
axiom-clean).

The *combinatorial* heart of the saturation, depending only on
`¬ 37 ∣ [E⁺ : C⁺]` (`caseIICPlus37.index.Coprime 37`): a real unit `w ∈ C⁺` that
is a `37`-th power in `(𝓞 K⁺)ˣ` is a `37`-th power **inside `C⁺`**.

This is the direct Bézout `37`-saturation lemma
`mem_of_pow_mem_of_index_coprime` specialised to `H = caseIICPlus37`.  It is
strictly more reusable than `caseIICor815_saturation`: any route to
`caseIICPlus37.index.Coprime 37` (e.g. a direct class-number computation) feeds
it, not only the analytic index formula. -/
theorem caseIICor815_saturation_of_index_coprime
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_coprime : (caseIICPlus37.index).Coprime 37)
    (h_index_ne : caseIICPlus37.index ≠ 0)
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37)
    (h_pow : ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      β ^ 37 = w) :
    ∃ γ ∈ caseIICPlus37, γ ^ 37 = w := by
  obtain ⟨β, hβ⟩ := h_pow
  refine ⟨β, ?_, hβ⟩
  exact FLT37.Sinnott.mem_of_pow_mem_of_index_coprime (by decide) h_index_ne h_coprime
    (hβ ▸ hw)

/-- **Corollary 8.15 isomorphism `E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}`, membership form**
(proven, axiom-clean *given* `SinnottIndexFormula 37`).

For a real unit `w ∈ C⁺`: `w` is a `37`-th power in `(𝓞 K⁺)ˣ` **iff** it is a
`37`-th power inside `C⁺`.  The forward direction is the saturation
(`caseIICor815_saturation`, banking `¬ 37 ∣ h⁺`); the reverse is trivial (a
`37`-th power inside `C⁺` is a `37`-th power in the ambient group).

This is the literal content of Washington Corollary 8.15: the inclusion
`C⁺ ↪ (𝓞 K⁺)ˣ` induces an *injection on `37`-th-power quotients*, i.e.
`C⁺/(C⁺)^{37} ↪ E⁺/(E⁺)^{37}`, so `C⁺/(C⁺)^{37}` (generated by the real cyclotomic
units `Eᵢ`) computes `E⁺/(E⁺)^{37}` on its image — the structural reduction that
underlies the single-index expansion of the descent unit. -/
theorem caseIICor815_isPow_iff_isPow_in_CPlus
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide))
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37) :
    (∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ, β ^ 37 = w) ↔
      (∃ γ ∈ caseIICPlus37, γ ^ 37 = w) := by
  constructor
  · intro h_pow
    exact caseIICor815_saturation h_sinnott w hw h_pow
  · rintro ⟨γ, _, hγ⟩
    exact ⟨γ, hγ⟩

/-! ## 3. Lifting the K⁺-side single-index expansion to the K-side

The K⁺-side preimage of `E₃₂ = pollaczekUnitPlus 37 K 32` is
`W₃₂ = pollaczekUnitPlusKplus 37 K 32`, and the proven
`algebraMapPollaczekUnitPlusKplus_eq` says `algebraMap W₃₂ = E₃₂` (on underlying
elements).  Lifting this to the unit level (`Units.map`), a K⁺-side single-index
expansion `w = W₃₂^d · γ^{37}` pushes through the monoid homomorphism
`Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom` to the K-side expansion
`algebraMap w = E₃₂^d · α^{37}` — the exact shape consumed by
`caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`. -/

/-- `W₃₂ : (𝓞 K⁺)ˣ` — the K⁺-side preimage of `E₃₂ = pollaczekUnitPlus 37 K 32`,
the explicit cyclotomic-family product `pollaczekUnitPlusKplus 37 K 32`. -/
def caseIICor815_W32
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ :=
  FLT37.Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32 (by decide) (by decide)

/-- `W₃₂ ∈ C⁺` — the K⁺-side preimage of `E₃₂` lies in the cyclotomic-unit group
(it is a product of family generators). -/
theorem caseIICor815_W32_mem
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    caseIICor815_W32 ∈ caseIICPlus37 :=
  FLT37.Sinnott.pollaczekUnitPlusKplus_mem 37 (CyclotomicField 37 ℚ) 32 (by decide) (by decide)

/-- **`Units.map (algebraMap) W₃₂ = E₃₂`** (unit level), from the proven
underlying-element equation `algebraMapPollaczekUnitPlusKplus_eq` via `Units.ext`. -/
theorem caseIICor815_algebraMap_W32
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom caseIICor815_W32 =
      FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 := by
  apply Units.ext
  -- Underlying elements: algebraMap (W₃₂ : 𝓞 K⁺) = (pollaczekUnitPlus : 𝓞 K).
  exact FLT37.Sinnott.algebraMapPollaczekUnitPlusKplus_eq 37 (CyclotomicField 37 ℚ) 32
    (by decide) (by decide)

/-- **The K-side single-index expansion from the K⁺-side expansion** (proven,
axiom-clean).

Given a K⁺-side single-index expansion `w = W₃₂^{d} · γ^{37}` (the eigenspace
output of Corollary 8.15: only the irregular index `32` survives), the K-side
image under `algebraMap` is `algebraMap w = E₃₂^{d} · α^{37}` with
`E₃₂ = pollaczekUnitPlus 37 K 32` and `α = Units.map(algebraMap) γ`.

This pushes the K⁺-side expansion through the monoid homomorphism
`Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom`, using
`caseIICor815_algebraMap_W32`.  The K-side shape produced here is *exactly* the
hypothesis of `caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`. -/
theorem caseIICor815_algebraMap_singleIndexExpansion
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w γ : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (d : ℕ)
    (h_expand : w = caseIICor815_W32 ^ d * γ ^ 37) :
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w =
      FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ^ d *
        (Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom γ) ^ 37 := by
  rw [h_expand, map_mul, map_pow, map_pow, caseIICor815_algebraMap_W32]

/-! ## 4. The single-index collapse from the eigenspace output

Corollary 8.15's eigenspace argument (Galois `Δ`-action on `C⁺/(C⁺)^{37}` +
Bernoulli table `flt37_bernoulli_table`: the regular even indices `i ≠ 32` are
trivial because `37 ∤ Bᵢ`) says the `37`-residue of the *descent* unit `w` is an
`E₃₂`-monomial — equivalently, for some `d`, `w · (W₃₂^{d})⁻¹` is a **global**
`37`-th power in `(𝓞 K⁺)ˣ`.  We name this eigenspace output as the **per-unit**
predicate `Cor815EigenCollapseAt w` (the genuine remaining infrastructure: there is
no Galois `Δ`-action on `realCyclotomicUnitPlus` / `cyclotomicUnitFamilyKplus` in
the repo yet, and it is *not* a property of arbitrary `w ∈ C⁺`).  Combined with the
**proven** saturation (`caseIICor815_saturation`, banking `¬ 37 ∣ h⁺`), it yields
the explicit K⁺-side single-index expansion
`w = W₃₂^{d} · γ^{37}` with `γ ∈ C⁺`, and via the **proven**
`caseIICor815_algebraMap_singleIndexExpansion` the K-side
`algebraMap w = E₃₂^{d} · α^{37}`. -/

/-- **The Corollary-8.15 eigenspace output, as a per-unit predicate.**
`Cor815EigenCollapseAt w` says the `37`-residue of the real unit `w` is an
`E₃₂`-monomial: for some exponent `d`, the corrected unit `w · (W₃₂^{d})⁻¹` is a
**global** `37`-th power in `(𝓞 K⁺)ˣ`.

This is the content of Washington Corollary 8.15 / Lemma 9.9 restricting the
`37`-residue of the *descent unit* to the single irregular eigenspace `i = 32`
(the Galois `Δ`-action on the real cyclotomic units + the half-range Vandermonde
collapse `caseIIThm95_coeff_collapse_even` + the Bernoulli table killing regular
indices).

It is a **per-unit** predicate — it is *not* asserted for every `w ∈ C⁺` (that
would be false: a regular cyclotomic unit `E₂` is not an `E₃₂`-monomial modulo
`37`-th powers).  It holds for the descent unit because of its mod-`𝔩` residue
equations (Lemma 9.8 over all conjugates); it is supplied for that specific unit
by the descent-unit provenance `Cor815RealDescentData37`. -/
def Cor815EigenCollapseAt
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) : Prop :=
  ∃ (d : ℕ) (β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
    w * (caseIICor815_W32 ^ d)⁻¹ = β ^ 37

/-- **The K⁺-side single-index expansion from the (per-unit) eigenspace output and
saturation** (proven, axiom-clean *given* `SinnottIndexFormula 37`).

For `w ∈ C⁺` whose `37`-residue is an `E₃₂`-monomial (`Cor815EigenCollapseAt w`:
`w · (W₃₂^{d})⁻¹` is a `37`-th power in `(𝓞 K⁺)ˣ`), since `w, W₃₂ ∈ C⁺` the
corrected unit lies in `C⁺`, so the *proven* saturation `caseIICor815_saturation`
upgrades it to a `37`-th power **inside `C⁺`**: `w · (W₃₂^{d})⁻¹ = γ^{37}` with
`γ ∈ C⁺`.  Rearranging, `w = W₃₂^{d} · γ^{37}`.

This is the step where the *proven* `E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}` saturation
(banking `¬ 37 ∣ h⁺`) is load-bearing: it turns "global `37`-th power" into
"`37`-th power inside `C⁺`", giving the explicit `C⁺`-coefficient `γ`. -/
theorem caseIICor815_singleIndexExpansion_of_eigenCollapse
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide))
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37)
    (h_eigen : Cor815EigenCollapseAt w) :
    ∃ (d : ℕ) (γ : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
      w = caseIICor815_W32 ^ d * γ ^ 37 := by
  obtain ⟨d, β, hβ⟩ := h_eigen
  -- `w · (W₃₂^d)⁻¹ ∈ C⁺` (subgroup-closed: w ∈ C⁺, W₃₂ ∈ C⁺).
  have hmem : w * (caseIICor815_W32 ^ d)⁻¹ ∈ caseIICPlus37 :=
    caseIICPlus37.mul_mem hw
      (caseIICPlus37.inv_mem (caseIICPlus37.pow_mem caseIICor815_W32_mem d))
  -- It is a 37-th power in `(𝓞 K⁺)ˣ` (hβ), hence — by saturation — inside C⁺.
  obtain ⟨γ, _hγ_mem, hγ⟩ := caseIICor815_saturation h_sinnott
    (w * (caseIICor815_W32 ^ d)⁻¹) hmem ⟨β, hβ.symm⟩
  -- `w = W₃₂^d · γ^37` from `w · (W₃₂^d)⁻¹ = γ^37`.
  refine ⟨d, γ, ?_⟩
  rw [hγ, mul_comm w, mul_inv_cancel_left]

/-- **The K-side single-index expansion for a real cyclotomic unit** (proven,
axiom-clean *given* `SinnottIndexFormula 37` and the per-unit eigenspace output).

For a real cyclotomic unit `w ∈ C⁺` whose `37`-residue is an `E₃₂`-monomial
(`Cor815EigenCollapseAt w`), its K-side image `algebraMap w` is a single
`E₃₂`-monomial modulo `37`-th powers: `algebraMap w = E₃₂^{d} · α^{37}` in
`(𝓞 K)ˣ`.  This is the full Corollary-8.15 single-index expansion for the descent
unit, composed from the *proven*
`caseIICor815_singleIndexExpansion_of_eigenCollapse` and
`caseIICor815_algebraMap_singleIndexExpansion`. -/
theorem caseIICor815_realUnit_algebraMap_singleIndexExpansion
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide))
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37)
    (h_eigen : Cor815EigenCollapseAt w) :
    ∃ (d : ℕ) (α : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w =
        FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ^ d * α ^ 37 := by
  obtain ⟨d, γ, hexp⟩ :=
    caseIICor815_singleIndexExpansion_of_eigenCollapse h_sinnott w hw h_eigen
  exact ⟨d, _, caseIICor815_algebraMap_singleIndexExpansion w γ d hexp⟩

/-! ## 5. Discharging `Cor815SingleIndexExpansion37`

The Corollary-8.15 Prop `Cor815SingleIndexExpansion37` quantifies over the
Case-II descent instances and claims `ε₁/ε₂ = E₃₂^{d} · α^{37}`.  By the proven
core §1–§4, this reduces to a single named input — the descent-unit data
`Cor815RealDescentData37`, which provides, for the *specific* descent unit `ε₁/ε₂`:

* it is the K-image (`Units.map (algebraMap (𝓞 K⁺) (𝓞 K))`) of a real cyclotomic
  unit `w ∈ C⁺` (realness/membership: `η_a/η_b` is real and a cyclotomic unit,
  from the σ-stable `caseII_descent_equation`); and
* `w`'s `37`-residue is an `E₃₂`-monomial (`Cor815EigenCollapseAt w`: the
  eigenspace collapse, which holds for the descent unit because of its mod-`𝔩`
  residue equations — Lemma 9.8 over all conjugates — *not* for arbitrary
  `w ∈ C⁺`).

Given this plus the named `SinnottIndexFormula 37`, the proven
`caseIICor815_realUnit_algebraMap_singleIndexExpansion` produces the K-side
expansion of `Units.map w = ε₁/ε₂`, i.e. `Cor815SingleIndexExpansion37`. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Descent-unit data for Corollary 8.15** (a `def … : Prop`, **not** an axiom).

For every Case-II descent instance, the quotient unit `ε₁/ε₂` is the K-image of a
real cyclotomic unit `w ∈ C⁺` whose `37`-residue is an `E₃₂`-monomial: there is
`w ∈ caseIICPlus37` with `Cor815EigenCollapseAt w` and
`Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom w = ε₁/ε₂`.

This bundles the two descent-unit-specific facts of Washington Corollary 8.15
(realness + cyclotomic membership of `η_a/η_b`, and the `E₃₂`-monomial collapse of
its residue) for the *specific* descent unit.  Both are supplied by the σ-stable
`caseII_descent_equation` construction together with the mod-`𝔩` residue equations
(Lemma 9.8 over all conjugates) and the half-range Vandermonde collapse — they are
*not* derivable from the bare `Cor815SingleIndexExpansion37` equation shape, and
the eigenspace collapse is asserted only here, for the descent unit, never for
arbitrary `w ∈ C⁺` (which would be false). -/
def Cor815RealDescentData37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ w ∈ caseIICPlus37, Cor815EigenCollapseAt w ∧
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂

open FLT37.LehmerVandiver.CaseII in
/-- **Discharging Corollary 8.15 (`Cor815SingleIndexExpansion37`)** (proven,
axiom-clean *given* `SinnottIndexFormula 37` and `Cor815RealDescentData37`).

The descent-unit data (`h_prov`) provides, for each instance, a real cyclotomic
unit `w ∈ C⁺` with `Units.map w = ε₁/ε₂` and `Cor815EigenCollapseAt w`.  Feeding
these to the proven single-index core
(`caseIICor815_realUnit_algebraMap_singleIndexExpansion`, which uses the *proven*
`E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}` saturation banking `¬ 37 ∣ h⁺`) yields the
Corollary-8.15 single-index expansion `ε₁/ε₂ = E₃₂^{d} · α^{37}` for every Case-II
descent instance — i.e. `Cor815SingleIndexExpansion37`.

Everything between the named input and the conclusion — the saturation, the
torsion-killing, the explicit expansion, and the K-side lift — is proven in §1–§4
of this file. -/
theorem caseIICor815_singleIndexExpansion_of_realDescentData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide))
    (h_prov : Cor815RealDescentData37) :
    Cor815SingleIndexExpansion37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨w, hw_mem, hw_eigen, hw_eq⟩ := h_prov hV hSO D hx hy hz heq
  obtain ⟨d, α, hα⟩ :=
    caseIICor815_realUnit_algebraMap_singleIndexExpansion h_sinnott w hw_mem hw_eigen
  exact ⟨d, α, by rw [← hw_eq, hα]⟩

/-! ## 6. Assumption II from the reduced inputs

Composing the §5 discharge of Corollary 8.15 with the proven
`caseIIThm95_assumptionII_of_corollary815_lemma98` of `CaseIIAssumptionII.lean`
reduces **Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) — and
hence the entire Theorem-9.5 Case-II descent (modulo the proven adjacent-generator
producer) — to the *three* precisely-named inputs:

* `SinnottIndexFormula 37` — Sinnott's analytic index identity `[E⁺ : C⁺] = h⁺`
  (the regulator-of-cyclotomic-units determinant; `def … : Prop` already in the
  repo);
* `Cor815RealDescentData37` — for the descent unit `ε₁/ε₂`: it is the K-image of a
  real cyclotomic unit `w ∈ C⁺` whose `37`-residue is an `E₃₂`-monomial
  (Corollary 8.15 realness/membership + the descent-unit eigenspace collapse, from
  the σ-stable descent-equation construction and the mod-`𝔩` residue equations);
* `Lemma98LocalPower37` — Washington Lemma 9.8's mod-`𝔩` Kummer congruence
  `η_a/η_b ≡ (ρ_b/ρ_a)^{37} (mod 𝔩)`, *consumed directly* (this file makes no
  progress on Lemma 9.8: it is a residue-level computation on the cyclotomic
  numbers `η_a` / their mod-`𝔩` residues `ρ_a`, specific to the descent
  construction, with no cyclotomic-unit-index reduction available — so it is not
  re-wrapped).

The Corollary-8.15 contribution of this file — the `E⁺/(E⁺)^{37} ≅ C⁺/(C⁺)^{37}`
saturation core (the key reusable piece, banking the proven `¬ 37 ∣ h⁺`), the
torsion-killing, the explicit single-index expansion, the K-side lift — together
with the index/Vandermonde collapse of `CaseIIAssumptionII.lean` are *proven*. -/
theorem caseIICor815_assumptionII_of_reduced_inputs
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_sinnott : FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide))
    (h_prov : Cor815RealDescentData37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIThm95_assumptionII_of_corollary815_lemma98
    (caseIICor815_singleIndexExpansion_of_realDescentData h_sinnott h_prov)
    h_localPow

end BernoulliRegular.FLT37.Eichler

end
