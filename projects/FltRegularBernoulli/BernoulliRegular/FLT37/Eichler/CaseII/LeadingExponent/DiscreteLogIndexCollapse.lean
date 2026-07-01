import BernoulliRegular.FLT37.Eichler.Reduction.VandermondeCollapseAndLemma99Bridge

/-!
# Washington Theorem 9.5 Case-II descent for `p = 37`: the discrete-log index step

This file builds the **operative core** of the Washington Lemma-9.9 bridge for
Fermat's Last Theorem at `p = 37` (Case II): the *discrete-log index*
`ind₃₂ E₃₂ ≢ 0 (mod 37)` of the irregular real cyclotomic (Pollaczek) unit
`E₃₂ = pollaczekUnitPlus 37 K 32`, extracted from the already-proven mod-`𝔩`
non-`37`-th-power certificate (`caseIIThm95_engine_runs`).

It imports only — it does not modify any existing file.

## What is built here (real, axiom-clean Lean)

* `cyclicInd` / `residueUnitInd` — the **discrete logarithm** `ind` on a finite
  cyclic group, specialised to the residue unit group `(𝓞 K / 𝔩)ˣ` (cyclic of
  order `ℓ - 1 = 148 = 4·37`).  It is the honest discrete log via mathlib's
  `zmodCyclicMulEquiv`, valued in `ZMod (Nat.card (𝓞 K / 𝔩)ˣ)`.  Additivity:
  `cyclicInd_mul` / `cyclicInd_pow`, `residueUnitInd_mul` / `residueUnitInd_pow`.

* `isPow_iff_dvd_cyclicInd` — the **discrete-log criterion** for a cyclic group:
  a unit `u` is a `p`-th power iff `(p) ∣ ind u` (ring divisibility in
  `ZMod (Nat.card G)`), i.e. `(∃ v, u = vᵖ) ↔ p ∣ ind u`.

* `isPthPowerModPrime_iff_dvd_residueUnitInd` — the bridge tying the **proven**
  residue test `IsPthPowerModPrime` to the discrete log: for a unit
  `u : (𝓞 K)ˣ`, `IsPthPowerModPrime 37 𝔩 (u : 𝓞 K)` iff `(37) ∣ ind₃₂ u`.

* `residueInd37` + `isPthPowerModPrime_iff_residueInd37_eq_zero` — the index
  **reduced mod `37`**, valued in the field `𝔽₃₇`, and the criterion in clean
  field form: `IsPthPowerModPrime 37 𝔩 u ↔ ind₃₇ u = 0`.

* `caseIIThm95_ind_E32_ne_zero` / `caseIIThm95_residueInd37_E32_ne_zero` —
  **the operative bottleneck**, proven: the discrete-log index of
  `E₃₂ = pollaczekUnitPlus 37 K 32` in `(𝓞 K / 𝔩)ˣ` satisfies
  `(37 : ZMod 148) ∤ ind₃₂ E₃₂`, equivalently `ind₃₇ E₃₂ ≠ 0` in `𝔽₃₇`, i.e.
  `ind₃₂ ≢ 0 (mod 37)`.  This is `caseIIThm95_engine_runs` (`Q₃₂⁴ ≢ 1`) re-read
  through the criterion (`isPthPowerModPrime_iff_pow_card_div_p_eq_one` is the
  underlying bridge, here packaged via `isPow_iff_dvd_cyclicInd`).

* `caseIIThm95_descentUnit_isPow_of_singleIndexExpansion` — the **single-index
  Lemma-9.9 collapse**: given the Corollary-8.15 single-index expansion
  `δ = E₃₂^{d}·α^{37}` and `IsPthPowerModPrime 37 𝔩 δ` (Lemma 9.8), the index
  arithmetic above forces `37 ∣ d`, hence `δ` is a global `37`-th power.

* `caseIIThm95_assumptionII_of_corollary815_lemma98` — discharges **Assumption
  II** (`WashingtonCaseIIExactQuotientUnitPower37Source`), and
  `caseIIThm95_lemma99Bridge_of_corollary815_lemma98` the named bridge
  `CaseIIThm95Lemma99Bridge`, from the two explicit structural hypotheses
  `Cor815SingleIndexExpansion37` and `Lemma98LocalPower37` (the genuine remaining
  content — Corollary 8.15's `E⁺/(E⁺)³⁷` single-index expansion and Lemma 9.8 —
  named as `def … : Prop`, not axioms).  Everything between them and Assumption
  II — the entire index/Vandermonde collapse — is proven here.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Theorem 9.5, Lemmas 9.6–9.9 (pp. 176–181), §8.3 (Prop 8.18, Cor 8.19),
  Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 0. Abstract discrete logarithm on a finite cyclic group

The discrete logarithm `ind` of a finite cyclic group `G` is the inverse of
mathlib's `zmodCyclicMulEquiv : Multiplicative (ZMod (Nat.card G)) ≃* G`.  The
basic fact we need is the **`p`-th-power criterion via the index**: a unit `u` is
a `p`-th power iff `(p : ZMod (Nat.card G)) ∣ ind u`, i.e. the index of `u` is
divisible by `p` (ring divisibility in `ZMod (Nat.card G)`).  This is the precise
content of "the discrete-log index `indᵢ` is divisible by `p`". -/

/-- **The discrete logarithm `ind` on a finite cyclic group `G`.**  Valued in
`ZMod (Nat.card G)`, it is the inverse of mathlib's
`zmodCyclicMulEquiv : Multiplicative (ZMod (Nat.card G)) ≃* G`.  For a generator
`g` corresponding to `1`, `ind (gⁿ) = n`. -/
def cyclicInd {G : Type*} [CommGroup G] [Finite G] (h : IsCyclic G) (u : G) :
    ZMod (Nat.card G) :=
  Multiplicative.toAdd ((zmodCyclicMulEquiv h).symm u)

/-- **`ind` is additive in the group operation.**  `ind (u * v) = ind u + ind v`:
the discrete log is a group homomorphism `(G, *) → (ZMod (Nat.card G), +)` (the
composite of `(zmodCyclicMulEquiv h).symm` and `Multiplicative.toAdd`).  This is
the additivity that turns a multiplicative cyclotomic-unit factorisation
`δ = ∏ᵢ Eᵢ^{dᵢ}` into the *linear* index equation `ind δ = ∑ᵢ dᵢ · ind Eᵢ`. -/
theorem cyclicInd_mul {G : Type*} [CommGroup G] [Finite G] (h : IsCyclic G)
    (u v : G) : cyclicInd h (u * v) = cyclicInd h u + cyclicInd h v := by
  unfold cyclicInd
  rw [map_mul]
  rfl

/-- **`ind` of a power: `ind (uⁿ) = n · ind u`** (`ℕ`-power form).  Combined with
`cyclicInd_mul`, this gives `ind (∏ᵢ Eᵢ^{dᵢ}) = ∑ᵢ dᵢ · ind Eᵢ`, the linear
index relation underlying Washington Lemma 9.9. -/
theorem cyclicInd_pow {G : Type*} [CommGroup G] [Finite G] (h : IsCyclic G)
    (u : G) (n : ℕ) : cyclicInd h (u ^ n) = n * cyclicInd h u := by
  unfold cyclicInd
  rw [map_pow]
  simp only [toAdd_pow, nsmul_eq_mul]

/-- **The discrete-log `p`-th-power criterion.**  In a finite cyclic group `G`, a
unit `u` is a `p`-th power iff `(p : ZMod (Nat.card G)) ∣ ind u` (ring
divisibility in `ZMod (Nat.card G)`).  This is the abstract heart of Washington's
Proposition 8.18: `p ∣ indᵢ Eᵢ` exactly when `Eᵢ` is a `p`-th power. -/
theorem isPow_iff_dvd_cyclicInd {G : Type*} [CommGroup G] [Finite G]
    (h : IsCyclic G) (u : G) (p : ℕ) :
    (∃ v : G, u = v ^ p) ↔ (p : ZMod (Nat.card G)) ∣ cyclicInd h u := by
  unfold cyclicInd
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Multiplicative.toAdd ((zmodCyclicMulEquiv h).symm v), ?_⟩
    rw [map_pow]
    simp only [toAdd_pow, nsmul_eq_mul]
  · rintro ⟨z, hz⟩
    refine ⟨(zmodCyclicMulEquiv h) (Multiplicative.ofAdd z), ?_⟩
    rw [← map_pow]
    have hsymm : (zmodCyclicMulEquiv h).symm u = (Multiplicative.ofAdd z) ^ p := by
      apply Multiplicative.toAdd.injective
      rw [hz]
      simp [toAdd_pow, nsmul_eq_mul, mul_comm]
    rw [← hsymm, MulEquiv.apply_symm_apply]

/-- **Unit `p`-th powers in a field: ring vs unit-group.**  For a field `F`, a
unit `w : Fˣ`, and `0 < p`, the underlying element `(w : F)` is a `p`-th power in
`F` iff `w` is a `p`-th power in the unit group `Fˣ`.  (Any `p`-th root of a
nonzero element is itself nonzero, hence a unit.)  This converts the
ring-level `IsPthPowerModPrime` existential into a unit-group statement to which
the discrete-log criterion applies. -/
theorem field_isPow_unit_iff {F : Type*} [Field F] (w : Fˣ) (p : ℕ) (hp : 0 < p) :
    (∃ y : F, (w : F) = y ^ p) ↔ (∃ v : Fˣ, w = v ^ p) := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hy
      exact w.ne_zero hy
    exact ⟨Units.mk0 y hy0, Units.ext (by push_cast; simpa using hy)⟩
  · rintro ⟨v, hv⟩
    exact ⟨(v : F), by rw [hv]; push_cast; rfl⟩

/-! ## 1. The Lehmer–Vandiver residue prime for `p = 37`, `ℓ = 149`

We instantiate the auxiliary prime `𝔩 = lehmerVandiverPrime 37 149 4 …` over
`ℓ = 149 = 4·37 + 1`.  Its residue field `𝓞 K / 𝔩 ≅ 𝔽₁₄₉` is finite with
`148 = ℓ - 1` units, and its unit group is cyclic.  All instances below are
derived from `NumberField (CyclotomicField 37 ℚ)` and the maximality of `𝔩`. -/

/-- The Lehmer–Vandiver prime `𝔩 ⊂ 𝓞 (ℚ(ζ₃₇))` over `ℓ = 149`, with the worked
Theorem-9.5 certificate parameters `(t, k) = (2, 4)`. -/
def lv149 : Ideal (𝓞 (CyclotomicField 37 ℚ)) :=
  FLT37.lehmerVandiverPrime 37 149 4
    (by decide : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1)

/-- `lv149` is a maximal ideal: it is prime (`lehmerVandiverPrime_isPrime`) and
nonzero (it lies over the rational prime `149`), so in the Dedekind domain
`𝓞 (ℚ(ζ₃₇))` it is maximal. -/
instance lv149_isMaximal : lv149.IsMaximal := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  unfold lv149
  refine Ideal.IsPrime.isMaximal
    (FLT37.lehmerVandiverPrime_isPrime 37 149 4 _ _ _) ?_
  have h := FLT37.lehmerVandiverPrime_natCast_ℓ_mem 37 149 4
    (by decide : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide +revert : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1)
  intro h_zero
  rw [h_zero] at h
  simp at h

/-- The residue field `𝓞 (ℚ(ζ₃₇)) / 𝔩` is finite (`NumberField` + maximality). -/
instance : Finite (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) := inferInstance

/-- The residue field at `lv149` is a field (maximality). -/
noncomputable instance : Field (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) :=
  Ideal.Quotient.field lv149

/-- The residue unit group `(𝓞 (ℚ(ζ₃₇)) / 𝔩)ˣ` is finite. -/
instance : Finite (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ := inferInstance

/-- The residue unit group `(𝓞 (ℚ(ζ₃₇)) / 𝔩)ˣ` is cyclic (finite field). -/
instance : IsCyclic (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ := inferInstance

/-- **The residue field has `149` elements.**  `Nat.card (𝓞 K / 𝔩) = ℓ = 149`,
from the proven `lehmerVandiverPrime_quotient_card` (which identifies the residue
field with `𝔽₁₄₉`).  Stated with `Nat.card`, which is independent of the chosen
`Fintype` instance. -/
theorem lv149_quotient_card : Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) = 149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  letI : Fintype (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) :=
    FLT37.lehmerVandiverPrime_quotientFintype (p := 37) 149 4
      (by decide : (149 : ℕ) = 4 * 37 + 1)
      (by decide : (2 : ℕ).Coprime 149)
      (by decide +revert : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1)
  rw [Nat.card_eq_fintype_card]
  exact FLT37.lehmerVandiverPrime_quotient_card (p := 37) 149 4
    (by decide : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide +revert : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1)

/-- **The residue unit group has `148 = 4·37` elements.**  `Nat.card (𝓞 K / 𝔩)ˣ
= ℓ - 1 = 148`, the cyclic order in which the discrete log `ind` is valued.
Since `148 = 4·37`, the index-`37` subgroup (the `37`-th powers) has order `4`. -/
theorem lv149_unit_card : Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ = 148 := by
  rw [Nat.card_units, lv149_quotient_card]

/-! ## 2. The discrete log `ind` on the residue unit group, and its `p`-th-power
criterion

The discrete log `ind₃₂ : (𝓞 K)ˣ → ZMod 148` sends a global unit `u` to the
discrete log of its residue `Q u ∈ (𝓞 K / 𝔩)ˣ`.  Washington's `indᵢ Eᵢ` (the
index appearing in Lemma 9.9) is exactly `ind₃₂ Eᵢ`. -/

/-- The image of a global unit `u : (𝓞 K)ˣ` in the residue unit group
`(𝓞 K / 𝔩)ˣ` (the functorial `Units.map` of the quotient ring hom). -/
def residueUnit (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ :=
  Units.map (Ideal.Quotient.mk lv149 : 𝓞 (CyclotomicField 37 ℚ) →+* _).toMonoidHom u

/-- `(residueUnit u : 𝓞 K / 𝔩) = Q(u : 𝓞 K)`: the underlying ring element of the
residue unit is the quotient image of `u`. -/
theorem residueUnit_val (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    ((residueUnit u : (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) :
        𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) =
      Ideal.Quotient.mk lv149 (u : 𝓞 (CyclotomicField 37 ℚ)) := rfl

/-- **The discrete-log index `ind₃₂` of a global unit `u`.**  This is the
discrete log of the residue `Q u ∈ (𝓞 K / 𝔩)ˣ` in the cyclic group of order
`148 = 4·37`, valued in `ZMod (Nat.card (𝓞 K / 𝔩)ˣ) = ZMod 148`.  Washington's
`indᵢ Eᵢ` (Proposition 8.18 / Lemma 9.9) is `residueUnitInd Eᵢ`. -/
def residueUnitInd (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) :=
  cyclicInd (inferInstance : IsCyclic (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)
    (residueUnit u)

/-- **`residueUnit` is multiplicative**: `Q(u·v) = Q(u)·Q(v)` in `(𝓞 K / 𝔩)ˣ`. -/
theorem residueUnit_mul (u v : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    residueUnit (u * v) = residueUnit u * residueUnit v := by
  unfold residueUnit; rw [map_mul]

/-- **`residueUnit` of a power**: `Q(uⁿ) = Q(u)ⁿ`. -/
theorem residueUnit_pow (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (n : ℕ) :
    residueUnit (u ^ n) = residueUnit u ^ n := by
  unfold residueUnit; rw [map_pow]

/-- **The discrete-log index `ind₃₂` is additive**:
`ind₃₂ (u·v) = ind₃₂ u + ind₃₂ v`.  This is the additivity that linearises a
cyclotomic-unit factorisation `δ = ∏ᵢ Eᵢ^{dᵢ}` into `ind₃₂ δ = ∑ᵢ dᵢ · ind₃₂ Eᵢ`. -/
theorem residueUnitInd_mul (u v : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    residueUnitInd (u * v) = residueUnitInd u + residueUnitInd v := by
  unfold residueUnitInd; rw [residueUnit_mul, cyclicInd_mul]

/-- **`ind₃₂` of a power**: `ind₃₂ (uⁿ) = n · ind₃₂ u`. -/
theorem residueUnitInd_pow (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (n : ℕ) :
    residueUnitInd (u ^ n) = n * residueUnitInd u := by
  unfold residueUnitInd; rw [residueUnit_pow, cyclicInd_pow]

/-- **The mod-`𝔩` `p`-th-power criterion in discrete-log form.**  For a global
unit `u : (𝓞 K)ˣ` and `0 < p`, the residue test `IsPthPowerModPrime p 𝔩 (u : 𝓞 K)`
holds iff `(p : ZMod 148) ∣ ind₃₂ u`, i.e. the discrete-log index of `u` is
divisible by `p`.

This packages the proven cyclic criterion
(`isPthPowerModPrime_iff_pow_card_div_p_eq_one`, here routed via
`isPow_iff_dvd_cyclicInd`) into the index language of Washington Prop 8.18:
`p ∣ indᵢ x ↔ x` is a `p`-th power mod `𝔩`. -/
theorem isPthPowerModPrime_iff_dvd_residueUnitInd
    (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (p : ℕ) (hp : 0 < p) :
    BernoulliRegular.IsPthPowerModPrime p lv149
        ((u : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ↔
      (p : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) ∣ residueUnitInd u := by
  -- `IsPthPowerModPrime` unfolds to `∃ y, Q(u) = y^p`.
  unfold BernoulliRegular.IsPthPowerModPrime residueUnitInd
  -- Rewrite `Q(u) = (residueUnit u).val` to expose the unit `residueUnit u`.
  rw [← residueUnit_val u]
  -- Ring `p`-th power of a unit element ↔ unit-group `p`-th power.
  rw [field_isPow_unit_iff (residueUnit u) p hp]
  -- Discrete-log criterion for the cyclic unit group.
  exact isPow_iff_dvd_cyclicInd _ (residueUnit u) p

/-! ### The index reduced mod `37`

Because `148 = 4·37`, the natural projection `ZMod 148 → ZMod 37` sends
`(37 : ZMod 148)` to `0`.  Reducing the discrete log mod `37` lands in the
**field** `ZMod 37`, where the `p`-th-power criterion `(37) ∣ ind` becomes the
single equation `ind₃₇ = 0`, and `37 · (anything) = 0` automatically — exactly
the simplification that makes the regular cyclotomic-unit factors drop out and
the Lemma-9.9 collapse a one-variable statement. -/

/-- **Divisibility by `37` in `ZMod 148` ⟺ vanishing of the mod-`37` reduction.**
For `x : ZMod (Nat.card (𝓞 K / 𝔩)ˣ) = ZMod 148`,
`(37 : ZMod 148) ∣ x ↔ (cast x : ZMod 37) = 0`.  The forward direction is
`map_mul`; the reverse uses that `(x.val : ZMod 37) = 0 ↔ 37 ∣ x.val`. -/
theorem dvd37_iff_castHom_eq_zero
    (x : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) :
    (37 : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) ∣ x ↔
      (ZMod.castHom (by rw [lv149_unit_card]; decide :
        (37 : ℕ) ∣ Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) (ZMod 37)) x = 0 := by
  haveI : NeZero (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) := by
    rw [lv149_unit_card]; exact ⟨by decide⟩
  constructor
  · rintro ⟨z, rfl⟩
    rw [map_mul]
    have h37 : (ZMod.castHom (by rw [lv149_unit_card]; decide :
        (37 : ℕ) ∣ Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) (ZMod 37))
        (37 : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) = 0 := by
      rw [show (37 : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) =
          ((37 : ℕ) : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) by push_cast; ring,
        map_natCast]
      decide
    rw [h37, zero_mul]
  · intro h
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨q, hq⟩ := h
    refine ⟨(q : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)), ?_⟩
    have hxv : x = ((x.val : ℕ) :
        ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) :=
      (ZMod.natCast_zmod_val x).symm
    rw [hxv, hq]; push_cast; ring

/-- **The discrete-log index reduced mod `37`, `ind₃₇ : (𝓞 K)ˣ → 𝔽₃₇`.**  The
projection of the discrete log `ind₃₂` to the field `ZMod 37`.  This is the
genuine `indᵢ` of Washington Lemma 9.9 *as an element of `𝔽₃₇`* — the half-range
residue equations of Lemma 9.9 are linear equations over this field. -/
def residueInd37 (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) : ZMod 37 :=
  (ZMod.castHom (by rw [lv149_unit_card]; decide :
    (37 : ℕ) ∣ Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ) (ZMod 37))
    (residueUnitInd u)

/-- **`ind₃₇` is additive**: `ind₃₇ (u·v) = ind₃₇ u + ind₃₇ v` (ring-hom image of
the additive `ind₃₂`). -/
theorem residueInd37_mul (u v : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    residueInd37 (u * v) = residueInd37 u + residueInd37 v := by
  unfold residueInd37; rw [residueUnitInd_mul, map_add]

/-- **`ind₃₇` of a power**: `ind₃₇ (uⁿ) = (n : 𝔽₃₇) · ind₃₇ u`.  In particular the
`p = 37` power has `ind₃₇ (u³⁷) = 0` (since `37 = 0` in `𝔽₃₇`): every global `37`-th
power drops out of the mod-`37` index, which is what lets the regular cyclotomic
factors `Eᵢ^{37·(…)}` vanish from the obstruction. -/
theorem residueInd37_pow (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (n : ℕ) :
    residueInd37 (u ^ n) = (n : ZMod 37) * residueInd37 u := by
  unfold residueInd37; rw [residueUnitInd_pow, map_mul, map_natCast]

/-- **The mod-`𝔩` `37`-th-power criterion in field-index form.**  For a global unit
`u : (𝓞 K)ˣ`, the residue test `IsPthPowerModPrime 37 𝔩 (u : 𝓞 K)` holds iff
`ind₃₇ u = 0` in the field `𝔽₃₇`.  This is the cleanest form of Washington
Proposition 8.18's `p`-th-power criterion: `Eᵢ` is a `37`-th power mod `𝔩` ⟺
`ind₃₇ Eᵢ = 0`. -/
theorem isPthPowerModPrime_iff_residueInd37_eq_zero
    (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
        ((u : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ↔
      residueInd37 u = 0 := by
  rw [isPthPowerModPrime_iff_dvd_residueUnitInd u 37 (by decide)]
  rw [show ((37 : ℕ) : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) =
      (37 : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) by push_cast; ring,
    dvd37_iff_castHom_eq_zero]
  rfl

/-! ## 3. The operative bottleneck: `ind₃₂ E₃₂ ≢ 0 (mod 37)`

This is the single arithmetic input that drives Washington's Lemma 9.9 for `37`.
The proven certificate `caseIIThm95_engine_runs` says `E₃₂ = pollaczekUnitPlus 37 K 32`
is **not** a `37`-th power mod `𝔩` (`Q₃₂⁴ ≢ 1`).  Re-read through the discrete-log
criterion `isPthPowerModPrime_iff_dvd_residueUnitInd`, this says exactly that the
discrete-log index `ind₃₂ E₃₂` is **not** divisible by `37`, i.e.
`ind₃₂ E₃₂ ≢ 0 (mod 37)`. -/

/-- **`ind₃₂ E₃₂ ≢ 0 (mod 37)` — the operative core of Washington Lemma 9.9 for
`p = 37`** (proven, axiom-clean).

The discrete-log index of the irregular real cyclotomic (Pollaczek) unit
`E₃₂ = pollaczekUnitPlus 37 K 32` in the residue unit group `(𝓞 K / 𝔩)ˣ` (cyclic
of order `148 = 4·37`) is **not** divisible by `37`:

  `(37 : ZMod 148) ∤ ind₃₂ E₃₂`.

Proof: the proven mod-`𝔩` certificate `caseIIThm95_engine_runs`
(`¬ IsPthPowerModPrime 37 𝔩 E₃₂`, i.e. Washington's `Q₃₂⁴ ≢ 1`) combined with the
discrete-log criterion `isPthPowerModPrime_iff_dvd_residueUnitInd`.  This is the
non-vanishing `indᵢ Eᵢ ≢ 0` of Washington Proposition 8.18 for the irregular
index `i = 32`, the input that makes the Lemma-9.9 collapse force `d₃₂ ≡ 0`. -/
theorem caseIIThm95_ind_E32_ne_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ (37 : ZMod (Nat.card (𝓞 (CyclotomicField 37 ℚ) ⧸ lv149)ˣ)) ∣
      residueUnitInd (FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32) := by
  intro hdvd
  -- Convert back to `IsPthPowerModPrime` via the criterion …
  have hpow : BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) :=
    (isPthPowerModPrime_iff_dvd_residueUnitInd
      (FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32) 37 (by decide)).mpr hdvd
  -- … contradicting the proven non-`37`-th-power certificate.
  exact caseIIThm95_engine_runs hpow

/-- **`ind₃₇ E₃₂ ≠ 0` — the operative core, in field form** (proven, axiom-clean).

The mod-`37` discrete-log index of the irregular Pollaczek unit
`E₃₂ = pollaczekUnitPlus 37 K 32` is **nonzero** in the field `𝔽₃₇`:
`ind₃₇ E₃₂ ≠ 0`.  This is Washington Proposition 8.18's non-vanishing
`indᵢ Eᵢ ≢ 0 (mod p)` for the sole irregular index `i = 32` of `37` — the input
that makes the Lemma-9.9 collapse force the descent exponent `d₃₂ ≡ 0`.

Proof: `caseIIThm95_engine_runs` (`¬ IsPthPowerModPrime 37 𝔩 E₃₂`) through the
field criterion `isPthPowerModPrime_iff_residueInd37_eq_zero`. -/
theorem caseIIThm95_residueInd37_E32_ne_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    residueInd37 (FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32) ≠ 0 := by
  intro h0
  exact caseIIThm95_engine_runs
    ((isPthPowerModPrime_iff_residueInd37_eq_zero
      (FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)).mpr h0)

/-! ## 4. The single-index Lemma-9.9 collapse: reducing Assumption II

Washington Lemma 9.9 closes the Case-II descent by showing the descent-equation
quotient unit `δ = ε₁/ε₂` is a `37`-th power.  For `37`, whose **only** irregular
even index in `[2, 34]` is `32` (the proven Bernoulli table
`Sinnott.flt37_bernoulli_table`), Corollary 8.15 expands `δ` over the real
cyclotomic units `Eᵢ` and the regular factors drop out, leaving a **single
surviving index**: `δ = E₃₂^{d₃₂} · α^{37}`.

Given that single-index expansion, the discharge of Assumption II is *purely the
index arithmetic proven above*:

* `ind₃₇ δ = d₃₂ · ind₃₇ E₃₂` (additivity `residueInd37_mul`/`_pow`, and
  `ind₃₇(α^{37}) = 0` since `37 = 0` in `𝔽₃₇`);
* `δ` is a `37`-th power mod `𝔩` (Lemma 9.8) ⟹ `ind₃₇ δ = 0`
  (`isPthPowerModPrime_iff_residueInd37_eq_zero`);
* with `ind₃₇ E₃₂ ≠ 0` (the operative core) and `𝔽₃₇` a field, `d₃₂ ≡ 0 (mod 37)`;
* hence `E₃₂^{d₃₂}` is a global `37`-th power and so is `δ`.

The two genuinely structural inputs — Corollary 8.15's single-index expansion and
Lemma 9.8's "δ is a `37`-th power mod `𝔩`" — are taken as explicit hypotheses;
everything else (the entire index collapse) is the proven content of this file. -/

/-- **The single-index Lemma-9.9 collapse for `p = 37`** (proven, axiom-clean
*given* its two named structural hypotheses).

Let `δ : (𝓞 K)ˣ` be a unit (Washington's descent unit `ε₁/ε₂`).  Assume:

* `h_expand` (**Corollary 8.15, single-index form**): `δ = E₃₂^{d} · α^{37}` for a
  natural number `d` and a unit `α` — the expansion of `δ` over the real
  cyclotomic units in which only the sole irregular index `32` survives (the
  regular indices drop out by `Sinnott.flt37_bernoulli_table`).

* `h_localPow` (**Lemma 9.8**): `δ` is a `37`-th power modulo `𝔩`
  (`IsPthPowerModPrime 37 𝔩 δ`).

Then `δ` is a **global** `37`-th power: `∃ ε' : (𝓞 K)ˣ, δ = ε'^{37}`.

This is exactly the conclusion of Washington Lemma 9.9 (and hence
**Assumption II**, `WashingtonCaseIIExactQuotientUnitPower37Source`'s payload),
reduced to its two structural inputs.  The collapse itself —
`ind₃₇ δ = d · ind₃₇ E₃₂`, `ind₃₇ δ = 0`, `ind₃₇ E₃₂ ≠ 0 ⟹ 37 ∣ d ⟹ δ = ε'^{37}`
— is fully proven here from `caseIIThm95_residueInd37_E32_ne_zero`. -/
theorem caseIIThm95_descentUnit_isPow_of_singleIndexExpansion
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (δ : (𝓞 (CyclotomicField 37 ℚ))ˣ) (d : ℕ) (α : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (h_expand : δ = FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ^ d * α ^ 37)
    (h_localPow : BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((δ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, δ = ε' ^ 37 := by
  -- Lemma 9.8: `δ` is a 37th power mod 𝔩 ⟹ `ind₃₇ δ = 0`.
  have hind_zero : residueInd37 δ = 0 :=
    (isPthPowerModPrime_iff_residueInd37_eq_zero δ).mp h_localPow
  -- Compute `ind₃₇ δ` from the single-index expansion: `= d · ind₃₇ E₃₂`.
  have hind_eq : residueInd37 δ =
      (d : ZMod 37) * residueInd37 (FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32) := by
    rw [h_expand, residueInd37_mul, residueInd37_pow, residueInd37_pow]
    -- The `α^37` factor contributes `(37 : 𝔽₃₇) · ind₃₇ α = 0`.
    rw [show ((37 : ℕ) : ZMod 37) = 0 by decide, zero_mul, add_zero]
  -- `d · ind₃₇ E₃₂ = 0` with `ind₃₇ E₃₂ ≠ 0` in the field `𝔽₃₇` ⟹ `(d : 𝔽₃₇) = 0`.
  rw [hind_eq] at hind_zero
  have hd37 : (d : ZMod 37) = 0 :=
    (mul_eq_zero.mp hind_zero).resolve_right caseIIThm95_residueInd37_E32_ne_zero
  -- `(d : 𝔽₃₇) = 0` means `37 ∣ d`.
  rw [ZMod.natCast_eq_zero_iff] at hd37
  obtain ⟨c, rfl⟩ := hd37
  -- Then `E₃₂^{37·c} = (E₃₂^c)^{37}`, so `δ = (E₃₂^c · α)^{37}` is a global 37th power.
  refine ⟨FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ^ c * α, ?_⟩
  rw [h_expand, mul_pow, ← pow_mul, mul_comm c 37]

/-! ## 5. Discharging Assumption II from the two structural inputs

We package the two genuinely structural inputs of Washington Lemma 9.9 — the
single-index Corollary-8.15 expansion of the descent unit and the Lemma-9.8
mod-`𝔩` power-ness — as explicit mathematical hypotheses (`def … : Prop`, **not**
axioms), matching the telescope of
`WashingtonCaseIIExactQuotientUnitPower37Source` (Assumption II).  The discharge
then follows from the proven single-index collapse §4: *modulo these two named
inputs, Assumption II holds*.  This isolates precisely what remains. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Corollary 8.15, single-index form for the Case-II descent unit** (a
`def … : Prop`, **not** an axiom).

For every Case-II descent instance, the descent-equation quotient unit `ε₁/ε₂`
admits the single-index cyclotomic-unit expansion
`ε₁/ε₂ = E₃₂^{d} · α^{37}` (the regular indices having dropped out via the
Bernoulli table `Sinnott.flt37_bernoulli_table`, leaving only the sole irregular
index `i = 32`).  This is the structural content of Washington Corollary 8.15
specialised to `37`'s single irregular index; it is not yet formalised in the
repo (no `E⁺/(E⁺)³⁷` cyclotomic-unit basis with Galois-eigenspace decomposition). -/
def Cor815SingleIndexExpansion37
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
    ∃ (d : ℕ) (α : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ε₁ / ε₂ = FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ^ d * α ^ 37

open FLT37.LehmerVandiver.CaseII in
/-- **Lemma 9.8 for the Case-II descent unit** (a `def … : Prop`, **not** an
axiom).

For every Case-II descent instance, the descent-equation quotient unit `ε₁/ε₂` is
a `37`-th power **modulo `𝔩`** (`IsPthPowerModPrime 37 𝔩 (ε₁/ε₂)`).  This is
Washington Lemma 9.8 (the Kummer congruence `η_a/η_b ≡ (ρ_b/ρ_a)ᵖ (mod 𝔩)`),
specialised to the descent unit; it is the residue-level statement that the
discrete-log criterion of this file turns into `ind₃₇ (ε₁/ε₂) = 0`. -/
def Lemma98LocalPower37
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
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)))

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the two structural inputs** (proven, axiom-clean *given*
`Cor815SingleIndexExpansion37` and `Lemma98LocalPower37`).

Combining Corollary 8.15's single-index expansion (`h_expand`) and Lemma 9.8's
mod-`𝔩` power-ness (`h_localPow`) with the proven single-index collapse §4
(`caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`, whose operative core is
`ind₃₇ E₃₂ ≠ 0`) discharges **Assumption II**, i.e. produces
`WashingtonCaseIIExactQuotientUnitPower37Source`: the descent unit `ε₁/ε₂` is a
`37`-th power.

This is the precise reduction of the remaining Theorem-9.5 Case-II content to its
two structural inputs (Corollary 8.15 single-index expansion and Lemma 9.8);
everything else — the entire index/Vandermonde collapse — is proven in this file. -/
theorem caseIIThm95_assumptionII_of_corollary815_lemma98
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (h_localPow : Lemma98LocalPower37) :
    WashingtonCaseIIExactQuotientUnitPower37Source := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨d, α, hexp⟩ := h_expand hV hSO D hx hy hz heq
  exact caseIIThm95_descentUnit_isPow_of_singleIndexExpansion (ε₁ / ε₂) d α hexp
    (h_localPow hV hSO D hx hy hz heq)

/-- **The Lemma-9.9 bridge `CaseIIThm95Lemma99Bridge` from the two structural
inputs** (proven, axiom-clean *given* the two named inputs).

`CaseIIThm95Lemma99Bridge` (`CaseIIThm95Discharge.lean`) is definitionally
`WashingtonCaseIIExactQuotientUnitPower37Source`, so the previous discharge
produces it directly.  Feeding it to the proven
`caseIIThm95Descent37_of_lemma99Bridge` then yields the full Theorem-9.5 Case-II
descent `CaseIIThm95Descent37`, given the proven σ-stable adjacent-generator
source.  Thus the **entire** remaining Case-II content for `p = 37` is the pair
`(Cor815SingleIndexExpansion37, Lemma98LocalPower37)`. -/
theorem caseIIThm95_lemma99Bridge_of_corollary815_lemma98
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (h_localPow : Lemma98LocalPower37) :
    CaseIIThm95Lemma99Bridge :=
  caseIIThm95_assumptionII_of_corollary815_lemma98 h_expand h_localPow

end BernoulliRegular.FLT37.Eichler

end
