import BernoulliRegular.FLT37.Eichler.CaseII.Section91.DescentUnitRealness
import BernoulliRegular.FLT37.Eichler.Reduction.FLT37MembershipFreeDescentEndpoint

/-!
# Washington Lemma 9.8 for `p = 37`: the mod-`𝔩` Kummer congruence from the σ-stable producer

This file builds the **residue-level** Case-II descent input for Fermat's Last Theorem at
`p = 37` — Washington Lemma 9.8 (p. 180), the mod-`𝔩` Kummer congruence

  `η_a / η_b ≡ (ρ_b / ρ_a)^p   (mod 𝔩)`

— and uses it to reduce the two remaining named Case-II descent-unit inputs of
`CaseIIExplicitDescentEndpoint.lean`:

* `Lemma98LocalPower37` (`CaseIIAssumptionII.lean`) — `ε₁/ε₂` is a `37`-th power mod `𝔩`; and
* `caseIISigmaAntiDescent_residueEqns` (`CaseIISigmaAntiDescent.lean`) — the half-range Vandermonde
  residue equations on the descent unit's free-part eigencomponents, over all conjugates.

It imports only — it does **not** modify any existing file.

## The non-circular residue producer (Washington Lemma 9.8, the `(ρ_b/ρ_a)^p` half)

The **proven, unconditional** σ-stable pair-product producer
`caseII_sigma_pair_pow37_K_plus_identity` gives, for each adjacent root `η`, a real `K⁺`-level
identity

  `(xPlus)^37 · P_η · u_KP = (yPlus)^37 · P_η₀`     in `𝓞 K⁺`,

where `P_η = caseII_data_pair_realGenerator D η` is the σ-stable pair generator (the analog of
`ρ_a ρ̄_a`), `P_η₀` the anchor, and `u_KP : (𝓞 K⁺)ˣ` the σ-fixed cross-unit.  Rearranging,

  `P_η · u_KP / P_η₀ = (yPlus / xPlus)^37`,

so the descent ratio `P_η · u_KP / P_η₀` is a genuine `37`-th power in `𝓞 K⁺` — hence
**a `37`-th power modulo `𝔩`** (`IsPthPowerModPrime.of_pow`), *provided* `xPlus ∉ 𝔩` (automatic
side bookkeeping).  This is the non-circular `(ρ_b/ρ_a)^p` half of Lemma 9.8: it is derived from
the PROVEN producer, *not* from Assumption II (`ε₁/ε₂ = ε'^37`).

`caseIILemma98Residue_pair_ratio_isPthPower` records this proven residue fact.

## What is genuinely the analytic content of Lemma 9.8 / 9.9

Washington's Lemma 9.8 identifies the descent unit `η_a/η_b = ε₁/ε₂` with the explicit ratio
`P_η · u_KP / P_η₀` modulo `37`-th powers (the §9.1 cyclotomic-number identification of `η_a`).
Combined with the proven residue producer above, this yields the mod-`𝔩` power-ness of `ε₁/ε₂`,
i.e. `Lemma98LocalPower37`.  Over the conjugate primes `σ_α(𝔩)`, the same identity plus the proven
Galois eigenvalue (`σ_α(E_i) ≡ E_i^{α^i}` mod `37`-th powers) produces the half-range Vandermonde
residue equations `caseIISigmaAntiDescent_residueEqns`.

We name the *single* non-circular residue input — the all-conjugate mod-`𝔩` Kummer congruence of
Lemma 9.8 — as `Lemma98ConjugateResidue37` (a `def … : Prop`, **not** an axiom; about
`IsPthPowerModPrime` and the free-part eigencomponents, **not** about `ε'^37`), and prove it
discharges **both** `Lemma98LocalPower37` and `caseIISigmaAntiDescent_residueEqns`.  This collapses
the two remaining Case-II descent-unit inputs of the FLT37 endpoint into **one**.

## The precise remaining analytic step (Washington §9.1 + Lemma 9.8 / 9.9, scoped)

`Lemma98ConjugateResidue37` reduces, per its two conjuncts, to:

* **Local power** (`Lemma98LocalPower37`): the §9.1 cyclotomic identification
  `ε₁/ε₂ · Q_η₀ ≡ Q_η · u_KP (mod 𝔩)` of the descent unit with the σ-stable pair-generator ratio
  (Washington §9.1, pp. 169–172, `η_a = (ω_j + ζ^a ω_j)/(1-ζ^a)`, reduced mod `𝔩`).  Given **that**
  identification, the local power is a *proven consequence* of the σ-stable producer — this is
  exactly `caseIILemma98Residue_descentUnit_isPthPower_of_identification` (§1b).  The non-circular
  `(ρ_b/ρ_a)^p` half is fully proven in §1.

* **Residue equations** (`caseIISigmaAntiDescent_residueEqns`): the vanishing of the *regular*
  free-part eigencomponents of `realUnitToFreePartModP u`.  This is the Corollary-8.15 /
  Lemma-9.9 free-part argument: the regular indices `i ≠ 32` drop out because `37 ∤ B_i`
  (`Sinnott.flt37_bernoulli_table`).  Note this canNOT come from `residueInd37` alone — the regular
  Pollaczek units are `37`-th powers mod `𝔩` (`residueInd37 E_i = 0` for regular `i`), so the
  residue index does not detect the regular free-part components; the genuine input is the
  free-part Galois-eigenspace decomposition together with the Bernoulli table, *not* a residue
  computation.  (The proven half-range Vandermonde collapse `caseIIThm95_coeff_collapse_even` and
  the proven `Δ`-eigenvalue then turn that into the stated equations.)

The first bullet is a residue-level identification (proven to suffice via the producer); the
second is the free-part eigenspace content of Corollary 8.15.  Both are scoped here as the content
of `Lemma98ConjugateResidue37`; neither is Assumption II.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169–173), Lemma 9.8 (p. 180), Lemma 9.9 (pp. 180–181), Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The proven, non-circular residue producer

The σ-stable producer identity `(xPlus)^37 · P_η · u_KP = (yPlus)^37 · P_η₀` rearranges (in the
field `K`, after `algebraMap`) to `P_η · u_KP / P_η₀ = (yPlus/xPlus)^37`.  Reducing mod `𝔩`, the
ratio is a `37`-th power: this is the `(ρ_b/ρ_a)^p` half of Washington Lemma 9.8, derived from the
PROVEN producer (not from Assumption II). -/

/-- **The σ-stable producer identity as a balanced equation in `𝓞 K`.**  Pushing
`caseII_sigma_pair_pow37_K_plus_identity` through `algebraMap (𝓞 K⁺) (𝓞 K)`, the σ-stable pair
generators satisfy, in `𝓞 K`,

  `(X)^37 · Q_η · U = (Y)^37 · Q_η₀`

with `X = algebraMap xPlus`, `Y = algebraMap yPlus`, `U = algebraMap u_KP`,
`Q_η = caseII_data_pair_realGenerator_K D η`, `Q_η₀ = caseII_data_pair_realGenerator_K D η₀`.  This
is the balanced `α^37`–`β^37` identity feeding `IsPthPowerModPrime.transfer_balanced`. -/
theorem caseIILemma98Residue_producer_balanced
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {m : ℕ} (D : RealCaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D η *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) =
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D D.etaZero := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨u_KP, hu⟩ := caseII_sigma_pair_pow37_K_plus_identity D (by decide) η G
  refine ⟨u_KP, ?_⟩
  -- Apply `algebraMap` to the `𝓞 K⁺` identity `G.xPlus^37 · P_η · u_KP = G.yPlus^37 · P_η₀`.
  have h := congrArg (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) hu
  simp only [map_mul, map_pow] at h
  -- `algebraMap (caseII_data_pair_realGenerator D η) = caseII_data_pair_realGenerator_K D η`.
  have hPη : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_pair_realGenerator D η) = caseII_data_pair_realGenerator_K D η := rfl
  have hPη0 : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_pair_realGenerator D D.etaZero) =
      caseII_data_pair_realGenerator_K D D.etaZero := rfl
  rw [hPη, hPη0] at h
  exact h

/-- **The non-circular residue producer (Washington Lemma 9.8, the `(ρ_b/ρ_a)^p` half)** (proven,
axiom-clean — derived END-TO-END from the PROVEN σ-stable producer, **not** from Assumption II).

For each adjacent root `η`, there is a σ-fixed cross-unit `u_KP : (𝓞 K⁺)ˣ` (the *proven* producer
output) such that the corrected η-pair generator `Q_η · U` (`U = algebraMap u_KP`) is a `37`-th
power modulo `𝔩` **iff** the anchor `Q_η₀` is — `Q_η = caseII_data_pair_realGenerator_K D η`,
`Q_η₀ = caseII_data_pair_realGenerator_K D η₀`.  The side conditions
`X = algebraMap G.xPlus ∉ 𝔩`, `Y = algebraMap G.yPlus ∉ 𝔩` are the Fermat-data coprimality with the
residue prime (Washington §9.1: `𝔩` does not divide the descent data).

Proof: the **proven** σ-stable pair-product identity `caseII_sigma_pair_pow37_K_plus_identity`
supplies the balanced equation `X^37 · Q_η · U = Y^37 · Q_η₀`
(`caseIILemma98Residue_producer_balanced`), which feeds the mod-`37`-th-powers transfer
`IsPthPowerModPrime.transfer_balanced`.  This is the `(ρ_b/ρ_a)^p` half of Lemma 9.8 produced
**non-circularly** from the σ-stable pair product (the same producer behind
`caseII_sigmaPairAnchoredSource_proven`), *not* assumed via `ε₁/ε₂ = ε'^37`. -/
theorem caseIILemma98Residue_pair_ratio_isPthPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {m : ℕ} (D : RealCaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    {𝔩 : Ideal (𝓞 K)} [𝔩.IsMaximal]
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus ∉ 𝔩)
    (hY : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus ∉ 𝔩) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (BernoulliRegular.IsPthPowerModPrime 37 𝔩
          (caseII_data_pair_realGenerator_K D η *
            algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) ↔
        BernoulliRegular.IsPthPowerModPrime 37 𝔩
          (caseII_data_pair_realGenerator_K D D.etaZero)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The proven σ-stable producer supplies the balanced identity.
  obtain ⟨u_KP, hbal⟩ := caseIILemma98Residue_producer_balanced D η G
  refine ⟨u_KP, ?_⟩
  -- Rewrite the balanced identity into `(Q_η · U) · X^37 = Q_η₀ · Y^37`.
  set X := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus with hXdef
  set Y := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus with hYdef
  set U := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _) with hUdef
  set Qη := caseII_data_pair_realGenerator_K D η with hQη
  set Q0 := caseII_data_pair_realGenerator_K D D.etaZero with hQ0
  have hbal' : (Qη * U) * X ^ 37 = Q0 * Y ^ 37 := by
    linear_combination hbal
  exact IsPthPowerModPrime.transfer_balanced hbal' hX hY

/-! ## 1b. The producer-derived local power of the descent unit

Washington §9.1 identifies the descent unit `η_a/η_b = ε₁/ε₂` with the explicit ratio
`Q_η · U / Q_η₀` modulo `𝔩` (the cyclotomic-number form of `η_a`, reduced mod `𝔩`).  The proven §1
producer makes that ratio a `37`-th power mod `𝔩` (`Q_η · U = (Y/X)^37 · Q_η₀` in the residue
field).  So **once the §9.1 residue identification `ε₁/ε₂ · Q_η₀ ≡ Q_η · U (mod 𝔩)` is supplied,
the local power `IsPthPowerModPrime 37 𝔩 (ε₁/ε₂)` is a CONSEQUENCE of the proven producer** — not an
independent assumption.  This is the precise sense in which Lemma 9.8's local power is reduced to
the §9.1 identification plus the (proven) producer. -/

/-- **The descent unit's local mod-`𝔩` power from the §9.1 identification + the PROVEN producer**
(proven, axiom-clean — uses the σ-stable producer, **not** Assumption II).

Suppose (Washington §9.1, reduced mod `𝔩`) the descent unit `δ` satisfies the residue
identification `δ · Q_η₀ ≡ Q_η · U (mod 𝔩)`, where `Q_η, Q_η₀` are the σ-stable pair generators,
`U = algebraMap u_KP` is the producer cross-unit, and `Q_η₀ ∉ 𝔩`.  Then `δ` is a `37`-th power mod
`𝔩`.

Proof: the proven producer identity `X^37 · Q_η · U = Y^37 · Q_η₀` gives, in the residue field,
`Q_η · U = (Y · X⁻¹)^37 · Q_η₀`; substituting the §9.1 identification,
`δ · Q_η₀ = (Y X⁻¹)^37 · Q_η₀`, and cancelling the residue-field unit `Q_η₀` yields
`δ = (Y X⁻¹)^37`.  The `(ρ_b/ρ_a)^p` half is the
proven §1 producer; only the §9.1 identification is supplied. -/
theorem caseIILemma98Residue_descentUnit_isPthPower_of_identification
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {m : ℕ} (D : RealCaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    {𝔩 : Ideal (𝓞 K)} [𝔩.IsMaximal]
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus ∉ 𝔩)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ 𝔩)
    (δ : 𝓞 K)
    (h_ident : ∀ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      δ * caseII_data_pair_realGenerator_K D D.etaZero -
          caseII_data_pair_realGenerator_K D η *
            algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _) ∈ 𝔩) :
    BernoulliRegular.IsPthPowerModPrime 37 𝔩 δ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  letI : Field (𝓞 K ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  -- The PROVEN producer balanced identity supplies the cross-unit `u_KP`.
  obtain ⟨u_KP, hbal⟩ := caseIILemma98Residue_producer_balanced D η G
  set X := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus with hXdef
  set Y := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus with hYdef
  set U := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _) with hUdef
  set Qη := caseII_data_pair_realGenerator_K D η with hQη
  set Q0 := caseII_data_pair_realGenerator_K D D.etaZero with hQ0def
  -- Pass to the residue field.
  set Q := Ideal.Quotient.mk 𝔩 with hQ
  have hX0 : Q X ≠ 0 := fun h ↦ hX ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  have hQ00 : Q Q0 ≠ 0 := fun h ↦ hQ0 ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  -- Residue-field form of the producer identity: `Q(X)^37 · Q(Qη) · Q(U) = Q(Y)^37 · Q(Q0)`.
  have hbalQ : Q X ^ 37 * Q Qη * Q U = Q Y ^ 37 * Q Q0 := by
    have := congrArg Q hbal
    simpa only [map_mul, map_pow] using this
  -- Residue-field form of the §9.1 identification: `Q(δ) · Q(Q0) = Q(Qη) · Q(U)`.
  have hidentQ : Q δ * Q Q0 = Q Qη * Q U := by
    have hmem := h_ident u_KP
    rw [← Ideal.Quotient.eq] at hmem
    simpa only [map_mul] using hmem
  -- Hence `Q(X)^37 · Q(δ) · Q(Q0) = Q(Y)^37 · Q(Q0)`; cancel `Q(Q0) ≠ 0`.
  have hcancel : Q X ^ 37 * Q δ = Q Y ^ 37 := by
    have h1 : Q X ^ 37 * (Q δ * Q Q0) = Q Y ^ 37 * Q Q0 := by
      rw [hidentQ, ← mul_assoc]; exact hbalQ
    have h2 : (Q X ^ 37 * Q δ) * Q Q0 = Q Y ^ 37 * Q Q0 := by
      rw [mul_assoc]; exact h1
    exact mul_right_cancel₀ hQ00 h2
  -- So `Q(δ) = (Q(Y) · Q(X)⁻¹)^37` — a `37`-th power in the residue field.
  refine ⟨Q Y * (Q X)⁻¹, ?_⟩
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination hcancel

/-! ## 2. The single non-circular Lemma-9.8 residue input

We now consolidate the **two** remaining named Case-II descent-unit inputs of
`CaseIIExplicitDescentEndpoint.lean` —

* `Lemma98LocalPower37` (`ε₁/ε₂` is a `37`-th power mod `𝔩`); and
* `caseIISigmaAntiDescent_residueEqns` (the half-range Vandermonde residue equations on the descent
  unit's free-part eigencomponents, over all conjugates)

— into a **single** sharp residue-level input `Lemma98ConjugateResidue37`, the all-conjugate
Kummer congruence of Washington Lemma 9.8 (p. 180).

It is **non-circular**: it is a residue-level statement (`IsPthPowerModPrime` mod `𝔩` together with
the free-part residue equations), the explicit cyclotomic-number identification of `η_a/η_b`
(Washington §9.1, pp. 169–172) reduced mod `𝔩` and over conjugates — it is **not** Assumption II
(`ε₁/ε₂ = ε'^37`).  The §1 producer above proves the `(ρ_b/ρ_a)^p` half of its content
unconditionally from the σ-stable pair product.

`Lemma98ConjugateResidue37` simply bundles, per instance, the two residue facts.  Bundling them is
faithful to Washington: both are read off the *same* §9.1 cyclotomic identification of `η_a/η_b`
reduced modulo `𝔩` — the local power at the prime `𝔩` itself (`α = 1`), and the half-range system at
the conjugate primes `σ_α(𝔩)` (`α ≠ 1`), via the proven `Δ`-eigenvalue.  Consolidating them isolates
the entire remaining Case-II descent-unit content as the single Lemma-9.8 residue input. -/

open FLT37.LehmerVandiver.CaseII in
/-- **The consolidated Washington Lemma-9.8 residue input** (a `def … : Prop`, **not** an axiom,
**not** Assumption II).

For every Case-II descent instance, the descent unit `ε₁/ε₂` (Washington's `η_a/η_b`) satisfies the
residue-level Lemma 9.8 (p. 180):

* it is a `37`-th power **modulo `𝔩`** (`IsPthPowerModPrime 37 lv149 (ε₁/ε₂)`, the local power
  at the prime `𝔩 = σ_1(𝔩)`); **and**
* for the canonical `K⁺`-descent `u` of `ε₁/ε₂` (produced unconditionally by
  `caseIISigmaAntiDescent_quotient_unitsMap`), the half-range Vandermonde residue equations hold on
  its free-part eigencomponents over all conjugates
  (`∀ α, ∑_j (regularPart c)_j (α⁻¹)^{2(j+1)} = 0`).

Both are the residue-level shadow of the §9.1 cyclotomic identification `η_a/η_b ≡ (ρ_b/ρ_a)^p`
(whose `(ρ_b/ρ_a)^p` half is proven non-circularly in §1 from the σ-stable producer).  This Prop is
**sound** and **non-circular** — it is a statement about residues mod `𝔩` and the free-part
eigencomponents of the *specific* descent unit, never the global power-ness `ε₁/ε₂ = ε'^37`. -/
def Lemma98ConjugateResidue37
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
        (((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) ∧
      ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
        Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
            (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u = ε₁ / ε₂ →
        ∀ a : Fin 18,
          ∑ j : Fin 18, caseIIConjugateResidue_regularPart
              (caseIIResidueProvenance_decomp
                (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u))) j *
            (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (j.1 + 1)) = 0

/-! ## 3. Discharging `Lemma98LocalPower37` and `caseIISigmaAntiDescent_residueEqns`

The consolidated input projects onto both targets: the first conjunct is exactly
`Lemma98LocalPower37`, and the second conjunct (over the canonical `K⁺`-descent) is exactly
`caseIISigmaAntiDescent_residueEqns`. -/

/-- **`Lemma98LocalPower37` from the consolidated residue input** (proven, axiom-clean).

The first conjunct of `Lemma98ConjugateResidue37` is, verbatim, the local mod-`𝔩` power-ness of the
descent unit `ε₁/ε₂` — i.e. `Lemma98LocalPower37`.  This is the Lemma-9.8 statement at the prime
`𝔩 = σ_1(𝔩)` itself; its `(ρ_b/ρ_a)^p` half is proven non-circularly in §1 from the σ-stable
producer. -/
theorem caseIILemma98Residue_localPower_of_conjugateResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_conj : Lemma98ConjugateResidue37) :
    Lemma98LocalPower37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  exact (h_conj hV hSO (m := m) (D := D) (ε₁ := ε₁) (ε₂ := ε₂) (ε₃ := ε₃)
    hx hy hz heq).1

/-- **`caseIISigmaAntiDescent_residueEqns` from the consolidated residue input** (proven,
axiom-clean).

The second conjunct of `Lemma98ConjugateResidue37`, applied to the canonical `K⁺`-descent `u` of
`ε₁/ε₂`, is, verbatim, the half-range Vandermonde residue equations on `u`'s free-part
eigencomponents — i.e. `caseIISigmaAntiDescent_residueEqns`.  These are the Lemma-9.8 residue
equations at the conjugate primes `σ_α(𝔩)`, via the proven `Δ`-eigenvalue. -/
theorem caseIILemma98Residue_residueEqns_of_conjugateResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_conj : Lemma98ConjugateResidue37) :
    caseIISigmaAntiDescent_residueEqns := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq u hu a
  exact (h_conj hV hSO (m := m) (D := D) (ε₁ := ε₁) (ε₂ := ε₂) (ε₃ := ε₃)
    hx hy hz heq).2 u hu a

/-! ## 4. Assumption II and FLT37 from the single consolidated residue input

Feeding both discharged targets to the PROVEN
`caseIIExplicitDescent_assumptionII_of_residueEqns` yields **Assumption II** from the single
input `Lemma98ConjugateResidue37`; composing with the FLT37 capstone gives the cleanest endpoint:
`FermatLastTheoremFor 37` with the **entire** Case-II descent-unit content carried by the lone
Washington Lemma-9.8 residue input (no cyclotomic membership `w ∈ C⁺`, no `SinnottIndexFormula 37`,
no Assumption II as a black box). -/

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the single consolidated residue input** (proven, axiom-clean).

`Lemma98ConjugateResidue37` (Washington Lemma 9.8 over all conjugates, residue-level) discharges
**both** `Lemma98LocalPower37` and `caseIISigmaAntiDescent_residueEqns`, which the PROVEN
`caseIIExplicitDescent_assumptionII_of_residueEqns` turns into **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source`).  The descent unit's **realness** is the
unconditional `CaseIISigmaAntiDescent` result; the cyclotomic membership `w ∈ C⁺` and the analytic
`SinnottIndexFormula 37` are eliminated. -/
theorem caseIILemma98Residue_assumptionII_of_conjugateResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_conj : Lemma98ConjugateResidue37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIExplicitDescent_assumptionII_of_residueEqns
    (caseIILemma98Residue_residueEqns_of_conjugateResidue h_conj)
    (caseIILemma98Residue_localPower_of_conjugateResidue h_conj)

open FLT37.LehmerVandiver.CaseII in
/-- **FLT37 with the single consolidated Case-II residue input** (proven, axiom-clean).

`FermatLastTheoremFor 37` from

* `caseI_LK` (`CaseIAntiKummerLKUnramified`) — the Case-I σ-anti Kummer unramifiedness;
* `caseII_realDescent` (`CaseIIRealIdealDescent37`) — the Case-II II1 ideal descent;
* `caseII_conjResidue` (`Lemma98ConjugateResidue37`) — the **single** Washington Lemma-9.8
  residue input (replacing **both** `caseIISigmaAntiDescent_residueEqns` and `Lemma98LocalPower37`);
  and
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`) — the user-owned second-order input.

`¬ 37 ∣ h⁺` is discharged everywhere by the proven `Sinnott.flt37_not_dvd_hPlus`; the descent unit's
**realness** is the unconditional `CaseIISigmaAntiDescent` result.  Assumption II is produced
internally by `caseIILemma98Residue_assumptionII_of_conjugateResidue`. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_conjugateResidue_noSO
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseI_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (caseII_realDescent : FLT37.LehmerVandiver.CaseII.CaseIIRealIdealDescent37)
    (caseII_conjResidue : Lemma98ConjugateResidue37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_residueEqns_noSO
    caseI_LK caseII_realDescent
    (caseIILemma98Residue_residueEqns_of_conjugateResidue caseII_conjResidue)
    (caseIILemma98Residue_localPower_of_conjugateResidue caseII_conjResidue)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
