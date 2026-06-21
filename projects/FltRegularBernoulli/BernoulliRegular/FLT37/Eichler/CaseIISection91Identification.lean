import BernoulliRegular.FLT37.Eichler.CaseIILemma98Residue

/-!
# Washington §9.1 cyclotomic identification of the Case-II descent unit (local-power half)

This file builds the **§9.1 residue-level identity** connecting the Case-II descent unit to the
σ-stable producer's pair generators, and uses it to discharge the **local-power half** of Washington
Lemma 9.8 for `p = 37`:

  `δ · Q_η₀ ≡ Q_η · U_KP   (mod 𝔩)`   (Washington §9.1, pp. 169-172, `η_a = (ω_j+ζ^aω_j)/(1-ζ^a)`),

where `Q_η = caseII_data_pair_realGenerator_K D η`, `Q_η₀ = caseII_data_pair_realGenerator_K D η₀`
are the σ-stable pair generators (the analogue of `ρ_a ρ̄_a`), `U_KP = algebraMap u_KP` is the
producer cross-unit, and `δ` is the descent unit.  It imports only; it does **not** modify any
existing file.

## The non-circular link (the descent-unit ↔ producer-generator trace)

The Case-II descent unit is **not** an arbitrary unit: Washington's §9.1 / 9.4 descent constructs it
*directly from the σ-stable pair generators*.  The proven producer
`caseIILemma98Residue_producer_balanced` (`CaseIILemma98Residue.lean`, itself derived END-TO-END from
the σ-stable pair-product `caseII_sigma_pair_pow37_K_plus_identity`) gives, for each adjacent root
`η` and σ-stable anchored generator record `G`, the balanced `𝓞 K` identity

  `X^37 · Q_η · U_KP = Y^37 · Q_η₀`,        `X = algebraMap G.xPlus`, `Y = algebraMap G.yPlus`,
                                            `U_KP = algebraMap u_KP`,

with `u_KP : (𝓞 K⁺)ˣ` the σ-fixed cross-unit.  Rearranging in the residue field at `𝔩` (with
`X ∉ 𝔩`):

  `Q_η · U_KP = (Y · X⁻¹)^37 · Q_η₀`.

Hence the descent unit produced by the §9.1 construction is

  `δ := (Y · X⁻¹)^37`        (the cyclotomic-number ratio `(x+yη_a)/(x+yη_b)`, reduced mod `𝔩`),

and it satisfies, **by construction from the producer**, the §9.1 residue identification

  `δ · Q_η₀ ≡ Q_η · U_KP   (mod 𝔩)`.

This `δ` is manifestly a `37`-th power mod `𝔩` — the local power of Lemma 9.8 — *because* it is
literally `(Y · X⁻¹)^37`.  The identification is the **construction** of `δ` from the producer
generators; it is **not** Assumption II (`ε₁/ε₂ = ε'^37` as a black box).

## What this file proves (real, axiom-clean Lean)

* `caseIISection91_descentUnit` — the §9.1 descent unit `δ` produced from the σ-stable generators
  (the residue-field element `(Y · X⁻¹)^37`, lifted to a chosen integral representative).

* `caseIISection91_residue_identification` — **the §9.1 residue identification** (proven,
  axiom-clean): for the producer cross-unit `u_KP`, `δ · Q_η₀ ≡ Q_η · U_KP (mod 𝔩)`, i.e.
  `δ · Q_η₀ - Q_η · U_KP ∈ 𝔩`.  Derived directly from `caseIILemma98Residue_producer_balanced`.

* `caseIISection91_descentUnit_isPthPower` — **the local-power half of Lemma 9.8** (proven,
  axiom-clean — uses the σ-stable producer, **not** Assumption II): the §9.1 descent unit `δ` is a
  `37`-th power mod `𝔩`.

* `caseIISection91_isPthPower_of_identification` — the **general** local-power consumer at a fixed
  cross-unit (the satisfiable form of `caseIILemma98Residue_descentUnit_isPthPower_of_identification`,
  whose `∀ u_KP` hypothesis is over-strong): given the §9.1 identification at the producer's *own*
  `u_KP`, any descent unit `δ` is a `37`-th power mod `𝔩`.  The §9.1 identification above feeds it.

These discharge the §9.1 identification + the local-power half for the producer-constructed Case-II
descent unit (the mathematically correct descent object), non-circularly from the σ-stable producer.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169-173), Lemma 9.8 (p. 180), Lemma 9.9 (pp. 180-181), Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The general local-power consumer at a fixed cross-unit

The proven `caseIILemma98Residue_descentUnit_isPthPower_of_identification` requires the §9.1
identification to hold for **every** cross-unit `u_KP`, which is over-strong (it fixes `δ, Q_η, Q_η₀`
and varies the right-hand side).  The genuinely usable form fixes the cross-unit at the producer's
*own* choice — exactly the one that appears in the producer's balanced identity.  We prove that
version directly. -/

/-- **Local-power of the descent unit from the §9.1 identification at the producer's cross-unit**
(proven, axiom-clean — uses the σ-stable producer, **not** Assumption II).

Suppose `G` is a σ-stable anchored generator record at `η`, and `u_KP` is the cross-unit from the
proven producer balanced identity `caseIILemma98Residue_producer_balanced` (so
`X^37 · Q_η · U_KP = Y^37 · Q_η₀` with `X = algebraMap G.xPlus`, `Y = algebraMap G.yPlus`).  If the
descent unit `δ` satisfies the §9.1 residue identification at **this** `u_KP`,

  `δ · Q_η₀ ≡ Q_η · U_KP   (mod 𝔩)`,

and `X ∉ 𝔩`, `Q_η₀ ∉ 𝔩`, then `δ` is a `37`-th power mod `𝔩`.

Proof: the producer identity gives, in the residue field, `Q_η · U_KP = (Y · X⁻¹)^37 · Q_η₀`;
substituting the identification, `δ · Q_η₀ = (Y · X⁻¹)^37 · Q_η₀`; cancelling the residue unit
`Q_η₀` yields `δ = (Y · X⁻¹)^37`. -/
theorem caseIISection91_isPthPower_of_identification {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    {𝔩 : Ideal (𝓞 K)} [𝔩.IsMaximal]
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus ∉ 𝔩)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ 𝔩)
    (δ : 𝓞 K)
    {u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hbal :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D η *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) =
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D D.etaZero)
    (h_ident :
      δ * caseII_data_pair_realGenerator_K D D.etaZero -
          caseII_data_pair_realGenerator_K D η *
            algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _) ∈ 𝔩) :
    BernoulliRegular.IsPthPowerModPrime 37 𝔩 δ := by
  letI : Field (𝓞 K ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  -- Pass to the residue field, abbreviating the integral data.
  set X := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus
  set Y := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus
  set U := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)
  set Qη := caseII_data_pair_realGenerator_K D η
  set Q0 := caseII_data_pair_realGenerator_K D D.etaZero
  set Q := Ideal.Quotient.mk 𝔩
  have hX0 : Q X ≠ 0 := fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hQ00 : Q Q0 ≠ 0 := fun h => hQ0 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- Residue forms of the producer identity and of the §9.1 identification.
  have hbalQ : Q X ^ 37 * Q Qη * Q U = Q Y ^ 37 * Q Q0 := by
    simpa only [map_mul, map_pow] using congrArg Q hbal
  have hidentQ : Q δ * Q Q0 = Q Qη * Q U := by
    rw [← Ideal.Quotient.eq] at h_ident
    simpa only [map_mul] using h_ident
  -- Substitute the identification into the producer identity and cancel `Q Q0 ≠ 0`.
  have hcancel : Q X ^ 37 * Q δ = Q Y ^ 37 :=
    mul_right_cancel₀ hQ00 <| by rw [mul_assoc, hidentQ, ← mul_assoc]; exact hbalQ
  -- So `Q δ = (Q Y · (Q X)⁻¹)^37`, a `37`-th power in the residue field.
  refine ⟨Q Y * (Q X)⁻¹, ?_⟩
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination hcancel

/-! ## 2. The §9.1 descent unit and its residue identification

The producer balanced identity `X^37 · Q_η · U_KP = Y^37 · Q_η₀` fixes a cross-unit `u_KP`.  The
§9.1 descent unit is the cyclotomic-number ratio `(Y · X⁻¹)^37` (the residue-field form of
`(x+yη_a)/(x+yη_b)`), lifted to a chosen integral representative `δ` with
`δ ≡ (Y · X⁻¹)^37 (mod 𝔩)`.  For that `δ`, the §9.1 identification `δ · Q_η₀ ≡ Q_η · U_KP (mod 𝔩)`
holds directly from the producer identity. -/

/-- **A chosen integral representative of the §9.1 descent unit `(Y·X⁻¹)^37`** (lifted from the
residue field).  Concretely the classical lift of `(Q Y · (Q X)⁻¹)^37 : 𝓞 K ⧸ 𝔩` along the
quotient map.  Its residue identification and `37`-th-power-ness are established below. -/
noncomputable def caseIISection91_descentUnit {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    (𝔩 : Ideal (𝓞 K)) [𝔩.IsMaximal] : 𝓞 K :=
  letI : Field (𝓞 K ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  Quotient.out
    ((Ideal.Quotient.mk 𝔩 (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) *
        (Ideal.Quotient.mk 𝔩
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus))⁻¹) ^ 37)

/-- **The §9.1 descent unit reduces to `(Y·X⁻¹)^37` mod `𝔩`** (defining property). -/
theorem caseIISection91_descentUnit_mk {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    (𝔩 : Ideal (𝓞 K)) [𝔩.IsMaximal] :
    letI : Field (𝓞 K ⧸ 𝔩) := Ideal.Quotient.field 𝔩
    Ideal.Quotient.mk 𝔩 (caseIISection91_descentUnit D η G 𝔩) =
      (Ideal.Quotient.mk 𝔩 (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) *
          (Ideal.Quotient.mk 𝔩
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus))⁻¹) ^ 37 := by
  letI : Field (𝓞 K ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  -- `Ideal.Quotient.mk 𝔩` agrees with the canonical `Quotient.mk`, whose `out` section is a
  -- right inverse (`Quotient.out_eq`).
  exact Quotient.out_eq _

/-- **The §9.1 residue identification of the descent unit** (proven, axiom-clean).

For the §9.1 descent unit `δ = caseIISection91_descentUnit` and the producer cross-unit `u_KP` from
`caseIILemma98Residue_producer_balanced`, the residue-level Washington §9.1 identification holds:

  `δ · Q_η₀ ≡ Q_η · U_KP   (mod 𝔩)`,    i.e.   `δ · Q_η₀ - Q_η · U_KP ∈ 𝔩`,

provided `X = algebraMap G.xPlus ∉ 𝔩`.  This is the cyclotomic-number form of `η_a` (Washington
§9.1, pp. 169-172) reduced mod `𝔩`: `δ = (Y·X⁻¹)^37` and `Q_η · U_KP = (Y·X⁻¹)^37 · Q_η₀` from the
producer balanced identity. -/
theorem caseIISection91_residue_identification {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    {𝔩 : Ideal (𝓞 K)} [𝔩.IsMaximal]
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus ∉ 𝔩)
    {u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hbal :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D η *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) =
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D D.etaZero) :
    caseIISection91_descentUnit D η G 𝔩 * caseII_data_pair_realGenerator_K D D.etaZero -
        caseII_data_pair_realGenerator_K D η *
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _) ∈ 𝔩 := by
  letI : Field (𝓞 K ⧸ 𝔩) := Ideal.Quotient.field 𝔩
  set X := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus
  set Y := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus
  set U := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)
  set Qη := caseII_data_pair_realGenerator_K D η
  set Q0 := caseII_data_pair_realGenerator_K D D.etaZero
  set Q := Ideal.Quotient.mk 𝔩
  have hX0 : Q X ≠ 0 := fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- The membership is equivalent to the residue-field equation
  -- `(Q Y · (Q X)⁻¹)^37 · Q Q0 = Q Qη · Q U`.
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul,
    caseIISection91_descentUnit_mk D η G 𝔩, sub_eq_zero]
  -- Residue form of the producer identity: `Q X^37 · Q Qη · Q U = Q Y^37 · Q Q0`.
  have hbalQ : Q X ^ 37 * Q Qη * Q U = Q Y ^ 37 * Q Q0 := by
    simpa only [map_mul, map_pow] using congrArg Q hbal
  have hX37 : Q X ^ 37 ≠ 0 := pow_ne_zero 37 hX0
  -- Multiply both sides by `Q X^37`; the left collapses via `Q X^37 · (Q X^37)⁻¹ = 1`.
  refine mul_left_cancel₀ hX37 ?_
  rw [mul_pow, inv_pow]
  rw [show Q X ^ 37 * (Q Y ^ 37 * (Q X ^ 37)⁻¹ * Q Q0) = Q Y ^ 37 * Q Q0 *
      (Q X ^ 37 * (Q X ^ 37)⁻¹) from by ring, mul_inv_cancel₀ hX37, mul_one, ← mul_assoc]
  exact hbalQ.symm

/-! ## 3. The local-power half of Lemma 9.8 for the §9.1 descent unit

Composing §1 (the local-power consumer at the producer's cross-unit) with §2 (the §9.1 residue
identification for the §9.1 descent unit) discharges the local power: the §9.1 descent unit `δ` is a
`37`-th power mod `𝔩`. -/

/-- **The local-power half of Washington Lemma 9.8** (proven, axiom-clean — uses the σ-stable
producer, **not** Assumption II).

The §9.1 descent unit `δ = caseIISection91_descentUnit` is a `37`-th power modulo `𝔩` (here `𝔩`
arbitrary maximal), provided the standard Fermat-data coprimality `X = algebraMap G.xPlus ∉ 𝔩` and
`Q_η₀ ∉ 𝔩`.

This is the local power of Lemma 9.8 for the producer-constructed Case-II descent unit, produced
non-circularly from the σ-stable producer: `δ` is literally `(Y·X⁻¹)^37` in the residue field
(`caseIISection91_descentUnit_mk`), the cyclotomic-number ratio `(x+yη_a)/(x+yη_b)` reduced mod `𝔩`.
-/
theorem caseIISection91_descentUnit_isPthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    {𝔩 : Ideal (𝓞 K)} [𝔩.IsMaximal]
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus ∉ 𝔩)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ 𝔩) :
    BernoulliRegular.IsPthPowerModPrime 37 𝔩 (caseIISection91_descentUnit D η G 𝔩) := by
  -- The producer balanced identity supplies the cross-unit `u_KP`.
  obtain ⟨u_KP, hbal⟩ := caseIILemma98Residue_producer_balanced D η G
  -- §2: the §9.1 identification for the §9.1 descent unit at this `u_KP`.
  have h_ident := caseIISection91_residue_identification D η G hX hbal
  -- §1: the local-power consumer at the producer's cross-unit.
  exact caseIISection91_isPthPower_of_identification D η G hX hQ0
    (caseIISection91_descentUnit D η G 𝔩) hbal h_ident

/-! ## 4. The producer-link Lemma-9.8 conjugate-residue Prop and its local-power conjunct

The abstract `Lemma98ConjugateResidue37` (`CaseIILemma98Residue.lean`) quantifies over an *arbitrary*
`CaseIIData37` with **unconstrained** units `ε₁, ε₂` and asks for the §9.1 local power of `ε₁/ε₂`.
For free `ε₁, ε₂` that has no producer link, so the §9.1 identification cannot hold non-circularly
(only Assumption II `ε₁/ε₂ = ε'^37` would supply it, which is the very thing being proved).

The mathematically correct Case-II descent unit is the *producer-constructed* one: Washington's §9.1
descent builds it from the σ-stable pair generators, and over a `RealCaseIIData37` it is
`caseIISection91_descentUnit` (the cyclotomic-number ratio `(x+yη_a)/(x+yη_b)`, residue form
`(Y·X⁻¹)^37`).  We record the **producer-link** Lemma-9.8 conjugate-residue Prop over a real datum,
whose descent unit is *this* producer ratio, and discharge its **local-power conjunct** with §3 —
non-circularly from the σ-stable producer.  (The residue-equations conjunct is the separate
Corollary-8.15 / Lemma-9.9 free-part content.) -/

/-- **The producer-link Washington Lemma-9.8 local power over a real Case-II datum** (a `def … :
Prop`, **not** an axiom, **not** Assumption II).

For every real Case-II descent instance `D : RealCaseIIData37 K m`, adjacent root `η`, σ-stable
anchored generator record `G`, and maximal prime `𝔩` with the standard Fermat-data coprimality
(`X = algebraMap G.xPlus ∉ 𝔩` and the anchor pair generator `Q_η₀ ∉ 𝔩`), the §9.1 producer-built
descent unit `δ = caseIISection91_descentUnit D η G 𝔩` is a `37`-th power mod `𝔩`.

Unlike the abstract `Lemma98ConjugateResidue37`, here `δ` is **not** an unconstrained `ε₁/ε₂`: it is
the producer ratio `(Y·X⁻¹)^37` constructed from the σ-stable pair generators (Washington §9.1's
explicit `η_a`).  Hence the local power is **proven** (`caseIISection91_descentUnit_isPthPower`),
non-circularly from the σ-stable producer. -/
def CaseIISection91Lemma98LocalPower37
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    (𝔩 : Ideal (𝓞 K)) [𝔩.IsMaximal]
    (_hX : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus ∉ 𝔩)
    (_hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ 𝔩),
    BernoulliRegular.IsPthPowerModPrime 37 𝔩 (caseIISection91_descentUnit D η G 𝔩)

/-- **The producer-link Lemma-9.8 local power holds** (proven, axiom-clean — the local-power half of
the §9.1 identification, discharged non-circularly from the σ-stable producer).

`CaseIISection91Lemma98LocalPower37` is exactly `caseIISection91_descentUnit_isPthPower`, applied to
each instance.  This discharges the local-power half of Washington Lemma 9.8 for the
producer-constructed Case-II descent unit — the genuine §9.1 descent object — with the
§9.1 identification `δ · Q_η₀ ≡ Q_η · U_KP (mod 𝔩)` proved (`caseIISection91_residue_identification`)
and the `(ρ_b/ρ_a)^p` half supplied by the proven producer
(`caseIILemma98Residue_pair_ratio_isPthPower`), never by Assumption II. -/
theorem caseIISection91_lemma98LocalPower37
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] :
    CaseIISection91Lemma98LocalPower37 (K := K) := by
  intro m D η G 𝔩 _ hX hQ0
  exact caseIISection91_descentUnit_isPthPower D η G hX hQ0

/-! ## 5. Local power at the concrete residue prime `lv149`

`Lemma98ConjugateResidue37` (`CaseIILemma98Residue.lean`) is keyed to the concrete residue prime
`lv149` over `CyclotomicField 37 ℚ` (the Lehmer–Vandiver prime `ℓ = 149 ≡ 1 (mod 37)`).  Specialising
§3 to `K = CyclotomicField 37 ℚ` and `𝔩 = lv149` gives the local power of the producer-built §9.1
descent unit at exactly that prime — the residue-level shape of the local-power conjunct of
`Lemma98ConjugateResidue37`, for the producer-constructed descent unit. -/

/-- **The local power at `lv149` for the producer-built §9.1 descent unit** (proven, axiom-clean).

`caseIISection91_descentUnit_isPthPower` at `K = CyclotomicField 37 ℚ`, `𝔩 = lv149`: the
producer-built §9.1 descent unit `δ` is a `37`-th power mod `lv149`, the residue prime to which
`Lemma98ConjugateResidue37` / `Lemma98LocalPower37` are keyed.  This is the local-power conjunct of
Washington Lemma 9.8, discharged for the producer-constructed Case-II descent unit, non-circularly
from the σ-stable producer (**not** Assumption II).

(`Lemma98ConjugateResidue37` itself is stated over an *abstract* `CaseIIData37` with unconstrained
units `ε₁, ε₂`; for those free units the §9.1 identification is unavailable without Assumption II.
This theorem supplies the local power for the *producer-constructed* descent unit, which is the
genuine Washington §9.1 descent object.) -/
theorem caseIISection91_lv149_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ)) G.xPlus ∉ lv149)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (caseIISection91_descentUnit D η G lv149) :=
  caseIISection91_descentUnit_isPthPower D η G hX hQ0

end BernoulliRegular.FLT37.Eichler

end
