# T-PIC-F-001c: Assembly — `κ ∘ σ̄ = id` at Pic⁰ level

**Status**: DONE (`picZeroOfPoint_sigmaBar` in
`HasseWeil/Curves/Miller.lean`, axiom-clean — uses `picZeroIsoE` as
the equivalence)
**Silverman**: III.3.4(a) (full bijection)
**Module**: `HasseWeil/Curves/PicZero.lean` and `EC/IsogenyAG/HomProperty.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: easy
**Phase**: F (final assembly for σ̄ injectivity)

## Depends on

- T-PIC-F-001a (existence)
- T-PIC-F-001b (uniqueness)
- T-PIC-A-001 (DONE), T-PIC-B-001 (DONE), T-PIC-A-003 (DONE), T-PIC-A-002 (after assembly)

## Blocks

- T-PIC-F-003 (B-4-003 closure) — provides `h_inj_W₁` witness.

## Statement

The witness needed by `AddHomProperty_of_picZero_witnesses`:

```lean
theorem picZeroOfPoint_picZeroSum
    [W.IsElliptic] [IsAlgClosed F]
    (h_van : ∀ D ∈ projPrincipalSubgroup ⟨W⟩,
              projectiveDivisorSum W D = 0)
    (D : PicProj₀ ⟨W⟩) :
    picZeroOfPoint W (picZeroSumOfWitness W h_van D) = D
```

In words: the composition `κ ∘ σ̄` equals identity on Pic⁰(E).

## Proof approach

Via `Quotient.ind`:

```lean
theorem picZeroOfPoint_picZeroSum h_van D := by
  refine Quotient.inductionOn D fun D₀ => ?_
  -- D₀ : ProjectiveDivisor.degZero
  -- Want: κ(σ(D₀)) = [D₀] in Pic⁰
  -- Equivalently: kappaDivisor (σ(D₀)) ~ D₀.val
  obtain ⟨P, hP⟩ := exists_kappa_form D₀  -- F-001a
  -- hP : D₀.val ~_div kappaDivisor W P
  -- We want P = σ(D₀):
  have h_P_eq_sigma : P = picZeroSumOfWitness W h_van [D₀] := by
    -- Apply σ̄ to both sides of hP, use σ̄ ∘ κ = id (B-003 DONE)
    have h_sigma_eq : projectiveDivisorSum W (kappaDivisor W P) =
                     projectiveDivisorSum W D₀.val := by
      ... -- σ respects ~ via h_van
    rw [projectiveDivisorSum_kappaDivisor] at h_sigma_eq -- B-003
    exact h_sigma_eq.symm
  rw [← h_P_eq_sigma]
  -- Now: κ P = [D₀], which is hP packaged in Pic⁰
  exact (Quotient.sound hP.symm)
```

**Key insight**: F-001a gives existence (some P with D ~ κ(P)); F-001b
gives uniqueness (that P = σ(D)). Combined, they say κ ∘ σ̄ = id.

Wait — F-001b is not actually needed for this lemma! Re-read:
- F-001a says `∃ P, D ~ κ(P)`.
- We then show `P = σ(D)` by applying `σ` to both sides:
  `σ(D) = σ(κ(P))` using σ-respects-~ (which uses A-002, the h_van
  hypothesis). And `σ(κ(P)) = P` by B-003 (DONE).
- So `P = σ(D)`, hence `κ(σ(D)) = κ(P) ~ D`, i.e., `κ(σ(D)) = D` in Pic⁰.

**F-001b is NOT used by F-001c.** F-001b is the **converse direction**
(σ̄ ∘ κ = id at the point level), but B-003 already gives `σ̄ ∘ κ = id` at
the divisor level. So F-001b is needed only to **lift B-003 from divisor
to Pic⁰ level** (which is the "P = Q from κ(P) ~ κ(Q)" direction).

Let me reconsider: σ̄ ∘ κ at Pic⁰ level needs **κ injective**, which is
F-001b. But we don't need that for F-001c (the κ ∘ σ̄ direction).

**So**: F-001c needs only F-001a + B-003 + A-002. **F-001b is needed for
the OTHER half of the bijection** — for σ̄ to be a group iso (which is
what T-PIC-F-002 packages).

For the witness needed by `AddHomProperty_of_picZero_witnesses`,
**only κ ∘ σ̄ = id is required**, which is F-001c. So:

**Updated dependency**: F-001c needs F-001a + A-002 (via h_van) + B-003.
**F-001b is independent** and only needed for T-PIC-F-002 (full bijection
package).

This means: **B-4-003 unconditional needs A-002 + C-003 + F-001a**,
and **NOT F-001b**!!

This is a significant insight: **the worker-K dependency disappears**
for B-4-003, IF F-001a goes through.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.picZeroOfPoint_picZeroSum
```
reports only standard axioms.

## Risks

- **σ-respects-~ step**: requires h_van (which is A-002 / σ vanishes on
  principal). This is the hypothesis already wired through
  `AddHomProperty_of_picZero_witnesses`.

- **B-003 application**: `σ ∘ κ = id` at divisor level is shipped as
  `projectiveDivisorSum_kappaDivisor` (DONE). Application is mechanical.

- **`exists_kappa_form` from F-001a**: the existential needs to be
  unpacked via `Classical.choose` or pattern-matched in tactic mode.

## Progress log

- **2026-04-29**: Critical insight discovered while writing this ticket —
  F-001b is NOT required for B-4-003 unconditional. Only κ ∘ σ̄ = id
  (this direction) is needed; F-001b is for the other direction. **The
  worker-K blocker disappears for B-4-003 unconditional**, conditional
  on F-001a (existence) shipping.
