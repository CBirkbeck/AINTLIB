# Prove Remaining Sorries — Plan

**Goal:** Remove the 3 remaining sorries in the adic spaces formalization.

**Sorries:**
1. `isUnit_canonicalMap_s` (Presheaf.lean:284) — `D'.canonicalMap D.s` is a unit
2. `restrictionMapAlg_continuous` (Presheaf.lean:298) — algebraic restriction map is continuous
3. `IsSheafy.discrete` (StructureSheaf.lean:203) — discrete rings are sheafy

---

## Mathematical Analysis (from Wedhorn §8.1)

### Sorry 1: `isUnit_canonicalMap_s`

**Statement:** If `R(T'/s') ⊆ R(T/s)` then `D'.canonicalMap(s)` is a unit in `presheafValue D'`.

**Wedhorn's proof (Lemma 8.1):** Uses Prop 7.52 on `A⟨T'/s'⟩` — needs full affinoid ring
structure on the presheaf value (PlusSubring, open maximal ideals, etc.).

**Our approach (algebraic, avoids full affinoid machinery):**

1. For every prime `p ⊂ A` with `s' ∉ p`, construct the trivial valuation `v_p ∈ Spa A A⁺`
   with `supp(v_p) = p`. (For discrete `A`, every valuation is continuous and the
   `A⁺` condition is automatic since the trivial valuation takes values in `{0,1}`.)

2. Since `s' ∉ p`, we have `v_p(s') ≠ 0` and `v_p(t') ≤ v_p(s')` for all `t' ∈ T'`
   (trivial since `v_p(s') = 1`). So `v_p ∈ R(T'/s')`.

3. By the inclusion `R(T'/s') ⊆ R(T/s)`: `v_p ∈ R(T/s)`, so `v_p(s) ≠ 0`, i.e., `s ∉ p`.

4. Since this holds for all primes `p` with `s' ∉ p`: `V(s) ⊆ V(s')` in `Spec A`,
   so `s' ∈ √(s)`, i.e., `s'^n ∈ (s)` for some `n`.

5. In `Localization.Away s'`: `algebraMap(s) · algebraMap(a) = algebraMap(s')^n` (a unit),
   so `algebraMap(s)` is a unit.

6. Ring homs preserve units: `canonicalMap(s) = coeRingHom(algebraMap(s))` is a unit
   in `presheafValue D'`.

**Key new infrastructure needed:**
- `Spv.ofPrime p` — trivial valuation at any prime ideal
- `ofPrime_mem_spa_discrete` — membership in `Spa A A⁺` for discrete `A`
- Ideal radical membership: `s' ∈ √(s)` from `∀ p prime, s ∈ p → s' ∈ p`

**Limitation:** Step 1 uses `DiscreteTopology A` (to ensure every prime's trivial valuation
is in `Spa`). For general `A`, would need open maximal ideals or f-adic structure.

**Decision:** Prove for discrete `A` (add `[DiscreteTopology A]` hypothesis). This suffices
for `IsSheafy.discrete`. The general case needs Prop 7.52 on presheafValue (future work).

### Sorry 2: `restrictionMapAlg_continuous`

**Statement:** `restrictionMapAlg D D' h` is continuous from `D.topology` to the
completion topology on `presheafValue D'`.

**For discrete `A`:** Trivial. When `A` is discrete, `I` is nilpotent (since `I^n → 0` in
discrete topology means `I^N = 0`), so `locNhd N = {0}`, making `D.topology` discrete.
Every function from a discrete space is continuous.

**For general `A`:** The proof requires showing that the algebraic lift maps localization
neighborhoods into completion neighborhoods. The key ingredients:
- `D'.canonicalMap` maps `I^n` into the completion neighborhoods of `D'`
- Multiplication by ring-of-definition elements and `canonicalMap(s)^{-1}` preserves neighborhoods
This is a medium-difficulty proof about cross-topology continuity of localization maps.

**Decision:** Prove for discrete `A` (same hypothesis). Leave general case as sorry.

### Sorry 3: `IsSheafy.discrete`

**Statement:** For discrete `A`, `productRestriction A C` is injective for every
rational covering `C`.

**Proof strategy (using Thm 8.28(c)):**

1. **Discrete completions are trivial:** `presheafValue D ≃+* Localization.Away D.s`
   (discrete space is complete, so completion = identity).

2. **Restriction maps are algebraic:** Under the isomorphism, `restrictionMap D D' h`
   corresponds to `IsLocalization.Away.lift s (isUnit...)`.

3. **Covering implies unit ideal:** The rational covering condition, for discrete `A`,
   means the images of `{D_i.s}` generate the unit ideal in `Localization.Away C.base.s`.

4. **Algebraic locality:** If `{s_i}` generate the unit ideal in `R` and `x ∈ R` maps
   to 0 in each `R_{s_i}`, then `x = 0`. (Standard commutative algebra: `s_i^{n_i} x = 0`
   for all `i`, and `∑ a_i s_i^{n_i} = 1`, so `x = 0`.)

**Key issue:** Since `isUnit_canonicalMap_s` and `restrictionMapAlg_continuous` are sorry
for general `A`, the `restrictionMap` used in `productRestriction` is sorry-tainted.
Even in the discrete case, we can't compute with it unless the sorries are resolved.

**Resolution:** Since we're proving the discrete case, we either:
(a) Prove sorries 1 and 2 for discrete `A` first, making `restrictionMap` computable, OR
(b) Bypass `productRestriction` entirely and prove injectivity via a separate construction

We choose **(a)**: make `isUnit_canonicalMap_s` a theorem (removing sorry) at least
for discrete `A`, then the `extensionHom` construction becomes honest.

---

## Implementation Plan

### Task A: Trivial valuation at a prime (AdicSpectrum.lean)

Add `exists_mem_spa_of_prime` that constructs the trivial valuation at any prime ideal
for discrete rings. This generalizes `exists_mem_spa_supp_eq` (which only handles maximal ideals).

Construction: `Valuation.comap (algebraMap (A ⧸ p) (FractionRing (A ⧸ p)) ∘ Ideal.Quotient.mk p) Valuation.one`

### Task B: Prove `isUnit_canonicalMap_s` (Presheaf.lean)

Using Task A + radical ideal argument + localization unit characterization.
Add `[DiscreteTopology A]` hypothesis (or prove without it if possible).

### Task C: Prove `restrictionMapAlg_continuous` (Presheaf.lean)

For discrete `A`: show `D.topology` is discrete, then all functions are continuous.
Infrastructure: `PairOfDefinition.I_nilpotent_discrete`, `locTopology_eq_bot_discrete`.

### Task D: Prove `IsSheafy.discrete` (StructureSheaf.lean)

With Tasks B and C done, the `restrictionMap` is sorry-free for discrete `A`.
Prove injectivity using completion-triviality + algebraic locality of localizations.
