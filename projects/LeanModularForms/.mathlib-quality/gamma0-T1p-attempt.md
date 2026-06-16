# Attempt: `Gamma0_T1p_mul_T1ppow_coprime` (CongruenceHecke.lean:5287)

**Date**: 2026-04-15 session
**Status**: REPORTED AS BLOCKED (no code changes committed)

## Goal

Prove (at Γ₀(N) level, p prime coprime to N, k ≥ 1):

```
T'(1,p) · T'(1, p^k) = T'(1, p^(k+1)) + c_k • T'(p, p^k)
```

where `c_k = p+1` if `k = 1`, else `c_k = p`. This is Shimura 3.24(5) at the
Γ₀(N) level (p ∤ N case), a level-N analogue of `T_sum_prime_mul_T_ad`
(LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean:487).

## Attempted approaches

### Approach 1: Transfer via `shimura_ring_hom` (Thm 3.35 surjection) — CIRCULAR

The file already defines a surjective ring hom `φ : 𝕋(GL) →+* 𝕋(Γ₀(N))` via
`shimura_ring_hom` (CongruenceHecke.lean:5671). Applying φ to the GL identity
`T(p) · T(1, p^k) = T(1, p^(k+1)) + c_k · T(p, p^k)` naively gives the target.

**Blocker**: We need `φ(T_ad 1 (p^k)) = T'(1, p^k)` and
`φ(T_ad p (p^k)) = T'(p, p^k)` in 𝕋(Γ₀(N)). These follow from:
- `T_ad 1 (p^k) = T_sum(p^k) - T_pp(p) · T_sum(p^{k-2})` (Shimura 3.24(2))
- `T_ad p (p^k) = T_pp(p) · T_ad 1 (p^{k-1})` (scalar shift)
- `T_sum(p^{k+1}) = T(p) · T_sum(p^k) − p·T_pp(p)·T_sum(p^{k-1})` (Shimura 3.24(6))

Inductively computing `φ` on these requires knowing `φ(T_sum(p^k))` and
`φ(T_ad 1 (p^k))`, but each step of the induction uses the very identity
(Shimura 3.24(5)) we're trying to prove at Γ₀(N) level. CIRCULAR.

### Approach 2: Direct proof at Γ₀(N) level (GL-level proof structure)

Following `T_sum_prime_mul_T_ad` (GL2/MultiplicationTable.lean:487), the proof
structure at Γ₀(N) level would be:

1. **Support bound**: `mulSupport(rep D'_1, rep D'_2) ⊆ {D'_out1, D'_out2}` where
   `D'_out1 = T'(1, p^(k+1))`, `D'_out2 = T'(p, p^k)`.
   - Transfer via `cosetMap N` and use GL-level `mulSupport_pp_subset`
     (GL2/MultiplicationTable.lean:263), then `shimura_prop_3_31` (line 785)
     for coprime-det coset injectivity.
   - `mulSupport_pp_subset` is `private`, needs de-privatization OR redo.

2. **Support non-empty**: `D'_out1 ∈ mulSupport`.
   - Would use `HeckeRing.mem_mulSupport_of_product_mem` with specific
     `h₁, h₂ ∈ Γ₀(N).H`. The GL-level witnesses (`L₁⁻¹`, `R₁⁻¹·L₂⁻¹`) from
     `D_out1_pp_in_mulSupport` don't automatically lie in Γ₀(N) — they come
     from `T_diag_rep_decompose` at GL level, which gives SL₂(ℤ) elements
     that may not be in Γ₀(N).
   - This requires a **Γ₀(N) version of `T_diag_rep_decompose`**, giving
     representatives `L, R ∈ Γ₀(N)` such that `rep (T_diag_Gamma0 N a) = L·diag(a)·R`.
     Such a lemma would need `Gamma0_exists_diag_rep` style argument.

3. **Degree sum**: `m'_1 · deg(D'_out1) + m'_2 · deg(D'_out2) = deg(D'_1) · deg(D'_2)`.
   - By `HeckeRing.deg_mul` + support bound. Needs `heckeMultiplicity_deg_sum_eq`
     analog at Γ₀(N) level (the GL version is `private` in MultiplicationTable.lean:343).

4. **Γ₀(N) degree values**: Need concrete formulas for all four cosets:
   - `deg_{Γ₀(N)}(T'(1, p)) = p + 1`
   - `deg_{Γ₀(N)}(T'(1, p^k)) = p^{k-1}(p+1)`
   - `deg_{Γ₀(N)}(T'(1, p^(k+1))) = p^k(p+1)`
   - `deg_{Γ₀(N)}(T'(p, p^k)) = p^{k-2}(p+1)` for k ≥ 2, `= 1` for k = 1

   These follow from `stab_diag_eq_Gamma0` (line 3770) + index computation
   `[Γ₀(N) : Γ₀(mN)] = [Γ : Γ₀(m)]` when `gcd(m, N) = 1`.

   **This last equality is not yet proved in the codebase.** It requires:
   - `Gamma0(m) · Gamma0(N) = SL₂(ℤ)` (CRT-style product covering)
   - `Gamma0(m) ∩ Gamma0(N) = Gamma0(mN)` for coprime m, N

   The second is `Gamma0_inf_eq_of_coprime` (line 3593) — already exists!
   The first is part of the proof of `Gamma0_deg_coprime_mul` (line 3889)
   but is bundled into a specific statement rather than exposed as a reusable
   index equality lemma.

5. **Extract multiplicities**: Use steps 1-4 + `D'_out1 ∈ mulSupport` to get
   `m'_1 ≥ 1`, then arithmetic (analogous to GL proof's `nlinarith`) to
   conclude `m'_1 = 1` and `m'_2 = c_k`.

**Estimated effort for full approach 2**:
- De-privatize or rewrite `mulSupport_pp_subset`, `D_out1_pp_in_mulSupport`,
  `heckeMultiplicity_deg_sum_eq` — needs careful mulSupport analysis
- Prove Γ₀(N)-version of `T_diag_rep_decompose` — ~50 lines
- Prove Γ₀(N) degree formulas for `T'(1, p^k)` and `T'(p, p^k)` via CRT
  + `stab_diag_eq_Gamma0` + `Gamma0_inf_eq_of_coprime` — ~300-500 lines
- Final proof combining all pieces — ~150 lines

**Total: ~500-700 lines of new infrastructure.**

### Approach 3: Multiplicity equality bridge (Shimura 3.29(5))

Prove directly:
```
∀ g₁ g₂ d : (Gamma0_pair N).Δ,  (all with coprime det),
  heckeMultiplicity (Gamma0_pair N) g₁ g₂ d = heckeMultiplicity (GL_pair 2) g₁ g₂ d
```

Together with GL-level `heckeMultiplicity_values` (GL2/MultiplicationTable.lean:379)
this would immediately give the Γ₀(N) multiplicities.

**Blocker**: This lemma is essentially **Shimura Proposition 3.29(5)** from
his book — a delicate result about left-coset decomposition refinement.
The counterexample in the codebase (CongruenceHecke.lean:660-686) shows that
the "obvious" refinement (same representatives at both levels) is FALSE, so
the proof requires a careful bijection argument via `doubleCoset_eq_of_Gamma0_coprimeDet`.

**Estimated effort**: ~400-600 lines (including the counter-examples avoidance).

## What's readily available (confirmed sorry-free infrastructure)

- `cosetMap N` (line 742): the projection `HeckeCoset(Γ₀(N)) → HeckeCoset(GL)`
- `cosetMap_T_diag_Gamma0` (line 3344): commutes with diagonal cosets
- `cosetMap_mulMap_mem_GL_DC` (line 3355): commutes with mulMap on product
- `shimura_prop_3_31` (line 785): injectivity on coprime-det cosets (both directions)
- `shimura_prop_3_31_surjective` (line 4249)
- `T_sum_prime_mul_T_ad` (GL2/MultiplicationTable.lean:487): the full GL identity
- `T_Gamma0_scalar_mul`, `T_Gamma0_scalar_mul_gen` (line 5117, 5051): scalar mult
- `mulMap_Gamma0_coprime_eq` (line 3481), `mulMap_Gamma0_scalar_eq` (line 4950)
- `T_coprime_mul` (line 4083), `T_bad_mul` (line 1592)
- `Gamma0_deg_coprime_mul` (line 3889): degree multiplicativity for coprime m, n
- `Gamma0_inf_eq_of_coprime` (line 3593), `card_quotient_inf_of_set_mul` (3557)

## Recommendation

Given the effort budget implied by "keep effort focused", the cleanest path
forward is **Approach 2 split into multiple tickets**:

1. **Ticket A**: Expose/prove `Gamma0_relIndex_eq_Gamma_index_of_coprime`:
   `[Γ₀(N) : Γ₀(mN)] = [Γ : Γ₀(m)]` when `gcd(m, N) = 1`.
   (≈200 lines, uses `Gamma0_inf_eq_of_coprime` + product covering)

2. **Ticket B**: Prove Γ₀(N) degree formulas:
   - `HeckeCoset_deg_Gamma0_ppow`: for coprime m, N, `deg_{Γ₀(N)}(T'(1, m))` matches
     the GL-level formula (≈100 lines, uses Ticket A + `stab_diag_eq_Gamma0`)
   - `HeckeCoset_deg_Gamma0_scalar_ppow`: similar for `T'(p, p^k)` (≈80 lines,
     uses scalar centrality + Ticket A)

3. **Ticket C**: De-privatize or rewrite `mulSupport_pp_subset`,
   `D_out1_pp_in_mulSupport`, `heckeMultiplicity_deg_sum_eq` from
   GL2/MultiplicationTable.lean (≈20 lines modification).

4. **Ticket D**: Prove Γ₀(N)-level analogs of support/witness lemmas:
   - `mulSupport_Gamma0_pp_subset`: support inclusion at Γ₀(N) level
     (≈80 lines, uses cosetMap + shimura_prop_3_31)
   - `D_out1_Gamma0_pp_in_mulSupport`: witness at Γ₀(N) level
     (≈50 lines, uses Γ₀(N) version of `T_diag_rep_decompose`)

5. **Ticket E**: Final proof of `Gamma0_T1p_mul_T1ppow_coprime` (≈150 lines,
   combining A-D with arithmetic analogous to GL proof).

**Total effort**: 600-700 lines across 5 tickets.

This is substantially more than a "reasonable amount of code" for a single
proof-filling task. The existing `sorry` documentation already acknowledges
this (CongruenceHecke.lean:5264-5267):
> **Status**: Sorry'd. Filling this requires showing the multiplication
> compatibility of cosetMap on coprime-det cosets, which reduces to a
> multiplicity equality lemma. The proof of that requires the decompQuot
> bijection following from `Gamma_gcd_eq_mul`.

## Current build status (unchanged)

- `CongruenceHecke.lean` builds successfully (1 sorry at line 5287)
- No new code was committed during this attempt
