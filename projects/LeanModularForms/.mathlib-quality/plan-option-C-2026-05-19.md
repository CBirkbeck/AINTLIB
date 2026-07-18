# Plan: Option C — Follow Miyake Exactly via M7-sqfree Refactor

**Date**: 2026-05-19
**Status**: planning (`/develop`)
**Strategy**: Follow Miyake's proof of (4.6.14) verbatim. The proof composes
M6(1) + M7-sqfree (4.6.7) + M6(2) (4.6.6(2)) cleanly **if** M7-sqfree exposes
its internal V_q-preimage `F_q` at the natural level `Γ_1((N·l²)/q)`. The
project's M7-sqfree currently restricts F_q to level `Γ_1(N·l²)` for output
uniformity, losing the natural-level information.

**Fix**: extend M7-sqfree's output type to also expose F_q at level
`Γ_1((N·l²)/q)`, alongside the existing uniform-level g_q.

## Goal

Discharge `miyake_descent_l_prime_gt_one_helper`'s sorry at
`SMOObligations.lean:6833` by directly applying Miyake's argument:

```
slash_sum_at_l'N(h)(z)
  = slash_sum_at_l'³·N(h)(z)              -- M6(1), h at level l'·N
  = Σ_q slash_sum_at_l'³·N(V_q(g_q))(z)   -- linearity (h = Σ V_q(g_q))
  = Σ_q slash_sum_at_(l'³·N/q)(F_q)(q·z)  -- M6(2), N_M6 = l'³·N/q, l_M6 = q
```

Take m-th Fourier coefficient: for Coprime m l', each summand vanishes
(q ∤ m for q ∈ l'.primeFactors).

## References

- **Miyake §4.6** — pp. 158 (4.6.6), 159 (4.6.7), 161-162 (4.6.14).
- **Project's M6(2)** at `SMOObligations.lean:5246`.
- **Project's M6(1)** at `SMOObligations.lean:5172`.
- **Project's M7-sqfree** at `SMOObligations.lean:5697`.
- **M7-sqfree's internal proof** at `SMOObligations.lean:5879+` (where
  F_q is constructed via dichotomy at level Γ_1((N·l²)/q)).

## Why Miyake's Argument Composes

The key insight Miyake uses (and which we missed in our earlier
adversarial pass on the original Option A):

- h is at level Γ_1(l'·N), in modFormCharSpace.
- M6(1) bridges slash sums at l'·N and l'³·N for **h itself** (not for
  individual V_q(g_q) summands). The bridge requires h in
  modFormCharSpace at smaller level Γ_1(l'·N) — which it IS.
- Linearity then redistributes the slash sum over the M7-sqfree
  decomposition h(z) = Σ_q V_q(g_q)(z) at the function level.
- M6(2) applied at smaller level Γ_1(l'³·N/q) gives the identity
  slash_sum_at_l'³·N(V_q(g_q at l'³·N))(z) =
  slash_sum_at_(l'³·N/q)(F_q at l'³·N/q)(q·z).

The level Γ_1(l'³·N/q) is M7-sqfree's INTERNAL F_q level. The current
M7-sqfree statement uniformizes to Γ_1(l'³·N), losing this info.

## What needs to change in M7-sqfree

Current statement (paraphrased, see line 5714):
```
∃ g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k,
  (∀ q ∈ l.primeFactors, g q ∈ cuspFormCharSpace ...) ∧
  ∀ n, qExp(f).coeff n = Σ_{q∣l, q∣n} qExp(g q).coeff (n / q)
```

Strengthened statement:
```
∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
  (F : ℕ → CuspForm ((Gamma1 ((N * l ^ 2) / · )).map (mapGL ℝ)) k),
  -- F q at level Γ_1((N·l²)/q), the V_q-preimage natural level
  (∀ q ∈ l.primeFactors, g q ∈ cuspFormCharSpace ...) ∧
  (∀ q ∈ l.primeFactors, F q ∈ cuspFormCharSpace ...) ∧
  -- F q is the V_q-preimage of g q as functions on ℍ
  (∀ q ∈ l.primeFactors,
    ⇑(HeckeRing.GL2.modularFormLevelRaise ((N · l²)/q) q k (F q).toModularForm') =
      (⇑(g q) : ℍ → ℂ)) ∧
  -- The q-expansion identity (unchanged)
  (∀ n, qExp(f).coeff n = Σ_{q∣l, q∣n} qExp(g q).coeff (n / q))
```

Note: `(N · l²)/q` is type-dependent on `q`. Lean needs care here — we
might use a Sigma type or pair of dependent CuspForms.

Alternative formulation: separate F at varying levels via dependent
sigma, or simply expose F at level `Γ_1((N·l²)/q)` parametrically
per-q.

## Mathlib Inventory

| Concept | Status | Action |
|---------|--------|--------|
| `miyake_4_6_6_level_commute` (M6(1)) | ✅ Exists | USE |
| `miyake_4_6_6_level_commute_delta` (M6(2)) | ✅ Exists | USE |
| `miyake_4_6_7_squarefree_decomp` (M7-sqfree, current) | ✅ Exists | **STRENGTHEN** |
| `qExpansion_one_modularFormLevelRaise_coeff` (V_q qExp) | ✅ Exists | USE |
| `multipass_V_p_slash_descendCoset` | ✅ Exists | USE (for bridging V_p) |
| Function-evaluated-at-qz qExp formula (a_m of z↦f(qz)) | ❓ Check | USE/PROVE |

## File Structure

Modify `LeanModularForms/SMOObligations.lean`:
- Section 1: Strengthen `miyake_4_6_7_squarefree_decomp` to expose F_q at
  natural level. This may add a separate theorem
  `miyake_4_6_7_squarefree_decomp_with_preimage` and keep the existing
  uniform-level statement as a corollary.
- Section 2: Discharge the helper sorry using the strengthened M7-sqfree.

## Dependency Graph

```
miyake_4_6_7_squarefree_decomp_with_preimage (NEW or strengthened)
       │
       └──> miyake_4_6_6_level_commute (M6(1))
       └──> miyake_4_6_6_level_commute_delta (M6(2))
                  │
                  ↓
       miyake_descent_l_prime_gt_one_helper (the existing sorry)
                  │
                  ↓
       miyake_descent_witness_exists
                  │
                  ↓
       miyake_4_6_8_inductive_step (M8)
                  │
                  ↓
       strongMultiplicityOne_axiom_clean
```

## Estimated Effort

| Step | LOC estimate |
|------|--------------|
| Strengthen M7-sqfree to expose F_q | 150-200 |
| Discharge helper sorry using strengthened M7-sqfree | 80-120 |
| **Total** | **~250-320 LOC** |

This is SIGNIFICANTLY smaller than Option B (~500-1000 LOC) and
matches Miyake's actual proof structure.

## Key Risk Assessment

**Risk 1**: M7-sqfree's INDUCTIVE proof structure may not directly
expose F_q at level (N·l²)/q. Specifically, the inductive case (l = q · l')
constructs F_q via dichotomy on the q-filter of f at level N·q²
(not N·l²). The natural F_q level might be N·q (not (N·l²)/q).

**Check**: re-read M7-sqfree's proof. The internal dichotomy at line
5879 gives F at level (M_M7)/q = (N · l²)/q (matching our target).
✓ The level IS (N·l²)/q.

**Risk 2**: Dependent levels in Lean. F at level `Γ_1((N·l²)/q)` for
varying q — needs care with Lean's type system. Workarounds:
- Use Sigma type: `∃ F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 ((N·l²)/q)).map (mapGL ℝ)) k`.
- Or use the level-dependent return type via `letI`/`haveI`.

**Risk 3**: M6(1) bridge requires h ∈ modFormCharSpace at level l'·N
with multiplier l'² ∣ (l'·N)/p. Need to verify l'² ∣ N/p. Have l' ∣ N
(squarefree, primes in N), and Coprime l' p (so l'² Coprime p). Hence
l'² ∣ N iff each prime square of l' divides N. Since l' is squarefree,
l'² = ∏ q² for q ∈ l'.primeFactors. For q² ∣ N requires q²∣N for each
q ∣ l'. Hmm — this requires N to have stronger divisibility than just
"primes of l' divide N".

**Resolution**: Re-check hypotheses. Actually M6(1)'s hypothesis is
`l ∣ N/p` (NOT `l² ∣ N`). For our use, l = l'² and "N" in M6(1) = l'·N
(smaller level), so we need l'² ∣ (l'·N)/p = l'·(N/p). l'² ∣ l'·(N/p)
iff l' ∣ N/p. Now l' ∣ N (squarefree, primes ⊆ N.primeFactors) and
Coprime l' p, so l' ∣ N/p. ✓

## Verification Path

1. Strengthen M7-sqfree (~150-200 LOC). Verify with `lake build`.
2. Write helper proof using strengthened M7-sqfree (~80-120 LOC).
3. Verify the helper compiles + the full SMO chain still compiles.
4. Run axiom check to ensure no new axioms introduced.

## Decision Point

Option C is the SMALLEST scope path forward and follows Miyake's
proof directly. The only required change is strengthening M7-sqfree
to expose its internal V_q-preimage.

The user should approve this path before proceeding.
