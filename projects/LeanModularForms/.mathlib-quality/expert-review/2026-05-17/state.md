# Expert-review session state

- Generated: 2026-05-17
- Audience: Senior modular forms expert with Lean/Mathlib knowledge
- Goal of brief: Both blocker + chain audit — unblock T5a-3a-clean's Lean matrix-eval issue AND audit the soundness/structure of the entire SMO chain
- Scope: Full SMO chain audit (Miyake §4.6 chain producing the algebraic Main Lemma)
- Length: Comprehensive (~13 pages)
- Notation convention: Miyake (D_0(N), T(l,m), T(n), Greek for chars)
- Reply received: true (date: 2026-05-17)
- Reply integrated: true (date: 2026-05-17)
- Pass G audit run: 2026-05-17 (saved to `./pass-G-audit.md`)

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Is Miyake's §4.6 chain (4.6.5 → 4.6.6 → 4.6.7 → 4.6.8 → 4.6.12) the right route to formalize SMO algebraically? Alternative: Atkin–Lehner / DS analytic. |
| Q2 | Is the normalisation $p/C_{N,p}$ for $\Phi_p$ standard? Miyake uses $p$ (unnormalised); we chose so that $\Phi_p \circ V_p = \mathrm{id}$. |
| Q3 | Is "slash sum vanishes on $M_k(N, \chi)$ when $\chi$ doesn't factor through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$" a standard fact (reference?) — needed for M5 bundle's $\Gamma_1(N/p)$-invariance on general $f$. |
| Q4 | The $[1,0;0,p]$-conjugation in T6b-coset-inv: $[1,0;0,p]$ is not in $\mathrm{SL}_2(\mathbb{Z})$, but the conjugation entry-computation works and lands in $\Gamma_1(N)$. Sanity check? |
| Q5 | **Lean technique**: What's the correct simp pattern to reduce `Matrix.vecCons a (fun i ↦ b) ⟨0, h⟩` to `a` when the Fin index is built via `Fin.mk`? Failing at T5a-3a-clean's 4 entry equations. |
| Q6 | Existing Lean/Mathlib formalisations of the inter-level descent operator $T_p^{(N)}$ from $M_k(N)$ to $M_k(N/p)$? |
| Q7 | Of the 12 open sorries, which to attack first to unblock the most downstream? Intuition: T5a-0 (CRT for SL_2(Z)) since deepest dep, but T5a-3a-clean might give more momentum if Q5 is resolved. |
| Q8 | Is the multi-pass audit / `/develop` → `/beastmode` workflow right for this work? Audit underestimated matrix-algebra LOC by ~2x and over-claimed mathlib has lemmas it doesn't. |

## Ticket-board snapshot at brief time (12 open sorries)

| # | Ticket name | Status | Depends on |
|---|---|---|---|
| 1 | `int_exists_coprime_adjust` | open | (CRT/Bezout primitives) |
| 2 | `SL2Z_to_SL2_ZMod_surjective` | open | #1 |
| 3 | `descendExtraGamma_exists` (T5a-0) | open | #2 |
| 4 | `descendCosetList_action_upper_tri_clean` (T5a-3a-clean) | open | helpers (proven) — **Lean-blocker focal** |
| 5 | `descendCosetList_action_upper_tri_extra` (T5a-3a-extra) | open | helpers, case algebra |
| 6 | `descendCosetList_action` (T5a-3 / M5a) | open | #4, #5 |
| 7 | `miyake_hecke_descend` (M5 bundle) | open | M5a + M5b/c/d (b/c/d done) |
| 8 | `descendCosetList_slash_sum_rep_invariance` (T6b-coset-inv) | open | H24 (proven), CRT-conjugation |
| 9 | `descendCosetList_slash_sum_commute` (T6b-commute) | open | #8, M5a |
| 10 | `miyake_4_6_6_level_commute_delta` (M6(2)) | open | #9, helpers |
| 11 | `miyake_4_6_7_squarefree_decomp` (M7-decomp) | open | M5, M6 |
| 12 | `miyake_V_p_descend_identity` + `miyake_4_6_8_inductive_step` | open | M5, M6, M7 |

## Stuck points (from §8 of brief)

- 8.1 T5a-3a-clean Lean blocker: `Matrix.vecCons _ _ ⟨0, _⟩` doesn't reduce under simp (Fin.mk pattern not matched).
- 8.2 M5 bundle: character decomposition needed for $\Gamma_1(N/p)$-invariance on general $f$.
- 8.3 T5a-0: standard strong-approximation for SL_2(Z) → SL_2(Z/NZ); recipe given but not executed.
- 8.4 T6b: rep-invariance and slash-sum commutation across levels; conjugation argument with $[1,0;0,p]$ outside SL_2(Z).
- 8.5 M7/M8: routine multi-prime induction once M5+M6 done.

## Reference list (from §2.2 of brief)

- [Miy] Miyake, *Modular Forms*, 2006 (primary)
- [DS] Diamond–Shurman, *A First Course in Modular Forms*, 2005
- [AL] Atkin–Lehner 1970 (cross-validation)
- [Li] Li 1975
- [Shi] Shimura 1971
- [Mathlib] Lean 4 mathlib (snapshot ~early 2026)
