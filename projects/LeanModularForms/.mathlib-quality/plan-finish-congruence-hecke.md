# Plan: Finish CongruenceHecke.lean (eliminate all sorries + errors)

## Goal
Make `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean` build cleanly with
**no sorries, no axioms, no #exit**. Currently 55 errors + 3 pre-existing
sorries blocking compilation. Same for `BlockBijection.lean` (already
builds with 1 pre-existing sorry to eliminate).

## Strategy: Bottom-up from Shimura §3.24 (n=2)

The remaining errors trace back to ONE missing lemma:
`HeckeRing.GLn.Inj.monomial_eval_kronecker` referenced in `T_gen_algebraicIndependent`.

### Math: Shimura Theorem 3.24 (n=2)
For prime p, the local Hecke ring R_p^(2) is the polynomial ring ℤ[T(1,p), T(p,p)].

Key identities (Shimura p. 63):
- (1) T(m) = ∑_{ad=m, a|d} T(a, d)
- (2) T(1, p^k) = T(p^k) − T(p,p) · T(p^{k-2}) for k ≥ 2
- (4) T(p^r)·T(p^s) = ∑_{t=0}^r p^t · T(p^t, p^t) · T(p^{r+s−2t}) for r ≤ s
  - Special case: T(p)·T(p^k) = T(p^{k+1}) + p·T(p,p)·T(p^{k−1})

The proof of (4) embeds R_p^(2) into ℚ[A, B] via 1−T(p)X+pT(p,p)X² = (1−AX)(1−BX),
yielding T(p^m) = (A^{m+1}−B^{m+1})/(A−B). The recurrence follows by algebra.

### Math: Kronecker delta
Using Shimura (4) and (1), every basis coset T(p^k, p^l) (with k ≤ l, hence k+l ≤ 2l)
factors as T(1, p^{l-k}) · T(p, p)^k. Therefore:

**Claim**: `(T(1,p)^{a₁} · T(p,p)^{b₁}) at T(p^{b₂}, p^{a₂+b₂}) = δ_{(a₁,b₁), (a₂,b₂)}`
under hypothesis b₂ ≤ b₁.

**Proof**: Write T(1,p)^{a₁} = ∑_{j=0}^{⌊a₁/2⌋} c_j · T(1, p^{a₁-2j}) · T(p,p)^j
(by Shimura recurrence, c_0 = 1).

Then T(1,p)^{a₁} · T(p,p)^{b₁} = ∑_j c_j T(1, p^{a₁-2j}) · T(p,p)^{j+b₁}
= ∑_j c_j · T(p^{j+b₁}, p^{a₁-j+b₁}) (Shimura (1) inverse).

Coefficient at T(p^{b₂}, p^{a₂+b₂}): need j+b₁ = b₂ AND a₁-j+b₁ = a₂+b₂.
- First → j = b₂-b₁ (need b₂ ≥ b₁; given b₂ ≤ b₁, forces b₁ = b₂, j = 0)
- With j=0, b₁=b₂: a₁ = a₂.
- For (a₁,b₁) = (a₂,b₂): coefficient is c_0 = 1.
- Otherwise: coefficient is 0.

## Tickets

### Phase 0: Foundation (BlockBijection sorry)
- [B-01] BlockBijection.lean:1339 — fill the Shimura Lemma 3.19 sorry
  (lattice projection bijection M' ↔ M' ∩ L)

### Phase 1: Hecke recurrence infrastructure (Shimura Th 3.24)
- [H-01] Define `T_p_pow_recurrence`: T(p)·T(p^k) = T(p^{k+1}) + p·T(p,p)·T(p^{k-1})
  - Refs: Shimura Th 3.24 (4), proof via embedding into ℚ[A,B]
  - Or: prove directly via Hecke convolution (mulMap) on diagonal cosets
- [H-02] Define `T_p_pow_expansion`: T(p)^a = ∑_{j=0}^{⌊a/2⌋} c_j(a) · T(1, p^{a-2j}) · T(p,p)^j
  - By induction on a using H-01
  - With c_0(a) = 1 explicit
- [H-03] Define `T_diag_factor`: T(p^k, p^l) = T(1, p^{l-k}) · T(p, p)^k for k ≤ l
  - Direct: T_diag_scalar_mul + T_elem manipulation

### Phase 2: monomial_eval_kronecker
- [K-01] Add `monomial_eval_kronecker` lemma in CongruenceHecke.lean
  (matching case using H-02 + H-03; non-matching via determinant from
  T_gen_pow_support_qpower already proved)

### Phase 3: Cascade fixes
- [C-01] T_gen_algebraicIndependent now compiles with K-01
- [C-02] product_mem_GL_DC_scalar timeout fix (split rw into smaller steps)
- [C-03] Remaining cascade errors in mulMap_Gamma0_scalar_eq downstream
  (~30 errors of types: invalid coercion, rfl failed, unsolved goals)

### Phase 4: PolynomialRing.lean sorry
- [P-01] Fill `evalHom_injective_two` sorry (PolynomialRing.lean:459)
  Uses K-01 same way as T_gen_algebraicIndependent

### Phase 5: Pre-existing CongruenceHecke sorries
- [S-01] CongruenceHecke.lean:5390 — pre-existing sorry in T_pp_rec proof
  (Shimura Prop 3.33)
- [S-02] CongruenceHecke.lean:2679 + 2837 — content-reduction sorries
  (these may be inside docstrings — verify)

### Phase 6: Final verification
- [V-01] `lake build` succeeds
- [V-02] No sorry/axiom in CongruenceHecke.lean or BlockBijection.lean
- [V-03] No #exit directives

## Estimated effort
- Phase 1 (recurrence infrastructure): ~200 lines, 2-4 hours
- Phase 2 (Kronecker): ~50 lines once Phase 1 done
- Phase 3 (cascades): ~30 small fixes, 1-2 hours
- Phase 4 (PolynomialRing): ~50 lines, 1 hour
- Phase 5 (existing sorries): variable, 2-4 hours
- Total: ~6-12 hours focused work

## References
- Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* §3.2-3.3
  - pp. 60-64 (Theorems 3.20, 3.24)
  - pp. 65-70 (Theorem 3.34, congruence subgroup case)
- Diamond-Shurman, *A First Course in Modular Forms* Chapter 5

## Key codebase touchpoints
- `LeanModularForms/HeckeRIngs/GL2/Basic.lean` — T_pp, T_ad, T_elem definitions
- `LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean` — evalHom infrastructure
- `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean` — main file
- `LeanModularForms/HeckeRIngs/GLn/BlockBijection.lean` — Shimura 3.19
- `LeanModularForms/HeckeRIngs/AbstractHeckeRing/*` — abstract Hecke ring
