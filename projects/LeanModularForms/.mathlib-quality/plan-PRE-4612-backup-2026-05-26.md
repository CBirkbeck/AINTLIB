# Development Plan: Generalized Hecke Action for Arbitrary Hecke Pairs

## Goal

Generalize `heckeSlash`, `heckeSlashExt`, `heckeSlash_comp` from `GL_pair 2` to
arbitrary `P : HeckePair (GL (Fin 2) ℚ)`, then bridge `heckeT_p_fun` at level
`Γ₁(N)` to `heckeSlash_gen (Gamma1_pair N)`, unlocking commutativity as a
one-liner from `mul_comm` in the Hecke algebra's `CommRing` instance.

## Current Status (after 2026-04-14 sessions)

**Completed:**
- Generalized `heckeSlash_gen`, `heckeSlash_gen_comp`, `heckeSlash_gen_comm`
  (HeckeActionGeneral.lean, 761 lines)
- GL_pair 2 bridge for SL₂(ℤ)-invariant forms (HeckeT_p_GLpair.lean, 864 lines)
- Step 6 partial: `heckeOperatorExt` + AddMonoidHom + coe_apply
  (HeckeModularForm.lean, +150 lines)
- Step 5 at Γ₁(N) substantial pieces (HeckeT_p_Gamma1.lean, 661 lines):
  - `D_p_Gamma1` double coset
  - `T_p_upper` membership
  - `sigma_p_specific` (explicit Γ₀(N) elt with d=p exactly)
  - `M_∞` definition + value + membership + product equivalence
  - `slash_M_infty_eq_diamond_slash_T_p_lower` — the diamond identity
  - Both distinctness lemmas (upper-upper, M_∞-vs-upper)
  - **T021 done**: `conj_diag_mem_Gamma1_of_mem_GL_pair` — the gcd-using
    conjugation preservation lemma (key for natural `Γ₁(N)` ↪ `GL_pair`)
  - `h_quot_imp_adj_mem_Gamma1` helper for the unused injectivity arg.

**Remaining (blocked — see below):**
- Cardinality `|decompQuot D_p_Gamma1| = p+1`
- Bridge theorem composition
- CommRing instance for `𝕋 (Gamma1_pair N) ℤ`
- One-line commutativity payoff

## 🛑 OBSTRUCTION DISCOVERED (2026-04-14)

**The bridge `heckeT_p_fun = heckeSlash_gen D_p_Gamma1` is FALSE at Γ₁(N)
for p ≢ 1 (mod N).**

Root cause: `adj` maps `D_p_Gamma1 = ⟦diag(1,p)⟧` to a **different** double
coset `D(p,1) = ⟦diag(p,1)⟧` at Γ₁(N) (they coincide at `SL₂(ℤ)` only because
the swap `[[0,-1],[1,0]]` is in `SL₂(ℤ)` but not in `Γ₁(N)`).

Consequently:
- `adj(T_p_upper(b)) = [[p,-b],[0,1]] ∉ D_p_Gamma1` (top-left ≡ p mod N, but
  `D_p_Gamma1` mod N has top-left ≡ 1).
- `heckeSlash_gen ⟦diag(1,p)⟧ · f = ∑_σ f ∣ adj(σ·diag(1,p)) = ∑_σ f ∣
  (diag(p,1) · adj(σ))` sums elements of `D(p,1)`, **not** `D(1,p)`.
- `heckeT_p_fun f = ∑_b f ∣ T_p_upper(b) + f ∣ M_∞` sums elements of `D(1,p)`
  (`T_p_upper(b)`, `M_∞ ∈ Δ₁(N) ⊆ D(1,p)`).

The two sums are over genuinely different sets; they are not equal as
functions.

See `GL2/HeckeT_p_Gamma1.lean:617` for the full analysis and options.

## Path forward (requires architectural decision)

The four options (see `HeckeT_p_Gamma1.lean:617` for details):
1. Use `heckeSlash_gen ⟦diag(p,1)⟧` — but `diag(p,1) ∉ Δ₁(N)`, so this
   coset doesn't exist in `Gamma1_pair N`.
2. Define a non-`adj` variant of `heckeSlash_gen` that sums
   `f ∣ (σ.out · rep)`. Match is automatic. But algebraic structure
   (composition, commutativity) must be re-established.
3. Use a larger Hecke pair whose Δ is closed under `adj`.
4. Restrict to trivial-character forms (still has the same mismatch).

**Suggested**: Option 2 (non-`adj` variant). This is a substantial but
focused refactor of the abstract theory. The existing pieces (T020-T024
infrastructure) remain valuable.

Alternative: bypass `heckeSlash_gen` entirely and prove commutativity
directly, using the CommRing structure as an abstract black-box.

## References

- `docs/plans/hecke-action-generalization.md` — original spec
- Diamond–Shurman, *A First Course in Modular Forms*, §5.2 Prop 5.2.1
  — explicit T_p formula at Γ₁(N) with diamond twist
- Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*:
  - §3.4 Prop 3.30 — abstract Hecke action via slash sum
  - §3.8 — commutativity from anti-involution fixing every double coset
- `GL2/HeckeT_p_GLpair.lean:557` — `tRep_gen_D_p_matches_T_p_reps` (level-1
  template for the bridge proof)
- `GL2/HeckeT_p_GLpair.lean:459` — `card_decompQuot_D_p` (level-1 cardinality
  via degree formula `deg_T_diag_ppow`)
- `GLn/CongruenceHecke.lean:2997` — `instCommRing_Gamma0` (template for Γ₁
  CommRing via Atkin-Lehner anti-involution)

## Mathlib Inventory

| Concept | Status | Action |
|---------|--------|--------|
| `HeckePair`, `decompQuot`, `mulMap` | Local | USE |
| `GL_transposeEquiv 2` | Local | USE |
| `CommRing (𝕋 (Gamma0_pair N) ℤ)` | Local | USE as template |
| `Subgroup.relIndex_le_index` | Mathlib | USE for cardinality bound |
| `Quotient.map'` | Mathlib | USE for natural map |
| `Subgroup.subgroupOf` | Mathlib | USE (already does) |
| `ConjAct.toConjAct` | Mathlib | USE |
| `Fintype.card_le_of_injective` | Mathlib | USE |

## File Structure

- `GL2/HeckeT_p_Gamma1.lean` — extending current 534 lines:
  - T020-T024: cardinality + bridge
- `GL2/Gamma1Pair.lean` or new `GL2/Gamma1CommRing.lean` — T025: CommRing
  instance for `𝕋 (Gamma1_pair N) ℤ`
- `GL2/HeckeT_p_Gamma1.lean` — T026: commutativity payoff
- (Optional) `GL2/HeckeT_n.lean` — replace `heckeT_n_comm` proof with
  one-liner via the abstract algebra (out of scope for this plan)

## Dependency Graph

```
T020 (lower bound: Fin(p+1) ↪ decompQuot)
  └─→ T023 (cardinality = p+1) ─→ T024 (bridge theorem)
T021 (conjugation preservation, gcd-using)              ↓
  └─→ T022 (natural map Γ₁ decompQuot ↪ SL₂ decompQuot)
        └─→ T023                                         ↓
T025 (CommRing for 𝕋(Gamma1_pair N) ℤ)                  ↓
  └─→ T026 (heckeT_p_all_comm via heckeSlash_gen_comm)←─┘
```

## Generality Decisions

- All work at general `N : ℕ` with `[NeZero N]` and `gcd(p, N) = 1`
- `sigma_p_specific` constructed so lower-right entry is exactly `p` (not just
  `≡ p mod N`) — this enables clean factorization in M_∞ membership proof
- `M_infty` defined directly via `mkOfDetNeZero` (not as a product) so that
  `M_infty_val` is `rfl` — separate `M_infty_eq_sigma_mul_T_p_lower` lemma
  bridges to the product form for the diamond identity

## Approach Details

### Cardinality (T020-T023)

**Lower bound (T020)**: Direct adaptation of GLpair `tRep_gen_D_p_matches_T_p_reps`
proof structure (lines 569-707 in HeckeT_p_GLpair.lean). Define
`φ_Gamma1 : Fin(p+1) → decompQuot` via `Classical.choose` from existing
membership lemmas (`T_p_upper_mem_D_p_Gamma1`, `M_infty_mem_D_p_Gamma1`).
Prove injective using `adj_upper_inv_mul_upper_not_mem_Gamma1` and
`adj_M_infty_inv_mul_upper_not_mem_Gamma1`. Conclude
`p + 1 ≤ Fintype.card (decompQuot D_p_Gamma1)` via
`Fintype.card_le_of_injective`.

**Upper bound via natural map (T021-T022)**:
- T021 (key lemma): For `γ ∈ Γ₁(N).H`, if `g⁻¹ γ g ∈ (GL_pair 2).H` (integer
  entries), then `g⁻¹ γ g ∈ (Gamma1_pair N).H`. Proof: extract integer matrix
  `s ∈ Γ₁(N)` for `γ`, extract integer matrix `t` for the conjugate, observe
  `t = !![s 0 0, p·s 0 1; s 1 0 / p, s 1 1]`, check `t ∈ Γ₁(N)` via three
  conditions (top-left ≡ 1 mod N, lower-right ≡ 1 mod N, lower-left ≡ 0 mod N).
  The lower-left needs `p | s 1 0` (from integer entries) AND `s 1 0 ≡ 0 mod N`
  (from `s ∈ Γ₁(N)`); combined with `gcd(p, N) = 1` gives `s 1 0 ≡ 0 mod Np`,
  so `s 1 0 / p ≡ 0 mod N`.
- T022 (natural map): Construct `decompQuot (Gamma1_pair N) (diag) →
  decompQuot (GL_pair 2) (diag)` via `Quotient.map'` with the `Gamma1_pair_H_le_GL_pair_H`
  inclusion. The map is well-defined because `Stab_Γ₁ ⊆ Stab_GLpair` (always).
  Injectivity uses T021: for `γ_1, γ_2 ∈ Γ₁(N).H` with `γ_1⁻¹ γ_2 ∈ Stab_GLpair`,
  T021 gives `γ_1⁻¹ γ_2 ∈ Stab_Γ₁`. (Note: `decompQuot` uses `HeckeCoset.rep`,
  which may differ from `diag(1,p)`; reconcile via conjugation if needed, or
  prove a `card_decompQuot_invariant_under_rep` helper.)

**Combine (T023)**: From T020 (≥ p+1) and T022 (via Fintype.card_le_of_injective
applied to T022 + level-1 cardinality), conclude `= p+1`.

### Bridge theorem (T024)

Mirrors `tRep_gen_D_p_matches_T_p_reps` from HeckeT_p_GLpair.lean line 557.
Uses cardinality (T023) + distinctness lemmas + diamond identity
(`slash_M_infty_eq_diamond_slash_T_p_lower`).

### CommRing for Γ₁(N) (T025)

The transpose anti-involution `g ↦ wgᵀw⁻¹` (with `w = diag(1, N)`) preserves
`Γ₁(N)`: for `g = [[a,b],[c,d]] ∈ Γ₁(N)` (so `a, d ≡ 1 mod N`, `c ≡ 0 mod N`,
`det = 1`), the conjugate is `[[a, c/N], [Nb, d]]`, which has top-left
`a ≡ 1 mod N`, lower-left `Nb ≡ 0 mod N`, lower-right `d ≡ 1 mod N`. Det
preserved by transpose. ✓

Need to construct an `AntiInvolution (Gamma1_pair N)` and verify it fixes every
double coset (Shimura Prop 3.8).

### Final commutativity (T026)

```lean
theorem heckeT_p_all_comm_distinct_via_abstract ... := by
  rw [heckeT_p_fun_eq_heckeSlash_gen_Gamma1, heckeT_p_fun_eq_heckeSlash_gen_Gamma1]
  exact heckeSlash_gen_comm_commRing ...
```
