# Plan: Finish Remaining Sorries in Hecke Ring Refactor

**Date**: 2026-04-16
**Branch**: `hecke-ring`
**Current state**: `lake build` clean. 11 sorries remain across 4 files, all genuinely blocked on substantial new infrastructure.

## Current Sorry Inventory

| File | Line | Name | Block reason |
|------|------|------|--------------|
| CongruenceHecke.lean | 5287 | `Gamma0_T1p_mul_T1ppow_coprime` | Shimura 3.24(5) at Γ₀(N), needs CRT + Γ₀ degree formulas |
| BlockBijection.lean | 1389 | `heckeMultiplicity_block_embed` (≤ dir) | Shimura 3.19 hard half, needs `slPredEmbed` |
| BlockBijection.lean | 1418 | `heckeMultiplicity_block_embed` (≥ dir) | Needs `heckeMultiplicity_well_defined` (Prop 3.4) |
| PolynomialRing.lean | 1193 | `T_gen_generates_R_p` (general n) | Depends on BlockBijection |
| PolynomialRing.lean | 1204 | `evalHom_injective` (general n) | Depends on BlockBijection |
| Projection.lean | 145 | `scalar_mul_coeff_cons_one_eq_zero` | General-n scalar-shift, needs gen `T_elem_mul_scalar` |
| Projection.lean | 173 | `heckeMultiplicity_firstEntry_ge_p_eq_zero` | Same |
| Projection.lean | 185 | `hecke_coeff_compat_gen` | Depends on BlockBijection |
| Projection.lean | 205 | `evalHom_lift_injective` | Depends on BlockBijection |
| Projection.lean | 313 | (Phase C step) | Depends on earlier |
| Projection.lean | 403 | (Phase C step) | Depends on earlier |

## Two Independent Tracks

The remaining work splits into two disjoint dependency chains:

- **Track 1 (Γ₀(N) level)**: Gamma0_T1p_mul_T1ppow_coprime. Only unblocks the `T_1m_mem_ψ_range` surjectivity for p ∤ N, k ≥ 2. No other sorries depend on it.
- **Track 2 (general-n GL level)**: BlockBijection → Projection → PolynomialRing general-n. A single linear dependency chain.

Both are substantial; either can be tackled first.

## Track 1: Γ₀(N)-level Shimura 3.24(5)

**Target**: `Gamma0_T1p_mul_T1ppow_coprime`
```
T'(1,p) * T'(1, p^k) = T'(1, p^(k+1)) + c_k • T'(p, p^k)
```
where c_k = p+1 if k=1, p if k≥2.

**Strategy**: Direct Γ₀(N)-level proof, mirroring the GL proof in `T_sum_prime_mul_T_ad` (GL2/MultiplicationTable.lean:487) but with Γ₀ degree values substituted. The `shimura_ring_hom` approach is circular (confirmed in `.mathlib-quality/gamma0-T1p-attempt.md`).

### T1-A: `Gamma0_relIndex_eq_Gamma_index_of_coprime` (~200 lines)
**Statement**: For coprime m, N: `[Γ₀(N) : Γ₀(mN)] = [SL₂(ℤ) : Γ₀(m)]`.

**Proof**: Second isomorphism theorem applied to:
1. `Γ₀(m) · Γ₀(N) = SL₂(ℤ)` when gcd(m,N)=1 (CRT-style covering)
2. `Γ₀(m) ∩ Γ₀(N) = Γ₀(mN)` — already available as `Gamma0_inf_eq_of_coprime` at line 3593.

Step 1 uses `Gamma_gcd_eq_mul` (already in file at line 421).

**Dependencies**: none (uses only existing lemmas).

### T1-B1: `HeckeCoset_deg_Gamma0_one_ppow` (~100 lines)
**Statement**: For prime p coprime to N, `deg_{Γ₀(N)}(T'(1, p^k)) = p^(k-1)(p+1)`.

**Proof**: `deg_{Γ₀(N)}(T'(1, p^k)) = [Γ₀(N) : Stab_{Γ₀(N)}(diag(1,p^k))] = [Γ₀(N) : Γ₀(p^k · N)]` (by `stab_diag_eq_Gamma0` which needs to be defined per `docs/plans/2026-04-09-shimura-3-35-infrastructure.md` Phase 1.1) `= [SL₂(ℤ) : Γ₀(p^k)]` (by T1-A) `= p^(k-1)(p+1)` (standard — also needs proof or mathlib lookup).

**Dependencies**: T1-A, `stab_diag_eq_Gamma0` (30-50 lines new), `[SL₂(ℤ) : Γ₀(p^k)]` formula (50 lines, explicit coset representatives).

### T1-B2: `HeckeCoset_deg_Gamma0_scalar_ppow` (~80 lines)
**Statement**: For prime p coprime to N, k ≥ 1:
- `deg_{Γ₀(N)}(T'(p, p^k)) = p^(k-2)(p+1)` for k ≥ 2
- `deg_{Γ₀(N)}(T'(p, p^1)) = 1` (scalar)

**Proof**: Factor `diag(p, p^k) = diag(p,p) · diag(1, p^(k-1))`. Scalar centralizer is all of Γ₀(N). Then apply T1-B1 for `T'(1, p^(k-1))`.

**Dependencies**: T1-B1, `Gamma0_HeckeCoset_deg_scalar` (already exists at line ~5755).

### T1-C: De-privatize GL2 helpers (~20 lines)
Make public in `GL2/MultiplicationTable.lean`:
- `mulSupport_pp_subset` (line 263)
- `D_out1_pp_in_mulSupport` (line 316)
- `heckeMultiplicity_deg_sum_eq` (line 343)

**Dependencies**: none.

### T1-D1: `mulSupport_Gamma0_pp_subset` (~80 lines)
**Statement**: Support of `T'(1,p) * T'(1, p^k)` at Γ₀(N) is ⊆ {`T'(1, p^(k+1))`, `T'(p, p^k)`}.

**Proof**: Transfer via `cosetMap` to GL-level `mulSupport_pp_subset` + `shimura_prop_3_31` (injectivity on coprime-det cosets) to upgrade GL-level support to Γ₀(N)-level.

**Dependencies**: T1-C.

### T1-D2: `D_out1_Gamma0_pp_in_mulSupport` (~50 lines)
**Statement**: `T'(1, p^(k+1))` is in `mulSupport(rep T'(1,p), rep T'(1, p^k))` at Γ₀(N) level.

**Proof**: Construct explicit witnesses `i, j ∈ Γ₀(N)` — needs Γ₀(N) version of `T_diag_rep_decompose` (gives L, R ∈ Γ₀(N) such that `rep(T'(a)) = L · diag(a) · R`). This follows from `Gamma0_exists_diag_rep` style argument.

**Dependencies**: Γ₀(N)-level `T_diag_rep_decompose` (~50 new lines).

### T1-E: Assemble `Gamma0_T1p_mul_T1ppow_coprime` (~150 lines)
**Proof skeleton**: mirror GL-level proof of `T_sum_prime_mul_T_ad`:
1. Support bound (T1-D1) → `mulSupport ⊆ {D'_1, D'_2}`.
2. `mulSupport_pp_subset_explicit` gives multiplicities `m'_1, m'_2`.
3. `HeckeRing.deg_mul` + T1-B values → `m'_1 · p^k(p+1) + m'_2 · deg(T'(p,p^k)) = (p+1) · p^(k-1)(p+1)`.
4. T1-D2 gives `m'_1 ≥ 1`, so nlinarith closes arithmetic to `m'_1 = 1`, `m'_2 = c_k`.

**Dependencies**: T1-A through T1-D.

### Track 1 summary
- Total estimated: **600-700 lines** across 5-7 tickets.
- **Critical path**: T1-A → T1-B1 → T1-B2 → T1-C → T1-D1 → T1-D2 → T1-E.
- Shimura reference: *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), §3.2 Theorem 3.24, p. 63; §3.3 Theorem 3.34 (the level-N analog).

## Track 2: General-n Shimura Theorem 3.20

**Targets**:
- `PolynomialRing.lean:1193` (general-n surjectivity)
- `PolynomialRing.lean:1204` (general-n injectivity)
- `BlockBijection.lean:1389, 1418` (Shimura Lemma 3.19)
- `Projection.lean` (6 sorries)

**Strategy**: Induction on n using Shimura Lemma 3.19 (the projection ψ: R_p^(n) → R_p^(n-1)).

### T2-A: General-n `T_elem_mul_scalar` (~60 lines)
**Statement**: For general n, b : Fin n → ℕ positive DivChain, c > 0:
```
T_elem b * T_elem (fun _ => c) = T_elem (b * (fun _ => c))
```

**Proof**: Mirror `GL2/Basic.lean:270` proof for GL(n). Needs `diagMat_scalar_comm` for general n (likely already exists or trivial).

**Dependencies**: none.

### T2-B: `scalar_mul_coeff_cons_one_eq_zero` (Projection.lean:145) (~50 lines)
**Statement**: `(T_elem (fun _ : Fin (m+1) => p) * x)(T_diag (Fin.cons 1 d)) = 0`.

**Proof**: Mirror `T_mul_T_pp_pow_eval_at_one_zero` in PolynomialRing.lean — scalar shift with `p^1`, target first entry `1`, `p ∤ 1`, scalar mismatch → 0. Uses T2-A.

**Dependencies**: T2-A.

### T2-C: General-n `T_mul_T_scalar_eval_zero_of_not_dvd` helpers (~150 lines)
Port the Inj namespace helpers from n=2 to general n:
- General `T_single_diag_mul_T_scalar`
- General `T_mul_T_scalar_eval_shifted`
- General `T_mul_T_scalar_eval_zero_of_not_dvd`

**Dependencies**: T2-A.

### T2-D: `slPredEmbed` infrastructure (~200 lines)
**Statement**: For σ ∈ SL_{m+1}(ℤ) with first column = e_0, define `slPredEmbed σ ∈ SL_m(ℤ)` by deleting first row/column. Prove:
- It's well-defined (reversible of `slSuccEmbed`).
- Respects multiplication and the fiber structure.

**Proof**: Matrix block computation. `slSuccEmbed` already exists; this is its inverse on the image.

**Dependencies**: none.

### T2-E: BlockBijection ≥ direction (Line 1418) (~100-200 lines)
**Statement**: `heckeMultiplicity_block_embed ≥` direction.

Two sub-approaches:
1. Via `heckeMultiplicity_well_defined` (Shimura Prop 3.4) — needs new proof in Ring.lean (~100-200 lines)
2. Direct via existing `heckeMultiplicity_block_embed_ge_diagMat` + invariance bridge (~30-50 lines if the bridge is available).

**Dependencies**: None for direct approach; `heckeMultiplicity_well_defined` for the other.

### T2-F: BlockBijection ≤ direction (Line 1389) (~300-500 lines)
**Statement**: `heckeMultiplicity_block_embed ≤` direction (harder half).

**Proof** (Shimura p.59):
1. Given σ ∈ SL_{m+1}(ℤ) representing a fiber pair at dim m+1 with cons-1 diagonal
2. Decompose M' = σ · diag(1,a) · ℤ^{m+1} = ℤu_0 ⊕ M where u_0 = σ(e_0)
3. Since c_0 = 1, u_0 ≡ e_0 (mod L), so M = M' ∩ L
4. Build σ_m via `slPredEmbed`, verify fiber condition
5. Map is injective

**Dependencies**: T2-D (slPredEmbed).

### T2-G: `heckeMultiplicity_firstEntry_ge_p_eq_zero` (Projection.lean:173) (~60 lines)
**Statement**: For coset E with first diagonal entry ≥ p, multiplicity `μ(E, T(cons 1 b), T(cons 1 d)) = 0`.

**Proof**: Scalar factoring: E = T(p,...,p) · E'. Scalar shifts all output entries by p, preventing any first-entry-1 output.

**Dependencies**: T2-C.

### T2-H: `hecke_coeff_compat_gen` (Projection.lean:185) (~150 lines)
**Statement**: `evalHom (m+1) p P at T_diag(cons 1 d) = evalHom m p (killCompl P) at T_diag d`.

**Proof**: Shimura Lemma 3.19. Uses T2-F (BlockBijection) + T2-G.

**Dependencies**: T2-F, T2-G.

### T2-I: `evalHom_lift_injective` (Projection.lean:205) (~80 lines)
**Statement**: If rename P at (m+1) evaluates to 0, then P at m evaluates to 0.

**Proof**: Apply T2-H repeatedly to extract coefficient compatibility.

**Dependencies**: T2-H.

### T2-J: Phase C.1/C.2 sorries (Projection.lean:313, 403) (~120 lines each)
**Purpose**: "Scalar element is not a zero divisor", plus the matching weight-induction step.

**Dependencies**: T2-B, T2-H.

### T2-K: `T_gen_generates_R_p` general n (PolynomialRing.lean:1193) (~80 lines)
**Proof**: Induction on n using T2-J (weight induction) + T2-H (ψ projection).

**Dependencies**: T2-I, T2-J.

### T2-L: `evalHom_injective` general n (PolynomialRing.lean:1204) (~80 lines)
**Proof**: Dual of T2-K. Algebraic independence via ψ and zero-divisor lemma.

**Dependencies**: T2-I, T2-J.

### Track 2 summary
- Total estimated: **~1200-1600 lines**.
- **Critical path**: T2-A → T2-B → T2-C → T2-D → T2-F → T2-G → T2-H → T2-I → T2-J → T2-K/L.
- Shimura reference: *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), §3.2 Theorem 3.20, p. 59-60; Lemma 3.19, p. 59.

## Priority / Critical Path Recommendation

Track 1 is smaller and more self-contained (~650 lines for one sorry). Track 2 is larger (~1400 lines for 10 sorries).

**Recommendation**: Start with Track 1 because:
1. Smaller scope.
2. Unblocks the entire `T_1m_mem_ψ_range` chain (critical for Shimura Thm 3.35).
3. The GL-level helpers that need de-privatizing are already there.
4. Phase 0 (PolynomialRing build error at :400) is already fixed.

Then proceed to Track 2 if energy remains.

## Execution Order (suggested single-person sprint, ~4-6 weeks)

**Week 1-2: Track 1 foundations**
- T1-A: Gamma0_relIndex_eq_Gamma_index_of_coprime (~200 LOC)
- T1-C: de-privatize GL2 helpers (~20 LOC)
- T1-B1: deg(T'(1, p^k)) formula (~100 LOC)

**Week 3: Track 1 core**
- T1-B2: deg(T'(p, p^k)) formula (~80 LOC)
- T1-D1: mulSupport_Gamma0_pp_subset (~80 LOC)
- T1-D2: D_out1 witness (~50 LOC, needs Γ₀-level T_diag_rep_decompose)

**Week 4: Track 1 finale**
- T1-E: assemble Gamma0_T1p_mul_T1ppow_coprime (~150 LOC)
- Verify build + no regressions

**Week 5-6 (optional): Track 2 start**
- T2-A, T2-B, T2-C: general-n scalar shift helpers
- Begin T2-D: slPredEmbed

## References

- **Shimura, G.**: *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University Press (1971). §3.2 (pp. 59-64), §3.3 (pp. 65-71). PDF at `/Users/mcu22seu/Documents/GitHub/LeanModularForms-hecke/docs/...Goro Shimura...pdf`.
- Previous attempt report: `.mathlib-quality/gamma0-T1p-attempt.md`
- Original plan: `.mathlib-quality/plan-finish-congruence-hecke.md`
- Infrastructure plan: `docs/plans/2026-04-09-shimura-3-35-infrastructure.md`
- Theorem 3.20 plan: `docs/plans/theorem-3-20-plan.md`

## What's already done (for reference)

- **T_gen_algebraicIndependent**, **evalHom_injective_two**, **monomial_eval_kronecker**: sorry-free in PolynomialRing.lean
- **CongruenceHecke.lean**: only 1 sorry remains (Gamma0_T1p_mul_T1ppow_coprime)
- All **Cluster A & B errors** fixed (started at 55 errors, now 0)
- Helpers moved from CongruenceHecke to PolynomialRing: Inj namespace is the canonical home
- **CoprimeMul.lean group algebra** sorries: both filled
