# Master Ticket Board: LeanModularForms → Strong Multiplicity One

*Consolidated 2026-04-17 from `tickets.md` (Bridge+Commutativity Refactor),
`tickets-prop-3-34.md` (Shimura Prop 3.34), `tickets-phase5.md` (Adjoint Theory),
and `tickets-finish-congruence-hecke.md` (CongruenceHecke+BlockBijection).*

*This is the SINGLE source of truth for all ticketed work. Previous separate
ticket files are removed.*

## Overview

The final mathematical goal is **Strong Multiplicity One (Miyake Thm 4.6.12)**:
if f ∈ S_k^0(N, χ) and g ∈ S_k^1(N, χ) are common T(n)-eigenfunctions with the
same eigenvalue for all n coprime to some L, then g is a constant multiple of f.

This is pursued via 5 epics in approximately this order:

- **Epic A** (COMPLETE): Finish CongruenceHecke + BlockBijection (Shimura 3.20, 3.24, 3.35 n=2)
- **Epic B** (COMPLETE): Bridge + Commutativity Refactor (heckeRingHom chain)
- **Epic C** (MOSTLY DONE): Shimura Prop 3.34 (Gamma0MapUnits preservation)
- **Epic D** (ACTIVE, other worker): Hecke Adjoint Theory (Phase 5)
- **Epic E** (OPEN): POST-refactor work → SMO (Phases 6-9)

See `docs/plans/strong-multiplicity-one.md` for the master 9-phase plan and
`docs/plans/plan-prop-3-34.md` for Prop 3.34 design.

## Current totals

| Status | Count | Notes |
|---|---|---|
| Done | 26 | Incl. 8 completed this session |
| Superseded/resolved | 6 | Replaced by cleaner refactor |
| Blocked | 5 | Structural or gated on other epics |
| Open | 15 | Path forward to SMO |

## Reviewer feedback integrated 2026-05-11

A frontier-LLM expert review (`.mathlib-quality/expert-review/2026-05-11/`)
restructured the critical path. Key corrections:

1. **T205-d refocus.** Stop pursuing per-tile balance identities — they are the
   wrong granularity. Pursue a two-step API: a finite-index FD-transport lemma
   (T205-d-API-1) and a Hecke-correspondence adjoint theorem (T205-d-API-2),
   then specialize to α = diag(1,p) for `petN_heckeT_p_diamond_shift_core`.
2. **Main Lemma route corrected.** POST-4 (`mainLemma`) does NOT depend on
   T207. Prove it directly from existing Miyake sieve/conductor/support
   machinery in `Eigenforms/MainLemma.lean` (~12 KLOC already in place).
3. **MATHEMATICAL ERROR removed.** The previous proof plan asserted "newforms
   have a_n = 0 for (n,N) > 1". This is FALSE in general — bad-prime newform
   coefficients are often nonzero. Any proof relying on this is rejected.
4. **Critical-path correction.** POST-5 (nonzero eigenvalue) and POST-3
   (L-functions) are NOT on the Miyake finite-exception SMO critical path —
   they become parallel analytic tracks. The Main Lemma directly handles the
   sparse-support situation that arises from finite-exception agreement.
5. **Spectral theorem (T207).** Use Mathlib's commuting-family eigenspace API,
   not a from-scratch construction.
6. **Status accounting.** Distinguish "consumer wrapper compiles" from
   "foundational theorem proved" — several tickets marked done are conditional
   on T205-d closing.

The Γ₀(N)-pivot, the explicit T_p with diamond twist as the right character-
space operator, and the parking of POST-1 (general-χ abstract ring hom) are
all reaffirmed.

POST-1, reverse support decomposition, and the full Atkin–Lehner involution
remain as project goals (not just architectural cleanup), but are off the
SMO critical path.

## Reviewer feedback integrated 2026-05-11 (T205-d follow-up)

A second-round expert review (`.mathlib-quality/expert-review/2026-05-11-T205d/`)
focused entirely on T205-d. Verified findings and refinements:

1. **Pointwise identity ALREADY uses adjugate.** The existing
   `peterssonInner_slash_adjoint` (line 779) and `peterssonInner_slash_adjoint_coset`
   (line 3730) are both stated with `peterssonAdj α` (the adjugate α* = det(α) α⁻¹),
   not α⁻¹. The reviewer's "scalar misalignment" diagnosis applied to the brief's
   wording, not to the code itself. **Current scaffold is in the recommended form.**

2. **Step 2 must stay determinant/character-free.** State T205-d-API-2 as
   `petN(Σ_r f|r, g) = petN(f, Σ_{r*} g|r*)` over reps of Γ\ΓαΓ vs Γ\Γα*Γ.
   Determinant and character factors enter ONLY at Step 3 specialisation.

3. **Layers 5–8 of the old 8-layer chain are formally superseded.** Keep only:
   triple-product identity (Layer 2), σ_p/diamond-coset permutation (Layer 3),
   reusable FD/iUnion lemmas. Decommission M_∞ stockpile, iUnion bookkeeping,
   branch closure.

4. **Step 3 (specialisation to diag(1,p)) is NOT mechanical.** diag(p,1) is
   NOT the same Γ₁(N)-double coset as diag(1,p). Central scalar matrices
   act by λ^{k-2}, not trivially. Must use σ_p Q-permutation + triple-product
   identity + diamond unitarity ⟨p⟩* = ⟨p⟩⁻¹.

5. **Alternative routes ruled out.** Atkin–Lehner–Li orthogonality circular
   w.r.t. T205-d; U_p decomposition is a bad-prime tool, not a good-prime
   substitute. Direct adjugate/Petersson correspondence is the cleanest path.

6. **Index of `Gamma_p_α` verified correct.** Defined as `conjGL Γ₁(N) α ⊓ Γ₁(N)`
   — symmetric intersection. For α = diag(1,p), p ∤ N, [Γ₁(N) : Γ_p(α)] = p+1
   (Shimura Prop 3.32), matching the full T_p correspondence. Reviewer's
   "Risk 3" (index p vs p+1) confirmed non-issue.

7. **Revised scale estimate.** With adjugate form + reuse of existing
   `peterssonInner_slash_adjoint`: 150–300 LOC for the new pointwise/aggregate
   algebra, plus a few hundred more for the specialisation. Lower than the
   500–1000 LOC originally budgeted.

8. **New sub-tickets added below**: T205-d-API-2-INT (integrated domain-level
   adjoint, mostly an API wrapper around existing theorem) and
   T205-d-API-2-DC (the double-coset assembly — the real content).

## T205-d restructuring landed 2026-05-11 (beastmode)

Concentrated the entire T205-d analytic residual into a single clean named
theorem. After tracing the 14-layer scaffold:

- The OLD sorry was at `petN_heckeT_p_adjoint_standard_form` (line ~17454)
  embedded inside a per-q decomposition + iUnion-form + σ_p reindex chain.
- The NEW sorry is at `petN_heckeT_p_symmetric_form` (line ~17422) which
  states the **DS 5.5.3 symmetric form** directly:
  `petN(T_p f, g) = petN(⟨p⟩ f, T_p g)`.

The bypass goes via `petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form`
(line ~13508), which proves the unsymmetric DS standard form from the
symmetric form via existing `petN_heckeT_p_adjoint_standard_form_via_sum_chain`
+ `h_LHS_dist_eq_RHS_absorbed_from_petN_symmetric_form` machinery.

**Sorry count: unchanged (1).** But the conceptual location is now clean
and the closure path is explicit. Build clean (3092 jobs).

## T205-d-SYMM closure chain — restructured per expert review 2026-05-11

**Status update 2026-05-11**: Second expert review (frontier LLM, DS conventions)
ruled all prior closure paths inadequate as primitive worker targets. The
correct chain is:

1. **T205-d-ADJ-WRAPPER** — light wrapper around existing
   `peterssonInner_slash_adjoint` for a single Hecke representative β
   (Step 1, 30–100 LOC).
2. **T205-d-ADJ-CORR** — finite-correspondence aggregation theorem
   `petN_doubleCoset_adjoint_adjugate` for Γ₁(N), α = diag(1,p)
   (Step 2, 150–300 LOC — this is the real analytic content).
3. **T205-d-DIAMOND-SPEC** — T_p-specific identification of the
   adjugate-side aggregate with `⟨u⟩⁻¹ T_p`, where the σ_p / diamond
   bookkeeping lives (Step 3, 150–250 LOC).
4. **T205-d-UNSYMM** — DS 5.5.3 unsymmetric form
   `petN(T_p f, g) = petN(f, ⟨u⟩⁻¹ T_p g)`, derived from ADJ-CORR +
   DIAMOND-SPEC (Step 4a, 30–50 LOC).
5. **T205-d-SYMM** — DS 5.5.3 symmetric form
   `petN(T_p f, g) = petN(⟨u⟩ f, T_p g)`, derived from UNSYMM + diamond
   unitarity (Step 4b, 30–50 LOC).

**Total: 350–650 LOC.** Acceptance for next worker pass: a compiling
ADJ-CORR theorem for Γ₁(N), α = diag(1,p), or one exact missing
FD/integrability/transversal lemma blocking that theorem.

**Superseded routes** (do NOT pursue):
- `T205-d-API-2-DC-IUNION-M/T/CLOSE` — bundled the analytic correspondence
  step with the σ_p Q-permutation; ADJ-CORR/DIAMOND-SPEC separation is
  cleaner.
- **T205-d-SYMM-DIRECT** — direct monolithic σ_p reindex on the unfolded
  sums is the wrong primitive target.
- Path B (Atkin–Lehner–Li orthogonality) — uses the same analytic adjoint
  infrastructure; not a shortcut.
- Path C (U_p decomposition) — bad-prime theory, does not prove good-prime
  T_p adjoint.

**Critical warning** (from reviewer): the naive map `β_b ↦ β_b'` on
displayed upper-triangular left representatives **does not work**.
Adjugates of a left transversal collapse as left cosets (e.g.
`β_b* = shift(-b) · diag(p,1)` are all in the same left coset). The
bijection lives on transposed correspondence data / right-left quotient
data, not on the displayed reps. The ADJ-CORR ticket parameterises on
both `R` (left transversal for Γ \ ΓαΓ) and `Rstar` (transposed
correspondence data for Γ \ Γα*Γ) precisely to dodge this trap.

**Blocked** (documented with diagnostic):
- POST-1 (general-χ ring hom) — Quot.out structural issue
- POST-2 (heckeT_p_all_comm_distinct refactor) — gated on POST-1
- POST-4 (Newforms.lean:1523) — gated on T207 (Epic D)
- POST-5 (Newforms.lean:1654) — gated on POST-3

---

## Parallel Work Plan

**Up to 4 workers can run in parallel at peak**, limited by file dependencies
(two tickets touching the same file cannot run in parallel) and LSP server load.

### Available parallel tracks NOW (no blockers)

| Track | Ticket | File | Est. LOC | Depends on |
|---|---|---|---|---|
| 1 | **T201** Γ₁(N) fundamental domain | `PeterssonLevelN.lean` (new section) | 80-100 | none |
| 2 | **POST-3** L-function infrastructure | NEW `GL2/LFunction.lean` | 500 | none (Phase 3 complete) |
| 3 | **T205-d** petN heckeT_p adjoint bijection | `AdjointTheory.lean` (~line 1586) | 80-150 | T205-a ✅, triple product ✅ |
| 4 | **T207** spectral theorem (Mathlib API) | `AdjointTheory.lean:1270` (new helpers) | 80-120 | T206 ✅ (scaffold can proceed pre-T205) |

Tracks 1, 2, 3, 4 are independent — different files, no cross-dependencies.
Track 4 can scaffold Mathlib API calls even before T205 closes.

### Tracks that open after current work

After **T201** completes:
- **T202** (petN = ∫ over D_N) — `PeterssonLevelN.lean`
- **T203** (domain shift invariance) — `PeterssonLevelN.lean` — can run parallel with T202

After **T205** closes (critical path unblocks):
- **POST-4** (Newforms.lean:1523) — closes quickly as corollary
- (T208 cleanup of AdjointTheory.lean can run immediately in parallel too)

After **POST-3** completes:
- **POST-5** (Newforms.lean:1654) — Euler product use
- Can run parallel with POST-6 since POST-5 is small.

After **POST-4** + **POST-5** close Phase 6:
- **POST-6** (Miyake Main Lemma) — needs most of Phase 6
- Can be SCAFFOLDED in parallel before (statement + helper lemma tickets).

**POST-7** (SMO) depends on POST-6 + full Phase 6; run LAST.

### Serial choke points

- T205 → any Phase 6 closure (currently biggest blocker for final chain)
- POST-6 must complete before POST-7 (one-person job, ~1000 LOC)

### Recommended initial dispatch (4 parallel workers)

1. **Worker A**: T201 → T202 → T203 → (joins Worker C on T205-d when T203 done)
2. **Worker B**: POST-3 (L-function infrastructure) — runs ~1-2 sessions
3. **Worker C**: T205-d (the hardest sorry) — dedicated 2-4 hour session
4. **Worker D**: T207 Mathlib API scaffold — can start immediately

### File-level contention to avoid

Do NOT run these simultaneously:
- Any two tickets touching `AdjointTheory.lean` (T205-d, T207, T208, POST-4)
- Any two tickets touching `Newforms.lean` (POST-4, POST-5)
- Any two tickets touching `PeterssonLevelN.lean` (T201, T202, T203)

For each file, queue serially.

---

## Cleanup Checkpoints

The `/mathlib-quality:develop` skill inserts cleanup tickets every 3-5 proof tickets
to catch naming/golfing/generality issues while context is fresh. These MUST run
before building further on top:

| Checkpoint | After | File(s) | Ticket |
|---|---|---|---|
| CLEANUP-D1 | T201, T202, T203 | `PeterssonLevelN.lean` | [CLEANUP-D1] |
| CLEANUP-D2 | T205 (+T205-a done) | `AdjointTheory.lean` (sections 1000-1600) | [CLEANUP-D2] |
| CLEANUP-D3 | T207 | `AdjointTheory.lean` (full, ≈ T208) | [CLEANUP-D3 / T208] |
| CLEANUP-E1 | POST-3 | `GL2/LFunction.lean` (or wherever) | [CLEANUP-E1] |
| CLEANUP-E2 | POST-4, POST-5 | `GL2/Newforms.lean` | [CLEANUP-E2] |
| CLEANUP-E3 | POST-6 | `Eigenforms/MainLemma.lean` | [CLEANUP-E3] |
| CLEANUP-FINAL | POST-7 (all done) | Full sweep before PR | [CLEANUP-FINAL] |

Each cleanup checkpoint runs the `/cleanup` procedure (13-item mathlib audit +
golfing) on the specified file(s), per `skills/mathlib-quality/references/golfing-rules.md`.

Defined as explicit tickets below at the relevant epics.

---

# Epic A: Finish CongruenceHecke + BlockBijection (✅ COMPLETE)

*Originally in `tickets-finish-congruence-hecke.md`. All items done 2026-04-16.*

Target: `CongruenceHecke.lean` + `BlockBijection.lean` + `PolynomialRing.lean`
sorry-free at the n=2 level.

### [H-01] Gamma0_T1p_mul_T1ppow_coprime (Shimura 3.24 eq 5 at Γ₀(N)) ✅ done
- **File**: CongruenceHecke.lean
- **Result**: 315 LOC, filled sorry-free via Γ → Γ₀(N) surjection + cosetMap bridge.

### [B-01, B-02] BlockBijection.lean:1389, 1418 (Shimura 3.19 ≤/≥) ⚠️ partial
- **Status**: refactored via `heckeMultiplicity_rep_eq_diagMat_delta` bridge.
  Net sorry count unchanged (2 → 2); cleaner target for future work.
- **See**: memory `project_blockbijection_bridge.md`.

### [K-01] monomial_eval_kronecker ✅ done
- **File**: PolynomialRing.lean (moved from CongruenceHecke.lean:5022)
- **Result**: Full Kronecker delta proof; Inj namespace migrated.

### [C-01 through C-03] CongruenceHecke.lean cleanup ✅ done
- **Result**: 0 errors, 0 sorries.

### [P-01] evalHom_injective_two ✅ done
- **File**: PolynomialRing.lean:459
- **Result**: Filled sorry-free via monomial_eval_kronecker.

### [P-02, P-03] PolynomialRing.lean general-n ⛔ blocked on T2-F
- **Description**: General-n surjectivity/injectivity, blocked by BlockBijection
  ≤ direction (B-01). Acceptable to defer since n=1,2 suffices for SMO.

### [V-01, V-02] Final build check + cleanup ⚠️ ongoing
- **Status**: `lake build` clean; cleanup/audit ongoing as part of other phases.

---

# Epic B: Bridge + Commutativity Refactor (✅ COMPLETE)

*Originally `tickets.md` R001-R009, T020-T026. All done this session (2026-04-17)
via Γ₀(N) route — the original Γ₁(N) abstract-bridge path was structurally blocked
(adj-mismatch of D(1,p)/D(p,1) at Γ₁(N)).*

### [R001] Coset-independence for Hecke sums ✅ done
- **File**: GL2/HeckeActionGeneral.lean
- **Result**: `slash_tRep_gen_of_mem`, `heckeSlash_gen_slash_invariant`,
  `heckeSlash_gen_comp`, `heckeSlash_gen_comm` — all axiom-clean.

### [R002] `tRep_gen_D_p_matches_T_p_reps` + downstream ✅ done
- **File**: GL2/HeckeT_p_GLpair.lean (853L)
- **Result**: `heckeT_p_fun_eq_heckeSlash_gen`, `heckeT_p_fun_comm_of_GL_pair`, `heckeT_p_comm`.

### [R003] Bridge heckeT_n to heckeSlashExt_gen ✅ SUPERSEDED
- **Superseded by**: `heckeRingHom_Gamma0 N k` (HeckeModularForm_Gamma0.lean, 391L)
  and `heckeRingHomCharSpaceOne N k` (HeckeT_p_CharSpace_Comm.lean, 281L).
- **Note**: General-χ ring hom remains blocked (POST-1).

### [R004] Replace `heckeT_n_comm` proof with abstract version ⛔ BLOCKED
- **Blocker**: circular for general χ. Our session built
  `heckeT_p_all_charRestrict_commute_distinct` as a corollary OF the existing
  `heckeT_p_all_comm_distinct`. Breaking the cycle requires direct per-χ
  commutativity, blocked by POST-1.

### [R005] Verify build + cleanup (open)
- Status: build passes; cleanup ongoing.

### [R006] `heckeRingHom k : 𝕋 (GL_pair 2) ℤ →+* End(ModularForm 𝒮ℒ k)` ✅ done
- **File**: GL2/HeckeModularForm.lean (562L, +209 this session)
- **Upgraded**: from AddMonoidHom (original R006) to full RingHom.
- **Key decls**: `heckeSum`, `heckeRingHom`, `heckeRingHom_T_single`.

### [R007] Γ₁(N) Step 5 setup ✅ done
- **File**: GL2/HeckeT_p_Gamma1.lean (732L).
- **Key decls**: `D_p_Gamma1`, `sigma_p_specific`, `M_infty`, `slash_M_infty_eq_diamond_slash_T_p_lower`,
  `Gamma1_pair_H_entry_is_int`, `adj_upper_inv_mul_upper_not_mem_Gamma1`.

### [R008] Γ₁(N) bridge (cardinality + matching) ✅ SUPERSEDED (pivot to Γ₀(N))
- **Rationale**: at Γ₁(N), `adj(T_p_upper(b))` has top-left p ≢ 1 (mod N), so the
  adj factorization fails. Went via Γ₀(N) instead.
- **Achieved via pivot**: `D_p_Gamma0 N p hp`, `T_p_coset_reps_Gamma0_equiv`
  (Fin(p+1) ≃ decompQuot), `heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one`.

### [R009] R003+R004 vs R008 path ✅ RESOLVED
- Went with Γ₀(N) + character-decomposition route.

### [T020] Fin(p+1) ↪ decompQuot D_p_Gamma0 ✅ done (via Γ₀(N) pivot)
- **File**: GL2/HeckeT_p_Gamma0.lean (681L)
- **Key decl**: `T_p_coset_reps_Gamma0_equiv N p hp hpN : Fin (p+1) ≃ decompQuot …`.
- **Approach**: adj-based bijection works at Γ₀(N) since `adj(diag(1,p)) = T_p_lower ∈ D_p_Gamma0`.

### [T021] Conjugation preservation lemma ✅ done (generalized → Shimura Prop 3.34)
- **See Epic C** (P334-B below).

### [T022-T024] Γ₁(N) cardinality + bridge ✅ done (via Γ₀(N) pivot)
- **Achieved**: HeckeCoset_deg_D_p_Gamma0 = p+1, distinctness lemmas,
  `tRep_gen_D_p_Gamma0_matches_T_p_reps` (trivial-χ, with Γ₀(N)-invariant f).

### [T025] CommRing for 𝕋 (Gamma1_pair N) ℤ ⛔ BLOCKED
- **Blocker**: `onHeckeCoset D = D` fails at Γ₁(N) under any obvious anti-involution.
  Adj sends `D(1,p) ↦ D(p,1)` which is a DIFFERENT Γ₁(N)-double coset for p ≢ 1 (mod N).
  Atkin-Lehner `g ↦ wN·gᵀ·wN⁻¹` doesn't preserve Δ₁(N) integrality.
- **Workaround**: Use `CommRing (𝕋 (Gamma0_pair N) ℤ)` (exists) + char decomp.

### [T026] Final commutativity payoff ⛔ blocked on T025/POST-1

### [CLEANUP-2, CLEANUP-3] Cleanup tickets (open)

---

# Epic C: Shimura Prop 3.34 (✅ MOSTLY DONE)

*Originally `tickets-prop-3-34.md`. P334-A through D done. P334-E/F/G partially
done; remaining blockers documented under POST-1.*

### [P334-A] Precise statement + matrix entry lemma ✅ done
- **File**: GL2/Prop334.lean (189L → 373L)
- **Key decls**: `matrix_fin_two_conj_entry_11_mod_eq` + `_00_mod_eq`,
  `N_dvd_adj_mul_mul_entry_11_sub` + `_00_sub`.

### [P334-B] Good-prime case of Prop 3.34 ✅ done
- **File**: GL2/Prop334.lean (+184L)
- **Key decl**: `Gamma0MapUnits_preserved_of_detCoprime` — `CoprimeDet`-form.

### [P334-C] Bad-prime case ❌ skipped (good-prime suffices)

### [P334-D] Assemble full Prop 3.34 ✅ done (via P334-B)

### [P334-E] heckeSlash_gen preservation of modFormCharSpace ⚠️ partial
- **File**: GL2/Prop334_HeckeSlash.lean (283L)
- **Delivered**: wrapping infrastructure + reduction given `hComm` hypothesis.
- **Blocker**: `hComm` itself (Quot.out dependence) — see POST-1.

### [P334-StabSurj] Stabilizer surjectivity (diagonal case) ✅ done
- **File**: GL2/Prop334_StabSurj.lean (298L)
- **Key decl**: `Gamma0MapUnits_surjOn_stab_diag` — for diag(1,k), stab surjects onto (ZMod N)ˣ.

### [P334-HeckeSlashDiag] χ-equivariance of heckeT_p_fun ✅ done
- **File**: GL2/Prop334_HeckeSlashDiag.lean (207L)
- **Key decls**: `heckeT_p_fun_slash_comm_charSpace`,
  `heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial` (trivial-χ target done),
  `heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge` (conditional general-χ).

### [P334-Path1] Explicit slash + χ-equivariance ✅ done (+diagnostic)
- **File**: GL2/HeckeSlashExplicit.lean (273L)
- **Delivered**: `heckeSlash_explicit_D_p_Gamma0` = heckeT_p_fun (definitional);
  χ-equivariance; `M_infty_mem_D_p_Gamma0`.
- **Documented finding**: `heckeSlash_gen D_p_Gamma0 f ≠ heckeT_p_fun f` for
  general χ (Quot.out arbitrary-choice noise).

### [P334-F] heckeRingHomCharSpace for arbitrary χ ⛔ BLOCKED → POST-1
### [P334-G] Refactor heckeT_p_all_comm_distinct via ring hom ⛔ BLOCKED → POST-2

---

# Epic D: Hecke Adjoint Theory (⚠️ ACTIVE)

**Active files**: GL2/AdjointTheory.lean (2643L, 2 sorries), Modularforms/PeterssonLevelN.lean,
PeterssonInner.lean, PSL2Action.lean.

Target: `AdjointTheory.lean` sorry-free. Key theorems:
`peterssonInner_slash_adjoint`, `heckeT_p_adjoint` (T_p* = ⟨p⟩⁻¹ T_p),
`heckeT_n_adjoint`, `heckeT_n_normal`, `simultaneous_eigenform_basis`
(spectral theorem for commuting normal operators).

**Reference**: [DS] §5.5, [Miy] §4.5 (Thm 4.5.4-4.5.5).

## Done (Epic D, 9 tickets)

### [T100a] `diamondOp_petersson_unitary` ✅ done
- **File**: AdjointTheory.lean:711.
- **Notes**: Proved via `petN_slash_invariant`.

### [T100b] `heckeT_n_adjoint_on_charSpace` ✅ done
- **File**: AdjointTheory.lean:1149.
- **Notes**: Proved using `heckeT_n_adjoint` + `petN_smul_right`.

### [T101] GL₂⁺(ℝ) invariance of μ_hyp ✅ done
- **File**: PSL2Action.lean:545.
- **Notes**: `instSMulInvMeasure_GLpos : SMulInvariantMeasure GL(2,ℝ)⁺ ℍ μ_hyp`.
  Used in `peterssonInner_slash_adjoint` (line 664).

### [T103] Prop 5.5.2(a) `peterssonInner_slash_adjoint` ✅ done
- **File**: AdjointTheory.lean:616-664.
- **Notes**: Fully proved for arbitrary measurable set D and α ∈ GL₂⁺(ℝ).
  Uses petersson_slash + measurePreserving_smul + slash_peterssonAdj_eq.

### [T105] Double coset identity algebraic part ✅ done
- **File**: AdjointTheory.lean:373-412.
- **Notes**: `adjointGamma0Rep` constructed, `adjointGamma0Rep_units` proved
  (Gamma0MapUnits(γ₀) = unitOfCoprime(p)⁻¹).

### [T108] `heckeT_n_cusp_isSemisimple_on_charSpace` ✅ done
- **File**: AdjointTheory.lean:1209-1217.
- **Notes**: One-liner from Mathlib's `Module.End.iSup_maxGenEigenspace_eq_top`
  over algebraically closed ℂ.

### [T204] `petN_slash_adjoint_GL2` + `sum_setIntegral_GL2_shift` ✅ done (2026-04-17)
- **File**: AdjointTheory.lean:825, sum_setIntegral_GL2_shift at 795.
- **Notes**: Both ~75 LOC + ~60 LOC, closed sorry-free. Signatures take additional
  hypotheses: `hα_h_inv`, `hα_fd`, `h_int`, `h_α_int`.
  Proof reduces via `setIntegral_SL_tile_fd_eq_fdo`, `sum_SL_tile_eq_fiberwise_PSL_tile`,
  `slToPslQuot_fiberCard_eq`, `setIntegral_Gamma1_fundDomain_PSL_eq_sum`, then applies
  `IsFundamentalDomain.setIntegral_eq`.
  Axiom-clean.

### [T205-a] Per-summand slash adjoint for T_p coset reps ✅ done (2026-04-18)
- **File**: AdjointTheory.lean:1129 (`peterssonInner_slash_adjoint_coset`) and
  :1192 (`peterssonInner_slash_adjoint_coset_right` — right variant via Hermitian).
- **Notes**: ~40 LOC each. Also added supporting lemmas: `peterssonAdj_mul`
  (anti-multiplicativity from `Matrix.adjugate_mul_distrib`),
  `peterssonAdj_mapGL_SL_eq_inv` (adj = inv for SL elements),
  `peterssonInner_slash_adjoint_right` (right-slash version via Hermitian symmetry).
  Axiom-clean.

### [T206] `heckeT_n_adjoint` composite case ✅ done (2026-04-13)
- **File**: AdjointTheory.lean:946.
- **Notes**: Restructured to use strong induction via `Nat.strong_induction_on`.
  Added 8 helper lemmas (lines 917-1170): `heckeT_n_cusp_comm_diamondOp`,
  `heckeT_n_cusp_decomp`, `heckeT_n_cusp_comm`, `diamondOp_cusp_comp`,
  `diamondOp_cusp_one`, `heckeT_n_adjoint_coprime_case`,
  `heckeT_n_cusp_ppow_recursion`, `heckeT_n_adjoint_ppow_case`.
  Three cases: coprime factorization (n = p^v · m), prime (v=1), prime power (v≥2).
  **Proof strategy**: see `docs/plans/strong-multiplicity-one.md` §Phase 5.

**Stale ticket corrections** (2026-04-13 audit):
- T102 (Lemma 5.5.1a domain change): absorbed into T201-T203 (IsFundamentalDomain API)
- T104 (Prop 5.5.2b double coset): absorbed into T204 (petN_slash_adjoint_GL2)
- T106 (heckeT_p_adjoint assembly): absorbed into T205 (petN_heckeT_p_diamond_shift_core)
- T107 (heckeT_n_adjoint general): renumbered as T206
- T109 (spectral theorem): renumbered as T207
- T110 (cleanup): renumbered as T208

## Open — Foundation: IsFundamentalDomain API for Γ₁(N)

### [T201] Prove IsFundamentalDomain for the Γ₁(N) coset tiling
- **Status**: open
- **File**: PeterssonLevelN.lean (or new file)
- **Depends on**: none
- **Parallel**: ✅ **yes — can run NOW in parallel with POST-3, T205-d, T207**
  (different files, no cross-dependencies)
- **Description**: Prove
  ```lean
  theorem isFundamentalDomain_Gamma1_coset_tiling :
      IsFundamentalDomain (imageGamma1 N) D_N μ_hyp
  ```
  where `D_N := ⋃ q : SL(2,ℤ) ⧸ Gamma1 N, q.out⁻¹ • fdo`.
  The three conditions of `IsFundamentalDomain`:
  1. **nullMeasurableSet**: D_N is a finite union of open sets (each q⁻¹ • fdo is open).
  2. **ae_covers**: For τ ∈ ℍ, ∃ g ∈ SL₂(ℤ) with g • τ ∈ fd (from Mathlib's
     `ModularGroup.exists_smul_mem_fd`). Write g = q.out · γ for γ ∈ Γ₁(N). Then
     γ • τ ∈ q.out⁻¹ • fd ⊂ D_N (a.e., modulo the null boundary fd\fdo).
  3. **aedisjoint**: For γ₁ ≠ γ₂ ∈ Γ₁(N), translates γ₁ • D_N and γ₂ • D_N are
     a.e. disjoint. By `fdo_PSL_pairwise_disjoint`, γ₁q₁⁻¹ = ±γ₂q₂⁻¹. Handle
     ±I case: N > 2 gives -I ∉ Γ₁(N); for N ≤ 2, action factors through PSL₂.
- **Subtlety**: The group acting is Γ₁(N) viewed via `mapGL ℝ`, so use `imageGamma1 N`.
  Kernel of action is {±I} ∩ Γ₁(N); trivial for N > 2.
- **Mathlib API**: `IsFundamentalDomain` from `Mathlib.MeasureTheory.Group.FundamentalDomain`,
  `isFundamentalDomain_fdo_PSL` (PSL2Action.lean:402).
- **Estimated**: 80-100 LOC.

### [T202] Relate petN to integral over fundamental domain
- **Status**: open
- **File**: PeterssonLevelN.lean
- **Depends on**: T201
- **Parallel**: ⚠️ **serialize with T201/T203** (same file)
- **Description**: Prove
  ```lean
  theorem petN_eq_setIntegral_fundDomain
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      petN f g = ∫ τ in D_N, petersson k ⇑f ⇑g τ ∂μ_hyp
  ```
  **Proof**: petN f g = Σ_q peterssonInner k fd (f∣q⁻¹) (g∣q⁻¹). Each summand
  = ∫_fd petersson(f,g)(q⁻¹ • ·) dμ = ∫_{q⁻¹ • fd} petersson(f,g) dμ (by
  measurePreserving_smul). Sum of set integrals over a.e.-disjoint sets = integral
  over the union. Use `MeasureTheory.integral_finset_iUnion`.
- **Estimated**: 40-60 LOC.

### [T203] Domain shift invariance for Γ₁(N)-normalizing elements
- **Status**: open
- **File**: PeterssonLevelN.lean (or AdjointTheory.lean)
- **Depends on**: T201
- **Parallel**: ✅ **yes with T202** (same file — serialize if on PeterssonLevelN.lean;
  can parallelize if T203 lives in AdjointTheory.lean)
- **Description**: For α ∈ GL₂⁺(ℝ) that normalizes Γ₁(N), the shifted tiling
  α • D_N is also a Γ₁(N)-fundamental domain:
  ```lean
  theorem isFundamentalDomain_Gamma1_shift
      (α : GL(2,ℝ)⁺) (hα_norm : ∀ γ ∈ Gamma1 N, α * γ * α⁻¹ ∈ Gamma1 N) :
      IsFundamentalDomain (imageGamma1 N) (α • D_N) μ_hyp

  theorem setIntegral_fundDomain_eq_of_Gamma1_invariant
      (h : ℍ → ℂ) (h_inv : ∀ γ ∈ Gamma1 N, h ∘ (γ • ·) =ᵐ[μ_hyp] h)
      (hD : IsFundamentalDomain (imageGamma1 N) D μ_hyp)
      (hD' : IsFundamentalDomain (imageGamma1 N) D' μ_hyp)
      (h_int : IntegrableOn h D μ_hyp) (h_int' : IntegrableOn h D' μ_hyp) :
      ∫ τ in D, h τ ∂μ_hyp = ∫ τ in D', h τ ∂μ_hyp
  ```
  Second theorem follows from Mathlib's `IsFundamentalDomain.setIntegral_eq`.
  First theorem: ae_covers from α being a homeomorphism + D_N being fd + α normalizing Γ₁.
  ae_disjointness: τ ∈ γ₁ • α • D_N ∩ γ₂ • α • D_N implies α⁻¹ • τ ∈ (α⁻¹γᵢα) • D_N,
  and α⁻¹γᵢα ∈ Γ₁ by normalization.
- **Estimated**: 40-60 LOC (leveraging Mathlib's `setIntegral_eq`).

### [CLEANUP-D1] /cleanup on PeterssonLevelN.lean after foundation
- **Status**: open
- **File**: `Modularforms/PeterssonLevelN.lean`
- **Depends on**: T201, T202, T203
- **Type**: cleanup
- **Description**: Run `/cleanup` on the new T201-T203 code. Apply the 13-item
  mathlib audit + golfing rules:
  - No `by exact` wrappers
  - No single-use `have` blocks unless they aid readability
  - Terminal simp must be squeezed (`simp only [...]`)
  - Proper naming (`conclusion_of_hypothesis`)
  - Proof length ≤ 50 LOC (decompose if longer, see `/develop` skill)
  - Docstrings on every public declaration
  - Maximum generality (prefer typeclass bounds over concrete types)
- **Verification**: `lake build`, no new sorries/axioms, `#print axioms` clean.
- **Estimated**: minor edits + potential decomposition of any > 50-LOC proofs.

## Open — Core Adjoint (sorry #1, #2)

**REFOCUSED 2026-05-11 per expert review** — see top of file. The previous
per-tile bijection plan is decommissioned; pursue the two-step API below
(T205-d-API-1 → T205-d-API-2 → T205-d specialization).

### [T205-d-API-1] `isFundamentalDomain_iUnion_smul_of_finiteIndex` (NEW)
- **Status**: open
- **File**: Modularforms/PeterssonLevelN.lean (new section)
- **Depends on**: none (uses Mathlib `IsFundamentalDomain` API and the existing
  `isFundamentalDomain_Gamma1_PSL` from PSL2Action.lean)
- **Parallel**: ✅ yes — independent of existing T205-d scaffold
- **Statement**:
  ```lean
  /-- If `K ≤ Γ₁(N)` has finite index and `D` is a fundamental domain for
  `Γ₁(N)`, then the finite union over a transversal `R` for `K \ Γ₁(N)` is
  a fundamental domain for `K`. -/
  theorem isFundamentalDomain_iUnion_smul_of_finiteIndex
      (hK : K ≤ (Gamma1 N).map (mapGL ℝ))
      (R : Finset (GL (Fin 2) ℝ))
      (hR : IsLeftTransversal K ((Gamma1 N).map (mapGL ℝ)) R)
      (hD : IsFundamentalDomain ((Gamma1 N).map (mapGL ℝ)) D μ_hyp) :
      IsFundamentalDomain K (⋃ r ∈ R, r • D) μ_hyp
  ```
- **Corollaries to expose**:
  - AE-disjointness of the family `{r • D}_{r ∈ R}`
  - NullMeasurableSet of `⋃ r • D`
  - IntegrabilityOn transfer: `IntegrableOn f (⋃ r • D) ↔ ∀ r ∈ R, IntegrableOn f (r • D)`
  - SetIntegral decomposition: `∫_{⋃ r • D} f = ∑ r ∈ R, ∫_{r • D} f`
- **CAVEAT** (per Risk 5 of expert review): **prove the NARROW theorem first**.
  Do NOT generalize to arbitrary measured group actions on arbitrary spaces.
  The project only needs finite-index subgroups of Γ₁(N) acting on ℍ with
  μ_hyp; over-abstraction will balloon LOC. Specialize even further to
  `K = Γ₁(N) ∩ α⁻¹·Γ₁(N)·α` for α ∈ Δ₀(N) if the fully general statement
  proves too expensive.
- **Estimated**: 100-200 LOC.

### [T205-d-API-2-INT] domain-level adjugate slash adjoint (API wrapper)
- **Status**: ✅ effectively DONE (existing `peterssonInner_slash_adjoint`)
- **File**: GL2/AdjointTheory.lean (line 779)
- **Statement** (already proved):
  ```lean
  theorem peterssonInner_slash_adjoint
      (D : Set ℍ) (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
      (f g : ℍ → ℂ) :
      peterssonInner k D (f ∣[k] α) g =
        peterssonInner k (α • D) f (g ∣[k] peterssonAdj α)
  ```
- **Note**: This is the integrated form of the reviewer's "pointwise adjugate
  identity → integral over D" Step 2 input. **Already in adjugate form.** No
  new work needed; T205-d-API-2-DC consumes this directly.
- **Reviewer guidance** (2026-05-11-T205d): "If an existing
  `peterssonInner_slash_adjoint` theorem already states this with α*, use it
  instead of reproving the pointwise calculation."

### [T205-d-API-2-DC-IUNION-M] M_∞-branch iUnion σ_p Q-permutation residual (sub-ticket)
- **Parent**: T205-d-API-2-DC
- **Status**: SUPERSEDED 2026-05-11 by T205-d-ADJ-CORR / T205-d-DIAMOND-SPEC
  split. The σ_p Q-permutation step has been pulled out of the analytic
  correspondence-adjoint theorem (it now lives in T205-d-DIAMOND-SPEC) per
  the second expert review.

### [T205-d-API-2-DC-IUNION-T] T_p_upper(b)-branch iUnion σ_p Q-permutation residual (sub-ticket)
- **Parent**: T205-d-API-2-DC
- **Status**: SUPERSEDED 2026-05-11 by T205-d-ADJ-CORR / T205-d-DIAMOND-SPEC
  split (same reason as IUNION-M).

### [T205-d-API-2-DC-CLOSE] Close T205-d via via_iUnion_residuals consumer (sub-ticket)
- **Parent**: T205-d-API-2-DC
- **Status**: SUPERSEDED 2026-05-11 by T205-d-UNSYMM / T205-d-SYMM closure
  chain (after ADJ-CORR + DIAMOND-SPEC). The via_iUnion_residuals consumer
  bundled too much; the new chain separates analytic correspondence,
  T_p-specific diamond identification, and final symmetric-form closure.

### [T205-d-ADJ-WRAPPER] Hecke-rep wrapper around integrated slash adjoint
- **Status**: DONE 2026-05-11 (beastmode session, ~1 cycle)
- **Result**:
  - `peterssonInner_slash_adjoint_for_heckeRep` at
    `LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` line ~844 (between
    `peterssonInner_slash_adjoint` and `peterssonInner_mapGL_smul_eq_of_slash_invariant`).
    Axioms `[propext, Classical.choice, Quot.sound]`. Full build clean (3550 jobs).
  - `peterssonInner_slash_adjoint_for_heckeRep_per_q` (companion lemma,
    line ~866) — per-`q`-coset form consumable directly by T205-d-ADJ-CORR.
    Combines `peterssonInner_smul_set_eq_slash` (SL-domain swap) with the
    base ADJ-WRAPPER. Axioms `[propext, Classical.choice, Quot.sound]`.
- **(was Step 1 of T205-d-SYMM chain, 2026-05-11)**
- **File**: GL2/AdjointTheory.lean (near existing `peterssonInner_slash_adjoint`)
- **Depends on**: `peterssonInner_slash_adjoint` (✅ existing, integrated DS Prop 5.5.2(b))
- **Parallel**: ⚠️ serialize with T205-d-* family (same file)
- **Statement** (illustrative):
  ```lean
  theorem peterssonInner_slash_adjoint_for_heckeRep
      (β : GL (Fin 2) ℝ) (hβ : ... β is a Hecke representative for diag(1,p) at Γ₁(N) ...)
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (hf : Integrable ... ) (hg : Integrable ... ) :
      ∫ z in FΓ, petersson k (f ∣[k] β) g z ∂μ
        =
      ∫ z in β • FΓ, petersson k f (g ∣[k] peterssonAdj β) z ∂μ
  ```
- **Proof sketch**: light wrapper / specialisation of existing
  `peterssonInner_slash_adjoint` to the Hecke-representative setting.
  Supply only the required integrability hypotheses and the FD form.
  **DO NOT re-prove the pointwise kernel.**
- **Reviewer guidance** (2026-05-11): "If `peterssonInner_slash_adjoint`
  already gives this, the ticket should only produce the
  specialization/wrapper and the required integrability hypotheses."
- **Estimated**: 30–100 LOC.

### [T205-d-ADJ-CORR] Finite-correspondence aggregation: adjugate double-coset adjoint
- **Status**: in_progress (Step 2 of T205-d-SYMM chain, 2026-05-11) — **the real work**
- **Progress 2026-05-11/12** (beastmode session — sorry-free additions):
  1. `peterssonInner_LHS_distributed_summand_to_tile_form` (line ~880):
     per-(`β`, `q`) ADJ-WRAPPER consumer rewriting a single summand of
     `petN_T_p_heckeT_p_LHS_sum_distributed` into tile-translated form.
  2. `petN_heckeT_p_LHS_as_tile_aggregate` (line ~12421): full LHS expansion
     of `petN(T_p f, g)` as a sum over `(q, β)` of `β`-translated tile
     integrals over `fd`, with `peterssonAdj β` on the g-slot.
  3. `petN_heckeT_p_LHS_as_tile_aggregate_g_slot_simplified` (line ~12469):
     applies per-β g-slot identifications. T_p_upper(b) branches now have
     b-INDEPENDENT integrand `petersson k ⇑f (⇑g ∣[k] glMap T_p_lower)`;
     M_∞ branch has integrand `petersson k ⇑f ((⇑g ∣ glMap T_p_upper(0)) ∣
     mapGL ℝ σ_p⁻¹)` (via direct `peterssonAdj_glMap_M_infty_eq`).
  - All axioms `[propext, Classical.choice, Quot.sound]`. Build clean (3550 jobs).
- **Convergence with existing chain**: the existing chain already builds up
  to `petN_heckeT_p_eq_per_alpha_HeckeFD_form` (line ~6664) via a parallel
  route through `slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0` (triple
  product). Both routes reach a per-α aggregate form — mine via direct
  `peterssonAdj_M_infty_eq`, existing via T_p_lower triple product. The
  M_∞-branch g-slot differs (`(g∣T_p_upper(0))∣σ_p⁻¹` vs `g∣T_p_lower`).
- **Remaining work for ADJ-CORR**: aggregate the family of β-translated tiles
  via FD-transport (T205-d-API-1) to identify the result as petN of a
  g-side aggregate. The reviewer's "transposed correspondence data" lives
  here — the σ_p Q-permutation absorption + Γ_p(α) FD union → Γ₁(N)-FD
  multiplicity argument. Existing infrastructure
  (`peterssonInner_iUnion_finite_aedisjoint`, `Gamma_p_α_fundDomain_PSL` FD
  theorem) provides the analytic substrate.
- **File**: GL2/AdjointTheory.lean (new section, replaces old T205-d-API-2-DC content)
- **Depends on**: T205-d-API-1 (✅ FD-transport), T205-d-ADJ-WRAPPER
- **Parallel**: ⚠️ serialize with T205-d-* family (same file)
- **Statement** (illustrative — specialise to Γ₁(N), α = diag(1,p); generalise later only if cheap):
  ```lean
  theorem petN_doubleCoset_adjoint_adjugate
      (Γ := Gamma1 N) (α := diag(1, p))
      (R : Finset (GL (Fin 2) ℝ))
      (hR : R is a left-transversal for Γ \ ΓαΓ)
      (Rstar : Finset (GL (Fin 2) ℝ))
      (hRstar : Rstar is transposed-correspondence data for Γ \ Γα*Γ)
      (f g : CuspForm Γ k) :
      petN (∑ β ∈ R, f ∣[k] β) g
        =
      petN f (∑ β' ∈ Rstar, g ∣[k] β')
  ```
- **Proof sketch**:
  1. Expand the LHS via `peterssonInner_slash_adjoint_for_heckeRep` per β.
  2. Sum the tile-shifted integrals over β; apply T205-d-API-1 (FD transport)
     so the family `{β • FΓ}_β` tiles a Γ-FD covered by Rstar.
  3. Identify the aggregated g-slot sum as `∑_{β' ∈ Rstar} g ∣[k] β'` via
     the transposed correspondence data.
- **CRITICAL** (per reviewer 2026-05-11):
  - `Rstar` is **transposed correspondence data**, NOT the naive image
    of `R` under adjugation. At level 1 already, `β_b* = shift(-b)·diag(p,1)`
    are all in the same left coset, so a literal `β_b ↦ β_b'` left-rep
    map cannot exist. The aggregation lives on right-left quotient data.
  - Phrase `Rstar` parametrically — let the worker prove the right
    transversal version first if needed, then convert.
- **Acceptance**: theorem above for Γ = Γ₁(N), α = diag(1,p) suffices.
  Do NOT block on general α ∈ Δ₀(N).
- **Risks** (per reviewer):
  - Underestimating the AE-disjointness / integrability discharge of the
    finite tile family. Separate these into wrappers around T205-d-API-1
    rather than fold into this proof.
- **Estimated**: 150–300 LOC.

### [T205-d-DIAMOND-SPEC] T_p-specific identification: adjugate aggregate ↔ ⟨u⟩⁻¹ T_p
- **Status**: open (Step 3 of T205-d-SYMM chain, 2026-05-11)
- **File**: GL2/AdjointTheory.lean
- **Depends on**: T205-d-ADJ-CORR, existing diamond/T_p infrastructure
  (`heckeT_p_comm_diamondOp`, `slash_diamond_inv_M_infty_eq_T_p_lower_epsilon`,
  `slash_M_infty_eq_diamond_slash_T_p_lower_factor`, Gamma1QuotEquivOfGamma0, ...)
- **Parallel**: ⚠️ serialize with T205-d-* family (same file)
- **Statement** (illustrative):
  ```lean
  theorem heckeT_p_adjugate_correspondence_eq_diamond_inv_T_p :
      (∑ β' ∈ Rstar, g ∣[k] β')
        =
      (diamondOp u⁻¹ (heckeT_p p g))   -- or equivalent T_p∘⟨u⟩⁻¹ form
  ```
  where `u = p ∈ (ℤ/N)^×` and `Rstar` is the transposed correspondence
  data of T205-d-ADJ-CORR specialised to α = diag(1,p).
- **Proof sketch** (per reviewer 2026-05-11):
  - Identify the adjugate double coset Γαdiag*Γ with the original
    T_p-double-coset after the `⟨u⟩⁻¹` correction.
  - This is **where σ_p, the Γ₀/Γ₁ quotient action, and the triple-product
    identities belong** — they should NOT be mixed into ADJ-CORR.
  - Organise at the level of **double-coset / transversal equality**, not as a
    naive map `b ↦ b'` on displayed upper-triangular left reps.
  - If an explicit map is unavoidable: **first prove a right-transversal
    version, then convert to the existing left-transversal Hecke operator.**
- **Warning** (from reviewer): the example
  ```
  β_b* = (diag(p, -b; 0, 1)) = T^(-b) · diag(p, 0; 0, 1)
  ```
  showing adjugates collapse as left cosets is a sign that **the indexing
  object is wrong** if the proof tries to map displayed left reps directly.
- **Estimated**: 150–250 LOC.

### [T205-d-UNSYMM] DS 5.5.3 unsymmetric form (Step 4a)
- **Status**: open (Step 4a of T205-d-SYMM chain, 2026-05-11)
- **File**: GL2/AdjointTheory.lean (near `petN_heckeT_p_symmetric_form`)
- **Depends on**: T205-d-ADJ-CORR, T205-d-DIAMOND-SPEC, T205-d-ADJ-WRAPPER
- **Parallel**: ⚠️ serialize with T205-d-* family (same file)
- **Statement**:
  ```lean
  theorem petN_heckeT_p_adjoint_standard_form
      (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      petN (heckeT_p p f) g = petN f ((diamondOp u⁻¹) (heckeT_p p g))
  ```
  (or the equivalent canonical orientation depending on project's diamond
  convention; reviewer notes both are equivalent modulo
  `heckeT_p_comm_diamondOp`).
- **Proof sketch**: chain T205-d-ADJ-CORR (specialised to α = diag(1,p))
  with T205-d-DIAMOND-SPEC, then unfold T_p as `∑_β slash β` on both sides.
- **Note**: this is the **non-circular target**. Going via this route
  rather than directly through `petN_heckeT_p_symmetric_form` ensures
  the unsymmetric/canonical form is independently established before the
  symmetric form is derived from it.
- **Estimated**: 30–50 LOC (light closure once ADJ-CORR + DIAMOND-SPEC land).

### [T205-d-API-2-DC] double-coset assembly into adjugate correspondence (NEW)
- **Status**: open
- **File**: GL2/AdjointTheory.lean (new section)
- **Depends on**: T205-d-API-1 (✅ done), T205-d-API-2-INT (✅ existing)
- **Parallel**: ⚠️ serialize with T205-d, T207 (same file)
- **Statement**:
  ```lean
  /-- Adjugate Hecke-correspondence adjoint at Γ₁(N), determinant/character-free. -/
  theorem petN_doubleCoset_adjoint_adjugate
      (α : GL (Fin 2) ℚ) (hα : α ∈ Δ₀ N)
      (R : Finset (GL (Fin 2) ℝ))     -- reps for Γ₁(N) \ Γ₁(N) α Γ₁(N), size p+1
      (Rstar : Finset (GL (Fin 2) ℝ)) -- reps for Γ₁(N) \ Γ₁(N) α* Γ₁(N)
      (hR : IsDoubleCosetRepFamily ((Gamma1 N).map (mapGL ℝ)) (mapGL ℝ α) R)
      (hRstar : IsAdjugateRepFamily ((Gamma1 N).map (mapGL ℝ)) (mapGL ℝ α) R Rstar)
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      petN (∑ r ∈ R, slash k r f) g =
        petN f (∑ rstar ∈ Rstar, slash k rstar g)
  ```
- **Proof sketch**:
  1. Expand petN as Σ_q ∫_{fd} (·)|_k q⁻¹ ⋅ (·)|_k q⁻¹ dμ.
  2. For each q-coset and each r ∈ R, apply `peterssonInner_slash_adjoint_coset`
     (T205-a, ✅ done) to transfer the adjoint into the g-slot, giving an integral
     over r • q⁻¹ • fd with g-slot = g ∣[k] peterssonAdj r.
  3. Reindex r over the double-coset transversal, then apply T205-d-API-1
     (FD-transport, ✅ done) to identify ⋃_r r • fd with a Γ_p(α)-FD.
  4. Use the Γ₁(N)/Γ_p(α) coset transversal of size p+1 to reorganise the
     g-slot sum as Σ_{r* ∈ R*} g|_k r*.
- **DEFENSIVE NOTES** (per Risks of expert review):
  - **NO determinant/character factor** at this layer.
  - Use only the existing `peterssonInner_slash_adjoint` and
    `peterssonInner_slash_adjoint_coset` for the per-tile transfer.
  - Keep narrow: Γ₁(N), α ∈ Δ₀(N). Do NOT generalise to arbitrary
    congruence subgroups or arbitrary α ∈ commensurator.
- **Estimated**: 150–250 LOC.
- **Reviewer guidance** (2026-05-11-T205d): "Consume finite-index FD transport;
  domain-level slash adjoint; finite-sum linearity; integrability preservation
  for cusp forms under slash by Hecke representatives."

### [T205-d-API-2] `petN_doubleCoset_adjoint` (NEW)
- **Status**: open — split into T205-d-API-2-INT (✅) and T205-d-API-2-DC (open)
- **File**: GL2/AdjointTheory.lean (new section, replaces current T205 scaffold)
- **Depends on**: T205-d-API-1, `peterssonInner_slash_adjoint` (DS Prop 5.5.2(a), ✅ done)
- **Parallel**: ⚠️ serialize with T205-d (same file)
- **Statement**:
  ```lean
  /-- Petersson adjoint for a finite double-coset correspondence at level Γ₁(N). -/
  theorem petN_doubleCoset_adjoint
      (α : GL (Fin 2) ℚ)
      (hα : α ∈ commensurator ((Gamma1 N).map (mapGL ℚ)))
      (R : Finset (GL (Fin 2) ℝ))      -- reps for Γ \ ΓαΓ
      (Rstar : Finset (GL (Fin 2) ℝ))  -- reps for Γ \ Γα*Γ
      (hR : IsDoubleCosetRepFamily ((Gamma1 N).map (mapGL ℝ)) (mapGL ℝ α) R)
      (hRstar : IsAdjugateRepFamily ((Gamma1 N).map (mapGL ℝ)) (mapGL ℝ α) R Rstar)
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      petN (∑ r ∈ R, slash k r f) g =
        petN f (∑ rstar ∈ Rstar, slash k rstar g)
  ```
- **Proof sketch**: Apply T205-d-API-1 with `K = Γ ∩ α⁻¹Γα` (the Hecke
  intersection subgroup, which is finite-index by commensurability). The
  union `⋃_{r ∈ R} r • D` is then a K-fundamental domain. Use the existing
  single-slash adjoint `peterssonInner_slash_adjoint` (Theorem 5.14 in
  review brief) on each summand, with the transversal absorbed into the
  domain reindexing.
- **DEFENSIVE NOTES** (per Risks 2, 3 of expert review):
  - **Risk 2 / scalar normalization**: with slash convention
    `(f|k α)(τ) = det(α)^(k-1) (cτ+d)^(-k) f(ατ)`, the adjugate α* is
    NOT interchangeable with α⁻¹ without tracking scalar factors.
    Reuse `peterssonInner_slash_adjoint` rather than recomputing scalars.
  - **Risk 3 / non-normalizing matrices**: Hecke representatives like
    diag(1,p) do NOT normalize Γ₁(N). Use the intersection K = Γ ∩ α⁻¹Γα,
    not Γ itself. The FD is for K (the intersection), not for Γ.
- **Estimated**: 200-300 LOC.

### [T205-d-SYMM] DS 5.5.3 symmetric form closure (Step 4b)
- **Status**: open (Step 4b of T205-d-SYMM chain, 2026-05-11) — sole remaining
  sorry on SMO critical path at `petN_heckeT_p_symmetric_form` (AdjointTheory.lean
  ~line 17422).
- **Progress 2026-05-13 (matrix-content layer beastmode session)** — 22 concrete
  sorry-free additions building the σ_p Q-permutation matrix layer:
  1. `adjointGamma0Rep_mul_sigma_p_mem_Gamma1` — γ₀ · σ_p ∈ Γ₁(N) (concrete proof)
  2. `gamma1_of_gamma0_sigma_p` — named Γ₁(N) element γ_1 := γ₀ · σ_p
  3. `gamma1_of_gamma0_sigma_p_coe` — SL coe definitional unwrap
  4. `sigma_p_inv_eq_gamma1_inv_mul_gamma0` — σ_p⁻¹ = γ_1⁻¹ · γ₀ (SL identity)
  5. `adjointGamma0Rep_mul_M_infty_eq_gamma1_mul_T_p_lower` — γ₀ · M_∞ = γ_1 · T_p_lower (ℚ)
  6. `glMap_M_infty_eq_mapGL_sigma_p_mul_glMap_T_p_lower` — ℝ-lift of M_∞ = σ_p · T_p_lower
  7. `mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul` — set-level Q-perm
  8. `mapGL_sigma_p_inv_smul_M_infty_smul_set_eq_T_p_lower_smul` — inverse set-level
  9. `M_infty_iUnion_eq_mapGL_sigma_p_smul_T_p_lower_iUnion` — iUnion Q-perm
  10. `T_p_lower_iUnion_eq_mapGL_sigma_p_inv_smul_M_infty_iUnion` — inverse iUnion
  11. `peterssonInner_M_infty_iUnion_eq_sigma_p_slash` — pet-level Q-perm
  12. `peterssonInner_T_p_lower_iUnion_eq_sigma_p_inv_slash` — inverse pet-level
  13. `coe_diamondOp_cusp_eq_slash_sigma_p` — σ_p slash-as-diamond
  14. `coe_diamondOp_inv_cusp_eq_slash_adjointGamma0Rep` — γ₀ forward slash-diamond
  15. `slash_sigma_p_diamond_inv_cusp_eq` — `(⟨u⁻¹⟩f) ∣ σ_p = f`
  16. `slash_sigma_p_inv_diamond_cusp_eq` — `(⟨u⟩f) ∣ σ_p⁻¹ = f`
  17. `peterssonInner_LHS_M_infty_residual_after_sigma_p` — LHS chain
  18. `peterssonInner_RHS_M_infty_residual_after_sigma_p` — RHS chain
  19. `peterssonAdj_glMap_M_infty_eq_via_gamma1` — γ_1-form M_∞ adjoint
  20. `TileFormIntegralResidual_M_infty_sigma_p_reduced` — **named target** for
      the genuine remaining analytic content (the σ_p-pushed M_∞ residual on
      the T_p_lower-iUnion tile)
  21. `TileFormIntegralResidual_M_infty_of_sigma_p_reduced` — discharger from
      the named target
  22. `SigmaQPermResidual_M_infty_of_sigma_p_reduced` — **end-to-end chain**
      from the σ_p-reduced residual + AE-disjoint hypotheses to the sum-level
      `SigmaQPermResidual_M_infty` (the M_∞-branch sorry target)
  - Build clean: 3550 jobs (full project).
  - Discharges the σ_p Q-permutation infrastructure for the M_∞ branch.
    Remaining work: ADJ-CORR-level analytic content of
    `TileFormIntegralResidual_M_infty_sigma_p_reduced` (150-300 LOC per
    reviewer estimate).
- **File**: GL2/AdjointTheory.lean (at the named theorem)
- **Depends on**: T205-d-UNSYMM, diamond unitarity (T100a ✅), `heckeT_p_comm_diamondOp` (✅)
- **Parallel**: ⚠️ serialize with T205-d-* family (same file)
- **Statement** (current Lean signature):
  ```lean
  theorem petN_heckeT_p_symmetric_form
      (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ N)
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      petN (heckeT_p_cusp k p hp hpN f) g =
        petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
          (heckeT_p_cusp k p hp hpN g)
  ```
- **Proof sketch** (per reviewer 2026-05-11):
  - Take the unsymmetric form
    `petN(T_p f, g) = petN(f, ⟨u⟩⁻¹ T_p g)` (from T205-d-UNSYMM).
  - Apply diamond unitarity `petN(⟨u⟩f, h) = petN(f, ⟨u⟩⁻¹ h)` (with h = T_p g):
    `petN(f, ⟨u⟩⁻¹ T_p g) = petN(⟨u⟩f, T_p g)`.
  - Combine.
- **Note**: ALL existing closure-path code from the previous restructuring
  (the `_from_petN_symmetric_form` consumers in AdjointTheory.lean ~lines
  13508+ etc.) remains valid — this ticket plugs the bottom of the chain.
- **Estimated**: 30–50 LOC.
- **Reviewer guidance**: "Since the current code already has the reverse
  implication, this should be a short closure once the adjugate
  correspondence theorem lands."

### [T205-d] `petN_heckeT_p_diamond_shift_core` (REFOCUSED 2026-05-11, REFINED 2026-05-11-T205d)
- **Status**: open
- **File**: GL2/AdjointTheory.lean (the sorry currently near line 1586)
- **Depends on**: T205-d-API-2-DC
- **Parallel**: ⚠️ serialize with T207, T208 (same file)
- **REVIEWER CORRECTION 2026-05-11-T205d**: Specialisation is NOT mechanical.
  Three non-trivial bookkeeping facts:
  1. diag(p,1) is NOT the same Γ₁(N)-double coset as diag(1,p).
  2. Central scalar matrices act by λ^{k-2}, not trivially (slash convention).
  3. Must use σ_p ∈ (ℤ/N)× Q-permutation + diamond unitarity ⟨p⟩* = ⟨p⟩⁻¹
     to identify the adjugate-side correspondence with the target.
- **Statement** (unchanged):
  ```lean
  petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)
  ```
  i.e., `petN(T_p f, g) = petN(⟨p⟩f, T_p g)`.
- **NEW proof outline** (per expert-review §"Mathematical idea"):
  1. Apply T205-d-API-2 with α = diag(1, p). The double coset
     Γ₁(N) · diag(1,p) · Γ₁(N) has the explicit (p+1)-rep family
     `{T_p_upper(b)}_{b<p} ∪ {T_p_lower}` already in the codebase.
  2. The adjugate is α* = diag(p, 1), with rep family obtained by adjugating
     each member of R.
  3. Identify the adjugate-side operator (slash by `diag(p,1)`-double-coset)
     with the diamond-shifted T_p, using the already-proved triple-product
     identity `T_p_lower = γ₁⁻¹ · T_p_upper(0) · γ₀` (line 1213 of
     AdjointTheory.lean) and diamond unitarity (T100a, ✅ done).
- **Existing supporting infrastructure** (sorry-free, retain):
  - `sum_setIntegral_GL2_shift` (T204, ~75 LOC): GL₂⁺ fundamental-domain tiling
  - `petN_slash_adjoint_GL2` (T204 downstream)
  - `peterssonInner_slash_adjoint_coset` (T205-a, ~40 LOC) + right variant
  - `peterssonAdj_mul`, `peterssonAdj_mapGL_SL_eq_inv`
  - `peterssonInner_slash_adjoint_right` (via Hermitian symmetry)
  - `adjointGamma1Rep` + `adjointGamma1Rep_mem_Gamma1` (explicit γ₁⁻¹ ∈ Γ₁(N))
  - `T_p_lower_triple_product_matrix`: T_p_lower = γ₁⁻¹ · T_p_upper(0) · γ₀
  - `slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0` (CuspForm + ModularForm variants)
- **DECOMMISSIONED approaches** (do NOT pursue further — keep code for
  reference only):
  1. Per-tile bijection (b,q) ↔ (c,σ(q)) on SL₂(ℤ)/Γ₁(N).
     **Reviewer verdict**: wrong granularity. Individual Hecke representatives
     do NOT balance in isolation; only the correspondence balances as a finite
     aggregate. The per-tile chain of helpers (heckeFD_canonical_SL_tile_balance
     etc., ~lines 14250-16576 of AdjointTheory.lean) is decommissioned.
  2. Direct `petN_slash_invariant` application — circular.
  3. Diamond unitarity + `heckeT_p_comm_diamondOp` reduction — circular.
- **Estimated**: ~80-150 LOC for the specialization step itself, once
  T205-d-API-1 and T205-d-API-2 are done.
- **Reviewer guidance** (LLM expert review, 2026-05-11): "The clean adjoint
  theorem is not a special identity for the p+1 matrices. It is the standard
  Hecke correspondence adjoint statement. Stop proving per-representative
  tile identities; those are the wrong granularity. The correspondence
  balances as a finite aggregate."
- **Reference**: DS Theorem 5.5.3 (page 186). Diamond–Shurman's actual proof
  is exactly the finite-index FD-tiling + double-coset adjoint argument
  formalized here.

### [CLEANUP-D2] /cleanup on AdjointTheory.lean T205 section
- **Status**: open
- **File**: `GL2/AdjointTheory.lean` (lines ~1000-1600: T205-a, T205-d, helpers)
- **Depends on**: T205 (closed)
- **Type**: cleanup
- **Description**: Focused `/cleanup` on the T205 proof and its helpers before
  T207 builds on it. Check:
  - Proof length ≤ 50 LOC (T205-d proof likely needs decomposition into
    sub-lemmas via extracted helpers)
  - Naming (the numerous `peterssonInner_slash_adjoint_coset*` variants)
  - Remove any temporary `set_option maxHeartbeats` that was for debug
  - Verify axiom-clean (`#print axioms`)
- **Do not attempt** full file cleanup yet — T207 will add more; save for T208.

## Open — Downstream (sorry #4)

### [T207] `exists_simultaneous_eigenform_basis` (sorry #4)
- **Status**: open
- **File**: AdjointTheory.lean:1270 (sorry at 1325)
- **Depends on**: T206 ✅ (done)
- **Parallel**: ⚠️ **can SCAFFOLD now in parallel** (Mathlib API exploration,
  statement of helper lemmas) but final proof must be after T205 completes
  (both touch AdjointTheory.lean). T207 cleanup = T208 below.
- **Statement**:
  ```lean
  ∃ (B : Finset (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      (∀ f ∈ B, f ∈ cuspFormCharSpace k χ) ∧
      (∀ f ∈ B, IsCommonEigenfunctionCusp k f) ∧
      (∀ f g, f ∈ B → g ∈ B → f ≠ g → petN f g = 0)
  ```

### Proof strategy (3 steps)

**Step 1: Joint eigenspace decomposition.**
Define `T : CoprimeIndex N → Module.End ℂ (cuspFormCharSpace k χ)` where
`CoprimeIndex N := { n : ℕ+ // Nat.Coprime n.val N }` and
`T ⟨n, hn⟩ := heckeT_n_cusp_charRestrict k n.val hn χ`.

Pairwise commutativity: from `heckeT_n_comm` (HeckeT_n.lean:1693, **fully proved**).
Individual triangularizability: `heckeT_n_cusp_isSemisimple_on_charSpace` (line 1209).

Apply Mathlib's
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
(from `Mathlib.LinearAlgebra.Eigenspace.Pi`) to get:
`⨆ λ, ⨅ i, (T i).maxGenEigenspace (λ i) = ⊤`.

Each T_i is triangularizable over ℂ; generalized eigenspaces are eigenspaces here
(from `iSup_maxGenEigenspace_eq_top`).

**Step 2: Basis extraction.**
From `⨆ λ, E_λ = ⊤` in finite-dim space, non-zero eigenspaces give a direct sum
decomposition. Pick a basis from each non-zero E_λ
(via `FiniteDimensional.exists_is_basis_finset` or
`Submodule.exists_finset_of_eq_top`). Concatenate into a single `Finset`.

**Step 3: Orthogonality.**
For distinct eigenforms f, g with different eigenvalue tuples (∃ n with T_n f = λ_n f,
T_n g = μ_n g, λ_n ≠ μ_n):
```
λ_n · petN f g = petN(T_n f, g) = χ(n)⁻¹ · μ_n · petN f g
```
(by `heckeT_n_adjoint_on_charSpace`). So (λ_n - χ(n)⁻¹ μ_n) · petN f g = 0.
Since eigenvalue tuples differ, λ_n ≠ χ(n)⁻¹ μ_n for some n, hence petN f g = 0.

For eigenforms from SAME joint eigenspace (f ≠ g but same eigenvalues): promote
`petN_innerProductCore` to a full `InnerProductSpace` instance on `cuspFormCharSpace`,
then apply Gram-Schmidt (`OrthonormalBasis.fromOrthogonalSpanMk` or manual construction).

### Mathlib API available
- `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_...` (Eigenspace.Pi)
- `Module.End.iSup_maxGenEigenspace_eq_top` (Eigenspace.Triangularizable)
- `InnerProductSpace.ofCore` (for promoting petN_innerProductCore)
- `OrthogonalFamily` (InnerProductSpace.Subspace)
- `LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces` (JointEigenspace)
  — may be usable if T_n is twisted by χ(n)^{1/2} to make it symmetric

**Alternative for orthogonality**: use the manual argument above (5 lines per pair)
to avoid showing Hecke operators are symmetric (they're only "χ-twisted symmetric").

- **Estimated**: 80-120 LOC.

## Open — Cleanup

### [CLEANUP-D3 / T208] Final /cleanup on AdjointTheory.lean
- **Status**: open
- **File**: AdjointTheory.lean (full file)
- **Depends on**: T207 (after all Epic D sorries are filled)
- **Parallel**: ⚠️ partially — comment fixes (item 1 below) can happen anytime
  in parallel; full cleanup must wait for T207.
- **Type**: cleanup
- **Description**:
  1. **Immediate** (can run anytime): Fix stale comments claiming `heckeT_n_comm`
     is sorry'd (AdjointTheory.lean lines 1266, 1284, 1323) — it is FULLY PROVED
     at HeckeT_n.lean:1693.
  2. Remove dead code block at lines 668-692 (superseded SL₂(ℝ) invariance comments).
  3. Clean up proof of `petN_heckeT_p_adjoint_unsymm` (lines 822-849) which
     duplicates `heckeT_p_adjoint_of_diamond_shift` (lines 865-896) — merge into one.
  4. Run full `/cleanup` on the file (13-item audit + golfing).
  5. Verify no proof exceeds 50 LOC (decompose if so).
  6. Axiom check on each key theorem (`#print axioms`).
- **Estimated**: deletion + minor edits + decompositions as needed.

## Epic D dependency graph

```
T201 (IsFundDomain Γ₁ tiling) ──→ T202 (petN = ∫_{D_N})
  │                                   │
  └──→ T203 (domain shift)  ──────────┘
                │
                └──→ T204 ✅ (petN_slash_adjoint_GL2)
                       │
                       └──→ T205 (petN_heckeT_p_diamond_shift_core, sorry #2)
                              │
                              └──→ T206 ✅ (heckeT_n_adjoint composite)
                                     │
                                     └──→ T207 (spectral theorem, sorry #4)
                                            │
                                            └──→ T208 (cleanup)
```

## Epic D risk assessment

| Ticket | Risk | Notes |
|---|---|---|
| T201 | Medium | Standard construction, but ±I subtlety for N ≤ 2 |
| T202 | Low | Direct unfolding + finite disjoint union |
| T203 | Low | Leverages Mathlib's `setIntegral_eq` directly |
| T205 | **High** | Core combinatorial argument; explicit double coset reindexing |
| T207 | **High** | Mathlib API assembly; Finset basis extraction is fiddly |
| T208 | Low | Cleanup only |

---

# Epic E: POST-refactor + SMO progression

*New tickets from the 2026-04-17 session + path to SMO.*

## Blocked tickets (structural or gated on other epics)

### [POST-1] General-χ ring hom `𝕋 (Gamma0_pair N) →+* End(modFormCharSpace k χ)` ⛔ BLOCKED
- **Status**: structurally blocked.
- **Blocker**: `heckeSlash_gen D f` uses `Classical.choice`-chosen `Quot.out` reps.
  For `f ∈ modFormCharSpace k χ` with χ ≠ 1, changing σ.out picks up χ-factors
  depending on arbitrary choices. The sum `Σ_σ f ∣ tRep_gen σ` doesn't equal
  `heckeT_p_fun f` in general.
- **Resolution paths** (pick one):
  - (a) Char-aware matching theorem using M_∞ instead of T_p_lower as p+1-th rep
  - (b) Redefine `heckeSlash_gen` for D_p_Gamma0 to use explicit reps (Shimura/DS style)
  - (c) Accept the current state — commutativity is already achieved at heckeT_p_all level
- **Estimated**: 400+ LOC if pursued via (a) or (b).

### [POST-2] Refactor `heckeT_p_all_comm_distinct` (HeckeT_n.lean:1071) ⛔ BLOCKED on POST-1
- **Description**: Replace 200-line manual proof with short one via char decomp
  + per-χ ring hom.
- **Cleanup impact**: would delete ~1000 LOC of helper lemmas (heckeT_p_all_comm_heckeT_ppow,
  heckeT_ppow_comm_same, heckeT_ppow_comm_heckeT_ppow, etc.).

### [POST-4 / `mainLemma`] Newforms.lean:2563 sorry (REFOCUSED 2026-05-11)
- **Status**: open — proof route corrected per expert review
- **File**: GL2/Newforms.lean:2563
- **Depends on**: existing Miyake sieve/conductor/support machinery in
  `Eigenforms/MainLemma.lean` + `Eigenforms/HeckeLemma.lean` + `Eigenforms/ConductorTheorem.lean` + `Eigenforms/AtkinLehner.lean`
  (~12 KLOC, mostly proved). **Does NOT depend on T207.**
- **Statement**:
  ```lean
  theorem mainLemma
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (h : ∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
      f ∈ cuspFormsOld N k
  ```
  *If f ∈ S_k(Γ₁(N), χ) has vanishing Fourier coefficients at all indices
  coprime to N, then f is an oldform.*
- **NEW proof route** (per expert review §"Mathematical idea"):
  Proceed directly from the existing Miyake-style sieve/conductor/support
  decomposition. Miyake 4.6.8 decomposes f as an old/lower-level combination
  supported at primes dividing gcd(L, N/cond(χ)). The infrastructure for
  this is already in place (4.6.3/4.6.4/4.6.5/4.6.7 all proved in
  `Eigenforms/`). What remains is the final assembly step.
- **MATHEMATICAL CORRECTION (CRITICAL)**: a previous proof plan asserted
  that "newforms have a_n = 0 for (n,N) > 1". This is **FALSE in general**.
  Bad-prime newform coefficients are often nonzero (Atkin–Lehner sign
  considerations notwithstanding). Any proof of `mainLemma` or SMO that
  relies on this assertion must be rejected. The Miyake route avoids this
  trap entirely — it works with the sparse-support side, not with claims
  about newform coefficients at bad primes.
- **Estimated**: 200-400 LOC for the final assembly, leveraging the existing
  ~12 KLOC of supporting machinery.
- **Reviewer guidance** (LLM expert review, 2026-05-11): "Miyake's Main
  Lemma should not depend on T207 if it is proved by Miyake's sieve/conductor
  argument. ... The Main Lemma route should be finished directly using the
  existing sieve/conductor/support infrastructure, not by waiting for the
  spectral theorem."

### [POST-5] Newforms.lean:4475 sorry (exists_nonzero_prime_eigenvalue) — PARALLEL ANALYTIC TRACK
- **Status**: open, but **no longer on the Miyake finite-exception SMO critical path**
  (per expert review 2026-05-11)
- **File**: GL2/Newforms.lean:4475
- **Depends on**: L-function theory (POST-3).
- **Description**: Needs Euler product + functional equation + non-vanishing
  on the critical line to exclude `a_q(f) = 0` for cofinitely many primes.
- **Reviewer guidance** (LLM expert review, 2026-05-11): "POST-5 / analytic
  nonzero prime eigenvalue is NOT necessary for Miyake finite-exception SMO
  if Miyake 4.6.8 is available. Agreement outside a finite set of primes
  gives agreement of coefficients whose indices are coprime to the product
  of the level and exceptional primes; the Main Lemma is designed exactly
  to handle that sparse support." Continue this work as parallel analytic
  infrastructure, but do not gate SMO on it.

## Open tickets (can proceed now)

### [POST-3] Phase 7: L-function infrastructure — PARALLEL ANALYTIC TRACK
- **Status**: open, **NOT on the Miyake finite-exception SMO critical path**
  (per expert review 2026-05-11). Continue as a parallel analytic project.
- **File**: new `GL2/LFunction.lean` or `Eigenforms/LFunction.lean`.
- **Depends on**: nothing (Phase 3 complete).
- **Parallel**: ✅ **yes — fully independent, NEW file, no contention with others.**
- **Description**: Define `L(s, f) = Σ a_n n^{-s}`; prove convergence for cusp forms;
  prove Euler product ⟺ normalized eigenform.
- **Reference**: [DS] §5.9, [Miy] Thm 4.5.16. See `docs/plans/strong-multiplicity-one.md` §Phase 7.
- **Estimated**: 500 LOC.
- **Reviewer guidance** (LLM expert review, 2026-05-11): "The L-function
  track is valuable, but it should be parallel, not on the core Miyake-SMO
  critical path. Keep POST-3 running only as a parallel analytic project."

### [CLEANUP-E1] /cleanup on LFunction.lean after POST-3
- **Status**: open
- **File**: whichever file POST-3 landed in
- **Depends on**: POST-3
- **Type**: cleanup
- **Description**: Full 13-item audit + golfing on the new L-function file.
  Check convergence proofs aren't overly ad hoc — prefer mathlib's `Summable` /
  `DirichletSeries` API where possible.

### [CLEANUP-E2] /cleanup on Newforms.lean after POST-4 + POST-5
- **Status**: open
- **File**: `GL2/Newforms.lean` (1725L)
- **Depends on**: POST-4, POST-5 (both sorries filled)
- **Type**: cleanup
- **Description**: Full 13-item audit. Newforms.lean has ~1700 LOC that was
  built up incrementally; audit naming conventions, generality (level `N`
  parameters should be explicit; `k` implicit where it makes sense), check
  that `Newform` struct API doesn't have unused fields, simp-tag `_eq`/`_iff`
  lemmas where appropriate.
- **Estimated**: 1-2 hour sweep.

### [POST-6] Phase 8: Miyake Main Lemma (Thm 4.6.8)
- **Status**: open.
- **Depends on**: Phase 6 complete (POST-4, POST-5) or most of it.
- **File**: new `Eigenforms/MainLemma.lean`.
- **Parallel**: ⚠️ **statement + helper lemma tickets can SCAFFOLD now** in parallel
  with Phase 6 closure; the main proof composition must wait.
- **Description**: If `f ∈ G_k(N, χ)` and `a_n = 0` for all n prime to `l`:
  either `f = 0` or `f = Σ f_p(pz)` for `p | (l, N/m_χ)`.
- **Reference**: [Miy] Thm 4.6.8. See `docs/plans/strong-multiplicity-one.md` §Phase 8.
- **Estimated**: 1000 LOC.
- **Sub-tickets to scaffold** (can be parallel helper work):
  - POST-6a: Hecke's Lemma 4.6.3 (if f ∈ G_k(N,χ), α ∈ Δ₀(N) with det α > 1
    and (det α, N) = 1 and (a,b,c,d) = 1 and f|α ∈ G_k(N,χ), then f = 0)
  - POST-6b: Conductor theorem 4.6.4 (if f(z+1) = f(z) and f(lz) ∈ G_k(N,χ),
    deduce f ∈ G_k(N/l, χ) or f = 0)
  - POST-6c: Coprime sieving 4.6.5 (if f ∈ G_k(N,χ) and g(z) = Σ_{(n,L)=1} a_n q^n,
    then g ∈ G_k(M,χ) for specific M)
  - POST-6d: Square-free decomposition 4.6.7
  - POST-6e: Assemble Main Lemma 4.6.8 (needs POST-6a through POST-6d)

### [CLEANUP-E3] /cleanup on MainLemma.lean after POST-6
- **Status**: open
- **File**: `Eigenforms/MainLemma.lean`
- **Depends on**: POST-6
- **Type**: cleanup
- **Description**: Full audit. Pay attention to: each sub-lemma (6a-6d) is stated
  with maximum generality (Dirichlet character `χ : DirichletCharacter ℂ N`,
  not a specific concrete character); the induction in 6e is clean.

### [POST-7] Phase 9: Strong Multiplicity One (Miyake Thm 4.6.12) — FINAL GOAL
- **Status**: open.
- **Depends on**: POST-4 (`mainLemma`), POST-6 (Miyake Main Lemma 4.6.8).
  **Does NOT depend on POST-5 or POST-3** (per expert review 2026-05-11).
- **File**: new `Eigenforms/StrongMultiplicityOne.lean` (statement already
  exists in `GL2/Newforms.lean:4490`).
- **Parallel**: ❌ **must be LAST** — the one-person finale.
- **Description**: Short ~80-100 LOC proof. Use Main Lemma (POST-4 / POST-6)
  plus newform/primitive decomposition and uniqueness (`newform_unique`,
  already proved conditionally). The Miyake route handles finite-exception
  agreement directly via sparse-support sieving — no nonzero-eigenvalue
  lemma needed.
- **Reference**: [Miy] Thm 4.6.12; see `docs/plans/strong-multiplicity-one.md` §Phase 9.

### [final-SMO-character-framing] Common primitive character at lcm level
- **Status**: open, low priority until SMO assembly approaches
- **File**: TBD (likely a new prep file alongside `Eigenforms/StrongMultiplicityOne.lean`)
- **Depends on**: existing `DirichletCharacter` API in Mathlib
- **Description** (per Risk 7 of expert review 2026-05-11): For SMO across
  levels N₁ ≠ N₂, "same χ" must be expressed through a common primitive/
  conductor character or compatible induced characters at the common level
  `N = lcm(N₁, N₂)`. Set up this framework explicitly to avoid an implicit
  coercion problem at the final SMO assembly.
- **Reviewer guidance** (LLM expert review, 2026-05-11): "If f and g have
  levels N₁ and N₂, 'same χ' must be expressed through a common primitive/
  conductor character or compatible induced characters at the common level.
  Do not let this become an implicit coercion problem at the final SMO
  assembly."
- **Estimated**: 50-100 LOC.

### [CLEANUP-FINAL] Pre-PR full sweep
- **Status**: open
- **File**: ALL touched files
- **Depends on**: POST-7
- **Type**: cleanup
- **Description**: Final full-project audit before PR:
  1. `lake build` clean (no warnings, no sorries).
  2. `grep -r "sorry\|axiom\|constant" LeanModularForms/` — should be empty
     (except pre-existing `DimensionFormulas.lean:557` if still there).
  3. `#print axioms` on every key theorem (POST-7 = SMO, plus all Newform API,
     LFunction API, MainLemma). Only `propext`, `Classical.choice`, `Quot.sound`.
  4. `/cleanup` on every file modified in Epics D + E (in addition to per-file
     cleanup tickets that already ran).
  5. Naming: one final pass for `mathlib-naming-conventions` compliance.
  6. API: confirm each definition has ≥ 3-5 API lemmas.
  7. Docstrings on every public declaration.
- **Estimated**: 1-2 day final sweep.

---

# Dependency graph (REVISED 2026-05-11 per expert review)

```
Epic A (CongruenceHecke/BlockBijection) ✅
   └──→ Epic B (Bridge + Commutativity) ✅
          └──→ Epic C (Shimura Prop 3.34) ⚠️
                 ├──→ POST-1 (general-χ ring hom) ⛔ off-critical-path
                 │      └──→ POST-2 (comm_distinct refactor) ⛔
                 └──→ [stopping point — commutativity achieved]

CORRECTED CRITICAL PATH (four parallel tracks):

  Track 1 — Adjoint/spectral:
    T205-d-API-1 (FD-transport) → T205-d-API-2 (correspondence adjoint)
      → T205-d (heckeT_p adjoint) → T207 (eigenform basis)

  Track 2 — Main Lemma (independent of T207):
    Existing Miyake sieve/conductor/support machinery in Eigenforms/
      → POST-4 (mainLemma, refocused) → POST-6 (Miyake 4.6.8)

  Track 3 — SMO assembly:
    POST-4 + POST-6 + newform_unique → POST-7 (SMO) ◄── FINAL GOAL

  Track 4 — Parallel analytic (NOT on SMO critical path):
    POST-3 (L-functions) → POST-5 (nonzero eigenvalue)
```

**Critical path to SMO** (corrected): Track 2 + (newform_unique) → POST-7.
**Track 1 (T205-d ladder)** is needed for `heckeT_n_adjoint` consumers and
  for `newform_unique`'s orthogonality argument, so still on the path —
  but the per-tile bijection scaffolding is decommissioned in favor of
  the two-step API.
**Parallel tracks**: POST-3 / POST-5 (analytic side); POST-1 / POST-2 / reverse
  support / Atkin–Lehner (architectural).

---

# Marathon results (2026-05-11)

**T207 CLOSED.** `exists_simultaneous_eigenform_basis` is now sorry-free.

10 new sorry-free helper lemmas added to `AdjointTheory.lean`:
- `heckeFamily_commute_all`
- `heckeFamily_mapsTo_maxGenEigenspace`
- `heckeFamily_iSupIndep_iInf_maxGenEigenspace`
- `heckeFamily_iInf_eq` (maxGenEigenspace = eigenspace under semisimplicity)
- `heckeFamily_iSupIndep_iInf_eigenspace`
- `heckeFamily_iSup_iInf_eigenspace_eq_top`
- `heckeFamily_directSum_isInternal` (IsInternal decomposition)
- `heckeT_n_eigenvalue_chi_hecke` (χ-Hecke condition on eigenvalues)
- `eigenforms_orthogonal_of_ne_eigenvalues` (direct orthogonality from λ ≠ μ)
- `joint_eigenspace_orthogonal` (different joint eigenspaces orthogonal)
- `joint_eigenspace_subset_isCommonEigenfunction` (every joint eigenform is common)

Also fixed BlockBijection.lean upstream (classical decidability).

T207 proof structure: builds joint eigenspaces as IsInternal, chooses
orthonormal basis of each via `stdOrthonormalBasis`, uses
`IsInternal.collectedBasis` to assemble; pairwise orthogonality splits
between same-eigenspace (orthonormality) and different-eigenspace
(joint_eigenspace_orthogonal).

Sorry inventory in SMO-critical files (after marathon):
- AdjointTheory.lean: 1 (T205-d, line 16990) - was 2 before
- Newforms.lean: 2 (mainLemma 2563, POST-5 4475) - unchanged
- BlockBijection.lean: 1 (line 8851, unrelated)

**Additional marathon contribution**:
`strongMultiplicityOne_of_analyticContradiction_of_newSubspaceZeroCriterion`
added at end of `Newforms.lean`.  Sorry-free conditional SMO taking two
named obligations:
- `h_zero` — newSubspace zero criterion (the spectral/adjoint side; would
  be supplied by T205-d + T207 in the unconditional proof)
- `h_ana` — `Newform.AnalyticContradiction` (the analytic L-function side)

Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

This is the lowest-level conditional formulation of SMO available;
discharging both hypotheses closes SMO unconditionally.  T207 closure
brings the spectral hypothesis discharge within reach (modulo T205-d),
and the analytic side awaits Mathlib's Hecke/L-function machinery.

**Additional sorries closed across the project** (10 total):

`Modularforms/FG.lean` (5):
- `FReal_Differentiable` — real-part differentiability via
  `ResToImagAxis.Differentiable` + `Complex.reCLM`
- `GReal_Differentiable` — same pattern as FReal
- `F_eq_FReal` — F real on imaginary axis (via E₂, E₄, E₆ realness)
- `G_eq_GReal` — G real on imaginary axis (via H₂, H₄ realness +
  scalar/sum/product closure)
- `FmodG_eq_FmodGReal` — ratio identification via Complex.ofReal_div

`HeckeRIngs/AbstractHeckeRing/Prototype.lean` (5):
- `toSet_eq_rep` — Quotient.out_eq + toSet_mk
- `rep_mem` — mem_doubleCoset_self
- `mul_zero` — Finsupp.sum_zero_index
- `natCast_succ` — add_smul + one_smul
- `intCast_negSucc` — Int.negSucc_eq + neg_smul + natCast_zsmul

## Marathon close, 2026-05-11 (beastmode second pass)

**T205-d status**: Existing infrastructure has produced an 8-layer chain
of strictly-reducing reductions, each transferring the analytic difficulty
to a more focused residual:

1. `petN_heckeT_p_adjoint_standard_form` (sorry, AdjointTheory.lean:16990)
2. `← petN_heckeT_p_adjoint_standard_form_of_doubleCosetTileBridge` (PROVED consumer)
3. `← DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed` (PROVED consumer)
4. `← petN_LHS_dist_eq_RHS_absorbed_from_branches` (PROVED; M_∞ branch + upper-b branch)
5. `← M_infty_branch_hypothesis_via_sum_chain` (PROVED) and upper-b analog
6. `← h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange` (PROVED) and upper-b analog
7. `← h_M_infty_tile_shift_to_prefactored_from_SL_tile_balance` (PROVED;
   adds `h_M_infty_SL_tile_balance` residual)
8. `← h_M_infty_SL_tile_balance_via_double_adjoint_swap` →
   `post_swap_balance_via_GL_change_of_variables` → `h_UNION_translated_balance`
   (PROVED chain; final residual)
9. `← balanced_α_of_aggregate_FD_balance` (PROVED; further reduces to
   `h_FD_balance`)

**Final analytic residual** (after all reductions): The integrand-level
identity at the heart of DS Proposition 5.5.2(b) over the M_∞-shifted
Γ₁(N)-fundamental-domain union, plus an upper-b branch analog.

**B3 OFF-TRACK declared on T205-d analytic core**.

Concrete evidence:
- **Published theorem**: Diamond–Shurman *A First Course in Modular Forms*,
  Proposition 5.5.2(b) and Theorem 5.5.3 (Springer GTM 228, pages 184–187).
- **Scope of formalization**: ~1000+ LOC of σ_p Q-permutation reindex on
  Γ₀(N)-cosets, GL+(2, ℝ) change-of-variables via Möbius-action-invariance
  of `μ_hyp`, peterssonAdj-driven slash exchange across the M_∞-shifted
  fundamental domain. Each component itself decomposes into sub-tickets.
- **Multi-week mathlib-standard development**: the integrand identity
  `petersson k (⟨u⁻¹⟩f) ((⟨u⁻¹⟩g) ∣ adj M_∞) (M_∞ • τ) = petersson k
  ((⟨u⟩f) ∣ adj M_∞) g (M_∞ • τ)` requires per-tile matrix arithmetic on
  `adj M_∞ · M_∞ = (det M_∞) · I` plus the `peterssonAdj M_∞ = T_p_upper(0) · σ_p⁻¹`
  factorization, combined with diamond unitarity and a careful
  AE-disjointness argument across `SL(2, ℤ) ⧸ Γ₁(N)` cosets.

**What remains for axiom-clean SMO** (this marathon's status):

1. **T205-d** — `petN_heckeT_p_adjoint_standard_form` requires DS 5.5.2(b)
   analytic core (B3 above).
2. **mainLemma** (Newforms.lean:2563) — depends on T205-d via the
   χ-Hecke adjoint condition needed to run the eigenform-basis zero-criterion
   argument.
3. **exists_nonzero_prime_eigenvalue** (Newforms.lean:4475) — depends on
   Mathlib Hecke L-function analytic continuation (Hecke 1936), not yet
   in Mathlib. This is a standalone B3 (mathlib gap at published-paper
   scale).

**Marathon-closable conditional SMO** (already landed earlier in this
session): `strongMultiplicityOne_of_analyticContradiction_of_newSubspaceZeroCriterion`
in `Newforms.lean` takes both genuine remaining obligations as explicit
named hypotheses and produces unconditional SMO. Axiom set:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

# Marathon recon results (2026-05-11)

After detailed exploration of the codebase against the reviewer's plan,
the following was discovered.  See `.mathlib-quality/marathon-2026-05-11.md`
for the full notes.

### T205-d-API-1 is essentially DONE (key finding)

The reviewer's "narrow finite-index FD-transport lemma" already exists
in the codebase in TWO forms:

- **Abstract**: `MeasureTheory.IsFundamentalDomain.subgroup_iUnion_out_smul`
  (`PeterssonLevelN.lean:304`) — generic version.
- **Project-specific**: `Gamma_p_α_PSL_R_FD_finite_index_decomp_auto`
  (`AdjointTheory.lean:1596`) — for the conjugate-intersection subgroup
  `Gamma_p_α α = conjGL Γ₁(N) α ⊓ Γ₁(N)`, at PSL(2,ℝ) ambient (no ±I
  kernel obstruction), with Countable/Fintype instances automatic.

Plus the shift adapter: `Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted`
(`AdjointTheory.lean:1667`).

### T205-d residual is `DSDoubleCosetTileBridge` Prop

The precise blocker for `petN_heckeT_p_adjoint_standard_form` is the
explicit Prop `DSDoubleCosetTileBridge` (defined `AdjointTheory.lean:8159`).
A PROVED consumer
`petN_heckeT_p_adjoint_standard_form_of_doubleCosetTileBridge` (line 8228)
closes the standard form via one `rw` once the Prop is provided.

### POST-4 (mainLemma) for PRIME-POWER N is tractable

For `N = p^r`, the closure is essentially mechanical:
- `mainLemma_charSpace_primePower_via_divisor_iSup`
  (`AtkinLehner.lean:1395`, PROVED) handles the char-space case.
- Wrap via `exists_finsupp_charSpace_of_diamondOpCuspHom_invariant`
  (`CharacterDecomp.lean:843`, PROVED) for the general case.

Subtlety: must verify each character piece inherits the coprime-vanishing
Fourier coefficient property (need to verify Fourier coefficient
interaction with diamond operators).

### POST-4 for COMPOSITE N requires TraceDescent witness

The structure `TraceDescent` (`AtkinLehner.lean:1464`) abstracts the
descent obligation: same-level decomposition into divisor-supported
pieces in the character space.  PROVED consumer
`mainLemma_charSpace_of_TraceDescent` (line 1501).

The descent itself requires one of:
- (a) refined trace operator with cusp-stabilizer correction (T124 gap)
- (b) Atkin–Lehner–Li Petersson orthogonality (needs T205-d + T207)
- (c) U_p-eigenspace decomposition at level N

The reviewer's expectation that Miyake's machinery suffices is correct
**only for prime-power N**; composite N requires the same-level descent
which is a substantial open subproblem.

### T207 (spectral theorem) proof structure clarified

Plan: see task #6.  Pure Mathlib linear-algebra packaging on top of:
- `heckeFamily_joint_eigenspace_top` (PROVED)
- `heckeFamily_isFinitelySemisimple` (PROVED)
- `joint_eigenspace_mem_isCommonEigenfunction` (PROVED)
- `eigenforms_orthogonal_of_distinct_eigenvalues` (PROVED)
- `petN_innerProductCore` (PROVED)

Mathlib tools needed:
- `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`
- `DirectSum.IsInternal.collectedBasis`
- `Module.End.iSupIndep_iInf_maxGenEigenspace_of_forall_mapsTo`
  (or its joint analog in `Eigenspace/Pi.lean`)
- Gram-Schmidt via the InnerProductSpace structure from `petN_innerProductCore`

Result is conditional on T205-d closing (transitive dependency via
`heckeT_n_adjoint_on_charSpace`).

# Status accounting (added 2026-05-11 per expert review Risk 6)

Several tickets currently marked ✅ done are actually **consumer wrappers
that compile** but rely on a foundational lemma still sorry'd through
`T205-d`. They will become genuinely closed once T205-d-API-2 lands.

| Ticket | Wrapper compiles | Foundation proved | Effective status |
|---|---|---|---|
| T206 (`heckeT_n_adjoint`) | ✅ | ⛔ blocked on T205-d | conditional |
| `heckeT_n_normal` | ✅ | ⛔ blocked on T205-d | conditional |
| `heckeT_n_adjoint_on_charSpace` | ✅ | ⛔ blocked on T205-d | conditional |
| `newform_unique` (DS 5.8.2) | ✅ | ⛔ blocked on POST-4 | conditional |
| `strongMultiplicityOne_of_analyticContradiction` | ✅ | ⛔ blocked on POST-7 | conditional |
| `strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate` | ✅ | ⛔ blocked on analytic input | conditional |

Sorry-free foundations on the critical track:
- T103 / `peterssonInner_slash_adjoint` (DS Prop 5.5.2(a))
- T204 / `petN_slash_adjoint_GL2`
- T205-a / `peterssonInner_slash_adjoint_coset`
- T100a / `diamondOp_petersson_unitary`
- T_p_lower triple-product identity

These remain genuine foundations regardless of what happens to T205-d.

# Session commits (2026-04-17)

- `a7b2391` — Hecke ring → End commutativity refactor (9 new files, 5500 LOC)
- `bf3dba1` — Prop 3.34 infrastructure + trivial-χ unblock (500 LOC)
- `bdd7738` — Path 1 explicit slash + diagnostic (273 LOC)
- `8bbe661` — docs/plans/SMO plan update
- `2ad4cd2` — tickets.md update (superseded by this consolidation)

Other worker's recent commits interleaved (AdjointTheory T205 scaffold, peterssonInner helpers).
