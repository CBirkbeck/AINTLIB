# Reply integration — 2026-05-27 round 5

Reply received from senior expert in adic spaces / rigid analytic geometry on 2026-05-27.

- Brief: `brief.md` (in this folder)
- Reply: `reply.md` (in this folder)
- State: `state.md` (in this folder, now marked `Reply integrated: true`)

## Interpretation summary

The reviewer addressed all seven questions (Q1–Q7) with high-confidence direct answers, plus added two unprompted tactical recommendations (T-AR-3 ideal-containment restatement; T-LEGACY-MIGRATE priority bump) and a 6-step execution order.

Key bindings established:
1. **Q1 / A′-B′-C′ semantics**: P.I-image units are INSIDE H, not outside. Convex-subgroup decomposition produces `(u_max, H)` with cofinality.
2. **Q2 / bypass Presheaf.IsSheaf**: T-SP-SHEAF-B PERMANENTLY-SCOPED-OUT. Keep IsSheafy as main target.
3. **Q3 / path α**: explicit `[IsNoetherianRing P.A₀]` parameter is the right call; document as restricted theorem.
4. **Q4 / architecture**: keep current decomposition (Cor 8.32 + flat descent + standard-cover + Tate-OMT + restrictToConvex + Artin-Rees).
5. **Q5 / Lemma745 reuse**: `restrictToConvex` is canonical for Lean; do not search for alternative.
6. **Q6 / strong noetherianity bite**: local-basis + Cor 8.32 are genuine uses; OMT only indirect.
7. **Q7 / references**: current set is right; do not bring in Bhatt–Scholze for this step.

Plus two unprompted advice points:
- **T-AR-3 ideal-containment first**: prove `α ∈ I^(n+k·c) + ker(A → A[1/D.s])` then derive element witness.
- **T-LEGACY-MIGRATE priority bump**: false single-map injectivity is currently load-bearing in active code.

## Changes applied

### A. Round-7 sub-tickets re-decomposed with corrected semantics

- **T-WED-745-CONT-A**: status SIGNATURE-DEFECTIVE → OPEN with corrected A′ signature `∃ (u_max, H), u_max < 1 ∧ u_max ∈ H ∧ cofinality(u_max^n ≤ h, ∀ h ∈ H)`. No more "P.I units ∉ H" conjunct.
- **T-WED-745-CONT-B**: status BLOCKED-ON-A → OPEN with corrected B′ scope (A₀ → ≤1, T/s → ≤1, P.I^n bounded by u_max^n).
- **T-WED-745-CONT-C**: status BLOCKED-ON-A → OPEN with corrected C′ continuity discharge via cofinality + power-decay.

### B. T-SP-SHEAF-B permanently scoped out

- Status: SIGNATURE-DEFECTIVE → PERMANENTLY-SCOPED-OUT. Reviewer directive recorded verbatim.

### C. structurePresheaf_isSheaf refactor reverted

- Body returned to plain `sorry` with docstring pointing at the round-5 reply. The `isSheaf_of_homPresheaves_isSheaf` helper (T-SP-SHEAF-A landing) remains as a general-purpose utility lemma but no longer applied to the parent — since the Hom-presheaf decomposition route is permanently scoped out per reviewer guidance.

### D. New ticket T-PATH-ALPHA-RESTRICTED-NAMING added

- Documents the project's current sheafy target as `isSheafy_ofStronglyNoetherianTate_with_noetherian_pair` (explicit noeth-A₀ parameter). The Wedhorn-clean variant becomes a future ticket.

### E. Retired noeth-A₀ helpers deprecated; full deletion deferred

- Added `@[deprecated]` annotations on `_aux_noeth_A0_generic_of_stronglyNoetherianTate` and `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` (StructureSheaf.lean:1613, 1628).
- Merged docstrings to point at the round-5 reviewer directive and the migration ticket.
- Full caller deletion deferred to ticket **T-DELETE-RETIRED-NOETH-A0-HELPERS** (newly added, also in D) — multi-file refactor (~10 caller migrations across StructureSheaf.lean + AuditCleanWrappers.lean).
- Rationale for deferral: full migration ripples through 5+ public-API theorems and ~10 caller sites; would block the higher-priority A′/B′/C′ work per the reviewer's execution-order #1. `@[deprecated]` annotation + tracking ticket addresses the substantive concern (helpers should not be load-bearing in new code) while keeping the build clean.

### F. T-AR-3 restated as ideal-containment-first

- Status: OPEN (restated). Reviewer's better target shape recorded: `algebraMap(α · e_0^k_a) ∈ locNhd D m ⇒ α ∈ P.I^(n + k_a · D₀.hopen) + ker(algebraMap A → A[1/D.s])`.
- Split into T-AR-3-CONTAINMENT (ideal-level, ~80-100 LOC) and T-AR-3-WITNESS (element-level corollary, ~30 LOC). Lower than the original ~150 LOC estimate.

### G. T-LEGACY-TATEACYCLICITY-MIGRATE promoted to HIGH-PRIORITY

- Reviewer directive recorded verbatim. Migration plan reaffirmed: thread `perE_inj` per-E separation hypothesis through `tateAcyclicity_gluing_via_refinement` and `tateAcyclicity` Part 1; delete deprecated `restrictionMapHom_injective` and `restrictionMapHom_surj` post-migration.

### H. Round-5 review memory recorded

- New memory file: `feedback_round_5_review.md` documenting all seven binding decisions, plus the reviewer's 6-step execution order. Indexed in `MEMORY.md`.

### Round-5 execution-order recommendation (binding for next session)

1. Fix T-WED-745-CONT-A/B/C signatures using corrected A′/B′/C′ semantics.
2. Finish Wedhorn 7.45 continuity by abstracting Lemma745.
3. Finish T-AR-3 as ideal-containment lemma, then T-AR-4.
4. Migrate legacy Tate acyclicity callers off false single-map injectivity.
5. Keep structure sheaf `Presheaf.IsSheaf` out of the critical path.
6. Continue Path α assembly with explicit noetherian-pair hypotheses.

## Changes rejected by user

(none — user approved all 8)

## Notable conservative deviation

For E (delete retired noeth-A₀ helpers), the full deletion was deferred to ticket T-DELETE-RETIRED-NOETH-A0-HELPERS rather than executed in this round, because the full caller migration would touch ~10 sites across StructureSheaf.lean and AuditCleanWrappers.lean and would block the higher-priority A′/B′/C′ work. The `@[deprecated]` annotation + tracking ticket addresses the substantive concern. User should approve this deviation or request the full migration in a dedicated session.

## Open questions remaining

None — reviewer addressed all seven questions Q1–Q7.

## Decisions recorded but not actioned in code

- The path-α naming convention (D) was documented in the ticket board but no actual rename was applied to public-API theorems. The rename to `isSheafy_ofStronglyNoetherianTate_with_noetherian_pair` is recorded in ticket T-PATH-ALPHA-RESTRICTED-NAMING; it will land when that ticket is picked up.

## Files updated

- `.mathlib-quality/tickets.md` — 5 modified tickets (A/B/F/G + new D), 1 new (T-DELETE-RETIRED-NOETH-A0-HELPERS), 1 new (T-PATH-ALPHA-RESTRICTED-NAMING), round-5 execution-order block added.
- `Adic spaces/StructureSheaf.lean` — `structurePresheaf_isSheaf` reverted to plain `sorry` (C); `_aux_noeth_*` helpers deprecated (E).
- `.mathlib-quality/expert-review/2026-05-27/reply.md` — reviewer reply saved verbatim.
- `.mathlib-quality/expert-review/2026-05-27/integration.md` — this file.
- `~/.claude3/.../memory/feedback_round_5_review.md` — new memory note (H).
- `~/.claude3/.../memory/MEMORY.md` — index updated.

## Saved for posterity

- `.mathlib-quality/expert-review/2026-05-27/brief.md` (the brief sent to the reviewer)
- `.mathlib-quality/expert-review/2026-05-27/reply.md` (the reviewer's reply, verbatim)
- `.mathlib-quality/expert-review/2026-05-27/state.md` (session state, will be flipped to Reply integrated: true)
- `.mathlib-quality/expert-review/2026-05-27/integration.md` (this file)
