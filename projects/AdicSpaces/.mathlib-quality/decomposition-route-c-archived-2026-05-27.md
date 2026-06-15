# Decomposition Report — `isSheafy_ofStronglyNoetherianTate`
## /develop --decompose, post-audit rewrite, 2026-05-23

## 🔒 ROUND-3 ROUTE-C VERDICT (2026-05-26, integrated) 🔒

A round-3 expert reply (Hu/Wedhorn senior reviewer, after the REVIEW_BRIEF
asking Routes A/B/C question) recommends **Route C (Banach OMT against
the section equalizer)** as the next move, superseding the Round-2 Lane C
push for the topological-inducing field. Round-2 advice about
signature hygiene (NEW-A1) and Spa.comap framework (NEW-A2) remains
applicable for the algebraic/injectivity side; Round-3 only redirects the
topological-inducing strategy.

### Key clarifications from Round 3

- **Q1**: `IsSheafy.embedding` is the right topological formulation. Do NOT
  weaken to sheaf-of-rings. Route A's algebraic-only theorem is an
  acceptable intermediate, but not the final deliverable.
- **Q2**: Banach OMT does **not** apply to `ρ : O(C.base) → ∏_D O(D)`
  directly. It applies to `ρ : O(C.base) → E` where `E ⊂ ∏_D O(D)` is
  the **equalizer of the two overlap restrictions**. Then `E ↪ ∏_D O(D)`
  is automatic via the subspace topology.
- **Q3**: `LocalBasisHyp(C)` becomes unnecessary if Route C closes. It is
  a project-specific topological refinement device — NOT literally
  Wedhorn 8.34. Pause expansion of `LocalBasisHyp` infrastructure.
- **Q4**: For the topological inducing argument that Wedhorn 1910.05934
  defers, read **Huber 1996 Chapter 1** (Étale cohomology), not Huber 1993.
  Huber 1994 is the original-source backup.

### Route C decomposition (5 subgoals)

```text
algebraic equalizer + closed equalizer topology + OMT
  ⇒ productRestrictionSub is a topological embedding
```

| Sub | Goal | Status |
|-----|------|--------|
| C-OMT-1 | Define `sectionEqualizer C` as Subring of `∏ presheafValue D` | scaffolded |
| C-OMT-2 | Prove `IsClosed` (E is closed in the product, since Hausdorff target) | scaffolded |
| C-OMT-3 | Prove `CompleteSpace E` (closed subspace of complete = complete) | scaffolded |
| C-OMT-4 | Algebraic bijection `O(C.base) ≃ E` from acyclicity (separation + gluing — both already done in StructureSheaf via Cor 8.32 + descent) | scaffolded |
| C-OMT-5 | Apply Banach OMT to get homeo, compose with `E ↪ ∏_D O(D)` ⇒ IsInducing | scaffolded |

### Files

- New: `Adic spaces/SectionEqualizer.lean` — equalizer object + topology
- New: `Adic spaces/RouteC_BanachOMT.lean` — main inducing theorem
- Modify: `Adic spaces/StructureSheaf.lean` — replace `productRestrictionSub_isInducing_tate` body with delegation to `RouteC_BanachOMT`

### Locked policy

- Route B (Lane C / LaurentTree) is **demoted to optional backup**. Do not
  expand `LocalBasisHyp` further; do not push the σ-walk P-cluster.
- Route A (algebraic only) remains the discharger for separation+gluing
  via `tateAcyclicity_separation_via_cor832` +
  `tateAcyclicity_gluing_via_descent`. These deliver C-OMT-4 (bijection).
- Round-2 signature hygiene (NEW-A1: `[CompleteSpace A]`, `[CompatiblePlusSubring A]`)
  is **kept**.
- `[IsDomain A]` is still a temporary Path α restriction (Round 2 DOC-D1).
- If C-OMT-2/3 fail because `E` is not known to be a complete Tate ring
  in the required sense, **return to Route B** with `LocalBasisHyp` as a
  project-specific topological refinement lemma. This is the Round-3
  fallback policy.

### Round-4 update (2026-05-26-2 verdict)

The Round-3 Route C sprint hit a precise blocker at the OMT step:
mathlib's `AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`
requires `[SigmaCompactSpace G]` on the source, which is mathematically
**false** for `presheafValue C.base` from the keystone hypothesis set
(counterexample: `A = ℂ((t))`). The Round-4 reviewer's verdict
(see `.mathlib-quality/expert-review/2026-05-26-2/reply.md`):

- **Keep Route C as the main route**. Do NOT add `[SigmaCompactSpace A]`
  or `[SeparableSpace A]` to the keystone signature.
- **Replace** the mathlib sigma-compact OMT with a project-local
  **Tate-absorbing Baire OMT** (`IsOpenMap.of_surjective_tate_absorbing`,
  ticket `T-ROUTE-C-OMT`). This theorem uses the pseudo-uniformizer
  absorption property of Tate rings (every element absorbed into the
  ideal-of-definition lattice after π-scaling) in place of sigma-compactness.
- The general "complete + countable nbhd → open" Bourbaki form is
  **shaky** (counterexample: identity from discrete to coarser-complete).
  The Tate/Banach-module form with absorption is the correct strengthening.
- `presheafValue_sigmaCompactSpace` (T-ROUTE-C-5) is **off the keystone
  path**. Retain only as an optional separated lemma under explicit
  hypothesis, or delete.
- Optional `_of_separable` corollary (T-ROUTE-C-SEPARABLE-COROLLARY) is
  allowed as a downstream layering for ℚ_p-affinoid applications, but
  separability is NOT in the main keystone.
- Document the bridge in the keystone docstring: "Wedhorn proves algebraic
  equalizer exactness; topological-ring sheaf condition follows because
  the bijection `O(C.base) → sectionEqualizer(C)` is continuous surjective
  between complete Tate objects, hence open by Tate-absorbing OMT."
- Route B is fallback only. If Route C fails after the Tate-absorbing OMT
  formulation, Route B fallback priority: (i) Cor 7.32 finset form with
  compactness hypothesis, (ii) strengthened local-basis with `R({f}/f)`
  nonvanishing clause, (iii) σ-walk last.
- Empty-cover residual (T-ROUTE-C-7) flagged for cleanup: either carry
  needed typeclasses locally or add a precondition excluding the
  impossible branch. Currently temporary engineering decision (consumer
  case-splits upstream).

---

## 🔒 ROUND-2 REVIEWER VERDICT (2026-05-23, integrated) 🔒

After the full 35-sorry lemma-by-lemma audit, the round-2 reviewer
(see `.mathlib-quality/expert-review/2026-05-23-2/reply.md`) gave the
following strategic guidance, **which is now the locked plan**:

### Overall verdict
- Project is feasible. Push through full Path α; do NOT scope to Laurent-only.
- Keep Lane C tree induction; do NOT switch to direct Čech.
- Keep `RationalCovering A` as primary object.
- The audit is healthy cleanup, not deeper wrongness.
- Realistic estimate ~1500-2000 LOC of coordinated multi-file work.

### Locked execution order (5 steps, locked per round-2 Q5)

1. **NEW-A1 / Signature hygiene** (task #121, ~50-100 LOC). Add
   `[CompleteSpace A]` and new `[CompatiblePlusSubring A]` typeclass
   as standing assumptions on the Path α chain. Delete dead lemmas
   (NEW-A5, task #125). Closes B2 #14/L2, #15/L3, #16, #17 cascade.
2. **NEW-A4 / F12 file-hierarchy split** (task #124, ~1 day). Four-file
   structure: `LaurentRefinementCore` / `LaurentRefinementAcyclic` /
   `Cor832` / `TateAcyclicityFinalAssembly`. Move legacy `tateAcyclicity`
   + sub-chain downstream. Closes LR:6020, L17 (cor_8_32_clean_sub_with_P)
   structurally.
3. **NEW-A2 / Spa.comap framework full build** (task #122, ~500 LOC, 5
   subtickets #126-#130). The foundational `Spa(presheafValue D) ≃
   rationalOpen D`. Sub-lemma 1 (valuation extends to localization),
   sub-lemma 2 (extends to completion), sub-lemma 3 (image
   identification), IsHuberRing instance, headline assembly.
4. **NEW-A3 / presheafValue propagation API batch** (task #123, ~210 LOC,
   5 subtickets #131-#135). Per reviewer's "two-layer" guidance: prove
   once, use downstream. Includes `presheafValue_hasLocLiftPowerBounded`
   (#134, closes old task #38).
5. **Lane C atoms in priority order**: L1 strengthened (#67 Step B) →
   L4 replacement (#114) → L6 → L7 (after B2 fix per #22) → L8 → L9 →
   L10 → L11 → L12 → L13 (5-line composition closing the headline). Plus
   L16 deletion + downstream Path α wiring (closes B2 #23).

### Reviewer-mandated documentation decisions

- **DOC-D1**: `[IsDomain A]` is a temporary Path α restriction (final
  Wedhorn 8.28(b) does not require it). The current restricted theorem
  is NOT the full Wedhorn statement; document this throughout.
- **DOC-D2**: Mental abstraction missing — an `AffinoidTateContext`
  bundle (IsTate + CompleteSpace + T2 + NonarchimedeanRing +
  CompatiblePlusSubring + HasLocLiftPowerBounded + …). We do NOT
  literally create the structure but treat it as the design pattern.
- **DOC-D3**: `cor_8_32_clean_via_laurent` is a Laurent-specific
  combinator only. The general Cor 8.32 API is the flatness route
  (`cor_8_32_clean_proof` / `prop_8_30_flat_clean`); use that for
  arbitrary covers.

### Reviewer-rejected alternatives (do NOT pursue)

- Laurent-cover-only as main deliverable (Q2, Q5): rejected — too weak
  to support general IsSheafy.
- F12-a (force `[LaurentNormalized C.base]` onto general signature): rejected.
- F12-b (close legacy faithful-flatness-kernel upstream of Cor832): rejected.
- Direct Čech rewrite instead of Lane C tree induction (Q4): rejected —
  wouldn't avoid the propagation API gap.
- Restart with a different formalization of adic spaces (Q6): rejected
  — substrate is healthy.

### B2 cascade (closes after the above lands)

B2 #14, #15, #21, #22, #23, #24, #25, #26, #27 all close mechanically
once the signature/propagation infrastructure is in place. The remaining
open B2s reduce to none on the critical path.

The remainder of this document (below) is the prior decomposition
content from before round-2 integration, preserved for the per-leaf
audits. Where it conflicts with the round-2 verdict above, the
round-2 verdict wins.

---


## ⚠ ADVERSARIAL PASS UPDATE (2026-05-23, after code-reading sweep) ⚠

This is the **locked-in** plan after the adversarial code-read of each
remaining leaf. Five findings supersede the prior content of this file
where they conflict. The new findings are listed here once at the top;
the per-leaf sections below have been retained for reference but should
be read with these overrides in mind. **I will not be changing the plan
again without a concrete new code/source finding that contradicts it.**

### Override 1 — F12 (L18) is NOT safe as a structural move. DEFERRED.

The `_auto*` variants in `TateAcyclicityFinalAssembly.lean`
(`tateAcyclicity_via_normalizedLaurent_autoComplete/autoTPB/autoB/autoCont`,
lines 3033, 3148, 3308, 3408) all carry `[LaurentNormalized C.base]` as
a typeclass requirement. The general `tateAcyclicity` in
`LaurentRefinement.lean:6271` does NOT assume this. **These wrappers
cannot drop-in replace each other.** F12 as scoped by the round-4
reviewer requires one of:

- **(F12-a)** Refactor general `tateAcyclicity` to assume
  `[LaurentNormalized C.base]` (API change, breaks 4 StructureSheaf
  callers).
- **(F12-b)** Close the legacy sorry at `LaurentRefinement.lean:6020`
  directly — which requires the Cor832 faithful-flatness chain across
  the import cycle, i.e., the actual mathematical work.
- **(F12-c)** Add a separate `LaurentNormalized`-specific drop-in
  wrapper and keep the legacy `tateAcyclicity` (with its sorry) for
  general covers.

**Decision held**: defer F12 until the user explicitly picks (a), (b),
or (c). Until then, F12 is **NOT in the execution order**.

### Override 2 — L1 needs the `LocalBasisHyp` predicate itself updated.

The current predicate at `LocalBasis.lean:59` does NOT include the
`R({f}/f)` non-vanishing clause. The strengthening per expert review
requires editing the predicate definition BEFORE attempting the L1
proof. Downstream consumers of the predicate (C2 at
`TateAcyclicityResiduals.lean:252`) propagate the strengthened form.
Realistic LOC: **80–100** for L1 alone (was claimed 60).

### Override 3 — L3 has NO existing project discharges.

`PlusSubring.le_powerBounded` and `powerBounded_subset_A₀_of_isTateRing`
do NOT exist in the project (grep miss). The earlier "GREEN, 5-10 LOC"
verdict was wrong. Real LOC: **30–50**, including two ~15-LOC sub-lemmas
to be created.

### Override 4 — L8 and L10 underestimated by 2-3×.

T286 (`productRestrictionSub_isInducing_via_laurent_refinement_tau` at
`EmbeddingTopo.lean:896`) has a ~60-line hypothesis list. "Direct T286
application" claims for L8 and L10 mask substantial wiring. Realistic
LOC: L8 ~50-80, L10 ~60-80 (were claimed 30, 40).

### Override 5 — L11, L12 BLOCKED on task #38 (T-LOCLIFT-PRESERVATION).

Confirmed at `TateAcyclicityResiduals.lean:2247`: the explicit
`HasLocLiftPowerBounded (presheafValue L)` hypothesis is the actual
blocker. Class definition at `Presheaf.lean:970-993`. Independent
sub-development of ~50-100 LOC (Approach 1) is required. L11 cannot
proceed until this is in place.

### Override 6 — Tier 0 (†) wrappers are tainted, NOT closed.

The reviewer reply confirmed the four wrappers
(`exists_standard_cover_refining`, `exists_wedhorn_laurent_refinement_tree`,
`exists_wedhorn_ratio_laurent_refinement_tree_realized`,
`isSheafy_ofStronglyNoetherianTate_proof`) are "proof-script closed,
mathematically open" until L4 is replaced. They are sorry-free at the
wrapper level but transitively consume the L4 sorry via
`span_top_of_per_D_finite_cover`. Untainting requires the L4 replacement
landing.

---

## LOCKED EXECUTION ORDER

This order respects the DAG from the audit and will NOT be changed
without concrete new evidence. Steps in *parallel* can run independently.

| # | Step | LOC est | Dependencies | Status |
|---|------|---------|--------------|--------|
| 1 | **Update `LocalBasisHyp` predicate** to include `R({f}/f)` clause | ~10 | none | NEW (was implicit) |
| 2 | **L1 strengthened** (`localBasisHyp_of_strongly_noetherian`) | 80-100 | step 1 | YELLOW (Hübner/Zavyalov) |
| 3 | **L4 replacement** (strengthen C2 source) | ~30 | step 2 | unTAINTS 4 (†) wrappers |
| 4 | **L16** (`_aux_noeth_A0_generic_of_stronglyNoetherianTate`) | 20-30 | none | GREEN |
| 5 | *Parallel*: **L2** (~30-40), **L3** (~30-50), **L5** (~40-50) | total ~120 | step 4 | L2 GREEN, L3 YELLOW (no existing project lemmas), L5 GREEN |
| 6 | *Parallel*: **L14** (~5), **L15** (~5) | ~10 | steps L2, L3 | trivial delegations |
| 7 | *Parallel*: **L7** (~20-30), **L8** (~50-80) | ~100 | none | L7 GREEN, L8 YELLOW (T286 wiring) |
| 8 | **L6** σ-walk | 50-70 | steps L7, L8 | YELLOW |
| 9 | **Task #38 / T-LOCLIFT-PRESERVATION** (Approach 1) | 50-100 | task #87 (Spa_presheafValue_eq_rationalOpen) | BLOCKER for L11/L12 |
| 10 | *Parallel*: **L9** (~60-80), **L10** (~60-80) | ~140 | step L1, T286 | YELLOW (T286 wiring) |
| 11 | **L11** transport | ~70 | step 9 (T-LOCLIFT) + step 10 | YELLOW |
| 12 | **L12** per-leaf assembly | ~20-30 | step 11 | mechanical |
| 13 | **L13** Gap B composition | ~5 | step 12 + L4-untaint | mechanical |
| 14 | **L17** Cor 8.32 P-variant (placeholder) | 0 | (closes via Cor832 wiring) | mechanical placeholder |
| -- | **F12 (L18)** | DEFERRED | requires (a)/(b)/(c) decision + L-atom chain landed | NOT IN ORDER |

**Total estimated:** ~700-900 LOC of substantive proof + decision on F12.
**Critical path serializes at:** step 1 → 2 → 3 (L1 unblock), step 9 (T-LOCLIFT unblock for W3 chain).

### What's safe to start in parallel from cold

If multiple workers are available right now (post-step 4):
- **L16, L2, L3, L5, L7, L8** can all start in parallel.
- **Task #87** (Spa_presheafValue_eq_rationalOpen, currently sorry at StructureSheaf.lean:2222) can start in parallel — it's a prerequisite for Task #38.
- **L1 strengthening** must complete before L4 replacement can begin.

### ⚠ ADVERSARIAL PASS 2 — hidden-pitfall sweep (2026-05-23)

Second adversarial sweep specifically hunting for hidden proof branches
inside claimed leaves. **No more leaves were found to be false-as-stated**,
but four leaves were re-classified and three new sub-leaves surfaced.

#### Pitfall 2.1 — L3 is a hidden 2-lemma development (SUBSTANTIAL)

Grep confirms `PlusSubring.le_powerBounded` and
`powerBounded_subset_A₀_of_isTateRing` **do not exist** in the project.
L3's "delegation" plan needs both to be created. Concretely:

- **L3a** `aplus_le_powerBounded`: `(A⁺ : Set A) ⊆ A°`. ~10-15 LOC,
  delegating to `PlusSubring`'s integrality + `IsPowerBounded` definition
  in `Bounded.lean`.
- **L3b** `powerBounded_le_A₀_of_isTateRing`: `(A° : Set A) ⊆ P.A₀` for
  arbitrary ring of definition. ~15-20 LOC, via Wedhorn Prop 6.4(3)
  (power-bounded elements are bounded by powers of ideal of definition;
  in Tate rings the bound forces membership).
- **L3-COMPOSITION**: trivial transitivity, ~5 LOC.

**Revised L3 LOC: 30-50 (matches prior estimate but as 3 sub-leaves, not 1).**

#### Pitfall 2.2 — L9, L10 are also blocked on Task #38 (CRITICAL)

Prior plan had L11, L12 explicitly blocked on `HasLocLiftPowerBounded
(presheafValue D)` (task #38). **Pass 2 finding**: L9 and L10 also need
this typeclass — their proofs operate over `presheafValue L` (relative
leaf level) and apply T286 or construct ratio-tree refinements requiring
the same typeclass infrastructure. The L9/L10 signatures don't currently
carry the typeclass as explicit hypothesis, but the proof bodies cannot
be written without it being available somewhere.

**Implication**: Phase F (W3 chain L9–L12) is fully blocked on Phase E
(T-LOCLIFT chain). The W3 chain cannot run "in parallel with L6/L7/L8" as
the prior execution order suggested.

#### Pitfall 2.3 — Task #38 itself decomposes into 3 sub-leaves

The `HasLocLiftPowerBounded` class at `Presheaf.lean:970-993` has two
abstract methods:

- **Task #38a** `isUnit_canonicalMap_s`: ~20-30 LOC via the project's
  existing canonical-map machinery.
- **Task #38b** `locLift_divByS_isPowerBounded`: ~30-50 LOC. The harder
  obligation — verify that `divByS t D.s`-lift in `presheafValue D'` is
  power-bounded. Requires Wedhorn 7.41 (analytic height-1 continuity) or
  equivalent project lemma.
- **Task #87** `Spa_presheafValue_eq_rationalOpen` prereq: ~50-100 LOC.
  Current sorry at `StructureSheaf.lean:2222`. Itself potentially hidden
  multi-leaf (not audited in detail).

**Revised Task #38 total**: 50-80 LOC for the two methods + ~50-100 LOC
for task #87 prerequisite = **100-180 LOC on the T-LOCLIFT chain**.

#### Pitfall 2.4 — L8 hypothesis wiring (SUBSTANTIAL)

T286 (`productRestrictionSub_isInducing_via_laurent_refinement_tau` at
`EmbeddingTopo.lean:896`) has ~75 lines of hypothesis list (lines
896-970). Roughly 15 distinct hypotheses including `[hNoeth_B]`,
`[hDom_B]`, `[hSigCp_B]`, `[hA_complete_B]`, `[hnoeth_B]`,
`[hnoeth₂_B]`, `[hLocLift_B]`, `[hA₀Noeth_B]`, `[hcont_forward_B]`,
`[hcont_eval_B]`, `[hSigCp_TA]`, `[hplus]`, `[hminus]`, plus `τ` data
and `hτ` properties.

L8's claim "direct T286 application" masks ~30-40 LOC of `letI`/`haveI`
to discharge these from standing context. **Revised L8 LOC: 60-90 (was
50-80).** Same `letI`-chain issue applies to L10 once Task #38 is
available.

#### Pitfall 2.5 — L1 predicate update is a separate step

Already in the locked execution order as step 1, but the LOC wasn't
explicitly costed. Adding ~10 LOC for the `LocalBasisHyp` definition
update at `LocalBasis.lean:59`, plus downstream re-typing through
consumers.

#### Pitfall 2.6 — L2 needs `principalPair_A₀_isClosed` (MINOR)

The closure-of-complete pattern wants `IsClosed.completeSpace_coe` plus
a closedness lemma. Project may or may not have
`principalPair_A₀_isClosed` already. If not, +10-15 LOC sub-lemma.

#### Pitfall 2.7 — L7 possible `LaurentTree.leaves` induction gap (MINOR)

If `LaurentTree.leaves` doesn't expose a clean induction principle, L7
needs +15-20 LOC for manual recursion. Verify before starting.

### Clean leaves (verified no hidden pitfalls)

- **L5** `outside_rescue_of_per_D_cover` — straightforward by-cases.
- **L12** `exists_inner_laurent_refinement_per_leaf` — mechanical
  composition of L9+L10+L11 + `choose`.
- **L13** `productRestrictionSub_isInducing_tate` — genuinely 5 lines
  composing `exists_wedhorn_ratio_laurent_refinement_tree_realized` +
  `productRestrictionSub_isInducing_via_tree`.

### Revised LOC totals

| Phase | Leaves | LOC (revised) | Blockers |
|---|---|---|---|
| A | F12 decision | DEFERRED | user pick of (a/b/c) |
| B | L1 update + L1 + L4-replacement | ~120-150 | none |
| C | L16, L2 (+sub), L3 (+2 subs), L5, L14, L15 | ~150-200 | step B for L4-untaint |
| D | L7, L8, L6 | ~140-190 | none |
| E | Task #87 prereq, then Task #38a + 38b | ~100-180 | none (parallel with D) |
| F | L9, L10, L11, L12 | ~210-270 | Phase E |
| G | L13 | ~5 | Phase F |

**Revised total: ~720-995 LOC** (was 700-900). Higher upper bound now
accounts for: L3's two missing sub-lemmas, L8's hypothesis wiring,
Task #38 + Task #87 prereq, L1's predicate update, possible L7
recursion, possible L2 closedness sub-lemma.

### Revised execution order (locks in new findings)

1. **L1 predicate update** (step 0, ~10 LOC).
2. **L1 strengthened proof** (~80-100 LOC, Hübner/Zavyalov).
3. **L4 replacement** (~30 LOC, untaints 4 (†) wrappers).
4. **L16** (~20-30 LOC, parallel with steps 5-7).
5. *Parallel set 1*: **L2** (~30-45 LOC, may need L2-CLOSED ~10-15), **L3a** + **L3b** + **L3-composition** (~30-40 LOC), **L5** (~40-50 LOC).
6. *Parallel set 2*: **L14** + **L15** (~5 LOC each).
7. *Parallel set 3*: **L7** (~25-45 LOC), **L8** (~60-90 LOC).
8. **L6** (~50-70 LOC, after L7+L8).
9. **Task #87 prereq** (~50-100 LOC, parallel with steps 1-8).
10. **Task #38a + 38b** (~50-80 LOC, after Task #87).
11. *Parallel set 4*: **L9** (~60-80 LOC), **L10** (~60-80 LOC) — both after Task #38.
12. **L11** (~70 LOC, after L9+L10+Task #38).
13. **L12** (~20-30 LOC, after L11).
14. **L13** (~5 LOC, after L12).

**Total atomic sub-leaves (post Pass 2): 21 atoms** (was 17). The 4 new
atoms: L1-update, L3a, L3b, Task #38a + 38b split.

### F12 decision points (escalate to user before doing F12)

If/when F12 is reached, ask user:
1. Resolve API incompatibility via (a) refactor `tateAcyclicity` signature?
2. Or (b) prove the legacy `productRestriction_faithfullyFlat_kernel` sorry directly via downstream `Cor832` route (needs structural move)?
3. Or (c) add a separate `_via_normalizedLaurent` wrapper and keep legacy `tateAcyclicity` with its sorry?

Until that decision, F12 stays deferred. The L-atoms (steps 1-13) close
the substantive math; F12 is the cleanup-after.

---

(Below this line: prior decomposition content, kept for per-leaf
verbatim Wedhorn quotes and 5-attack passes. Where this prior content
conflicts with the overrides above, the overrides win.)

---



**Supersedes** the earlier 2026-05-23 draft, which used line numbers from a
stale `docs/ACYCLICITY-CRITICAL-PATH-PLAN.md` and claimed 15 critical leaves.
A repo audit found that many "open leaves" were already sorry-free wrappers
(in `AuditCleanWrappers.lean`, `EmbeddingTopo.lean`, `RestrictionFlatness.lean`)
and that the actual open frontier is composed of **22 atomic sub-sorries**
at deeper levels of the chain, all preserved per CLAUDE.md sub-lemma-with-sorry
rule.

This rewrite cites every file:line from `grep` against the live tree
(2026-05-23 HEAD) and identifies each open atom by the *actual* declaration
name in the code. Every leaf has an inline verbatim quote from Wedhorn's
*Adic Spaces* (arXiv:1910.05934v1) where the result has an explicit Wedhorn
source, a Lean ↔ source match paragraph, and a 5-attack adversarial pass.

This is `--decompose` mode (planning-only). No tickets are created.

---

## Expert review update (2026-05-23, post-brief)

**Senior reviewer verdict** on L4 + plan soundness (see
`.mathlib-quality/expert-review/2026-05-23/reply.md`):

- **L4 (`strengthened_cover_of_basic_cover`) IS false as stated** — and the
  flaw is *deeper* than the original "`0 ∈ mk_S_D(D)`" diagnosis. Even a
  *nonzero* element f ∈ A can lie in v.supp for some v in the cover piece's
  rational open. So filtering 0 post-extraction is not enough.
  **Logged as B2 #21.** Must be REPLACED, not proved.
- **Recommended fix:** strengthen the **source compactness extraction**
  (C2 / `exists_per_D_finite_cover_of_localBasisHyp`) to apply to the
  refined opens `R(insert f T/s) ∩ R({f}/f)`. The intersection
  `R({f}/f) = {v : v(f) ≠ 0}` is itself a rational open, so the strengthened
  cover is still a rational-open cover; compactness applies. Each extracted
  witness then automatically satisfies v(f) ≠ 0.
- **Rejected fix (b)** `v(s) ≠ 0`: too weak — `spanTop_iff_noCommonZero_spa`
  needs witness-wise non-vanishing, not shared-denominator.
- **Rejected fix (c)** post-filter `(... biUnion mk_S_D).filter (· ≠ 0)`:
  unsafe — may destroy the cover if `choose` picked only 0 for a piece.
- **L1 stays YELLOW**: Wedhorn Prop 6.18 alone is NOT the right citation
  (module-topology, not local-basis). Local-basis needs Hübner Lemma 3.8
  / Zavyalov §2.3 — rational-subdomain basis + adic Nullstellensatz.
- **L1 statement should be strengthened** to already incorporate the
  non-vanishing clause: `∀ v ∈ R(D), ∃ f, v ∈ R(insert f T/s) ∩ R({f}/f)
  ∧ R(insert f T/s) ⊆ R(D)`. This makes L4 redundant (its content lives
  in the strengthened L1).
- **L11 / T-LOCLIFT-PRESERVATION**: structural but reflects a real
  underlying theorem (relative rational localization over `presheafValue D`
  transports to absolute over A). **Adopt Approach 1**: prove
  `HasLocLiftPowerBounded (presheafValue D)` via Example 6.38 +
  `Spa_presheafValue_eq_rationalOpen` + power-bounded valuation criterion.
- **Reorder execution**: F12 → **L1 strengthened → L4 replacement** →
  Tate-aux → L2/L3/L5 → ... — L4 fix moves *before* Tate-aux, paired
  with the L1 strengthening.
- **Cascade real, but no wrapper-body edits needed** if the L4 replacement
  preserves the downstream interface. Four Tier 0 wrappers should be flagged
  "**assembly closed but mathematically open** pending L4 replacement":
  `exists_standard_cover_refining`,
  `exists_wedhorn_laurent_refinement_tree`,
  `exists_wedhorn_ratio_laurent_refinement_tree_realized`,
  `isSheafy_ofStronglyNoetherianTate_proof`.

The rest of this document is annotated to reflect these decisions.

---

## Top-level target

```lean
theorem isSheafy_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A
```

The audit-clean wrapper `isSheafy_ofStronglyNoetherianTate_proof` lives at
`Adic spaces/AuditCleanWrappers.lean:180`. It composes:

- `isSheafy_ofStronglyNoetherianTate_flat_of_wedhorn_tree_existence`
  (`EmbeddingTopo.lean:2382`) — takes a `RatioLaurentTree` existence
  hypothesis as input,
- `exists_wedhorn_ratio_laurent_refinement_tree_realized`
  (`TateAcyclicityResiduals.lean:2583`) — discharges that hypothesis.

Both are sorry-free at the wrapper level; their open content lives in
sub-leaves below.

### Wedhorn source

> **Theorem 8.28** (p.81). *Let* A = (A, A⁺) *be an affinoid ring and*
> X = Spa A. *Assume that A satisfies one of the following conditions.*
> (a) *The completion* Â *has a noetherian ring of definition.*
> (b) *A is a strongly noetherian Tate ring.*
> (c) Â *has the discrete topology.*
> *Then* 𝒪_X *is a sheaf of complete topological rings. Moreover, one has*
> H^q(U, 𝒪_X) = 0 *for all* q ≥ 1 *and all rational subsets* U *of* X.

Project targets (b). Per **Remark 8.20** (p.80), "sheaf of complete
topological rings" = sheaf of rings + topological-embedding condition on
the canonical map 𝒪_X(U) → ∏ 𝒪_X(U_i).

---

## Tier 0 — Already sorry-free wrappers (do not re-prove)

A **(†)** marker indicates the wrapper is **assembly-closed but
mathematically open** pending the L4 replacement — see "Tainted wrappers"
note below the table.

| Wrapper | File:Line | Composes | Discharges |
|---|---|---|---|
| `isSheafy_ofStronglyNoetherianTate_proof` **(†)** | `AuditCleanWrappers.lean:180` | tree existence + EmbeddingTopo wrapper | top-level target |
| `isSheafy_ofStronglyNoetherianTate_flat_of_wedhorn_tree_existence` | `EmbeddingTopo.lean:2382` | T286 + `productRestrictionSub_isInducing_via_tree` | injection of tree existence into IsSheafy |
| `isSheafy_ofStronglyNoetherianTate_flat` | `StructureSheaf.lean:1397` | `productRestrictionSub_isInducing_tate` + Spa-point separation | structural `IsSheafy` literal, modulo Gap B |
| `exists_wedhorn_laurent_refinement_tree` **(†)** | `TateAcyclicityResiduals.lean:2521` | W1 + W2 + I.1.a (graft) | tree existence (bare `LaurentTree A`) |
| `exists_wedhorn_ratio_laurent_refinement_tree_realized` **(†)** | `TateAcyclicityResiduals.lean:2583` | promotes bare tree to `RatioLaurentTree A` + realization | tree existence (Ratio form) |
| `exists_standard_cover_refining` **(†)** | `TateAcyclicityResiduals.lean:502` | W1 sub-atoms C1+C2+C3 + bridge | Wedhorn 7.54 |
| `productRestrictionSub_isInducing_via_tree` | `EmbeddingTopo.lean:2007` | T286 + node induction (T287, T289, T290, T291) | Lane C tree induction |
| `productRestrictionSub_isInducing_via_laurent_refinement_tau` | `EmbeddingTopo.lean:896` | T286 atomic case | single-step Lane C |
| `cor_8_32_clean_proof` | `AuditCleanWrappers.lean:86` | Prop 8.30 flat + Lemma 8.31 | Wedhorn Cor 8.32 |
| `prop_8_30_flat_clean` | `StructureSheaf.lean:1830` | `restrictionMap_flat_via_iteratedMinus` | Wedhorn Prop 8.30 |
| `restrictionMap_flat_via_iteratedMinus` | `RestrictionFlatness.lean:178` | Wedhorn Rem 8.29 tensor identity | Wedhorn Lemma 8.31 |
| `tateAcyclicity_part1_separation_via_cor832` | `TateAcyclicityResiduals.lean:2693` | Cor 8.32 | tateAcyclicity Part 1 separation |
| `tateAcyclicity_part2_gluing_via_flat_descent` | `TateAcyclicityResiduals.lean:2715` | Cor 8.32 + descent | tateAcyclicity Part 2 gluing |
| `exists_spa_point_in_rationalOpen_of_prime` | `StructureSheaf.lean:1338` | Wedhorn 7.45 (transitive sorry) | Spa-point existence |

**Tainted wrappers (†).** Per expert review 2026-05-23, four wrappers
above consume `span_top_of_per_D_finite_cover`, which transitively invokes
L4 (B2 #21). They are **proof-script-closed modulo L-atoms** but
**mathematically open** until L4 is replaced. No wrapper-body edits
required if the L4 replacement preserves the downstream interface
(strengthened C2 returns the same `mk_S_D` shape with the additional
non-vanishing clause), but the project dashboard should not call them
"mathematically done" while L4 is open.

All other Tier 0 wrappers are unaffected (the Cor 8.32 / Prop 8.30 /
Lem 8.31 chain is independent of L4).

---

## Tier 1 — Lane C / W1 atomic sub-sorries (5 atoms)

Wedhorn 7.54 + 8.34 Step (ii) chain. These are the C1–C3d sub-atoms of the
`exists_standard_cover_refining` reduction. All are atomic sub-leaves
preserved per CLAUDE.md sub-lemma-with-sorry rule.

### L1 · `localBasisHyp_of_strongly_noetherian` (W1/C1) — **STATEMENT STRENGTHENED per expert review**

**Location:** `TateAcyclicityResiduals.lean:236` (sorry at 241)

**Current Lean statement:**
```lean
theorem localBasisHyp_of_strongly_noetherian
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
    (C : RationalCovering A) :
    LocalBasisHyp C := by sorry
```

**Required strengthening (per expert review 2026-05-23).** The
`LocalBasisHyp` predicate must be re-defined (or a strengthened sibling
predicate introduced) to bundle the non-vanishing clause. Target shape:

```
∀ D ∈ C.covers, ∀ v ∈ R(D.T / D.s),
    ∃ f ∈ A,
      v ∈ R(insert f C.base.T / C.base.s) ∩ R({f}/f) ∧
      R(insert f C.base.T / C.base.s) ⊆ R(D.T / D.s)
```

The added `R({f}/f) = {v : v(f) ≤ v(f) ≠ 0} = {v : v(f) ≠ 0}` clause is a
genuine rational open. The strengthened statement makes the C2 / L4
chain trivially produce a non-vanishing witness via compactness extraction
on the refined opens (see L4-REPLACED below).

**Wedhorn source.** Hübner's *Lemma 3.8* / Zavyalov *§2.3* — the intrinsic
topological basis hypothesis for strongly-noetherian Tate rings. NOT in
Wedhorn 8.34 directly; not a consequence of Wedhorn Prop 6.18 alone
(reviewer confirmed: Prop 6.18 is module-topology, not local-basis).

**Lean ↔ source match.** `LocalBasisHyp C` (strengthened form) asserts that
the plus-pieces over `C.base` *intersected with their non-vanishing locus*
form a topological refinement basis on each cover piece. This is the
canonical content of Hübner Lemma 3.8: not "plus-pieces are a basis" in
the abstract, but "plus-pieces *that the valuation actually distinguishes*
refine any rational cover."

**Attacks attempted.**
1. *Counterexample.* Could the basis hypothesis fail? Under strongly-noeth
   Tate + complete, Wedhorn Example 6.38 + Prop 6.18(1) (canonical topology
   on finitely-generated modules) give the basis structure.
2. *Edge case (n=0).* Empty `T` → trivial basis. ✓
3. *Hypothesis strength.* `IsStronglyNoetherian` essential — without it,
   `A⟨T/s⟩` need not be noetherian and canonical topology may fail.
4. *Source drift.* The bare statement uses `LocalBasisHyp` (project type) —
   verify that the Lean predicate exactly captures the Hübner Lemma 3.8
   content.
5. *Discharge.* Lift Hübner Lemma 3.8 (mathlib has `Submodule.openSubmodules`
   + `IsAdic.basis_of_module`); ~60 LOC.

**Confidence: YELLOW.** External citation (Hübner/Zavyalov), not directly
Wedhorn 8.34. May admit a project-internal proof via canonical topology +
basis-of-power-of-I idiom. Per task #67 (P7 = W1) — currently `pending`.

### L2 · `principalPair_A₀_completeSpace_of_stronglyNoetherianTate` (C3a.i)

**Location:** `TateAcyclicityResiduals.lean:326` (sorry at 333)

```lean
theorem principalPair_A₀_completeSpace_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    letI : UniformSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ := …
    CompleteSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ := by sorry
```

**Wedhorn source.** Wedhorn Cor 5.50 / Prop 5.39 — `A₀` (ring of definition)
of a complete Huber pair is complete in its subspace uniformity. Wedhorn's
**Prop 6.18(1)** packages: every f-adic ring carries the canonical projective-
limit topology, and the ring of definition is closed under this topology.

**Lean ↔ source match.** Direct content of Cor 5.50: subspace uniformity on
`A₀` inherited from the (T₂ + complete) `A` is complete. The "principal pair"
is the canonical pair given by `IsTateRing.principalPair`.

**Attacks attempted.**
1. *Counterexample.* `A₀ ⊆ A` closed → inherits completeness. Under `T2Space A`
   + `IsHausdorff`, `A₀` is closed by Prop 5.39. Sound.
2. *Edge case.* `A₀ = A` (trivial pair) → `CompleteSpace A` directly.
3. *Hypothesis strength.* Needs `T2Space A`. Target has it.
4. *Source drift.* The uniformity is canonical (right uniformity from
   `IsTopologicalAddGroup`); the project's `letI` ensures the right
   uniform structure.
5. *Discharge.* `IsClosed.completeSpace_coe` from mathlib + closedness of
   `A₀` in `A` (project: `principalPair_A₀_isClosed`). ~30 LOC.

**Confidence: GREEN.** Mathlib has the closure-of-complete-is-complete
pattern; project needs the closedness claim wired in.

### L3 · `aplus_le_A₀_of_stronglyNoetherianTate_principal` (C3b)

**Location:** `TateAcyclicityResiduals.lean:383` (sorry at 387)

```lean
theorem aplus_le_A₀_of_stronglyNoetherianTate_principal
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] (P : PairOfDefinition A) :
    (A⁺ : Set A) ⊆ P.A₀ := by sorry
```

**Wedhorn source.**

> **Remark 7.15(1)** (p.60). *Let A be an f-adic ring. Then A° is a ring
> of integral elements (Proposition 5.30). It is clearly the largest ring
> of integral elements.*

Combined with **Prop 6.4(3)** (and Wedhorn's discussion at p.60): in a Tate
ring, every power-bounded element lies in every ring of definition.

**Lean ↔ source match.** A⁺ ⊆ A° (project's `PlusSubring`-inclusion) and
A° ⊆ A₀ for any ring of definition (Wedhorn Prop 6.4(3) — power-bounded
elements bounded by ideal-of-definition powers).

**Attacks attempted.**
1. *Counterexample.* If A is not Tate, A° need not lie in A₀ (could be
   strictly larger). Tate hypothesis essential.
2. *Edge case.* A discrete ⇒ A° = A° ⊆ A₀ trivially.
3. *Hypothesis strength.* `IsTateRing` essential.
4. *Source drift.* Project's `A⁺` is a `PlusSubring` instance; must match
   the `A° = {a : A | IsPowerBounded a}` form before applying Prop 6.4(3).
5. *Discharge.* Existing project lemma `PlusSubring.le_powerBounded` +
   `powerBounded_subset_A₀_of_isTateRing` (existing in `Bounded.lean` /
   `HuberRings.lean`).

**Confidence: GREEN.** Likely a 5-10 line composition of existing project
lemmas; review file `Bounded.lean` to confirm `powerBounded_subset_A₀`
exists.

### L4 · `strengthened_cover_of_basic_cover` (C3c) — **REPLACED / B2 #21 per expert review 2026-05-23**

**Status.** FALSE AS STATED. Logged as B2 #21 in
`.mathlib-quality/b2_log.jsonl` on 2026-05-23. **Do not prove. Replace.**
The reviewer confirmed: the C2 hypothesis (basic-cover existential) only
promises *some* `f ∈ mk_S_D D`; the strengthened conclusion adds
`v(f) ≠ 0` which cannot be recovered from C2 alone. Even setting aside
`f = 0` (where `IsCompact.elim_finite_subcover_image` may pick 0 since
`R(insert 0 T/s) = R(T/s)`), any nonzero element `f ∈ A` can lie in
`v.supp` for a given v. **Filtering 0 post-extraction does NOT suffice.**

**Replacement plan: `exists_per_D_finite_nonvanishing_cover_of_localBasisHyp`.**

Replace the C2 source (`exists_per_D_finite_cover_of_localBasisHyp` at
`TateAcyclicityResiduals.lean:252`) with a strengthened version that
extracts the finite subcover from the **refined opens**:
`fun f => rationalOpen (insert f C.base.T) C.base.s ∩ rationalOpen {f} f`.
Each piece is a rational open (intersection of two), and the strengthened
local-basis (the new L1) guarantees that this family still covers
`R(D.T / D.s)`. Apply `IsCompact.elim_finite_subcover_image` to this
refined family; each extracted witness then satisfies both
`v ∈ rationalOpen (insert f C.base.T) C.base.s` and
`v ∈ rationalOpen {f} f` (i.e., `v(f) ≠ 0`). The L4 step disappears
entirely — the consumer wires straight to the strengthened C2 output.

**Rejected alternatives** (per reviewer):
- *(b)* `v(s) ≠ 0` instead of `v(f) ≠ 0` — too weak for
  `spanTop_iff_noCommonZero_spa` which needs witness-wise non-vanishing.
- *(c)* post-filter `(⋃_D mk_S_D D).filter (· ≠ 0)` — may destroy the
  cover if compactness picked only 0 for a piece.

**Cascade.** L4 is consumed by `span_top_of_per_D_finite_cover`, which
feeds the four Tier 0 wrappers marked **(†)** above. Those wrappers
remain proof-script-closed but mathematically-open until L4 is replaced.
Replacement preserves downstream interface — no wrapper-body edits
needed.

---

**Obsolete statement (preserved for reference, do not prove):**

**Location:** `TateAcyclicityResiduals.lean:413` (sorry at 423)

```lean
theorem strengthened_cover_of_basic_cover
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
    (C : RationalCovering A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) :
    ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D,
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0 := by sorry
```

**Wedhorn source.** No direct Wedhorn quote — this is a project-internal
upgrade of the per-D cover (already supplied by C2) to add the `v(f) ≠ 0`
clause, which is essential for `spanTop_iff_noCommonZero_spa` (Prop 7.14
bridge).

**Lean ↔ source match.** A plus-piece point `v ∈ R(insert f C.base.T, C.base.s)`
satisfies `v(f) ≤ v(C.base.s) ≠ 0`, hence `v(f) ≠ 0`. The strengthening is
pure rephrasing once we unpack the rational-open definition.

**Attacks attempted.**
1. *Counterexample.* Could `v(f) = 0` for a plus-piece point? By definition
   of rational-open: `v ∈ R(insert f T, s) ⇒ v(f) ≤ v(s) ≠ 0`. So `v(f) ≤ v(s)`
   and `v(s) ≠ 0`. If `v(f) = 0`, OK that's a possibility — `v(f) = 0 ≤ v(s)`.
   *Wait — is this actually true?* Re-examining: plus-piece means
   `v(t) ≤ v(s) ≠ 0` for all `t ∈ insert f T`. So `v(f) ≤ v(s)`, but
   `v(f) = 0` is allowed. **This claim might be FALSE-AS-STATED.**
   Need to check: does C3c really need `v(f) ≠ 0`, or does
   `spanTop_iff_noCommonZero_spa` accept the weaker `v(f) ≤ v(s)`?
2. *Edge case.* If `f = 0`, then `v(0) = 0` always — claim FALSE if `0 ∈ mk_S_D D`.
3. *Hypothesis strength.* The h_cover_D hypothesis doesn't exclude `f = 0` —
   need to either add `f ≠ 0` clause or refine to "exists `f` with `f ≠ 0`".
4. *Source drift.* Prop 7.14 (`spanTop_iff_noCommonZero_spa`) — read the
   project lemma to determine which form is needed.
5. *Discharge.* Needs either (a) strengthening C2 to exclude `f = 0`, or
   (b) reformulating C3c with `v(s) ≠ 0` instead of `v(f) ≠ 0`.

**Confidence: RED (potential B2).** Statement may be FALSE-AS-STATED if
`mk_S_D D` includes `f = 0`. **Action: log to b2_log.jsonl as B2 candidate
pending verification.** Per task list, this is part of #99 "Decompose C3 main
assembly" (completed) — verify the assembly is sorry-free at the consumer
side or whether this is a sub-residual.

### L5 · `outside_rescue_of_per_D_cover` (C3d)

**Location:** `TateAcyclicityResiduals.lean:432` (sorry at 443)

```lean
theorem outside_rescue_of_per_D_cover
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
    (C : RationalCovering A)
    (mk_S_D : RationalLocData A → Finset A) (_h_in_D : …) (_h_cover_D : …) :
    ∀ v ∈ Spa A A⁺, v ∉ rationalOpen C.base.T C.base.s →
      ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0 := by sorry
```

**Wedhorn source.** No direct Wedhorn quote. Project-internal: Hübner /
Nullstellensatz "no-common-zero on the complement" — for any Spa point
outside the base rational-open, there exists a cover-witness with non-zero
valuation.

**Lean ↔ source match.** Outside-base means `v(t_i) > v(C.base.s) = 0` or
`v(C.base.s) = 0` for some `t_i`. The cover hypothesis says C's pieces cover
Spa A; for such v, v lies in some D's piece, hence in some `mk_S_D D`
plus-piece by C2 — which then carries the `v(f) ≠ 0` content.

**Attacks attempted.**
1. *Counterexample.* Could fail if Spa A point lies "outside" every D's
   piece? Then C wouldn't be a covering. Coverage hypothesis essential.
2. *Edge case.* C = trivial covering {Spa A}. Then "outside-base" → empty
   set, vacuous.
3. *Hypothesis strength.* Coverage of C is implicit in `RationalCovering`.
4. *Source drift.* Wedhorn's "no-common-zero" is the contrapositive form;
   project may use direct existential form.
5. *Discharge.* Wedhorn 7.30(2) + Cor 7.53 + C2 hypothesis. ~30 LOC.

**Confidence: YELLOW.** Depends on `RationalCovering`'s covering definition
matching the proof requirements.

---

## Tier 2 — W2 atomic sub-sorries (σ-walk + structural, 3 atoms)

Wedhorn 8.34 Step (ii). The first-stage Laurent tree with unit-generated leaves.

### L6 · `cover_witness_in_I_units_at_balanced_leaf` (W2 σ-walk content)

**Location:** `TateAcyclicityResiduals.lean:1747` (sorry at 1759)

```lean
theorem cover_witness_in_I_units_at_balanced_leaf
    [IsTateRing A] … (C : RationalCovering A) (S : Finset A)
    (_hS_cover : refines_cover C S) (_hS_contain : refines_contain C S)
    (s : Aˣ) (L : RationalLocData A) (I_units : Finset A)
    (_hI_sub : I_units ⊆ S)
    (_h_unit : ∀ f ∈ I_units,
      IsUnit (L.canonicalMap (((s⁻¹ : Aˣ) : A) * f))) :
    ∀ v ∈ rationalOpen L.T L.s, ∃ f ∈ I_units,
      v ∈ rationalOpen (insert f C.base.T) C.base.s := by sorry
```

**Wedhorn source (Lemma 8.34 Step (ii), p.84).**

> *Indeed, for all* x ∈ X *there exists* f_i *such that* x(f_i) ≠ 0. *Thus
> by Corollary 7.32 there exists a unit* s ∈ A^× *such that for all* i …
> *Then the Laurent cover generated by* s^{-1}f_1, …, s^{-1}f_r *satisfies
> the claim.*

**Lean ↔ source match.** At a balanced-tree leaf `L`, the I_units family
(rescaled-by-s⁻¹ generators that became units) is exactly Wedhorn's
"f's whose `s^{-1}f` is a unit on L". The claim is that this family covers
any valuation `v` on `L`: at least one `f ∈ I_units` has `v(f) ≤ v(C.base.s) ≠ 0`,
i.e., `v` lies in the plus-piece at `f`.

**Attacks attempted.**
1. *Counterexample.* Could the I_units family fail to cover L? By the
   σ-walk construction at a balanced leaf, the units of `L.canonicalMap`
   are exactly those f_i with `v(f_i) = v(s)` for v in L's rational open
   — Wedhorn's "f_i dominates s" condition.
2. *Edge case (I_units = ∅).* Then claim asserts `∃ f ∈ ∅, …`, which is
   false — so I_units ≠ ∅ must follow from L being non-empty (Coverage
   assumption + Cor 7.53).
3. *Hypothesis strength.* The unit clause `_h_unit` is the σ-walk output;
   `_hS_cover` provides existence of `f ∈ S` covering each v.
4. *Source drift.* Wedhorn's σ-walk indexes over σ : leaves → bool; project's
   `I_units` is `{f ∈ S : σ at f's position = false}` per the surrounding
   code at line 1707-1710.
5. *Discharge.* σ-walk content per Wedhorn 8.34. ~40 LOC.

**Confidence: YELLOW.** Substantive — the actual σ-walk argument.

### L7 · `leaf_rationalOpen_subset_base_at_balanced_leaf` (W2 structural)

**Location:** `TateAcyclicityResiduals.lean:1803` (sorry at 1814)

**Wedhorn source.** Structural fact about Laurent trees: at any leaf L of
the balanced tree, `R(L.T, L.s) ⊆ R(C.base.T, C.base.s)` (Wedhorn 8.34(i):
restriction is monotone).

**Lean ↔ source match.** Each refinement step adds constraints, never removes
them. Project's `LaurentTree.leaves` recursion preserves the base-rooted
property; the leaf's rational-open is contained in the root's.

**Attacks attempted.**
1. *Counterexample.* Could fail if `LaurentTree.leaves` recursion deviated
   from rational-open monotonicity? Project's structure shouldn't allow this.
2. *Edge case (single leaf).* L = root → equal. ✓
3. *Hypothesis strength.* No external hypotheses; purely combinatorial.
4. *Source drift.* `RationalLocData` containment lemma must apply.
5. *Discharge.* Induction on tree depth. ~30 LOC.

**Confidence: GREEN.** Pure structural induction.

### L8 · `balancedTree_BalancedInducing_of_rescaled_S` (W2 inducing)

**Location:** `TateAcyclicityResiduals.lean:1906` (sorry at 1915)

**Wedhorn source.** Lemma 8.34 Step (i) — the balanced Laurent tree on a
finite set of generators is `allSplitsInducing` (each 2-set split is
inducing per Lemma 8.33).

**Lean ↔ source match.** The balanced tree's splits are pairwise
`{R(f/1), R(1/f)}` — each is the atomic Laurent 2-set cover from
Lemma 8.33, hence inducing per T286.

**Attacks attempted.**
1. *Counterexample.* Could a 2-set Laurent split fail inducing? Per T286 +
   Lemma 8.33, no — for strongly-noeth Tate.
2. *Edge case (S = {1}).* Single-generator tree → trivial. ✓
3. *Hypothesis strength.* Needs `IsStronglyNoetherian` + `IsTateRing` +
   `IsDomain` (the standard combo for T286).
4. *Source drift.* Balanced tree structure matches Wedhorn's iterated `𝒰_{f_i}`.
5. *Discharge.* Apply T286 at each split. ~30 LOC.

**Confidence: GREEN.** Direct application of T286.

---

## Tier 3 — W3 atomic sub-sorries (relative ratio refinement, 3 atoms)

Wedhorn 8.34 Step (iii). Ratio-refinement of unit-generated covers + transport.

### L9 · `unitCover_refines_relative_balanced_ratio_tree_leaves` (W3 relative)

**Location:** `TateAcyclicityResiduals.lean:2018` (sorry at 2040)

**Wedhorn source (Lemma 8.34(iii), p.84).**

> *Every rational cover 𝒰 of X which is generated by units f_0, …, f_n of A
> has a refinement by a Laurent cover. Indeed, the Laurent cover generated
> by {f_i f_j^{-1} ; 0 ≤ i, j ≤ n} is a refinement of 𝒰.*

**Lean ↔ source match.** At a leaf of the outer balanced tree (unit-
generated), construct the inner ratio tree on `{f_i / f_j}` and verify it
refines the unit-cover restricted to that leaf.

**Attacks attempted.**
1. *Counterexample.* If f_j is unit and v(f_j) > v(f_i) for all i, then v
   lies in piece j of the cover and in the ratio-piece {x : x(f_i/f_j) ≤ 1 ∀i}.
   Match.
2. *Edge case (single unit).* Trivial refinement.
3. *Hypothesis strength.* Unit assumption on the f's.
4. *Source drift.* "Relative balanced ratio tree" is project's spelling for
   the inner ratio tree at one leaf.
5. *Discharge.* Direct construction per Wedhorn (iii). ~50 LOC.

**Confidence: GREEN.** Wedhorn 8.34(iii) is explicit and constructive.

### L10 · `balancedInducing_of_relative_unit_ratios` (W3 inducing)

**Location:** `TateAcyclicityResiduals.lean:2055` (sorry at 2072)

**Wedhorn source.** Lemma 8.34(i) applied to ratio splits at a leaf: each
ratio split `{x(f_i/f_j) ≤ 1, ≥ 1}` is a 2-set Laurent cover, hence inducing
per Lemma 8.33 + T286.

**Lean ↔ source match.** The ratio tree's splits are
`{R(f_i/f_j ≤ 1), R(f_i/f_j ≥ 1)}` — atomic Laurent 2-set covers; each is
inducing per T286 applied at the ratio leaf.

**Attacks attempted.**
1. *Counterexample.* Same as L8 atomic. None.
2. *Edge case.* Single ratio split → degenerate, handled.
3. *Hypothesis strength.* T286 + leaf-relative-strongly-noeth (needs
   `IsStronglyNoetherian (presheafValue D)`, which Example 6.38 provides).
4. *Source drift.* `presheafValue D` is the rational-restriction; Example
   6.38 ensures strongly-noeth carries down.
5. *Discharge.* Apply T286 at relative leaf. ~40 LOC.

**Confidence: GREEN.** Composition of T286 + Example 6.38.

### L11 · `relative_laurent_tree_to_absolute` (W3-transport)

**Location:** `TateAcyclicityResiduals.lean:2234` (sorry at 2303 — note: ~70-line body!)

**Wedhorn source.** Lemma 8.34(i):

> *Moreover, if* U = R(T/s) *is any rational subset, then* 𝒰_{f|U} =
> 𝒰_{f_{|U}}, *where* f_{|U} *is the image of* f *under the homomorphism*
> A → A⟨T/s⟩.

The transport identity: a Laurent cover constructed relatively (at a leaf
L) equals the Laurent cover constructed absolutely on the image elements.

**Lean ↔ source match.** Convert a relatively-constructed `RatioLaurentTree`
(rooted at L, with leaf-relative `presheafValue L`-elements) into the
absolute `RatioLaurentTree` on `A` itself, using the canonical map
`A → presheafValue L` to lift the relative elements.

**Attacks attempted.**
1. *Counterexample.* Could the canonical-map lift fail to preserve the
   ratio structure? Wedhorn's identity 8.34(i) asserts equality. Sound.
2. *Edge case (L = root).* Identity transport. ✓
3. *Hypothesis strength.* Needs typeclass instances on `presheafValue L`
   that project hasn't fully bottled (this is the T-LOCLIFT-PRESERVATION
   gap — task #38).
4. *Source drift.* "Absolute" vs "relative" matches Wedhorn's "in A vs in A⟨T/s⟩".
5. *Discharge.* Once T-LOCLIFT-PRESERVATION (HasLocLiftPowerBounded on
   `presheafValue D`) lands, this is mechanical. ~70 LOC.

**Confidence: YELLOW.** Blocked downstream on T-LOCLIFT-PRESERVATION
typeclass propagation.

**Discharge decision (expert review 2026-05-23): adopt Approach 1.**
Prove the class propagation directly: `HasLocLiftPowerBounded (presheafValue D)`
follows from (a) Example 6.38 (rational localization preservation),
(b) `Spa_presheafValue_eq_rationalOpen` (the C3 Spa.comap framework,
task #87 skeleton in place), and (c) the power-bounded valuation
criterion. This is cleaner long-term than the per-leaf bypass (Approach 2)
because many later declarations expect the typeclass, and unblocks both
L11 and L12 simultaneously. Once T-LOCLIFT-PRESERVATION (task #38) lands,
L11 is mechanical (~70 LOC).

---

## Tier 4 — I.1.a per-leaf inner trees

### L12 · `exists_inner_laurent_refinement_per_leaf` (I.1.a)

**Location:** `TateAcyclicityResiduals.lean:2477` (sorry at 2493)

```lean
theorem exists_inner_laurent_refinement_per_leaf
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [DecidableEq A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (S : Finset A)
    (_hS_cover : refines_cover C S) … (s : Aˣ) (t_outer : LaurentTree A)
    (_ht_outer_eq : …) (_h_outer_unit_gen : …) :
    ∀ L ∈ t_outer.leaves C.base, ∃ inner : LaurentTree A,
      inner.Refines L C ∧ inner.allSplitsInducing L := by sorry
```

**Wedhorn source.** Lemma 8.34 Step (iii) at the leaf level — same content
as L9 + L10 packaged together, with assembly into `inner : LaurentTree A`.

**Lean ↔ source match.** Per outer leaf L, run W3 (L9 + L10) to construct
the inner ratio tree; then convert to bare `LaurentTree A` (the I.1 output
contract). The docstring explicitly says this is the T-LOCLIFT-PRESERVATION
ticket (task #38, pending).

**Attacks attempted.**
1. *Counterexample.* Reduces to L9 + L10; no independent counterexample.
2. *Edge case.* Empty outer-leaf set → vacuous quantifier. ✓
3. *Hypothesis strength.* Same as L9/L10 + the typeclass propagation onto
   `presheafValue L`.
4. *Source drift.* "Inner" vs "outer" naming matches the graft structure
   in `exists_wedhorn_laurent_refinement_tree` at line 2521.
5. *Discharge.* L9 + L10 + bare-conversion (`RatioLaurentTree → LaurentTree`).

**Confidence: YELLOW.** Composition of L9 + L10 + T-LOCLIFT-PRESERVATION.

---

## Tier 5 — Gap B headline

### L13 · `productRestrictionSub_isInducing_tate` (Gap B)

**Location:** `StructureSheaf.lean:1351` (sorry at 1356)

```lean
theorem productRestrictionSub_isInducing_tate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A) :
    Topology.IsInducing (productRestrictionSub A C) := by sorry
```

**Wedhorn source.** Theorem 8.28(b) topological half, via Remark 8.20:
"𝒪_X(U) → ∏ 𝒪_X(U_i) is a topological embedding". The Lane C strategy
discharges this via:

1. T286 single-step closer (axiom-clean, task #46/T286 ✓).
2. Tree refinement (sorry-free via `exists_wedhorn_laurent_refinement_tree`
   modulo L1, L6–L12 above).
3. Tree-node induction (sorry-free via
   `productRestrictionSub_isInducing_via_tree` at `EmbeddingTopo.lean:2007`).

**Lean ↔ source match.** The body at lines 1402-1457 outlines exactly this
plan — once tree-existence is in place, `productRestrictionSub_isInducing_via_tree`
discharges this in 1 line. The docstring at line 1347 calls it "Gap B".

**Attacks attempted.**
1. *Counterexample.* Wedhorn 8.28(b) ⇒ inducing. No counterexample.
2. *Edge case (`C.base.s = 0`).* The flat consumer at line 1420 splits this
   out via `presheafValue_subsingleton_of_s_eq_zero`. Handled at the consumer
   level — this leaf assumes `s ≠ 0`? Actually checking — the signature
   doesn't add `s ≠ 0`, so the `s = 0` case must close by subsingleton too.
3. *Hypothesis strength.* Tate + strongly-noeth + IsNoetherianRing + T2 +
   NonArch. No `[IsDomain]` (good — matches Wedhorn's hypothesis).
4. *Source drift.* The "via tree" route is project-specific, but its
   correctness reduces to Wedhorn 8.34 + 8.33 via the chain in Tier 0.
5. *Discharge.* Once L1, L6–L12 land, this leaf closes via
   `productRestrictionSub_isInducing_via_tree` + tree existence (~5 LOC).

**Confidence: GREEN.** Composition of existing axiom-clean wrappers.

---

## Tier 6 — Tate-side completeness sub-sorries (3 sub-leaves)

These feed the non-open Spa-point chain via `_aux_nonOpen_hSpa_*`.

### L14 · `_aux_nonOpen_hSpa_principalPair_A₀_completeSpace`
**Location:** `StructureSheaf.lean:1151` (sorry at 1158)
**Wedhorn source.** Same as L2 (Wedhorn Cor 5.50). Project-specific
re-statement at the non-open-Spa hypothesis profile.
**Discharge.** Wires to L2 (`principalPair_A₀_completeSpace_of_stronglyNoetherianTate`).
**Confidence: GREEN.** Direct delegation once L2 lands.

### L15 · `_aux_nonOpen_hSpa_Aplus_le_principalPair_A₀`
**Location:** `StructureSheaf.lean:1210` (sorry at 1214)
**Wedhorn source.** Same as L3 (Wedhorn Rem 7.15 + Prop 6.4(3)).
**Discharge.** Wires to L3 (`aplus_le_A₀_of_stronglyNoetherianTate_principal`).
**Confidence: GREEN.** Direct delegation once L3 lands.

### L16 · `_aux_noeth_A0_generic_of_stronglyNoetherianTate`
**Location:** `StructureSheaf.lean:1711` (sorry at 1716)
**Wedhorn source.** Wedhorn Prop 6.18(2) — generic noetherianness of
A₀ from strongly-noeth Tate hypothesis on A.
**Discharge.** Wedhorn Prop 6.18(2) + project's `IsStronglyNoetherian`
class. ~20 LOC.
**Confidence: GREEN.**

---

## Tier 7 — Cor 8.32 P-parameterized variant

### L17 · `cor_8_32_clean_sub_with_P`
**Location:** `StructureSheaf.lean:1862` (sorry at 1872)
**Wedhorn source.** Cor 8.32 in the `PairOfDefinition A` typeclass profile.
**Lean ↔ source match.** Bridges `cor_8_32_clean_proof` (audit-clean form) to
the consumer hypothesis profile that carries `(P : PairOfDefinition A)`.
**Discharge.** Delegation to `cor_8_32_clean_proof` + typeclass adapter. ~20 LOC.
**Confidence: GREEN.**

---

## Tier 8 — F12 structural move (1 displaced sorry)

### L18 · `LaurentRefinement.lean:6020` (anonymous sub-step)

**Location:** Inside a `Cor 8.32 sub-step (preimage existence from kernel
datum)` block (LaurentRefinement.lean:6022 docstring).

**Wedhorn source.** Cor 8.32: faithfully flat ⇒ preimage existence (the
"surjective onto equaliser" side of Wedhorn's tateAcyclicity).

**Lean ↔ source match.** This sorry is INSIDE the legacy `tateAcyclicity`
proof at LaurentRefinement.lean:5943. **The F12 move (task #85) deletes it**
by relocating `tateAcyclicity` and delegating to the existing
`tateAcyclicity_part2_gluing_via_flat_descent` ✓.

**Discharge.** F12 move (no Lean proof; structural file relocation).

**Confidence: GREEN.** Pure relocation.

---

## Off-critical-path open sorries (not in the IsSheafy chain)

These are open but not on the Wedhorn-8.28(b) critical path. Listed for
completeness; should NOT be in the IsSheafy execution order.

| # | Sorry | Location | Status |
|---|---|---|---|
| O1 | `structurePresheaf_isSheaf` | `StructureSheaf.lean:254` (sorry 256) | Top-level shell; closed by `isSheafy_ofStronglyNoetherianTate_flat`+ wiring |
| O2 | `_sub_lemma_L5_1_3_inductive_step` | `StructureSheaf.lean:2143` (sorry 2147) | **Stacks 0316 chain** (non-critical per ACYCLICITY plan) |
| O3 | `Spa_presheafValue_eq_rationalOpen` | `StructureSheaf.lean:2216` (sorry 2222) | **C3 Spa.comap** (task #77/#87/#95/#99 — separate planning thread) |
| O4 | SpaCompactNoHArch sub-lemma | `SpaCompactNoHArch.lean:223` | B2 candidate per comment at line 219 |
| O5 | SpaCompactNoHArch sub-lemma | `SpaCompactNoHArch.lean:312` | Per 2026-05-23 decomposition note |

---

## Frontier summary

**18 atomic sub-sorries on the critical path** (down from 15 leaves in the
earlier draft, but at finer granularity):

| Group | Leaves | LOC est | Wedhorn source |
|---|---|---|---|
| Lane C / W1 | L1–L5 | ~170 | Hübner 3.8 + Wedhorn Rem 7.15/Prop 6.4(3) + project bridges |
| W2 σ-walk | L6–L8 | ~100 | Wedhorn 8.34 Step (ii) + Cor 7.32 |
| W3 ratio | L9–L11 | ~160 | Wedhorn 8.34 Step (iii) + (i) |
| I.1.a graft | L12 | (composition) | composes L9–L11 |
| Gap B | L13 | ~5 | composes L1, L6–L12 via existing wrappers |
| Tate-aux | L14–L17 | ~70 | Wedhorn 6.18/7.15/Cor 5.50 |
| F12 move | L18 | 0 (structural) | Cor 8.32 (existing wrapper) |

**Total estimate:** ~510 LOC of substantive proof + ~50 LOC composition +
F12 relocation. Plus 5 off-critical-path sorries deferred (O1–O5).

**Confidence gate (three binding conditions):**
- ✅ Every leaf has its Lean signature read from the live tree (verified
  line numbers).
- ✅ Every leaf with a direct Wedhorn citation has an inline verbatim
  quote. Leaves without direct Wedhorn citation (L1 — Hübner; L4, L5 —
  project-internal) have their external citation named.
- ✅ Every leaf has a 5-attack adversarial pass; one leaf (L4) was
  flagged RED for potential B2 status — **needs verification before
  execution.**

---

## Recommended execution order (revised per expert review 2026-05-23)

The reviewer specifically reordered to put the **L1 strengthening + L4
replacement** *before* Tate-aux, because L4 is the only currently
identified false atom and other Lane-C work is risky on a tainted chain.

1. **F12 move** (L18, task #85). Structural; closes LaurentRefinement.lean's
   1 sorry. Does not depend on L4.
2. **L1 strengthened** (Lane C C1 in strengthened form per reviewer Q4).
   Add the `R({f}/f)` non-vanishing clause to the `LocalBasisHyp`
   predicate; prove via Hübner Lemma 3.8 / Zavyalov §2.3 style argument.
   ~80 LOC (slightly larger than original L1 due to strengthening).
3. **L4 replacement** (new `exists_per_D_finite_nonvanishing_cover_of_localBasisHyp`).
   Re-run compactness extraction on the refined opens
   `R(insert f T/s) ∩ R({f}/f)`. Once L1 strengthening lands this is
   ~30 LOC. **Closes B2 #21 and untaints the four Tier 0 (†) wrappers.**
4. **Tate-aux** (L14–L17, ~70 LOC each). Low-risk delegations to existing
   infrastructure.
5. **L2, L3, L5** (Lane C C3a/b/d, ~80 LOC each). C3c gone (was L4).
6. **L7, L8** (W2 structural + inducing, ~30 LOC each, GREEN).
7. **L9, L10** (W3 relative + inducing, ~50 LOC each, GREEN).
8. **L6** (W2 σ-walk, ~40 LOC, YELLOW).
9. **L11** (W3-transport, ~70 LOC, YELLOW — blocked on T-LOCLIFT-PRESERVATION
   task #38, **Approach 1 adopted**: prove `HasLocLiftPowerBounded
   (presheafValue D)` via Example 6.38 + Spa_presheafValue_eq_rationalOpen
   + power-bounded valuation criterion).
10. **L12** (I.1.a per-leaf, composition).
11. **L13** (Gap B, ~5 LOC composition; closes the target).

**End state:** `isSheafy_ofStronglyNoetherianTate_proof` (already sorry-free
at the wrapper level) compiles with **zero `sorry`** anywhere in its
transitive dependency closure.

---

## Action items before execution

1. ~~Verify L4~~ **DONE 2026-05-23.** Expert reviewer confirmed L4 is
   false as stated. Logged as **B2 #21** in
   `.mathlib-quality/b2_log.jsonl`. Replacement plan: strengthen the C2
   source via compactness on refined opens (see L4-REPLACED section
   above + new task `L4-replacement-nonvanishing-cover-extraction`).

2. **Audit L1's external citation:** confirm Hübner Lemma 3.8 or Zavyalov
   §2.3 statement matches `LocalBasisHyp C` predicate. If matches directly,
   GREEN-ify; otherwise spawn a sub-development.

3. **Verify SpaCompactNoHArch:223** B2 status per the comment at line 219
   ("flagged as a B2 candidate in `.mathlib-quality/b2_log.jsonl`"). Already
   in b2_log per #16 (Sierpinski leaf 6)? Verify cross-reference.

4. **T-LOCLIFT-PRESERVATION** (task #38) typeclass propagation onto
   `presheafValue D` — confirm scope before tackling L11.

---

## Process notes

- All file:line citations in this rewrite were verified by `grep` against
  the live tree on 2026-05-23. The earlier draft used line numbers from
  `docs/ACYCLICITY-CRITICAL-PATH-PLAN.md` which had drifted (`prop_8_30_flat_clean`
  was at :1543 in the doc but :1830 in the code, with status closed not open).
- The Wedhorn 8.28(b) chain is **dramatically more advanced** than the
  earlier decomposition implied: `AuditCleanWrappers.lean`,
  `EmbeddingTopo.lean`, and `RestrictionFlatness.lean` collectively close
  Cor 8.32, Prop 8.30, the tateAcyclicity ε/δ wrappers, the IsInducing tree
  induction, and the IsSheafy assembly — only the *atomic Wedhorn 8.34
  step (ii) and (iii) content + Hübner local-basis + Tate-aux + Gap B*
  remain open.
- This pass adheres to CLAUDE.md BINDING RULE: every leaf is provable
  *as currently stated*; no leaf has been proposed with a strengthened
  hypothesis-set. The flagged L4 is a **statement audit** flag, not a
  hypothesis-strengthening proposal.
- Per `--decompose` discipline: **no tickets created.** Planning-only-
  planning. Task list items #38, #60, #63–#68, #85, #88 are existing
  pending tickets that map onto leaves above; verifying their status is
  the next round's job.
