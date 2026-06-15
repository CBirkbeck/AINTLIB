# Finishing Tate Acyclicity (non-discrete): Dependency Map

**Date:** 2026-04-14
**Goal:** Make `tateAcyclicity` sorry-free for the non-discrete strongly noetherian Tate case.
**Prerequisite plan:** `2026-04-08-wedhorn-vs-zavyalov.md` (the main Wedhorn route).

## What's actually done (verified)

| Phase | Item | File:line |
|---|---|---|
| 1 | Audit + reframe R2 | DONE |
| 2.1 | Prop 6.17 statement | `NoetherianTateModules.lean:299` |
| 2.2 | Natural Tate topology on `TateAlgebra A` | `TateAlgebraTopology.lean` |
| 2.3 | Prop 6.17 proof (Krull intersection route) | `NoetherianTateModules.lean` |
| 2.4 | `(1-sX)` closed | `TateAlgebra.lean` |
| 2.5 | Quotient complete + T2 | `TateAlgebraTopology.lean` |
| 2.6 | Continuous bijection `tateQuotientToPresheafHom` | `TopologyComparison.lean:1616` |
| 2.7 | Banach → homeomorphism | `TopologyComparison.lean:2266` (`tateQuotientToPresheafHom_isHomeomorph`) |
| 4 (partial) | Route B: `laurentCover_gluing_presheaf` via `row3_exact` | `LaurentRefinement.lean:588` (reduced to 5 bridge stubs) |

**Phase 2 is fully in place:** the topological ring iso `presheafValue D ≃_top A⟨X⟩/(1-s·X)` is accessible via `presheafValueTateQuotientEquiv`, `presheafValueCanonicalQuotientEquiv`, and `tateQuotientToPresheafHom_isHomeomorph` (with 5 hypotheses, all dischargeable for strongly noetherian Tate rings).

## The real blockers (what's still sorry'd)

### Sorry layer A — "independent infrastructure"

These are not sorry-chained through other Tate-acyclicity sorries. Fixing any of them is a standalone win.

| Sorry | File:line | Dependency | Est. effort |
|---|---|---|---|
| `exists_spa_point_in_rationalOpen` (non-open prime case) | `StructureSheaf.lean:682` | Lemma 7.45 via completion (`Lemma745.lean` sorry-free) | ~80 lines |
| 5 Route B bridges | `LaurentRefinement.lean:419–480` | Phase 2 iso + base-change machinery | ~200 lines combined |
| `RationalLocData.completedLocSubring_isAdic` | `Presheaf.lean:421` | AdicCompletionBridge extension | ~50 lines |
| `PresheafTateStructure.lean:1073` (idealOfDef_pow_val_isClosed) | `PresheafTateStructure.lean:1073` | AdicCompletion map_exact | ~150 lines |

### Sorry layer B — "Phase 3/4/5 assembly"

These CAN be filled once layer A lands, but they assemble other pieces:

| Sorry | File:line | Blocks | Blocked by |
|---|---|---|---|
| `restrictionMapHom_surj` | `PresheafTateStructure.lean:1226` | `restrictionMap_isLocalization` | Baire infrastructure (or: skip via Route B) |
| `restrictionMapHom_injective` | `PresheafTateStructure.lean:1322` | `tateAcyclicity` Part 1, `rationalCovering_hasSeparation` | Cor 8.32 faithful flatness |
| `tateAcyclicity` Part 2 | `LaurentRefinement.lean:642` | `rationalCovering_hasGluing` (nonempty), `isSheafy...flat.gluing` | Lemma 8.34 + `laurentCover_gluing_presheaf` (Route B bridges) |
| `rationalCovering_hasSeparation` empty branch | `LaurentRefinement.lean:716` | `isSheafy...flat` empty edge | Spa-point at non-open prime (layer A) |
| `isSheafy_ofStronglyNoetherianTate_flat.embedding` | `StructureSheaf.lean:996` | `IsSheafy` instance | Phase 2 iso + 3×3 topological chase (Phase 4) |

## Critical path to sorry-free `tateAcyclicity`

```
  Lemma 7.45 completion → exists_spa_point_in_rationalOpen (non-open)  ─┐
                                                                        │
  ┌─── Phase 2 iso ────┐                                               │
  │    (DONE)          │                                               │
  │                    ↓                                               │
  │              presheafValue_flat_of_tateQuotient (DONE)              │
  │                    ↓                                               │
  │              Cor 8.32 faithful flatness  ←──────────────────────────┘
  │                    ↓                                               (uses Spa-point radical arg)
  │              restrictionMapHom_injective  ←──────── Cor 8.32 injectivity corollary
  │                    ↓
  │              tateAcyclicity Part 1 (rewrite)
  │
  └─── Route B ──→ 5 bridge lemmas ──→ laurentCover_gluing_presheaf (sorry-free via bridges)
                         ↓
                   Lemma 8.34 refinement transfer
                         ↓
                   tateAcyclicity Part 2 (rewrite)

  Result: tateAcyclicity sorry-free.
```

## Critical-path line budget

| Step | Est. lines |
|---|---|
| Non-open prime Spa-point (`exists_spa_point_in_rationalOpen`) | ~80 |
| Cor 8.32 (faithful flatness + radical arg) | ~150 |
| Rewrite `restrictionMapHom_injective` via Cor 8.32 | ~20 |
| Rewrite `tateAcyclicity` Part 1 using Cor 8.32 directly | ~15 |
| 5 Route B bridges (`laurentPlus/MinusBridge` + 3 compat) | ~200 |
| Lemma 8.34 (refinement transfer via `CechCohomology` + Laurent) | ~100 |
| Rewrite `tateAcyclicity` Part 2 via `laurentCover_gluing_presheaf` + 8.34 | ~50 |
| Rewrite `rationalCovering_hasSeparation` empty branch | ~10 |
| Dead code removal (Baire surj, old `restrictionMap_isLocalization`) | ~30 |
| **Total** | **~655** |

**Realistic pacing:** 3 sessions of ~200 lines each, or 2 sessions of ~325 lines.

## Suggested session order

**Session A (unblocking layer A + Phase 3 core):**
1. Fill `exists_spa_point_in_rationalOpen` non-open prime via Lemma 7.45 completion.
2. Prove Cor 8.32 (needs the above).
3. Rewrite `restrictionMapHom_injective` + Part 1 of `tateAcyclicity` via Cor 8.32.
4. Empty-branch `hasSeparation` via same Spa-point lemma.
5. **Expected end state:** separation-side sorry-free end-to-end; `tateAcyclicity` Part 2 still sorry.

**Session B (Route B bridges):**
1. Fill `laurentMinusBridge` (Phase 2 iso + base-change + unit-rescaling).
2. Fill `laurentPlusBridge` (Phase 2 iso + f-X identification).
3. Fill the three compat lemmas.
4. **Expected end state:** `laurentCover_gluing_presheaf` sorry-free end-to-end.

**Session C (Lemma 8.34 + final assembly):**
1. State + prove Lemma 8.34 (induction over `|T|`, uses `laurentCover_gluing_presheaf` + `CechCohomology` refinement).
2. Rewrite `tateAcyclicity` Part 2 using 8.34.
3. Rewrite `isSheafy_ofStronglyNoetherianTate_flat.embedding` via the topological iso chain.
4. Dead code removal.
5. **Expected end state:** `tateAcyclicity` sorry-free; `isSheafy_ofStronglyNoetherianTate_flat` sorry-free.

## Single-session partial-progress notes

If you only have one session:
- **Sessions A or B each produce a genuine, self-contained deliverable.** A yields separation; B yields Laurent gluing.
- **Do not start C without A+B both done** — C assembles other pieces and stalls without them.
- **Route B bridges (B)** are the most confined single-session target: they touch only `LaurentRefinement.lean` + `TopologyComparison.lean` and don't interact with the Spa-point infrastructure.

## Files that will be touched

- `LaurentRefinement.lean` (main: bridges, `tateAcyclicity`, `rationalCovering_*`)
- `StructureSheaf.lean` (Spa-point at non-open prime, `isSheafy_...flat`)
- `PresheafTateStructure.lean` (remove dead sorries, rewrite `restrictionMapHom_injective`)
- `CechCohomology.lean` or a new `Lemma8_34.lean` (refinement transfer)
- New: `Cor8_32.lean` or integrated into `StructureSheaf.lean` (faithful flatness)

## Known risks

1. **`exists_spa_point_in_rationalOpen` non-open prime case** is the most mathematically delicate piece. The completion route (take A/p completion as a Tate ring, use its Tate unit valuation, pull back) is well-trodden mathematically but needs careful topological bookkeeping. Budget a full session just for this.
2. **Route B bridges require non-discrete generalization of `tateQuotientFSubXEquiv`** (currently `[DiscreteTopology]` only). The complete-A setting should make this tractable via Phase 2 iso + evaluation at X=f, but the details need care around the T-extension topology.
3. **Lemma 8.34 may need `CechCohomology.Refinement` extensions** — check existing refinement API before writing new primitives.

---

## 2026-04-14 reviewer addendum — Q1/Q2/Q3 guidance

A full-context AI reviewer revisited the three architectural questions that
Wave 2 surfaced. The guidance reshapes the critical path below.

### Q1 — `mem_prime_of_rational_subset_nonOpen` (Presheaf.lean:665)

**Reviewer verdict:** the previous statement was unprovably strong. When
`rationalOpen D'.T D'.s` is empty (e.g., `X(1/π)` in some Tate settings), the
inclusion hypothesis is vacuous yet the conclusion `D'.s ∈ p` can fail.

**Resolution (commit 51f3332):** the non-open helper now takes an explicit
fiberwise-nonemptiness premise
`hnonempty : ∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp`. The public wrapper
`mem_prime_of_rational_subset` threads this conditionally on `¬IsOpen p`.
Three callers now hold the genuine obligation: Spa-point existence over a
non-open prime inside a specific rational open — Wedhorn Lemma 7.45 +
valuation-domination over `Frac(A/p)`.

Callers:
- `Presheaf.lean` `isUnit_algebraMap_s_of_huber`
- `CompletionLocalization.lean` `isUnit_algebraMap_s_of_subset`
- `PresheafTateStructure.lean` `isUnit_algebraMap_s_of_rational_subset`

**Recommended route if re-attempted:** algebraic via `K := Frac(A/p)`. Let
`R ⊂ K` be the image of `A⁺` plus the fractions `t/s` for `t ∈ D'.T`. If the
image of the ideal of definition is proper in `R`, pick `q ⊇ I·R`, localize,
and dominate by a valuation ring (every local subring of a field is dominated
by a valuation ring — standard, but not in current Mathlib). Pulling back gives
a continuous valuation of support `p` inside `rationalOpen D'.T D'.s`. Mathlib
lacks the "dominating valuation ring" existence theorem; that is a small
Zorn-based addition.

### Q2 — `structureSheaf` sheaf condition (StructureSheaf.lean:225)

**Reviewer verdict:** do not build `HasLimits CompleteTopCommRingCat`. That
path is a 150–300 line side quest and Zavyalov's theorem only needs the weaker
topological-ring sheaf formulation.

**Recommended route:** direct sheaf proof.
1. Existence/uniqueness of the glued section from the Types-level sheaf
   (`subpresheafToTypes.isSheaf`, Mathlib-provided).
2. Ring structure of the glued section: addition and multiplication are
   verified after restriction to the cover, so continuity is inherited.
3. Topological part: strict Laurent/Čech exactness.

**Status:** not yet attempted. Single-session target once Route B bridges land.

### Q3 — Route B bridges (LaurentRefinement.lean:419–495)

**Reviewer verdict:** the theorem should be generic in the base ring `B`
(complete strongly noetherian Tate), not bespoke to `presheafValue D₀`.
Zavyalov's Step 0/1 model: first replace by the completion, then replace a
rational subdomain by its own affinoid presentation `Spa(B, B⁺)` via
Lemma 2.13. The bridge theorem should live at a generic `B` and
`presheafValue D₀` is an instance via `B := presheafValue D₀`. That avoids
the "non-discrete `quotientFSubXEquiv` parameterised by `D₀`" trap.

**Q3-STEP1 (commit 7091dfb):** stripped spurious `[IsDomain A]` from the
Laurent-bridge chain (9 theorems). `presheafValueTateQuotientEquiv` itself
never required it; the annotation was copy-pasted across the bridge stubs
but never invoked. Krull intersection (the real `[IsDomain A]` dependency)
is confined to `epsilonHom_gen_injective` in the `General` section of
`LaurentCoverExact` and is never used by the Laurent-gluing path. The
bridges' eventual proofs must now work without `[IsDomain A]` on the outer
ring — correct direction for the generic-B target.

**Q3-STEP2 — iterated rational localization (Wedhorn Lemma 2.13):** the only
genuinely new primitive required. Precise statements for Q3-STEP3 to compose:

1. **Plus branch iterated-rational equivalence.**
   For `B := presheafValue D₀` and `b := D₀.canonicalMap f`, the rational open
   of `laurentPlusDatum D₀ f` in `Spa A` corresponds to the rational open
   of the "trivial plus datum on B at b" (i.e., `T_B = {b}`, `s_B = 1`) in
   `Spa B`. At the ring level:
   ```
   presheafValue_A(laurentPlusDatum D₀ f)  ≃+*  presheafValue_B(D_B_plus)
   ```
   where `D_B_plus : RationalLocData B` is the trivial datum at `b`.

2. **Non-discrete `f - X` quotient equivalence over a generic B.**
   Once (1) is in hand, we need:
   ```
   presheafValue_B(D_B_plus)  ≃+*  B⟨X⟩ ⧸ (algebraMap b − X)
                              =    LaurentCover.B₁_gen b
   ```
   The left side is the completion of `Localization.Away 1 ≃ B` with the
   topology that forces `b` to be power-bounded. The right side is the Tate
   algebra quotient forcing `X = b`. These agree because both are the
   universal complete Tate ring over `B` making `b` power-bounded.

3. **Minus branch symmetry.**
   For the minus datum `laurentMinusDatum D₀ f` (with `s = D₀.s · f`,
   `T` extended to force `D₀.s · f` power-bounded with `1/(D₀.s · f)`-relation),
   the analogous iterated-rational identification over `B` gives a datum
   `D_B_minus` with `s_B = b`. Then `presheafValueTateQuotientEquiv` at
   `A := B`, `D := D_B_minus` yields `B⟨X⟩ ⧸ (1 − b·X) = B₂_gen b`.

The minus branch can re-use the existing `presheafValueTateQuotientEquiv`
directly (no new quotient-equiv primitive needed). The plus branch requires
a new primitive (the `f − X` analogue of `presheafValueTateQuotientEquiv`) —
but crucially, this primitive lives **generically at base B**, not
parameterised by `D₀`.

**Q3-STEP2 line estimate:** ~120 lines for (1)+(2)+(3) statement+proof, with
proofs of (1) and (2) each comprising a substantive completion-topology
argument. (3) is a small reduction to existing machinery.

**Q3-STEP3:** compose Q3-STEP2 pieces inside the four `laurent±Bridge` stubs
in `LaurentRefinement.lean`. Each becomes 5–15 lines once Q3-STEP2 exists.

### Recommended order (post-addendum)

| Priority | Task | Est. lines |
|---|---|---|
| 1 | Q3-STEP2 statements + `iteratedRationalMinus` via `presheafValueTateQuotientEquiv` | ~40 |
| 2 | Q3-STEP2 `iteratedRationalPlus` (requires new f−X quotient equiv over generic B) | ~80 |
| 3 | Q3-STEP3: close 4 bridge sorries + 1 delta-compat | ~30 |
| 4 | Q2: direct sheaf proof (existence via Types; ring via pointwise ops; topology via Čech) | ~150 |
| 5 | Q1: if still on critical path, formalize valuation-ring domination over `Frac(A/p)` | ~120 |

If only one session is available: Q3-STEP2 (1)+(3) alone unlocks the minus
bridge and documents the plus bridge to a precise sorry.

---

## 2026-04-14 Q3 scaffolding complete

Commits `60802d8`, `8f959bd`, `f1020be` delivered the Q3 scaffolding:

| Commit | Artifact |
|---|---|
| `60802d8` | `iteratedPlusDatum_B`, `iteratedMinusDatum_B`: concrete `RationalLocData (presheafValue D₀)` with `hopen` fully discharged. |
| `8f959bd` | `presheafValue_iteratedPlus_equiv`, `presheafValue_iteratedMinus_equiv`: sorry'd `noncomputable def` stubs with precise signatures (Wedhorn Lemma 2.13). |
| `f1020be` | `laurent±Bridge` and composites tightened to accept `P : PairOfDefinition A` and noetherian hypotheses. `laurentMinusBridge` is now `iteratedMinus_equiv ≫ presheafValueTateQuotientEquiv at B` (5 hypothesis discharges sorry'd). `laurentPlusBridge` is `iteratedPlus_equiv ≫ presheafValue_trivialPlus_fSubX_equiv` (2 sorry'd factors). |

### Remaining Q3 sorries, organised by content

**Q3-STEP2C** — iterated rational identifications (Wedhorn Lemma 2.13):
- `presheafValue_iteratedPlus_equiv` at LaurentRefinement.lean.
- `presheafValue_iteratedMinus_equiv` at LaurentRefinement.lean.

Each identifies a completion-of-localization on `A` with a
completion-of-localization on `B := presheafValue D₀`. Both are
completion-theoretic equivalences.

**Q3-STEP2D** — non-discrete `f − X` quotient over generic Tate base B
(reviewer-flagged as the sole genuinely new primitive):
- `presheafValue_trivialPlus_fSubX_equiv` at LaurentRefinement.lean.

Identifies `presheafValue (iteratedPlusDatum_B)` with `TateAlgebra B ⧸
(algebraMap(canonicalMap f) − X)`. Both are universal complete
nonarchimedean `B`-algebras in which `canonicalMap f` is power-bounded.

**Q3-STEP4** — `presheafValueTateQuotientEquiv` hypothesis discharges
at `A := presheafValue D₀` (inside `laurentMinusBridge`, 5 sorries):
`hb`, `hcs`, `ht0`, `hcont_eval`, `hdense` at the B level. Consider
switching to `presheafValueCanonicalQuotientEquiv` (different 5
hypotheses) or to the full `tateQuotientToPresheafHom_isHomeomorph`
(7 hypotheses including BaireSpace and SigmaCompactSpace).

**Q3-STEP5** — compat theorems:
- `laurentPlusBridge_restrictionMap`, `laurentMinusBridge_restrictionMap`,
  `laurentBridge_delta_eq_zero_of_compat` at LaurentRefinement.lean.

These three are still sorry'd. They depend on the specific forms of
iterated rational / quotient equivs, so cannot be discharged until
Q3-STEP2C/STEP2D/STEP4 land.

### Current sorry count contribution (bridge chain only)

- 2 iterated rational identifications (Q3-STEP2C).
- 1 non-discrete f−X primitive (Q3-STEP2D).
- 5 hypothesis discharges in `laurentMinusBridge` (Q3-STEP4).
- 3 compat theorems (Q3-STEP5).
- **Total: 11 bridge-related sorries** (out of 103 total project sorries).

Each is targeted at a specific, documented mathematical obligation. No
sorry in the bridge chain is vague or unprovably strong.
