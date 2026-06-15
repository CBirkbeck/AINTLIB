# Axiom-Clean Tickets v4: Remove sorryAx from isSheafy via Wedhorn

**Goal:** `isSheafy_ofStronglyNoetherianTate_flat` axiom-clean.

**Key insight (2026-04-03, reviewer):** `locLift_preimage_locNhd` (old S1) is **FALSE**.
Individual restriction maps are NOT topological embeddings.

**Counterexample (Conrad):** `A = Q_p⟨X⟩`, `U = R({p,X}/p)`. Then `X^m ∈ p^m A₀[X/p]`
but `X^m ∉ pA₀`, so no backward neighborhood inclusion exists.

**Key insight (2026-04-08, audit v1):** Wedhorn's published proof of
Theorem 8.28(b) (lecture notes `1910.05934v1.pdf` pp. 81–85) goes via
**flatness** (Lemma 8.31) + **Laurent cover acyclicity** (Lemma 8.33) +
**refinement transfer** (Lemma 8.34) — no defect-correction or Banach-OMP
on the completed Čech complex. The earlier v2 architecture
(R2 = "strict exactness via Banach open mapping") was using the wrong tool.

**Key insight (2026-04-08, audit v2 / Option A):** Our `IsSheafy` class
DOES require the full sheaf-of-topological-rings condition (embedding field,
matching Wedhorn Def 8.26). Initially we considered weakening to
sheaf-of-sets, but this would have left `AffinoidAdicSpace` out of sync with
the standard Wedhorn definition. The topological embedding is reachable in
the Wedhorn flatness route IF Phase 2 produces Example 6.38 as a
**TOPOLOGICAL** ring iso (not just algebraic), because the 3×3 diagram chase
then preserves topology through Tate-algebra quotient identifications
(quotient maps of Tate algebras are continuous and open).

**The defect-correction approach was the wrong TOOL, not the wrong GOAL.**
The goal (topological embedding for the product restriction) is correct.
The Wedhorn route achieves it via the universal-property topological iso in
Example 6.38, not via defect correction.

See `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` for the full Wedhorn plan
and `docs/STATUS.md` for the Phase 1 + Option A session log.

---

## New Architecture (v4, 2026-04-08)

**DELETE** the false chain (R1, done):
- `locLift_preimage_locNhd` (FALSE)
- `locLift_isUniformInducing` (depends on above)
- `restrictionMapAlg_isUniformInducing` (depends on above)
- `restrictionMapHom_isInducing` (depends on above)
- `productRestrictionSub_isInducing` (depends on above)

**DELETE** the topological R2 chain (deprecated 2026-04-08):
- `defect_correction_exists` (`LaurentRefinement.lean`) — DELETED
- `compatible_sections_in_image` (`LaurentRefinement.lean`) — DELETED
- `density_approximation` (`LaurentRefinement.lean`) — DELETED
- The "topological embedding" framing of `IsSheafy` docstring — FIXED

**REPLACE** with the Wedhorn flatness route:
```
Lemma 8.31  (A⟨X⟩, A⟨X⟩/(f-X), A⟨X⟩/(1-fX) flat over A — DONE in TateAlgebra.lean)
    ↓
Prop 6.17   (ideals in noeth Tate are closed — Phase 2.3)
    +
Tate topology on A⟨X⟩  (the full ring, not just A₀⟨X⟩ — Phase 2.2)
    ↓
Example 6.38  (presheafValue D ≃+* A⟨X⟩/(closed ideal) as TOPOLOGICAL rings —
               Phase 2, universal property preserves topology)
    ↓
Cor 8.32  (faithful flatness of product restriction → injective — R2a)
    ↓                                              ↓
Embedding (IsSheafy.embedding)          Lemma 8.33 (2-element Laurent cover acyclic,
= separation (injective) + inducing      3×3 chase, topology preserved via Example 6.38 — R2b)
(from Cor 8.32 + topology preserved                ↓
 through Example 6.38 iso)               Lemma 8.34 (refinement transfer to rational covers — R2c)
                                                   ↓
                                         Gluing (IsSheafy.gluing)
```

**KEEP:**
- Algebraic exactness (T1: `row3_exact`, sorry-free) — feeds Lemma 8.33
- Refinement infrastructure (`CechCohomology.lean`, `Refinement`) — feeds Lemma 8.34
- Flatness of `A⟨X⟩` and quotients (`tateAlgebra_flat`, `flat_quotient_*_general`) — feeds Cor 8.32
- Lemma 7.54 (`rationalOpen_eq_iInter_singleton`) — feeds Lemma 8.34
- Lemma 7.45 (`Lemma745.lean`) — Spa-point construction for the radical-of-annihilator step in Cor 8.32
- `pairSubring P`, `pairIdeal P`, `pairSubring_isHuberRing` (`TateAlgebraTopology.lean`) — base layer for Phase 2.2
- `IsModuleTopology.isOpenMap_of_surjective_of_finite` (`NoetherianTateModules.lean`) — Prop 6.18(2), feeds Phase 2.3

---

## Tracker

| Ticket | Status | Agent | Notes |
|--------|--------|-------|-------|
| **R1** | DONE | claude-opus | 2026-04-03. Quarantined false chain, gave restrictionMapHom_injective a sorry for new proof. |
| **R2 (v2 strict-exactness)** | REFRAMED | claude-opus | 2026-04-08 Phase 1. Replaced by Wedhorn flatness route below. defect_correction_exists, compatible_sections_in_image, density_approximation deleted; tateAcyclicity Part 2 reframed. |
| **R2-Phase1 (audit + reframe + Option A)** | DONE | claude-opus | 2026-04-08. `IsSheafy` class restored to sheaf-of-topological-rings (embedding field, Option A); discrete instance sorry-free; `isSheafy_…_flat` reduced to single sorry pointing at Phase 2-4; docstrings + ticket file updated. |
| **R2-Phase2.1 (Wedhorn Prop 6.17 statement)** | DONE | claude-opus | 2026-04-08. `Wedhorn.isClosed_ideal_of_noetherian` stated with sorry in `NoetherianTateModules.lean:299`. API now available for downstream work. |
| **R2-Phase2.2 (Tate topology on `A⟨X⟩`)** | NOT STARTED | — | **Highest leverage. ~200 lines.** Define topology on full `TateAlgebra A` (not just `pairSubring P`) making it a Huber ring with pair `(pairSubring P, pairIdeal P)`; prove Tate ring, complete, Hausdorff. Independent of 2.3. |
| **R2-Phase2.3 (Wedhorn Prop 6.17 proof)** | DONE | claude | 2026-04-08. `Wedhorn.isClosed_ideal_of_noetherian` proved sorry-free via **Route 2: Krull intersection in noetherian A₀**. Signature takes `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as explicit hypothesis (the `[IsNoetherianRing A]` from the v1 signature is now unused and removed). Proof strategy: (a) `A₀ = P.A₀` closed in `A` (open subgroup), inherits complete + T2; (b) helper `isClosed_ideal_of_adicComplete_noetherian` proves `J₀ := J.comap A₀.subtype` closed in `A₀` via `IsAdicComplete.le_jacobson_bot` + `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`; (c) lift to `A` using a principal pair `P'` (via `IsTateRing.exists_principal_pairOfDefinition`) with generator `π`: for `x ∈ closure(J)`, `π^k · x → 0` lands in `A₀` for some `k`, lies in `J.closure ∩ A₀ = J₀ ⊆ J`, then `x = π^(-k) · (π^k · x) ∈ J`. Axioms: `{propext, Classical.choice, Quot.sound}` — only standard mathlib axioms. |
| **R2-Phase2.4 ((1-sX) closed)** | NOT STARTED | — | ~30 lines. Apply 2.3 (via 2.1 API) to `oneSubfXIdeal D.s` using the 2.2 topology. Depends on 2.2 + 2.3. |
| **R2-Phase2.5 (quotient complete + T2)** | NOT STARTED | — | ~50 lines. `A⟨X⟩/(1-sX)` with quotient topology is complete (quotient of complete by closed) + T2 (closed ideal). Depends on 2.4. |
| **R2-Phase2.6 (continuous bijection)** | NOT STARTED | — | ~200 lines. Show `tateQuotientToPresheafHom D hb` is continuous + bijective (injectivity: ker = (1-sX); surjectivity: dense + closed image). Depends on 2.2 (for continuity) + 2.5 (for surjectivity via complete image). |
| **R2-Phase2.7 (Banach → homeomorphism)** | NOT STARTED | — | ~50 lines. Continuous bijection between complete T2 topological rings + Banach (Wedhorn Thm 6.16) ⇒ homeomorphism ⇒ topological ring iso. Depends on 2.6. |
| **R2a (Cor 8.32 faithful flatness)** | NOT STARTED | — | ~150 lines. Uses Phase 2.7 iso + `flat_quotient_oneSubfX_general` + Spa-point radical arg for the Tate case. Gives `IsSheafy.embedding` (via injective part). Depends on 2.7. Parallel with R2b. |
| **R2b (Lemma 8.33 in Tate case)** | NOT STARTED | — | ~150 lines. 3×3 diagram chase using Phase 2.7 iso + algebraic core `row3_exact`. Parallel with R2a. |
| **R2c (Lemma 8.34 refinement assembly)** | NOT STARTED | — | ~100 lines. Refinement transfer (Lemma 7.54 + Prop A.3 from `CechCohomology.lean`). Depends on R2b. |
| **R3 (refactor IsSheafy)** | OBSOLETE | — | Phase 1 audit + Option A landed the correct spec (sheaf-of-topological-rings via embedding field). R3's original task ("remove strict exactness dependency") is no longer meaningful. |
| **R4** | IN PROGRESS | claude | 2026-04-08. `isIntegral_of_forall_valuation_le_one` PROVED (Wedhorn Prop 7.18). `locLift_vle_one_at_spa` mostly proved. Tate instance has 2 sorries in PresheafIdentification.lean isolated as named lemmas: (1) `tate_aplus_le_A₀_sorry` (typeclass design — A⁺ ⊆ D'.P.A₀ not bundled), (2) `tate_vle_one_on_A₀_isContinuous_sorry` documented as **FALSE** in general (counterexample: trivial valuation; needs Wedhorn 7.22 / non-triviality witness OR refactor of integral criterion to topology-aware version). **Fully independent of R2.** |
| **R5** | DONE | claude | 2026-04-08. `IsHuberRing.firstCountableTopology` instance in HuberRings.lean derives it from the pair of definition via `hasBasis_nhds_zero` + translation. Removed 36/37 explicit `[FirstCountableTopology A]` hypotheses (1 remains in TateAlgebra.lean `MuMapSurjective` section which lacks `[IsHuberRing A]`). Full project builds. |

## Dependency Graph (v4, 2026-04-08)

```
                         R1 ─ DONE ──────────────────────────────────┐
                          │                                          │
                          ▼                                          │
              ┌─ Phase1 (audit/reframe/Option A) ─ DONE ─┐           │
              │                                          │           │
              ▼                                          ▼           │
     ┌────────────────────┐                 ┌──────────────────┐    │
     │ Phase2.1 (6.17 API) │                │ R4 (HasLocLift…)  │    │
     │       DONE          │                │  IN PROGRESS      │    │
     └────────────┬────────┘                │  INDEPENDENT      │    │
                  │                         └──────────────────┘    │
          ┌───────┴───────────┐                                      │
          │                   │                                      │
          ▼                   ▼                                      │
  ┌────────────────┐  ┌────────────────┐                             │
  │ Phase2.2       │  │ Phase2.3       │                             │
  │ Tate topology  │  │ Prop 6.17 proof│                             │
  │ on A⟨X⟩ (~200) │  │ (~150)         │                             │
  │                │  │                │                             │
  │  ★ PARALLEL ★  │  │  ★ PARALLEL ★  │                             │
  └───────┬────────┘  └───────┬────────┘                             │
          │                   │                                      │
          └──────┬────────────┘                                      │
                 ▼                                                   │
        ┌───────────────────┐                                        │
        │ Phase2.4          │                                        │
        │ (1-sX) closed     │                                        │
        │ (~30)             │                                        │
        └────────┬──────────┘                                        │
                 ▼                                                   │
        ┌───────────────────┐                                        │
        │ Phase2.5          │                                        │
        │ quot complete+T2  │                                        │
        │ (~50)             │                                        │
        └────────┬──────────┘                                        │
                 ▼                                                   │
        ┌───────────────────┐                                        │
        │ Phase2.6          │                                        │
        │ cont. bijection   │                                        │
        │ (~200)            │                                        │
        └────────┬──────────┘                                        │
                 ▼                                                   │
        ┌───────────────────┐                                        │
        │ Phase2.7          │                                        │
        │ Banach→homeo      │                                        │
        │ (~50)             │                                        │
        └────────┬──────────┘                                        │
                 │                                                   │
       ┌─────────┴─────────┐                                         │
       ▼                   ▼                                         │
  ┌─────────┐        ┌─────────┐                                     │
  │ R2a     │        │ R2b     │                                     │
  │ Cor 8.32│        │ Lemma   │                                     │
  │ (~150)  │        │ 8.33    │                                     │
  │         │        │ (~150)  │                                     │
  │★PARALLEL│        │★PARALLEL│                                     │
  └────┬────┘        └────┬────┘                                     │
       │                  │                                          │
       └────────┬─────────┘                                          │
                ▼                                                    │
       ┌───────────────┐                                             │
       │ R2c           │                                             │
       │ Lemma 8.34    │                                             │
       │ assembly      │                                             │
       │ (~100)        │                                             │
       └───────────────┘                                             │
                                                                     │
                                                     R5 ─ DONE ──────┘
```

### Wave-by-wave parallelism

**Wave 0 (done):** R1, Phase1, Phase2.1, R5.

**Wave 1 (currently available — 3 parallel agents):**
- `R4` (HasLocLiftPowerBounded — 2 sorries, independent of R2)
- `Phase2.2` (Tate topology on `A⟨X⟩` — infrastructure for R2)
- `Phase2.3` (Prop 6.17 proof — infrastructure for R2)

**Wave 2 (after Phase2.2 + Phase2.3, sequential):**
- Phase2.4 → Phase2.5 → Phase2.6 → Phase2.7

  (Can partially parallelize within Phase2.6: 2.6a continuity needs only 2.2, while 2.6b/2.6c need 2.5. One agent could start on continuity once 2.2 is done.)

**Wave 3 (after Phase2.7 — 2 parallel agents):**
- `R2a` (Cor 8.32 faithful flatness → embedding field of `IsSheafy`)
- `R2b` (Lemma 8.33 in Tate case)

**Wave 4 (after R2b):**
- `R2c` (Lemma 8.34 + final assembly)

### Notes on parallelism

- **Phase2.2 and Phase2.3 are genuinely independent.** 2.2 is a specific construction (Tate topology on `A⟨X⟩` via `pairSubring P`); 2.3 is a general theorem about complete noetherian Tate rings, agnostic to which ring. Two agents can tackle them simultaneously without touching each other's files.
- **R4 is independent of R2 entirely.** R4 is about `HasLocLiftPowerBounded.tate` (eliminating the typeclass hypothesis for Tate rings); R2 is about `IsSheafy.ofStronglyNoetherianTate_flat`. They touch different files (`PresheafIdentification.lean` vs. `StructureSheaf.lean`/`TateAlgebraTopology.lean`). An R4 agent can run concurrently with any R2 wave.
- **R2a and R2b in Wave 3 are independent.** R2a builds Cor 8.32 from the Phase 2 iso + existing flatness; R2b runs the 3×3 diagram chase using the Phase 2 iso. They touch different theorems and can be parallelized.
- **Phase2.6 is the only genuinely hard sequential block** within Phase 2. It has the most lines (~200) and the most subtlety (injectivity `ker = (1-sX)` in the Tate case is non-trivial). Consider budgeting 2 sessions for 2.6.

---

## TICKET R1: Delete False Inducing Chain — DONE 2026-04-03

Quarantined the false `locLift_preimage_locNhd` chain. Kept forward-direction
infrastructure (`locLift_maps_locNhd`, `restrictionMapAlg_continuous`,
`restrictionMapHom_surj`). See commit history for details.

---

## TICKET R2 (v3): Wedhorn Flatness Route

**Status:** REFRAMED 2026-04-08; broken into Phase1 (done) / Phase2.1-2.7 / R2a / R2b / R2c.
**Total estimate:** ~900 lines across 10 sub-tickets.
**Replaces:** the v2 "strict exactness via Banach open mapping" framing, which was the wrong tool for the right goal. The goal (topological embedding for product restriction) IS correct (matches Wedhorn 8.26); the Wedhorn route achieves it via the universal-property topological iso in Example 6.38.
**Reference:** `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md`.

### Overall task

Prove `isSheafy_ofStronglyNoetherianTate_flat` axiom-clean via Wedhorn's published proof of Theorem 8.28(b) (lecture notes pp. 81–85):

1. **Phase 1 (audit + reframe + Option A) — DONE:** restore `IsSheafy.embedding` field (Wedhorn 8.26); delete defect-correction red herring; reframe `tateAcyclicity` around the Wedhorn route.
2. **Phase 2 (Example 6.38 in the Tate case):** Establish `presheafValue D ≃_top A⟨X⟩/(closed ideal)` as a **topological** ring iso for strongly noetherian Tate `A`. Sub-tasks 2.1-2.7.
3. **R2a (Cor 8.32):** Faithful flatness of the product restriction `presheafValue C.base → ∏ presheafValue D` ⇒ injectivity. Combined with the topology-preserving iso from 2.7, this gives `IsSheafy.embedding`.
4. **R2b (Lemma 8.33 in Tate case):** 2-element Laurent cover acyclicity via the 3×3 diagram chase, lifted from the algebraic core `LaurentCoverExact.row3_exact` through the iso from 2.7.
5. **R2c (Lemma 8.34 + assembly):** Refinement transfer (Lemma 7.54 + Prop A.3) to general rational covers ⇒ `IsSheafy.gluing`.

---

### R2-Phase2: Example 6.38 in the Tate case (~680 lines total)

**Overall goal:** Prove that for strongly noetherian Tate `A` with compatible plus subring, there is a canonical **topological ring isomorphism**
```
presheafValue D  ≃_top  TateAlgebra A ⧸ oneSubfXIdeal D.s
```
The iso must preserve topology (not just be a ring iso) because the downstream 3×3 diagram chase (R2b) preserves topology through it.

#### Phase 2.1: Wedhorn Prop 6.17 API — DONE

Stated `Wedhorn.isClosed_ideal_of_noetherian` in `NoetherianTateModules.lean:299` as a theorem with sorry. Signature:
```lean
theorem Wedhorn.isClosed_ideal_of_noetherian
    {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [T2Space A] [CompleteSpace A] [IsNoetherianRing A]
    [IsTateRing A] (I : Ideal A) : IsClosed (I : Set A)
```
The API is available for downstream Phase 2 work to cite.

#### Phase 2.2: Natural Tate topology on `TateAlgebra A`

**Estimated:** ~200 lines.
**Independent of 2.3** — can be done in parallel.
**Location:** new section in `TateAlgebraTopology.lean` or new file.

**Task.** Define a topology on `TateAlgebra A` (the full ring, not just the subring `pairSubring P`) such that `pairSubring P ⊂ TateAlgebra A` is an open subring with the existing `(pairIdeal P)`-adic topology from `pairSubring_isHuberRing`. Prove:

1. `@TopologicalSpace (TateAlgebra A)` instance compatible with `pairSubring P` being open.
2. `@IsTopologicalRing (TateAlgebra A)` with this topology.
3. `@IsHuberRing (TateAlgebra A)` with pair of definition `(pairSubring P, pairIdeal P)`.
4. `@IsTateRing (TateAlgebra A)` when `A` has a topologically nilpotent unit.
5. `@CompleteSpace (TateAlgebra A)` — follows from `pairSubring P` being complete (I-adic completeness of `MvPowerSeries` + Mathlib's `AdicCompletion.completeSpace`) + the localization-at-π argument.
6. `@T2Space (TateAlgebra A)` — follows from `⋂ I^n = 0` in `pairSubring P` (Krull intersection).
7. `@IsNoetherianRing (TateAlgebra A)` when `A` is strongly noetherian (this is essentially the definition of strongly noetherian).

**Key technique.** Use the "Huber ring from pair of definition" pattern. `TateAlgebra A` is the localization of `pairSubring P` at the image of `π ∈ A`, and the topology is the pair topology with basis `{π^n · pairSubring P}`.

#### Phase 2.3: Wedhorn Prop 6.17 proof

**Estimated:** ~150 lines.
**Independent of 2.2** — can be done in parallel.
**Location:** `NoetherianTateModules.lean` (fill the 2.1 sorry).

**Task.** Prove `Wedhorn.isClosed_ideal_of_noetherian`. The argument:

1. Let `A` be a complete noetherian Tate ring, `I ⊆ A` an ideal.
2. `A/I` is a finitely generated `A`-module (generated by `1`).
3. By Wedhorn Prop 6.18(1), there is a canonical complete Hausdorff `A`-module topology on `A/I`. Use Mathlib's `IsModuleTopology` machinery plus the strict-exactness package in `NoetherianTateModules.lean`.
4. The quotient map `A → A/I` is continuous (Prop 6.18(2), equivalent to Mathlib's `IsModuleTopology.continuous_linearMap_of_finite`).
5. `A/I` is T2 (Hausdorff).
6. `I = π⁻¹({0})` is closed as preimage of `{0}` (closed in T2) under a continuous map.

**Hard part.** Step 3's Hausdorffness of the canonical topology on `A/I`. This uses `⋂ (I^n · (A/I)) = 0` via Krull intersection for noetherian rings, combined with the fact that `{I^n · (A/I)}` is a neighborhood basis.

#### Phase 2.4: `(1-sX)` closed

**Estimated:** ~30 lines.
**Depends on:** Phase 2.2 + Phase 2.3.
**Location:** `PresheafIdentification.lean` or `TopologyComparison.lean`.

One-line application: `Wedhorn.isClosed_ideal_of_noetherian (oneSubfXIdeal D.s)` with `TateAlgebra A` now carrying the topology from 2.2.

#### Phase 2.5: Quotient complete + T2

**Estimated:** ~50 lines.
**Depends on:** Phase 2.4.

The quotient `TateAlgebra A ⧸ oneSubfXIdeal D.s` with the quotient topology is:
- Complete (quotient of complete by closed ideal).
- T2 (quotient by closed ideal in T2).
- A topological ring.

Uses Mathlib's `Ideal.Quotient.completeSpace` / `Ideal.Quotient.t2Space` if available, or direct proof.

#### Phase 2.6: Continuous bijection

**Estimated:** ~200 lines.
**Depends on:** Phase 2.2 (for continuity of the map), Phase 2.5 (for surjectivity via complete image).
**Location:** `TopologyComparison.lean` (revise the existing `presheafValueTateQuotientEquiv`).

**Three sub-parts that can be partially parallelized:**

- **2.6a — Continuity:** show `tateQuotientToPresheafHom D hb` is continuous from the 2.2 quotient topology to the completion topology on `presheafValue D`. Via the universal property of `presheafValue D` (Wedhorn §5.51 / `locTopology_continuous_lift`) + extension to the quotient. **Needs only 2.2** — can start as soon as 2.2 is done.

- **2.6b — Injectivity (`ker = (1-sX)`):** in the Tate case, show `ker(tateEvalPresheafHom D hb) = oneSubfXIdeal D.s`. The `⊇` direction is `oneSubsX_le_ker_tateEvalPresheafHom` (already have). The `⊆` direction is the hard part — in the discrete case it uses the polynomial-division argument via `evalInvFHom`, but that doesn't generalize directly. For the Tate case, use: if `g ∈ ker`, then `g` is in the closure of `(1-sX)` (density argument), and since `(1-sX)` is closed (from 2.4), `g ∈ (1-sX)`.

- **2.6c — Surjectivity:** the image contains `D.canonicalMap(A)` which is dense in `presheafValue D`. The image is complete (continuous image of complete under 2.2's topology) → closed (in T2 = `presheafValue D` is T2 from `[T2Space A]` + completion) → all of `presheafValue D`.

#### Phase 2.7: Banach → homeomorphism

**Estimated:** ~50 lines.
**Depends on:** Phase 2.6.

From 2.6: `tateQuotientToPresheafHom D hb` is a continuous ring bijection between complete topological rings with countable nhd bases. By Wedhorn Thm 6.16 (Banach open mapping — already stated in `NoetherianTateModules.lean` as `AddMonoidHom.isOpenMap_of_complete_countable`), it is open. A continuous open bijection is a homeomorphism. Package as a topological ring iso (`RingEquiv` + `IsHomeomorph` or `ContinuousRingEquiv`).

This completes Example 6.38: `presheafValue D ≃_top A⟨X⟩/(oneSubfXIdeal D.s)`.

---

### R2a: Cor 8.32 (faithful flatness of product restriction)

**Estimated:** ~150 lines.
**Depends on:** Phase 2.7 (the topological iso).
**Parallel with:** R2b.

1. Use Phase 2.7 iso + `flat_quotient_oneSubfX_general` ⇒ `presheafValue D` flat over `A` (unconditionally, no TopologyComparison hypotheses).
2. Assemble faithful flatness of the product `presheafValue C.base → ∏ presheafValue D`.
3. The "no prime of `presheafValue C.base` lies in all kernels" step uses the Spa-point radical argument. We have the discrete-case analog (`base_s_mem_annihilator_radical` in `Presheaf.lean`); the Tate case will use Lemma 7.45 (`Lemma745.lean`) to construct Spa points in the required rational opens.
4. Faithful flatness ⇒ injective on elements with vanishing restrictions ⇒ **sheaf separation**.
5. Combined with the topological iso from 2.7 (which preserves topology through the diagram chase), this gives the full `IsSheafy.embedding` field.

### R2b: Lemma 8.33 in the Tate case

**Estimated:** ~150 lines.
**Depends on:** Phase 2.7 (the topological iso).
**Parallel with:** R2a.

The 3×3 diagram chase: use the ring isos from Phase 2.7 to identify
- `presheafValue R(f/1) ≃_top A⟨ζ⟩/(f-ζ)`
- `presheafValue R(1/f) ≃_top A⟨η⟩/(1-fη)`
- `presheafValue R(f, 1/f) ≃_top A⟨ζ, ζ⁻¹⟩/(f-ζ)`

Then run Wedhorn's diagram chase (lecture notes p. 83). The algebraic core (`row3_exact`) is in `LaurentCoverExact.lean` already (sorry-free, general case). The topology is preserved because Tate-algebra quotient maps are continuous and open.

### R2c: Lemma 8.34 + assembly

**Estimated:** ~100 lines.
**Depends on:** R2b.

- Laurent cover induction (Wedhorn Lemma 8.34(i)): every Laurent cover is acyclic.
- Refinement (8.34(ii,iii)): every rational cover generated by `T` with `T·A = A` refines to a Laurent cover.
- Assembly: `IsSheafy.gluing` via `tateAcyclicity` Part 2 (`LaurentRefinement.lean`).
- This also discharges the single sorry still in `isSheafy_ofStronglyNoetherianTate_flat.embedding` (the `s ≠ 0` branch, modulo R2a).

---

## TICKET R3: OBSOLETE (2026-04-08)

The original R3 was "refactor `isSheafy_ofStronglyNoetherianTate_flat` to use strict exactness instead of `productRestrictionSub_isInducing`". This is no longer relevant: there is no strict exactness step in the Wedhorn route, and `IsSheafy` only requires sheaf-of-sets. The misleading "topological embedding" docstring on `IsSheafy` was fixed in Phase 1.

---

## TICKET R4: HasLocLiftPowerBounded.tate (Power-Bounded from Rational Containment)

**Status:** IN PROGRESS (claude, 2026-04-08)
**Estimated:** ~100 lines remaining
**Independent of R2** — different files, different sorries. Can run in parallel with any Phase 2 agent.

### Task

Establish the `HasLocLiftPowerBounded A` typeclass instance for strongly
noetherian Tate rings with a compatible plus subring (Wedhorn Prop 7.14 /
"adic Nullstellensatz" + valuative criterion for integrality).

### Progress

- `isIntegral_of_forall_valuation_le_one` — **PROVED** (topology-aware
  Wedhorn Prop 7.18 / Hu2 Lemma 3.3).
- `locLift_vle_one_at_spa` — mostly proved.
- `HasLocLiftPowerBounded.tate` instance in `PresheafIdentification.lean`
  has 2 remaining sorries isolated as named lemmas.

### Remaining sorries

1. `tate_aplus_le_A₀_sorry` — typeclass design issue: `(A⁺ : Set A) ⊆ D'.P.A₀`
   not bundled. Discharged via the `CompatiblePlusSubring` typeclass
   (Wedhorn Remark 7.17).
2. `tate_vle_one_on_A₀_isContinuous_sorry` — documented as **FALSE** in
   general (counterexample: trivial valuation). Needs Wedhorn 7.22 /
   non-triviality witness OR refactor of integral criterion to
   topology-aware version.

### Interaction with R2

R2 currently takes `hb : IsPowerBounded (invS D)` as a hypothesis (or uses
the `HasLocLiftPowerBounded A` typeclass). Once R4 lands, the typeclass
instance is automatic for strongly noetherian Tate rings and the
hypothesis can be removed from R2's statements. Until then, R2 and R4
proceed independently — R2 just treats `HasLocLiftPowerBounded` as an
external typeclass hypothesis.

---

## TICKET R5: Remove FirstCountableTopology — DONE 2026-04-08

`IsHuberRing.firstCountableTopology` instance in `HuberRings.lean` derives
first-countability from the pair of definition via `hasBasis_nhds_zero` +
translation. Removed 36 of 37 explicit `[FirstCountableTopology A]`
hypotheses. One remains in `TateAlgebra.lean` `MuMapSurjective` section
(which lacks `[IsHuberRing A]`). Full project builds.

---

## Summary (v4, 2026-04-08)

| Ticket | Lines | Depends on | Parallel with | Difficulty | Status |
|--------|-------|------------|---------------|------------|--------|
| R1 | ~50 | — | — | Easy | ✓ DONE |
| Phase1 (audit + Option A) | ~150 | R1 | — | Easy | ✓ DONE |
| **Phase2.1** (6.17 API) | ~30 | Phase1 | — | Easy | ✓ DONE |
| **Phase2.2** (Tate topology on `A⟨X⟩`) | ~200 | Phase2.1 | **Phase2.3, R4** | Hard | ⚠ NEXT |
| **Phase2.3** (Prop 6.17 proof) | ~150 | Phase2.1 | **Phase2.2, R4** | Hard | ⚠ NEXT |
| **Phase2.4** ((1-sX) closed) | ~30 | Phase2.2 + Phase2.3 | — | Easy | pending |
| **Phase2.5** (quot complete+T2) | ~50 | Phase2.4 | — | Easy | pending |
| **Phase2.6a** (continuity) | ~50 | Phase2.2 | Phase2.6b/c | Medium | pending |
| **Phase2.6b** (injective ker=(1-sX)) | ~100 | Phase2.4 | Phase2.6a/c | Hard | pending |
| **Phase2.6c** (surjective via closed image) | ~50 | Phase2.5 | Phase2.6a/b | Medium | pending |
| **Phase2.7** (Banach → homeo) | ~50 | Phase2.6 | — | Easy | pending |
| **R2a** (Cor 8.32 faithful flatness) | ~150 | Phase2.7 | **R2b, R4** | Medium | pending |
| **R2b** (Lemma 8.33 Tate) | ~150 | Phase2.7 | **R2a, R4** | Medium | pending |
| **R2c** (Lemma 8.34 + assembly) | ~100 | R2b | — | Easy | pending |
| R3 | — | — | — | — | ✗ OBSOLETE |
| **R4** (HasLocLiftPowerBounded) | ~100 | — | **everything in R2** | Hard | 🔄 IN PROGRESS |
| R5 | ~50 | — | — | Medium | ✓ DONE |

**Critical path:** R1 → Phase1 → Phase2.1 → (Phase2.2 ∥ Phase2.3) → Phase2.4 → Phase2.5 → Phase2.6 → Phase2.7 → (R2a ∥ R2b) → R2c.

**Parallelism opportunities:**
- **Now (3 agents):** Phase2.2, Phase2.3, R4 can all run concurrently. Each touches distinct files.
- **After Phase2.2 (2 agents):** Phase2.6a (continuity, needs only 2.2) can start alongside the Phase2.3 → 2.4 → 2.5 chain.
- **After Phase2.7 (2 agents):** R2a and R2b can run concurrently.
- **R4 runs in parallel with ALL of R2** — no dependency in either direction.

**Total new lines:** ~900 across 11 sub-tickets. Largest single block is Phase2.2 (~200) and Phase2.6 (~200 across 3 sub-parts).
