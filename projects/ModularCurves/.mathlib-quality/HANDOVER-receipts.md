# HANDOVER — the KM 4.7.0 representability "receipts"

*Written 2026-07-20 for the incoming worker. Branch `dev/modular-curves`, HEAD `50d5f9d37` (synced with origin). Everything below is verified against the tree at this commit, not memory.*

---

## 0. TL;DR — read this first

**Goal of the workstream:** make the 7 "receipt" theorems (the fine-modular-curve
representability results, KM/Loeffler §3.8 + KM 4.7.0) axiom-clean —
`#print axioms` = `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.

**Where it actually stands:** **1 of the receipts is clean; the other ~5 are blocked
by exactly TWO structural walls**, with a handful of *assembly-class* leaves sitting
between the receipts and those walls.

- **Wall B2 — `legendreDeltaGAction` is IMPOSSIBLE as currently stated.** This is not a
  "hard proof", it is a **false statement**. The shared engine's D(2)/Legendre mouth asks
  for a *global* group action that provably cannot exist. **This needs an OWNER
  ARCHITECTURAL DECISION, not more proving.** Until it's decided, the 4 non-Drinfeld
  receipts cannot close no matter how much other work lands. Three concrete resolutions
  are in §3.1 — **pick one before dispatching a worker at these receipts.**
- **Wall B3 — Oort–Tate / finite-flat group schemes are absent from mathlib.** The 2
  Drinfeld receipts need Drinfeld-level *regularity*, which bottoms out at
  `smul_eq_zero_of_factors` = the Oort–Tate classification. mathlib has **no** group-scheme
  theory (confirmed by search — only étale/separable infra exists). This is a **multi-week,
  publishable-scale contribution**, genuinely out of reach as a side-quest.

**The one decision that gates everything:** the B2 owner decision (§3.1). A worker *can*
make real progress on the assembly-class leaves (§4.A/§4.B) in parallel and they are worth
banking — but **they flip no receipt on their own**, so don't mistake them for the finish.

---

## 1. The 7 receipts and their status

| # | Receipt | Location | In-file `sorry`? | Last wall |
|---|---------|----------|------------------|-----------|
| 1 | `gammaFullNaive_representable` | `Moduli/Representability.lean:641` (sorry `:646`) | yes | **B2** |
| 2 | `gammaFullDrinfeld_representable` | `Moduli/GammaH.lean:1074` (sorry `:1077`) | yes | **B2 + B3** |
| 3 | `gammaOneDrinfeld_representable` | `Moduli/GammaH.lean:1087` (sorry `:1090`) | yes | **B2 + B3** |
| 4 | `gammaBot_representable` | `Moduli/GammaHMaster.lean:1338` | no — routes through engine | **B2** |
| 5 | `gammaH_representable_of_orderOf` | `Moduli/GammaHMaster.lean:1115` | no — routes through engine | **B2** |
| 6 | `gammaOneDrinfeld` (master) | `Moduli/GammaHMaster.lean:1306` | no — routes through engine | **B2 + B3** |
| 7 | `levelSpaceΓπ_etale` | `Moduli/GammaHRepresentability.lean:3498` | no | **✅ CLEAN** |

Notes:
- "routes through engine" = the theorem body is `representable_of_affineOverEll_of_rigidNoeth …`
  (sorry-free wiring) — so it has **no direct sorry**, but it carries `sorryAx` transitively
  through the engine's open leaves (§2). Receipts 1/2/3 additionally still carry a *direct*
  sorry that a worker would replace with the same engine call once the leaves land.
- Receipt 7 (`levelSpaceΓπ_etale`) is the étale-ness statement; it does not need
  representability and was confirmed axiom-clean this session. **Re-verify with
  `lean_verify ModularCurves.levelSpaceΓπ_etale` before trusting it after any bump.**

---

## 2. The engine — how the 6 open receipts route

All 6 non-étale receipts funnel through **one** theorem:

- `ModuliProblem.representable_of_affineOverEll_of_rigidNoeth` — `Moduli/EngineWiring.lean:106`
  (this file is **sorry-free**). It is the **recollement** over `D(2) ∪ D(3) = Spec R` of two
  "mouth" instantiations:
  - **D(3) mouth** — naive level-3 / `GL₂(𝔽₃)` over `R[1/3]`. The φ-action here
    (`gammaFullNaiveGlAction`, level-3) **genuinely exists** (pure re-marking). ✅
  - **D(2) mouth** — Legendre / `GL₂(𝔽₂) × ℤˣ` over `R[1/2]`. Its φ-action is
    `legendreDeltaGAction` — **this is wall B2** (§3.1). ❌

The bare unconditional statement `representable_iff_rigidNoeth` (`Moduli/EllCategory.lean:310`,
sorries `:298`/`:324`) is **deliberately bypassed** — every receipt cone was re-pointed onto the
engine, so that bare sorry is no longer in any cone. Do **not** try to close `:324` directly;
it is the thing the engine replaces.

The engine itself, once B2 is resolved, still bottoms out at three **assembly-class** leaves
(§4.A) shared by all 6 receipts: the mouth core, the Zariski descent glue, and the √-cover
sections.

---

## 3. The two walls (the real content of this handover)

### 3.1 Wall B2 — `legendreDeltaGAction` is impossible as stated → OWNER DECISION

- **Location:** `Moduli/LegendreTorsor.lean:273` (`noncomputable def legendreDeltaGAction`, sorry `:275`).
- **Statement:** `legendreDeltaGAction R : GL₂(𝔽₂) × ℤˣ →* Aut (legendreDeltaProblem R)` — a
  **global functor automorphism** (natural iso `δ ≅ δ` on the whole category).
- **Why it cannot exist (proven this session, logged in `.mathlib-quality/b2_log.jsonl`):**
  `legendreDeltaProblem` has `δ(X) = {(full-level-2 marking, ω-basis) // IsLegendreDatum}`, and
  `IsLegendreDatum` **pins** `x(Q) − x(P) = 1`. A `GL₂(𝔽₂)` re-marking permutes the 2-torsion,
  which forces `ω` to rescale by `√(x(Q′) − x(P′))`. That square root is **not globally available**
  on a general `X` (take any `X` where the abscissa difference is a non-square unit) — so the
  action is **undefined** on `δ(X)` there. A functor automorphism needs the action on **every**
  `δ(X)`, so no such global `φ` exists.
- **What DOES exist:** the *scheme-level* action `σZ` (`G` acting on the √-cover representing
  scheme) is fine. The obstruction is purely the **global φ-side**. Pinpoint of the coupling:
  `TorsorData.equivariant` (`Moduli/QuotientProblem.lean:766`) equates `σZ` with `(φ γ⁻¹).hom.app`
  at every value — forcing φ to act globally.
- **Ruled out already** (don't re-try): the ambient fix `δ' = (level-2 × ω)` is **not** a
  `G`-torsor (its ω-part is `𝔾ₘ`, not `{±1}` — the `IsLegendreDatum` cut is exactly what makes it
  a finite torsor *and* what forces the √). So you can't dodge B2 by dropping the datum condition.

**The three owner resolutions (choose ONE):**

1. **φ-free `TorsorData`** (mouth-interface change). Reformulate `TorsorData` so its equivariance
   is stated *intrinsically* via the existent `σZ`, never via a global φ. Cost: touches
   `representable_of_rigidNoeth_of_torsor` + the D(3) wiring (which currently *supplies* a φ). This
   is the minimal-blast-radius fix if it goes through, but it's an interface redesign.
2. **Switch the D(2) rigidifier to LEVEL 4** *(my recommendation for a fresh worker).* `N = 4 ≥ 3`,
   `4 = 2²` is invertible over `R[1/2]`, and `gammaFullNaiveGlAction R 4` is a **genuine global**
   `GL₂(ℤ/4)` re-marking action — **no B2**, and it's rigid
   (`glSmul_eq_one_of_eq_self`, `gammaFullNaiveProblem_map_negIso_ne_of_three_le`, both general-`N`).
   This deletes the **entire** Legendre/√-cover subtree (§4.B) from every receipt cone.
   **Cost:** level-4 needs a full `ℰ₄`-machine for its *direct absolute* representability (the
   analogue of the existing 3-specific `ℰ₃`-machine: `universalE3_generation` + `isE3Datum_of_bridges`).
   General-`N` representability is proven only *via the engine*, which is circular for something
   used *as* a rigidifier — so you must build `ℰ₄` directly. The level-3 torsor generalises cheaply
   (`isIso_torsorSigmaDesc_of_existsUnique` + `glSmul` are general-`N`; `ℤ/4`-ring vs `𝔽₃`-field is a
   free-module-basis argument).
3. **Fix Legendre** — build the √-cover representability (`scaleTorsor_spec` / `[T-E14-ACT']`, §4.B)
   *and* accept that `legendreDeltaGAction` must be reformulated φ-free anyway (the √-cover action
   can't be global). Effectively (1) + all of §4.B. Most work, keeps the mathematics closest to the
   source.

All three are **owner-scope** — they change either the interface or the rigidifier. **This is the
call to make before putting a worker on receipts 1/2/4/5.** My steer: **option 2 (level-4)** — it
excises the impossible object entirely and turns the remaining work into a self-contained
`ℰ₄`-machine build rather than an interface redesign that ripples through the engine.

### 3.2 Wall B3 — Oort–Tate / finite-flat group schemes (mathlib gap)

- **Blocks:** receipts 2/3/6 (the Drinfeld ones) — they need Drinfeld-level *regularity*.
- **Bottoms out at:** `smul_eq_zero_of_factors` (the "kill by the order" law for a
  finite-locally-free subgroup). Present as *statements* in several places, all `sorry`/gated:
  - `GroupScheme/DeligneOrder.lean:2121` `smul_eq_zero_of_factors'`
  - `GroupScheme/Subgroup.lean:317` `HasRank.smul_eq_zero_of_factors`
  - `LevelStructure/ExactOrder.lean:113` `…IsSubgroup.smul_eq_zero_of_factors`
  - `LevelStructure/ExactOrder.lean:832` `Section.HasExactOrder.pull_nsmul_jetData` (B3-gated)
- **Why it's a wall:** proving these correctly requires the **Oort–Tate classification** of
  finite flat group schemes of order `p`, and more generally Deligne's order-kills-the-group
  theorem — i.e. a **from-scratch finite-flat-group-scheme library** (Hopf algebras / Cartier
  duality / Oort–Tate). mathlib has none of this. **This is a genuine research contribution,
  weeks of work, and should be scoped as its own project**, not attempted as a receipt leaf.
- The Drinfeld regularity leaves that consume it: `gammaHNaive_relativelyRepresentable`
  (`GammaH.lean:475`, sorry `:483`), `gammaHNaive_rigid_iff` (`:489`, sorry `:496`),
  `gammaHNaive_representable_of_rigid` (`:503`, sorry `:508`).

---

## 4. Open-leaf inventory (grouped by tractability)

### 4.A — ASSEMBLY-CLASS (no research gap; a worker can close these now). Shared by all 6 receipts.

1. **Mouth core** — `exists_localModel_core_at` — `Moduli/EngineDescent.lean:2525` (sorry `:2593`).
   KM 2.2.5–6 semilocal local-model gluing. **De-risked to volume-only** (~1000-line native
   assembly over `A_a`; the EGA IV §8 "spreading" was *avoided* via glue-over-`A_a`). No deep gap.
   Prerequisites already **banked** (§5): `ForMathlib/AffineCechH1.lean`,
   `ForMathlib/PicSubsingletonFree.lean`, `ForMathlib/SemilocalOmegaBasis.lean`; Stage-1/2
   semilocalization preamble is in.
2. **Zariski descent glue** — `glueEllObj_representableBy` — `Moduli/Recollement.lean:1484`
   (sorry `:1491`), plus its helper `HomGlueDescent` producer at `:1392`. The **parametrized
   skeleton** `glueEllObj_representableBy_of_zariskiGlue` and the sheaf input
   `moduliProblem_zariski_glue` ([R-sheaf-P], in `Moduli/Stack.lean`) already **landed**. Remaining:
   `[R-chart-eqv]` + `[R-hom-glue]` + final assembly. **A full consumption spec exists** — read
   `scratchpad/glueEllObj_consumption_spec.md` (it lists every proven primitive and the exact
   assembly). This is the single most "ready to be finished" leaf.

### 4.B — `[T-E14-ACT']` — the √-extraction dictionary (a focused multi-lemma build, NOT research).

Only relevant if the owner picks B2-resolution **1 or 3** (option 2/level-4 deletes this subtree).

- `scaleTorsor_spec` — `Moduli/SqrtCoverGlue.lean:772` (sorry `:804`), and its helper
  `specMap_resLE_fromSpec` (`:644`, sorry `:705`). The √-cover double-cover sections. Builder-D
  confirmed this is **blocked by `[T-E14-ACT']`** — it is *not* pure assembly.
- The Legendre subtree, downstream of `scaleTorsor_spec` (`Moduli/LegendreTorsor.lean`):
  - `legendreDelta_exists_naturalFamily` (`:214`, sorry `:222`) — `[T-E14-NAT]`, thread naturality.
  - `legendreDelta_surjective_of` (`:296`, sorry `:300`).
  - `legendreDelta_torsor_of` (`:308`, sorry `:316`) — fibrewise simple transitivity (`|G| = 12`).
- **What `[T-E14-ACT']` actually needs** (genuinely unbuilt): the `abscissaDiff` ↔ `basisUnitAt`
  dictionary — Piece 1 (LHS-section μ₂-torsor), Piece 2 (`IsLegendreDatum` ↔ abscissa bridge),
  Piece 3 (abscissaDiff pullback-compat), B1 (local-sign stability). Three μ₂-torsor helpers were
  already banked (§5); these four bridges are the open part.

### 4.C — Wall B2 (§3.1) — owner decision.  ### 4.D — Wall B3 (§3.2) — research scope.

---

## 5. Already banked this session — do NOT redo

All axiom-clean, committed on `dev/modular-curves`:
- `moduliProblem_zariski_glue` ([R-sheaf-P]) — `Moduli/Stack.lean`.
- `glueEllObj_representableBy_of_zariskiGlue` + `ZariskiSheaf` + naturality — `Moduli/Recollement.lean`.
- `exists_cocycle_hρact_of_presentation` (mouth Stage-4) + Stage-1/2 preamble — `Moduli/EngineDescent.lean`.
- Torsor helpers `Equiv.ofBasepointTorsor`, `nonempty_equiv_of_pseudotorsor`,
  `isLegendreDatum_exists_connecting_sqrtOne` (RHS μ₂-pinning) — `Moduli/SqrtCoverGlue.lean`.
- `IsLegendreDatum.smul_of_sq_eq_one` (μ₂-on-ω, B1) — `Moduli/LegendreDatumSymmetry.lean`.
- `ForMathlib/PicSubsingletonFree.lean`, `ForMathlib/SemilocalOmegaBasis.lean`,
  `ForMathlib/AffineCechH1.lean` (mouth-core prerequisites).

**Lesson banked (churn rule):** before firing parallel no-commit builders, verify the import DAG
**both** directions — a builder editing a *low-level* file (e.g. `ExactOrder.lean`) transiently
breaks the verification of every dependent. Only run concurrent builders on mutually
import-isolated files or brand-new files.

---

## 6. Recommended plan for the incoming worker

1. **Owner: settle B2 (§3.1) first.** Nothing on receipts 1/2/4/5 can finish until this is chosen.
   My recommendation: **option 2 (level-4 rigidifier)** — it deletes the impossible object and the
   whole §4.B subtree, converting the work into a self-contained `ℰ₄`-machine build.
2. **In parallel (safe regardless of the B2 choice): finish §4.A.** Close
   `glueEllObj_representableBy` from the consumption spec, then `exists_localModel_core_at` from the
   banked prerequisites. These are shared by all 6 receipts and are the highest-probability wins.
3. **After B2 lands + §4.A lands:** receipts 1/4/5 (and 2/3/6 modulo B3) should fall out of the
   engine. Re-verify each with `lean_verify` and confirm `#print axioms` is the clean triple.
4. **Scope B3 (Oort–Tate) as its own project**, not a receipt leaf. Receipts 2/3/6 stay blocked on
   it and that is expected — say so honestly rather than forcing it.
5. **Discipline:** atomic pathspec commits; `git fetch` + `rev-list --left-right` before every push;
   never `2>/dev/null` next to a `lake`/`lean` call (use `2>&1`); no statement edits to force a pass;
   no new `sorry` outside a claimed leaf. `.mathlib-quality/` is dev-branch process (not merged to main).

---

## 7. Artifacts to read (in order)

1. `.mathlib-quality/b2_log.jsonl` — the two B2 entries (`legendreDeltaGAction` + the `[B2-TD-CONV]`
   convention amendment). The definitive record of *why* B2 is impossible.
2. `scratchpad/glueEllObj_consumption_spec.md` — the ready-to-execute spec for the §4.A descent leaf.
3. `.mathlib-quality/tickets.md` — board entries v10.320–v10.341 (the full narrative).
4. Memory: `aintlib-fin-engine-wired-legendre-b2.md` (the engine-wired + B2 finding),
   `aintlib-fin-b2tdconv-wave.md` (the convention amendment history).

*— end of handover. Sync state at write: HEAD `50d5f9d37`, `0 0` vs `origin/dev/modular-curves`.*
