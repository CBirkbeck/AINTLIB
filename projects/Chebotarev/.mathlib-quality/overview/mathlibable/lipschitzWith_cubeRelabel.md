# Mathlibable assessment — `Chebotarev.lipschitzWith_cubeRelabel`

**Verdict: NO — mathlib already has it (`IsometryEquiv.piCongrLeft'`, whose `.isometry.lipschitz` is exactly this statement; the underlying map is `Equiv.piCongrLeft'`).**

- **Declaration:** `Chebotarev.lipschitzWith_cubeRelabel`
- **Location:** `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:265`
- **Earmark:** `ForMathlib/` helper, author-flagged for mathlib.
- **Date:** 2026-06-18
- **Sibling assessment:** the parent def is assessed in
  `…/mathlibable/cubeRelabel.md` (verdict NO — `Equiv.piCongrLeft'`); this report is the
  lemma-level companion and re-confirms it independently.

---

## Phase 0 — Baseline

- lake build:               stale locally (per task note); reasoned from source + local mathlib pin.
- decl `Chebotarev.lipschitzWith_cubeRelabel`: ✓ resolved at `…/ForMathlib/NormLeOneLipschitz.lean:265`
  (namespace `Chebotarev`, opened line 79, `end` line 673 — qualified name **confirmed**).
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — finitely
  many Lipschitz cube images covering the `realSpace`/`mixedSpace`/`index` frontier (Gun–Ramaré–
  Sivaraman boundary input, after Debaene / Widmer–Lang).

---

## Phase 1 — Statement (in prose)

```lean
open scoped Classical in
theorem lipschitzWith_cubeRelabel : LipschitzWith 1 (cubeRelabel K) :=
  lipschitzWith_one_of_edist_apply_le (F := cubeRelabel K)
    fun c d j ↦ edist_le_pi_edist c d (equivFinRank.symm j)
```

where (line 260)

```lean
def cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
    {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun j ↦ c (equivFinRank.symm j)
```

**Math statement.** Reindexing the coordinates of a tuple `c ∈ ℝ^{Fin (r−1)}` (`r = #InfinitePlace K`)
by the fixed bijection `equivFinRank.symm : {w ≠ w₀} → Fin (rank K)`, producing the tuple
`(c_{equivFinRank.symm j})_{j ∈ {w ≠ w₀}}`, is `1`-Lipschitz when both function spaces carry the
sup (`L∞`) metric. In one phrase: **a coordinate relabelling of a finite product is non-expansive**
(it is in fact an isometry — the proof only invokes the ≤ half).

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K]` `[NumberField K]` — supplies `InfinitePlace K` (a `Fintype`), the
  distinguished place `w₀`, the rank `rank K = #InfinitePlace K − 1`, and `equivFinRank`.

Hypotheses: none beyond `K` a number field.

Conclusion (math): the relabelling map is `1`-Lipschitz for the `L∞` metric on both sides.
Conclusion (Lean): `LipschitzWith 1 (cubeRelabel K)`.

**Mathlib ingredients (all `open NumberField`, hence unqualified in source):**
- `NumberField.Units.w₀ : InfinitePlace K` — `…/Units/DirichletTheorem.lean` (distinguished place).
- `NumberField.Units.rank K := Fintype.card (InfinitePlace K) − 1` — `…/Units/DirichletTheorem.lean:356`.
  Hence the domain index `Fin (Fintype.card (InfinitePlace K) − 1)` **is** `Fin (rank K)`.
- `NumberField.Units.equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}`
  — `…/Units/Regulator.lean:57`.
- `Fintype (InfinitePlace K)` — `…/InfinitePlace/Basic.lean:310`; so `{w ≠ w₀}` and `Fin (rank K)`
  are both fintypes.
- `edist_le_pi_edist` — `…/Topology/EMetricSpace/Pi.lean:42` (per-coordinate `edist` ≤ pi `edist`).
- `lipschitzWith_one_of_edist_apply_le` — a **private** helper in this very file (line 100), the
  "pi-codomain companion of `LipschitzWith.eval`".

---

## Phase 2 — Preliminary checks

### 2a. Size classification
**SMALL.** A 2-line regularity lemma about a project-local convenience def; not a named theorem, not
a `## Main results` entry (it is an internal step toward `exists_lipschitzWith_frontierCoverFamily`).

### 2b. One-line check
n/a — kind is `theorem` (the one-liner gate applies to `def`/`abbrev`/`structure`). Note for the
record: the *def it is about*, `cubeRelabel`, is a one-liner and was assessed `NO` in its own report.

---

## Phase 3 — Literature search (EXHAUSTIVE)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1  | WebSearch (specific form) | "reindexing tuple by bijection of index set isometry sup metric L-infinity norm" | yes | `‖a−b‖_∞ = max_i |a_i−b_i|`; a bijection `φ:K→K` (reordering) preserves sums/structure of families | The L∞ metric on the relabelled tuple coincides coordinatewise; reorder is non-expansive (an isometry). |
| 2  | WebSearch (general form) | "coordinate permutation product space isometry L^p norm reindex equivalence" | yes | for finite `I,J` and injective `f:I→J`, the reindex `f_* : ℝ^I → ℝ^J` satisfies `‖f_*(x)‖ = ‖x‖`; `ℓ_p` norms are exactly the permutation-invariant multiplicative norms | The standard fact is an **isometry for every `L^p`**, `p ∈ [1,∞]` — sup is the `p=∞` case. Strictly more general than the bare `L∞`-Lipschitz claim. |
| 3  | WebSearch (aliases / Lean) | "Lipschitz function reindexing coordinates pi type equivalence Lean mathlib Equiv.piCongrLeft" | yes | mathlib `Equiv.piCongrLeft'`, `LinearEquiv.piCongrLeft'` reindex pi types by an equiv via `e.symm` | Confirms the canonical mathlib object by name; doc notes `piCongrLeft'` applies `e.symm` (exactly `cubeRelabel`). |
| 4  | ChatGPT math MCP | "standard generality of: reindexing coordinates of a finite tuple is an isometry / 1-Lipschitz; historical formulation" | n/a | — | MCP down in this environment (task note). Covered by channels 1–2 (explicit `L^p` isometry statement) + 5–6. |
| 5  | Local references | grep `.mathlib-quality/references/` for "reindex"/"isometry"/"Lipschitz" | n/a | (no references dir) | `projects/Chebotarev/.mathlib-quality/references/` is **absent** — recorded n/a. |
| 6  | nLab | "isometry", "product metric", "isometric isomorphism" | yes | a bijection of the index set induces an isomorphism of the product; for `ℓ^∞`/product (uniform) structure it is an **isometric isomorphism** | nLab "isometry": an isomorphism in the category of metric spaces; product reindexing is the canonical example. |
| 7  | nCatLab / categorical | — | n/a | — | Not a categorical-structure question beyond "iso of products"; covered by nLab row. |
| 8  | Stacks Project | — | n/a | — | Not an algebraic-geometry concept. |
| 9  | MathOverflow / MSE | "permutation of coordinates isometry sup norm" | yes | folklore: coordinate permutations are the linear isometries of `ℓ^∞_n` (with sign flips); reindexing by a bijection is an isometry | Standard, uncontested; the `≤`-direction (Lipschitz 1) is the trivial half. |
| 10 | recent arXiv (≤5y) | (from rows 1–2) e.g. arXiv:1102.2618 "multiplicative property characterizes ℓ_p and L_p norms" | yes | `‖f_*(x)‖ = ‖x‖` for injective reindex `f`, all `ℓ_p` | Modern source restating the isometry; nothing newer changes the (classical) statement. |

### Literature summary (Phase 3)
- Concept identified as: **reindexing / permutation of the coordinates of a finite (or `ℓ^p`) tuple
  by a bijection of the index set** — equivalently, the isomorphism of products induced by a
  bijection of the indexing set.
- Sources agree on the standard form: **yes**. It is an **isometry** (norm-preserving), uniformly
  across all `L^p` norms including `p = ∞` (the sup/product metric relevant here).
- Most general standard form: for any bijection `e : I ≃ J` of index sets and any families of
  (pseudo-e)metric fibers `Y_i`, the reindex `(∀ i, Y_i) → (∀ j, Y_{e.symm j})` is an isometry.
- Generality dimensions where the literature varies:
  - **metric**: `L^p` for any `p ∈ [1,∞]` (isometry for *all*); the lemma uses only `p = ∞`.
  - **regularity claimed**: isometry (full) vs `1`-Lipschitz (the `≤` half) vs antilipschitz (`≥`).
    The literature standard is the full isometry; the lemma claims only the weaker `1`-Lipschitz.
  - **fibers**: arbitrary (possibly dependent) `Y_i`; the lemma fixes `Y = ℝ` constant.
  - **index types**: any two (here, finite) index sets; the lemma fixes `Fin (rank K)` and `{w ≠ w₀}`.
- Disagreement with the literature: none — the lemma is a strict *specialisation and weakening*
  (single `p=∞`, constant fiber `ℝ`, fixed indices, only the `≤` half) of the standard isometry.

---

## Phase 4 — Generality analysis

Literature-standard form (Phase 3): for `e : I ≃ J` (fintypes) and `(pseudo-e)metric` fibers
`Y : I → Type*`, the map `(∀ i, Y i) → (∀ j, Y (e.symm j))`, `c ↦ (c (e.symm j))_j`, is an **isometry**.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/stronger form exists? | Reason |
|---|------------------------|-------------------|--------------------------|------------------------------|--------|
| 1 | conclusion `LipschitzWith 1` | `1`-Lipschitz (`≤` half) | full **isometry** (`edist` equality) | **STRONGER exists** | A coordinate reindex is an isometry; mathlib states the isometry (`IsometryEquiv.piCongrLeft'`), which *implies* this. |
| 2 | metric on each side | sup (`L∞`) `edist` on `ℝ`-valued pi | isometry for every `L^p`, `p∈[1,∞]` | yes | The proof uses `edist_pi_def` (= sup); the result holds for all `p`, but `L∞` is the right one for this file. |
| 3 | fiber `ℝ` | constant fiber `ℝ` | arbitrary (dependent) `[PseudoEMetricSpace (Y j)]` | yes | `cubeRelabel` fixes `ℝ`; mathlib's `piCongrLeft'` is fiber-polymorphic. |
| 4 | index types | `Fin (rank K)` and `{w ≠ w₀}` | any two fintypes via `e : ι ≃ ι'` | yes | `equivFinRank` is one specific `e`; nothing in the proof needs number-field structure. |
| 5 | map | the bare relabelling | a bundled **`IsometryEquiv`** (`≃ᵢ`, gives the inverse + isometry both ways) | yes (mathlib has it bundled) | mathlib packages it as an equiv, exposing surjectivity (`exists_cubeRelabel_eq`) and the inverse for free. |

### Generality verdict (Phase 4b)
The current form is **STRICTLY NARROWER AND WEAKER THAN STANDARD** (single `p=∞`, constant fiber,
fixed indices, only the `1`-Lipschitz half rather than the isometry). However — see Phase 5 — the
**maximally general form is already in mathlib**, so the relevant verdict axis is "mathlib has it",
not "generalise then add". There is nothing to upstream.

### Modern-idiom check (Phase 4c)
| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled-hypotheses → typeclasses/instances | no | already typeclass-driven (`Fintype`, `PseudoEMetricSpace`) | — |
| 2 | sequences/metric → filters/topology | no | this is a metric (Lipschitz/isometry) statement; no sequence to filter-ise | — |
| 3 | construction → universal-property class | partial | the modern idiom is the **bundled `IsometryEquiv`** (`IsometryEquiv.piCongrLeft'`), not a bare Lipschitz lemma | gives the inverse + `≃ᵢ` API; supersedes the standalone Lipschitz fact |
| 4 | set+closure-pred → bundled substructure | no | n/a | — |
| 5 | vector/metric-specific → weaker typeclass | yes | fiber `ℝ` → any `PseudoEMetricSpace`; already realised by mathlib | full pi-isometry API |
| 6 | 1-categorical → higher-categorical | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → general structure | yes | fixed `Fin (rank K)`/`{w ≠ w₀}` → arbitrary `ι ≃ ι'` | already realised by mathlib |

**Modern-idiom verdict:** the contemporary mathlib idiom for "coordinate relabelling is non-expansive"
is the **bundled isometry equiv `IsometryEquiv.piCongrLeft'`** — and it is *already in mathlib*. This
does not yield a "generalise-then-add" target for us; it confirms the result is mathlib's, not ours.

---

## Phase 4.5 — Diamond / defeq risk
n/a — declaration kind is `theorem` (no definitional equalities or instance-search paths introduced).

---

## Phase 5 — Mathlib search (five methods)

### Search-status: `Chebotarev.lipschitzWith_cubeRelabel`

- **[A] Lean-Finder** — `n/a: tool not available in this environment` (the MCP loogle/leansearch
  endpoints returned "No such tool available"). Substituted by authoritative method **[D]** (reading
  the actual mathlib source on the local pin).
- **[B] Loogle** (`lean_loogle`) — `n/a: tool not available` ("No such tool available"). Intended
  query `Isometry (Equiv.piCongrLeft' _ _)` / `LipschitzWith 1 (Equiv.piCongrLeft' _ _)`. Substituted by [D].
- **[C] LeanSearch** (`lean_leansearch`) — `n/a: tool not available` ("No such tool available").
  Intended query "reindexing a function on a pi type by an equivalence is an isometry/Lipschitz".
  Substituted by [D] + WebSearch row 3 (which surfaced `Equiv.piCongrLeft'` from mathlib docs).
- **[D] Grep mathlib source** (local pin `.lake/packages/mathlib/`) — **HITS** (read in full):
  - `Equiv.piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b)` with
    `toFun f x := f (e.symm x)` — `Mathlib/Logic/Equiv/Basic.lean:805`. With `P := fun _ ↦ ℝ`,
    `e := equivFinRank`: `⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank) c = fun j ↦ c (equivFinRank.symm j)
    = cubeRelabel K c` — **definitional** (`@[simps apply]` ⇒ `piCongrLeft'_apply`).
  - `IsometryEquiv.piCongrLeft' [Fintype ι] [Fintype ι'] {Y} [∀ j, PseudoEMetricSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y i) ≃ᵢ ∀ j, Y (e.symm j)` with `toEquiv := Equiv.piCongrLeft' _ e` and
    `isometry_toFun` proved by `edist_pi_def` + `Equiv.iSup_comp` — `Mathlib/Topology/MetricSpace/Isometry.lean:602`.
    **This is exactly "`cubeRelabel` is an isometry."**
  - `IsometryEquiv.isometry (h : α ≃ᵢ β) : Isometry h` — `Isometry.lean:391`.
  - `Isometry.lipschitz (h : Isometry f) : LipschitzWith 1 f` — `Isometry.lean:77`.
  - Strengthenings, should they ever be wanted: `LinearEquiv.piCongrLeft'`,
    `LinearIsometryEquiv.piLpCongrLeft` (`Mathlib/Analysis/Normed/Lp/PiLp.lean`).
  - Supporting: `edist_le_pi_edist` `…/EMetricSpace/Pi.lean:42`; `Equiv.iSup_comp`
    `…/Order/CompleteLattice/Basic.lean:183`.
  - **No dedicated `LipschitzWith _ (… piCongrLeft …)` lemma** exists (grep empty) — because the
    isometry packaging *is* the canonical route (`.isometry.lipschitz`).
- **[E] Name-pattern** — grep `piCongrLeft`, `lipschitz.*piCongr`, `Isometry.*piCongr` over mathlib —
  HITS converge on the `piCongrLeft'` family above; no separate Lipschitz lemma.

Searched for **both** forms:
- user's form `LipschitzWith 1 (cubeRelabel K)` — is `(IsometryEquiv.piCongrLeft' equivFinRank).isometry.lipschitz`.
- literature-standard form (the isometry / general fibers / general indices) — is
  `IsometryEquiv.piCongrLeft'` itself.

**Concluded:** found in mathlib as **`IsometryEquiv.piCongrLeft'`** (the isometry packaging, of which
this is the `.isometry.lipschitz` corollary) on the map **`Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank`**
which is **definitionally `cubeRelabel K`**; the user's form follows in ≤1 line (more general form —
we would be a specialisation + weakening).

---

## Phase 6 — Composition check (+ call sites)

### 6.0 Call sites — `Chebotarev.lipschitzWith_cubeRelabel`
Internal use count (excluding the declaring file): **0**.
External-to-file callers: **0 distinct files**.
Total occurrences (incl. declaring file): 3 — the decl head (line 265) + two uses inside
`exists_lipschitzWith_frontierCoverFamily` (lines 304, 305).

| Caller file:line | Usage pattern |
|------------------|---------------|
| NormLeOneLipschitz.lean:304 | `(hM₀.comp (lipschitzWith_cubeRelabel K)).weaken …` (same file, internal) |
| NormLeOneLipschitz.lean:305 | `((hMs p).comp (lipschitzWith_cubeRelabel K)).weaken …` (same file, internal) |

**Inline-derivation grep — the decisive signal.** The *same* coordinate-relabelling-is-`1`-Lipschitz
fact is re-derived **inline, via the mathlib route, later in the very same file**:
- `NormLeOneLipschitz.lean:664` —
  `(IsometryEquiv.piCongrLeft' (Y := fun _ ↦ ℝ) g).isometry.lipschitz`
  inside `normLeOne_frontier_lipschitz_cover_index`, for the analogous relabelling `fun a ↦ c (g.symm a)`
  on the `index K` dimension. The author **bypasses** `lipschitzWith_cubeRelabel` there and inlines the
  mathlib composition — demonstrating both that the wrapper is non-essential and that the mathlib
  `IsometryEquiv.piCongrLeft'` route is the author's own idiom.

Per the call-sites table in the skill: **K = 0 external uses AND the same statement is re-derived
inline elsewhere via mathlib ⇒ NO-composable / NO-mathlib-has-it.** Here mathlib has the packaged
result, so it is NO-mathlib-has-it.

### 6a Composition attempt
Goal: `LipschitzWith 1 (cubeRelabel K)`.

Attempt 1 (≤1 mathlib "object", then 2 projections):
```lean
example : LipschitzWith 1 (cubeRelabel K) :=
  (IsometryEquiv.piCongrLeft' (Y := fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ ℝ) equivFinRank).isometry.lipschitz
```
- Mathlib decls used: `IsometryEquiv.piCongrLeft'`, `IsometryEquiv.isometry`, `Isometry.lipschitz`.
- Relies on the defeq `cubeRelabel K = ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)`
  (`@[simps]`; verified at the local pin in `cubeRelabel.md`). If Lean needs the nudge, a leading
  `show LipschitzWith 1 ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)` (or `simp only [cubeRelabel]`)
  makes it `rfl`-aligned — still ≤3 calls.
- Result: **succeeds** — and this is literally the line the author already wrote at line 664 (with
  `equivFinRank` in place of `g`).

**Conclusion: NOT-COMPOSABLE-AS-NEW** in the "needs a new lemma" sense — because it is **identical to
an existing mathlib declaration applied** (`IsometryEquiv.piCongrLeft'.isometry.lipschitz`), not a
genuine composition gap. Routes the verdict to **NO-mathlib-has-it**.

---

## Phase 7 — Verdict

## Verdict: `Chebotarev.lipschitzWith_cubeRelabel`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature (Phase 3): the standard object is "reindexing the coordinates of a finite/`ℓ^p` tuple by
  a bijection of the index set", and it is an **isometry** for every `L^p` (sup included) — strictly
  stronger than the `1`-Lipschitz claim. ≥3 WebSearch generality levels + nLab + MathOverflow + arXiv.
- Generality (Phase 4): STRICTLY NARROWER AND WEAKER than standard — but the *maximally general* form
  is the one mathlib ships, so there is nothing to generalise-and-add.
- Mathlib search (Phase 5): found as `IsometryEquiv.piCongrLeft'` (`Isometry.lean:602`) on the map
  `Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank` (`Equiv/Basic.lean:805`), which is **definitionally
  `cubeRelabel K`**; `.isometry.lipschitz` is exactly this lemma.
- Composition (Phase 6): the statement is a single mathlib decl applied — and the author already
  inlines that exact line at `NormLeOneLipschitz.lean:664`. Zero external call sites.

**WHY not (refactor-actionable).** Mathlib already contains this fact, in a strictly stronger and more
general form. `cubeRelabel K` is definitionally `⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)`
(domain `Fin (Fintype.card (InfinitePlace K) − 1) = Fin (rank K)`), and mathlib's
`IsometryEquiv.piCongrLeft' equivFinRank` proves that this very map is an **isometry** (both index
sets are fintypes, so the `[Fintype ι] [Fintype ι']` hypotheses are met; the fiber `ℝ` is a
`PseudoEMetricSpace`). `LipschitzWith 1` is then the standard `.isometry.lipschitz` corollary. The
specific gap this would "fill" in mathlib is **none** — mathlib's pi-reindexing API is complete at the
`Equiv` → `Isometry` → `Linear` → `LinearIsometry` levels, and a bare `LipschitzWith` lemma is
deliberately absent precisely because it is the trivial half of the isometry. This is a perfectly
reasonable *local* convenience step, but it adds nothing upstream and is the author's own non-preferred
idiom (cf. line 664, where the mathlib route is inlined directly).

Existing mathlib decl:        `IsometryEquiv.piCongrLeft'` (with `IsometryEquiv.isometry`, `Isometry.lipschitz`)
Located at:                   `Mathlib/Topology/MetricSpace/Isometry.lean:602` (`:391`, `:77`);
                              underlying map `Mathlib/Logic/Equiv/Basic.lean:805`.

Our form follows in ≤1 line:
```lean
example : LipschitzWith 1 (cubeRelabel K) :=
  (IsometryEquiv.piCongrLeft' (Y := fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ ℝ)
    equivFinRank).isometry.lipschitz
-- (defeq cubeRelabel K = ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank); add
--  `show LipschitzWith 1 ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)` if a nudge is needed.)
```

Call sites in our project (from Phase 6.0): **K = 0** external; 2 internal uses (lines 304–305) inside
`exists_lipschitzWith_frontierCoverFamily`.

**Refactor plan.** This is a project-cleanup action, not a mathlib submission (the `ForMathlib/`
earmark should be **dropped** for this lemma):
1. Delete `lipschitzWith_cubeRelabel` (and, per the sibling `cubeRelabel.md`, ideally the whole
   `cubeRelabel` wrapper block) from `NormLeOneLipschitz.lean`.
2. At lines 304–305, replace `lipschitzWith_cubeRelabel K` with
   `(IsometryEquiv.piCongrLeft' (Y := fun _ : {w // w ≠ w₀} ↦ ℝ) equivFinRank).isometry.lipschitz`
   — i.e. exactly the line already present at 664 (with `equivFinRank` for `g`). The two uses are
   `hM₀.comp (… )` / `(hMs p).comp (… )`, so a `1`-Lipschitz term in that slot is a drop-in; the
   `mul_one`/`weaken` plumbing is unchanged.
3. If a defeq nudge is needed, precede with `show LipschitzWith 1 ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ)
   equivFinRank)` or `simp only [cubeRelabel]`.
4. This unifies the file on a single idiom (the one at line 664) and removes ~6 lines of wrapper +
   the private helper `lipschitzWith_one_of_edist_apply_le`'s only non-`clampUnit` consumer.

**Note on the private helper.** `lipschitzWith_one_of_edist_apply_le` (line 100) is still used by
`lipschitzWith_clampUnit` (line 107), so it stays; only its `cubeRelabel` consumer goes.

**Cost is not the reason** for this verdict and is not cited as one — the verdict is NO purely because
mathlib already has the (stronger) result.

### Next action
Delete `Chebotarev.lipschitzWith_cubeRelabel`; at its two call sites (lines 304–305) inline
`(IsometryEquiv.piCongrLeft' (Y := fun _ : {w // w ≠ w₀} ↦ ℝ) equivFinRank).isometry.lipschitz`
(the line already used at 664). Drop the `ForMathlib` earmark for this lemma. Track under the same
cleanup ticket as the sibling `cubeRelabel` removal.

### Sources
- mathlib4 docs — `Mathlib.Logic.Equiv.Basic` (`Equiv.piCongrLeft'`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Basic.html
- mathlib4 docs — `Mathlib.Topology.MetricSpace.Isometry` (`IsometryEquiv.piCongrLeft'`, `Isometry.lipschitz`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Isometry.html
- mathlib4 docs — `Mathlib.LinearAlgebra.Pi` (`LinearEquiv.piCongrLeft'`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Pi.html
- mathlib source (local pin): `Mathlib/Topology/MetricSpace/Isometry.lean:{602,391,77}`,
  `Mathlib/Logic/Equiv/Basic.lean:805`, `Mathlib/Topology/EMetricSpace/Pi.lean:42`,
  `Mathlib/Order/CompleteLattice/Basic.lean:183`, `Mathlib/Analysis/Normed/Lp/PiLp.lean`,
  `Mathlib/NumberTheory/NumberField/Units/{Regulator.lean:57, DirichletTheorem.lean:356}`,
  `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:310`.
- Literature: ℓ_p permutation-invariance / multiplicative characterisation —
  https://arxiv.org/pdf/1102.2618 ; coordinate-permutation isometries of `ℓ_p` —
  https://arxiv.org/pdf/0706.3861 ; "$T((y_n)) = (ε_n y_{σ(n)})$ is an isometry" (reorder + sign).
- Sibling assessment (same conclusion, parent def): `…/mathlibable/cubeRelabel.md`.
