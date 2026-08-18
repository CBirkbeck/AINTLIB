# /mathlibable report — `Chebotarev.cubeRelabel_mem_Icc`

## Baseline (Phase 0)
- lake build:               not re-run (env: local build stale per task brief); decl read directly from source
- decl `Chebotarev.cubeRelabel_mem_Icc`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:269`
- qualified name:           `Chebotarev.cubeRelabel_mem_Icc` (VERIFIED — `namespace Chebotarev` opens at line 79, closes at line 673; decl at line 269; no nested namespace)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Lipschitz parametrization of the frontier of `normLeOne K` — a `ForMathlib/`
  helper file building the finite Lipschitz-image cover of the norm-≤-1 frontier for the effective
  lattice-point count (Gun–Ramaré–Sivaraman §3.3, after Debaene; Widmer/Lang boundary cells).

Exact source:

```lean
/-- Relabel cube coordinates `Fin (#InfinitePlace K - 1) → ℝ` by the non-distinguished places
`{w ≠ w₀}` via `equivFinRank`. -/
def cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
    {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun j ↦ c (equivFinRank.symm j)

theorem cubeRelabel_mem_Icc {c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ}
    (hc : c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1) :
    cubeRelabel K c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
  ⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩
```

---

## Statement (Phase 1)

`Chebotarev.cubeRelabel_mem_Icc` is a theorem stating the following:

`cubeRelabel K` is the **reindexing** map `(Fin (r−1) → ℝ) → ({w ≠ w₀} → ℝ)`, `r = #InfinitePlace K`,
defined by `cubeRelabel K c j = c (equivFinRank.symm j)` — i.e. precomposition by the bijection
`equivFinRank.symm : {w ≠ w₀} ≃ Fin (rank K)` (note `rank K = Fintype.card (InfinitePlace K) − 1`, so the
two `Fin` cardinalities coincide). The lemma says: if a tuple `c` lies in the unit cube
`Icc (0 : Fin (r−1) → ℝ) 1`, then its reindexing `cubeRelabel K c` lies in the unit cube
`Icc (0 : {w ≠ w₀} → ℝ) 1`. In ordinary mathematics: **permuting/relabelling the coordinates of a point
of `[0,1]^{r−1}` lands you back in `[0,1]^{r−1}`** (over a different but equinumerous index set).
Membership in these **pi-type** order intervals is coordinatewise: `f ∈ Icc 0 1 ↔ ∀ i, 0 ≤ f i ∧ f i ≤ 1`.

Variables / typeclasses involved (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — the number field; only enters through `equivFinRank`
  and the index types `InfinitePlace K`, `{w ≠ w₀}`. Plays **no mathematical role** in the membership
  fact itself, which is pure reindexing.
- `c : Fin (Fintype.card (InfinitePlace K) − 1) → ℝ` — the tuple being relabelled.

Hypotheses (Lean side):
- `hc : c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) − 1) → ℝ) 1` — `c` lies in the source unit cube.

Conclusion (math): `(c ∘ equivFinRank.symm) ∈ [0,1]^{w ≠ w₀}` — reindexing keeps you in the cube.
Conclusion (Lean): `cubeRelabel K c ∈ Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1`.

Proof body: `⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩` — `hc.1 : 0 ≤ c` and `hc.2 : c ≤ 1` are pointwise
`∀ i, 0 ≤ c i` / `∀ i, c i ≤ 1` (the pi order, `Pi.le_def`); applying each at the reindexed point
`equivFinRank.symm j` gives the two halves of `cubeRelabel K c ∈ Icc 0 1`. **No values are produced —
the bounds are inherited verbatim from `hc`.**

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper membership lemma about a project-local one-line `def` (`cubeRelabel`); not a named
theorem, not a `## Main results` entry (the file's main results are the three
`normLeOne_frontier_lipschitz_cover*` theorems), introduces no new structure. It is pure plumbing for
the `clampUnit_eq_self` rewrites at the two call sites.

(Note: literature width is EXHAUSTIVE regardless of SMALL.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def` — the one-liner def-check is n/a. (The *parent* `cubeRelabel` is a one-line
`def`; its mathlibability is its own question — assessed separately in `cubeRelabel.md`, verdict
**NO — mathlib has it** as `Equiv.piCongrLeft'` / `IsometryEquiv.piCongrLeft'`.) The lemma's proof is a
single bundled-pair of pointwise projections — a strong "trivial composition" signal carried into Phase 6/7.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "reindexing tuple preserves coordinatewise bounds product order interval membership"       | weak | permutation/reindex of a tuple preserves coordinatewise bounds (it is a coordinate bijection) | only tangential hits (pandas reindexing, interval-arithmetic monotony); the fact is treated as self-evident, never named |
| 2  | WebSearch (general form)         | "precomposition by bijection preserves membership product order interval pi type"          | weak | order-preserving bijections / order isos: `x ≤ y ↔ f x ≤ f y`; reindex by a bijection is an order iso of the product order | order-iso refs (UMD/Cornell/MIT notes, Wikipedia "order type"); "reindex stays in the box" is structural, not a theorem with a name |
| 3  | WebSearch (named-after / mathlib)| "mathlib4 OrderIso preimage_Icc Equiv piCongrLeft order isomorphism pi type"               | yes  | `OrderIso.preimage_Icc : e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b)`; `Equiv.piCongrLeft'` exists as `LinearEquiv.piCongrLeft'` (reindex a pi type) | leanprover-community mathlib4 docs: the relevant mathlib machinery is order-iso preimage of `Icc` + `piCongrLeft'`; matches the sibling `cubeRelabel` finding |
| 4  | ChatGPT MCP                      | "is `c ∘ e ∈ Icc 0 1` on a pi type a named result or a trivial unfolding; shortest mathlib derivation; piCongrLeft' order-iso vs inline" | ERRORED | n/a | MCP unavailable in this environment (Codex stdin failure; task brief flagged it as possibly down). One attempt, errored. Compensated by 3 WebSearch generality levels + direct mathlib-source reading. |
| 5  | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/` for "reindex"/"Icc"/"piCongr"      | n/a  | (no references dir) | `projects/Chebotarev/.mathlib-quality/references/` is absent — recorded n/a |
| 6  | nLab                             | "order isomorphism / product order reindexing"                                             | n/a  | n/a | Below nLab's granularity — reindexing keeping you in a product interval is the codomain of a bijection-of-coordinates, not an entry nLab carries. Recorded n/a with reason. |
| 7  | nCatLab                          | —                                                                                          | n/a  | n/a | Not a categorical concept. |
| 8  | Stacks Project                   | —                                                                                          | n/a  | n/a | Not an algebraic-geometry concept. |
| 9  | MathOverflow / Math.SE           | covered implicitly by WebSearch #2 (order-preserving-bijection hits)                       | weak | reindex/permute coordinates = order iso of `∏ [a_i,b_i]`; stays in the box | folklore; the membership is taken as obvious, never a headline Q/A |
| 10 | recent arXiv (last 5 years)      | surfaced by WebSearch #2 (interval-relation / order-iso papers)                            | weak | order isos and interval relations; reindexing preserves product intervals structurally | confirms it is standard and unnamed |

### Literature summary (Phase 3)

Concept identified as: **reindexing (precomposition by a coordinate bijection) preserving membership in a
product order interval** `[0,1]^I`; equivalently, that the reindexing equiv `Equiv.piCongrLeft'` is an
order isomorphism of the product order sending the cube to the cube.
Sources agree on the standard form: **yes** — a bijection of index sets induces an order iso of the
product order, hence maps `∏ [a_i, b_i]` bijectively to the reindexed product interval; membership is
preserved by definition. Universal, no finiteness needed.
Most general standard form: for any bijection `e : κ ≃ ι` and any family of intervals, precomposition
`f ↦ f ∘ e` carries `{f | ∀ i, f i ∈ S_i}` to `{g | ∀ j, g j ∈ S_{e j}}`; for the constant family
`S_i = [0,1]` this is exactly "reindex the cube, stay in the cube."
Generality dimensions where the literature varies:
  - index types: finite (the usual `ℝ^n` picture) up to arbitrary (the fact needs no finiteness).
  - carrier / order: any partially-ordered carrier with a product order; ℝ and `[0,1]` are incidental.
  - map: a full equiv is not even needed for the **⊆** direction — any function `e` gives
    `(c ∘ e) ∈ Icc 0 1` from `c ∈ Icc 0 1` (you only reindex the universally-quantified bounds).
Disagreement with the literature: **none**. Crucially, "reindexing keeps you in the product interval" is
**never a named theorem** — it is the structural fact that the product order is pointwise and a bijection
of coordinates is an order iso. The named object in mathlib's vocabulary is the reindexing iso itself
(`Equiv.piCongrLeft'` / `OrderIso.preimage_Icc`), not this membership corollary.

---

## Generality analysis — `Chebotarev.cubeRelabel_mem_Icc`

Literature-standard form (from Phase 3): precomposition by a bijection (in fact any function) of index
sets preserves membership in a product order interval, over any carrier and any index types.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `K`, `[Field K]`, `[NumberField K]` | a number field | **nothing** — pure reindexing | YES (drop entirely) | `K` enters only to name `equivFinRank` and the index types; the membership fact has no number-theory content whatsoever |
| 2 | index `Fin (card − 1)` / `{w ≠ w₀}` | the two NT-specific index types | arbitrary index types `κ`, `ι` | yes | nothing uses the specific index types; only a map `κ → ι` between them is needed |
| 3 | the map `equivFinRank.symm` | a specific equiv | any equiv `e : κ ≃ ι` (or even any function for ⊆) | yes | the proof `fun _ ↦ hc.1 _` only reindexes the `∀`; it never uses that `equivFinRank` is bijective |
| 4 | carrier `ℝ` | the reals | any `[Preorder α]` (or `OrderedAddCommMonoid` for `0`/`1`) | yes | `Pi.le` is pointwise for any `Preorder`; `0`/`1` are the only ℝ-specific items, and even they are arbitrary endpoints |
| 5 | bounds `0`, `1`        | the unit cube            | any `Icc a b` (product interval)  | yes                 | nothing uses `0`/`1` specifically |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (specialised to a number field, two NT index
types, ℝ, and the unit cube), **but this narrowing is irrelevant to the verdict** because the statement
is **subsumed by mathlib primitives at every generality level** (Phase 5/6). The maximally-general form —
"precomposition by a function preserves product-interval membership" — is itself a one-line coordinatewise
unfolding (`Pi.le_def`), and mathlib already packages the equiv case as `OrderIso.preimage_Icc` via
`Equiv.piCongrLeft'`. Generalising would only produce a *more general trivial lemma* that is *still* a
≤2-projection composition; it does not convert a NO into a YES.
Number of weakening opportunities found: 5 (drop `K` entirely, arbitrary indices, arbitrary map, arbitrary
carrier, arbitrary bounds) — all cosmetic relative to the verdict.
Cost of restatement: CHEAP — but moot, since the lemma should not exist in mathlib in any form.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | bundled hypotheses → typeclasses? | no | — | already minimal; only the (removable) `NumberField K` is bundled |
| 2  | sequences/metric → filters/topology? | no | — | purely an order-membership fact; no limits |
| 3  | construction → universal property? | no | — | nothing to characterise universally |
| 4  | set-with-predicate → bundled substructure? | **yes (points away from a lemma)** | the idiomatic encoding is `OrderIso.preimage_Icc` applied to the reindexing order-iso `Equiv.piCongrLeft'`: reindexing is an order iso, so it maps `Icc 0 1` to `Icc 0 1` by `preimage_Icc` (with `0`/`1` fixed) | this is the decisive point — mathlib already has the *reindexing iso* and a *general* `preimage_Icc`; the loose membership corollary is the less idiomatic direction |
| 5  | field/metric-specific → weaker typeclass? | yes (cosmetic) | any `[Preorder α]`, any `Icc a b` | full `Pi.le`/`Icc` API already at that generality |
| 6  | 1-categorical → higher-categorical? | no | — | n/a |
| 7  | concrete index → arbitrary structure? | yes (cosmetic) | arbitrary `κ`, `ι` with a map between them | the fact is index-agnostic |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, and it points AWAY from a named lemma.** The contemporary mathlib encoding
of "reindexing keeps you in the cube" is to use the **reindexing order-isomorphism itself**:
`Equiv.piCongrLeft'` (already in mathlib, and identified in `cubeRelabel.md` as the home of `cubeRelabel`)
packaged as an `OrderIso`, with membership following from the *general* `OrderIso.preimage_Icc`
(`Mathlib/Order/Interval/Set/OrderIso.lean:36`) since `0`/`1` are fixed by reindexing. Across the pi type
the bare fact is just the coordinatewise unfolding `Set.mem_Icc` + `Pi.le_def`. The move is to **use the
reindexing iso + the general `preimage_Icc`**, not to introduce a bespoke membership proposition. Real
mathematical improvement from a new lemma: none — this is a structural triviality already captured by
mathlib's order-iso/`Pi.le` API.

---

## Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (introduces no definitional equality or typeclass-search path).

---

## Mathlib search-status: `Chebotarev.cubeRelabel_mem_Icc`

[A] Lean-Finder        — natural-language "reindex tuple stays in unit cube / piCongrLeft preserves Icc"   n/a: AI index not reachable in this sandbox (local Lean build stale per task brief); compensated by exhaustive grep of the full mathlib tree, Method D, authoritative here
[B] Loogle             `(_ ≃ _) → _ ∈ Set.Icc _ _` ; `_ ∈ Set.Icc (0 : _ → _) 1` ; `Equiv.piCongrLeft' _ _ ∈ Set.Icc _ _`   n/a: `lean_loogle` tool not available in this environment
[C] LeanSearch         "reindexing a tuple by a bijection preserves membership in the unit cube"   n/a: `lean_leansearch` tool not available in this environment
[D] Grep mathlib src   `piCongrLeft`, `preimage_Icc`, `Pi.le_def`, `mem_Icc`, `pi_univ_Icc`, `piecewise_mem_Icc`, `comp.*Icc`, `reindex.*Icc`   **hits** (building blocks; no exact lemma)
[E] Name pattern       `piCongrLeft`, `preimage_Icc`, `mem_Icc`, `OrderIso`   **hits** (the primitives below)

Searched for both the user's form (`cubeRelabel … ∈ Icc 0 1`) and the literature-standard form
("reindex by a bijection ⟹ product-interval membership preserved" at any generality). Findings
(Method D, over `.lake/packages/mathlib/Mathlib/`):

- **`Set.mem_Icc` (`Order/Interval/Set/Defs.lean:80`, `@[simp]`)**: `x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b` — and
  it is `.rfl`, so `cubeRelabel K c ∈ Icc 0 1` is **definitionally** the pair `⟨0 ≤ cubeRelabel K c,
  cubeRelabel K c ≤ 1⟩` — exactly the anonymous constructor the project proof uses.
- **`Pi.le_def` (`Order/Basic.lean`)**: `x ≤ y ↔ ∀ i, x i ≤ y i` — the pi order is pointwise; this is what
  turns each half of `hc` and of the goal into a `∀`-over-coordinates, where reindexing is transparent.
- **`Equiv.piCongrLeft'`** (and `LinearEquiv.piCongrLeft'`, surfaced by WebSearch #3 and used in the
  sibling `cubeRelabel.md`): reindexing a pi type by an equiv; `cubeRelabel K c = Equiv.piCongrLeft' _
  equivFinRank.symm` shape. Composes with order-iso `preimage_Icc` below.
- **`OrderIso.preimage_Icc` (`Order/Interval/Set/OrderIso.lean:36`)**:
  `e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b)` — the general, idiomatic route: reindexing is an order iso
  fixing `0`/`1`, so it carries `Icc 0 1` to `Icc 0 1`.
- **`Set.pi_univ_Icc` (`Order/Interval/Set/Pi.lean:40`)** and **`Set.piecewise_mem_Icc'`
  (`Pi.lean:53`)** already exhibit the exact `⟨fun i ↦ …, fun i ↦ …⟩` / `⟨h.1 _, h.2 _⟩` idiom for proving
  pi-`Icc` membership coordinatewise — the project's proof is a textbook instance of this idiom.
- No `cubeRelabel` / "reindex preserves `Icc`" standalone membership lemma exists (reindexing is
  represented by the iso `piCongrLeft'`, whose membership consequences come from `preimage_Icc`, not from
  a bespoke lemma).

Concluded: **found the building blocks** (`Set.mem_Icc` `.rfl` + `Pi.le_def`, with the idiomatic packaged
route `Equiv.piCongrLeft'` + `OrderIso.preimage_Icc`); the lemma's content is a ≤2-call coordinatewise
composition (in practice: reindex the two `∀`-bounds of `hc`). **Not in mathlib as a named lemma — and
should not be**, because the membership is the pointwise unfolding of the product order under an order-iso
reindexing.

---

## Call sites — `Chebotarev.cubeRelabel_mem_Icc`

Internal use count: **2** (both within the declaring file `NormLeOneLipschitz.lean`)
External-to-file callers: **0** distinct files (confirmed: `grep -rn cubeRelabel_mem_Icc projects/
--include=*.lean` outside `NormLeOneLipschitz.lean` returns nothing)

| Caller file:line                         | Usage pattern (one-line excerpt) |
|------------------------------------------|-----------------------------------|
| NormLeOneLipschitz.lean:325              | `rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]` — supplies `cubeRelabel K c ∈ Icc 0 1` so the clamp is the identity on the `w₀`-face term |
| NormLeOneLipschitz.lean:337              | `rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]` — same, on the side-face term |

Inline-derivation grep (was the same statement re-derived elsewhere without `cubeRelabel_mem_Icc`?):
  - (none) — the only producers of `cubeRelabel K c ∈ Icc 0 1` route through this lemma; both feed
    `clampUnit_eq_self`.

Signal reading: K = 2 internal uses, both inside the declaring file, zero external, zero in any other
project file. Per the call-sites table this is a **local convenience wrapper** — real enough that inlining
would repeat the same 2-projection term twice, but with no consumer outside this single file and none
outside the project. Combined with the trivial (reindexing-only) proof, this leans
**NO-composable-from-mathlib** (it is glue, not API). It is the exact structural twin of the sibling
`clampUnit_mem_Icc` (also `NO-composable-from-mathlib`, also K = 2 in-file).

---

## Composition check (Phase 6)

Can `cubeRelabel K c ∈ Set.Icc 0 1` be derived from mathlib in ≤3 chained calls? `cubeRelabel K c` is
*definitionally* `fun j ↦ c (equivFinRank.symm j)`, and `Set.mem_Icc` is `.rfl`, so the goal is
definitionally `0 ≤ cubeRelabel K c ∧ cubeRelabel K c ≤ 1`.

Attempt 1 (the existing proof, already a composition):
  `⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩`
  - Mathlib decls used: `Set.mem_Icc` (`.rfl`), `Pi.le_def` (the pi order is pointwise) — both implicit
    in the anonymous constructor and the `hc.1 _` / `hc.2 _` applications.
  - Result: **succeeds** — this *is* the proof; two pointwise projections of `hc` reindexed, no lemma of
    its own needed.
  - Notes: no values produced; the bounds are literally `hc`'s, applied at `equivFinRank.symm j`.

Attempt 2 (idiomatic packaged route, via the reindexing order-iso):
  treat reindexing as `OrderIso` `o` built from `Equiv.piCongrLeft' _ equivFinRank.symm`; then
  `o ⁻¹' Icc 0 1 = Icc (o.symm 0) (o.symm 1) = Icc 0 1` by `OrderIso.preimage_Icc` + `map_zero`/`map_one`.
  - Mathlib decls used: `Equiv.piCongrLeft'`, `OrderIso.preimage_Icc`, `map_zero`/`map_one`.
  - Result: **succeeds** but is **heavier** than Attempt 1 — only worth it if one wants the set-level
    equality `cubeRelabel '' Icc 0 1 = Icc 0 1` rather than a single-point membership.

Conclusion: **COMPOSABLE.** The statement is a ≤3-call composition — in practice a 2-projection
reindexing of `hc` (`⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩`), with an idiomatic order-iso alternative via
`OrderIso.preimage_Icc`. No mathematical content beyond the pointwise product order.

---

## Verdict: `Chebotarev.cubeRelabel_mem_Icc`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): "reindexing keeps you in the product interval" is the structural fact that
  the product order is pointwise and a coordinate bijection is an order iso — **never a named result**;
  the named object is the reindexing iso (`Equiv.piCongrLeft'` / `OrderIso.preimage_Icc`), not this
  membership corollary.
- Generality analysis (Phase 4): STRICTLY NARROWER (number field, two NT index types, ℝ, unit cube) but
  moot — even dropping `K` entirely and going to arbitrary indices/carrier/bounds yields a one-line
  coordinatewise triviality. Modern-idiom check (4c) shows the idiomatic encoding is the reindexing
  order-iso + the *general* `OrderIso.preimage_Icc`, pointing away from a bespoke lemma.
- Mathlib search (Phase 5): no named lemma; building blocks present — `Set.mem_Icc` (`.rfl`), `Pi.le_def`,
  `Equiv.piCongrLeft'`, `OrderIso.preimage_Icc`; `Set.pi_univ_Icc` / `Set.piecewise_mem_Icc'` already use
  the identical coordinatewise idiom.
- Composition check (Phase 6): **COMPOSABLE** — the proof is itself the composition
  (`⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩`, reindexing the two `∀`-bounds of `hc`).

**Rationale:**

`cubeRelabel_mem_Icc` says that relabelling the coordinates of a point of the unit cube `[0,1]^{r−1}` (via
the bijection `equivFinRank.symm`) keeps you in the unit cube. Because membership in a pi-type `Icc 0 1`
is *pointwise* (`Set.mem_Icc` is `.rfl`; `Pi.le_def` makes `0 ≤ f` / `f ≤ 1` mean `∀ i, …`), the lemma is
nothing more than reindexing the two universally-quantified bounds of the hypothesis `hc`: `hc.1` and
`hc.2` applied at `equivFinRank.symm j`. The proof produces no values and uses no property of
`equivFinRank` beyond its being a function — even bijectivity is unnecessary for this direction. Mathlib
already represents the reindexing itself as `Equiv.piCongrLeft'` (the home of the parent `cubeRelabel`,
per `cubeRelabel.md`, verdict NO-mathlib-has-it) and carries a fully general `OrderIso.preimage_Icc`; the
membership is the pointwise unfolding of those, exactly the idiom mathlib already uses in
`Set.piecewise_mem_Icc'` and `Set.pi_univ_Icc`. The lemma therefore has no mathematical content of its own,
is a ≤3-call composition, and has zero consumers outside its single declaring file (K = 2, both feeding
`clampUnit_eq_self`). It is the structural twin of the sibling `clampUnit_mem_Icc` (also
NO-composable-from-mathlib), differing only in that here the bounds are *inherited* (reindexing) rather
than *produced* (clamping) — making it, if anything, even more trivial.

This is a textbook NO-composable: mathlib has the building blocks, the form is a trivial inline
composition, and no new lemma is justified.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; `cubeRelabel K c ∈ Icc 0 1` is a 1–3-call composition.
  - Building blocks (with full paths):
    - `Set.mem_Icc` — `Mathlib/Order/Interval/Set/Defs.lean:80` (`@[simp]`, `.rfl`) — `x ∈ Icc a b ↔ a ≤ x
      ∧ x ≤ b`; makes the goal *definitionally* a pair.
    - `Pi.le_def` — `Mathlib/Order/Basic.lean` — `x ≤ y ↔ ∀ i, x i ≤ y i`; the pi order is pointwise, so
      reindexing the bound is transparent.
    - (idiomatic, optional) `Equiv.piCongrLeft'` — reindex a pi type by an equiv — plus
      `OrderIso.preimage_Icc` — `Mathlib/Order/Interval/Set/OrderIso.lean:36` —
      `e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b)`, for the set-level statement.
  - Composition sketch (≤3 lines), pick either:
    ```lean
    -- the existing proof: reindex the two pointwise bounds of hc
    example {c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ}
        (hc : c ∈ Set.Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1) :
        cubeRelabel K c ∈ Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
      ⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩
    -- or, fully general, drop K / number field entirely:
    --   example {κ ι : Type*} (e : κ → ι) {c : ι → ℝ} (hc : c ∈ Set.Icc 0 1) :
    --     (c ∘ e) ∈ Set.Icc 0 1 := ⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩
    ```
  - Call sites in this project (from Phase 6.0): **K = 2** — `NormLeOneLipschitz.lean:325` and
    `NormLeOneLipschitz.lean:337`, both `rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]`.
  - Refactor plan: this is a `ForMathlib/` helper that, on the evidence, should **not** be upstreamed as
    its own lemma. Two reasonable dispositions, both fine for `main`/cleanup (no statement change to any
    public result):
      1. **Keep it project-local** (recommended) — it is a 2-use convenience wrapper that legitimately
         avoids repeating the 2-projection term twice in the `clampUnit_eq_self` rewrites; it is *not*
         mathlib material, so it should simply lose any "earmarked for mathlib" tag. No PR.
      2. **Inline** — at lines 325 and 337 replace `cubeRelabel_mem_Icc K hc` with the inline term
         `(⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩ : cubeRelabel K _ ∈ Set.Icc 0 1)` (Lean infers the cube from
         `clampUnit_eq_self`'s expected argument), then delete `cubeRelabel_mem_Icc`. The two sites are
         identical, so the inline is mechanical; check the implicit-`hc` flow at each.
  - Net: do **not** open a mathlib PR for this lemma. If any cube↔reindex API is wanted upstream, the
    mathlib-shaped statement is the *set-level* `Equiv.piCongrLeft' _ e '' Icc 0 1 = Icc 0 1` (or the
    `preimage` form) for a general equiv — which is itself an `OrderIso.preimage_Icc` corollary, not new
    content. The sibling `cubeRelabel` (the def) is already `NO — mathlib has it` (`Equiv.piCongrLeft'`),
    consistent with this membership corollary being NO-composable.

---

## Next step

Do not upstream `Chebotarev.cubeRelabel_mem_Icc`. Either keep it as a project-local convenience helper
(drop the mathlib earmark) or inline the ≤3-call composition `⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩` at its two
call sites (`NormLeOneLipschitz.lean:325`, `:337`) and delete it. The membership is the pointwise
unfolding of the product order under reindexing — `Set.mem_Icc` (`.rfl`) + `Pi.le_def`, with the idiomatic
packaged route being `Equiv.piCongrLeft'` + the general `OrderIso.preimage_Icc` — so no new mathlib lemma
is justified.
