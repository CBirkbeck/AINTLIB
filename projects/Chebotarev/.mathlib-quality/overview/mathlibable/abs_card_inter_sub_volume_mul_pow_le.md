# /mathlibable report — `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`

_Step-9 overview mathlibable assessment, single declaration. ChatGPT-math MCP was
down for the whole run (consistent Codex stdin failure); the literature phase was
carried by WebSearch (≥5 distinct queries at varying generality) + mathlib-doc
search. Loogle/LeanSearch deferred tools were not available in this environment;
Phase 5 used the authoritative mathlib source grep + the official mathlib4 docs.
Local references directory absent → recorded n/a._

---

### Baseline (Phase 0)
- lake build:               not re-run (task note: local build stale; reasoning from source). Decl elaborates in-repo (it is consumed by two downstream theorems that build).
- decl `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean:277`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Effective lattice-point count with a Lipschitz-boundary `O(nᵈ⁻¹)` error term — the deepest analytic input to the class-field-theory-free Chebotarev density formalisation. File header explicitly says "It is stated here for a future mathlib contribution."

True qualified name **verified**: the decl sits in `namespace Chebotarev` (opened line 51), is a plain `public`/`@[expose]` `theorem` (not `private`), so the qualified name is `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`. The parsed name in the ticket is correct.

---

### Statement (Phase 1)

`Chebotarev.abs_card_inter_sub_volume_mul_pow_le` is a theorem stating the
**count ↔ volume bridge** (the cell-count sandwich step of the classical
Lipschitz principle):

> Let `s ⊆ ℝ^d` (`d = #ι`, `ι` a fintype) be bounded and measurable, and let
> `n ≥ 1` be an integer. Form the scaled standard lattice `n⁻¹·ℤ^d`. Then the
> number of lattice points of `n⁻¹·ℤ^d` lying in `s` differs from `vol(s)·nᵈ`
> by at most the number of grid cells (half-open cubes of side `1/n`) of the
> `n⁻¹ℤ^d` grid that **meet the topological frontier `∂s`**:
> `| #(s ∩ n⁻¹·ℤ^d) − vol(s)·nᵈ | ≤ #{ cells of the n-grid meeting ∂s }`.

The proof is the standard three-set sandwich. Let `Inside = {ν : box(n,ν) ⊆ s}`,
`Meet = {ν : box(n,ν) ∩ s ≠ ∅}`, `Bd = index n '' frontier s` (cells meeting
`∂s`), and `Tag = {ν : tag(n,ν) ∈ s}` (the cells whose chosen lattice point lies
in `s`, in bijection with `s ∩ n⁻¹ℤ^d`). One shows `Inside ⊆ Tag ⊆ Meet` and the
key topological fact `Meet ⊆ Inside ∪ Bd` (a cell meeting `s` but not contained
in `s` must meet `∂s`, proved by `index_mem_image_frontier_of_box_meet_not_subset`
using preconnectedness of a box). Volume monotonicity gives
`#Inside ≤ vol(s)·nᵈ ≤ #Meet` (each cell has volume `n⁻ᵈ`). Combining,
`|#Tag − vol(s)·nᵈ| ≤ #Bd`.

Variables / typeclasses (Lean side):
- `ι : Type*`, `[Fintype ι]` — the (finite) coordinate index; `d = Fintype.card ι`.
- `s : Set (ι → ℝ)` — the region.
- `n : ℕ`, `hn : 1 ≤ n` — the lattice-refinement parameter.

Hypotheses (Lean side):
- `hbdd : Bornology.IsBounded s` — region is bounded (needed for finiteness of the cell sets and `vol s < ∞`).
- `hmeas : MeasurableSet s` — region is measurable (used only through `NullMeasurableSet` + `vol s ≠ ⊤`).
- `hn : 1 ≤ n` — i.e. `NeZero n`; `n⁻¹` makes sense and the grid is non-degenerate.

Conclusion (math): `| #(s ∩ n⁻¹ℤ^d) − vol(s)·nᵈ | ≤ #(cells meeting ∂s)`.

Conclusion (Lean):
`|(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) - volume.real s * (n:ℝ) ^ Fintype.card ι| ≤ (index n '' frontier s).ncard`.

Note the lattice is written `span ℤ (range (Pi.basisFun ℝ ι))` = `ℤ^ι` (the
standard `ZLattice`), and `index n '' frontier s` is exactly the set of grid
indices `ν` such that the cell `box n ν` meets `∂s`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (leaning BIG-adjacent)
Reason: it is a `theorem` (not a new structure), a *helper/building block* rather
than the file's terminal export. But it is named in the module docstring under
"building blocks reused by the unit-grid ideal-congruence count" and is the
*mathematical heart* of the effective count — so although formally SMALL, it is
the load-bearing analytic lemma, not throwaway glue. (Literature width was
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. (Body is a ~75-line
sandwich proof, the opposite of a one-liner.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "lattice point counting bounded region volume error term number of boundary cells Lipschitz boundary"  | yes  | `‖ #(Z∩ℤⁿ) − vol(Z)‖ ≤ Σ boundary terms`; "abs value of the difference between #lattice points in K and vol(K) is bounded by the number of boundary cubes" | Widmer (RHUL notes), Gorodnik–Nevo, arXiv 2411.13522 |
| 2  | WebSearch (named-after / general)| "number of lattice points in domain equals volume plus error bounded by boundary cells Davenport Lang" | yes  | Davenport: `#(S∩ℤⁿ) = volₙ(S) + O(max V̄(S),1)`; explicit form `‖|Z∩ℤⁿ| − Vol(Z)‖ ≤ Σⱼ hⁿ⁻ʲVⱼ(Z)` | Davenport 1951; "classical Lipschitz counting principle" named explicitly |
| 3  | WebSearch (convex-body variant)  | "boundary cubes lattice points convex body difference volume bounded number of cubes intersecting boundary" | yes | van der Corput / Blichfeldt covolume bounds; counting via boundary cubes | geometry-of-numbers context (Minkowski circle) |
| 4  | WebSearch (Widmer / sandwich)    | Widmer "number of grid cells"/"unit cubes" meeting boundary, sandwich before Lipschitz                  | **yes (decisive)** | **"The number of lattice points in S differs from the volume of S by at most the number of integer vector translates of the half-open unit tile [0,1)ⁿ that meet the boundary ∂S."** | Widmer, *Lipschitz class, narrow class, and counting lattice points*; this is **verbatim our lemma** (with the tile scaled by n) |
| 5  | WebSearch (mathlib-doc / effective) | "mathlib4 ... tendsto_card_div_pow_atTop_volume effective error term Lipschitz boundary"             | yes  | mathlib has only the **rate-free limit**; no effective version | leanprover-community docs for `BoxIntegral.UnitPartition`; also surfaced `ZLattice.Covolume` |
| 6  | ChatGPT MCP                      | "standard name + generality of the cell-count sandwich; does it need ∂s regularity?"                    | n/a  | — | **MCP down** all run (Codex stdin failure); task warned of this. Compensated by extra WebSearch queries #3,#4. |
| 7  | Local references                 | grep `.mathlib-quality/references/` for the concept                                                    | n/a  | — | **No references dir** (`projects/Chebotarev/.mathlib-quality/references/` and `refs/` both absent) → recorded n/a per protocol. |
| 8  | nLab                             | "lattice point counting / Lipschitz principle"                                                          | n/a  | — | Not an nLab-style categorical concept; nLab has no dedicated entry on the boundary-cell count. Recorded n/a with reason. |
| 9  | nCatLab                          | —                                                                                                       | n/a  | — | Not a categorical concept. |
| 10 | Stacks Project                   | —                                                                                                       | n/a  | — | Not an algebraic-geometry concept (real-analytic geometry of numbers). |
| 11 | MathOverflow / Math.SE           | covered via WebSearch #1–#4 (geometry-of-numbers Q&A surfaced)                                          | yes  | agrees: error ≤ #boundary cells | folded into #1–#4 |
| 12 | recent arXiv (last 5 yrs)        | "sharp o-minimality and lattice point counting"; "heights and morphisms in number fields"; GRS 1611.10103 | yes | Lipschitz principle main-term-plus-error is current and actively used | arXiv 2503.01731, 2411.13522, **1611.10103 (Gun–Ramaré–Sivaraman, the project's own ref family)** |

Protocol pass check: WebSearch ran 5 distinct queries at 4 generality levels
(specific cell form / Davenport general / convex-body / Widmer-sandwich /
mathlib). ChatGPT MCP attempted twice, down both times — explicitly recorded,
not silently skipped. Local refs, nLab, nCatLab, Stacks, MathOverflow, arXiv all
checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the cell-count step of Davenport's Lipschitz (counting)
principle** — "the number of lattice points of a set differs from its volume by
at most the number of grid cells meeting the boundary." Classical; appears in
Davenport (1951), Lang *Algebraic Number Theory* GTM 110 (Ch. V §2 / Ch. VI §3
Thm 3, p. 129), Widmer (*Lipschitz class, narrow class, and counting lattice
points*), Masser–Vaaler, and — directly for this project — Gun–Ramaré–Sivaraman,
*Counting ideals in ray classes*, JNT 243 (2023), after Debaene.

Sources agree on the standard form: **yes.** Widmer states the cell-count
sandwich essentially verbatim. It is a *recognised standalone intermediate step*:
the principle is universally proved in two stages — (a) error ≤ #boundary cells
(this lemma, needing only bounded + measurable), then (b) #boundary cells =
`O(nᵈ⁻¹)` via Lipschitz parametrisation of `∂s` (the project's separate
`ncard_index_image_frontier_le`).

Most general standard form: for a full-rank lattice `Γ ⊂ ℝⁿ` with covolume
`det Γ`, `‖ #(S ∩ Γ) − vol(S)/det Γ ‖ ≤ #{ fundamental cells of Γ meeting ∂S }`,
for **any bounded measurable** `S` (no boundary regularity needed at this step).

Generality dimensions where the literature varies:
- **lattice**: from "scaled standard lattice `n⁻¹ℤⁿ`" (this lemma) up to "arbitrary full-rank `Γ` with covolume" (Widmer's general form). The standard-lattice-scaled-by-n form is the textbook special case.
- **boundary regularity**: the *full* principle assumes `∂S` is Lipschitz-parametrisable, but the *cell-count step alone* (this lemma) assumes only bounded + measurable. This lemma is correctly stated at the weaker hypothesis for the pure-sandwich half. ✓
- **measure**: Lebesgue throughout (Haar on `ℝⁿ`).

Disagreement with the literature: none. The Lean form matches the recognised
standalone step at the right (minimal) hypotheses for that step.

---

### Generality analysis — `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`

Literature-standard form (from Phase 3): error ≤ #(fundamental cells meeting ∂S),
for any bounded measurable S, over a full-rank lattice Γ; the most general
*lattice* axis is "arbitrary `Γ` with covolume", the textbook case being
`Γ = n⁻¹ℤⁿ`.

| # | Parameter / hypothesis      | Current Lean form                 | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|-----------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | `[Fintype ι]`              | finite coordinate index           | `n`-dimensional Euclidean space  | NO                  | `d = #ι` must be finite for `vol`, grid cells, and `nᵈ`. Maximal. |
| 2 | `hbdd : IsBounded s`       | bounded                           | bounded                          | NO                  | needed for cell-set finiteness + `vol s < ∞`. Maximal for this step. |
| 3 | `hmeas : MeasurableSet s`  | measurable                        | measurable                       | borderline          | used only via `NullMeasurableSet` + `vol s ≠ ⊤`; could weaken to `NullMeasurableSet`, but that is a cosmetic micro-weakening, not a literature axis. |
| 4 | `hn : 1 ≤ n`               | refinement integer ≥ 1            | covolume of a general lattice Γ  | **conceptually yes**| the lattice is hard-wired as `n⁻¹·(standard ℤ^ι)`. The literature-general statement is over an arbitrary full-rank `Γ` (mathlib: `ZLattice` / `ZLattice.Covolume`). This is the one real generality axis. |
| 5 | RHS `(index n '' frontier s).ncard` | #cells of the n-grid meeting ∂s | #fundamental cells of Γ meeting ∂S | tied to #4 | the cell-count is expressed in the n-grid's `index`; a Γ-general form would phrase it via Γ's fundamental domain. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for the set `s` axis** (bounded +
measurable is exactly the right minimal hypothesis for the pure cell-count step),
but **STRICTLY NARROWER on the lattice axis** (hard-wired `n⁻¹·ℤ^ι` rather than a
general `ZLattice`).

Number of weakening opportunities found: 1 substantive (lattice axis) + 1
cosmetic (`MeasurableSet` → `NullMeasurableSet`).

Proposed restatement (lattice-general), schematic:
```
theorem abs_card_inter_sub_volume_le {ι} [Fintype ι]
    {Λ : Submodule ℤ (ι → ℝ)} [IsZLattice ℝ Λ]   -- full-rank lattice
    {s : Set (ι → ℝ)} (hbdd : IsBounded s) (hmeas : NullMeasurableSet s) :
    |(Nat.card ↑(s ∩ Λ) : ℝ) - volume.real s / ZLattice.covolume Λ|
      ≤ #{ fundamental cells of Λ meeting (frontier s) }
```
Cost of restatement: **EXPENSIVE** — the entire `box`/`index`/`tag`
infrastructure of `BoxIntegral.unitPartition` is built specifically for the
`n⁻¹ℤ^ι` grid; a Γ-general fundamental-domain cell count and its sandwich would
need new API (essentially a `ZLattice`-level reworking of `unitPartition`). This
is a genuine research-formalisation effort, not a mechanical rewrite.

**Crucial caveat (why this does NOT force YES-but-generalise):** mathlib's own
companion result `tendsto_card_div_pow_atTop_volume` is *also* hard-wired to the
`n⁻¹ℤ^ι` grid (same `L = span ℤ (range (Pi.basisFun ℝ ι))`, same `box`/`index`
machinery). The project's lemma is the **effective sibling at exactly mathlib's
established generality**. Generalising the lattice axis is a separate, library-wide
project that should generalise *both* the limit and the effective form together —
it is not a precondition for upstreaming the effective form in the form mathlib
already chose for the qualitative one. Per the skill's cost rule, EXPENSIVE does
not by itself downgrade the verdict; and here the narrower lattice axis is the
*house style* of the very mathlib file this would join.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | bundled-hyp → typeclass/instance? | no | `IsBounded`/`MeasurableSet` are already the idiomatic predicate hypotheses | — |
| 2  | sequences/metric → filters/topology? | no | statement is a single inequality at fixed `n`; no limit to filter-ise (the *limit* sibling already lives in mathlib) | — |
| 3  | construct → universal property? | no | nothing constructed | — |
| 4  | set-with-predicate → bundled substructure? | no | — | — |
| 5  | vector-space/field-specific → weaken typeclass? | no | already over `ι → ℝ` exactly as mathlib's `unitPartition`; `ℝ`-specific is intrinsic (Lebesgue/Haar) | — |
| 6  | 1-categorical → higher-categorical? | no | — | — |
| 7  | **concrete index → general algebraic structure?** | **yes** | replace `n⁻¹·(standard ℤ^ι)` by a general `ZLattice` Λ with `ZLattice.covolume` (the mathlib idiom surfaced in Phase-5 search: `Mathlib.Algebra.Module.ZLattice.Covolume`) | a `ZLattice`-general effective count would compose with all of mathlib's `ZLattice`/covolume/Minkowski API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, in principle** (the `ZLattice` generalisation of
the lattice axis), **but it is the SAME generalisation as Phase-4b row 4**, and:
- Cost: **EXPENSIVE** (needs a `ZLattice`-level reworking of `unitPartition`'s
  `box`/`index`/`tag`).
- It applies *equally* to mathlib's existing `tendsto_card_div_pow_atTop_volume`,
  which has **not** been so generalised. Asking the project's effective lemma to
  jump a generality bar that mathlib's own qualitative lemma has not cleared is
  not the right gate — they should be generalised together as a future
  `unitPartition`-over-`ZLattice` project.
- Real mathematical improvement: yes *eventually*, but **not blocking**: the
  contribution mathlib is missing is the *effective error term at the existing
  generality*, which is exactly what this lemma supplies.

Conclusion: the modern-idiom move is real but library-scoped and shared with the
existing mathlib limit; it informs *sequencing* (a later `ZLattice` generalisation
PR for the whole `unitPartition` family) rather than downgrading this lemma to
YES-but-generalise-first. This is a `BORDERLINE` consideration, surfaced as a
question to the maintainer below.

---

### Diamond / defeq risk — n/a

Declaration kind is `theorem` → Phase 4.5 skipped (no definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search-status: `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`

[A] Lean-Finder      — (deferred tool unavailable in this env) — n/a
[B] Loogle           — (deferred tool unavailable in this env) — n/a; compensated by source grep [D] + official docs
[C] LeanSearch       — natural-language web proxy: "mathlib4 lattice point count volume effective error term" — no effective-form hit; only the `tendsto_*` limits
[D] **Grep mathlib src** — `abs.*card.*volume`, `card.*sub.*volume`, `ncard.*frontier`, `Nat.card.*frontier`, `ncard.*volume.real` over **all** of `Mathlib/` — **no hits anywhere**; the only file pairing `card ∩ (scaled lattice)` with `volume` at all is `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`, which stops at the rate-free limit
[E] Name pattern     — searched `tendsto_card_div_pow*`, `*card*volume*pow*`, `*frontier*ncard*` — only `tendsto_card_div_pow_atTop_volume`, `…_volume'`, `tendsto_tsum_div_pow_atTop_integral` (all limits, no inequality)

Searched for both:
  - the user's current form (effective inequality with cell-count RHS) — **not in mathlib**
  - the literature-standard / more-general form (general `ZLattice` covolume effective bound) — **not in mathlib** (mathlib has `ZLattice.Covolume` definitions and `ZLattice` Minkowski theory, but **no** effective count-vs-volume error bound, and no boundary-cell sandwich, in any form)

Confirmed against the official mathlib4 docs page for `BoxIntegral.UnitPartition`
(leanprover-community.github.io): the file's public API is exactly the three
`tendsto_*` limits + the `box`/`index`/`tag`/`admissibleIndex`/`prepartition`
infrastructure. **No effective version is present.**

Concluded: **"not in mathlib (all available methods exhausted, plus the
literature-standard more-general form)."** Mathlib has the *qualitative limit*
sibling and the *infrastructure* this lemma is built on, but not this lemma's
*effective inequality* nor any generalisation of it.

---

### Call sites — `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`

Internal use count: **2** (within the project, excluding the declaring file's own
docstring/`Main results` mentions)
External-to-file callers: **1 distinct file** (`IdealCongruenceCount.lean`) — plus
1 same-file consumer.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `…/ForMathlib/LatticePointCount.lean:378` | `refine (abs_card_inter_sub_volume_mul_pow_le hbdd hmeas hn).trans ?_` — derives the terminal export `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (the `O(nᵈ⁻¹)` form) |
| `…/ForMathlib/IdealCongruenceCount.lean:247` | `have hbridge := abs_card_inter_sub_volume_mul_pow_le hRbdd hRmeas (n := 1) le_rfl` — applied with `n := 1` to a translated/scaled region `R = -w +ᵥ c•s`, powering the translate-uniform real-scale count `abs_cardR_translate_sub_volume_le` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this
lemma?): **(none)** — no other site re-proves a `|card − vol·pow| ≤ …` sandwich
inline. Both consumers go through this lemma.

Signal reading: **K = 2 genuine internal uses across two files, zero inline
re-derivation, used at both `n` general and `n = 1`** → this is real, reused API
(matches the "K ≥ … no inline re-derivation → YES-* bucket" row). The cross-file
reuse (`IdealCongruenceCount`) is the strongest signal — it is not a one-shot
wrapper around its own terminal export; an independent development re-applies it to
a transformed region.

---

### Composition check (Phase 6)

Can `abs_card_inter_sub_volume_mul_pow_le` be derived from mathlib in ≤3 chained
calls?

Attempt 1: from `tendsto_card_div_pow_atTop_volume` (the mathlib limit).
  - Mathlib decls used: `tendsto_card_div_pow_atTop_volume`.
  - Result: **fails.** That theorem is a *qualitative limit statement*
    (`card/nᵈ → vol s` as `n → ∞`, and only under `vol(∂s) = 0`). It yields **no
    effective bound at a fixed `n`**, and a limit cannot imply a finite-`n`
    inequality with an explicit RHS. Wrong direction of logical strength.

Attempt 2: assemble directly from `MeasureTheory` + `unitPartition` primitives
(`measureReal_mono`, `volume_box`, `Set.ncard_union_le`, the `box`/`index`/`tag`
lemmas).
  - Result: **fails as a ≤3-call composition.** The actual proof is the ~75-line
    three-set sandwich `Inside ⊆ Tag ⊆ Meet`, `Meet ⊆ Inside ∪ Bd`, with the
    topological lemma `index_mem_image_frontier_of_box_meet_not_subset`
    (preconnectedness of `box n ν`) and two volume-monotonicity bounds. This is a
    genuine proof with intermediate `have`s and real reasoning between them — by
    the skill's heuristics, "multiple `have`s with non-trivial reasoning ⇒ NOT a
    composition."

Conclusion: **NOT-COMPOSABLE.** Mathlib supplies the *infrastructure* but not a
≤3-call route to the statement; the cell-count sandwich is irreducible work.

---

## Verdict: `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`

**Category:** YES-add-as-is

(with a single BORDERLINE flag for the maintainer on lattice-axis sequencing — see
question at the end; it does not block the YES.)

**Evidence:**
- Literature search (Phase 3): the cell-count sandwich step of Davenport's
  Lipschitz principle; Widmer states it essentially verbatim ("#lattice points
  differs from the volume by at most the number of unit-tile translates meeting
  ∂S"); standard in Lang GTM 110, Masser–Vaaler, Gun–Ramaré–Sivaraman. Stated at
  the correct minimal hypotheses (bounded + measurable; no boundary regularity for
  this step).
- Generality analysis (Phase 4): MAXIMALLY GENERAL on the set axis; STRICTLY
  NARROWER only on the lattice axis — but that narrower axis is *identical to
  mathlib's own `tendsto_card_div_pow_atTop_volume`*, so it is house-style, not a
  defect. Generalising it is an EXPENSIVE, library-wide `ZLattice` project shared
  with the existing limit.
- Mathlib search (Phase 5): not in mathlib in any form; the file
  `BoxIntegral/UnitPartition.lean` has the rate-free limit and the infrastructure,
  but no effective error bound (confirmed against official mathlib4 docs).
- Composition check (Phase 6): NOT-COMPOSABLE (the limit is strictly weaker; the
  sandwich is a ~75-line proof).

**Rationale:**

This is the canonical "effective sibling of an existing mathlib limit." Mathlib's
`tendsto_card_div_pow_atTop_volume` already establishes `card(s ∩ n⁻¹ℤ^d)/nᵈ →
vol s` (rate-free, under `vol(∂s)=0`), using the very same `box`/`index`/`tag`
unit-partition machinery. The project's lemma proves the **finite-`n`,
quantitative** statement that *underlies* that limit: at each `n`, the count error
is bounded by the number of grid cells meeting the boundary. That is strictly more
information than the limit (the limit follows from it by sending `n → ∞` once the
cell count is `o(nᵈ)`), and it is exactly the form needed for any *effective*
application (power-saving error terms, the Lipschitz principle, ideal-counting in
analytic number theory). The literature treats the cell-count sandwich as a named,
standalone step, stated at precisely these hypotheses.

**WHY add it (the gap, refactor-actionable):** the concrete, named gap is that
`Mathlib/Analysis/BoxIntegral/UnitPartition.lean` provides *only* the rate-free
limits (`tendsto_card_div_pow_atTop_volume`, `…'`, `tendsto_tsum_div_pow_atTop_integral`)
and the unit-partition infrastructure, but has **no effective / error-term
companion** — there is currently no way in mathlib to bound `|count − vol·nᵈ|` at
a fixed `n`. Anyone wanting an explicit rate (the entire geometry-of-numbers
Lipschitz-principle toolkit: Davenport, Widmer, Masser–Vaaler) must rebuild this
sandwich by hand, as this project did. Adding it:
- *fills the effective-counting gap* in `UnitPartition` directly above the
  existing limit (it is the lemma the limit's own proof morally contains but does
  not expose);
- *composes with the existing API*: it is built from `volume_box`,
  `setFinite_index`, `measureReal_biUnion_finset`, `Set.ncard_union_le` — all
  already in mathlib — and in turn it makes the effective `O(nᵈ⁻¹)` count
  (`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, also in this file)
  derivable, which is the actual deliverable downstream consumers want;
- has **2 real consumers already** (one cross-file), demonstrating it is reusable
  API, not a single-use wrapper.

Proposed mathlib location: `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`
(same file as `tendsto_card_div_pow_atTop_volume` — it belongs *immediately before*
the limit, as the effective lemma the limit specialises from), or a sibling
`Mathlib/Analysis/BoxIntegral/UnitPartitionCount.lean` if the file is felt too
long. The supporting helpers (`setFinite_index_image_of_isBounded`, the `box`-meets-
`∂s` ⇒ index-in-`frontier`-image lemma, `measureReal_biUnion_box`) ship alongside.

Proposed PR title: `feat(Analysis/BoxIntegral): effective lattice-point count
error bound (boundary-cell sandwich)`

PR grouping: ship as one PR with its immediate `ForMathlib/LatticePointCount.lean`
neighbours that are also clean upstream candidates — at least
`setFinite_index_image_of_isBounded` (a genuinely general "index-image of a bounded
set is finite" fact) and the terminal `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
(the `O(nᵈ⁻¹)` Lipschitz-boundary form) — so the effective lemma lands together
with the export it powers and the finiteness helper it needs. (Run `/mathlibable`
per-decl on those neighbours first to confirm.)

Pre-PR checklist before opening:
- [ ] `/generalise Chebotarev.abs_card_inter_sub_volume_mul_pow_le` — apply the
  cosmetic `MeasurableSet → NullMeasurableSet` weakening (the proof already only
  uses `NullMeasurableSet` + `vol s ≠ ⊤`); confirm no other easy weakening. Decide
  with the maintainer whether to do the `ZLattice` lattice-axis generalisation now
  or as a follow-up that also generalises the existing limit.
- [ ] `/cleanup …/LatticePointCount.lean Chebotarev.abs_card_inter_sub_volume_mul_pow_le`
  — full style audit + diff gates (drop the `Chebotarev` namespace; rename to drop
  the project prefix; align with `unitPartition`'s naming, e.g. live under
  `BoxIntegral.unitPartition` and reuse its `L`/`box`/`index` rather than re-spelling
  `span ℤ (range (Pi.basisFun ℝ ι))`).
- [ ] Pick a reviewer from recent `Mathlib/Analysis/BoxIntegral/` history — the
  author/maintainers of `UnitPartition.lean` (the `tendsto_card_div_pow` series)
  are the natural reviewers since this slots directly into their file.

**BORDERLINE flag for the maintainer (single question, does not block the YES):**
1. Should the effective lemma be upstreamed *now* at mathlib's existing
   `n⁻¹·ℤ^ι`-grid generality (matching `tendsto_card_div_pow_atTop_volume`), with
   the `ZLattice`-general version deferred to a later PR that generalises the whole
   `unitPartition` count family (limit + effective) together? (Recommended: **yes**
   — do not gate the effective form on a library-wide generalisation that mathlib's
   own qualitative form has not undergone.)

---

## Next step

Open a `feat(Analysis/BoxIntegral)` PR adding the effective boundary-cell count
bound to `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`, grouped with
`setFinite_index_image_of_isBounded` and the `O(nᵈ⁻¹)` export it powers. First run
`/generalise` (apply the `NullMeasurableSet` weakening; settle the `ZLattice`
question with the maintainer) and `/cleanup` (drop the `Chebotarev` namespace,
align naming with `unitPartition`).
