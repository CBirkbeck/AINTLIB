# /mathlibable report — `Chebotarev.ncard_index_image_chart_le`

## Verdict: **YES-but-generalise-first**

One-line: standard "Principle of Lipschitz" boundary kernel, genuinely missing from
mathlib, but stated narrower than the literature (sup-norm-hardcoded, unit-cube-only) —
generalise the domain/codomain before PR.

---

### Baseline (Phase 0)

- lake build:               not re-run (project build stale per task; reasoning from source)
- decl `Chebotarev.ncard_index_image_chart_le`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean:138`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  effective (`O(tᵈ⁻¹)`-rate) lattice-point count with a
  Lipschitz-boundary error term — the deepest analytic input to the CFT-free
  Chebotarev density proof; the file is explicitly earmarked "stated here for a future
  mathlib contribution".

Qualified name **VERIFIED** from source: namespace `Chebotarev` (line 51) + `theorem
ncard_index_image_chart_le` (line 138) ⇒ `Chebotarev.ncard_index_image_chart_le`. (The
parsed guess in the task was correct.)

---

### Statement (Phase 1)

`ncard_index_image_chart_le` is the **single-chart cell-count** kernel of the Lipschitz
lattice-point counting principle. In prose:

> Let `φ : [0,1]^{d-1} → ℝ^d` be an `M`-Lipschitz map, where `ℝ^d = (ι → ℝ)` carries the
> sup (ℓ^∞) metric and `d = Fintype.card ι`. For the scaled integer grid `(1/n)·ℤ^d`
> (`n ≥ 1`), the number of grid cells that meet the image `φ([0,1]^{d-1})` is at most
> `(2⌈M⌉+1)^d · (n+1)^{d-1}`, i.e. `O(n^{d-1})`.

Here "grid cells meeting `φ([0,1]^{d-1})`" is encoded as the cardinality of the
`index n`-image of `φ([0,1]^{d-1})`, where mathlib's `BoxIntegral.unitPartition.index n x
i = ⌈n·xᵢ⌉ - 1` assigns to each point the index of the half-open cell of `(1/n)ℤ^d`
containing it. So `(index n '' (φ '' Icc 0 1)).ncard` = number of distinct cells touched.

Variables / typeclasses (Lean side):
- `{ι : Type*} [Fintype ι]` — coordinate index; `Fintype` supplies the sup-metric on `ι → ℝ`.
- `{M : ℝ≥0}` — Lipschitz constant.
- `{φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)}` — the chart; domain `[0,1]^{d-1}`,
  codomain `ℝ^d`.
- `{n : ℕ}` — grid refinement parameter.

Hypotheses (Lean side):
- `(hφ : LipschitzWith M φ)` — φ is `M`-Lipschitz.
- `(hn : 1 ≤ n)` — non-degenerate grid.

Conclusion (math): `#{cells of (1/n)ℤ^d meeting φ([0,1]^{d-1})} ≤ (2⌈M⌉+1)^d·(n+1)^{d-1}`.
Conclusion (Lean): `(index n '' (φ '' Set.Icc 0 1)).ncard ≤ (2 * ⌈(M:ℝ)⌉₊ + 1) ^
Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1)`.

Proof shape (≈55 lines): cover `[0,1]^{d-1}` by the `(n+1)^{d-1}` fibres of the
quantiser `q y k = ⌈n·yₖ⌉` (indexed by `T = Icc 0 (fun _ ↦ n)`); each fibre `Icc 0 1 ∩
q⁻¹{v}` has diameter `≤ 1/n` (`abs_sub_le_one_div_of_ceil_natCast_mul_eq`); under the
`M`-Lipschitz φ it maps to a set of diameter `≤ M·(1/n)` (`LipschitzWith.diam_image_le`),
which by the sibling lemma `ncard_index_image_le_of_diam_le` meets `≤ (2⌈M⌉+1)^d` cells;
sum over the `(n+1)^{d-1}` fibres via `Finset.set_ncard_biUnion_le`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline).
Reason: it is a named building block of a `## Main results`-listed development and the
quantitative kernel of a classical named principle (the "Principle of Lipschitz" /
Davenport's Lemma). Not a person-named theorem itself, but the literature anchor is a
named principle — so it is treated as BIG and the full exhaustive lit sweep is warranted.
(Note: lit width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-liner check **n/a**. (Body is a
~55-line proof.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "lattice point counting Lipschitz boundary number of grid cells O(n^{d-1}) Lang algebraic number theory" | yes  | `S ∈ Lip(D,M,L)`: ∂S covered by M maps `φᵢ:[0,1]^{D-1}→ℝ^D`, `\|φᵢ(x)-φᵢ(y)\|≤L\|x-y\|`; error = #boundary cells | Widmer (RHUL/TU Graz), Gorodnik–Nevo, Lang GTM 110 |
|  2 | WebSearch (general / framework)  | "number of unit cubes intersecting image of Lipschitz map cube boundary estimate counting lattice points" | yes  | "a Lipschitz map sends a cube in the domain into a cube in the codomain" — *verbatim* the kernel | Widmer (Proc. AMS 2012); Masser–Vaaler |
|  3 | WebSearch (named-after / origin) | "Davenport lemma 1951 lattice points region bounded Lipschitz constant number of unit cubes meeting boundary" | yes  | **"The Principle of Lipschitz is also known as Davenport's Lemma."** #lattice pts = vol + O(boundary) | canonical name pinned: *Principle of Lipschitz* / *Davenport's Lemma* |
|  4 | WebSearch (history chain)        | "Masser Vaaler counting algebraic numbers Lipschitz parametrizable boundary lattice point error term grid cubes" | yes  | Masser–Vaaler star-body count; "refined to explicit error terms with power savings" | confirms M=L can be large vs diam, error may exceed main term — exactly the constant tracked here |
|  5 | WebSearch (mathlib anchor)       | "mathlib4 tendsto_card_div_pow_atTop_volume unitPartition BoxIntegral lattice points index" | yes  | mathlib has only the **qualitative** limit (no rate) | `tendsto_card_div_pow_atTop_volume`: `card(s ∩ n⁻¹•ℤ^ι)/n^d → vol s`; NO error term |
|  6 | ChatGPT MCP                      | standard-form + generality + historical-evolution question (×2 attempts, high + medium effort)         | n/a  | —                                | **server down** — Codex `exec` command failed both attempts (task pre-warned the MCP may be down); WebSearch channels 1–5 cover the same ground |
|  7 | Local references (`.mathlib-quality/references/`) | dir check + module-docstring citations                                                  | n/a  | —                                | no PDF refs dir for Chebotarev; the file itself cites Lang GTM 110 Ch.VI §3 Thm 3 (p.129) and Gun–Ramaré–Sivaraman §3.3/§3.5 after Debaene — the standard sources |
|  8 | nLab                             | (folded into queries 1–4 with "nLab" term)                                                             | n/a  | —                                | not a categorical concept; nLab has no dedicated page — recorded n/a |
|  9 | nCatLab                          | —                                                                                                      | n/a  | —                                | not a categorical concept |
| 10 | Stacks Project                   | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept (analytic NT / geometry of numbers) |
| 11 | MathOverflow / Math.SE           | (surfaced via queries 1–4)                                                                             | yes  | matches #1–#4; "Principle of Lipschitz" widely discussed | consistent with the named-principle finding |
| 12 | recent arXiv (last 5y)           | (surfaced via queries 1,2,4)                                                                           | yes  | Barroero–Widmer, "Slicing the stars" (arXiv 1609.08720), Debaene, "Sharp o-minimality and lattice point counting" (arXiv 2503.01731) | active area; all use the same Lipschitz-class kernel, never as a standalone named cell-count lemma |

### Literature summary (Phase 3)

Concept identified as: **the Principle of Lipschitz** (= **Davenport's Lemma**, 1951);
modern framework: **Lipschitz parametrizability / Lipschitz class `Lip(D,M,L)`** (Masser–
Vaaler; Widmer). The specific decl is the **per-chart cell-count kernel** of that
principle.

Sources agree on the standard form: **yes**. Universally: ∂S is covered by `M` maps
`φᵢ : [0,1]^{D-1} → ℝ^D` with `|φᵢ(x)-φᵢ(y)| ≤ L|x-y|`, and the counting error is bounded
by the number of grid cells meeting `∪ᵢ φᵢ([0,1]^{D-1})`. The mechanism — *"a Lipschitz
map sends a cube in the domain into a cube in the codomain"* — is exactly this decl's
proof. The whole-boundary version is the sibling `ncard_index_image_frontier_le`; this
decl is the single-chart core.

Most general standard form: the count is `O(L^D · n^{D-1})` for the unit `(1/n)`-grid
(the constant here, `(2⌈M⌉+1)^d`, is the standard `(2⌊L⌋+2)^D`-type bound; the literature
tracks `L` carefully because `L` may be large relative to `diam S`).

Generality dimensions where the literature varies:
  - **norm on the codomain**: literature uses an arbitrary norm (Euclidean is common, the
    bound is norm-agnostic up to constants); the *cleanest* statement is the sup-norm one
    — which is what the decl uses (matches mathlib's `Pi.instMetricSpace` sup-metric).
  - **domain**: standardly the unit cube `[0,1]^{D-1}` (this is baked into the definition
    of `Lip(D,M,L)`); occasionally a general box. The decl hardcodes `[0,1]^{d-1}`.
  - **dimension of the chart domain**: standardly `D-1` (boundary of a `D`-body); but the
    kernel argument works for **any** domain dimension `k` (cube `[0,1]^k` → `O(n^k)`
    cells). The decl hardcodes `k = Fintype.card ι - 1`.
  - **codomain**: `ℝ^D`. The kernel works for any finite-dimensional sup-normed space; the
    `ZLattice`/general-lattice version is a further (CHEAP-MODERATE) generalisation.

Disagreement with the literature: **none** — the decl is a faithful, correctly-constanted
instance of the standard kernel.

---

### Generality analysis — `Chebotarev.ncard_index_image_chart_le`

Literature-standard form (from Phase 3): per-chart cell count for an `M`-Lipschitz map of
a cube `[0,1]^k` into a finite-dimensional normed space, against the `(1/n)`-grid, giving
`O(n^k)` cells with an explicit `(2⌈M⌉+1)`-type constant.

| # | Parameter / hypothesis                | Current Lean form                         | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|-------------------------------------------|------------------------------------------|---------------------|------------------------------------|
| 1 | chart domain dim `Fintype.card ι - 1` | hardcoded `d-1` (boundary of a `d`-body)  | any cube dimension `k`                    | **yes**             | the proof never uses `= d-1`; `Fin k → ℝ` works verbatim. Generalising to a free `κ : Type* [Fintype κ]` (or `k : ℕ`) gives `O(n^{#κ})` and is **CHEAP** (mechanical) |
| 2 | domain `Set.Icc 0 1`                  | unit cube `[0,1]^{d-1}`                    | unit cube (standard) / general box        | yes (minor)         | proof uses `IsBounded (Icc 0 1)` + the quantiser fibres; a general `Icc a b` works but the side-count constant changes. **MODERATE**; low value — the unit cube is the literature standard, keep it |
| 3 | codomain `ι → ℝ` (sup-metric)         | `Fintype`-indexed `ℝ^d`, ℓ^∞             | finite-dim normed space, any norm          | yes                 | `index`/`box`/`diam_boxIcc` are defined for `ι → ℝ` in mathlib; the ℓ^∞ choice is *forced* by the `unitPartition` API, not by the decl. Genuinely more general (normed-space / `ZLattice`) is **EXPENSIVE** (needs a different cell structure). Out of scope for a first PR |
| 4 | `[Fintype ι]`                         | finite coordinate set                      | finite-dim (= `Fintype` here)              | NO                  | the sup-metric on `ι → ℝ` and the finite cell count both require finiteness — essential |
| 5 | `(hn : 1 ≤ n)`                        | `n ≥ 1`                                    | `n ≥ 1`                                    | NO                  | `n = 0` collapses the grid; `(n+1)^{d-1}` / `NeZero n` need it — essential and standard |
| 6 | `M : ℝ≥0`, free parameter             | free Lipschitz constant                    | free `L` (standard)                        | —                   | already maximally general; matches literature exactly |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (one CHEAP weakening that the
proof fully supports: the chart-domain dimension `d-1` → arbitrary `k`).
Number of weakening opportunities found: K = 1 cheap + 1 moderate-low-value + 1 expensive.

Proposed restatement (the CHEAP, high-value one — decouple the chart dimension from `d`):

```lean
theorem ncard_index_image_cube_le {ι κ : Type*} [Fintype ι] [Fintype κ] {M : ℝ≥0}
    {φ : (κ → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) :
    (index n '' (φ '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ Fintype.card κ
```

The original is then the `κ := Fin (Fintype.card ι - 1)` specialisation (a one-line
corollary), which is exactly what `ncard_index_image_frontier_le` needs.

Cost of restatement: **CHEAP** — the proof body is dimension-agnostic; replace
`Fin (Fintype.card ι - 1)` by `κ` throughout and `(Fintype.card ι - 1)` by
`Fintype.card κ` in the bound and the `Pi.card_Icc`/`Finset.Icc` count. No new ideas.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses?                                                              | no       | already typeclass-driven (`Fintype`, `LipschitzWith`) | — |
|  2 | sequences/metric → filters/topological?                                                      | no       | finite combinatorial count; no limit to filter-ise | — |
|  3 | construct an object → universal-property class?                                              | no       | it's an inequality, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                           | no       | no algebraic substructure here | — |
|  5 | vector-space/metric-specific → weaken typeclasses?                                            | **yes**  | codomain `ι → ℝ` → finite-dim normed space / `ZLattice` (row 3 above) | would let the whole `unitPartition` effective-count API run over arbitrary lattices, matching `Mathlib/Algebra/Module/ZLattice/Covolume.lean` | 
|  6 | 1-categorical → higher-categorical?                                                          | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → general additive structure?                                          | **yes (light)** | the chart-domain index type `Fin (d-1)` → arbitrary `Fintype κ` (row 1) | decouples the kernel from "boundary of a `d`-body"; reusable for any-codimension counting |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild, and it coincides with the Phase-4b CHEAP weakening)**.
  - Proposed mathlib-idiomatic restatement: the `{κ : Type*} [Fintype κ]` form above
    (row 1 / row 7). The `ZLattice`-codomain form (row 5) is a real but **EXPENSIVE**
    further modernisation, best deferred to a follow-up PR — it needs the cell structure
    redone for a general lattice, which `unitPartition` does not yet support.
  - Cost: CHEAP for the `κ`-generalisation; EXPENSIVE for the lattice-codomain one.
  - Mathlib downstream this enables: a dimension-agnostic per-chart cell count usable for
    any-codimension lattice-point boundary estimates, not just `∂`(d-body); composes with
    the existing `BoxIntegral.unitPartition` `index`/`box`/`diam_boxIcc` API.
  - Real mathematical improvement: yes — the `d-1` is an artifact of the *application*
    (frontier of a body), not of the *lemma*; removing it gives the genuine kernel.

→ Phase 4c "modern idiom available" + Phase 4b "STRICTLY NARROWER" both point at the same
`κ`-generalisation ⇒ verdict bucket is **YES-but-generalise-first** (not YES-add-as-is).

---

### Diamond / defeq risk — (Phase 4.5)

**n/a — declaration kind is `theorem`.** (Theorems introduce no definitional equalities or
typeclass-search paths.)

---

### Mathlib search-status: `Chebotarev.ncard_index_image_chart_le`

[A] Lean-Finder       (no Lean-Finder MCP surfaced in this env)             n/a: tool unavailable
[B] Loogle            (no Loogle MCP surfaced; ToolSearch returned none)    n/a: tool unavailable — substituted with structural grep over the full mathlib `UnitPartition` + `Lipschitz` API
[C] LeanSearch        (no LeanSearch MCP surfaced)                          n/a: tool unavailable
[D] Grep mathlib src  `ncard.*index`, `index.*ncard`, `ncard.*Lipschitz`, `Lipschitz.*ncard`, `_image_le_of_diam`, `cells`/`diam`/`box`/`grid` cell-count, `effective.*lattice`, full `Analysis/BoxIntegral/UnitPartition.lean` theorem list | **no hit** for any cell-count/effective bound. `index`+`ncard` only co-occur in `GroupTheory/Index.lean` & `GroupTheory/Complement.lean` (subgroup index — unrelated). `LipschitzWith.diam_image_le` / `isBounded_image` exist (the proof's building blocks) but no packaged cell count |
[E] Name pattern      `index_image`, `image_index`, `_chart_`, `chart_le`, `effective.*count` | **no hit** (only `mem_chart_source` etc. in `Geometry/Manifold` — unrelated) |

Searched for both:
  - the user's current form (per-chart `O(n^{d-1})` cell count) — **not in mathlib**.
  - the literature-standard form (per-chart `O(n^k)` cell count; whole-boundary
    `O(n^{d-1})` count; effective lattice count with error rate) — **not in mathlib**.

What mathlib DOES have nearby (all in `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`):
  - `BoxIntegral.unitPartition.index n x i = ⌈n·xᵢ⌉ - 1` (the cell-index map this decl uses)
  - `box`, `diam_boxIcc`, `volume_box`, `setFinite_index` (the cell geometry; `setFinite_index`
    is the qualitative "finitely many cells meet a finite-volume set" — **no quantitative bound**)
  - `tendsto_card_div_pow_atTop_volume`, `tendsto_card_div_pow_atTop_volume'`,
    `tendsto_tsum_div_pow_atTop_integral` — the **qualitative** lattice-count limits, with
    **no error term / no rate**. This decl is exactly the *effective* strengthening these lack.
  - `LipschitzWith.diam_image_le`, `LipschitzWith.isBounded_image` (`Mathlib/Topology/
    MetricSpace/Lipschitz.lean`) — the Lipschitz→diameter building block.

Concluded: **not in mathlib** (grep five-method exhausted, plus the literature-standard
form, plus the more-general `κ`-form). Mathlib has the *qualitative* limit and the
*building blocks* but not the *effective cell-count kernel*.

---

### Call sites — `Chebotarev.ncard_index_image_chart_le`

Internal use count: **K = 1** (within the project, excluding the declaring line).
External-to-file callers: 0 *uses* (1 file mentions it in a docstring).

| Caller file:line                          | Usage pattern (one-line excerpt)                                          |
|-------------------------------------------|---------------------------------------------------------------------------|
| ForMathlib/LatticePointCount.lean:221     | `(Finset.sum_le_sum fun j _ ↦ ncard_index_image_chart_le (hφ j) hn).trans` — summed over the `m` charts covering `∂s` to prove the whole-boundary bound `ncard_index_image_frontier_le` |
| ForMathlib/IdealCongruenceCount.lean:121  | docstring only: "...chart core of `LatticePointCount`'s `ncard_index_image_chart_le` adapted to count the *unit* grid..." — the **same argument is re-derived there** for the unit grid |

Inline-derivation grep: the `IdealCongruenceCount.lean` reference indicates the chart-core
argument is **re-implemented** (adapted) elsewhere in the project — a positive
composability signal: the kernel is reusable infrastructure, not a one-off. It is used
once directly and once by adaptation.

What the pattern tells us: K = 1 direct use *plus* one adaptation elsewhere. This is the
designated single consumer (`ncard_index_image_frontier_le`) — appropriate for a kernel
lemma that exists to be summed. Combined with "not in mathlib + standard named principle",
this is an API-building signal, not a wrong-abstraction signal. The re-derivation in
`IdealCongruenceCount` is itself evidence the general (`κ`-)form would be reused.

---

### Composition check (Phase 6)

Can `ncard_index_image_chart_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: `LipschitzWith.diam_image_le` (φ-image has small diameter) then some mathlib
"diameter → cell count" lemma then sum.
  - Mathlib decls used: `LipschitzWith.diam_image_le`, `BoxIntegral.unitPartition.index`, …
  - Result: **fails**. The crucial middle step — "a set of diameter ≤ r meets ≤ (2⌈nr⌉+1)^d
    cells of the `(1/n)`-grid" — is the sibling lemma `ncard_index_image_le_of_diam_le`,
    which is itself a ~30-line proof in this same file and is **not in mathlib**. Without it
    there is no composition.

Attempt 2: cover-and-sum directly.
  - The proof partitions `[0,1]^{d-1}` into `(n+1)^{d-1}` quantiser fibres, bounds each
    fibre's diameter via `abs_sub_le_one_div_of_ceil_natCast_mul_eq` (a private helper,
    not in mathlib), pushes through φ, applies `ncard_index_image_le_of_diam_le`, and sums
    via `Finset.set_ncard_biUnion_le`. This is a genuine ~55-line multi-`have` proof with
    real reasoning between steps — **not** a `.symm`/`.trans`/single-call composition.

Conclusion: **NOT-COMPOSABLE.** The decl rests on two project-local lemmas
(`ncard_index_image_le_of_diam_le`, `abs_sub_le_one_div_of_ceil_natCast_mul_eq`) that are
themselves not in mathlib, plus a cover-and-sum argument. No ≤3-call mathlib composition
exists.

---

## Verdict: `Chebotarev.ncard_index_image_chart_le`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): the **Principle of Lipschitz / Davenport's Lemma**; this is
  its per-chart cell-count kernel. Standard form identified across ≥5 WebSearch channels +
  the project's own Lang / Gun–Ramaré–Sivaraman citations. The decl is a faithful instance
  but **narrower** than the kernel (domain dimension hardcoded to `d-1`).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — one CHEAP weakening
  (chart-domain dimension `d-1` → arbitrary `Fintype κ`) that the proof fully supports;
  Phase 4c flags the same generalisation as a real modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib** under any form; mathlib has only the
  *qualitative* `tendsto_card_div_pow_atTop_volume` (no error rate) and the building blocks.
- Composition check (Phase 6): **NOT-COMPOSABLE** (rests on two non-mathlib project lemmas
  + a ~55-line cover-and-sum).

**Rationale:**

This is the effective (power-saving, `O(n^{d-1})`) kernel that mathlib's
`tendsto_card_div_pow_atTop_volume` conspicuously lacks: that theorem gives the lattice-
count limit with **no rate**, and the module docstring correctly frames this file as the
effective strengthening "stated here for a future mathlib contribution". The content is the
classical Principle of Lipschitz (Davenport 1951; Lang GTM 110 Ch.VI Thm 3; Masser–Vaaler;
Widmer; Debaene), whose mechanism — *a Lipschitz map sends a domain cube into a codomain
cube* — is exactly this proof. Mathlib does not have it (the only `index`/`ncard`
co-occurrences are the unrelated subgroup index), and it is not a short composition (it
depends on two further non-mathlib lemmas in the same file). So it is a genuine, well-
generalised, non-trivial addition — **but** the statement hardcodes the chart-domain
dimension to `Fintype.card ι - 1`, an artifact of the *application* (it is summed over the
charts of a frontier `∂s`) rather than of the *lemma*. The proof never uses `= d-1`, so the
honest kernel is the `{κ : Type*} [Fintype κ]`-domain form giving `O(n^{#κ})`, with the
current statement a one-line `κ := Fin (d-1)` corollary. Per the verdict gate (Phase 4b =
STRICTLY NARROWER, Phase 4c = real modern-idiom improvement), that mandates
**YES-but-generalise-first** rather than YES-add-as-is.

The right grain for a mathlib PR is the whole `LatticePointCount.lean` cluster shipped
together — `ncard_index_image_le_of_diam_le` (the diameter→cell-count step),
`setFinite_index_image_of_isBounded`, this chart kernel, and the whole-boundary
`ncard_index_image_frontier_le` — since the kernel is useless in mathlib without its
siblings and its sole consumer. Generalise the chart dimension first (cheap), optionally
flag the `ZLattice`-codomain generalisation (expensive) as a TODO, then PR the cluster into
`Mathlib/Analysis/BoxIntegral/UnitPartition.lean` (or a new `…/UnitPartition/Effective.lean`).

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the chart-domain dimension hardcoded to `d-1`,
    strictly narrower than the literature kernel (arbitrary cube dimension).
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c row 1/7 — decouple the chart index type from the
    ambient dimension (`Fin (d-1)` → `Fintype κ`), the genuine reusable kernel.

**Proposed restatement:**
```lean
theorem ncard_index_image_cube_le {ι κ : Type*} [Fintype ι] [Fintype κ] {M : ℝ≥0}
    {φ : (κ → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) :
    (index n '' (φ '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ Fintype.card κ := by
  sorry -- current proof survives verbatim with Fin (Fintype.card ι - 1) ↦ κ
```
Estimated cost of regeneralisation: **CHEAP** (mechanical; the proof is dimension-agnostic).
Note: EXPENSIVE does not downgrade the verdict — but here it is not even expensive.

Mathlib downstream this enables:
  - A dimension-agnostic per-chart cell count: any-codimension lattice-point boundary
    estimates, not only frontiers of `d`-bodies.
  - Composes with the existing `BoxIntegral.unitPartition` `index`/`box`/`diam_boxIcc`/
    `setFinite_index` API and supplies the **effective** companion to the qualitative
    `tendsto_card_div_pow_atTop_volume`.
  - The re-derived "unit-grid" variant in `IdealCongruenceCount.lean` would then reuse the
    one general lemma instead of re-proving it.

Next action: run `/generalise Chebotarev.ncard_index_image_chart_le` (tension against the
Principle-of-Lipschitz kernel form from Phase 3 and the `κ`-domain modern-idiom form from
Phase 4c), then `/cleanup` the cluster, then open the mathlib PR grouping the four
`LatticePointCount.lean` results together.

---

## Next step

Run `/generalise Chebotarev.ncard_index_image_chart_le` to restate with an arbitrary
`Fintype κ` chart domain (cheap; proof survives), keeping the current statement as a
`κ := Fin (Fintype.card ι - 1)` corollary; then `/cleanup` and PR the
`LatticePointCount.lean` cluster (`ncard_index_image_le_of_diam_le`,
`setFinite_index_image_of_isBounded`, the chart kernel, `ncard_index_image_frontier_le`)
into `Mathlib/Analysis/BoxIntegral/UnitPartition`.
