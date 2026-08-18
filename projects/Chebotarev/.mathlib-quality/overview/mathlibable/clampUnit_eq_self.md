# /mathlibable report — `Chebotarev.clampUnit_eq_self`

### Baseline (Phase 0)
- lake build:               (assumed clean per project; not re-run — stale local build, reasoned from source)
- decl `Chebotarev.clampUnit_eq_self`:  ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:94`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` —
  finitely many Lipschitz images of the unit cube `[0,1]^{r-1}` covering the `realSpace`
  frontier (Gun–Ramaré–Sivaraman §3.3 boundary-cell input). `clampUnit` is the 1-Lipschitz
  cube clamp used to globalise the face parametrizations.

---

### Statement (Phase 1)

`clampUnit_eq_self` states: the coordinatewise clamp of a function `c : ι → ℝ` onto the unit
cube `[0,1]` is the identity whenever `c` already lies in the cube. In symbols, with
`clampUnit ι c i = projIcc 0 1 (c i)` (clamp each coordinate to `[0,1]`), if
`c ∈ Icc (0 : ι → ℝ) 1` (equivalently `0 ≤ c i ≤ 1` for every `i`) then `clampUnit ι c = c`.

This is the elementary **fixed-point property of a retraction**: a coordinatewise retraction
onto a box restricts to the identity on the box. Pointwise it is exactly "the projection of
`ℝ` onto `[0,1]` fixes points already in `[0,1]`".

Variables / typeclasses involved (Lean side):
- `{ι : Type*}` — an arbitrary index type (no `Fintype` needed here; finiteness is only used
  by the *Lipschitz* lemma `lipschitzWith_clampUnit`, not by this identity).
- `{c : ι → ℝ}` — the point of the function space.

Hypotheses (Lean side):
- `(hc : c ∈ Icc (0 : ι → ℝ) 1)` — `c` lies in the closed unit cube (componentwise `0 ≤ c ≤ 1`).

Conclusion (math): the retraction `clampUnit ι` fixes `c`.
Conclusion (Lean): `clampUnit ι c = c`.

Proof body (verbatim):
`funext fun i ↦ congrArg _ (Set.projIcc_of_mem _ ⟨hc.1 i, hc.2 i⟩)`
— pointwise `funext`, then push the cube membership through mathlib's `Set.projIcc_of_mem`
and take the coercion with `congrArg`. Two mathlib calls; no new content.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma about a project-local one-line `def` (`clampUnit`); not a named theorem,
not a `## Main results` entry, introduces no new structure. (Lit width was exhaustive regardless.)

### One-line check (Phase 2b)

The declaration is a `theorem`, not a `def` — the one-line *definition* check is n/a.

Context note that matters for the verdict: the lemma is *about* the project-local def
`clampUnit` (`NormLeOneLipschitz.lean:88`), which **is** a one-liner:
`def clampUnit (ι) (c) := fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)`.
That def is not `@[reducible]`, has **zero uses outside its declaring file**, and exists purely
as private scaffolding for the frontier-cover construction. So any "ship to mathlib" story for
`clampUnit_eq_self` would first have to ship `clampUnit` — a one-liner with no exemption (no
defeq-barrier need, no diamond, no external API consumer). This biases the verdict toward NO.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | clamp function to interval retraction "projIcc" mathlib pointwise idempotent on box           | yes  | coordinatewise clamp `R(x)_i = min(b_i, max(a_i, x_i))`; identity on the box | Wikipedia *Clamp (function)*; confirms `R(x)=x` for `x` in the box |
|  2 | WebSearch (general form)         | retraction onto unit cube coordinatewise clamp identity on the cube projection Icc            | yes  | product of per-coordinate clamps; "if `x` already in the cube then `R(x)=x`" | arXiv *A representation of retracts of cubes* (math/0407196); standard |
|  3 | WebSearch (named-after / aliases)| nLab retract idempotent fixed points "retraction" restricts to identity on the subspace        | yes  | retraction `r: X→X`, `r∘i = id_A`: a retraction restricts to the identity on its image | nLab *retract*; Topospaces *Retract* — the abstract fixed-point property |
|  4 | ChatGPT MCP                      | (asked for the most general standard form + whether this is just `funext`+`projIcc_of_mem`)     | n/a  | —                                                                | Codex backend errored out (known-flaky per task note); covered by #1–#3 + mathlib source |
|  5 | Local references                 | `ls projects/Chebotarev/.mathlib-quality/references/`                                           | n/a  | —                                                                | No source-paper PDFs bear on a clamp-identity triviality; the GRS/Lang refs concern the boundary-cell *count*, not this helper |
|  6 | nLab                             | retract / retraction                                                                            | yes  | `r∘i = id_A` (retraction is identity on the retract)            | exactly the abstract statement; our lemma is the `ℝ^ι`-cube instance |
|  7 | nCatLab (if categorical)         | —                                                                                              | n/a  | —                                                                | not a categorical concept beyond the nLab *retract* page already covered |
|  8 | Stacks Project (if alg geom)     | —                                                                                              | n/a  | —                                                                | not an algebraic-geometry concept |
|  9 | MathOverflow / Math.StackExchange| (folded into #1/#2 web sweep)                                                                   | n/a  | —                                                                | a clamp-fixes-the-box-points fact is too elementary to have a dedicated MO thread; web hits suffice |
| 10 | recent arXiv (last 5 years)      | (covered by #1 *prox-regular sweeping* + #2 *retracts of cubes*)                                | yes  | coordinatewise clamp is 1-Lipschitz and fixes the box           | the property is treated as folklore in the optimisation / variational literature |

### Literature summary (Phase 3)

Concept identified as: **coordinatewise clamp / projection onto a box** (a.k.a. nearest-point
retraction onto `[0,1]^ι`); the lemma is its **fixed-point / identity-on-the-retract** property.
Sources agree on the standard form: **yes** — every channel states "a retraction is the identity
on its image", and the box-clamp is the canonical concrete retraction.
Most general standard form: for a retraction `r : X → X` onto `A`, `r|_A = id_A`. Concretely,
projection onto a closed interval (or product of intervals) is the identity on that interval.
Generality dimensions where the literature varies:
  - codomain: single interval → finite product → arbitrary closed convex set (nearest-point
    projection in a Hilbert space). The most general is "metric projection onto a closed convex
    set is the identity on the set", but that is a *different* lemma about a *different* object.
  - index: finite / arbitrary product — the identity-on-the-box statement holds for any index set.
Disagreement with the literature: **none**. The Lean form is the literal `[0,1]^ι` instance of
the universally-agreed "retraction fixes its image" fact.

---

### Generality analysis — `Chebotarev.clampUnit_eq_self`

Literature-standard form (from Phase 3): "a retraction onto `A` is the identity on `A`";
concretely "projection onto `[a,b]` (per coordinate) fixes points already in the box".

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|--------------------------------------------|---------------------|----------------------------------|
| 1 | `{ι : Type*}`                     | arbitrary index                    | any index set                              | already maximal     | no `Fintype` assumed; cannot weaken further |
| 2 | codomain `ℝ`                      | real coordinates, interval `[0,1]` | any conditionally-complete lattice / `LinearOrder` with `projIcc` | YES                 | mathlib's `Set.projIcc_of_mem` is already stated for `[a,b]` in any `[Preorder]`/`LinearOrder`; the `[0,1]/ℝ` specialisation is strictly narrower |
| 3 | bounds `0` and `1`                | fixed unit cube                    | arbitrary `a ≤ b`                          | YES                 | `Set.projIcc_of_mem` takes general `a b h`; the unit-cube pinning is a specialisation |
| 4 | "applied pointwise" (the pi-lift) | `funext` over `ι → ℝ`              | retraction on a product = product of retractions | already standard    | the pi-lift is the only "extra" over the scalar lemma, and it is one `funext` |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (pinned to `ℝ`, to bounds `0,1`, and
to the named project def `clampUnit`), **but this does not push toward YES-but-generalise-first**
— the maximally general scalar statement is *already in mathlib* as `Set.projIcc_of_mem`
(general `a b`, general order). What is narrow here is not a *missing* general lemma but the
project's deliberate specialisation-plus-pi-wrapper for one use. The pi-lift adds no general
content worth a mathlib lemma; it is one `funext`.
Number of weakening opportunities found: 2 (bounds, order generality) — **all already realised
in mathlib's `Set.projIcc_of_mem`**.
Proposed restatement: none worth shipping. The general scalar fact exists; a `Pi.projIcc_of_mem`
("projection onto a box is the identity on the box, pointwise") would be the only conceivable
mathlib addition, and even that is a one-`funext` corollary that the codebase shows is trivially
inlined.
Cost of restatement: CHEAP (but moot — see Phase 6).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                            | no       | —                      | nothing; it's a plain equality of functions |
|  2 | sequences/metric → filters/topology?                                                       | no       | —                      | no limiting process here |
|  3 | construction → universal-property class?                                                   | no       | —                      | clamp is a concrete formula, not a universal object |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | —                      | no substructure involved |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                      | partial  | state per-coordinate over any `LinearOrder`/lattice with `projIcc` | this is exactly what `Set.projIcc_of_mem` already does — no new decl needed |
|  6 | 1-categorical → higher-categorical?                                                         | no       | —                      | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                              | no       | the index `ι` is already arbitrary | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (net-new). The only "modernisation" (row 5) is to weaken the
order/bounds — and mathlib has *already done it* in `Set.projIcc_of_mem`. There is no
contemporary reformulation of `clampUnit_eq_self` that adds organisational value; it is a
specialised `funext` wrapper.
One-line reason this is not a modernisation move: the general, idiomatic statement already
lives in mathlib (`Set.projIcc_of_mem`); the project lemma is a downstream one-liner.

---

### Diamond / defeq risk — `Chebotarev.clampUnit_eq_self`

n/a — declaration kind is `theorem` (introduces no definitional equalities or instance-search
paths). (The associated `def clampUnit` would carry the usual one-liner reducibility question,
but it is sealed (non-`@[reducible]`) and unused outside its file, so even that is LOW and moot.)

---

### Mathlib search-status: `Chebotarev.clampUnit_eq_self`

[A] Lean-Finder       "projection onto interval is identity on the interval" / "clamp fixes points in the box" — not separately reachable (stale local index); covered by [D]/[E]
[B] Loogle            `Set.projIcc _ _ _ ?x = _` with `?x ∈ Set.Icc`; `?f ∈ Set.Icc 0 1 → _ = ?f` — hits the scalar lemma family in `Mathlib.Order.Interval.Set.ProjIcc`
[C] LeanSearch        "projection onto Icc of a point in Icc equals it"; "coordinatewise clamp is identity on the cube" — surfaces `Set.projIcc_of_mem`, `Set.projIcc_val`
[D] Grep mathlib src  `projIcc_of_mem`, `projIcc_val`, `IccExtend_of_mem`, `Pi.*projIcc`, `clampUnit` — **hits** `Set.projIcc_of_mem` (`ProjIcc.lean:100`), `Set.projIcc_val` (:110), `Set.IccExtend_of_mem` (:222); **no** `clampUnit`, **no** pi-level `projIcc` fixed-point lemma
[E] Name pattern      `clampUnit`, `projIcc.*self`, `projIcc.*pi` over mathlib — no project-name collision; no pi version exists

Searched for both:
  - the user's current form (pi-clamp fixes cube points) — **not in mathlib**
  - the literature-standard / scalar form (`projIcc` fixes interval points) — **in mathlib** as
    `Set.projIcc_of_mem` (and `Set.projIcc_val` for the bundled `Icc a b → …` variant)

Concluded: **found building blocks** — `Set.projIcc_of_mem`
(`Mathlib/Order/Interval/Set/ProjIcc.lean:100`,
`theorem projIcc_of_mem (hx : x ∈ Icc a b) : projIcc a b h x = ⟨x, hx⟩`) is the exact scalar
fact; the pi-version is a `funext` composition over it. The named pi-form is **not** in mathlib,
and does not need to be.

---

### Call sites — `Chebotarev.clampUnit_eq_self`

Internal use count: **2** (within the same project, NOT counting the *declaration line*), and
**both are inside the declaring file** (`NormLeOneLipschitz.lean`). External-to-file callers: **0**.

| Caller file:line                         | Usage pattern (one-line excerpt)                          |
|------------------------------------------|-----------------------------------------------------------|
| NormLeOneLipschitz.lean:325              | `rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]`       |
| NormLeOneLipschitz.lean:337              | `rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]`       |
| NormLeOneLipschitz.lean:312 (docstring)  | mention only, not a call                                  |

Associated def `clampUnit`: **0 uses outside `NormLeOneLipschitz.lean`** across the whole repo.

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — the only consumers are the two `rw`s above; no other file re-derives "clamp fixes
    cube points". The fact is otherwise just `Set.projIcc_of_mem` used directly.

Call-sites signal: both uses are file-internal and identical (`rw` to discharge the clamp inside
`frontier_subset_frontierCoverFamily`). This is a private convenience wrapper, not shared API —
points to NO-composable (or, since it's bound to a local def, fold into the def's own story).

---

### Composition check (Phase 6)

Can `clampUnit_eq_self` be derived from mathlib in ≤3 chained calls? **Yes — it already is.**

Attempt 1 (the actual proof in the file):
`funext fun i ↦ congrArg _ (Set.projIcc_of_mem _ ⟨hc.1 i, hc.2 i⟩)`
  - Mathlib decls used: `funext`, `congrArg`, `Set.projIcc_of_mem`.
  - Result: **succeeds** (this is the verbatim project proof — 2 mathlib lemmas + `funext`).
  - Notes: `Set.projIcc_of_mem` gives `projIcc 0 1 _ (c i) = ⟨c i, _⟩` in the subtype; `congrArg (↑·)`
    drops to the coercion `= c i`; `funext` lifts over `ι`. No `simp`, no `ring`, no real reasoning.

Conclusion: **COMPOSABLE** (≤3 calls; this is literally how it is proved). The lemma is a thin
`funext` wrapper over `Set.projIcc_of_mem`; consumers can inline `Set.projIcc_of_mem` directly
(or keep the helper as a *private* lemma, but it is not mathlib-worthy on its own).

---

## Verdict: `Chebotarev.clampUnit_eq_self`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the statement is the textbook "a retraction is the identity on
  its image", concretely "projection onto `[0,1]` fixes points in `[0,1]`" — folklore, agreed
  across Wikipedia/nLab/Topospaces/arXiv.
- Generality analysis (Phase 4): STRICTLY NARROWER than the standard scalar form, but the general
  scalar form is *already in mathlib*; the pi-lift adds no general content (one `funext`). No
  modern-idiom upgrade.
- Mathlib search (Phase 5): building blocks present — `Set.projIcc_of_mem`
  (`Mathlib/Order/Interval/Set/ProjIcc.lean:100`); named pi-form absent and unneeded.
- Composition check (Phase 6): COMPOSABLE — the file's own proof is `funext` +
  `congrArg` + `Set.projIcc_of_mem` (≤3 calls).

**Rationale:**

`clampUnit_eq_self` is the `[0,1]^ι` instance of the most elementary fact about retractions —
a clamp onto a box fixes the points already in the box — and mathlib already ships the load-
bearing scalar lemma `Set.projIcc_of_mem`. The project's proof *is* the composition: one
`funext` over the index, then `Set.projIcc_of_mem` (with `congrArg` to drop the subtype
coercion). There is no new mathematical content, no missing general lemma (the general bounds
and general order are already covered by `Set.projIcc_of_mem`), and no modernisation angle. On
top of that, the lemma is about a **project-private one-line def** `clampUnit` that is sealed,
unexported, and used at exactly two identical internal `rw` sites — so it is not even a candidate
to add "as is" without first upstreaming `clampUnit`, itself an unexemptioned one-liner. The
correct disposition is to keep it as a local helper (or inline it); it does not belong in mathlib.

**WHY not (refactor-actionable):**
Mathlib has the building block `Set.projIcc_of_mem` and the result is a ≤3-call composition over
it. The pi-version is a `funext` away and the codebase already writes it inline in the proof
body. No new lemma is warranted; consumers either keep the private helper or expand it.

Mathlib building blocks:
- `Set.projIcc_of_mem` — `Mathlib/Order/Interval/Set/ProjIcc.lean:100`
  (`theorem projIcc_of_mem (hx : x ∈ Set.Icc a b) : projIcc a b h x = ⟨x, hx⟩`)
- `funext`, `congrArg` (core)
- (related, for the bundled variant: `Set.projIcc_val`, `Mathlib/Order/Interval/Set/ProjIcc.lean:110`)

Composition sketch (≤3 lines) — the exact project proof:
```lean
example {ι : Type*} {c : ι → ℝ} (hc : c ∈ Set.Icc (0 : ι → ℝ) 1) :
    (fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)) = c :=
  funext fun i ↦ congrArg _ (Set.projIcc_of_mem _ ⟨hc.1 i, hc.2 i⟩)
```

Call sites in our project (from Phase 6.0): **2** (both in `NormLeOneLipschitz.lean`, lines
325 and 337; 0 external).

Refactor plan: this is a **ForMathlib/ helper that should NOT be upstreamed as a standalone
lemma**. Two equivalent dispositions, both leaving `main` green:
1. **Keep local** (recommended, lowest churn): keep `clampUnit` and `clampUnit_eq_self` as
   private project scaffolding (consider marking both `private`, since `clampUnit` has no
   external use and the lemma has no external use). No mathlib PR.
2. **Inline**: delete `clampUnit_eq_self`; at lines 325 and 337 replace
   `rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]` with a direct rewrite via
   `Set.projIcc_of_mem` (componentwise), e.g. unfold `clampUnit` and `simp only [...]` /
   `funext` + `Set.projIcc_of_mem`. Since `clampUnit` itself is only used to define the cover
   family and is 0-used elsewhere, the inline is mechanical.

Next action: do **not** open a mathlib PR for this lemma (nor for `clampUnit`). Treat it as a
local helper — optionally privatise it. If anything from this file is upstream-worthy, it is the
*other* results (e.g. the generic `exists_lipschitzWith_comp_clampUnit` /
`lipschitzWith_one_of_edist_apply_le` pattern), assessed separately — not this clamp-identity.
