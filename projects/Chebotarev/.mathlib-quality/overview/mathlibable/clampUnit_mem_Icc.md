# /mathlibable report — `Chebotarev.clampUnit_mem_Icc`

## Baseline (Phase 0)
- lake build:               not re-run (env: local build stale per task brief); decl read directly from source
- decl `Chebotarev.clampUnit_mem_Icc`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:90`
- qualified name:           `Chebotarev.clampUnit_mem_Icc` (VERIFIED — `namespace Chebotarev` opens at line 79; decl at line 90; no nested namespace)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Lipschitz parametrization of the frontier of `normLeOne K` — a `ForMathlib/`
  helper file building the finite Lipschitz-image cover of the norm-≤-1 frontier for the effective lattice-point count.

Exact source:

```lean
/-- The coordinatewise retraction of `ι → ℝ` onto the unit cube `Set.Icc 0 1`, given by
`Set.projIcc` in each coordinate. -/
def clampUnit (ι : Type*) (c : ι → ℝ) : ι → ℝ := fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)

theorem clampUnit_mem_Icc (ι : Type*) (c : ι → ℝ) : clampUnit ι c ∈ Icc (0 : ι → ℝ) 1 :=
  ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1,
    fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩
```

---

## Statement (Phase 1)

`Chebotarev.clampUnit_mem_Icc` is a theorem stating the following:

The coordinatewise clamp of a real-valued function `c : ι → ℝ` onto the unit cube — `clampUnit ι c`,
which sends each coordinate `c i` to `Set.projIcc 0 1 _ (c i) = max 0 (min 1 (c i))` — lies in the
order interval (box) `Icc (0 : ι → ℝ) 1`. In ordinary mathematics: the nearest-point / clamp
retraction of a point onto the axis-aligned box `[0,1]^ι` lands in that box. This is membership in the
**pi-type** order interval, which is coordinatewise: `f ∈ Icc 0 1 ↔ ∀ i, 0 ≤ f i ∧ f i ≤ 1`.

Variables / typeclasses involved (Lean side):
- `ι : Type*` — an arbitrary index type (no finiteness, no order, nothing required).
- `c : ι → ℝ` — the point being clamped.

Hypotheses (Lean side): none beyond the data.

Conclusion (math): `clamp_{[0,1]}(c) ∈ [0,1]^ι` — the box-clamp lands in the box.
Conclusion (Lean): `clampUnit ι c ∈ Set.Icc (0 : ι → ℝ) 1`.

Proof body: `⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1, fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩`
— each coordinate's lower/upper bound is literally the bundled subtype-membership proof `.2.1` / `.2.2`
of `Set.projIcc`, which returns a term of `↥(Icc 0 1)`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper membership lemma about a project-local one-line `def`; not a named theorem, not a
`## Main results` entry (the file's main results are the three `normLeOne_frontier_lipschitz_cover*`
theorems), introduces no new structure.

## One-line check (Phase 2b)

Kind is `theorem`, not `def` — the one-liner def-check is n/a. (Note: the *parent* `clampUnit` itself
is a one-line `def`; the parent's mathlibability is its own question and is not the subject here. This
report assesses only the membership lemma.) The lemma's proof is a single bundled-pair term — a strong
"trivial composition" signal carried into Phase 6/7.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "projIcc Mathlib clamp interval retraction unit cube Lipschitz"                            | yes  | `projIcc` = clamp to `[a,b]`; the retraction sends `(-∞,a]→a`, `[b,∞)→b`, fixes `[a,b]` | leanprover-community mathlib4 docs + arXiv Lipschitz-retraction papers; membership in the box is the *definition* of the retraction's codomain |
| 2  | WebSearch (general form)         | "coordinatewise clamp retraction unit cube [0,1]^n nearest point projection box standard"  | yes  | `R(x)_i = min{b_i, max{a_i, x_i}}`; the coordinatewise box-clamp is the nearest-point projection onto an axis-aligned box, 1-Lipschitz in any ℓ_p | the projection landing in the box is the defining property; no name attached to "it lands in the box" |
| 3  | WebSearch (named-after / convex) | "metric projection onto box lands in box trivial property nearest point convex projection Icc" | yes  | metric projection onto a closed convex set (a box is one) is the unique nearest point *in the set*; landing in the set is by definition (Chebyshev set / projection theorem) | EPFL/CSUS lecture notes, projection theorem refs; "lands in the set" is never stated as a standalone named result — it is part of the definition of the projection |
| 4  | ChatGPT MCP                      | "is `clampUnit c ∈ Icc 0 1` a named result or trivial composition; shortest derivation; maximally general form" | ERRORED | n/a | MCP unavailable in this environment (codex stdin failure; task brief flagged the MCP as possibly down). Two attempts, both errored. Compensated by 3 WebSearch generality levels + direct mathlib-source reading. |
| 5  | Local references                 | grep `.mathlib-quality/references/` for "projIcc" / "clamp"                                | n/a  | (no references dir) | `projects/Chebotarev/.mathlib-quality/references/` is absent — recorded n/a |
| 6  | nLab                             | "nearest point projection box / retraction onto interval"                                 | n/a  | n/a | The membership fact is below nLab's granularity — it is the codomain of a definition, not a theorem nLab would carry an entry for. Recorded n/a with reason. |
| 7  | nCatLab                          | —                                                                                          | n/a  | n/a | Not a categorical concept. |
| 8  | Stacks Project                   | —                                                                                          | n/a  | n/a | Not an algebraic-geometry concept. |
| 9  | MathOverflow / Math.SE           | covered implicitly by WebSearch #2/#3 (closest-point-on-AABB, projection-onto-convex hits) | yes  | clamp each coordinate to its range; result is in the box by construction | the standard "closest point on an axis-aligned bounding box" recipe (gamedev/optimization folklore) — the box-membership is taken as obvious |
| 10 | recent arXiv (last 5 years)      | surfaced by WebSearch #1 (Lipschitz-free-space / Lipschitz-retraction papers, 2018–2023)  | yes  | retractions onto convex/box sets; range ⊆ target set by definition of "retraction onto" | confirms the operation is standard; the membership is structural, never a headline lemma |

### Literature summary (Phase 3)

Concept identified as: the **coordinatewise clamp** / **nearest-point (metric) projection onto an
axis-aligned box** `[0,1]^ι`; in Mathlib terms, the pi-lift of `Set.projIcc`.
Sources agree on the standard form: **yes** — `R(x)_i = min{1, max{0, x_i}}`, the closest point of the
box, universally.
Most general standard form: for any box `∏_i [a_i, b_i]` over any index set, the coordinatewise clamp
is the nearest-point projection and **lands in the box by construction** (the box is the codomain).
Generality dimensions where the literature varies:
  - index type: finite (ℝ^n, the usual statement) up to arbitrary (the membership fact needs no finiteness).
  - ambient order/metric: any ℓ_p / any product order (the membership fact is purely order-theoretic).
Disagreement with the literature: **none**. Crucially, "the box-clamp lands in the box" is **never a
named theorem** in any source — it is the *defining property* of the projection's codomain. The
literature's named results about this map are its **non-expansiveness / 1-Lipschitz property** (which
this file states separately as `lipschitzWith_clampUnit`), not its membership.

---

## Generality analysis — `Chebotarev.clampUnit_mem_Icc`

Literature-standard form (from Phase 3): the coordinatewise box-clamp lands in the box, for any index
set and any product order. Mathlib already realises the per-coordinate version *as a type*: `Set.projIcc`
returns `↥(Set.Icc a b)`, so the membership is bundled into its codomain.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `ι : Type*`            | arbitrary index type     | arbitrary index set               | NO (already maximal) | no finiteness/order assumed — already the most general index |
| 2 | codomain `ℝ`          | the reals                | any conditionally-complete / lattice-ordered carrier with `projIcc` | yes (in principle) | `Set.projIcc` is defined for any `[LinearOrder α]` (in fact any structure with `max`/`min` + the order facts); the unit-cube `0`/`1` are ℝ-specific but the statement form generalises to `Icc a b` over any `LinearOrder` |
| 3 | bounds `0`, `1`       | the unit cube            | any box `[a,b]^ι`                 | yes                 | nothing uses `0`/`1` specifically; `projIcc a b h` works for any `a ≤ b` |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (specialised to ℝ and to the unit cube `[0,1]`),
**but** this narrowing is irrelevant to the verdict because the statement is **subsumed by mathlib
primitives at every generality level** (see Phase 5/6). Generalising it would just produce a *more
general trivial lemma* that is *still* a one-projection composition — it does not convert a NO into a YES.
Number of weakening opportunities found: 2 (codomain, bounds) — both cosmetic.
Cost of restatement: CHEAP — but moot, since the lemma should not exist in mathlib in any form.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | bundled hypotheses → typeclasses? | no | — | already typeclass-free |
| 2  | sequences/metric → filters/topology? | no | — | purely an order-membership fact; no limits |
| 3  | construction → universal property? | no | — | nothing to characterise universally |
| 4  | set-with-predicate → bundled substructure? | **partially** | the membership is *already* bundled in mathlib: `Set.projIcc` returns `↥(Set.Icc a b)`, so the codomain *is* the bundled box | this is the decisive point — mathlib's idiom already carries the membership in the **type** of `projIcc`; restating it as a loose `∈ Icc` proposition is the *less* idiomatic direction |
| 5  | field/metric-specific → weaker typeclass? | yes (cosmetic) | `Icc a b` over any `LinearOrder` | full `projIcc` API already lives at that generality |
| 6  | 1-categorical → higher-categorical? | no | — | n/a |
| 7  | concrete index (ℝ) → arbitrary structure? | yes (cosmetic) | already arbitrary in `ι`; only the carrier ℝ is concrete | minor |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, and it points AWAY from a named lemma.** The mathlib-idiomatic encoding of
"the clamp lands in the box" is *already in the library*: `Set.projIcc` is valued in the bundled subtype
`↥(Set.Icc a b)`, so per coordinate the membership is `Subtype.coe_prop`, and across the pi type it is the
coordinatewise unfolding `Set.mem_Icc` + `Pi.le_def`. The contemporary move is to **use the bundled
codomain**, not to introduce a loose membership proposition. Real mathematical improvement: none — this is
a structural triviality already captured by mathlib's types.

---

## Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (introduces no definitional equality or typeclass-search path).

---

## Mathlib search-status: `Chebotarev.clampUnit_mem_Icc`

[A] Lean-Finder        — natural-language "clamp lands in box / projIcc mem Icc"   n/a: AI index not reachable in this sandbox (recorded n/a; compensated by exhaustive grep of the full mathlib tree, Method D, which is authoritative here)
[B] Loogle             `Set.projIcc _ _ _ _ ∈ Set.Icc _ _` ; `_ ∈ Set.Icc (0 : _ → _) 1`   n/a: `lean_loogle` tool not available in this environment
[C] LeanSearch         "coordinatewise clamp onto unit cube lies in the cube"        n/a: `lean_leansearch` tool not available in this environment
[D] Grep mathlib src   `clamp`, `clampUnit`, `projIcc.*pi`, `pi.*projIcc`, `projIcc_mem`, `coe_prop`, `pi_univ_Icc`, `piecewise_mem_Icc`, `Pi.le_def`   **hits** (building blocks; no exact lemma)
[E] Name pattern       `projIcc`, `mem_Icc`, `clamp`, `coe_prop`, `coe_mem`         **hits** (the primitives below)

Searched for both the user's form (`clampUnit … ∈ Icc 0 1`) and the literature-standard form
("box-clamp ∈ box" at any generality). Findings (Method D, over
`.lake/packages/mathlib/Mathlib/`):

- **`Set.projIcc` (`Order/Interval/Set/ProjIcc.lean:48`)** is *valued in the bundled subtype*:
  `projIcc a b h x : Icc a b := ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩`.
  The membership-in-the-interval proof is **built into the return type** — it is exactly the `.2`
  used by `clampUnit_mem_Icc`'s proof.
- **`Subtype.coe_prop` (`Data/Subtype.lean:207`, `@[simp]`)**: `↑a ∈ S` for `a : {a // a ∈ S}`.
  Applied to `projIcc 0 1 _ (c i)` this is *exactly* `↑(projIcc …) ∈ Icc 0 1`, per coordinate, in one call.
- **`Set.mem_Icc` (`Order/Interval/Set/Defs.lean:80`, `@[simp]`)**: `x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b`.
- **`Pi.le_def` (`Order/Basic.lean:557`)**: `x ≤ y ↔ ∀ i, x i ≤ y i` — reduces the pi-box membership to
  coordinatewise.
- **`Set.pi_univ_Icc` (`Order/Interval/Set/Pi.lean:40`)** and **`Set.piecewise_mem_Icc'`
  (`Pi.lean:53`)** already exhibit the exact idiom `⟨fun i ↦ …, fun i ↦ …⟩` / `⟨h.1 _, h.2 _⟩` for
  proving pi-`Icc` membership coordinatewise.
- No `clamp` / `clampUnit` / "projIcc lands in Icc" standalone membership lemma exists. (`Fin.clamp`,
  `Order/Fin/Clamp.lean`, is an unrelated `Fin`-truncation; `clampDown`/`clampUp` are lattice ops —
  also unrelated.)

Concluded: **found the building blocks** (`Set.projIcc`'s bundled codomain + `Subtype.coe_prop` +
`Set.mem_Icc`/`Pi.le_def`); the lemma's content is subsumed by `Set.projIcc`'s own return type and is a
≤3-call composition. **Not in mathlib as a named lemma — and should not be**, because mathlib carries the
membership in the *type* of `projIcc`.

---

## Call sites — `Chebotarev.clampUnit_mem_Icc`

Internal use count: **2** (both within the declaring file `NormLeOneLipschitz.lean`)
External-to-file callers: **0** distinct files (and `clampUnit` itself is used in **no other file** in
the entire repo)

| Caller file:line                         | Usage pattern (one-line excerpt) |
|------------------------------------------|-----------------------------------|
| NormLeOneLipschitz.lean:120              | `refine ⟨M, fun c d ↦ (hM (clampUnit_mem_Icc ι c) (clampUnit_mem_Icc ι d)).trans ?_⟩` — feeds the cube-membership into a `LipschitzOnWith … (Icc 0 1)` application |
| NormLeOneLipschitz.lean:538              | `have := hB (mem_image_of_mem g (clampUnit_mem_Icc _ (cubeRelabel K c)))` — supplies `clampUnit … ∈ Icc 0 1` to `mem_image_of_mem` then a `subset_closedBall` membership |

Inline-derivation grep (was the same statement re-derived elsewhere without `clampUnit_mem_Icc`?):
  - (none) — the only producers of `… ∈ Icc 0 1` for clamped points route through this lemma.

Signal reading: K = 2 internal uses, both inside the declaring file, zero external. Per the call-sites
table this is a **local convenience wrapper** — real enough that inlining it would repeat the same
2-projection term twice, but with no consumer outside this single file and no consumer outside the
project. Combined with the trivial proof, this leans **NO-composable-from-mathlib** (it is glue, not API).

---

## Composition check (Phase 6)

Can `clampUnit ι c ∈ Set.Icc 0 1` be derived from mathlib in ≤3 chained calls? `clampUnit ι c` is
*definitionally* `fun i ↦ ↑(Set.projIcc 0 1 zero_le_one (c i))`.

Attempt 1 (the existing proof, already a composition):
  `⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1, fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩`
  - Mathlib decls used: `Set.projIcc` (bundled membership `.2`), pi-`Icc` membership = pair of pi-`≤`.
  - Result: **succeeds** — this *is* the proof; ≤3 projections, no lemma-of-its-own needed.
  - Notes: the membership proof is literally `Subtype`'s second component, no reasoning.

Attempt 2 (cleanest one-liner, coordinatewise `coe_prop`):
  `Set.mem_Icc.2 ⟨fun i ↦ (Subtype.coe_prop _).1, fun i ↦ (Subtype.coe_prop _).2⟩`
  (or simply `by simpa [clampUnit, Pi.le_def] using fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2`)
  - Mathlib decls used: `Subtype.coe_prop`, `Set.mem_Icc`, `Pi.le_def`.
  - Result: **succeeds** — a one-line `simp`/term composition.

Conclusion: **COMPOSABLE.** The statement is a ≤3-call composition (in practice a single
bundled-subtype projection lifted coordinatewise). The membership is already carried by
`Set.projIcc`'s codomain.

---

## Verdict: `Chebotarev.clampUnit_mem_Icc`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the box-clamp's *membership* is the trivial defining property of the
  nearest-point projection onto a box — **never a named result**; the literature's named facts about
  this map are its 1-Lipschitz/non-expansive property (which the file states separately).
- Generality analysis (Phase 4): STRICTLY NARROWER (ℝ, unit cube) but moot; modern-idiom check (4c)
  shows the membership is *already* carried by `Set.projIcc`'s bundled codomain — restating it loosely
  is the less idiomatic direction.
- Mathlib search (Phase 5): no named lemma; building blocks present — `Set.projIcc` (bundled `↥(Icc a b)`
  codomain), `Subtype.coe_prop`, `Set.mem_Icc`, `Pi.le_def`; the existing `Set.piecewise_mem_Icc'`
  already shows the identical coordinatewise idiom.
- Composition check (Phase 6): **COMPOSABLE** — the proof is itself the composition (the bundled `.2` of
  `projIcc` lifted across the pi order); a clean one-liner is
  `Set.mem_Icc.2 ⟨fun i ↦ (Subtype.coe_prop _).1, fun i ↦ (Subtype.coe_prop _).2⟩`.

**Rationale:**

`clampUnit_mem_Icc` asserts that the coordinatewise clamp onto `[0,1]^ι` lands in `[0,1]^ι`. Mathlib's
`Set.projIcc` is *valued in the bundled subtype* `↥(Set.Icc a b)`, so the membership of each clamped
coordinate is not a theorem at all — it is the second component of the term `projIcc` already returns
(`Subtype.coe_prop`). Lifting that across the pi type is the standard coordinatewise unfolding
(`Set.mem_Icc` + `Pi.le_def`), the exact idiom mathlib already uses in `Set.pi_univ_Icc` and
`Set.piecewise_mem_Icc'`. The whole lemma is therefore a ≤3-call composition (in practice one
subtype-projection), carries no mathematical content beyond `projIcc`'s definition, and has zero
consumers outside its single declaring file. The literature confirms there is nothing to "add": the
membership is the projection's defining codomain property; the genuinely-named result about this map —
its 1-Lipschitz/non-expansiveness — is already stated separately in the same file as
`lipschitzWith_clampUnit` and is the part with real content (and mathlib already has the per-coordinate
version, `LipschitzWith.projIcc`, `Topology/MetricSpace/Lipschitz.lean:199`).

This is a textbook NO-composable: mathlib has the building blocks, the form is a trivial inline
composition, and no new lemma is justified.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; `clampUnit ι c ∈ Icc 0 1` is a 1–3-call composition.
  - Building blocks (with full paths):
    - `Set.projIcc` — `Mathlib/Order/Interval/Set/ProjIcc.lean:48` — returns `↥(Set.Icc a b)`; its `.2`
      (or `Subtype.coe_prop`) is the per-coordinate membership.
    - `Subtype.coe_prop` — `Mathlib/Data/Subtype.lean:207` (`@[simp]`) — `↑a ∈ S`.
    - `Set.mem_Icc` — `Mathlib/Order/Interval/Set/Defs.lean:80` (`@[simp]`) — `x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b`.
    - `Pi.le_def` — `Mathlib/Order/Basic.lean:557` — reduces the pi order to coordinatewise.
  - Composition sketch (≤3 lines), pick either:
    ```lean
    -- as a term, mirroring the existing proof but routed through coe_prop:
    example (ι : Type*) (c : ι → ℝ) :
        (fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)) ∈ Set.Icc (0 : ι → ℝ) 1 :=
      Set.mem_Icc.2 ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1,
                     fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩
    -- or a one-liner:
    --   by simpa [Pi.le_def] using fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2
    ```
  - Call sites in this project (from Phase 6.0): **K = 2** — `NormLeOneLipschitz.lean:120` and
    `NormLeOneLipschitz.lean:538`.
  - Refactor plan: this is a `ForMathlib/` helper that, on the evidence, should **not** be upstreamed as
    its own lemma. Two reasonable dispositions, both fine for `main`/cleanup (no statement change to any
    public result):
      1. **Keep it project-local** (recommended) — it is a 2-use convenience wrapper that legitimately
         avoids repeating the bundled-projection term twice; it is *not* mathlib material, so it should
         simply lose any "earmarked for mathlib" tag. No PR.
      2. **Inline** — at lines 120 and 538 replace `clampUnit_mem_Icc ι c` /
         `clampUnit_mem_Icc _ (cubeRelabel K c)` with the composition above (a `Set.mem_Icc.2 ⟨…, …⟩`
         term, or the `simpa [Pi.le_def]` one-liner), then delete `clampUnit_mem_Icc`. Check the
         implicit/explicit `ι` flow at each site.
  - Net: do **not** open a mathlib PR for this lemma. The mathlib-worthy content in this neighbourhood is
    `lipschitzWith_clampUnit` (the 1-Lipschitz fact) — and even that is the pi-companion of the existing
    `LipschitzWith.projIcc`, so it too is a composition; assess it separately if desired.

---

## Next step

Do not upstream `Chebotarev.clampUnit_mem_Icc`. Either keep it as a project-local convenience helper
(drop the mathlib earmark) or inline the ≤3-call composition
`Set.mem_Icc.2 ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1, fun i ↦ …(c i)).2.2⟩` at its two call
sites (`NormLeOneLipschitz.lean:120`, `:538`) and delete it. The membership is already carried by
`Set.projIcc`'s bundled `↥(Icc 0 1)` codomain (`Subtype.coe_prop`), so no new mathlib lemma is justified.
