# /mathlibable report — `Chebotarev.lipschitzWith_clampUnit`

Mode A, single declaration. Source:
`projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:107`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source + mathlib tree)
- decl `Chebotarev.lipschitzWith_clampUnit`: ✓ resolved at `…/ForMathlib/NormLeOneLipschitz.lean:107`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrisation of the frontier of `normLeOne K` — a
  `ForMathlib/` helper file building the finite Lipschitz-cube cover of the norm-≤-1 cone
  boundary (Gun–Ramaré–Sivaraman §3.3 boundary-regularity input).

True qualified name **confirmed**: `Chebotarev.lipschitzWith_clampUnit`
(namespace `Chebotarev`, opened at line 79; lemma at line 107).

---

### Statement (Phase 1)

`lipschitzWith_clampUnit` asserts that the **coordinatewise clamp of `ι → ℝ` onto the unit
cube `[0,1]^ι`** (finite `ι`) is `1`-Lipschitz for the sup (L∞) metric. The clamp is
`clampUnit ι c = fun i ↦ projIcc 0 1 _ (c i)`, i.e. each coordinate `c i` is replaced by
`min 1 (max 0 (c i))`. Mathematically: the metric (nearest-point) projection of `ℝ^ι` onto
the closed box `[0,1]^ι`, in the `ℓ∞` metric, is nonexpansive.

Variables / typeclasses (Lean side):
- `ι : Type*`, `[Fintype ι]` — the (finite) coordinate index set.
- Codomain/domain `ι → ℝ` carries mathlib's pi `edist` = `Finset.sup` of coordinate `edist`s
  (the L∞ extended metric).

Hypotheses: none beyond `[Fintype ι]`.

Conclusion (math): the coordinatewise clamp onto `[0,1]^ι` is `1`-Lipschitz (nonexpansive).

Conclusion (Lean): `LipschitzWith 1 (clampUnit ι)`.

Proof body (2 substantive lines): applies the file-local private helper
`lipschitzWith_one_of_edist_apply_le` (a map into a finite pi type is `1`-Lipschitz once each
output coordinate's `edist` is bounded by the input `edist`), discharging the per-coordinate
bound with `(LipschitzWith.projIcc zero_le_one).edist_le_mul`, `one_mul`, and
`edist_le_pi_edist`, bridging the `projIcc` subtype coercion with `Subtype.edist_eq`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper lemma — the 1-Lipschitz property of a project-local coordinatewise clamp,
used to make the cube-face cover maps globally Lipschitz. Not a named theorem, not a `## Main
results` entry (those are the `normLeOne_frontier_lipschitz_cover*` results), not a new
structure.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not `def`.**

Note — the lemma is *about* the one-liner **def** `clampUnit ι c := fun i ↦ (Set.projIcc 0 1
zero_le_one (c i) : ℝ)` (line 88, a one-line `def`). That carrier def is itself a one-liner
**without a Phase-2b exemption**: it is sealed only for local convenience (readability of the
face-cover pipeline), there is no downstream proof that relies on its non-unfolding, no
typeclass-diamond it resolves, and its only "consumer" is this same file. This matters for
Phase 7: a lemma whose entire content is "the project-local one-liner `clampUnit` is
1-Lipschitz" is a wrapper, not an upstreamable unit.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (general form)         | metric projection onto convex set is nonexpansive 1-Lipschitz Hilbert space                            | yes  | `P_C` onto closed convex `C` in Hilbert/Hadamard space is firmly nonexpansive ⇒ nonexpansive (1-Lipschitz) | Folland-level classical convex analysis; arXiv 1602.06430, ScienceDirect S0022247X12004088, Frankfurt lecture notes Kap.4 |
|  2 | WebSearch (specific form)        | coordinatewise clamp projection onto box [0,1]^n is 1-Lipschitz sup norm nonexpansive                  | yes  | clip `x ↦ min(max(a,x),b)` is 1-Lipschitz; coordinatewise onto `[0,1]^n` is 1-Lipschitz in `‖·‖∞` | folklore in optimization / projected-gradient / 1-Lipschitz-ResNet literature (arXiv 2505.12003, PEPit operators docs) |
|  3 | WebSearch (mathlib-specific)     | mathlib4 LipschitzWith projIcc pi coordinatewise projection Icc product                                | partial | mathlib4 docs surface `Set.projIcc` + `LipschitzWith` but **not** the coordinatewise/pi combination | confirms single-coordinate API exists; pi version not indexed |
|  4 | ChatGPT MCP                      | "Does Mathlib have a pi/coordinatewise version of LipschitzWith.projIcc, and the codomain-pi companion of LipschitzWith.eval? Standard name + maximal generality?" | n/a  | (tool error)                                          | Codex backend errored (stdin failure); compensated by WebSearch ×3 + nLab + Loogle + direct source reading |
|  5 | Local references                 | `.mathlib-quality/references/` for "projection"/"Lipschitz"                                            | n/a  | (no references directory for Chebotarev)              | `.mathlib-quality/references/` absent — recorded n/a |
|  6 | nLab                             | metric projection nonexpansive map convex subset CAT(0) Lipschitz                                      | yes  | metric projection onto complete convex subset of a CAT(0) space is firmly nonexpansive / 1-Lipschitz | arXiv 1311.4174 (characterisation), 1410.1137; the box `[0,1]^ι` ⊂ `ℝ^ι` is exactly a closed convex subset |
|  7 | nCatLab                          | —                                                                                                      | n/a  | n/a — not a higher-categorical concept                | nearest-point projection is a metric, not categorical, notion |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | n/a — not an algebraic-geometry concept               | — |
|  9 | MathOverflow / Math.SE           | (covered transitively by #1/#2 result pages)                                                           | yes  | "projection onto convex set is nonexpansive" is a standard MO/MSE answer; the box clamp is the textbook example | consistent with #1 |
| 10 | recent arXiv (last 5 years)      | clip/clamp 1-Lipschitz box constraint (within #2)                                                      | yes  | the coordinatewise clip onto `[ℓ,u]` is 1-Lipschitz + idempotent, used pervasively in Lipschitz-constrained ML | arXiv 2505.12003, 2407.14156, 1010.0141 (L1 box projection) |

Protocol pass check:
- WebSearch ran **3 distinct queries** at different generality levels (general convex-projection
  form, specific box-clamp form, mathlib-specific form). ✓
- ChatGPT MCP attempted with an explicit standard-form/generality/history question — **backend
  errored**; recorded with reason. The remaining channels (WebSearch ×3, nLab, Loogle ×4, source)
  more than cover the standard-form question. ✓ (degraded but compensated)
- Local references checked → n/a (absent). ✓
- nLab checked → hit (CAT(0) metric projection). ✓
- Stacks / nCatLab → n/a with reason. ✓
- arXiv / MO → hit. ✓

### Literature summary (Phase 3)

Concept identified as: **metric (nearest-point) projection onto a closed convex set is
nonexpansive** — equivalently the **coordinatewise clip/clamp onto a box `[a,b]^n` is
1-Lipschitz in the sup norm** (the box being a product of intervals).
Sources agree on the standard form: **yes**.
Most general standard form: in a complete CAT(0) / Hadamard space (in particular any Hilbert
space, in particular `ℝ^ι` with any `ℓ^p`), the metric projection onto a nonempty closed
convex subset is firmly nonexpansive, hence 1-Lipschitz. The box `[0,1]^ι` with the `ℓ∞`
metric is a special case where the projection is computed coordinatewise by the scalar clip
`projIcc`.
Generality dimensions where the literature varies:
  - ambient space: from `ℝ^n` (sup or Euclidean) up to Hilbert / complete CAT(0) — most
    general is complete CAT(0).
  - target set: from a box `[a,b]^n` up to an arbitrary closed convex set — most general is
    arbitrary closed convex.
  - the *coordinatewise* description (`projIcc` per coordinate) is specific to **boxes in a
    product space with the sup metric**; for Euclidean/Hilbert the projection onto a box is
    still coordinatewise, but the constant-1 sup-norm statement is the cleanest.
Disagreement with the literature: none. The Lean form is a correct, strict specialisation of
the standard nonexpansive-projection fact.

---

### Generality analysis — `lipschitzWith_clampUnit` (Phase 4)

Literature-standard form (Phase 3): metric projection onto a closed convex set is nonexpansive;
its concrete shadow here is "coordinatewise clip onto a box is 1-Lipschitz in `ℓ∞`".

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | codomain scalar `ℝ` | each coordinate is `projIcc 0 1` into `ℝ` | clip onto any `[a,b]` in a `LinearOrder`/lattice; projection onto convex set in CAT(0) | yes | mathlib's scalar half is already general: `LipschitzWith.projIcc {a b : ℝ} (h : a ≤ b)`. Fixing `0,1` is a pure specialisation. |
| 2 | box `[0,1]` (fixed endpoints) | `Set.projIcc 0 1 zero_le_one` | any `[a,b]`, `a ≤ b`, possibly per-coordinate distinct | yes | nothing in the proof uses `0`/`1`; `LipschitzWith.projIcc` already covers arbitrary `a ≤ b`. |
| 3 | the **carrier** `clampUnit ι` | a project-local named one-liner | the standard object is just "coordinatewise `projIcc`" — no named wrapper in the literature | yes (remove the wrapper) | the literature/mathlib idiom is to apply `projIcc` pointwise; the named `clampUnit` is project bookkeeping, not a standard object. |
| 4 | finite `ι` (sup metric) | `[Fintype ι]`, pi `edist` = `Finset.sup` | for sup over an *arbitrary* index the L∞ bound still holds (mathlib's pi `edist` is `Fintype`-only; `iSup` needed for infinite) | partial | `Fintype` is essentially forced by mathlib's pi `PseudoEMetricSpace` instance; not a real restriction for the standard statement. |

The maximally reusable target is **not** "redo `clampUnit`". It is the **missing mathlib
companion lemma**: a map into a finite pi type is `K`-Lipschitz once each output coordinate is
(the codomain dual of `LipschitzWith.eval`). That lemma — call it `lipschitzWith_pi` /
`LipschitzWith.pi` — is exactly the content of the file-local *private* helper
`lipschitzWith_one_of_edist_apply_le`, and is genuinely absent from mathlib (see Phase 5). Once
present, `lipschitzWith_clampUnit` collapses to a one-liner:
`(lipschitzWith_pi …) <| fun i ↦ (LipschitzWith.projIcc _).comp (LipschitzWith.eval i)` —
making the named `clampUnit` lemma itself redundant for mathlib.

#### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (fixed `[0,1]`, named-wrapper-specific,
about a project-local one-liner).
Number of weakening opportunities found: 3 (drop `clampUnit` wrapper; arbitrary `[a,b]`; the
real target is the general pi-codomain lemma, not this clamp lemma).
Proposed restatement: **not a restatement of this lemma** — the mathlib-worthy artifact is the
*general* pi-codomain Lipschitz lemma (Phase 4c), from which this clamp fact is a trivial
specialisation that should be inlined, not upstreamed.
Cost of restatement (of the general companion lemma): **CHEAP** — it is the verbatim body of
the existing private helper.

#### 4c. Modern-idiom check (Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass? | no | already typeclass-driven (`Fintype`, `PseudoEMetricSpace`) | — |
|  2 | sequences/metric → filters/topological? | no | this is a genuine metric (Lipschitz-constant) statement; filters don't generalise a numeric constant | — |
|  3 | construct an object → universal property? | no | nearest-point projection has no universal-property class in mathlib | — |
|  4 | set+closure-predicate → bundled substructure? | no | — | — |
|  5 | vector/metric/field-specific → weaken typeclass? | **yes** | replace the bespoke `clampUnit` lemma with the **general finite-pi-codomain Lipschitz lemma** `LipschitzWith K f` from `∀ i, LipschitzWith K (f · i)` (the dual of `LipschitzWith.eval`), then derive box-clamp as `projIcc`-per-coordinate | every coordinatewise-defined Lipschitz map into a finite product (clamp, min/max with a vector, coordinate truncation, …) gets a one-line proof; pairs with the existing `LipschitzWith.eval` to complete the eval/pi API symmetry |
|  6 | 1-categorical → higher-categorical? | no | — | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → general algebraic? | no (already `ι` general) | — | — |

#### 4c verdict

Modern idiom available: **yes** — but the modernisation target is the **general pi-codomain
Lipschitz lemma**, *not* a re-statement of `lipschitzWith_clampUnit`.
- Proposed mathlib-idiomatic addition (separate from this decl):
  ```lean
  theorem lipschitzWith_pi {α ι : Type*} {β : ι → Type*}
      [PseudoEMetricSpace α] [∀ i, PseudoEMetricSpace (β i)] [Fintype ι]
      {K : ℝ≥0} {f : α → ∀ i, β i} (h : ∀ i, LipschitzWith K (fun a => f a i)) :
      LipschitzWith K f
  ```
  (the `K = 1`, `edist`-form of this is precisely the private `lipschitzWith_one_of_edist_apply_le`).
- Cost: **CHEAP**.
- Mathlib downstream: completes the missing direction of mathlib's pi Lipschitz API
  (`LipschitzWith.eval` is the projection half; this is the pairing/codomain half). With it,
  `lipschitzWith_clampUnit`, `lipschitzWith_cubeRelabel` (line 265, same file — same private
  helper!), and any future coordinatewise-Lipschitz lemma become one-liners.
- Real improvement: removes a recurring hand-rolled reduction (`of_edist_le` + `edist_pi_def`
  + `Finset.sup_le` + `edist_le_pi_edist`) that authors currently re-derive (this very file
  does it twice, lines 100–105 and reuses at 108, 266).

So the **upstreamable object is the general `lipschitzWith_pi`, not this clamp lemma.** This
decl, as stated, remains a project-local specialisation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or instance-search paths
introduced.)

---

### Mathlib search-status: `lipschitzWith_clampUnit` (Phase 5)

[A] Lean-Finder       (tool unavailable locally)                          n/a — env: mathlib-index MCP not resolving; substituted Loogle web API + source grep
[B] Loogle            `LipschitzWith, Set.projIcc` ; `LipschitzWith ?n (fun (c : ?i -> Real) => _)` ; `(∀ i, LipschitzWith ?K _) -> LipschitzWith ?K _`   →  see below
[C] LeanSearch        (tool unavailable locally)                          n/a — env; compensated by WebSearch #3 (mathlib4 docs) + Loogle
[D] Grep mathlib src  `projIcc` + (pi|fun|clamp|coordinate) ; `clamp` ; pi-codomain Lipschitz packaging   →  see below
[E] Name pattern      `lipschitzWith_pi` / `LipschitzWith.pi` / `lipschitz_pi`   →  no such decl

Loogle [B] results (decisive):
- `LipschitzWith ∩ Set.projIcc` → **exactly one** hit: `LipschitzWith.projIcc {a b : ℝ}
  (h : a ≤ b) : LipschitzWith 1 (Set.projIcc a b h)` (single coordinate only).
- `LipschitzWith ?n (fun (c : ?i → ℝ) => _)` → **0** matches among 108 `Real`+`LipschitzWith`
  decls (no coordinatewise-clamp-into-`ℝ^ι` Lipschitz lemma).
- `(∀ i, LipschitzWith ?K _) → LipschitzWith ?K _` → 2 matches, both **not** the finite-pi
  codomain lemma: `LipschitzWith.uncurry` (binary `Function.uncurry`, constant `Kα+Kβ`) and
  `LipschitzWith.list_prod` (composition of endomorphisms). The genuine finite-pi-codomain
  packaging lemma is absent.

Grep [D] results:
- mathlib's only "clamp" is `Fin.clamp` (`Mathlib/Order/Fin/Clamp.lean`) — unrelated (on `Fin`,
  order-theoretic, no metric content).
- pi Lipschitz infrastructure present: `LipschitzWith.eval` (proj half), `edist_pi_def`,
  `edist_le_pi_edist`, `edist_pi_le_iff`, `LipschitzWith.of_edist_le`, `LipschitzWith.projIcc`,
  `LipschitzWith.edist_le_mul`, `Subtype.edist_eq` — i.e. **all the building blocks, no packaged
  result.** The `lpSpace` file has `LipschitzWith.memℓp`-style per-coordinate hypotheses but for
  the bundled `ℓ∞` type, not `∀ i, β i`.

Searched for both:
  - the user's current form (`LipschitzWith 1 (clampUnit ι)`) — not in mathlib;
  - the literature-standard / general forms (coordinatewise box clamp; general pi-codomain
    Lipschitz; metric projection nonexpansive) — also not in mathlib as a named lemma.

Concluded: **not in mathlib** as a packaged result, but mathlib has the **building blocks**
(`LipschitzWith.projIcc`, `LipschitzWith.of_edist_le` / `edist_pi_le_iff`, `LipschitzWith.eval`,
`Subtype.edist_eq`); composition yields the user's form. (Mathlib also lacks the *general*
companion `lipschitzWith_pi` — a separate, genuinely-missing small lemma.)

---

### Composition check (+ call-sites signal) (Phase 6)

#### 6.0. Call sites — `lipschitzWith_clampUnit`

Internal use count: **1** (within the project, excluding the declaring decl).
External-to-file callers: **0** distinct files (the one use is *inside the same file*).

| Caller file:line | Usage pattern |
|---|---|
| `…/ForMathlib/NormLeOneLipschitz.lean:122` | `simpa using (lipschitzWith_clampUnit ι).edist_le_mul c d` — inside `exists_lipschitzWith_comp_clampUnit`, to transfer the clamp's `edist`-bound through `gcongr` |

Inline-derivation grep: the *sibling* lemma `lipschitzWith_cubeRelabel` (line 265, same file)
re-derives an analogous coordinatewise 1-Lipschitz fact via the same private helper
`lipschitzWith_one_of_edist_apply_le` — evidence the **general** reduction recurs, not that this
specific clamp lemma is reused.

Call-sites reading: K = 1 internal use, no external/downstream consumers, carrier is a
project-local one-liner. Per the call-sites signal table this leans **NO-composable** (the wrong
abstraction to upstream as-is; the right one is the general helper).

#### 6a. Composition attempt

Can `lipschitzWith_clampUnit` be derived from mathlib in ≤3 chained calls?

Attempt 1 (per-coordinate, via the eval/projIcc composition):
```lean
example (ι : Type*) [Fintype ι] : LipschitzWith 1 (clampUnit ι) :=
  LipschitzWith.of_edist_le fun c d => edist_pi_le_iff.2 fun i =>
    (Subtype.edist_eq _ _ ▸ ((LipschitzWith.projIcc (zero_le_one)).edist_le_mul (c i) (d i)).trans_eq (one_mul _)).trans (edist_le_pi_edist c d i)
```
  - Mathlib decls used: `LipschitzWith.of_edist_le`, `edist_pi_le_iff`, `LipschitzWith.projIcc`,
    `LipschitzWith.edist_le_mul`, `edist_le_pi_edist`, `Subtype.edist_eq` (coercion bridge).
  - Result: **succeeds** — this is, up to `simp`-normalisation, the exact 2-line proof already
    in the source (which factors the pi-reduction into the private helper). It is `of_edist_le`
    + `edist_pi_le_iff` (the pi reduction) + `projIcc.edist_le_mul` (the per-coordinate
    nonexpansiveness) — **3 mathlib calls**, the rest being the `projIcc` subtype-coercion
    bookkeeping (`Subtype.edist_eq`, `one_mul`).
  - Notes: the only friction is `Set.projIcc` landing in the subtype `↥(Icc 0 1)`, requiring the
    `Subtype.edist_eq` bridge — a coercion lemma, not new mathematics.

Conclusion: **COMPOSABLE** (≤3 mathlib calls + coercion glue). The composition is the proof
itself; no new mathematical content beyond mathlib's `projIcc` nonexpansiveness and the pi
sup-metric reduction.

#### 6b. Heuristic check

The composition is `of_edist_le (edist_pi_le_iff.2 fun i => (projIcc.edist_le_mul …).trans …)`
— a single chained term (function applications + `.trans` + a `▸` coercion rewrite), matching
the "yes" rows of the heuristics table (`.trans` chain, one function call per step, projection
bridge). It is **not** a multi-`have` proof with non-trivial reasoning between steps. The lone
caveat is the `Subtype.edist_eq` rewrite, which is coercion glue rather than a reasoning step.

---

## Verdict: `Chebotarev.lipschitzWith_clampUnit`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): standard fact — "metric projection onto a closed convex set is
  nonexpansive"; the concrete coordinatewise box-clamp is textbook/folklore. Maximally general
  form is CAT(0)/Hilbert nonexpansive projection.
- Generality analysis (Phase 4): **STRICTLY NARROWER** — fixed `[0,1]`, tied to the project-
  local one-liner `clampUnit`; the genuinely mathlib-worthy object is the *general* pi-codomain
  Lipschitz lemma (4c), not a restatement of this clamp fact.
- Mathlib search (Phase 5): not in mathlib as a packaged result; all building blocks present
  (`LipschitzWith.projIcc`, `of_edist_le`/`edist_pi_le_iff`, `eval`, `Subtype.edist_eq`).
- Composition check (Phase 6): **COMPOSABLE** in ≤3 mathlib calls (the existing 2-line proof);
  K = 1 internal call site, no external consumers.

**Rationale.**
As *stated*, `lipschitzWith_clampUnit` is the assertion that a **project-local one-line def**
(`clampUnit ι c = fun i ↦ projIcc 0 1 _ (c i)`) is 1-Lipschitz, proved in two lines by
composing mathlib's per-coordinate `LipschitzWith.projIcc` with the pi sup-metric reduction
(`of_edist_le` + `edist_pi_le_iff` + `edist_le_pi_edist`). That is a ≤3-call mathlib
composition, used exactly once, inside the same file, with no downstream consumers — the
canonical NO-composable profile. The carrier `clampUnit` is a one-liner with no Phase-2b
exemption (no defeq barrier, no diamond, no external API role), so the lemma about it should
not be shipped to mathlib as-is; it should be inlined where used.

The one genuinely mathlib-shaped finding here is *adjacent*, not this declaration: mathlib is
**missing the general finite-pi-codomain Lipschitz lemma** — the codomain dual of the existing
`LipschitzWith.eval` — which is precisely the content of this file's *private* helper
`lipschitzWith_one_of_edist_apply_le` (and which the file already needs twice, also for
`lipschitzWith_cubeRelabel`). That general lemma is the upstreamable unit; once it exists,
`lipschitzWith_clampUnit` is a one-liner and stays project-local. This is therefore a NO for
*this* decl, with a concrete spin-off recommendation rather than a YES.

**WHY not (refactor-actionable).**
Mathlib has every building block; the user's form is a 1–3-call composition over them. The
clamp lemma packages no mathematical content mathlib lacks — only the project-local naming of
`clampUnit`. The recurring piece (the pi-reduction) is real but belongs in a *general* lemma,
not this specialisation.

Mathlib building blocks:
- `LipschitzWith.projIcc` — `Mathlib/Topology/MetricSpace/Lipschitz.lean:199`
  (`{a b : ℝ} (h : a ≤ b) : LipschitzWith 1 (Set.projIcc a b h)`)
- `LipschitzWith.of_edist_le` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:169`
- `edist_pi_le_iff` — `Mathlib/Topology/EMetricSpace/Pi.lean:46`
- `edist_le_pi_edist` — `Mathlib/Topology/EMetricSpace/Pi.lean:42`
- `LipschitzWith.edist_le_mul` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:138`
- `Subtype.edist_eq` (coercion bridge for `projIcc`'s subtype codomain)
- (optionally `LipschitzWith.eval` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:219` — if
  factoring through `Function.eval`)

Composition sketch (≤3 mathlib calls + coercion glue), already the file's proof:
```lean
example (ι : Type*) [Fintype ι] : LipschitzWith 1 (clampUnit ι) :=
  LipschitzWith.of_edist_le fun c d => edist_pi_le_iff.2 fun i =>
    (Subtype.edist_eq _ _ ▸
      ((LipschitzWith.projIcc zero_le_one).edist_le_mul (c i) (d i)).trans_eq (one_mul _)).trans
      (edist_le_pi_edist c d i)
```

Call sites in our project (Phase 6.0): **K = 1** (`NormLeOneLipschitz.lean:122`, same file).

Refactor plan:
1. At the single call site (line 122, inside `exists_lipschitzWith_comp_clampUnit`), the use is
   `(lipschitzWith_clampUnit ι).edist_le_mul c d`. Since `clampUnit` stays a project-local def,
   the cleanest local refactor is to **keep `lipschitzWith_clampUnit` as a private helper in
   this file** (it is genuinely convenient here) — it does *not* need to travel to mathlib.
2. The mathlib-facing action is **separate and additive**: extract the file-local private
   `lipschitzWith_one_of_edist_apply_le` into the general `lipschitzWith_pi` /
   `LipschitzWith.pi` lemma (Phase 4c signature) and propose *that* to mathlib
   (`Mathlib/Topology/EMetricSpace/Lipschitz.lean`, beside `LipschitzWith.eval`). After it
   lands, both `lipschitzWith_clampUnit` and `lipschitzWith_cubeRelabel` simplify to one-liners
   against it.

Next action: do **not** upstream `lipschitzWith_clampUnit`. Keep it project-local (optionally
demote to `private`, since K = 1 and it is file-internal). Separately, consider a tiny mathlib
PR adding the general finite-pi-codomain Lipschitz lemma (`LipschitzWith.pi`, the dual of
`LipschitzWith.eval`) — that is the real gap this file revealed.

---

## Next step

Treat `lipschitzWith_clampUnit` as `NO-composable-from-mathlib`: it is a ≤3-call composition of
mathlib primitives over a project-local one-liner (`clampUnit`), used once, with no downstream
consumers — keep it local (optionally `private`). The upstreamable artifact this file surfaces
is the **separate** general lemma `LipschitzWith.pi` (a map into a finite pi type is
`K`-Lipschitz from per-coordinate `K`-Lipschitz — the codomain dual of `LipschitzWith.eval`),
currently the file's private `lipschitzWith_one_of_edist_apply_le`; propose that to mathlib on
its own.
