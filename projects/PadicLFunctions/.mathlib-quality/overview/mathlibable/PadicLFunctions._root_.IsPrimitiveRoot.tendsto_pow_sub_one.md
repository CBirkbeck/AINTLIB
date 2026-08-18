# `/mathlibable` report — `PadicLFunctions._root_.IsPrimitiveRoot.tendsto_pow_sub_one`

Mode A, full 10-phase workflow, exhaustive 9-channel literature search.
Qualified name: `IsPrimitiveRoot.tendsto_pow_sub_one` (declared with `_root_.`
inside `namespace PadicLFunctions`, so it lives in the **root**
`IsPrimitiveRoot` namespace — the namespace mathlib uses for its cyclotomic
lemmas; dot-notation `hζ.tendsto_pow_sub_one` is therefore available).

---

## Verdict (five-bucket)

**`NO-composable-from-mathlib`** — the statement is one mathlib call
(`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`) applied to the project's own
norm bound `IsPrimitiveRoot.norm_sub_one_lt`. The proof body **is** the
composition (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt hn)`),
a single chained call. The wrapper has **zero** internal call sites, and the
identical 1-call pattern is **re-derived inline at three other project sites**
that bypass it — the canonical NO-composable signature. The supply lemma
`norm_sub_one_lt` (the half mathlib does *not* have) is assessed separately and
is the project's real contribution (`YES-but-generalise-first`); the `tendsto`
corollary on top of it is not a separate mathlib-worthy lemma.

A note carried from Phase 4c: the conclusion `Tendsto ((ζ-1) ^ ·) atTop (𝓝 0)`
is *definitionally* `IsTopologicallyNilpotent (ζ-1)` (mathlib's
`IsTopologicallyNilpotent a := Tendsto (a ^ ·) atTop (𝓝 0)`). That is a
project-side cleanup recommendation (state the idiom, or inline), **not** a
reason to upgrade to a YES bucket — mathlib already gives the content in one
call.

---

## Baseline (Phase 0)

- lake build:               **not re-run** (build is stale/slow per task note); **reasoned from source** — Phase 0 fallback. The declaration, its one dependency (`norm_sub_one_lt`), the mathlib building block, and the three sibling re-derivation sites were all read directly from source.
- decl `IsPrimitiveRoot.tendsto_pow_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:200`
- kind:                      theorem
- has sorry:                 no (complete one-line proof, line 203)
- mathlib pin:               `d90090f647ca` (rc2, 2026-06-08); toolchain `leanprover/lean4:v4.31.0-rc2`
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field, and basic facts about `p^n`-th roots of unity used to build the Iwasawa algebra.

---

## Statement (Phase 1)

`IsPrimitiveRoot.tendsto_pow_sub_one` is a **theorem** stating the following:

> Let `L` be a nonarchimedean normed field that is a normed `ℚ_p`-algebra (so
> its residue characteristic is `p`). If `ζ ∈ L` is a primitive `p^n`-th root
> of unity with `n ≥ 1`, then the powers `(ζ − 1)^k` converge to `0` as
> `k → ∞`; i.e. `ζ − 1` is **topologically nilpotent**.

Mathematically: a primitive `p^n`-th root of unity in a `p`-adic field is
`≡ 1` modulo the maximal ideal, so `ζ − 1` has positive valuation
(`‖ζ−1‖ < 1`), and in an ultrametric (indeed in any seminormed ring) an element
of norm `< 1` has powers tending to `0`. The result is the **topological-
nilpotence corollary** of the norm bound `norm_sub_one_lt`; the project's
docstring states it as exactly that ("W2': hence `ζ − 1` is topologically
nilpotent (powers tend to `0`)").

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L]` — the ambient nonarchimedean value field.
- `[NormedAlgebra ℚ_[p] L]` — makes `L` a `ℚ_p`-algebra; used only *transitively*, inside `norm_sub_one_lt`, to obtain `‖(p:L)‖ < 1`. Not used directly by this corollary.
- `[IsUltrametricDist L]` — ultrametric norm; again used only transitively via `norm_sub_one_lt`.
- `[CompleteSpace L]` — **omitted** (`omit [CompleteSpace L] in`, line 198); not used.

Hypotheses (Lean side):
- `hζ : IsPrimitiveRoot ζ (p ^ n)` — `ζ` is a primitive `p^n`-th root of unity.
- `hn : 1 ≤ n` — excludes `n = 0` (where `ζ = 1`, `ζ − 1 = 0`; the conclusion is still true there, but `norm_sub_one_lt` needs `n ≥ 1`).

Conclusion (math): `(ζ − 1)^k → 0` (topological nilpotence of `ζ − 1`).

Conclusion (Lean): `Tendsto ((ζ - 1) ^ ·) atTop (𝓝 0)` — which **unfolds to**
`IsTopologicallyNilpotent (ζ - 1)` (defeq; see Phase 4c).

Proof body (verbatim, the whole thing):

```lean
tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt hn)
```

---

## Size classification (Phase 2a)

**Verdict: SMALL.**
Reason: a one-line corollary (`:= mathlib_lemma (project_lemma hn)`) deriving
topological nilpotence from the norm bound it sits directly beneath. It is not a
new structure, not a person/place-named theorem, and not a `## Main
declarations` headline — the file's three headline results are `integerRing`,
`norm_sub_one_lt`, and `norm_pow_sub_one_eq_one`. The docstring marks it "W2'",
the *primed* (i.e. derived) companion of the W2 headline `norm_sub_one_lt`.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing
only and does not gate the channels Phase 3 runs.)

## One-line check (Phase 2b)

Body line count: 1 substantive line.
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`.
The Phase-2b def-exemption table does not apply to theorems. The fact that the
proof is a one-liner is, however, a strong composability signal carried into
Phases 6–7 (a theorem whose proof is a single mathlib call applied to one
project lemma is the prototypical inline-able corollary).

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "primitive p^n-th root of unity (ζ-1)^k tends to 0 p-adic topologically nilpotent" | yes | `ζ_{p^r} − 1` divides `p`, is a non-zero-divisor, and is topologically nilpotent; recurring in p-adic Hodge / perfectoid theory | arXiv:2302.12747 (uses `ω=(ζ_p−1)`), arXiv:1608.00922 (Bhatt–Morrow–Scholze A_inf), Scholze perfectoid notes |
| 2 | WebSearch (general form) | "topologically nilpotent element norm less than one powers converge to zero ultrametric Banach algebra" | yes | in a non-archimedean Banach ring, `{x : ‖x‖<1} ⊆ A°°` (topologically nilpotent ideal); `‖x‖<1 ⇒ x^n→0` | planetmath "topologically nilpotent"; Kedlaya "non-archimedean Banach fields"; Wikipedia "Power-bounded element" |
| 3 | WebSearch (named-after / aliases) | "power-bounded topologically nilpotent elements adic ring norm bounded by one stacks perfectoid" | yes | Huber/Tate: a *topologically nilpotent unit* = *pseudo-uniformizer*; `A°°` (top. nilpotent elts) sits inside `A°` (power-bounded) | Scholze "Perfectoid Spaces" §2 (Adic Spaces); Wikipedia "Power-bounded element"; nLab "perfectoid space" |
| 4 | ChatGPT MCP | (would ask: standard def of topological nilpotence + its norm-`<1` sufficiency + history) | n/a | — | ChatGPT MCP **not installed** in this environment (only Asana/Linear/etc. claude.ai proxies are present); covered by channels 1–3 + 6 which already settle the standard form. Recorded n/a with reason. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | — | neither directory exists in this checkout (refs are local-only and absent here). Recorded n/a. |
| 6 | nLab / nCatLab | "topologically nilpotent element" (direct fetch + search) | yes | "an element is topologically nilpotent iff the sequence of its powers converges to 0"; every top. nilpotent element is power-bounded | nLab page returned 404 on direct fetch, but ProofWiki + planetmath + the nLab "perfectoid space" page all give the same def; the concept is standard and unanimous |
| 7 | Stacks Project | tag 0AMT + "topologically nilpotent" | partial/n/a | Stacks defines *topologically nilpotent ideals* (`I^n → 0`) in the adic-ring section; the element form is the `a^n → 0` specialisation | not primarily an algebraic-geometry-only concept; Stacks covers the ideal version. The element statement is the standard `a^n → 0`. |
| 8 | MathOverflow / Math.SE | "topologically nilpotent" definition powers tend to zero | yes | element form = powers tend to 0; this is the universally-quoted definition | ProofWiki "Definition:Topologically Nilpotent Ring Element" gives it verbatim |
| 9 | recent arXiv (last 5 yrs) | "topologically nilpotent" + `(ζ_p − 1)` perfectoid / p-adic Hodge | yes | `(ζ_p−1)`-adic topological nilpotence is a standard tool (Hitchin-small Higgs fields, A_inf-cohomology) | arXiv:2302.12747 (2025), arXiv:2411.03573 (2024) |

**Protocol pass check.** WebSearch ran 3 distinct queries at different
generality levels (specific `(ζ−1)` form / general norm-`<1` form / named-after
"pseudo-uniformizer"/"power-bounded"). ChatGPT MCP recorded `n/a` with the
genuine reason (not installed) — the standard form is nonetheless pinned by
channels 1–3, 6, 8. Local refs `n/a` (absent). nLab, Stacks, MathOverflow,
arXiv each checked. No channel was skipped silently.

### Literature summary (Phase 3)

Concept identified as: **topological nilpotence of `ζ − 1`** — equivalently
"`ζ − 1` lies in the topologically-nilpotent ideal `A°°`", a special case of
the universal fact **"in a (semi)normed ring, `‖x‖ < 1 ⇒ x^n → 0`"** combined
with the cyclotomic input **"`‖ζ_{p^n} − 1‖ < 1` in a `p`-adic field"**.

Sources agree on the standard form: **yes, unanimously.** "An element is
topologically nilpotent iff its powers converge to 0" is the textbook
definition (ProofWiki, planetmath, nLab, Huber/Scholze adic-spaces theory). The
specific input "`ζ_{p^n} − 1` is topologically nilpotent in a `p`-adic field"
is a recurring tool in p-adic Hodge theory and perfectoid geometry (BMS A_inf,
Scholze, the 2025 arXiv preprints).

Most general standard form: there are two orthogonal pieces. (a) The
*topological-dynamics* half — `‖x‖ < 1 ⇒ Tendsto (x^·) atTop (𝓝 0)` — holds in
**any seminormed ring** and is decades old. (b) The *cyclotomic* half —
`‖ζ_{p^n} − 1‖ < 1` — is the project's `norm_sub_one_lt`. The target lemma is
precisely **(a) ∘ (b)**.

Generality dimensions where the literature varies:
- the *ambient ring* for half (a): seminormed ring → normed ring → Banach
  ring; mathlib uses the most general (`SeminormedRing`).
- the *cyclotomic input* half (b): any nonarchimedean field of residue char
  `p` (this is the `norm_sub_one_lt` generality question — handled in that
  decl's own report, verdict `YES-but-generalise-first`).

Disagreement with the literature: **none.** The Lean form is exactly the
standard topological-nilpotence statement, unfolded.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): the corollary is the composite of
(a) the seminormed-ring fact `‖x‖<1 ⇒ x^n→0` and (b) the cyclotomic norm bound.
As a *statement*, the right-hand object is `IsTopologicallyNilpotent (ζ−1)`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` + `[IsUltrametricDist L]` + `[NormedAlgebra ℚ_[p] L]` | `p`-adic value field | same hypothesis cluster as `norm_sub_one_lt` | yes, but **inherited** | These hypotheses are only used *through* `norm_sub_one_lt`; the corollary itself needs nothing beyond what that lemma needs. Any weakening belongs to `norm_sub_one_lt`'s report, not here. |
| 2 | `hζ : IsPrimitiveRoot ζ (p ^ n)`, `hn : 1 ≤ n` | primitive `p^n` root, `n≥1` | the cyclotomic input | NO (for this corollary) | same hypotheses as the supply lemma; not independently weakenable. |
| 3 | conclusion `Tendsto ((ζ-1)^·) atTop (𝓝 0)` | unfolded tendsto | `IsTopologicallyNilpotent (ζ−1)` (defeq) | **reformulation, not weakening** | see Phase 4c — this is the idiom question. |

This corollary introduces **no hypotheses of its own** beyond the cyclotomic
ones, and every typeclass it carries is forwarded verbatim to
`norm_sub_one_lt`. There is therefore nothing to weaken *at this level* — the
generality question lives entirely in the supply lemma `norm_sub_one_lt`.

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** *as a corollary of `norm_sub_one_lt`*
— it forwards exactly that lemma's hypotheses and adds the seminormed-ring
tendsto step, which is already mathlib's most general form. There is no
weakening axis intrinsic to this lemma (the weakening axes belong to
`norm_sub_one_lt`).
Number of weakening opportunities found (intrinsic to this lemma): 0.
Proposed restatement: none on generality grounds.
Cost of restatement: n/a.

(Because Phase 4b says MAXIMALLY GENERAL, Phase 7 considers YES-add-as-is *or*
the NO buckets, and 4c is run to check for a modernisation flip.)

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | no | — | the hypotheses are already typeclasses; no bundled preamble to convert. |
| 2 | sequences/metric → filters/topological? | partial — **already done** | the conclusion already uses `Tendsto … atTop (𝓝 0)` (filter form), not an `∀ε∃N` sequence statement | already maximally filter-idiomatic. |
| 3 | construction → universal-property class? | no | — | no object is constructed. |
| 4 | set-with-closure-predicate → bundled substructure? | **yes, weakly** | the conclusion `Tendsto ((ζ-1)^·) atTop (𝓝 0)` **is defeq** to `IsTopologicallyNilpotent (ζ-1)`, the bundled mathlib predicate (`Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:46`) | composes with `IsTopologicallyNilpotent.add` / `.mul_left` / `.mul_right` / `.map`, and with `IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds`; matters because the docstring *already says* "topologically nilpotent" |
| 5 | vector-space/field-specific → weaken typeclasses? | no (here) | — | the typeclass weakening lives in `norm_sub_one_lt`, not this corollary. |
| 6 | 1-categorical → higher-categorical? | no | — | no categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general monoid/group? | no | — | `k : ℕ` is the natural index for `atTop`-limits of powers; nothing to generalise. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (row 4) — state the conclusion as
`IsTopologicallyNilpotent (ζ - 1)` rather than the unfolded
`Tendsto ((ζ-1)^·) atTop (𝓝 0)`.

- Proposed mathlib-idiomatic restatement (conclusion only):
  ```lean
  theorem IsPrimitiveRoot.isTopologicallyNilpotent_sub_one {ζ : L} {n : ℕ}
      (hζ : IsPrimitiveRoot ζ (p ^ n)) (hn : 1 ≤ n) :
      IsTopologicallyNilpotent (ζ - 1) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt hn)
  ```
  (proof unchanged — defeq).
- Cost: **CHEAP** (defeq; the existing proof term type-checks at the new type).
- Mathlib downstream this enables: the `IsTopologicallyNilpotent` algebra
  (`.add`, `.mul_left`, `.mul_right`, `.map`, `.exists_pow_mem_of_mem_nhds`).
- Real mathematical improvement: it names the property the docstring already
  claims, instead of leaving it as an anonymous limit a reader must recognise.

**Crucially, this idiom note does NOT flip the verdict to
YES-but-generalise-first.** The Bourbaki-2.0 honesty bar requires the
modernisation to be a *new mathlib contribution*. Here it is not: mathlib
**already has** both `IsTopologicallyNilpotent` *and* the one-call route to it
(`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`). The idiom point is a
**project-side** cleanup (state the bundled predicate, or inline at the call
sites), not an upstream lemma. The mathlib-worthy half is the *supply* lemma
`norm_sub_one_lt`; this `tendsto` corollary on top of it remains composable
from mathlib in one call (Phase 6). So 4c feeds Phase 7's *refactor plan*, not a
YES bucket.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths, so the six-row risk table is skipped.

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `IsPrimitiveRoot.tendsto_pow_sub_one`

```
[A] Lean-Finder       n/a — Lean-Finder MCP not installed; substituted with [D] grep over the pinned mathlib tree.
[B] Loogle            n/a — Loogle MCP not installed; type-pattern intent ("IsPrimitiveRoot _ (p^n) → Tendsto ((ζ-1)^·) atTop (𝓝 0)") executed as [D] grep instead.
[C] LeanSearch        n/a — LeanSearch MCP not installed; NL intent ("powers of (root of unity minus one) tend to zero p-adically") executed as web lit search (Phase 3) + [D] grep.
[D] Grep mathlib src  searched: `IsPrimitiveRoot.*(tendsto|nilpotent|nhds.*0|pow_sub_one|sub_one.*norm)`, `tendsto_pow_atTop_nhds_zero*`, `IsTopologicallyNilpotent.*(norm|lt_one|of_norm)`   → see results below
[E] Name pattern      searched: `tendsto_pow_sub_one`, `IsPrimitiveRoot.norm_sub_one_lt` over mathlib tree   → no hits in mathlib (both are project-local)
```

Searched for both:
- the user's current form (`tendsto … (𝓝 0)` for `(ζ_{p^n}−1)`): **no
  combined lemma in mathlib.** Mathlib's `IsPrimitiveRoot` p-power lemmas
  (`IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two`,
  `…_of_prime_ne_two`, `…_two`, `…_eq_prime_pow_of_ne_zero`, all in
  `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`) compute the **field
  norm** `Algebra.norm` of `ζ^s − 1` — a *different object* from the analytic
  norm `‖·‖` and unrelated to the limit statement.
- the literature-standard / modern-idiom form (`IsTopologicallyNilpotent (ζ−1)`):
  `IsTopologicallyNilpotent` exists at
  `Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:46`, defined as
  `Tendsto (a ^ ·) atTop (𝓝 0)` — **so the target's conclusion is defeq to it**
  — but **no `IsPrimitiveRoot`-specific instance and no
  `IsTopologicallyNilpotent.of_norm_lt_one` constructor** exists in mathlib.

Building blocks found in mathlib:
- **`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`**
  (`Mathlib/Analysis/SpecificLimits/Normed.lean:221`):
  `{R} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0)`.
  Gives the conclusion verbatim from a `‖·‖ < 1` hypothesis.
- The `‖ζ − 1‖ < 1` hypothesis is **not** in mathlib — it is supplied by the
  project's own `IsPrimitiveRoot.norm_sub_one_lt`
  (`Coefficients.lean:151`), confirmed absent from the mathlib tree by grep.

**Concluded:** "found building blocks
(`tendsto_pow_atTop_nhds_zero_of_norm_lt_one` + the project's
`IsPrimitiveRoot.norm_sub_one_lt`); a single chained call yields our form. No
combined `(ζ_{p^n}−1)`-tendsto lemma exists in mathlib (all methods exhausted,
plus the `IsTopologicallyNilpotent` idiom form)."

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `IsPrimitiveRoot.tendsto_pow_sub_one`

Internal use count: **0** (no qualified `IsPrimitiveRoot.tendsto_pow_sub_one`
and no dot-notation `.tendsto_pow_sub_one` usages anywhere in the repo outside
the declaring line `Coefficients.lean:200`).
External-to-file callers: **0 distinct files.**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none)           | — the wrapper is never invoked    |

Inline-derivation grep — was the equivalent re-derived elsewhere **without**
using `tendsto_pow_sub_one`? **Yes — three independent sites**, all using the
identical 1-call pattern `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (…)`:

| Site | Excerpt | What it proves |
|------|---------|----------------|
| `Interpolation/Twist.lean:169` (`tendsto_pow_pow_sub_one`) | `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_pow_sub_one_lt_one hζ c)` | "`ζ^c − 1` is topologically nilpotent for `ζ ∈ μ_{p^n}`" — a **near-twin** of the target (docstring nearly identical), built inline, bypassing the wrapper |
| `Interpolation/Branches.lean:268` | `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (h1.trans_lt h2)` | powers of an element of `pℤ_p` tend to 0 |
| `Interpolation/Branches.lean:402` | `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simp)` | `(0:ℤ_[p])^· → 0` |

### What the call-sites pattern tells you

Per the Phase 6.0.1 table: **K = 0 internal uses, AND the same statement is
re-derived inline at ≥1 site** → "it's a wrapper consumers bypass; verdict leans
NO-composable-from-mathlib (or NO-mathlib-has-it if a mathlib alternative
exists)." Here there is no mathlib alternative for the `‖ζ−1‖<1` half (that half
is the project's own lemma), so the lean is **NO-composable-from-mathlib**. The
`Twist.lean:169` near-twin is especially telling: a sibling author proving the
same kind of fact reached for the raw 1-call composition rather than this
wrapper — strong evidence the wrapper carries no API weight.

### Composition check

Can `IsPrimitiveRoot.tendsto_pow_sub_one` be derived from mathlib in ≤3 chained
calls?

Attempt 1: `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt hn)`
- Mathlib decls used: `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` (1 mathlib call).
- Project decls used: `IsPrimitiveRoot.norm_sub_one_lt` (supplies the `‖ζ−1‖<1` argument).
- Result: **succeeds** — this is literally the proof body (`Coefficients.lean:203`).
- Notes: one mathlib call applied to one project lemma. Per the Phase-6
  heuristics table, `Foo.bar (Bar.baz hx)` (a single function call) is
  **composable**. No `rw`/`ring_nf`/`aesop` glue; no chain of `have`s.

**Conclusion: COMPOSABLE.** The composition is `≤1` mathlib call (applied to the
project's own norm bound), well inside the 3-call budget.

---

## PHASE 7 — Verdict

## Verdict: `IsPrimitiveRoot.tendsto_pow_sub_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the statement is the standard "topologically
  nilpotent" predicate, defeq to mathlib's `IsTopologicallyNilpotent (ζ−1)`;
  the two pieces (`‖x‖<1 ⇒ x^n→0`, decades-old seminormed-ring fact; and
  `‖ζ_{p^n}−1‖<1`, the project's `norm_sub_one_lt`) are both standard.
- Generality analysis (Phase 4): MAXIMALLY GENERAL as a corollary (no intrinsic
  weakening axis); Phase 4c found a modern idiom (`IsTopologicallyNilpotent`)
  but it is a *project-side* reformulation, **not** an upstream contribution
  (mathlib already has the predicate and the one-call route to it).
- Mathlib search (Phase 5): building blocks found
  (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`,
  `Mathlib/Analysis/SpecificLimits/Normed.lean:221`); no combined lemma; the
  `‖ζ−1‖<1` half is the project's own `norm_sub_one_lt` (absent from mathlib).
- Composition check (Phase 6): **COMPOSABLE** — the proof body is itself the
  1-call composition; K = 0 internal uses; 3 inline re-derivations of the same
  pattern elsewhere.

**Rationale.**
This theorem is the topological-nilpotence corollary that sits one line below
its supply lemma, and its entire proof is `tendsto_pow_atTop_nhds_zero_of_norm_lt_one
(hζ.norm_sub_one_lt hn)` — a single mathlib call applied to the project's own
norm bound. Mathlib supplies the *only* genuinely-general half (the
seminormed-ring fact that an element of norm `< 1` has powers tending to `0`),
and it even supplies the bundled predicate `IsTopologicallyNilpotent` that the
docstring is gesturing at. What mathlib does *not* have — `‖ζ_{p^n}−1‖<1` — is
not this lemma but its dependency `norm_sub_one_lt`, which is assessed
separately and is the project's real mathlib-worthy contribution
(`YES-but-generalise-first`). Bolting a one-call `tendsto` wrapper on top of
`norm_sub_one_lt` does not produce a second mathlib lemma: anyone who has the
norm bound writes the limit in one call, which is exactly what three other
project sites already do.

The decisive evidence is the call-site pattern. The wrapper has **zero**
consumers, while the identical 1-call composition is re-derived inline at three
places — most strikingly `Twist.lean:169` (`tendsto_pow_pow_sub_one`), a
near-twin lemma with an almost identical docstring ("`ζ^c − 1` is topologically
nilpotent") that reaches straight for
`tendsto_pow_atTop_nhds_zero_of_norm_lt_one (...)` rather than this wrapper.
That is the textbook NO-composable signature from the Phase 6.0.1 table:
`K = 0` plus inline re-derivation elsewhere. The Phase-4c idiom note
(`IsTopologicallyNilpotent`) does not rescue a YES verdict, because the
honesty bar requires a *new* organisational contribution and mathlib already
owns both the predicate and the route to it; the idiom is a project cleanup,
folded into the refactor plan below.

**WHY not (refactor-actionable detail).**
Mathlib has the building block; the user's form is a 1-call composition applied
to the project's own `norm_sub_one_lt`. No new mathlib lemma is justified.

Mathlib building blocks:
- `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`
  (`Mathlib/Analysis/SpecificLimits/Normed.lean:221`) — for any `SeminormedRing`,
  `‖x‖ < 1 → Tendsto (x ^ ·) atTop (𝓝 0)`.
- (idiom, optional) `IsTopologicallyNilpotent`
  (`Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:46`) — the bundled
  predicate the conclusion is defeq to.

Project building block (not mathlib's): `IsPrimitiveRoot.norm_sub_one_lt`
(`projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:151`).

Composition sketch (≤3 lines — this is literally the current proof):
```lean
example {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) (hn : 1 ≤ n) :
    Tendsto ((ζ - 1) ^ ·) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt hn)
```

Call sites in our project (from Phase 6.0): **K = 0**.

Refactor plan:
1. **Do not upstream `tendsto_pow_sub_one` to mathlib.** It is a one-call
   corollary of the project's `norm_sub_one_lt`; mathlib's
   `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` already supplies the limit step.
2. **Project-internal (optional cleanup, not a mathlib action):** because the
   wrapper has zero call sites, consider **deleting** it and letting future
   consumers write the one-liner directly (as `Twist.lean:169`,
   `Branches.lean:268,402` already do). *If* a stable named handle is wanted,
   restate it in the mathlib idiom as
   `IsPrimitiveRoot.isTopologicallyNilpotent_sub_one : … → IsTopologicallyNilpotent (ζ - 1)`
   (same one-line proof, defeq) so it composes with mathlib's
   `IsTopologicallyNilpotent` API — and consider unifying it with the near-twin
   `Twist.lean:169 tendsto_pow_pow_sub_one`. This is a `/cleanup`-lane decision,
   not a mathlib PR.
3. **The mathlib action lives on the dependency**, not here: pursue
   `IsPrimitiveRoot.norm_sub_one_lt` (verdict `YES-but-generalise-first`) for
   upstreaming. If/when that lands in mathlib, a downstream user gets this
   `tendsto`/`IsTopologicallyNilpotent` statement in one call with no extra
   lemma.

Next action: keep `tendsto_pow_sub_one` out of any mathlib PR; (optionally)
inline-or-idiom-ise it project-side via `/cleanup`; focus mathlib effort on the
supply lemma `norm_sub_one_lt`.

---

## Next step

Keep `IsPrimitiveRoot.tendsto_pow_sub_one` **out of mathlib** — it is a 1-call
composition of mathlib's `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` with the
project's own `norm_sub_one_lt`, has zero call sites, and is already re-derived
inline at three other project locations. Project-side (a `/cleanup`-lane
decision, not a mathlib PR): either delete the unused wrapper and let consumers
write the one-liner, or restate it in mathlib's idiom as
`IsTopologicallyNilpotent (ζ - 1)` (defeq, same proof) and unify it with the
near-twin `Twist.lean:169`. Direct the actual mathlib effort at the dependency
`IsPrimitiveRoot.norm_sub_one_lt` (verdict `YES-but-generalise-first`).
