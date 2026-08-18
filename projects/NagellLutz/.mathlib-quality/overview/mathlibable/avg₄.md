# /mathlibable report — `EllSequence.avg₄`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — `avg₄ a b c d := (a + b + c + d) / 2` is a one-line,
project-internal proof abbreviation over `ℤ`. It *is* mathlib's integer division; it has no
named-concept status in the literature, no external consumers, and no Phase-2b exemption. Inline
it (or keep it as a private helper that travels with the un-upstreamed elliptic-net extension).

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `EllSequence.avg₄`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:214`
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, `complEDS`, and (in the AINTLIB fork only) the `addMulSub`/`rel₄`/`net`
  four-index "elliptic net" machinery and its index-transformation argument. `avg₄` lives in that
  fork-only extension.

---

### Statement (Phase 1)

`EllSequence.avg₄` is **a definition**: the half-sum (floor) of four integers.

> Given `a, b, c, d : ℤ`, `avg₄ a b c d := (a + b + c + d) / 2`, using integer (floor / `Int.ediv`)
> division by 2.

Docstring: *"The average of four indices."*

Variables / typeclasses involved (Lean side):
- `a b c d : ℤ` — four integer **indices** of an elliptic-net relation (section `variable (a b c d : ℤ)`).
- No typeclasses; the codomain is `ℤ` concretely.

Hypotheses (Lean side): none on the definition itself.

Conclusion (math): the integer `⌊(a+b+c+d)/2⌋`. When `a,b,c,d` share a parity (so `a+b+c+d` is even),
this equals the exact half-sum, and `2·avg₄ = a+b+c+d` (captured by the companion lemma
`HaveSameParity₄.avg₄_add_avg₄`).

Conclusion (Lean): n/a — definition. Type is `ℤ`.

**Mathematical role.** It is *not* an "average" in the arithmetic-mean sense (that would be `/4`). It
is the **center / half-sum** used to translate four same-parity indices to a canonical frame: one
sets `m := avg₄ a b c d` and studies the shifted indices `m - a, m - b, m - c, m - d`, turning a
`net`/`rel₄` relation into the normalized `addMulSub₄` form (`addMulSub_transf`, `rel₄_transf`,
`strictAnti₄_transf`). Pure proof-engineering device.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line arithmetic helper `def`; not a named structure, not a `## Main` result, not a
person/place theorem. It is a private notational convenience inside one proof argument.

(Literature width was still run at full EXHAUSTIVE breadth below.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`(a + b + c + d) / 2`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence                                                                                          |
|-----------------------------------|----------|---------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                 | **no**   | The def is actively *unfolded* — `rw [avg₄, …]` at line 493 of the declaring file. Far from being a sealed defeq barrier, the proofs rely on unfolding it. No `@[reducible]`/`@[irreducible]` discipline is in play. |
| Avoid typeclass diamonds          | **no**   | The body is a bare `ℤ`-valued expression. No instance is declared, no typeclass-search path is anchored; nothing can collide. |
| Mark semantic intent / API name   | **no**   | The only "consumer" is the same file's own transformation proof; the name buys local readability, not a stable downstream API surface. The companion lemma `avg₄_add_avg₄` is likewise internal. No decl outside the declaring file (and its sibling forks) depends on the name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION**.
→ Carried into Phase 7: verdict biased toward `NO-composable-from-mathlib` / `NO-mathlib-has-it`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (surrounding concept)  | `"elliptic divisibility sequence" "elliptic net" four index relation average of indices Stange`        | partial | Confirms the four-index net recurrence `W(p+q+s)W(p−q)W(r+s)W(r) + … = 0` (Stange) | The *relation* is standard; **no name for `(a+b+c+d)/2`** surfaced. Sources: Stange "Elliptic nets and elliptic curves" (arXiv:0710.1316); Stange EDS/elliptic-net formulary; Wikipedia "Elliptic divisibility sequence". |
|  2 | WebSearch (most-general / generic)| `arithmetic mean of four integers definition (a+b+c+d)/2 half-sum notation mathematics`                 | no   | Arithmetic mean of four numbers is `(a+b+c+d)/4`       | Search explicitly notes `(a+b+c+d)/2` is **not** the arithmetic mean and that "half-sum notation" is **not standard** terminology. Confirms there is no named generic concept. |
|  3 | WebSearch (named-after / aliases)| `Stange elliptic nets symmetric function four indices proof transformation Ward elliptic relation`     | partial | Ward's relation / Stange "basis transformation formula" for nets | The index-transformation *step* exists in Stange/Ward (matrix transformation of nets), but the **half-sum centering scalar is an implementation detail, never a named primitive**. Sources: Stange "Tate Pairing via Elliptic Nets" (eprint 2006/392); "On Symmetries of Elliptic Nets" (arXiv:1408.6623). |
|  4 | ChatGPT MCP                      | "Is `(a+b+c+d)/2` a standard named concept in EDS/elliptic-net literature; is it worth a library def; is there a more general primitive?" | **n/a** | —                                                      | **MCP unavailable** (Codex backend errored, as task warned). Compensated by extra WebSearch generality levels (#1–#3) + direct mathlib source grep + the Phase-6 composition reasoning. |
|  5 | Local references                 | `ls / grep projects/NagellLutz/.mathlib-quality/references/`                                            | n/a  | directory absent                                       | No project references dir — recorded n/a per protocol. |
|  6 | nLab                             | "average / half-sum of integer indices" relevance                                                      | n/a  | —                                                      | Not a categorical concept; `(a+b+c+d)/2` is an elementary arithmetic expression with no nLab entry. Recorded n/a with reason. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                                      | Not categorical. n/a. |
|  8 | Stacks Project                   | half-sum of indices / elliptic net                                                                     | n/a  | —                                                      | Elliptic divisibility sequences / elliptic nets are not in scope of the Stacks Project (scheme-theoretic alg. geom.), and this is a bare-ℤ helper. n/a with reason. |
|  9 | MathOverflow / Math.SE           | (covered by WebSearch #2 generic sweep)                                                                | no   | —                                                      | No MO/MSE thread names a "half-sum of four indices" primitive; generic `(a+b+c+d)/2` is trivial. |
| 10 | recent arXiv (last 5 yr)         | elliptic nets symmetries / valuations (arXiv:1408.6623, 1702.08102, 2512.09601, 2604.05280 surfaced)   | partial | Elliptic-net symmetry/transformation results          | The modern literature still treats the centering offset as an unnamed computational step, never a reusable named quantity. |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels (surrounding
concept / most-general arithmetic / named-after); local refs, nLab, Stacks, nCatLab, MO/arXiv each
checked or recorded n/a with a reason. ChatGPT MCP genuinely unavailable and compensated.

### Literature summary (Phase 3)

Concept identified as: **the half-sum (centering offset) of four integer indices** — i.e. `(a+b+c+d)/2`.
This is *not* a named mathematical concept. The arithmetic mean of four numbers is `(a+b+c+d)/4`;
`/2` here is a parity-specific device so that `2·avg₄ = a+b+c+d` and the four centered indices
`avg₄ − a, …, avg₄ − d` are integers summing nicely.
Sources agree on the standard form: **n/a — there is no standard form to agree on.** The literature
documents the *four-index net relation* (Ward/Stange) and the *existence* of index-transformation
arguments, but never names or reuses the half-sum scalar.
Most general standard form: **none exists**; `(a+b+c+d)/2` is an inline arithmetic expression.
Generality dimensions where the literature varies: n/a (no concept to generalize).
Disagreement with the literature: none — the literature simply has no opinion on this helper, which
itself signals it is too elementary/project-specific to be a named library entity.

---

### Generality analysis — `EllSequence.avg₄`

Literature-standard form (from Phase 3): **none** (not a named concept).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|----------------------------------|
| 1 | `a b c d : ℤ`          | four integers     | — (no literature concept) | n/a                 | The whole point is integer indices of an EDS; `ℤ` is the natural and only relevant domain. There is no meaningful "more general" domain — `(a+b+c+d)/2` only makes sense where floor-division-by-2 is intended, and the consuming proofs are intrinsically about `ℤ`-indexed sequences. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (vacuously — there is no more-general literature target;
`ℤ` is the intrinsic domain).
Number of weakening opportunities found: **0**.
Proposed restatement: none.
Cost of restatement: n/a.

Note: "maximally general" here is *not* a point in favour of inclusion — the form is maximal only
because the concept is too trivial to admit generalization. The decisive issue is one-liner-ness +
no consumers + composability, addressed below.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                             | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                       | no       | —                      | No structure here; bare function. |
|  2 | sequences/metric → filters/topology?                                                                  | no       | —                      | Finite arithmetic; no limits. |
|  3 | construction → universal-property class?                                                              | no       | —                      | A scalar, not an object with a UP. |
|  4 | set-with-closure-predicate → bundled substructure?                                                    | no       | —                      | No substructure. |
|  5 | vector-space/field-specific → weaken typeclass?                                                       | no       | —                      | Already over `ℤ`; nothing to weaken. |
|  6 | 1-categorical → higher-categorical?                                                                   | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                             | no       | —                      | The "average" needs `/2` (an `Invertible 2` or floor); a general additive group has neither. mathlib's actual half-sum primitive `midpoint` requires `Invertible 2`, which `ℤ` lacks — so `avg₄` cannot even be phrased as `midpoint`. Generalizing would *break* the floor-division semantics the proof depends on. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: This is an elementary integer floor-half-sum used as a local proof offset; there is
no contemporary mathlib formulation that improves its organisation, and the obvious "general" route
(`midpoint`, which needs `Invertible 2`) does not apply to `ℤ`.

---

### Diamond / defeq risk — `EllSequence.avg₄` (Phase 4.5, kind = `def`)

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond             | none    | No instance; produces a plain `ℤ`. Nothing enters typeclass search.                   |
| 2 | Reducibility leak             | low     | Not marked `@[reducible]`; semireducible. Body is one cheap arithmetic op, so even if unfolded by `simp`/`rfl` it is harmless (and the project *deliberately* unfolds via `rw [avg₄]`). |
| 3 | Non-canonical unfolding       | none    | `rw [avg₄]` exposes `(a+b+c+d)/2` exactly as written; no surprise.                     |
| 4 | Instance priority collision   | n/a     | Not an `instance`.                                                                    |
| 5 | Universe-polymorphism issues  | none    | Monomorphic (`ℤ → ℤ`).                                                                |
| 6 | Coercion ambiguity            | none    | No `CoeFun`/`CoeSort`.                                                                |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**. Top risks: none. (Risk is not the reason for the NO verdict; triviality +
composability is.)

---

### Mathlib search-status: `EllSequence.avg₄`

[A] Lean-Finder       (mathlib-index tool unavailable in this env)        n/a — tool not loadable here
[B] Loogle            `Int → Int → Int → Int → Int` half-sum pattern      n/a — tool not loadable; covered by source grep below
[C] LeanSearch        "average / half sum of four integers"               n/a — tool not loadable; covered by source grep below
[D] Grep mathlib src  `avg₄`, `avg4`, `avg`, `(_ + _ + _ + _) / 2`, `addMulSub`, `net` over whole `Mathlib/` tree | **no hits** for `avg₄`/`avg4`/`avg` anywhere; **no hits** for the four-summand half-sum pattern; AND the entire `addMulSub`/`rel₄`/`net` host machinery is **absent** from mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` |
[E] Name pattern      grep `def midpoint` / `average` in `Mathlib/`        Only `Mathlib/LinearAlgebra/AffineSpace/Midpoint.lean` `midpoint` (needs `Invertible 2`; does **not** specialize to `ℤ` floor-half-sum) |

Searched for both:
  - the user's current form `(a+b+c+d)/2 : ℤ` → not in mathlib.
  - any literature-standard form → none exists to search for (Phase 3).

Concluded: **not in mathlib** (name + pattern exhausted across the whole tree; the surrounding
four-index elliptic-net extension that would host it is itself not yet upstreamed — mathlib's EDS
file stops at `normEDS`/`complEDS`). The only related primitive, `midpoint`, requires `Invertible 2`
and does not cover the integer floor case.

---

### Call sites — `EllSequence.avg₄`

Internal use count (within the declaring file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, excluding the `def` at line 214): **12 occurrences across ~9 logical sites**, all inside the same `EllSequence` / `HaveSameParity₄` proof cluster.
External-to-file callers (genuine consumers, i.e. a *different* project importing NagellLutz): **0**.

| Caller file:line                                                      | Usage pattern (one-line excerpt)                                              |
|-----------------------------------------------------------------------|-------------------------------------------------------------------------------|
| …/LutzNagell/EllipticDivisibilitySequence.lean:232 (`avg₄_add_avg₄`)  | `avg₄ a b c d + avg₄ a b c d = a + b + c + d`                                 |
| …/EllipticDivisibilitySequence.lean:271–277 (`addMulSub_transf`)      | `addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧ …`|
| …/EllipticDivisibilitySequence.lean:281–294 (`rel₄_transf`, `strictAnti₄_transf`) | `rel₄ W (avg₄ a b c d - d) … |avg₄ a b c d - a|`; `… same.avg₄_add_avg₄`      |
| …/EllipticDivisibilitySequence.lean:493                               | `rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, …]` (unfold)|

Inline-derivation grep (was the equivalent re-derived elsewhere without using `avg₄`?):
  - The HasseWeil and NagellLutz `…Original.lean` hits are **byte-identical sibling forks** of the
    same source, **not** consumers — they each re-declare their own `avg₄`. So there are *three copies*
    of this def in the repo and **zero cross-project uses**.

**Signal:** matches the table row *"K = 0 external uses; purely internal to its own file; and the same
def is copy-pasted in sibling forks rather than imported"* → strong `NO` signal (it is a local proof
helper, not shared API). The internal uses keep it from being dead code, but they are all in the one
proof it was written for.

---

### Composition check (Phase 6)

Can `EllSequence.avg₄` be derived from mathlib in ≤3 chained calls? **It *is* a mathlib expression.**

Attempt 1: `avg₄ a b c d` **is literally** `(a + b + c + d) / 2`, i.e. `HAdd.hAdd`/`HDiv.hDiv` on `ℤ`
from mathlib's `Int` instances. No new definition is needed; the RHS is the composition.
  - Mathlib decls used: `Int` `Add`/`Div` instances (core/mathlib).
  - Result: **succeeds** — zero wrapper logic.

Its one companion fact composes in ≤1 mathlib call too:
  `avg₄_add_avg₄` = `(by rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd)` — i.e. it is
  exactly `Int.mul_ediv_cancel'` applied to the evenness witness. The line-493 use is
  `Int.ediv_lt_iff_lt_mul` applied directly. Both are mathlib `Int`-division lemmas used as-is.

Conclusion: **COMPOSABLE.** Wherever `avg₄ a b c d` appears, write `(a + b + c + d) / 2`; wherever
`avg₄_add_avg₄` is invoked, use `Int.mul_ediv_cancel'` on the parity/evenness witness.

---

## Verdict: `EllSequence.avg₄`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the four-index net relation is standard (Ward/Stange), but **no source
  names `(a+b+c+d)/2`**; it is not even the arithmetic mean (`/4`) — it is an unnamed parity-centering
  half-sum.
- Generality analysis (Phase 4): MAXIMALLY GENERAL only vacuously; no modern idiom applies (`midpoint`
  needs `Invertible 2`, which `ℤ` lacks).
- Mathlib search (Phase 5): **not in mathlib** (name + pattern exhausted; the host elliptic-net
  extension is itself un-upstreamed).
- Composition check (Phase 6): **COMPOSABLE** — it *is* `(a+b+c+d)/2`; its one lemma is
  `Int.mul_ediv_cancel'`.

**Rationale.**
`avg₄` is a one-line definitional abbreviation `(a + b + c + d) / 2 : ℤ` with no Phase-2b exemption: it
is not a defeq barrier (the proofs unfold it with `rw [avg₄]`), it anchors no typeclass instance, and
its name is local proof-readability rather than a stable API. The literature treats the half-sum as an
unnamed computational offset, so there is nothing of mathematical *content* to upstream — only a name
for an integer-division expression mathlib already provides. The single fact anyone needs about it,
`2 · avg₄ = a + b + c + d` under same-parity indices, is a one-call instance of mathlib's
`Int.mul_ediv_cancel'`. With zero external consumers (the only other copies are byte-identical sibling
forks, not importers), there is no API-stability argument for a named mathlib definition either.

**WHY not (refactor-actionable).**
Mathlib already provides every building block: integer `_ / 2` (`Int.ediv`) for the expression itself,
`Int.mul_ediv_cancel'` for `avg₄_add_avg₄`, and `Int.ediv_lt_iff_lt_mul` for the line-493 bound — all
of which the current proofs *already call directly*. The named `def` adds a layer with no payoff at
mathlib's bar. Note `midpoint` (`Mathlib/LinearAlgebra/AffineSpace/Midpoint.lean:46`) is **not** a
substitute: it requires `Invertible 2`, absent for `ℤ`, and would change floor semantics.

  Mathlib building blocks:
    - `(· / ·) : ℤ → ℤ → ℤ`  (integer floor division — core/`Mathlib` `Int` instances)
    - `Int.mul_ediv_cancel'`  (`Mathlib/.../Int` division API — discharges `avg₄_add_avg₄`)
    - `Int.ediv_lt_iff_lt_mul` (used as-is at the one inequality call site)
  Composition sketch (≤3 lines):
  ```lean
  -- the definition, inlined:
  example (a b c d : ℤ) : ℤ := (a + b + c + d) / 2
  -- its only lemma, from mathlib directly (h : (2 : ℤ) ∣ (a + b + c + d)):
  example (a b c d : ℤ) (h : (2 : ℤ) ∣ (a + b + c + d)) :
      (a + b + c + d) / 2 + (a + b + c + d) / 2 = a + b + c + d := by
    rw [← two_mul]; exact Int.mul_ediv_cancel' h
  ```
  Call sites in our project (from Phase 6.0): **0 external**, ~9 internal (all in the declaring file).
  Refactor plan: this decl should **not** be sent to mathlib as a standalone. Options, in order of
  preference:
    1. **Leave it as project-internal code** (private/local helper) — it is fine where it is; it just
       does not belong *in mathlib* as a public definition. If/when the `addMulSub`/`rel₄`/`net`
       elliptic-net extension is upstreamed, `avg₄` rides along as a `private`/file-local helper inside
       that PR, not as an independently named public API.
    2. **If trimming the fork for an upstream PR:** at each of the ~9 internal sites, inline
       `(a + b + c + d) / 2` for `avg₄ a b c d`, and replace `avg₄_add_avg₄`/the line-493 step with the
       direct `Int.mul_ediv_cancel'` / `Int.ediv_lt_iff_lt_mul` calls shown above (the proofs already
       invoke these lemmas, so the inlining is mechanical; mind the same-parity evenness witness
       `same.even_sum.two_dvd` that feeds `Int.mul_ediv_cancel'`).
  Next action: do **not** open a standalone mathlib PR for `avg₄`. Keep it local, or inline per the
  sketch when slimming the elliptic-net extension for upstreaming.

---

## Next step

Do not upstream `EllSequence.avg₄` on its own. It is a one-line `ℤ`-arithmetic abbreviation with no
external consumers and no named-concept status; it is `(a + b + c + d) / 2` and its sole lemma is
`Int.mul_ediv_cancel'`. Keep it as a project-internal/file-local helper (it travels inside the larger
elliptic-net extension if that is upstreamed), or inline the composition at its ~9 in-file call sites.
