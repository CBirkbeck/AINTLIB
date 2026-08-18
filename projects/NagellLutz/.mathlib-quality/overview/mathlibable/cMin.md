# /mathlibable report — `EllSequence.cMin`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — `cMin a := dMin a + 2` (where `dMin a := if Even a then 0 else 1`)
is a one-line, project-internal `ℤ → ℤ` proof helper: the *smallest valid third index of the same
parity as `a`* used as the base case of an induction over the four-index elliptic relation. It is
`(if Even a then 0 else 1) + 2`, i.e. `(if Even a then 2 else 3)` — a two-call composition of
mathlib's `if Even · then · else ·` (`Int.even_or_odd`/`decide`) and `(· + 2)`. It has no
named-concept status in the literature, **zero external consumers** (the only other copy in the repo
is a byte-identical sibling fork in HasseWeil that re-declares its own `cMin`, not an importer), and
no Phase-2b exemption (the proofs actively *unfold* it with `rw [cMin]` / `simp_rw [cMin, dMin]`).
Keep it as a private/file-local helper that travels with the un-upstreamed elliptic-relation
extension, or inline it at its in-file call sites.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `EllSequence.cMin`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:384`
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, `complEDS`, and (in the AINTLIB fork only) the `addMulSub`/`rel₄`/`Rel₄OfValid`
  four-index "elliptic relation" machinery and its strong-induction proof that `normEDS` is elliptic.
  `cMin` lives in that fork-only extension (mathlib's EDS file stops at `normEDS`/`complEDS`).

---

### Statement (Phase 1)

`EllSequence.cMin` is **a definition**: given an integer `a`, the smallest integer that is `≥ 2`,
nonnegative, and has the **same parity as `a`**.

> Given `a : ℤ`, `cMin a := dMin a + 2`, where `dMin a := if Even a then 0 else 1`. Equivalently
> `cMin a = if Even a then 2 else 3`. It is the minimal possible *third* index `c` in the four-index
> elliptic relation `rel₄ W a b c d`, given the first index `a`, when the four indices are required
> to be nonnegative, share a parity, and be strictly decreasing. (Its companion `dMin a` is the
> minimal possible *fourth* index `d`; one always has `dMin a < cMin a`.)

Docstring: *"The minimal possible third index in the four-index elliptic relation given the first index."*

Variables / typeclasses involved (Lean side):
- `a : ℤ` — the **first index** of a four-index elliptic relation. No typeclasses; codomain is `ℤ`
  concretely.

Hypotheses (Lean side): none on the definition itself.

Conclusion (math): the integer `if Even a then 2 else 3`.

Conclusion (Lean): n/a — definition. Type is `ℤ`.

**Mathematical role.** `cMin`/`dMin` package the *base case of the strong induction* that proves the
four-index elliptic relation holds for `normEDS`. The induction (`rel₄_of_anti_oddRec_evenRec`,
`Int.strongRec` on the first index `a`) reduces the general relation `rel₄ W a b c d` to the
"minimal" instance `rel₄ W a' b (cMin a) (dMin a)`: the smallest same-parity valid pair of trailing
indices. Choosing `c = cMin a`, `d = dMin a` is exactly what makes the recurrences `OddRec` (parity
odd ⇒ `(c,d) = (3,1)`) and `EvenRec` (parity even ⇒ `(c,d) = (2,0)`) the right two leaves
(see lines 498/503: `simp_rw [cMin, dMin, if_pos ea]` / `if_neg nea`). Pure proof-engineering
device: a name for "the smallest admissible third index of the correct parity."

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line arithmetic helper `def` (`dMin a + 2`); not a named structure, not a `## Main`
result, not a person/place theorem. It is a private notational convenience supplying the base case
of one induction.

(Note: literature width was still run at full EXHAUSTIVE breadth below.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`dMin a + 2`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence                                                                                          |
|-----------------------------------|----------|---------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                 | **no**   | The def is actively *unfolded*: `rw [cMin, …]` at lines 391, 469, 493; `rw [cMin, dMin]` at 404; `simp_rw [cMin, dMin, …]` at 498, 503 of the declaring file. Far from a sealed defeq barrier, every proof relies on unfolding it. No `@[reducible]`/`@[irreducible]` discipline is in play. |
| Avoid typeclass diamonds          | **no**   | The body is a bare `ℤ`-valued expression (`dMin a + 2`). No instance is declared, no typeclass-search path is anchored; nothing can collide. |
| Mark semantic intent / API name   | **no**   | The only consumers are the same file's own induction (`rel₄_of_min₂`, `addMulSub_mem_nonZeroDivisors`, `rel₄_of_anti_oddRec_evenRec`) and the byte-identical HasseWeil fork that *re-declares* its own `cMin`. The name buys local readability for one proof, not a stable downstream API surface. No decl outside the declaring file (and its sibling fork) depends on the name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION**.
→ Carried into Phase 7: verdict biased toward `NO-composable-from-mathlib` / `NO-mathlib-has-it`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (surrounding concept)  | `elliptic divisibility sequence Ward four-index relation minimal index parity recurrence division polynomial` | partial | Confirms the **four-index relation** `W(m+n)W(m−n)W(r)² + W(m+r)W(m−r)W(n)² + W(r+n)W(r−n)W(m)² = 0` (Ward 1948); EDS determined by `W(1)…W(4)` (rank-1 Laurentness). | The *relation* and its base-determining-terms are standard; **no name for "the smallest admissible same-parity third index"** surfaced. Sources: Ward "Memoir on EDS"; Wikipedia "Elliptic divisibility sequence"; Stange arXiv:0710.1316; cmeds.pdf (Leiden). |
|  2 | WebSearch (most-general / generic)| `smallest nonnegative integer with given parity "if even then 0 else 1" indicator function mathematics named` | no   | Generic "parity function" / "parity bit" / Iverson-bracket material only | Search explicitly notes **no standard named function** for "0 if even, 1 if odd as a *value*"; it is an elementary `if Even` branch, not a named primitive. (mathlib has `Int.negOnePow` for the *sign* `(-1)^a`, but not a "minimal nonneg of this parity" scalar.) |
|  3 | WebSearch (named-after / aliases)| `minimal index same parity strictly decreasing tuple elliptic net Stange recurrence base case`         | partial | Stange elliptic-net recurrence over tuples `p,q,r,s`; `W(−v)=−W(v)`, `W(0)=0`; Laurentness/which-terms-determine-the-net | The induction's *existence* and the recurrence are standard (Stange/Ward); the **specific base-index selector is an implementation detail, never a named primitive**. Sources: Stange arXiv:0710.1316, arXiv:0803.0728; "Elliptic Net Algorithm Revisited" arXiv:2109.07050. |
|  4 | ChatGPT MCP                      | "Is `if Even a then 2 else 3` / 'smallest admissible same-parity index ≥2' a standard named concept in EDS / elliptic-net literature; worth a library def; is there a more general primitive?" | **n/a** | —                                                      | **MCP unavailable** (Codex backend down, as task warned). Compensated by extra WebSearch generality levels (#1–#3), direct mathlib source grep (Phase 5), and the fact that mathlib's *own* division-polynomial files use the identical `if Even` idiom inline without naming such a helper (see Phase 5 [D]). |
|  5 | Local references                 | `ls / grep projects/NagellLutz/.mathlib-quality/references/`                                            | n/a  | directory absent                                       | No project references dir (`.../NagellLutz/.mathlib-quality/references/` does not exist) — recorded n/a per protocol. |
|  6 | nLab                             | "smallest integer of given parity / minimal admissible index" relevance                                | n/a  | —                                                      | Not a categorical concept; `if Even a then 2 else 3` is an elementary arithmetic expression with no nLab entry. Recorded n/a with reason. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                                      | Not categorical. n/a. |
|  8 | Stacks Project                   | minimal same-parity index / elliptic net base case                                                     | n/a  | —                                                      | EDS / elliptic nets are out of scope of the Stacks Project (scheme-theoretic AG), and this is a bare-ℤ helper. n/a with reason. |
|  9 | MathOverflow / Math.SE           | (covered by WebSearch #2 generic sweep)                                                                | no   | —                                                      | No MO/MSE thread names a "smallest nonnegative integer of a given parity ≥ 2" primitive; generic `if Even` is trivial. |
| 10 | recent arXiv (last 5 yr)         | elliptic nets / explicit valuations (arXiv:2512.09601, 2503.15428, 2109.07050 surfaced)                | partial | Modern elliptic-net valuation/isogeny results          | The modern literature still treats the base-index choice for the recurrence as an unnamed computational step, never a reusable named quantity. |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels (surrounding
concept / most-general "named parity scalar" / named-after-base-case); local refs, nLab, Stacks,
nCatLab, MO/arXiv each checked or recorded n/a with a reason. ChatGPT MCP genuinely unavailable and
compensated.

### Literature summary (Phase 3)

Concept identified as: **the smallest nonnegative integer `≥ 2` with the same parity as `a`** — i.e.
`if Even a then 2 else 3` — serving as the base-case third index of the four-index-elliptic-relation
induction. (Its companion `dMin a = if Even a then 0 else 1` is the same idea for the fourth index.)
This is *not* a named mathematical concept. The literature names the **four-index relation** itself
(Ward/Stange) and the fact that an EDS is determined by `W(1)…W(4)`, but never names the scalar that
selects the minimal admissible same-parity index in an induction over that relation.
Sources agree on the standard form: **n/a — there is no standard form to agree on.** The relation and
its inductive structure are standard; the base-index selector is a formalisation-internal device.
Most general standard form: **none exists**; `if Even a then 2 else 3` is an inline arithmetic
expression.
Generality dimensions where the literature varies: n/a (no concept to generalize).
Disagreement with the literature: none — the literature simply has no opinion on this helper, which
itself signals it is too elementary/project-specific to be a named library entity. **Corroborating
evidence:** mathlib's *own* division-polynomial development (`DivisionPolynomial/Basic.lean`,
`Degree.lean`) uses the identical `if Even n then … else …` parity-branch idiom inline dozens of
times (e.g. `expDegree n := (n^2 - if Even n then 4 else 1)/2`, `expCoeff n := if Even n then n/2
else n`) and *never* factors out a named "minimal same-parity index" helper — exactly the editorial
choice mathlib would make here.

---

### Generality analysis — `EllSequence.cMin`

Literature-standard form (from Phase 3): **none** (not a named concept).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|----------------------------------|
| 1 | `a : ℤ`                | one integer       | — (no literature concept) | n/a                 | The whole point is an *integer index* of an EDS / elliptic relation, with `Even a` driving the parity branch. `ℤ` is the natural and only relevant domain; there is no meaningful "more general" domain because the construction is `(if Even a then 0 else 1) + 2`, which needs both a parity predicate and the literals `0,1,2` — only sensible over `ℤ` (or `ℕ`), and the consuming proofs are intrinsically `ℤ`-indexed. |

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
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                             | no       | —                      | The body branches on `Even a` and adds the literals `0/1/2`; a general additive group has no parity predicate and no canonical "2". The parity choice is intrinsic to EDS index arithmetic; generalising would be meaningless, not cleaner. mathlib's own division-polynomial files keep this branch inline over `ℤ`/`ℕ`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: This is an elementary integer parity-branch (`if Even a then 2 else 3`) used as the
base index of one induction; there is no contemporary mathlib formulation that improves its
organisation, and mathlib's existing division-polynomial code uses precisely this inline idiom rather
than a named helper.

---

### Diamond / defeq risk — `EllSequence.cMin` (Phase 4.5, kind = `def`)

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond             | none    | No instance; produces a plain `ℤ`. Nothing enters typeclass search.                   |
| 2 | Reducibility leak             | low     | Not marked `@[reducible]`; semireducible. Body is `dMin a + 2` (one cheap op atop a `if Even`), so even if unfolded by `simp`/`rfl` it is harmless — and the project *deliberately* unfolds it via `rw [cMin]`/`simp_rw [cMin, dMin]`. |
| 3 | Non-canonical unfolding       | none    | `rw [cMin]` exposes `dMin a + 2` exactly as written; `simp_rw [cMin, dMin, if_pos/if_neg]` then resolves the parity branch deterministically. No surprise. |
| 4 | Instance priority collision   | n/a     | Not an `instance`.                                                                    |
| 5 | Universe-polymorphism issues  | none    | Monomorphic (`ℤ → ℤ`).                                                                |
| 6 | Coercion ambiguity            | none    | No `CoeFun`/`CoeSort`.                                                                |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**. Top risks: none. (Risk is not the reason for the NO verdict; triviality +
no consumers + composability is.)

---

### Mathlib search-status: `EllSequence.cMin`

[A] Lean-Finder       (mathlib-index tool unavailable in this env)        n/a — tool not loadable here
[B] Loogle            `Int → Int` "min same-parity index" pattern         n/a — tool not loadable; covered by source grep below
[C] LeanSearch        "smallest integer of given parity ≥ 2"              n/a — tool not loadable; covered by source grep below
[D] Grep mathlib src  `cMin`, `dMin`, `if Even .* then 0 else 1`, `if Even .* then 2 else 3`, `addMulSub`, `Rel₄`, parity-min names over whole `Mathlib/` tree | **no hits** for `cMin`/`dMin` anywhere (the `findMin'` hits are unrelated `Mathlib/Data/Ordmap` BST code); **no hits** for a named "smallest same-parity index"; AND the entire `addMulSub`/`rel₄`/`Rel₄OfValid` host machinery is **absent** from mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (which stops at `normEDS`/`complEDS`). Notably, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` use the same `if Even n then … else …` idiom **inline** (e.g. `expDegree`, `expCoeff`, lines 156–186) and never name a `cMin`/`dMin` helper. |
[E] Name pattern      grep `def .*[Pp]arity.*[Mm]in` / `leastEven` / `smallestOdd` in `Mathlib/` | **no hits** — mathlib has no "minimal integer of a given parity" named definition. |

Searched for both:
  - the user's current form `if Even a then 2 else 3 : ℤ` → not in mathlib.
  - any literature-standard form → none exists to search for (Phase 3).

Concluded: **not in mathlib** (name + pattern exhausted across the whole tree; the surrounding
four-index elliptic-relation extension that would host it is itself not yet upstreamed — mathlib's EDS
file stops at `normEDS`/`complEDS`, and mathlib's division-polynomial files keep the analogous parity
branch inline rather than naming it).

---

### Call sites — `EllSequence.cMin`

Internal use count (within the declaring file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, excluding the `def` at line 384): **~16 occurrences across ~10 logical sites**, all inside the same `EllSequence` `Rel₄OfValid` induction cluster (lines 388–503).
External-to-file callers (genuine consumers, i.e. a *different* project importing NagellLutz): **0**.

| Caller file:line                                                      | Usage pattern (one-line excerpt)                                              |
|-----------------------------------------------------------------------|-------------------------------------------------------------------------------|
| …/EllipticDivisibilitySequence.lean:388 (`dMin_lt_cMin`)              | `dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two`                        |
| …/EllipticDivisibilitySequence.lean:390–399 (`negOnePow_cMin*`)      | `(cMin a).negOnePow = (dMin a).negOnePow` / `= a.negOnePow` (`rw [cMin, …]`)  |
| …/EllipticDivisibilitySequence.lean:403–404 (`addMulSub_mem_nonZeroDivisors`) | `addMulSub W (cMin a) (dMin a) ∈ R⁰ … rw [cMin, dMin]; split_ifs`     |
| …/EllipticDivisibilitySequence.lean:458–471 (`rel₄_of_min₂`)         | `(rel : … Rel₄OfValid W a' b (cMin a) (dMin a)) …`; `rw [… cMin …]`           |
| …/EllipticDivisibilitySequence.lean:493 (`rel₄_of_anti_oddRec_evenRec`) | `rw [avg₄, …, cMin]; linarith`                                            |
| …/EllipticDivisibilitySequence.lean:498, 503                          | `simp_rw [cMin, dMin, if_pos ea]` / `simp_rw [cMin, dMin, if_neg nea]` (unfold) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `cMin`?):
  - The **only** other `cMin` in the whole repo is
    `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:310`, which is a
    **byte-identical sibling fork** of this same source — it **re-declares its own `cMin`** (with the
    identical `dMin`/`addMulSub`/`rel₄`/`rel₄_of_min₂` cluster), it does **not** import NagellLutz's.
    So there are *two copies* of this def in the repo and **zero cross-project uses**.

**Signal:** matches the table row *"K = 0 external uses; purely internal to its own file; and the same
def is copy-pasted in a sibling fork rather than imported"* → strong `NO` signal (a local proof helper,
not shared API). The ~16 internal uses keep it from being dead code, but they are all in the one
induction it was written to support.

---

### Composition check (Phase 6)

Can `EllSequence.cMin` be derived from mathlib in ≤3 chained calls? **It *is* a 2-call mathlib expression.**

Attempt 1: `cMin a` **is literally** `(if Even a then 0 else 1) + 2`, i.e.
`ite (Even a) 0 1 + 2` over `ℤ`. The `if`/`ite` is `Decidable`-driven by mathlib's
`Int.even_or_odd` / `Int.decEq`-backed `Decidable (Even a)`; the `+ 2` is `HAdd.hAdd` on `ℤ`. No new
definition is needed — the RHS *is* the composition (equivalently the more-collapsed
`if Even a then 2 else 3`).
  - Mathlib decls used: `ite`/`Decidable (Even ·)` (`Int.even_or_odd`, core/`Mathlib`), `Int` `Add`
    instance, literals `0,1,2 : ℤ`.
  - Result: **succeeds** — zero wrapper logic.

The handful of *facts* anyone needs about `cMin` each compose in ≤2 mathlib calls too, exactly as the
existing proofs already do:
  - `dMin_lt_cMin` = `lt_add_of_pos_right _ zero_lt_two` (one mathlib lemma, used as-is at line 388).
  - `negOnePow_cMin_eq_dMin` = `Int.negOnePow_add` then `mul_one` (lines 390–391).
  - `addMulSub_mem_nonZeroDivisors` resolves by `rw [cMin, dMin]; split_ifs` then `mul_mem` (line 404).
  - The two base-case leaves are just `simp_rw [cMin, dMin, if_pos/if_neg]` collapsing the branch.

Conclusion: **COMPOSABLE.** Wherever `cMin a` appears, write `(if Even a then 0 else 1) + 2` (or its
companion `dMin a + 2` if `dMin` is kept); each accompanying fact is a direct one-/two-lemma mathlib
call the proofs already invoke.

---

## Verdict: `EllSequence.cMin`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the four-index elliptic relation is standard (Ward/Stange), but **no
  source names** the scalar `if Even a then 2 else 3` ("smallest admissible same-parity third index");
  it is a formalisation-internal base-case selector. mathlib's own division-polynomial files use this
  exact `if Even` idiom inline without naming it.
- Generality analysis (Phase 4): MAXIMALLY GENERAL only vacuously; no modern idiom applies (the body
  needs a parity predicate + the literals `0,1,2`, intrinsic to `ℤ` index arithmetic).
- Mathlib search (Phase 5): **not in mathlib** (name + pattern exhausted; the host elliptic-relation
  extension is itself un-upstreamed; analogous parity branches are kept inline in mathlib).
- Composition check (Phase 6): **COMPOSABLE** — it *is* `(if Even a then 0 else 1) + 2`; each fact
  about it is a direct 1–2-call mathlib lemma the proofs already use.

**Rationale.**
`cMin` is a one-line definitional abbreviation `dMin a + 2 = (if Even a then 0 else 1) + 2 : ℤ` with
no Phase-2b exemption: it is not a defeq barrier (the proofs unfold it with `rw [cMin]` /
`simp_rw [cMin, dMin]`), it anchors no typeclass instance, and its name is local proof-readability
rather than a stable API. The literature treats the choice of the minimal admissible same-parity index
in an induction over the elliptic relation as an unnamed computational detail — so there is nothing of
mathematical *content* to upstream, only a name for a two-term integer expression mathlib already
provides. Decisively, mathlib's *own* elliptic-curve division-polynomial development
(`DivisionPolynomial/Basic.lean`, `Degree.lean`) uses the identical `if Even n then … else …` idiom
inline dozens of times and never factors out a "minimal same-parity index" helper — the strongest
possible signal that mathlib's editorial standard keeps this inline rather than naming it.

With **zero external consumers** (the only other copy is a byte-identical HasseWeil sibling fork that
re-declares its own `cMin`, not an importer), there is also no API-stability argument for a named
mathlib definition. The decl is correct and useful *where it is* — it just does not belong in mathlib
as a standalone public definition.

**WHY not (refactor-actionable).**
Mathlib already provides every building block: the `Decidable (Even ·)` instance for the parity branch
(`Int.even_or_odd`), `ℤ` addition, and the integer literals — so the def *is* the composition. The
accessory lemmas the proofs need are mathlib one-liners they already call directly: `lt_add_of_pos_right`
(for `dMin_lt_cMin`), `Int.negOnePow_add` + `mul_one` (for `negOnePow_cMin_eq_dMin`), and `split_ifs` +
`mul_mem` (for `addMulSub_mem_nonZeroDivisors`). The named `def` adds a layer with no payoff at
mathlib's bar.

  Mathlib building blocks:
    - `ite` / `Decidable (Even a)` via `Int.even_or_odd`  (core/`Mathlib` — the parity branch)
    - `(· + ·) : ℤ → ℤ → ℤ`  (the `+ 2`)
    - `lt_add_of_pos_right`, `Int.negOnePow_add`, `mul_one`, `mul_mem`  (the accessory facts, used as-is)
  Composition sketch (≤3 lines):
  ```lean
  -- the definition, inlined (equivalently `if Even a then 2 else 3`):
  example (a : ℤ) : ℤ := (if Even a then 0 else 1) + 2
  -- its ordering fact, from mathlib directly (here dMin a is the same `if Even a then 0 else 1`):
  example (a : ℤ) : (if Even a then 0 else 1) < (if Even a then 0 else 1) + 2 :=
    lt_add_of_pos_right _ zero_lt_two
  ```
  Call sites in our project (from Phase 6.0): **0 external**, ~10 internal (all in the declaring file's
  `Rel₄OfValid` induction).
  Refactor plan: this decl should **not** be sent to mathlib as a standalone. Options, in order of
  preference:
    1. **Leave it as project-internal code** (private/file-local helper) — it is fine where it is; it
       just does not belong *in mathlib* as a public definition. If/when the
       `addMulSub`/`rel₄`/`Rel₄OfValid` elliptic-relation extension is upstreamed, `cMin` (and its
       companion `dMin`) ride along as `private`/file-local helpers inside that PR, not as
       independently named public API.
    2. **If trimming the fork for an upstream PR:** inline `(if Even a then 0 else 1) + 2` (or keep
       `dMin` and write `dMin a + 2`) at the ~10 internal sites, and replace each accessory lemma
       with the direct mathlib call shown above (the proofs already invoke these lemmas, so the
       inlining is mechanical; `cMin`/`dMin` are best assessed and handled together as a pair since
       `cMin := dMin + 2`).
  Note: `cMin` and `dMin` are a unit — any upstreaming/inlining decision should treat them together.
  Next action: do **not** open a standalone mathlib PR for `cMin`. Keep it local (with `dMin`), or
  inline the composition at its ~10 in-file call sites when slimming the elliptic-relation extension
  for upstreaming.

---

## Next step

Do not upstream `EllSequence.cMin` on its own. It is a one-line `ℤ`-parity-branch abbreviation
(`if Even a then 2 else 3`, written `dMin a + 2`) with no external consumers and no named-concept
status; it *is* `(if Even a then 0 else 1) + 2`, and each fact about it is a direct mathlib one-liner
(`lt_add_of_pos_right`, `Int.negOnePow_add`, `split_ifs`/`mul_mem`). Keep it as a project-internal /
file-local helper alongside `dMin` (it travels inside the larger elliptic-relation extension if that is
upstreamed), or inline the composition at its ~10 in-file call sites. mathlib's own division-polynomial
files keep exactly this `if Even` idiom inline — the editorial precedent is clear.
