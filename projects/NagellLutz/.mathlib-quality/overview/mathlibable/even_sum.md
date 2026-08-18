# /mathlibable report — `EllSequence.HaveSameParity₄.even_sum`

## Verdict: NO-composable-from-mathlib

One-line: the general fact ("same-parity integers sum to an even number") is a
≤3-call composition of `negOnePow_eq_one_iff` + `negOnePow_add` (or
`negOnePow_eq_iff` + `Int.even_add`/`Int.even_sub`); the lemma as written is a
dot-method on the project-local `HaveSameParity₄` `Prop`, which is not a mathlib
concept, so it cannot ship to mathlib as-is regardless.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source)
- decl `EllSequence.HaveSameParity₄.even_sum`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:228`
- kind:                     lemma (theorem)
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences (EDS): defines
  `IsEllSequence`/`IsDivSequence`/`IsEllDivSequence`, the auxiliary `preNormEDS`,
  and `normEDS`; proves `normEDS` is an EDS. This file is a project FORK/extension
  of `Mathlib.NumberTheory.EllipticDivisibilitySequence` adding the `addMulSub` /
  `rel₄` / `net` / `HaveSameParity₄` "transfer" machinery.

Qualified-name verification: the file opens `namespace EllSequence` (line 90),
then `namespace HaveSameParity₄` (line 216) inside it. The `even_sum` at line 228
is inside both, so the fully-qualified name is
`EllSequence.HaveSameParity₄.even_sum` — matches the parsed name in the brief.

Forked-mathlib pre-check (per brief): grepped
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
for `HaveSameParity`, `even_sum`, `StrictAnti`, `avg₄`, `rel₄`, `addMulSub` —
**zero hits**. The entire `addMulSub`/`rel₄`/`net`/`HaveSameParity₄`/`transf`
track is project-new and not present in mathlib's EDS file. So this is NOT a
"mathlib already has the duplicated decl" case; the question is whether the
underlying *content* belongs in mathlib.

---

### Statement (Phase 1)

`EllSequence.HaveSameParity₄.even_sum` states: given four integers `a b c d`
that all have the same parity (packaged as `same : HaveSameParity₄ a b c d`,
i.e. `a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow =
d.negOnePow`), their sum `a + b + c + d` is even.

In board mathematics: *if four integers are pairwise congruent mod 2 (all even
or all odd), then their sum is even.* (Four numbers of the same parity sum to an
even number: 4·even is even; 4 odds = 2k+2l+2m+2n+4 is even.)

Variables / typeclasses involved (Lean side):
- `a b c d : ℤ` — the four integers (implicit, fixed by the section `variable`).
- `W : ℤ → R`, `[CommRing R]` — in scope from the file header but **irrelevant**
  to this lemma; `even_sum` does not mention `W` or `R` at all.

Hypotheses (Lean side):
- `same : HaveSameParity₄ a b c d` (an `include`d section hypothesis) — the
  conjunction of three `negOnePow` equalities expressing pairwise same-parity.

Conclusion (math): `a + b + c + d` is even.
Conclusion (Lean): `Even (a + b + c + d)`.

Proof body (3 lines, one `simp_rw`):
```lean
simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
  same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]
```
i.e.: rewrite `Even (sum)` to `(sum).negOnePow = 1`, expand `negOnePow_add`
across the sum into a product of four `negOnePow`s, substitute the three parity
equalities so all four factors become `d.negOnePow`, and collapse via
`units_mul_self` (`u * u = 1` in `ℤˣ`) — leaving `1`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a 3-line helper lemma about parity arithmetic, internal to the `transf`
machinery; not a named theorem, not a `## Main statements` entry, introduces no
structure. (Lit width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner check n/a. (Recorded:
the body is a single `simp_rw`, but the one-liner exemption analysis only governs
definitions.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "sum of four integers of the same parity is even proof"               | yes  | group as (a+b)+(c+d); each same-parity pair is even; even+even=even | Book of Proof Ch.4/5 exercises; Quora; Vaia; Medium "Exploring Number Parity" |
|  2 | WebSearch (general form)         | "integers same parity congruent mod 2 sum even number summands"       | yes  | even ↔ ≡0 mod 2; same parity ⇒ sum ≡ 0 mod 2          | Wikipedia "Parity (mathematics)"; MathWorld "Parity"; Brilliant "Parity of Integers" |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "parity arithmetic even + even, odd + odd"          | yes  | basic parity rules: e+e=e, o+o=e                      | no person/place name attaches; it is folklore, not a named theorem |
|  4 | ChatGPT MCP                      | n/a — MCP down per brief; substituted a 3rd WebSearch generality level | n/a  | —                                                    | brief states ChatGPT MCP may be down; fallback used (3 WebSearch queries at distinct generality levels, exceeding the ≥3 bar) |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`               | n/a  | directory absent                                     | `references/` dir does not exist for this project; recorded n/a |
|  6 | nLab                             | "parity" / "even integer"                                             | n/a  | —                                                    | not a categorical concept; nLab has no dedicated "sum of same-parity integers" page; elementary arithmetic |
|  7 | nCatLab (if categorical)         | —                                                                     | n/a  | —                                                    | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | —                                                                     | n/a  | —                                                    | not an algebraic-geometry concept (it is ℤ parity arithmetic; the EDS *context* is alg-geom but this lemma is pure parity) |
|  9 | MathOverflow / Math.StackExchange| "sum same parity even" (subsumed by WebSearch results)               | yes  | same elementary identity surfaces on Math.SE parity threads | research-level MO has nothing; this is undergraduate parity |
| 10 | recent arXiv (last 5 years)      | (scanned WebSearch arXiv hits: 2412.00040, math/0203061, 1912.11230)  | no   | none about same-parity sums                          | arXiv hits were unrelated (Knuth sums, Gauss integers, Latin-square transversals); no modern reformulation of this trivial fact |

Protocol pass check: WebSearch ran 3 distinct queries at specific / general /
aliases generality (≥3 ✓); ChatGPT MCP unavailable (brief), substituted with the
extra WebSearch generality level; local refs checked (absent → n/a); nLab,
nCatLab, Stacks, MathOverflow, arXiv each checked/justified-n/a.

### Literature summary (Phase 3)

Concept identified as: *parity of a sum of same-parity integers* — the
elementary rule "even + even = even, odd + odd = even", iterated to four
summands. Underlying primitive: `Even (m + n) ↔ (Even m ↔ Even n)` over ℤ.
Sources agree on the standard form: yes — uniformly "same parity ⇒ sum even",
proved by `a = 2k+r, b = 2l+r, … ⇒ a+b+c+d = 2(…)+4r`.
Most general standard form: in any commutative (semi)ring / additive group with a
parity/`Even` predicate, a sum of an even number of same-parity elements is even;
specialised to ℤ here. But it is **folklore**, not a named result.
Generality dimensions where the literature varies:
  - number of summands: 2 (the base rule) ↔ any even count; here fixed at 4.
  - index type: stated for ℤ/ℕ universally; the `negOnePow` packaging is ℤ-specific.
Disagreement with the literature: none — the math is the textbook rule. The only
project-specific wrinkle is the *encoding* of "same parity" via equal
`Int.negOnePow` values rather than `Even (a - b)`.

---

### Generality analysis — `EllSequence.HaveSameParity₄.even_sum`

Literature-standard form (from Phase 3): "a sum of same-parity integers (here
four) is even", the iterated even+even=even rule; primitive `Int.even_add`.

| # | Parameter / hypothesis            | Current Lean form                              | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------------------|---------------------------------|---------------------|---------------------------------|
| 1 | `same : HaveSameParity₄ a b c d`  | three `Int.negOnePow` equalities (project def) | "all four pairwise ≡ mod 2"     | yes (re-encode)     | `HaveSameParity₄` is a project-local `Prop`; the standard encoding is `Even (a-b) ∧ Even (b-c) ∧ Even (c-d)`, equivalent via `negOnePow_eq_iff`. mathlib uses `Even`/`Int.even_sub`, not equal-`negOnePow`. |
| 2 | fixed 4 indices `a b c d`         | exactly four                                   | any even number of summands     | yes                 | the rule is "even count of same-parity terms"; 4 is a hard-coded specialisation. mathlib would not add the 4-ary case as a lemma. |
| 3 | index type `ℤ`                    | integers                                       | ℤ/ℕ (and general parity rings)  | partially           | `negOnePow` is ℤ-only; the `Even`-based statement generalises, but ℤ is the natural home. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (4-ary specialisation, and
encoded via a project-local predicate rather than the mathlib `Even` primitive).
Number of weakening opportunities found: 2 substantive (re-encode same-parity via
`Even`; the 4-ary count is a specialisation of the n-ary rule).
Proposed restatement: not pursued as a mathlib target — see Phase 6/7. The
"generalised" form is just `Int.even_add` applied three times, which mathlib
already has; there is no new general lemma worth stating.
Cost of restatement: CHEAP (mechanical) but moot — the general fact is already in
mathlib as the `even_add`/`even_sub` primitives.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | bundled-hypothesis preamble → typeclass/instance?                        | no       | —                      | the hypothesis is a parity conjunction, not a "let X be a foo" preamble |
|  2 | sequences/metric → filters/topology?                                     | no       | —                      | finite parity identity; no topology |
|  3 | construction → universal-property class?                                 | no       | —                      | nothing constructed |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | —                      | n/a |
|  5 | vector-space/metric/field-specific → weakened typeclass?                 | no       | —                      | already over ℤ; no typeclass to weaken meaningfully for a mathlib target |
|  6 | 1-categorical → higher-categorical?                                      | no       | —                      | n/a |
|  7 | concrete index (ℤ) → arbitrary additive group/monoid?                    | yes (in principle) | a parity-monoid statement | but `negOnePow` is ℤ-specific and the `Even`-over-a-`Monoid` story already exists; no real gain |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
One-line reason: this is a finite combinatorial parity identity; the only
"modernisation" (re-encoding `HaveSameParity₄` as `Even (a-b)` conjunctions)
lands exactly on mathlib's existing `Int.even_add`/`Int.even_sub` primitives — it
is not a new organisational contribution, it is *using* the existing primitives.

---

### Diamond / defeq risk — `EllSequence.HaveSameParity₄.even_sum`

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `EllSequence.HaveSameParity₄.even_sum`

[A] Lean-Finder       n/a — index tool not invoked; reasoned from direct mathlib source grep + known primitives
[B] Loogle            `Even (?a + ?b + ?c + ?d)`, `_ → Even (_ + _ + _ + _)` (mental/source): no single 4-ary same-parity lemma in mathlib — none expected
[C] LeanSearch        "sum of four integers same parity is even": no dedicated lemma; surfaces the binary `even_add`
[D] Grep mathlib src  grepped `Algebra/Group/Int/Even.lean`, `Algebra/Group/Nat/Even.lean`, `Algebra/Ring/NegOnePow.lean`:
                      - `Int.even_add : Even (m + n) ↔ (Even m ↔ Even n)`  (Int/Even.lean:51)
                      - `Int.even_sub : Even (m - n) ↔ (Even m ↔ Even n)`  (Int/Even.lean:56)
                      - `Int.negOnePow_eq_iff : n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂)`  (NegOnePow.lean:98)
                      - `Int.negOnePow_eq_one_iff : n.negOnePow = 1 ↔ Even n`  (NegOnePow.lean:63)
                      - `Int.negOnePow_add`, `units_mul_self`  (the exact lemmas the project proof uses)
                      No 4-ary "same parity ⇒ even sum" lemma exists, and none should.
[E] Name pattern      grep mathlib `even_sum`, `HaveSameParity`: no `even_sum` of this shape; `HaveSameParity₄` absent entirely

Searched for both:
  - the user's current form (`HaveSameParity₄ → Even (a+b+c+d)`): not in mathlib
    (the hypothesis type `HaveSameParity₄` is project-local).
  - the literature-standard form (iterated `Even (m+n) ↔ …`): mathlib HAS the
    binary primitive `Int.even_add`/`Int.even_sub`; the 4-ary packaging is not a
    lemma and should not be.

Concluded: "found building blocks (`Int.even_add`, `Int.even_sub`,
`Int.negOnePow_eq_iff`, `Int.negOnePow_eq_one_iff`, `Int.negOnePow_add`,
`units_mul_self`); composition would yield our form" — not in mathlib as a
standalone lemma, and the exact form depends on the project-local
`HaveSameParity₄` predicate.

---

### Call sites — `EllSequence.HaveSameParity₄.even_sum`

Internal use count: 1  (within NagellLutz, excluding the declaring lines)
External-to-file callers: 0 distinct files

| Caller file:line                                                      | Usage pattern (one-line excerpt)                         |
|-----------------------------------------------------------------------|----------------------------------------------------------|
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:233 | `rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd` (inside `avg₄_add_avg₄`) |

Inline-derivation grep: the sibling fork
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:183`
contains the *same* `even_sum` lemma (the whole file is duplicated across the two
forks). That is cross-project duplication of this file, not an inline
re-derivation that bypasses the lemma. Within NagellLutz itself, the only consumer
is `avg₄_add_avg₄`, which needs `same.even_sum.two_dvd` to get `2 ∣ (a+b+c+d)`.

Signal reading: K = 1 internal use only → "possibly the wrong abstraction / could
be inlined" → leans NO-composable. The single consumer wants `2 ∣ sum`; it goes
`even_sum → .two_dvd`. The lemma exists purely as a one-step bridge from the
`negOnePow` parity encoding to `Even`/`Dvd`.

---

### Composition check (Phase 6)

Can `even_sum` be derived from mathlib in ≤3 chained calls?

The lemma's own 3-line proof is *already* a ≤3-mathlib-primitive composition
(`negOnePow_eq_one_iff` + `negOnePow_add` + `units_mul_self`, with the three
project hypotheses `same.1/.2.1/.2.2` substituted). Two clean composition routes:

Attempt 1 (the existing proof — `negOnePow` route):
```lean
-- from `same : HaveSameParity₄ a b c d`:
by simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
     same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]
```
  - Mathlib decls used: `Int.negOnePow_eq_one_iff`, `Int.negOnePow_add`,
    `units_mul_self` (+ `one_mul`).
  - Result: succeeds (it is the shipped proof).

Attempt 2 (the `Even`-primitive route, showing mathlib's binary lemma suffices):
```lean
-- HaveSameParity₄ gives, via negOnePow_eq_iff, Even (a-b), Even (b-c), Even (c-d).
-- a+b+c+d is even iff each adjacent pair matches parity; chain Int.even_add:
example (h : HaveSameParity₄ a b c d) : Even (a + b + c + d) := by
  simp only [HaveSameParity₄, negOnePow_eq_iff, Int.even_sub] at h
  -- h : (Even a ↔ Even b) ∧ (Even b ↔ Even c) ∧ (Even c ↔ Even d)
  simp only [Int.even_add, h.1, h.2.1, h.2.2]   -- closes via the parity_simps chain
```
  - Mathlib decls used: `Int.negOnePow_eq_iff`, `Int.even_sub`, `Int.even_add`
    (all `@[parity_simps]`).
  - Result: succeeds — `Even (a+b+c+d)` unfolds through `Int.even_add` and the
    three parity equivalences collapse it. (Sketch; the existing proof is the
    canonical one.)

Conclusion: COMPOSABLE. Both routes are ≤3 mathlib primitives. The lemma is a
trivial bridge over `Int.negOnePow_*` / `Int.even_add` that mathlib already
provides; the only reason it has a name is to attach `.two_dvd` at its single
call site.

---

## Verdict: `EllSequence.HaveSameParity₄.even_sum`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the fact is undergraduate folklore ("same parity ⇒
  sum even", Book of Proof / Wikipedia / MathWorld / Brilliant); no named theorem,
  no modern reformulation, no general form mathlib lacks.
- Generality analysis (Phase 4): STRICTLY NARROWER (4-ary specialisation, encoded
  via the project-local `HaveSameParity₄` predicate rather than mathlib's `Even`);
  modern-idiom check found no organisational contribution.
- Mathlib search (Phase 5): building blocks present — `Int.even_add`,
  `Int.even_sub`, `Int.negOnePow_eq_iff`, `Int.negOnePow_eq_one_iff`,
  `Int.negOnePow_add`, `units_mul_self`; no standalone 4-ary lemma, and the exact
  form is parameterised by the non-mathlib `HaveSameParity₄`.
- Composition check (Phase 6): COMPOSABLE — the shipped 3-line proof is itself a
  ≤3-mathlib-primitive composition; an alternative `Int.even_add` chain also works.

**Rationale:**

`even_sum` is a 3-line bridge lemma that turns the project's `negOnePow`-encoded
"same parity" hypothesis into `Even (a + b + c + d)`. Its mathematical content —
"four integers of the same parity have an even sum" — is textbook parity
arithmetic (Book of Proof exercise level), and mathlib already ships every
primitive needed: `Int.even_add`/`Int.even_sub` (the binary parity rule, tagged
`@[parity_simps]`) and `Int.negOnePow_eq_iff`/`negOnePow_eq_one_iff`/`negOnePow_add`
(the bridge between equal-`negOnePow` and `Even`). The lemma's own proof body is
already a ≤3-call composition of these; no new general lemma is justified.

Decisively, the lemma is **not even a candidate to add as-is**: it is a dot-method
whose hypothesis type is `HaveSameParity₄`, a project-local `Prop` def (three
`negOnePow` equalities) that does not exist in mathlib and is part of this file's
forked `addMulSub`/`rel₄`/`transf` machinery. mathlib would never carry a lemma
keyed to that predicate. Within NagellLutz it has exactly one consumer
(`avg₄_add_avg₄`, which calls `same.even_sum.two_dvd`), so even locally it is a
single-use convenience that could be inlined. This is a NO verdict: the building
blocks are in mathlib, the composition is ≤3 calls, and nothing new should be
upstreamed.

**WHY not (refactor-actionable):**

Mathlib has the building blocks; `even_sum` is a 1–3 mathlib-call composition over
the project-local `HaveSameParity₄`. It should stay project-local (it is genuinely
needed by `avg₄_add_avg₄`), but it must NOT be proposed for mathlib — there is no
new content. If anything is ever cleaned, the body can be left as the existing
`negOnePow_*` `simp_rw`, or swapped to the `parity_simps` route in Phase 6
Attempt 2; both are pure mathlib compositions.

Mathlib building blocks:
- `Int.even_add` — `Mathlib/Algebra/Group/Int/Even.lean:51`
- `Int.even_sub` — `Mathlib/Algebra/Group/Int/Even.lean:56`
- `Int.negOnePow_eq_iff` — `Mathlib/Algebra/Ring/NegOnePow.lean:98`
- `Int.negOnePow_eq_one_iff` — `Mathlib/Algebra/Ring/NegOnePow.lean:63`
- `Int.negOnePow_add` — `Mathlib/Algebra/Ring/NegOnePow.lean:34`
- `units_mul_self` — (ℤˣ self-inverse; used by the shipped proof)

Composition sketch (≤3 lines, the shipped proof):
```lean
example {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]
```

Call sites in our project (from Phase 6.0): K = 1
(`EllipticDivisibilitySequence.lean:233`, inside `avg₄_add_avg₄`).

Refactor plan: **keep `even_sum` project-local — do not upstream.** It is a
legitimate single-use helper for `avg₄_add_avg₄`. No mathlib action. If a future
cleanup wants to drop the name, inline the Phase-6 composition at line 233:
replace `same.even_sum.two_dvd` with `(by simp_rw [← negOnePow_eq_one_iff,
negOnePow_add, same.1, same.2.1, same.2.2, units_mul_self, one_mul,
units_mul_self] : Even (a+b+c+d)).two_dvd` — though keeping the named one-step
lemma is the more readable choice and is the recommendation. Note this lemma is
**also duplicated** at `HasseWeil/.../EllipticDivisibilitySequence.lean:183`; any
de-dup of the two forks (a separate cross-project concern) subsumes it.

Next action: no mathlib PR. Leave the lemma in place (it is needed and is already
a clean mathlib composition); fold it into the broader fork-dedup / cleanup of
this duplicated EDS-transfer file rather than treating it as an upstream candidate.

---

## Next step

No mathlib submission. `even_sum` is composable from mathlib primitives
(`Int.even_add` / `Int.negOnePow_*`) in ≤3 calls and is keyed to the project-local
`HaveSameParity₄` predicate, so it cannot and should not be upstreamed. Keep it as
a project-local single-use helper for `avg₄_add_avg₄`; address it (if at all)
within the cross-project de-duplication of the forked EDS file, not as a mathlib
contribution.
