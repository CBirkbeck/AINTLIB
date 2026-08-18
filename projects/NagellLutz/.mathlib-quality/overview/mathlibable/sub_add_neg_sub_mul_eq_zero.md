# /mathlibable report — `IsEllSequence.sub_add_neg_sub_mul_eq_zero`

## Verdict: BORDERLINE-needs-human

> One-line rationale: Net-new abstract-EDS API (not in pinned mathlib), but this
> single-use one-step helper's API grain (ship vs. inline/`private`) is a human call.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `IsEllSequence.sub_add_neg_sub_mul_eq_zero`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:665`
- qualified name:           `IsEllSequence.sub_add_neg_sub_mul_eq_zero`
  (VERIFIED: inside `namespace IsEllSequence`, opened at line 643; closed at line 702)
- kind:                     lemma
- has sorry:                no
- module docstring summary: Defines elliptic divisibility sequences (EDS) and constructs
  normalised EDSs from initial terms (file by David Angdinata, Apache-licensed — the same
  author as mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

**Fork situation (decisive context).** The pinned mathlib copy at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is **547 lines**
and ends at the `Map` section (`map_complEDS`). The project's file is **1667 lines** — it adds an
entire `namespace EllSequence` machinery (`addMulSub`, `rel₄`, `net`, `Rel₃`, `invarNum`,
`invarDenom`, …) and an entire `namespace IsEllSequence` API block (`oddRec`, `evenRec`, `zero`,
**`sub_add_neg_sub_mul_eq_zero`**, `neg`, `rel₄`, `net`, `invar`). **None of this block exists in
the pinned mathlib.** So the target is net-new abstract-EDS API, not a duplicate of an existing
mathlib decl. The same lemma appears verbatim (modulo `lia`/`omega` cosmetic differences) in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:542` and in the older
`EllipticDivisibilitySequenceOriginal.lean:637` — i.e. it is being developed in parallel across two
AINTLIB projects and is clearly bound for an upstream mathlib PR.

---

### Statement (Phase 1)

`IsEllSequence.sub_add_neg_sub_mul_eq_zero` states: for a commutative ring `R` and an **elliptic
sequence** `W : ℤ → R` (i.e. `W` satisfies the three-index relation `Rel₃(m,n,r)` for all integers),
and any `m, n, r ∈ ℤ`,

$$\bigl(W(m-n) + W\!\bigl(-(m-n)\bigr)\bigr)\cdot W(m+n)\cdot W(r)^2 \;=\; 0.$$

Equivalently (since the proof rewrites `-(m-n) = n-m`): `(W(m−n) + W(n−m))·W(m+n)·W(r)² = 0`.

This is the **symmetrisation step** in proving that an elliptic sequence is an *odd function*. The
defining relation `Rel₃(m,n,r)` is

$$W(m+n)\,W(m-n)\,W(r)^2 = W(m+r)\,W(m-r)\,W(n)^2 - W(n+r)\,W(n-r)\,W(m)^2.$$

Adding `Rel₃(m,n,r)` to `Rel₃(n,m,r)` (swap `m ↔ n`) makes the entire right-hand side cancel and
leaves `(W(m−n)+W(n−m))·W(m+n)·W(r)² = 0` on the left. The very next lemma, `IsEllSequence.neg`,
specialises this (with `W(1), W(2) ∈ R⁰`) to conclude `W(−k) = −W(k)`.

Variables / typeclasses (Lean side):
- `R : Type u`, `[CommRing R]` — the coefficient ring (arbitrary commutative ring).
- `W : ℤ → R` — the sequence.
- `(ell : IsEllSequence W)` — section hypothesis (the defining elliptic relation, `include`d).
- `(m n r : ℤ)` — the three free indices.

Hypotheses: only `ell : IsEllSequence W`. **No integral-domain or non-zero-divisor hypothesis at
this lemma.** (The `W 1, W 2 ∈ R⁰` hypotheses appear *after* this lemma, on `neg` and below.)

Conclusion (math): `(W(m−n) + W(n−m))·W(m+n)·W(r)² = 0`.
Conclusion (Lean): `(W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — an unnamed intermediate algebraic identity, a stepping stone to the
named result (oddness). Not a `## Main statement`, not named after a person/place, introduces no
new structure.

(Literature width still run EXHAUSTIVE.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (For the record the proof
body is 4 lines: a `congr(...)` of the relation with its swap, an `rw` to merge the distributive
factors, an `rw` to turn `-(m-n)` into `n-m`, and `convert … ; ring`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence is odd function W(-n)=-W(n) proof Ward"                         | yes  | EDS oddness `W₋ₙ = −Wₙ` is standard; this exact identity is not named | Wikipedia EDS; arXiv math/0402415 (Everest–Ward, sign of an EDS); Stange 0710.1316 |
|  2 | WebSearch (general / named-after)| "elliptic sequence W(m+n)W(m-n)W(r)^2 symmetry antisymmetric odd Stange elliptic nets"         | yes  | "for elliptic nets one always has `W(−v)=−W(v)` and `W(0)=0`" — **antisymmetry/oddness is the named property** | Stange, *Elliptic nets and elliptic curves* (0710.1316); EDS formulary |
|  3 | WebSearch (aliases)              | (covered by #1/#2: "elliptic net antisymmetry", "odd function", "Ward recurrence")             | yes  | same; the recurrence `W_{m+n}W_{m−n} = W_{m+1}W_{m−1}W_n² − W_{n+1}W_{n−1}W_m²` is the named object | the target is one `+`-of-two-instances step inside that recurrence |
|  4 | ChatGPT MCP                      | self-contained question: is the identity named, what is the named result, and at what generality | n/a  | — | **MCP down** (Codex exec failed — task flagged this; WebSearch + source evidence used as the sanctioned fallback) |
|  5 | Local references                 | `.mathlib-quality/references/` for NagellLutz                                                   | n/a  | — | no references dir present for this project; recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                              | n/a  | — | nLab has no EDS/elliptic-net page; not a category-theoretic concept |
|  7 | nCatLab                          | —                                                                                              | n/a  | — | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                              | n/a  | — | EDS/elliptic-sequence recurrences are not in Stacks' scope (no such tag) |
|  9 | MathOverflow / MSE               | "elliptic divisibility sequence odd antisymmetric proof"                                       | yes  | confirms oddness is the standard fact, derived from the Ward recurrence; the per-step identity is not separately quoted | consistent with #1/#2 |
| 10 | recent arXiv (last 5y)           | "elliptic net symmetries valuations" (1408.6623; 2512.09601)                                   | yes  | "On Symmetries of Elliptic Nets" treats `W(−v)=−W(v)` as a basic symmetry | the symmetrisation identity is subsumed, never named |

### Literature summary (Phase 3)

Concept identified as: the **symmetrisation / antisymmetry step** underlying the standard fact that
**an elliptic sequence (or net) is an odd function**, `W(−v) = −W(v)`.
Sources agree on the standard form: **yes** — oddness `W(−v)=−W(v)` is the named, universally cited
property (Stange 0710.1316; Wikipedia EDS; EDS formulary; Everest–Ward).
Most general standard form: the named theorem is "an elliptic sequence is odd". Our target is **not**
that theorem — it is the unnamed algebraic identity obtained by adding the defining relation to its
`m↔n` swap, which is the first half of the oddness proof; the named result is the *next* lemma
`IsEllSequence.neg`.
Generality dimensions where the literature varies:
  - coefficient ring: classical sources work over `ℤ` or a field/integral domain; the Lean form is
    over an arbitrary `CommRing R`. The target lemma itself needs **no** domain hypothesis — that is
    a genuine strengthening over the literature (the domain/non-zero-divisor condition is only needed
    to *divide out* `W(m+n)·W(r)²` in the downstream `neg`).
Disagreement with the literature: none. The literature simply doesn't name this intermediate step;
it names the conclusion (oddness).

---

### Generality analysis — `IsEllSequence.sub_add_neg_sub_mul_eq_zero`

Literature-standard target: "an elliptic sequence is odd, `W(−v)=−W(v)`" (a conclusion this lemma
*feeds*, it does not state it).

| # | Parameter / hypothesis        | Current Lean form            | Literature-standard form        | Weaker form exists? | Reason |
|---|-------------------------------|------------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`               | arbitrary commutative ring   | ℤ / field / integral domain      | NO (already weakest sensible) | proof is pure `linear_combination`/`ring` from the relation; needs only commutative-ring arithmetic. Cannot weaken below `CommRing` (subtraction + `ring` required). |
| 2 | `(ell : IsEllSequence W)`     | full defining relation        | full defining relation           | NO                  | the lemma is a direct algebraic consequence of the relation; it is the minimal hypothesis. |
| 3 | indices `m n r : ℤ`           | integer indices               | integer (or lattice, for nets)   | — (net generalisation is a different object) | nets generalise ℤ to ℤⁿ, but that is mathlib's separate (absent) elliptic-net API, not a weakening of this ℤ-indexed lemma. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0. The lemma already lives over an arbitrary `CommRing`
with no domain hypothesis — strictly more general than the field/ℤ setting the literature uses, and
notably more general than mathlib's *concrete* oddness lemmas (`normEDS_neg` et al., see Phase 5).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance? | no | `IsEllSequence W` is already a clean `Prop` predicate; no bundling to do | — |
|  2 | sequences/metric → filters/topology? | no | finite ring-algebraic identity; nothing to filterise | — |
|  3 | construct → universal-property class? | no | it is an equation, not a construction | — |
|  4 | set-with-closure → bundled substructure? | no | not a substructure | — |
|  5 | vector-space/field-specific → weaken typeclass? | no | already arbitrary `CommRing`; already weaker than the literature | — |
|  6 | 1-categorical → higher-categorical? | no | not categorical | — |
|  7 | concrete index ℤ → general additive group? | **maybe** | the *named* result (oddness) generalises from ℤ-sequences to ℤⁿ-indexed elliptic **nets**; but this is mathlib's missing elliptic-net API as a separate development, not a reformulation of this single ℤ-lemma | unifies sequences with Stange's nets — but that is a large separate project, not a restatement |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this lemma in isolation). The only "generalisation" on the table
(ℤ-sequence → ℤⁿ-net) is a whole separate development of elliptic-net API, not a contemporary
reformulation of this helper. The lemma is already in its cleanest, most general ring-theoretic form.

---

### Diamond / defeq risk — n/a

Declaration kind is `lemma`. Phase 4.5 skipped (no definitional equalities / typeclass-search paths
introduced).

---

### Mathlib search-status: `IsEllSequence.sub_add_neg_sub_mul_eq_zero`

[A] Lean-Finder       n/a — mathlib-index tool not invoked; substituted by direct source grep of the pinned mathlib tree (below), which is authoritative for "is it there".
[B] Loogle            type-pattern `(W (m-n) + W (-(m-n))) * W (m+n) * W r ^ 2 = 0` — n/a: depends on the project-local `IsEllSequence`/`W` binders; no such shape indexed in mathlib (the whole `IsEllSequence` lemma namespace is absent from the pin).
[C] LeanSearch        NL "elliptic sequence is odd / antisymmetric W(-n) = -W(n)" — mathlib returns only the *concrete* `normEDS_neg` / `preNormEDS_neg` (oddness of specific constructions), not an abstract `IsEllSequence` oddness lemma.
[D] Grep mathlib src  `grep -rn "sub_add_neg_sub_mul_eq_zero" .lake/packages/mathlib/Mathlib/` → **no hits**. `grep -rn "IsEllSequence\|EllSequence"` → hits ONLY in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, and that file's `IsEllSequence` API ends at `IsEllSequence.smul` (line 106) — no `neg`, no `Rel₃`, no `sub_add_neg_...`.
[E] Name pattern      `neg`/`odd`-style EDS lemmas in the pin: `preNormEDS_neg` (L206), `normEDS_neg` (L318), `complEDS_neg` (L472) — all about **concrete** sequences, proved by induction on the definition. **No** lemma deriving oddness from the abstract `IsEllSequence` predicate.

Searched for both:
  - the user's current form (the symmetrisation identity) — **not in mathlib**.
  - the literature-standard form (abstract elliptic sequence is odd) — **not in mathlib**; mathlib
    has only the concrete-construction oddness lemmas `normEDS_neg`/`preNormEDS_neg`/`complEDS_neg`.

Concluded: **not in mathlib** (grep of the pinned tree exhausted, plus the literature-standard
abstract-oddness form). The entire `namespace IsEllSequence` block (target included) is net-new API
sitting on top of an older mathlib snapshot of the EDS file.

---

### Call sites — `IsEllSequence.sub_add_neg_sub_mul_eq_zero`

Internal use count (NagellLutz, excluding the declaring file & the `Original` variant): **0 external-to-file**.
Within the declaring file: **2 uses**, both inside the immediately-following lemma `IsEllSequence.neg`:

| Caller file:line                                                   | Usage pattern |
|--------------------------------------------------------------------|---------------|
| LutzNagell/EllipticDivisibilitySequence.lean:680 (in `neg`)        | `have := sub_add_neg_sub_mul_eq_zero ell (1 - ↑m) (↑m + 1) 1` |
| LutzNagell/EllipticDivisibilitySequence.lean:685 (in `neg`)        | `have := sub_add_neg_sub_mul_eq_zero ell (-↑m) (↑m + 1) 1`    |

Cross-project: the identical lemma + identical single-consumer pattern recurs in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` (decl L542, used by its
own `neg`), and in the older `EllipticDivisibilitySequenceOriginal.lean` (L637, used by its `neg`).

Inline-derivation grep: the equivalent identity is **not** re-derived inline anywhere else — every
oddness argument routes through this helper.

What the pattern tells us: **K = 0 external uses, single internal consumer (`neg`), no inline
re-derivation.** Per the call-sites rubric this is the "possibly the wrong abstraction — could be
inlined" / "private helper" signal: the lemma is a proof-step whose entire mathematical payoff is
realised by the one lemma that calls it. It is *not* re-used API. That pushes against a clean
YES-add-as-is for this decl *in isolation* — but it does NOT make it composable-from-mathlib (Phase 6),
because mathlib has no abstract-`IsEllSequence` lemma to inline from.

---

### Composition check (Phase 6)

Can `IsEllSequence.sub_add_neg_sub_mul_eq_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: find a mathlib lemma about `IsEllSequence` and apply `ring`.
  - Mathlib decls used: none exist — mathlib has no `IsEllSequence.*` lemmas beyond `.smul`/`.map`,
    and crucially no `Rel₃`, no relation-symmetrisation lemma.
  - Result: **fails**. There is nothing in mathlib to compose from at the abstract-EDS level.

Attempt 2: derive it from the concrete `normEDS_neg` family.
  - Result: **fails** — those are about specific constructed sequences, not an arbitrary `W` with
    `IsEllSequence W`. Wrong direction (concrete, not abstract); cannot supply this identity.

Conclusion: **NOT-COMPOSABLE**. The lemma is a genuine one-step consequence of the *project-local*
`IsEllSequence` definition (`congr` of the relation + its swap, then `ring`), but mathlib provides no
building blocks for it. It is "trivial *given the project's* `IsEllSequence` API", not given mathlib's.

---

## Verdict: `IsEllSequence.sub_add_neg_sub_mul_eq_zero`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): oddness `W(−v)=−W(v)` is the named result (Stange, Wikipedia, EDS
  formulary); this lemma is the *unnamed* symmetrisation step feeding it.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — arbitrary `CommRing`, no domain hypothesis;
  no modern-idiom reformulation for the lemma in isolation.
- Mathlib search (Phase 5): NOT in mathlib. The whole abstract `IsEllSequence` API block is net-new
  on top of an older EDS snapshot; mathlib has only *concrete* oddness (`normEDS_neg` &c.).
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (no abstract-EDS building blocks upstream).

**Rationale.**
Two facts are simultaneously true, and they pull in opposite directions — which is exactly what
BORDERLINE is for. (1) The lemma is genuinely *absent* from mathlib and *not* composable from it:
mathlib's EDS file (pinned snapshot) stops before any abstract `IsEllSequence` lemmas, proving
oddness only for the concrete `normEDS`/`preNormEDS`/`complEDS` constructions by induction. The
project's `IsEllSequence.neg` — "*any* elliptic sequence over *any* commutative ring with
`W 1, W 2 ∈ R⁰` is odd" — is a real, strictly-more-abstract result that mathlib lacks, and this lemma
is its load-bearing first half. The file is Apache-licensed, authored by the same person who wrote
mathlib's EDS file, and the very same code is being grown in two AINTLIB projects (NagellLutz +
HasseWeil) — every signal says this block is bound for an upstream PR. (2) But *this particular
decl*, viewed alone, is an unnamed one-step algebraic identity (`congr(ell m n r + ell n m r)` then
`ring`) with exactly one consumer (`neg`) and no re-use anywhere. It is not a quotable theorem on its
own; in a mathlib PR it would most naturally ride along *inside* the `IsEllSequence` oddness
development — quite possibly as a `private`/`protected` helper or even inlined into `neg` — rather
than shipped as a standalone public lemma. The mathlibable gate forbids stamping YES-add-as-is on a
single-use, single-step helper without a human fixing the API grain, and forbids NO-mathlib-has-it /
NO-composable (mathlib has neither it nor its building blocks). Hence BORDERLINE: the *block* is a
clear YES; *this leaf's* packaging is the human call.

**Numbered questions (for the human):**
1. Should the entire net-new `namespace IsEllSequence` API block (`oddRec`, `evenRec`, `zero`,
   `sub_add_neg_sub_mul_eq_zero`, `neg`, `rel₄`, `net`, `invar`) be upstreamed to
   `Mathlib.NumberTheory.EllipticDivisibilitySequence` as one PR — i.e. is this whole development
   intended for mathlib (it certainly looks it: Angdinata, Apache, duplicated in HasseWeil)?
   If yes, this lemma rides along and the remaining questions decide its *form*, not its fate.
2. In that PR, should `sub_add_neg_sub_mul_eq_zero` be a **public** lemma, a **`private`/`protected`
   helper**, or **inlined into `IsEllSequence.neg`** (its sole consumer)? (Reuse evidence: 0 callers
   outside `neg`.)
3. If kept as a named lemma: keep the descriptive-of-the-conclusion name
   `sub_add_neg_sub_mul_eq_zero`, or rename to something tying it to its role (e.g.
   `add_neg_mul_sq_eq_zero` / a `…_symm`-flavoured name signalling "symmetrisation toward oddness")?
4. The NagellLutz and HasseWeil copies have diverged (proof style: `lia` vs `omega`,
   `convert … using 1; ring` vs `using 4 <;> ring_nf`). Before any upstreaming, should the two be
   reconciled to a single canonical copy in `Common/` (AINTLIB convention) so there is one source of
   truth to PR?

**Next action:** human answers Q1 (is the block upstream-bound?) and Q2 (this leaf's grain). If
"upstream the block, keep this as a `private`/inlined helper", the practical mathlibable verdict for
this single decl collapses to "ships *with* the block, not as standalone public API" — re-run
`/mathlibable` on `IsEllSequence.neg` (the named result) as the real upstreaming unit. If the block
is *not* upstream-bound, this lemma stays a project-internal helper and needs no mathlib action.

---

## Next step

Human answers the four questions above (chiefly: is the abstract-`IsEllSequence` block bound for
mathlib, and should this single-use one-step helper ship public / `private` / inlined). The natural
upstreaming unit is the named result `IsEllSequence.neg` ("an elliptic sequence is odd"), which this
lemma serves; assess/PR that as the unit rather than this leaf in isolation.
