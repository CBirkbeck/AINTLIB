# /mathlibable report — `EllSequence.rel₄_swap₀₁`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source.
- decl `EllSequence.rel₄_swap₀₁`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:517`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs
  normalised EDSs from initial terms; this local copy *extends* mathlib's file with the
  `addMulSub` / `rel₄` / `relFin4` / `net` four-index-relation machinery and the proof that
  `normEDS` is elliptic.

**Qualified name VERIFIED.** Namespace stack at line 517 is `namespace EllSequence`
(opened line 90) with only `section Perm` in between — no inner `namespace`. So the
fully-qualified name is `EllSequence.rel₄_swap₀₁`. The parsed guess was correct.

---

### Statement (Phase 1)

`EllSequence.rel₄_swap₀₁` states that the four-index elliptic relation `rel₄` is
**antisymmetric under transposition of its first two indices**:

> For a sequence `W : ℤ → R` (`R` a commutative ring) that is **odd**
> (`neg : ∀ k, W (-k) = -W k`), and for any integers `m, n, r, s`,
> `rel₄ W m n r s = - rel₄ W n m r s`.

Here `rel₄` is the project-local definition (lines 100–105):

```lean
def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c
```

built from `addMulSub W m n = W ((m+n).tdiv 2) * W ((m-n).tdiv 2)`. This `rel₄` is the
"three partitions of four indices into two pairs" form of the elliptic / elliptic-net
relation. `rel₄_swap₀₁` is one of three transposition lemmas
(`swap₀₁`, `swap₁₂`, `swap₂₃` — the adjacent transpositions generating `Perm (Fin 4)`),
each proved in one line from `addMulSub_swap` (`addMulSub W m n = - addMulSub W n m`,
which itself needs `neg`).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring.
- `(W : ℤ → R)` — the sequence.
- `{m n r s : ℤ}` — the four indices.

Hypotheses (Lean side):
- `neg : ∀ k, W (-k) = -W k` — `W` is an odd function (section-level `variable`,
  `include neg`).

Conclusion (math): `rel₄(m,n,r,s) = - rel₄(n,m,r,s)`.
Conclusion (Lean): `rel₄ W m n r s = - rel₄ W n m r s`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — one of three adjacent-transposition generators feeding the
omnibus permutation-invariance theorem `relFin4_perm`. Not a named theorem, not a new
structure, not a `## Main statements` entry. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner def check **n/a**.
(For the record the *proof* is a one-liner — `simp_rw [rel₄, addMulSub_swap W neg n m]; ring`
— but the 2b gate concerns one-line *definitions*, so it does not apply.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Stange elliptic nets net polynomial antisymmetry permutation indices relation" | yes | Stange's net polynomials Ω carry an explicit antisymmetric sign `(-1)^…` under permutation of the index/exponent data | arXiv:1408.6623 *On Symmetries of Elliptic Nets and Valuations of Net Polynomials*; Stange, *The Tate Pairing via Elliptic Nets* (eprint 2006/392); *Elliptic nets and elliptic curves* (arXiv:0710.1316) |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence Ward division polynomial four index relation symmetric" | yes | Ward's EDS recurrence `W_{m+n}W_{m-n}W_r² = W_{m+r}W_{m-r}W_n² − W_{n+r}W_{n-r}W_m²` and its "symmetry properties" (Ward 1948) | Wikipedia *Elliptic divisibility sequence*; *Sign of an EDS*; arXiv:2604.05280 *On Elliptic Sequences over Commutative Rings* |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "Ward symmetry", "Stange net polynomial sign" | yes | the sign-character / antisymmetry under index permutation is the well-known structural feature; the **specific `rel₄` 3-partition packaging is Angdinata's**, an implementation device for the mathlib formalisation | the exact `addMulSub`/`rel₄` grouping is not a named literature object — it is the Lean author's reformulation that makes the elliptic identity unconditional in `W` being odd |
|  4 | ChatGPT MCP                      | "standard form + generality + historical evolution of the four-index elliptic-net relation and its permutation antisymmetry" | n/a | — | ChatGPT MCP reported down in this environment (task brief); compensated with extra WebSearch + arXiv channels (#1,#2,#10) |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/` | n/a | — | no `references/` dir present (only `overview/`); recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net" | no | nLab has no dedicated EDS / elliptic-net entry | not a category-theoretic object; brief look confirms absence |
|  7 | nCatLab (if categorical)         | — | n/a | — | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | "elliptic divisibility" / "division polynomial" | no | Stacks has elliptic-curve scaffolding but no EDS/net-relation tag | EDS/net theory is not in Stacks' scope |
|  9 | MathOverflow / Math.StackExchange| "elliptic divisibility sequence symmetry four index" | yes (weak) | discussion confirms Ward symmetry + Stange net antisymmetry are standard folklore | no canonical single-lemma reference for the transposition sign in *this* packaging |
| 10 | recent arXiv (last 5 yrs)        | "elliptic sequences over commutative rings" | yes | arXiv:2604.05280 treats elliptic sequences over general commutative rings (matches the `[CommRing R]` generality used here) | confirms the commutative-ring generality is the modern standard |

### Literature summary (Phase 3)

Concept identified as: the **antisymmetry of the four-index elliptic / elliptic-net
relation under transposition of two of its indices** — a facet of the "symmetry of EDS"
(Ward, 1948) and the explicit permutation-sign character of Stange's net polynomials
(Stange thesis; arXiv:1408.6623).
Sources agree on the standard form: **yes** for the *phenomenon* (the relation is
alternating / sign-equivariant under permuting the indices). **No** for the *exact Lean
packaging*: `addMulSub` + the three-pair-partition `rel₄` is David Angdinata's
reformulation, engineered so the identity holds unconditionally and avoids characteristic-3
peculiarities (see the `net` docstring at lines 107–114). The literature states the
symmetry at the level of `W`-products / net polynomials, not this specific grouping.
Most general standard form: the elliptic relation holds over an arbitrary commutative ring
(arXiv:2604.05280), which is exactly the `[CommRing R]` setting here. The antisymmetry is
the statement that permuting indices multiplies the relation by the sign of the permutation
— `swap₀₁` is the transposition `(0 1)` instance, and the full statement is the omnibus
`relFin4_perm` (`relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t`).
Generality dimensions where the literature varies:
  - coefficient ring: ℤ (Ward) → arbitrary commutative ring (modern; matches here).
  - oddness of `W`: classical treatments assume `W` odd; this packaging isolates the
    `neg` hypothesis so non-sign facts stay unconditional.
Disagreement with the literature: none mathematically; the only gap is that the exact
`rel₄` grouping is a formalisation-specific device with no literature name.

---

### Generality analysis — `EllSequence.rel₄_swap₀₁`

Literature-standard form (from Phase 3): the elliptic relation is sign-equivariant under
permuting its indices, over an arbitrary commutative ring, for an odd sequence `W`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | arbitrary commutative ring | NO | already the modern maximal setting (arXiv:2604.05280); `rel₄` is a ring expression, needs commutativity |
| 2 | `neg : ∀ k, W (-k) = -W k` | `W` odd | `W` odd (classical assumption) | NO | the sign flip in `addMulSub_swap` genuinely needs `W` odd; cannot be dropped |
| 3 | `{m n r s : ℤ}` indices | four free integers | four free integers (no parity hyp needed for *this* lemma) | already maximal | the swap identity is unconditional in the indices — strictly more general than the same-parity-restricted `rel₄_of_…` theorems |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what the lemma asserts).
Number of weakening opportunities found: 0.
The statement is already at the modern standard generality (arbitrary commutative ring,
odd sequence, no superfluous parity constraint on the indices). No restatement proposed on
generality grounds.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | bundled hyp → typeclass/instance? | no | — | `neg` (oddness of `W`) is a genuine hypothesis on a specific `W`, not a structure-on-a-type; a typeclass would be artificial |
|  2 | sequences/metric → filters/topology? | no | — | purely algebraic identity; no limiting notion |
|  3 | construction → universal property? | no | — | it is an equation, not a construction |
|  4 | subset+closure → bundled substructure? | no | — | n/a |
|  5 | vector-space/field → module/(semi)ring weakening? | no | — | already at `CommRing`; cannot drop to non-commutative (the `ring` proof needs commutativity) |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index ℤ → general add. group/monoid? | **partially** | the indices live in ℤ (needed for `tdiv 2` / parity); the *permutation* structure is already abstracted via `Perm (Fin 4)` in the sibling `relFin4_perm` | the omnibus `relFin4_perm` IS the index-permutation-generalised form; `swap₀₁` is the generator. So the modern idiom *already exists in the file* as `relFin4_perm` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it is already present in the file as `relFin4_perm`.**
The mathlib-idiomatic packaging of "the relation is antisymmetric under any index
transposition" is the single sign-equivariance theorem over the full symmetric group
`relFin4_perm : relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t` (line 533). The three
adjacent-transposition lemmas (`swap₀₁`/`swap₁₂`/`swap₂₃`) are the **generators** used to
*prove* `relFin4_perm` (via `Perm.mclosure_swap_castSucc_succ`). So the relevant
"generalise-first" target is not a weakening of `swap₀₁` — it is the already-written
omnibus lemma, of which `swap₀₁` is the `σ = (0 1)` instance.
Real mathematical improvement: the omnibus lemma is the natural API surface; the individual
transpositions are scaffolding. Cost: n/a (already done in-repo).

---

### Diamond / defeq risk — `EllSequence.rel₄_swap₀₁`

n/a — declaration kind is **lemma** (no definitional equalities or typeclass-search paths
introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `EllSequence.rel₄_swap₀₁`

[A] Lean-Finder       "rel4 swap antisymmetry elliptic relation"      n/a — index unavailable locally; reasoned from source-grep of the mathlib tree
[B] Loogle            `?W m n r s = - ?W n m r s` / `EllSequence.rel₄` no hits — `rel₄` / `addMulSub` / `relFin4` symbols do not exist in mathlib
[C] LeanSearch        "four index elliptic relation antisymmetric swap indices" no hits — no such API in mathlib
[D] Grep mathlib src  `grep -n "rel₄\|addMulSub\|swap₀₁\|relFin4\|net" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **0 matches**
[E] Name pattern      grep mathlib tree for `rel₄_swap`, `relFin4`, `addMulSub` → 0 matches anywhere under `.lake/packages/mathlib/Mathlib/`

Searched for both:
  - the user's current form (`rel₄ W m n r s = - rel₄ W n m r s`) — absent;
  - the literature-standard form (permutation sign-equivariance of the elliptic relation) — absent.

**Decisive structural finding.** The mathlib file
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) is authored by the
**same author** (David Kurniadi Angdinata) and **stops at `normEDS` / `complEDS`**. Its
module docstring lists, under `## Main statements`,
`TODO: prove that normEDS satisfies IsEllDivSequence`. The project's local copy (1667 lines)
is *that upstream file plus the entire `addMulSub`/`rel₄`/`relFin4`/`net` development that
proves exactly this TODO*. So none of the `rel₄` machinery — including `rel₄_swap₀₁` — is in
mathlib yet. (It is, however, **duplicated within this monorepo**: byte-identical copies live
in `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:431` and in the
backup `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:496`.)

Concluded: **not in mathlib** (all methods exhausted, under both the user's form and the
literature-standard form). Mathlib has neither the lemma, nor the `rel₄` definition it is
stated about, nor composable building blocks for it.

---

### Call sites — `EllSequence.rel₄_swap₀₁`

Internal use count (this project, excluding the declaring file's own definition site): **0
outside the file**; **1 within the file**.
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:542` | `exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]` — sole consumer; discharges the three transposition-generator goals inside the proof of `relFin4_perm` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`rel₄_swap₀₁`?):
  - The lemma is **duplicated**, not re-derived: identical statements/proofs at
    `HasseWeil/.../EllipticDivisibilitySequence.lean:431` and
    `NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:496` (a parallel/backup copy).
    Each duplicate's only consumer is its own file's `relFin4_perm`.
  - No downstream module (`DivisionPolynomialOmega.lean`, HasseWeil `GenericPointZsmul.lean`,
    `DivisionPolynomial.lean`) uses the swap lemmas directly — they consume higher-level
    results only.

What this tells us: `rel₄_swap₀₁` is **pure scaffolding** — a generator of the
`Perm (Fin 4)` action used solely to build `relFin4_perm`. It has no independent consumer.
Per the Phase-6 call-sites table, a lemma with a single in-file use that exists only to feed
one omnibus theorem leans away from "export it to mathlib on its own" and toward
"the omnibus `relFin4_perm` is the contribution".

---

### Composition check (Phase 6)

Can `EllSequence.rel₄_swap₀₁` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: unfold `rel₄`, apply an antisymmetry-of-the-pairing lemma, `ring`.
  - Mathlib decls used: **none available** — `rel₄`, `addMulSub`, and `addMulSub_swap` are
    all project-local; mathlib has no analog.
  - Result: **fails** — there is nothing in mathlib to compose. (Within the *project* it is a
    one-liner from `addMulSub_swap`, but `addMulSub_swap` is itself local.)

Attempt 2 (intra-repo, for completeness — NOT a mathlib composition): once the omnibus
`relFin4_perm` exists, `swap₀₁` is its specialisation at `σ = Equiv.swap 0 1`:
  `relFin4_perm neg (Equiv.swap 0 1) t` + `Perm.sign_swap` + unfolding `relFin4` ⇒ the swap
  identity (a ≤3-step derivation). But `relFin4_perm` is not in mathlib either, and in *this*
  codebase the dependency runs the other way (`relFin4_perm` is proved *using* `swap₀₁`), so
  this is not a mathlib composition — it is a remark about granularity within the same
  prospective contribution.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib supplies no building block — not even
the underlying definition). The lemma is, however, a trivial specialisation of its own
sibling `relFin4_perm` *within the same development*.

---

## Verdict: `EllSequence.rel₄_swap₀₁`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the antisymmetry/permutation-sign of the four-index elliptic
  relation is standard (Ward 1948 symmetry; Stange net-polynomial sign; arXiv:1408.6623,
  2604.05280) — but the specific `rel₄` packaging is the Lean author's formalisation device.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it states; Phase 4c notes the
  mathlib-idiomatic form (`relFin4_perm`, full `Perm (Fin 4)` sign-equivariance) **already
  exists in the same file** and `swap₀₁` is merely its `(0 1)` generator.
- Mathlib search (Phase 5): not in mathlib — and neither is the `rel₄` definition it speaks
  about; upstream `EllipticDivisibilitySequence.lean` stops at `normEDS` with an explicit
  TODO to prove ellipticity, which is exactly what this local development supplies.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (no building blocks exist).

**Rationale.**
`rel₄_swap₀₁` is a true, mathematically standard fact (the elliptic relation is alternating
under transposing two indices), and mathlib genuinely lacks this whole area — so it is *not*
a NO-mathlib-has-it and *not* a NO-composable-from-mathlib (mathlib has neither the result
nor the building blocks; the very symbol `rel₄` is project-local). But it is also not a clean
YES-add-as-is for two coupled reasons. **(1) It cannot be upstreamed in isolation:** its
statement mentions `EllSequence.rel₄` (and is proved via `addMulSub_swap`), none of which is
in mathlib. The natural unit of contribution is the *whole* `addMulSub`/`rel₄`/`relFin4`/`net`
development together with the ellipticity theorem it culminates in — which would land as one
coherent PR discharging the upstream `normEDS`-is-elliptic TODO. **(2) Within that bundle,
`swap₀₁` is scaffolding, not the API surface:** it is one of three adjacent-transposition
generators (`swap₀₁`/`swap₁₂`/`swap₂₃`) whose sole purpose is to prove the omnibus
`relFin4_perm` (full symmetric-group sign-equivariance), and it has exactly one in-file
consumer and zero external ones. Once `relFin4_perm` is in mathlib, each `swapᵢⱼ` is a
one-line specialisation. So the genuine question is not "is this lemma true and useful" (it is
both) but a **granularity/policy judgment**: when this development is upstreamed, should the
three individual transposition lemmas be exported as public mathlib API, or kept as private
`omit`-style helpers behind the public `relFin4_perm`? That is exactly the taste-and-policy
call the skill must escalate rather than decide.

**Numbered questions (≤5):**
1. Is the plan to upstream the *whole* `addMulSub`/`rel₄`/`relFin4`/`net` + `normEDS`-is-
   elliptic development to mathlib as one PR (the unit that discharges the existing
   `EllipticDivisibilitySequence.lean` TODO)? `rel₄_swap₀₁` only makes sense bundled into that.
2. If yes: should the three adjacent-transposition lemmas (`rel₄_swap₀₁`/`swap₁₂`/`swap₂₃`)
   be **public** mathlib lemmas, or **private/`protected` helpers** behind the public omnibus
   `relFin4_perm` (full `Perm (Fin 4)` sign-equivariance)? They are pure proof scaffolding with
   a single in-file consumer.
3. Should the public antisymmetry API instead be just `relFin4_perm` (+ the convenience
   `relFin4_perm'`), with the per-transposition facts recovered on demand by users via
   `relFin4_perm … (Equiv.swap i j)`?
4. Independently of mathlib: the lemma is **duplicated** across two monorepo projects
   (NagellLutz and HasseWeil, byte-identical, plus a NagellLutz `…Original` backup). Should
   the shared `EllSequence` machinery be refactored into a single `Common/` module first
   (an AINTLIB-internal dedup) before any mathlib assessment is acted on?

**Next action:** user answers the questions; then either (a) fold `rel₄_swap₀₁` into the
single `rel₄`/`relFin4`-development mathlib PR with the chosen visibility, or (b) first
de-duplicate the `EllSequence` block into `Common/` within AINTLIB and re-assess the omnibus
`relFin4_perm` (not the individual swap lemma) as the mathlib-facing unit.

---

## Next step

Answer questions 1–4 above. The lemma is correct and the area is genuinely mathlib-shaped,
but `rel₄_swap₀₁` is not an independent contribution: it is a transposition generator inside
the (not-yet-upstreamed) `rel₄`/`relFin4` development, and the human call is about bundling +
visibility (export the generators, or only the omnibus `relFin4_perm`?) and about the prior
intra-monorepo de-duplication.
