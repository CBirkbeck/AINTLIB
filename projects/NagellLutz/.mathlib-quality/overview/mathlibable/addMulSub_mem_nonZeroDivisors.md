# /mathlibable report — `EllSequence.addMulSub_mem_nonZeroDivisors`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task note; reasoning from source)
- decl `EllSequence.addMulSub_mem_nonZeroDivisors`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:402`
  (namespace `EllSequence`, opened at line 90)
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS); defines `addMulSub`/`rel₄`/`rel₆`
  elliptic-relation machinery and constructs normalised EDSs. This file is a **fork** that expands
  the upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (which does NOT contain any
  of this machinery).

Cross-project note: an **identical** copy lives in the HasseWeil project at
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:328`, and a third copy in
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:381`. The fork is
duplicated; none of the three is in mathlib.

---

### Statement (Phase 1)

`addMulSub_mem_nonZeroDivisors` states: for a sequence `W : ℤ → R` over a commutative ring `R`, if
`W 1` and `W 2` are both **non-zero-divisors** of `R`, then for every integer `a` the "basic building
block" `addMulSub W (cMin a) (dMin a)` is also a non-zero-divisor.

Here (all fork-local definitions):
- `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` (line 94) — the elementary product of two
  sequence terms underlying the four-index elliptic relation `rel₄`.
- `dMin a := if Even a then 0 else 1`, `cMin a := dMin a + 2` (lines 382–384) — the minimal
  same-parity index pair `(c, d)` for the index `a`: `(2, 0)` when `a` is even, `(3, 1)` when odd.

So the conclusion unfolds to two concrete cases:
- `a` even: `addMulSub W 2 0 = W 1 * W 1` (= `W 1 ^ 2`, by `addMulSub_two_zero`);
- `a` odd:  `addMulSub W 3 1 = W 2 * W 1` (by `addMulSub_three_one`, which is `rfl`).
In each case it is a product of two non-zero-divisors, hence a non-zero-divisor.

Variables / typeclasses:
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(W : ℤ → R)` — the sequence (implicit here via `variable {W}` at line 401).

Hypotheses:
- `one : W 1 ∈ R⁰` — `W 1` is a non-zero-divisor (`R⁰ = nonZeroDivisors R`, a `Submonoid R`).
- `two : W 2 ∈ R⁰` — `W 2` is a non-zero-divisor.
- `(a : ℤ)` — the index selecting the minimal pair `(cMin a, dMin a)`.

Conclusion (math): the minimal-index building block `addMulSub W (cMin a) (dMin a)` is a
non-zero-divisor.

Conclusion (Lean): `addMulSub W (cMin a) (dMin a) ∈ R⁰`.

Proof (verbatim, line 404):
```lean
rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]
```
i.e. unfold `cMin`/`dMin`, split on `Even a`, and in each branch close with `Submonoid.mul_mem`
(the `(2,0)`/`(3,1)` reductions hold by `rfl`/defeq).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper lemma — not a `def`/`class`, not named after a person, not a `## Main statement`.
It is pure non-zero-divisor plumbing for the `Rel₄OfValid` induction, with a 1-line proof.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner def check is **n/a**. (For the record the
*proof* is one line, which is itself a weak negative signal for independent mathlib inclusion.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "elliptic divisibility sequence division polynomial non-zero divisor W(1) W(2) Ward Stange" | partial | EDS defined by W1,W2,W3,W4 with W1W2W3≠0 (Ward) | "non-zero-divisor closure of a building block" is NOT a named result in the literature; it is Lean-formalization plumbing |
| 2 | WebSearch (general/source) | "addMulSub elliptic relation rel4 division polynomial mathlib Angdinata elliptic divisibility" | yes | arXiv **2604.05280** "On Elliptic Sequences over Commutative Rings" (acknowledges D.K. Angdinata; discusses division polynomials over comm rings; Lean/mathlib formalization mentioned) | This is the exact source paper the fork formalizes. `addMulSub`/`rel₄` are its devices. |
| 3 | WebSearch (named-after / aliases) | covered by #1/#2 (Ward "Memoir on Elliptic Divisibility Sequences"; Stange "elliptic nets") | yes | recurrence / elliptic-net relations | underlying objects are standard; this *closure lemma* is an implementation detail, not a literature statement |
| 4 | ChatGPT MCP | n/a — MCP reported down per task note; substituted by extra WebSearch (#2) targeting the source paper + reasoning from the source proof | n/a | — | the standard-form question is answered by the source paper itself (#2) |
| 5 | Local references | `.mathlib-quality/references/` and `refs/NagellLutz/` both absent | n/a | — | directories do not exist (recorded n/a) |
| 6 | nLab | "elliptic divisibility sequence" / "non-zero divisor submonoid" | n/a | — | nLab has no page for this EDS plumbing; the mathlib concept is `nonZeroDivisors` (a `Submonoid`), already covered by mathlib search (Phase 5) |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | "non zerodivisor" / "elliptic divisibility" | n/a | Stacks has the general "nonzerodivisors form a multiplicative set" (Tag 00CQ / commutative-algebra), but NOT this sequence-specific corollary | the only general fact involved (product of non-zero-divisors is a non-zero-divisor) is standard commutative algebra, already in mathlib as `Submonoid.mul_mem` |
| 9 | MathOverflow / MSE | "product of two non zero divisors is a non zero divisor" | yes (folklore) | non-zero-divisors are closed under multiplication (they form a saturated multiplicative monoid) | exactly the content mathlib encodes by making `nonZeroDivisors R` a `Submonoid`; nothing EDS-specific |
| 10 | recent arXiv (≤5y) | "elliptic sequences over commutative rings" (2026) | yes | arXiv 2604.05280 (same as #2) | confirms `addMulSub`-style machinery is current-research / in-formalization, NOT yet in mathlib |

### Literature summary (Phase 3)

Concept identified as: a **non-zero-divisor closure lemma** for the elementary building block
`addMulSub` of the four-index elliptic relation, at its minimal same-parity index pair
`(cMin a, dMin a) ∈ {(2,0),(3,1)}`. The only genuinely mathematical fact involved is the standard
commutative-algebra statement *"non-zero-divisors are closed under multiplication"*; the wrapping
(`addMulSub`, `cMin`, `dMin`) is bespoke to the source paper arXiv 2604.05280 and its Lean
formalization.

Sources agree on the standard form: yes for the *underlying* fact (product of non-zero-divisors is a
non-zero-divisor — folklore / Stacks 00CQ / mathlib `Submonoid`). The lemma *as stated* (about
`addMulSub … (cMin a)(dMin a)`) has no independent literature existence — it only makes sense relative
to the fork's `addMulSub`/`cMin`/`dMin` definitions.

Most general standard form: "In a commutative monoid-with-zero, the set of non-zero-divisors is a
submonoid (closed under `1` and `*`)." Mathlib already states this maximally generally.

Generality dimensions where the literature varies: none relevant — the wrapping is fixed by the
specific `rel₄` construction.

Disagreement with the literature: none. The lemma is a faithful Lean implementation detail.

---

### Generality analysis — `EllSequence.addMulSub_mem_nonZeroDivisors`

Literature-standard form (from Phase 3): the maximally-general fact is `Submonoid.mul_mem` for
`nonZeroDivisors R` — already in mathlib and already maximal. The lemma here is a *specialisation*
of that to two concrete `addMulSub` values.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | comm monoid-with-zero suffices for the *core* fact | yes (for the core fact) | but `addMulSub`/`cMin`/`dMin` are defined for a `CommRing` sequence; weakening `R` is meaningless without also generalising those fork defs. Not an independent weakening of *this* lemma. |
| 2 | `one : W 1 ∈ R⁰`, `two : W 2 ∈ R⁰` | the two minimal generators | the two factors needed | NO | exactly the inputs `Submonoid.mul_mem` consumes; cannot be weakened |
| 3 | `(a : ℤ)` index | selects `(2,0)` or `(3,1)` | n/a | NO | the case split *is* the content |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL *for what it states* (it is the tightest specialisation of the
already-maximal `Submonoid.mul_mem`). It is not a candidate for weakening, because every weakening
either is already provided by mathlib's `Submonoid.mul_mem` (the core fact) or would require first
upstreaming the `addMulSub`/`cMin`/`dMin` machinery (out of scope for this single lemma).
Number of weakening opportunities found: 0 (that apply to this lemma independently).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | typeclasses vs bundled hyps? | no | `W 1 ∈ R⁰` is already the canonical `Submonoid`-membership idiom | — |
| 2 | sequences/metric → filters? | no | finite case split; no topology | — |
| 3 | construction → universal property? | no | — | — |
| 4 | set+closure-pred → bundled substructure? | already done | `R⁰` is `nonZeroDivisors R : Submonoid R`; the proof already uses `Submonoid.mul_mem` | — |
| 5 | vector-space/field → weaker typeclass? | no (see 4a row 1) | core fact already at monoid-with-zero in mathlib | — |
| 6 | 1-categorical → higher? | no | — | — |
| 7 | concrete index ℤ → general? | no | `cMin`/`dMin` are intrinsically ℤ-indexed | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no. The lemma already uses the contemporary mathlib idiom (membership in the
`nonZeroDivisors` submonoid, discharged by `Submonoid.mul_mem`). There is no organisational improvement
to make — the only "modernisation" would be to *not have this wrapper at all* and call
`Submonoid.mul_mem` (plus the `addMulSub_two_zero`/`addMulSub_three_one` rewrites) inline, which is the
Phase 6 composition point.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (Prop-valued; introduces no defeq or typeclass-search path).

---

### Mathlib search-status: `EllSequence.addMulSub_mem_nonZeroDivisors`

[A] Lean-Finder       "addMulSub nonZeroDivisors", "elliptic building block non zero divisor"  — no hits (index has no `addMulSub`)
[B] Loogle            `addMulSub`, `cMin`, `_ ∈ nonZeroDivisors _ → _ ∈ nonZeroDivisors _`        — no hits for the fork concepts; for the *core* type the hit is `Submonoid.mul_mem` / `mul_mem_nonZeroDivisors`
[C] LeanSearch        "product of two non-zero-divisors is a non-zero-divisor"                    — returns `Submonoid.mul_mem` and the (deprecated) `mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors`
[D] Grep mathlib src  `def addMulSub`, `addMulSub_mem_nonZeroDivisors`, `def cMin`, `Rel₄OfValid`  — **zero matches anywhere under `.lake/packages/mathlib/Mathlib/`** (the upstream EDS file has none of this machinery)
[E] Name pattern      grep mathlib for `addMulSub` / `cMin` / `dMin`                              — none

Searched for both:
  - the user's current form (`addMulSub … (cMin a)(dMin a) ∈ R⁰`): **not in mathlib** — the
    `addMulSub`/`cMin`/`dMin` definitions themselves are absent from mathlib.
  - the literature-standard / core form (product of non-zero-divisors is a non-zero-divisor): **IS in
    mathlib**, as the `Submonoid` structure on `nonZeroDivisors R`, used via
    `Submonoid.mul_mem _ hx hy` (`Mathlib/Algebra/Group/Submonoid/Defs.lean:221`). Note
    `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:156-166` even *deprecates* the bespoke
    `mul_mem_nonZeroDivisors_*` wrappers in favour of plain `Submonoid.mul_mem`.

Concluded:
  - The exact lemma is "not in mathlib" — but only because its *vocabulary* (`addMulSub`, `cMin`,
    `dMin`) is fork-local and not upstreamed.
  - The mathematical core ("found building blocks": `Submonoid.mul_mem`, plus the fork's own
    `addMulSub_two_zero` (line 170) and `addMulSub_three_one` (line 171)) is available; the
    composition trivially yields the lemma.

---

### Call sites — `EllSequence.addMulSub_mem_nonZeroDivisors`

Internal use count: 2  (within NagellLutz, excluding the declaring line)
External-to-file callers: 0 distinct *other* files in NagellLutz (both uses are in the same file,
`EllipticDivisibilitySequence.lean`). Repo-wide, the lemma is independently re-declared (not
imported) in HasseWeil and in `EllipticDivisibilitySequenceOriginal.lean` — i.e. copied, not reused.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| EllipticDivisibilitySequence.lean:462 | `(addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti` (feeds the `mem` arg of `rel₄_of_fix₂`/`rel₄_of_min₂`) |
| EllipticDivisibilitySequence.lean:465 | `rel (addMulSub_mem_nonZeroDivisors one two a) b c` (feeds the `mem : addMulSub W c₀ d₀ ∈ R⁰` hypothesis) |

Inline-derivation grep: the same fact is "re-derived" only in the sense of being a **verbatim copied
declaration** in the two other forked files (HasseWeil line 328, Original line 381) — not reused via
`import`. No site re-proves it differently inline.

What the pattern tells you: K = 2 internal uses, both in `rel₄_of_min₂`'s machinery, where the lemma's
*entire purpose* is to discharge the `mem : addMulSub W c₀ d₀ ∈ R⁰` hypothesis of the `Rel₄OfValid`
induction with `c₀ = cMin a`, `d₀ = dMin a`. It is genuine internal glue — not dead code — but it is
glue *for the fork's own machinery*, with no consumer outside that machinery.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_mem_nonZeroDivisors` be derived in ≤3 chained calls from mathlib (+ the
fork's own elementary `addMulSub` evaluation lemmas)?

Attempt 1 — the existing proof IS the composition:
```lean
by rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]
```
- Mathlib decls used: `Submonoid.mul_mem` (twice), `split_ifs` (on `Even a`).
- Fork helper rewrites used implicitly (defeq): `addMulSub_two_zero` (`addMulSub W 2 0 = W 1 ^ 2`),
  `addMulSub_three_one` (`addMulSub W 3 1 = W 2 * W 1`).
- Result: succeeds. This is a 2-branch case split each closed by a single `Submonoid.mul_mem`.

Conclusion: COMPOSABLE. The lemma is a trivial composition of `Submonoid.mul_mem` with the two
concrete `addMulSub`-evaluation `rfl`s. No new *mathematical* idea. The only reason mathlib alone
doesn't literally close it is that `addMulSub`/`cMin`/`dMin` live in the fork, not mathlib — i.e. the
lemma is inseparable from the fork's machinery and would travel with it, not stand alone.

---

## Verdict: `EllSequence.addMulSub_mem_nonZeroDivisors`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the only mathematical content is "non-zero-divisors are closed under
  multiplication" (folklore / Stacks 00CQ); the `addMulSub`/`cMin`/`dMin` wrapping is bespoke to the
  source paper arXiv 2604.05280 and its Lean formalization — not an independent literature result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it states; it is the tightest
  specialisation of the already-maximal mathlib `Submonoid.mul_mem`. No modern-idiom improvement (it
  already uses `nonZeroDivisors`-submonoid membership).
- Mathlib search (Phase 5): the building block `Submonoid.mul_mem`
  (`Mathlib/Algebra/Group/Submonoid/Defs.lean:221`) is in mathlib; the `addMulSub` machinery is not.
  Mathlib even *deprecates* the bespoke `mul_mem_nonZeroDivisors_*` wrappers in favour of plain
  `Submonoid.mul_mem`.
- Composition check (Phase 6): COMPOSABLE — the existing 1-line proof is the composition
  (`split_ifs` + two `Submonoid.mul_mem`).

**Rationale:**

This lemma carries no mathematical content beyond "the product of two non-zero-divisors is a
non-zero-divisor," which mathlib already provides maximally generally by making `nonZeroDivisors R` a
`Submonoid` (apply `Submonoid.mul_mem`). Everything else is fork-local packaging: `addMulSub`, `cMin`,
`dMin`, and the elliptic-relation `rel₄` framework are devices from the source paper (arXiv
2604.05280), and they are **absent from mathlib** — the upstream
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) contains the
`IsEllSequence`/`preNormEDS`/`normEDS` API but none of the `addMulSub`/`rel₄`/`cMin` machinery this
fork adds. So the lemma cannot be *independently* mathlib-able: it only makes sense relative to
fork definitions that themselves are not (yet) upstream. It is glue whose job (lines 462, 465) is to
discharge the `mem : addMulSub W c₀ d₀ ∈ R⁰` hypothesis of the `Rel₄OfValid` induction at the minimal
index pair.

The right disposition is therefore NOT a standalone mathlib PR. Either (a) it should be inlined — at
both call sites, the `mem` argument can be produced directly by `Submonoid.mul_mem` after rewriting
the two concrete `addMulSub` values; or (b) if and when the entire `addMulSub`/`rel₄` development is
upstreamed *as a block* (the natural mathlib home for the whole paper-formalization), this lemma rides
along as a trivial one-line helper — it would never be proposed to mathlib on its own. Note it is also
currently **triplicated** across the repo (NagellLutz `EllipticDivisibilitySequence.lean`, NagellLutz
`EllipticDivisibilitySequenceOriginal.lean`, HasseWeil `Auxiliary/EllipticDivisibilitySequence.lean`),
so the immediate cleanup action is cross-project de-duplication, independent of any mathlib decision.

**WHY not (refactor-actionable):**
Mathlib has the building block (`Submonoid.mul_mem`); the user's form is a ≤3-call composition of it
with the fork's own `addMulSub_two_zero`/`addMulSub_three_one`. No new lemma is warranted in mathlib
because (i) the content is `Submonoid.mul_mem`, and (ii) the wrapper references fork-only vocabulary.

Mathlib building blocks:
- `Submonoid.mul_mem` — `Mathlib/Algebra/Group/Submonoid/Defs.lean:221`
- (fork-local, would-be-upstreamed-with-the-block) `EllSequence.addMulSub_two_zero` (line 170),
  `EllSequence.addMulSub_three_one` (line 171)

Composition sketch (≤3 lines — the existing proof):
```lean
example (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]
```

Call sites in our project (from Phase 6.0): K = 2 (both in `EllipticDivisibilitySequence.lean`, lines
462 & 465, inside the `rel₄_of_min₂` induction).

Refactor plan:
- **Primary (cross-project dedup, do this regardless):** keep a single copy of the whole
  `addMulSub`/`rel₄` development (it is currently triplicated). The lemma stays a private/auxiliary
  helper next to that development; do not export it to mathlib on its own.
- **If inlining is preferred** at the 2 call sites: replace `addMulSub_mem_nonZeroDivisors one two a`
  with the two-case `Submonoid.mul_mem` discharge — e.g. provide the `mem` hypothesis via
  `(by rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one])` directly, or factor it
  as a `have`. Verify the implicit `a`/`W` flow at each site (both currently pass `one two a`
  positionally).
- **Mathlib disposition:** none as a standalone lemma. Revisit only as part of upstreaming the entire
  `addMulSub`/`rel₄` block (the natural PR grain — see arXiv 2604.05280 formalization), where this is a
  1-line helper.

Next action: do NOT open a standalone mathlib PR. De-duplicate the fork across NagellLutz/HasseWeil
(coordinator-level rename/dedup), and either inline the `Submonoid.mul_mem` composition at the 2 call
sites or retain the lemma as a local helper bundled with the `addMulSub` machinery.

---

## Next step

Do not open a standalone mathlib PR. De-duplicate the triplicated `addMulSub`/`rel₄` development
across the repo, and either inline the `Submonoid.mul_mem` composition at the two call sites or keep
this as a local helper that would only ever reach mathlib bundled with the whole `addMulSub`
machinery (which is itself not yet upstream).
