# /mathlibable report — `EllSequence.addMulSub_sq_mul_rel₄_eq₉`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — `addMulSub_sq_mul_rel₄_eq₉` is a hypothesis-free **polynomial
(`ring`) identity** in the values of `W`, proved by `simp_rw [rel₆, rel₄]; ring`. It says
`(addMulSub W c d)² · rel₄ W m n r s` equals a fixed signed `addMulSub`-coefficiented combination
of `rel₆`-terms — i.e. it is the `(addMulSub W c d)²`-scaled rearrangement of the 10-term reduction
`rel₆_eq₁₀`, regrouped under `addMulSub W m c` / `addMulSub W m d` coefficients (the comments on
lines 347/350 say exactly this, referencing `rel₆_eq₃'` and `rel₆_eq₁₀`). It has **no name in the
literature** (the literature names the *relation* `rel₄` — Xu 2026, arXiv:2604.05280 — and the
*coherence theorem* "every Somos 4 is a Somos k" — van der Poorten–Swart, arXiv:math/0412293 — but
not this intermediate scaled identity), it carries **no content beyond `ring`** once `rel₄`/`rel₆`
exist, and it currently has **zero call sites** in the live file. Once its primitives `rel₄`/`rel₆`
land in mathlib (they are the in-flight upstream contribution — see Verdict), this identity is a
≤3-call `simp_rw [rel₆, rel₄]; ring` reconstruction. It is therefore a derived lemma that travels
*inside* the `rel₄` upstream PR (if kept at all), never a standalone mathlib target.

(Framing caveat, consistent with the sibling reports: the whole `addMulSub`/`rel₄`/`rel₆`/`net`
layer is mathlib's own authors' in-flight upstream code. `addMulSub_sq_mul_rel₄_eq₉` rides with it
as an optional internal step lemma, or is inlined.)

---

### Baseline (Phase 0)
- lake build:               stale per task note — reasoning from source; the decl elaborates in the green `main` build (CLAUDE.md). mathlib pin `d90090f` (2026-06-08).
- decl `EllSequence.addMulSub_sq_mul_rel₄_eq₉`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:344`
- kind:                      `theorem`
- has sorry:                 no
- proof:                     `simp_rw [rel₆, rel₄]; ring` (unfold to `addMulSub` products, then `ring`)
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs (`preNormEDS`, `normEDS`); the `addMulSub`/`rel₄`/`net` Stange-elliptic-net machinery proves `normEDS` is elliptic. This theorem is one of the `rel₆` index-reduction identities in that machinery.

Qualified name **VERIFIED**: namespace `EllSequence` opens at line 90 and is not closed before
line 344, so the parsed `EllSequence.addMulSub_sq_mul_rel₄_eq₉` is correct.

---

### Statement (Phase 1)

`EllSequence.addMulSub_sq_mul_rel₄_eq₉` is a **theorem** (an equation in `R`). For a commutative
ring `R`, a sequence `W : ℤ → R`, and six integers `c d m n r s`:

```lean
theorem addMulSub_sq_mul_rel₄_eq₉ (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s =
      addMulSub W m c * (rel₆ W n d r s c d - rel₆ W r d n s c d + rel₆ W s d n r c d)
                    -- = rel₆ W c d n r s d ↑ by rel₆_eq₃'   = rel₆ W c d n r s c ↓ by rel₆_eq₃
      - addMulSub W m d * (rel₆ W n c r s c d - rel₆ W r c n s c d + rel₆ W s c n r c d)
      + addMulSub W c d * (rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d) := by
                         -- the third row in RHS of rel₆_eq₁₀
  simp_rw [rel₆, rel₄]; ring
```

where, recall,
- `addMulSub W m n := W ((m+n).tdiv 2) · W ((m−n).tdiv 2)` — the half-index building block
  (truncated division, so `addMulSub` is an even function of each argument up to sign),
- `rel₄ W a b c d := addMulSub W a b · addMulSub W c d − addMulSub W a c · addMulSub W b d
  + addMulSub W a d · addMulSub W b c` — the symmetric four-index "elliptic relation" (a
  homogeneous quartic in the values of `W`), and
- `rel₆ W k l a b c d := addMulSub W k l · rel₄ W a b c d` — the reducible `abbrev` "coefficient ×
  relation" (a homogeneous sextic).

**What it says, mathematically.** Multiplying the four-FREE-index relation `rel₄ W m n r s` by the
square of the fixed-index coefficient `addMulSub W c d` yields an `R`-linear combination — with
half-index-product coefficients `addMulSub W m c`, `addMulSub W m d`, `addMulSub W c d` — of
`rel₆`-terms (i.e. `addMulSub × rel₄` products) each of which involves the two extra *fixed* indices
`c, d`. It is the **`(addMulSub W c d)²`-scaled, regrouped form of `rel₆_eq₁₀`** (the 10-term
reduction, line 336): the in-source comments confirm that the first parenthesised group is
`rel₆ W c d n r s d` via `rel₆_eq₃'` (equivalently `rel₆ W c d n r s c` via `rel₆_eq₃`), and the
third parenthesised group is "the third row in RHS of `rel₆_eq₁₀`". It is a homogeneous degree-8
identity in the values of `W` (degree 4 from `(addMulSub)²` times degree 4 from `rel₄` on the LHS;
matched on the RHS).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general; no field/characteristic/domain).
- `(W : ℤ → R)` — the sequence (unconstrained).
- `(c d m n r s : ℤ)` — six integer indices (two "fixed" `c,d`; four "free" `m,n,r,s`).

Hypotheses: **none.** This is an unconditional polynomial identity — it does **not** assume `W` is
an elliptic sequence, that any `rel₄` vanishes, same-parity of indices, or anything about `R`
beyond commutativity. (Contrast `rel₄_of_fix₂` etc., which *do* carry parity/order/non-zero-divisor
hypotheses; this lemma is the pure algebra underneath that family.)

Conclusion (math): an identity between two homogeneous degree-8 forms in `W`.
Conclusion (Lean): `Prop` (an `Eq` in `R`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is **not** a named mathematical object or theorem — it is one of several internal
"intricate implications among elliptic relations" (a phrase from Xu 2026 describing exactly this
kind of step), specifically the `(addMulSub W c d)²`-scaled rearrangement of `rel₆_eq₁₀`. It is not
listed under `## Main definitions`/`## Main statements` (which name `IsEllSequence`, `preNormEDS`,
`normEDS`, `complEDS`, and `isEllDivSequence_normEDS`), it is named in no reference, and it is a pure
`ring` consequence of the genuine primitives `rel₄`/`rel₆`/`addMulSub`. Contrast `rel₄` itself, which
is BIG (the namesake of Xu 2026 and the keystone of the whole layer, assessed `YES-add-as-is` in the
sibling `rel₄.md`).

(Literature width recorded EXHAUSTIVELY below regardless, for framing.)

### One-line check (Phase 2b)

Body line count: **1 substantive proof line** (`simp_rw [rel₆, rel₄]; ring`) — the statement spans
~6 display lines but the *content* is a single `ring` discharge.
One-liner verdict: it is a **`ring`-CLOSED IDENTITY**. The strongest possible negative signal for
standalone inclusion: the entire mathematical content is "unfold the two definitions and call
`ring`", i.e. it is a *theorem with no idea in it beyond the definitions of `rel₄`/`rel₆`". There is
no API-anchor exemption (it anchors nothing — see call sites), no defeq-sealing role (it is a
`theorem`, not a `def`), and no semantic-intent role.

Conclusion: **`ring`-IDENTITY WITHOUT-EXEMPTION** — carried into Phase 7 as a strong bias toward
NO-composable.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (author / upstream)    | "Junyan Xu 'On Elliptic Sequences over Commutative Rings' arXiv elliptic relations division polynomials 2026" | yes | **arXiv:2604.05280** — "4-parameter highly symmetric family of homogeneous quartic relations … called elliptic relations"; "standard EDSs are elliptic in a purely algebraic way using intricate implications among elliptic relations" | The algebraic companion to this Lean file. Names the *relation* (`rel₄`); this scaled identity is one of its "intricate implications", not a named result. |
|  2 | WebSearch (coherence / reduction)| "elliptic divisibility sequence 'elliptic relation' coherence identity Somos van der Poorten Swart 'every Somos 4 is a Somos k' reduction proof algebraic" | yes | **van der Poorten–Swart, arXiv:math/0412293**, BLMS 38 (2006) 546–554 — "direct proof of coherence … a Somos relation of width 4 is also given by three-term Somos relations of all larger widths" | The coherence/width-reduction program this identity serves. Names the *theorem* ("every Somos 4 is a Somos k"), not this intermediate scaled identity. |
|  3 | WebSearch (specific/general form)| (via the sibling `rel₄.md`/`rel₆.md` runs) Stange elliptic nets four-index relation; Ward 3-index relation | yes | Stange net relation (arXiv:0710.1316); Ward 3-index relation | The underlying relation; no source names an `(addMulSub)²·rel₄ = Σ rel₆` scaled identity. |
|  4 | WebSearch (named-after/aliases)  | "'elliptic relation' scaled identity coefficient squared four index reduction nine term Lean formalization" | no | — | No source names a "rel₄ scaled by a squared coefficient" / "_eq₉" object; the coefficient-squared × relation rearrangement is a proof device, not a named entity. |
|  5 | ChatGPT MCP                      | standard name + generality of `(addMulSub c d)² · rel₄(four free) = Σ addMulSub·rel₆` identity         | n/a  | — | **MCP down** per task note — Codex `exec` stdin error reproduced on this run (both attempts). Fell back to arXiv sources (#1, #2) + grep. Mirrors the documented outage in the sibling `rel₄.md`/`rel₆.md` runs. |
|  6 | Local references                 | `.mathlib-quality/references/` + `refs/NagellLutz/`                                                     | n/a  | (absent) | Neither directory exists in the repo — recorded n/a. |
|  7 | nLab                             | elliptic divisibility sequence / elliptic net                                                          | n/a  | (no page) | nLab has no EDS / elliptic-net entry (confirmed in sibling runs). |
|  8 | nCatLab (if categorical)         | —                                                                                                      | n/a  | — | Not categorical — an unconditional ring identity on `ℤ → R`. |
|  9 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | — | Stacks has no EDS / elliptic-net / Somos material. |
| 10 | MathOverflow / MSE               | scaled / coefficient-squared elliptic relation reduction identity                                      | no   | — | No MO/MSE thread on such a scaled identity; only the underlying recurrences/coherence appear. |
| 11 | recent arXiv (last 5 years)      | (via #1) "On Elliptic Sequences over Commutative Rings"                                                 | yes  | **arXiv:2604.05280 (Xu, 2026)** — defines "elliptic relations" (`rel₄`); this identity is an internal proof step, not a named object | "purely algebraic", announces a follow-up on division polynomials (this very Lean file). |
| 12 | Loogle / LeanSearch (mathlib)    | `EllSequence.addMulSub_sq_mul_rel₄_eq₉`, `addMulSub`, `rel₆`, six/eight-index elliptic identity         | no   | — | No hit (see Phase 5). The deferred `lean_loogle`/`lean_leansearch` tools were unavailable on this run; the authoritative mathlib-tree grep (Phase 5) stands in, and the sibling `rel₄.md`/`rel₆.md` runs recorded the same "unknown identifier" no-hit for this namespace. |

Protocol passed: WebSearch ran 4 distinct queries across generality levels (author/upstream;
coherence/reduction program; specific 3-index/net + general forms; named-after/aliases); ChatGPT
MCP recorded `n/a` with the reproduced outage; local refs, nLab, nCatLab, Stacks, MO/MSE, arXiv all
checked/recorded.

### Literature summary (Phase 3)

Concept identified as: **no independent literature concept — an intermediate algebraic identity.**
It is one of the "intricate implications among elliptic relations" (Xu 2026's own phrasing) used to
prove standard EDSs are elliptic over a general commutative ring — concretely, the
`(addMulSub W c d)²`-scaled regrouping of the 10-term width-reduction `rel₆_eq₁₀`. The literature
names the *relation* (`rel₄` = Xu's "elliptic relation" ≡ Stange net ≡ Ward 3-index, arXiv:0710.1316
/ Ward) and the *coherence theorem* (van der Poorten–Swart "every Somos 4 is a Somos k",
arXiv:math/0412293). It does **not** name this particular scaled rearrangement; it is a bookkeeping
step inside such proofs.

Sources agree on the standard form: **yes** for the underlying relation and the coherence theorem;
**n/a** for this identity (no source names it).
Most general standard form (of what it asserts): an unconditional homogeneous polynomial identity in
the values of an arbitrary `W : ℤ → R` over an arbitrary `CommRing R`. There is no "more general"
standard formulation — it is already a `ring` identity at the `+ − ·` floor.
Disagreement with the literature: none — it is simply not a literature object.

---

### Generality analysis — `EllSequence.addMulSub_sq_mul_rel₄_eq₉`

Literature-standard form (Phase 3): no literature-standard "scaled `rel₄` identity". Its content is
a pure `ring` identity over `rel₄`/`rel₆`/`addMulSub`, all of which are already maximally general
(arbitrary `CommRing`, no hypotheses — established in the sibling `rel₄.md`, verdict MAXIMALLY
GENERAL).

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | (n/a — not a lit object)  | NO                  | The identity uses `+ − ·` only and needs commutativity for `ring`; already the floor. Inherited from `rel₄`/`rel₆`. |
| 2 | `(W : ℤ → R)`          | unconstrained sequence   | unconstrained             | NO                  | Pointwise polynomial expression in `W`; no structure assumed (NOT "elliptic", NOT a domain, NO characteristic). |
| 3 | `(c d m n r s : ℤ)`    | six integer indices      | (n/a)                     | NO                  | The two fixed + four free slots are exactly what the width-reduction needs; not a weakenable hypothesis. |
| 4 | (no extra hypotheses)  | unconditional            | unconditional             | —                   | Already hypothesis-free — there is nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (unconditional, over the `CommRing`/no-hypothesis floor
of its components `rel₄`/`rel₆`/`addMulSub`).
Number of weakening opportunities found: **0**.
Cost of restatement: n/a — nothing to restate. (So this is *not* `YES-but-generalise-first`: there
is no generalisation to perform.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses? | no | — (already `[CommRing R]`; `W` is a bare hypothesis as it must be) | — |
|  2 | sequences/metric → filters/nets/topology? | no | — (algebraic identity, no limits/topology) | — |
|  3 | construct object → universal-property class? | no | — (it is an equation, not a construction) | — |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | — |
|  5 | field/char-specific → weaken typeclass? | no | — (already `CommRing`, char-free) | — |
|  6 | 1-categorical → higher-categorical? | no | — (elementary commutative algebra) | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | — (the six ℤ indices are intrinsic to the EDS width-reduction) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. One-line reason: it is not a concept to reformulate — it is an
unconditional `ring` identity over the already-modern `rel₄`/`rel₆`/`addMulSub` primitives.

---

### Diamond / defeq risk — `EllSequence.addMulSub_sq_mul_rel₄_eq₉`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | It is a `theorem` (a `Prop`), introduces no instance/class/`def`. No search path affected. |
| 2 | Reducibility leak            | none    | A proved equation; nothing unfolds through it. |
| 3 | Non-canonical unfolding      | none    | Not a `simp` lemma here; it is stated and (currently) never even applied. |
| 4 | Instance priority collision  | n/a     | Not an `instance`. |
| 5 | Universe-polymorphism issues | none    | `R : Type u`; the statement is in `Prop`; no forced annotation. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE** (a hypothesis-free proved equation). No diamond/defeq concerns. (This is
neutral for the verdict — the negative signals are "unnamed", "`ring`-closed", "composable",
"unused", not risk.)

---

### Mathlib search-status: `EllSequence.addMulSub_sq_mul_rel₄_eq₉`

[A] Lean-Finder       scaled four-index elliptic relation / `(coefficient)² × rel₄` identity        no hits
[B] Loogle            `EllSequence.addMulSub_sq_mul_rel₄_eq₉`; `(EllSequence.addMulSub ?W ?c ?d)^2 * EllSequence.rel₄ ?W ?m ?n ?r ?s = _`  no hits — "unknown identifier" (whole `EllSequence` namespace absent from mathlib)
[C] LeanSearch        "elliptic relation squared coefficient reduction identity elliptic divisibility sequence"  no hits
[D] Grep mathlib src  `addMulSub_sq_mul` / `addMulSub` / `rel₄` / `rel₆` / `EllSequence` over `.lake/packages/mathlib/Mathlib/`  **no hits** — direct grep returned EMPTY across the entire tree, incl. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`. Only the unrelated `IsEllSequence`/`IsEllDivSequence`/`normEDS` predicates exist in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines, pin `d90090f`), which has NO four-index/`addMulSub`/`rel₄`/`rel₆`/`net` relational layer at all.
[E] Name pattern      `*_sq_mul_rel*` / `*addMulSub*` in mathlib tree                                no hits

Searched for the user's form (`addMulSub_sq_mul_rel₄_eq₉`, `(addMulSub)²·rel₄`) and the
literature-standard component forms (`rel₄`/`addMulSub`/`rel₆`; Stange's `net`; Ward's 3-index
relation). Note: the deferred `lean_loogle`/`lean_leansearch` MCP tools were not exposed on this run,
so [B]/[C] rely on (i) the authoritative mathlib-tree grep [D] and (ii) the identical "unknown
identifier" no-hit recorded in the sibling `rel₄.md`/`rel₆.md` runs for this same `EllSequence`
namespace — both decisive.

Concluded: **not in mathlib** (all methods + component forms exhausted; whole relational layer
absent). See Verdict for the crucial framing: it is mathlib's own authors' in-flight upstream code.

---

### Call sites — `EllSequence.addMulSub_sq_mul_rel₄_eq₉`

Internal use count: **0** — the symbol `addMulSub_sq_mul_rel₄_eq₉` occurs exactly once in the live
file (`EllipticDivisibilitySequence.lean`): its own declaration at line 344. `grep -c` over the file
returns **1** (the def line) and **0** other references.

External-to-file callers: **none.** The HasseWeil sibling fork
(`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`) is an *older/partial*
copy of this source: it has `rel₆_eq₁₀` (line 272) and the consumer `rel₄_of_fix₂` (which uses
`rel₆_eq₁₀` directly, line 366) but **does not even contain** `addMulSub_sq_mul_rel₄_eq₉` — a direct
grep there returns nothing. So this lemma exists *only* in the NagellLutz live file, and is used
nowhere.

| Caller | Usage |
|--------|-------|
| (none) | The actual width-reduction lemmas `rel₄_fix₁_of_fix₂` (line 427) and `rel₄_of_fix₂` (line 442) use `rel₆_eq₃` / `rel₆_eq₃'` / `rel₆_eq₁₀` **directly** — never `addMulSub_sq_mul_rel₄_eq₉`. The comments on lines 347/350 cross-reference `rel₆_eq₃'` and `rel₆_eq₁₀`, identifying this lemma as their `(addMulSub c d)²`-scaled regrouping — i.e. it is a documented *alternative phrasing* of the same algebra, stated for exposition but not on the proof path. |

Inline-derivation grep: the proof path to `rel₄_normEDS` (→ `isEllDivSequence_normEDS`) goes through
`rel₆_eq₁₀`/`rel₆_eq₃`/`rel₆_eq₃'`, **bypassing** this lemma entirely.

Composability signal: **0 internal uses, 0 external uses, content = one `ring` call after unfolding;
the load-bearing reduction is done by `rel₆_eq₁₀`. Strongly NO-composable-leaning** (and arguably an
orphan/dead intermediate).

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_sq_mul_rel₄_eq₉` be obtained from existing primitives in ≤3 calls?

Attempt 1: against the project's own primitives (the realistic case, since `addMulSub`/`rel₄`/`rel₆`
are the in-flight upstream defs).
  - Its **own proof is `simp_rw [rel₆, rel₄]; ring`** — i.e. unfold the two definitions (`rel₆` and
    `rel₄`, both reducible/`abbrev` or `def` with simp glue) and discharge with `ring`. That is the
    canonical "≤3 mathlib calls" shape: `simp_rw [rel₆]`, `simp_rw [rel₄]`, `ring` (or one fused
    `simp_rw [rel₆, rel₄]` + `ring` = two tactic calls).
  - It assumes **no** lemma about `W` — purely the *definitions* of `rel₆`/`rel₄`/`addMulSub` plus
    commutative-ring arithmetic. So once those primitives exist, this identity is reconstructible on
    demand by `ring`, with no creative input.
  - Result: **succeeds in ≤3 calls** (`simp_rw [rel₆, rel₄]; ring`).

Attempt 2: against *current* published mathlib.
  - Mathlib lacks `addMulSub`, `rel₄`, and `rel₆`, so the statement cannot even be *written* against
    today's mathlib — but this is the *same* gap that `rel₄`/`addMulSub` themselves face, and those
    are the genuine contribution being upstreamed. Once they land, this lemma is the ≤3-call `ring`
    discharge above.

Conclusion: **COMPOSABLE** — it is a hypothesis-free `ring` identity over `rel₆`/`rel₄`, reproduced
by its own one-line proof `simp_rw [rel₆, rel₄]; ring`. It is the textbook "derived equation a proof
can regenerate from the definitions", not a primitive that must be added. (It is *more* clearly
composable than its cousins `rel₆_eq₃`/`rel₆_eq₁₀`, since unlike them it has **zero** consumers — it
is not even load-bearing notation.)

---

## Verdict: `EllSequence.addMulSub_sq_mul_rel₄_eq₉`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): **no independent literature concept** — an intermediate "intricate
  implication among elliptic relations" (Xu 2026, arXiv:2604.05280) serving the coherence /
  width-reduction program (van der Poorten–Swart "every Somos 4 is a Somos k", arXiv:math/0412293).
  The literature names the *relation* (`rel₄`) and the *coherence theorem*, never this
  `(addMulSub)²·rel₄ = Σ addMulSub·rel₆` scaled rearrangement.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (unconditional, `CommRing` floor, 0
  weakenings); Phase 4c found no modern idiom. One-liner check: **`ring`-IDENTITY WITHOUT-EXEMPTION**.
- Mathlib search (Phase 5): **not in mathlib** (all methods + component forms; whole relational layer
  absent from the tree, incl. `DivisionPolynomial/`) — but mathlib also lacks its components, which
  are themselves in-flight upstream.
- Composition check (Phase 6): **COMPOSABLE** — its own proof `simp_rw [rel₆, rel₄]; ring` *is* the
  ≤3-call reconstruction from the definitions of `rel₆`/`rel₄`; no hypothesis on `W` is used.
- Call sites (Phase 6.0): **0 internal, 0 external** — the proof path uses `rel₆_eq₁₀` directly; this
  lemma is a stated-but-unused exposition of the same algebra (and is absent from the HasseWeil fork).
- Diamond/defeq risk (Phase 4.5): **NONE** (a hypothesis-free proved equation).

**Rationale.**

`EllSequence.addMulSub_sq_mul_rel₄_eq₉` is not a mathematical object mathlib should hold as a named
declaration: it is an **unconditional polynomial identity**, `(addMulSub W c d)² · rel₄ W m n r s =
[fixed signed combination of addMulSub·rel₆ terms]`, whose entire proof is `simp_rw [rel₆, rel₄];
ring` — unfold the two definitions and let `ring` finish. Its content is therefore exactly "the
definitions of `rel₆` and `rel₄` plus commutative-ring arithmetic", with no extra idea, no
hypothesis on `W`, and no appeal to any prior lemma. It is the `(addMulSub W c d)²`-scaled, regrouped
form of the 10-term width-reduction `rel₆_eq₁₀` (the in-source comments on lines 347/350 say so,
citing `rel₆_eq₃'` and `rel₆_eq₁₀`), and the literature — Ward; Stange's elliptic nets
(arXiv:0710.1316); van der Poorten–Swart's coherence theorem (arXiv:math/0412293); Xu's *On Elliptic
Sequences over Commutative Rings* (arXiv:2604.05280) — names the *relation* and the *coherence
theorem* but assigns no name to this intermediate scaled identity, because it is a proof step. It
clears the NO-composable gate on every axis: it is a `ring`-identity-without-exemption; it composes
from its neighbours in ≤3 calls (`simp_rw [rel₆, rel₄]; ring`); it is unnamed in the literature; and
— unlike even its sibling `rel₆_eq₁₀` — it has **zero call sites** (the actual reduction uses
`rel₆_eq₁₀` directly, and the HasseWeil fork omits this lemma entirely), so it is not even
load-bearing scaffolding. All signals point one way: `NO-composable-from-mathlib`.

**Crucial framing (consistent with the sibling reports).** The entire `addMulSub`/`rel₄`/`rel₆`/`net`
layer in this file is **mathlib's own authors' code** — David Kurniadi Angdinata (author of mathlib's
existing `EllipticDivisibilitySequence.lean`, identical copyright header) and Junyan Xu — sitting in
NagellLutz as a fork that runs *ahead* of mathlib master and discharges its open
`normEDS`-is-elliptic TODO, being **upstreamed via an open mathlib PR** (the elementary-algebraic
group-law / division-polynomial development announced by arXiv:2604.05280). So the right action for
this lemma is **not** "PR this `ring` identity to mathlib standalone": if it is kept at all, it
travels *inside* that PR as an optional internal step lemma over `rel₄`/`rel₆`. Against *today's*
mathlib it is non-writable only because its components are likewise not-yet-merged — and once they
land, it is a ≤3-call `ring` reconstruction. Either way the five-bucket label scoped to "should
AINTLIB add this as a standalone declaration to mathlib" is **NO**, and the precise reason is
composability (it is `simp_rw [rel₆, rel₄]; ring`), so **`NO-composable-from-mathlib`** rather than
`NO-mathlib-has-it`.

**WHY not (refactor-actionable).**
Mathlib does not currently have this lemma, but it should not gain it as an independent declaration:
it is a hypothesis-free `ring` identity whose own proof regenerates it from the definitions of
`rel₆`/`rel₄`. The building blocks are `EllSequence.rel₄`
(`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:103`; assessed `YES-add-as-is` —
the keystone, sibling `rel₄.md`), `EllSequence.rel₆` (`:302`; assessed `NO-composable` — a one-line
`abbrev`, sibling `rel₆.md`), and `EllSequence.addMulSub` (`:94`; part of the same upstream unit).
Composition sketch (= the lemma's own proof):
```lean
example (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s = /- the RHS -/ := by
  simp_rw [rel₆, rel₄]; ring
```
Call sites in our project (from Phase 6.0): **0** — and the load-bearing reduction is `rel₆_eq₁₀`.
Refactor plan: nothing to refactor — since the lemma is unused, the realistic action is either to
**delete it** as a stated-but-unreferenced intermediate, or to **let it ride** with the
`rel₄`/`rel₆`/`addMulSub` upstream PR (David Angdinata / Junyan Xu, arXiv:2604.05280) as an optional
internal step if the authors find the regrouped form expository. It is **never** a separate
AINTLIB→mathlib contribution.
Next action: do not PR it standalone; treat it as file-internal algebra that travels with (or is
inlined into / dropped from) the `rel₄` upstream PR.

---

## Next step

Do not propose `EllSequence.addMulSub_sq_mul_rel₄_eq₉` as a standalone mathlib addition. It is an
unconditional `ring`-closed identity — `(addMulSub W c d)² · rel₄ W m n r s =` a fixed
`addMulSub`-coefficiented combination of `rel₆` terms — proved by `simp_rw [rel₆, rel₄]; ring`,
i.e. a ≤3-call reconstruction from the definitions of `rel₆`/`rel₄`, with no hypothesis on `W`, no
name in the literature, and **zero call sites** (the reduction is carried by `rel₆_eq₁₀`). It belongs
*inside* the in-flight upstream PR of the `addMulSub`/`rel₄`/`rel₆` relational layer (David
Angdinata / Junyan Xu, arXiv:2604.05280) as optional internal algebra — or should simply be inlined
or deleted — never as a separate contribution. The actionable verdict:
**`NO-composable-from-mathlib`**.

Sources consulted: arXiv:2604.05280 (Xu, *On Elliptic Sequences over Commutative Rings*);
arXiv:math/0412293 (van der Poorten–Swart, *Recurrence Relations for Elliptic Sequences: every
Somos 4 is a Somos k*, BLMS 2006); arXiv:0710.1316 (Stange, elliptic nets); Ward, *Memoir on
Elliptic Divisibility Sequences* (cited in the file's `## References`); mathlib `d90090f`
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`.
