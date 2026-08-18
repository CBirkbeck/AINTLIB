# /mathlibable report — `preNormEDS`

> Step-9 mathlibable assessment (AINTLIB /overview), single declaration.
> Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
> Target: `preNormEDS` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:774`.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build is stale per task brief); reasoning from source.
- decl `preNormEDS`:        ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:774`
- kind:                     `def`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDSs and constructs
  normalised EDSs from initial terms (forked from `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

**Qualified name (VERIFIED).** The parse hint `preNormEDS` is correct. Line 774 sits inside
`section PreNormEDS` (line 704), which is a *plain `section`*, not a `namespace`. The nearest
`namespace` (`IsEllSequence`) closed at line 702. The only enclosing wrapper is the file-level
`@[expose] public section` (line 81). Hence the fully-qualified name is **`preNormEDS`** (root
namespace) — no namespace prefix. (Mathlib's copy is likewise in the root namespace.)

---

### Statement (Phase 1)

`preNormEDS b c d : ℤ → R` is a **definition**. For a commutative ring `R` and parameters
`b c d : R`, it is the auxiliary integer-indexed sequence underlying a normalised elliptic
divisibility sequence, with initial values `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d`, extended
to negative indices oddly. It is defined from the `ℕ`-indexed auxiliary `preNormEDS'` by

`preNormEDS b c d n  :=  n.sign * preNormEDS' b c d n.natAbs`.

The companion `preNormEDS'` is the genuine recursion (the EDS double/duplication recurrence
splitting into even/odd cases); `preNormEDS` is its odd extension to `ℤ`. This is the object used
to define `normEDS` and, downstream, the univariate `n`-division polynomials of elliptic curves
(omitting a factor of the bivariate 2-division polynomial — the "Angdinata normalisation").

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three normalisation parameters (`b` the duplication parameter; `c, d` the
  seed values `W(3), W(4)`).

Hypotheses: none (it is a total definition).

Conclusion (math): the function `ℤ → R`, `n ↦ sign(n) · preNormEDS'(b,c,d,|n|)`.
Conclusion (Lean): `ℤ → R` — n/a, definition.

---

### Size classification (Phase 2a)

Verdict: **BIG** (it is a named `def` introducing a mathematical construction — the auxiliary
sequence of a normalised EDS — and is a building block of a project main line). Recorded for
framing only; it does not gate the search width.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`n.sign * preNormEDS' b c d n.natAbs`).
One-liner verdict: **ONE-LINER** (`def`).

Exemption check is moot here: the decl is byte-identical to an existing mathlib `def` (Phase 5),
so the verdict is `NO-mathlib-has-it` regardless of any one-liner exemption. (For completeness:
mathlib ships it sealed, non-`@[reducible]`, with a docstring as a stable API anchor — i.e. the
"semantic-intent / API-name" exemption is the reason mathlib itself keeps it as a named def.)

Conclusion: ONE-LINER — exemption analysis not load-bearing; superseded by mathlib match.

---

### Literature search (Phase 3)

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "normalised elliptic divisibility sequence preNormEDS division polynomial Angdinata mathlib" | yes | `preNormEDS b c d n = sign(n)·preNormEDS'(b,c,d,|n|)`; aux seq for normalised EDS, seeds `0,1,1,c,d` | mathlib4 docs page lists `preNormEDS` directly; matches our statement exactly |
| 2 | WebSearch (general form / origin) | (same result set) "On Elliptic Sequences over Commutative Rings" (arXiv 2604.05280); Wikipedia "Elliptic divisibility sequence" | yes | EDS over a commutative ring; Ward's recurrence; the normalisation is `R`-general already | The `CommRing R` generality is the literature-general form; no field/domain needed |
| 3 | WebSearch (named-after / origin attribution) | (same result set) — Angdinata attribution | yes | "independently rediscovered by Angdinata during his formalization of standard EDSs in Lean's Mathlib" | The construction *originates in* the mathlib formalisation; it is a mathlib-native definition |
| 4 | ChatGPT MCP | (MCP down per task brief) | n/a | — | Fallback: WebSearch + direct mathlib-source read used instead; the source comparison (Phase 5) is dispositive |
| 5 | Local references | `.mathlib-quality/references/` for NagellLutz | n/a | — | Not consulted; the mathlib-source byte-identity already settles the verdict |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | Not an nLab/categorical topic; classical number theory. Recorded n/a. |
| 7 | nCatLab | — | n/a | — | Not a categorical concept. |
| 8 | Stacks Project | — | n/a | — | EDS recurrences are not a Stacks (scheme-theoretic AG) topic. |
| 9 | MathOverflow / MSE | (covered via WebSearch result set: arXiv math/0402415 "sign of an EDS", eprint 2008/444) | yes | EDS sign/divisibility literature; consistent with the `ℤ`-extension by `sign(n)` | Confirms the odd `sign`-extension is the standard integer indexing |
| 10 | recent arXiv (≤5y) | arXiv 2604.05280 (2026), eprint 2025/521 (Stange, division polynomials for isogenies) | yes | confirms the mathlib `preNormEDS` normalisation is the current standard, cites the Lean formalisation | The normalisation is now the literature reference point |

Sources:
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [On Elliptic Sequences over Commutative Rings (arXiv 2604.05280)](https://arxiv.org/pdf/2604.05280)
- [The sign of an elliptic divisibility sequence (arXiv math/0402415)](https://arxiv.org/pdf/math/0402415)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Division polynomials for arbitrary isogenies, K. Stange (eprint 2025/521)](https://eprint.iacr.org/2025/521.pdf)

#### Literature summary (Phase 3)

Concept identified as: the **auxiliary sequence of a normalised elliptic divisibility sequence**
(`preNormEDS`), in the Angdinata / mathlib normalisation used to build univariate division
polynomials of elliptic curves.
Sources agree on the standard form: **yes** — and crucially the "standard form" *is the mathlib
definition itself*; the recent literature (arXiv 2604.05280, eprint 2025/521) cites the Lean
formalisation as the reference.
Most general standard form: over an arbitrary `CommRing R` with parameters `b, c, d : R` — exactly
the form in front of us.
Generality dimensions where the literature varies: none that matter — `CommRing` is already the
maximal sensible base; the `ℤ` index and `sign`-extension are intrinsic to the construction.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): `preNormEDS (b c d : R) : ℤ → R` over `[CommRing R]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | EDS recurrence needs subtraction + multiplication + the comm-ring identities; this is already the maximal base used in the literature and in mathlib. |
| 2 | `(b c d : R)` | three ring elements | three ring elements | NO | These are the defining parameters; nothing to weaken. |
| 3 | index `ℤ` | integer index | integer index | NO | The construction is intrinsically `ℤ`-indexed (odd extension of a `ℕ` recurrence). |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to the mathlib/literature standard).
Weakening opportunities found: 0.

#### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | typeclass-ify "let X be a foo" preambles? | no | already a bare `def` over `[CommRing R]`. |
| 2 | sequences/metric → filters/topology? | no | finite algebraic recurrence; no topology. |
| 3 | construction → universal-property class? | no | it *is* a concrete recursive construction; that is the point (it backs division polynomials). |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure. |
| 5 | vector-space/field-specific → weaker typeclass? | no | already `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | classical NT. |
| 7 | concrete index `ℤ` → arbitrary additive structure? | no | the `ℤ`-indexing is essential to the EDS recurrence and the `sign`-extension. |

Modern-idiom verdict: **no** — this is already the contemporary mathlib formulation. (It is, in
fact, the very definition mathlib uses; the project copied it.)

---

### Diamond / defeq risk (Phase 4.5)

`def`, so in scope — but **n/a in practice**: the project decl is character-for-character identical
to the mathlib `def` (same body `n.sign * preNormEDS' b c d n.natAbs`, same attributes, same
non-reducibility). Whatever risk profile mathlib's own `preNormEDS` has, this clone inherits
exactly; there is no *new* risk to assess and nothing to add to mathlib. Overall risk: **NONE**
(it is the existing mathlib def).

---

### Mathlib search-status: `preNormEDS` (Phase 5)

[A] Lean-Finder       n/a (mathlib index tool) — superseded by direct source read.
[B] Loogle            n/a — superseded by direct source read.
[C] LeanSearch        n/a — superseded by direct source read.
[D] Grep mathlib src  `grep -rn "preNormEDS" .lake/packages/mathlib/`  → **HIT**.
[E] Name pattern      `def preNormEDS` in mathlib → **HIT** (root namespace).

**Direct source comparison (dispositive).** Mathlib defines `preNormEDS` at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:176`:

```lean
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs
```

The project's `preNormEDS` (line 774–775) is **byte-identical** (same signature `(n : ℤ) : R`,
same body, same docstring, same author header "David Kurniadi Angdinata", same root namespace,
same companion lemmas `preNormEDS_ofNat/_zero/_one/_two/_three/_four/_neg/_even/_odd` and the
underlying `preNormEDS'` with its `_zero/.../_even/_odd` lemmas). The project's
`EllipticDivisibilitySequence.lean` is an explicit **fork** of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (the task brief confirms this; the file's
copyright/author line matches mathlib's).

Searched for both the current form and the literature-standard form — they are the same form, and
mathlib has it.

Concluded: **found in mathlib as `preNormEDS`** (`Mathlib.NumberTheory.EllipticDivisibilitySequence`,
line 176); **identical form** (verbatim fork).

---

### Call sites — `preNormEDS` (Phase 6.0)

Internal use count: many — `preNormEDS` is used heavily within the same forked file (e.g.
`preNormEDS_ofNat/_neg/_even/_odd`, and `complEDS₂` at line 844 is defined in terms of
`preNormEDS (b^4) c d`), and by `normEDS` downstream. This is exactly mathlib's own usage pattern,
reproduced. The high internal-use count reflects that it is a genuine API anchor — *in mathlib*.

Inline-derivation grep: n/a — it is not re-derived inline; it is the named building block (as in
mathlib).

The call-site signal would lean YES-* for a *novel* def, but here the consumers are the forked
copies of mathlib's own consumers. The correct conclusion is that the project should depend on
mathlib's `preNormEDS`, not re-host it.

### Composition check (Phase 6)

Can `preNormEDS` be "derived from mathlib in ≤3 calls"? It need not be derived at all — it **is**
a mathlib `def`. The project's decl is replaced not by a composition but by an `import` of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and use of the existing `preNormEDS`.

Conclusion: **NOT-COMPOSABLE-but-IDENTICAL** → the operative bucket is `NO-mathlib-has-it`
(mathlib *has the exact decl*), not `NO-composable-from-mathlib`.

---

## Verdict: `preNormEDS`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): the standard form *is* the mathlib/Angdinata `preNormEDS`; recent
  arXiv/eprint sources cite the Lean formalisation as the reference.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS`** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:176`; **byte-identical** body and docstring.
- Composition check (Phase 6): n/a — exact decl already in mathlib; the project file is a verbatim fork.

**Rationale.**
The project's `EllipticDivisibilitySequence.lean` is an explicit fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, and `preNormEDS` is reproduced
character-for-character: same signature `def preNormEDS (n : ℤ) : R := n.sign * preNormEDS' b c d
n.natAbs`, same docstring, same author header (David Kurniadi Angdinata — the mathlib author), same
root namespace, same surrounding lemma suite. There is nothing to *add* to mathlib because mathlib
already contains this exact definition; indeed the construction *originated* in the mathlib
formalisation and the current number-theory literature now cites it. This is the cleanest possible
`NO-mathlib-has-it`.

**WHY not (refactor-actionable).**
Mathlib already has `preNormEDS` verbatim. The project carries a private fork of the whole EDS file
(presumably to extend it locally with the `complEDS₂` / 2-complement machinery and the
General/PID tracks the Nagell–Lutz development needs). The forked `preNormEDS` itself adds nothing
over mathlib's. Wherever the project genuinely needs *new* results, those should be stated against
mathlib's `preNormEDS` (via `import Mathlib.NumberTheory.EllipticDivisibilitySequence`), and the
duplicated definition deleted, so the project tracks mathlib's daily bumps instead of pinning a
stale copy.

- Existing mathlib decl:  `preNormEDS`
- Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:176`
- Our form follows in 0 lines — it is the *same* declaration:
  ```lean
  -- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
  example : (preNormEDS : R → R → R → ℤ → R) = preNormEDS := rfl  -- the mathlib decl IS ours
  ```
- Call sites in our project: the rest of the forked file + downstream Nagell–Lutz code.
- Refactor plan:
  1. Have the project `public import Mathlib.NumberTheory.EllipticDivisibilitySequence` instead of
     re-defining `preNormEDS'`, `preNormEDS`, and their `_zero/_one/_two/_three/_four/_ofNat/_neg/
     _even/_odd` lemma suites.
  2. Delete the duplicated definitions/lemmas (lines ~708–838 of the project file — the entire
     `preNormEDS'`/`preNormEDS` block) and keep only the *genuinely new* additions
     (`complEDS₂` and the complement/divisibility machinery that mathlib lacks — those are separate
     decls and out of scope for this report).
  3. Re-point any project lemmas that referenced the local `preNormEDS` at the mathlib one
     (names and argument order are identical, so this is mechanical).
- Caveat (project policy, not a blocker): this fork may be deliberate WIP — AINTLIB tolerates
  forking mathlib files to extend them on a `dev/` branch. The dedup is a *cleanup-on-`main`* task,
  not a producer task. So the actionable output is: file a cleanup ticket to **replace the forked
  `preNormEDS`/`preNormEDS'` block with a mathlib import**, gated on the local extensions
  (`complEDS₂` etc.) being upstreamed or re-based onto the mathlib definitions.

**Next action:** delete the duplicated `preNormEDS` (and `preNormEDS'`) from the project and import
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; re-point the project's genuinely-new EDS
extensions at mathlib's `preNormEDS`. (Coordinate via an AINTLIB cleanup ticket, since the file is
a deliberate fork.)

---

## Next step

Delete `preNormEDS`/`preNormEDS'` from `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
and `import Mathlib.NumberTheory.EllipticDivisibilitySequence` instead; keep only the project's
new additions (`complEDS₂`, the 2-complement / divisibility machinery), restated against mathlib's
`preNormEDS`.
