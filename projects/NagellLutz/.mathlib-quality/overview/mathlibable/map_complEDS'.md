# /mathlibable report — `map_complEDS'`

**TL;DR — `NO-mathlib-has-it`.** The project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork/extension of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, and `map_complEDS'` is present in
that mathlib file **verbatim** (same statement, same `@[simp]`, same proof). This is a
duplicated declaration, not a new contribution.

---

### Baseline (Phase 0)
- lake build:               not re-run (project's local build is known stale per the task brief; assessment reasons from source, which is sufficient because the dispositive comparison is a textual identity against the pinned mathlib source on disk).
- decl `map_complEDS'`:      ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1652` (with `@[simp]` on line 1651).
- qualified name:            **`map_complEDS'`** — VERIFIED. The only enclosing `namespace`/`end` pairs near the decl are `section ComplEDS` (`end ComplEDS`, line 1639) and `section Map` (`end Map`, line 1667); both are `section`s, not `namespace`s. The decl lives at the file's **root namespace**, exactly as in mathlib. Parsed base name `map_complEDS'` is correct and fully qualified.
- kind:                      lemma.
- has sorry:                 no.
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS, normalised EDS (`normEDS`), complement sequences (`complEDS₂`, `complEDS'`, `complEDS`), and their ring-hom functoriality. Header credits **David Kurniadi Angdinata** (the mathlib EDS author); the docstrings match the mathlib file line-for-line.

### Statement (Phase 1)

`map_complEDS'` states that the complement-sequence construction `complEDS'` for a normalised
elliptic divisibility sequence **commutes with ring homomorphisms**. Concretely: for a ring
homomorphism `f : R →+* S`, base data `b, c, d : R`, an index `k : ℤ` and a length `n : ℕ`,

  `f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n`.

It is the naturality / base-change compatibility of the `complEDS'` sequence under `f`,
i.e. `complEDS'` is a polynomial-with-integer-coefficients expression in `(b, c, d)`, so applying
`f` to its value equals evaluating it at the images `(f b, f c, f d)`. Tagged `@[simp]` so the
simplifier can push ring homs through `complEDS'`.

Variables / typeclasses involved (Lean side):
- `{R : Type u} [CommRing R]` — source commutative ring (carries `b c d`).
- `{S : Type v} [CommRing S]` — target commutative ring.
- `(f : R →+* S)` — the ring homomorphism that the construction commutes with.
- `(b c d : R)` — base data of the normalised EDS.
- `(k : ℤ)`, `(n : ℕ)` — index and term position of the complement sequence.

Hypotheses (Lean side): none beyond the typeclass/parameter context (it is an unconditional
functoriality identity).

Conclusion (math): `complEDS'` commutes with `f`, i.e. it is natural in the base ring.
Conclusion (Lean): `f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n`.

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: A `@[simp]` functoriality glue lemma (`f` commutes with a construction) — a helper, not a
named theorem and not a new structure. It is one of a family `map_preNormEDS' / map_preNormEDS /
map_complEDS₂ / map_normEDS / map_complEDS' / map_complEDS`, all the same shape.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (The proof body is a short induction, not a
one-line definition.) No defeq/diamond/API-name considerations apply.

### Literature search table (Phase 3)

| #  | Channel                          | Query / action                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" functoriality / ring homomorphism / base change | n/a  | —                   | Not load-bearing: this is a Lean-internal `@[simp]` naturality lemma for a *mathlib-defined* construction (`complEDS'`), not a named classical theorem. There is no "literature standard form" of a functoriality glue lemma to weigh the Lean form against. The dispositive fact is the verbatim mathlib match (Phase 5), which moots the lit sweep. |
|  2 | WebSearch (general form)         | division polynomials / EDS base change under ring maps                          | n/a  | —                   | Same reasoning. The mathematics ("division polynomials / EDS terms are integer polynomials in the coefficients, hence commute with ring maps") is folklore (Ward; Silverman, *Arithmetic of Elliptic Curves*, exercises on division polynomials) but is not a citable "form" for this glue lemma. |
|  3 | WebSearch (named-after/aliases)  | Ward elliptic divisibility sequence; Morgan Ward 1948 Memoir                    | n/a  | —                   | The *underlying construction* traces to M. Ward, *Memoir on Elliptic Divisibility Sequences* (Amer. J. Math. 70, 1948), cited in the module docstring. That is provenance for `complEDS'`/`normEDS`, not for the functoriality lemma. |
|  4 | ChatGPT MCP                      | (unavailable in this environment per task brief; fallbacks used)               | n/a  | —                   | MCP down; substituted by the direct mathlib-source comparison, which is conclusive. |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                           | n/a  | —                   | Directory absent (only `overview/` exists under `.mathlib-quality/`). Recorded n/a. |
|  6 | nLab                             | elliptic divisibility sequence                                                 | n/a  | —                   | nLab has no dedicated EDS page; not a category-theoretic concept. Functoriality of a polynomial construction is generic. |
|  7 | nCatLab                          | —                                                                              | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project                   | —                                                                              | n/a  | —                   | Not an algebraic-geometry stacks concept (EDS sit in arithmetic of elliptic curves; division polynomials appear, but not this glue lemma). |
|  9 | MathOverflow / Math.SE           | elliptic divisibility sequence ring homomorphism                               | n/a  | —                   | No specific result needed; the math content (integer-polynomial ⇒ commutes with ring maps) is standard and uncontested. |
| 10 | recent arXiv (≤5 yr)             | EDS / division polynomial formalisation                                        | n/a  | —                   | The relevant "source" is mathlib itself (Angdinata's EDS development), which already contains this exact lemma. |

### Literature summary (Phase 3)

Concept identified as: **functoriality (base-change / ring-hom compatibility) of the complement
sequence `complEDS'` of a normalised elliptic divisibility sequence** (Ward EDS theory; division
polynomials of elliptic curves).
Sources agree on the standard form: n/a — there is no separate "literature standard form" for a
Lean `@[simp]` naturality lemma; the mathematical content (an integer-coefficient polynomial
construction commutes with ring homomorphisms) is universally standard and trivially true.
Most general standard form: "any polynomial-with-ℤ-coefficients construction in the base data
commutes with ring maps." The Lean lemma is exactly this for `complEDS'`.
Disagreement with the literature: none.

### Generality analysis (Phase 4)

| # | Parameter / hypothesis  | Current Lean form          | Literature-standard form        | Weaker form exists? | Reason |
|---|-------------------------|----------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`, `[CommRing S]` | commutative rings   | commutative rings                | NO                  | `complEDS'`/`normEDS` are defined over `CommRing` (subtraction + commutativity used in the recursion); this is already the natural minimal setting, and it matches mathlib's own definition. |
| 2 | `f : R →+* S`            | ring homomorphism          | ring homomorphism               | NO                  | Naturality is *with respect to* a ring hom; you cannot weaken the morphism class and keep the statement. |
| 3 | `k : ℤ`, `n : ℕ`         | integer index, ℕ length    | same                            | NO                  | Indices of the sequence; intrinsic to `complEDS'`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is identical to mathlib's own, over `CommRing`).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1 | bundled hyps → typeclasses? | no | already a clean `RingHom` statement. |
| 2 | sequences/metric → filters/topology? | no | purely algebraic identity. |
| 3 | construction → universal property? | no | `complEDS'` is an explicit recursive construction; functoriality is the right statement. |
| 4 | set+closure → bundled substructure? | no | not a substructure result. |
| 5 | vector-space/field → module/ring weakening? | no | already at `CommRing`, the minimal natural setting. |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index → general algebraic index? | no | `k : ℤ`, `n : ℕ` are intrinsic to the EDS indexing. |

Modern idiom available: **no**. The lemma is already in the idiomatic mathlib form — indeed it
**is** the mathlib form, since mathlib defines this exact lemma. No reformulation would improve it.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

### Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a (mathlib index stale locally; superseded by direct source read) — see [D].
[B] Loogle            `f (complEDS' _ _ _ _ _) = complEDS' (f _) (f _) (f _) _ _` — pattern matches the mathlib decl; superseded by [D].
[C] LeanSearch        "ring hom commutes with complement elliptic divisibility sequence" — superseded by [D].
[D] Grep mathlib src  `grep -nE "complEDS|map_complEDS" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **HIT**. `map_complEDS'` is defined at **`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:534`** (with `@[simp]` at 533), inside `section Map`.
[E] Name pattern      `map_complEDS'` present in mathlib at the **root namespace** — exact qualified-name match.

Direct source comparison (the decisive evidence):

```
-- mathlib  (.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:533)
@[simp]
lemma map_complEDS' (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n := by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

-- project  (projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1651)
@[simp]
lemma map_complEDS' (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n := by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂,
      map_pow, map_mul, map_sub]   -- identical lemma set, only line-wrapped differently
    repeat rw [ih _ <| by linarith only]
```

The statement is **character-for-character identical**; the proof differs only in the line-wrap of
the `simp only` argument list. The supporting decls used in the proof (`complEDS'_even`,
`complEDS'_odd`, `map_normEDS`, `map_complEDS₂`, `complEDSRec'`) all exist in mathlib too — the
whole `ComplEDS` + `Map` machinery was forked from mathlib (matching docstrings, same author
attribution to D. K. Angdinata).

**Re-verified 2026-06-21 against the on-disk pinned mathlib.** `lakefile.toml` pins
`rev = "09b373db6e24"`; the vendored checkout `.lake/packages/mathlib` is at git HEAD
`09b373db6e247a35cfa5e44578c09a20e7c97271` (matches the pin). At that exact revision,
`map_complEDS'` is present at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:534`
(`@[simp]` at 533), **character-for-character identical** in statement and proof (the project body
at line 1657, `@[simp]` at 1656, only line-wraps the `simp only` list differently). So the
verbatim duplication still holds at the project's *current* mathlib pin — not merely at the earlier
`d90090f` bump.

Concluded: **found in mathlib as `map_complEDS'` (`Mathlib.NumberTheory.EllipticDivisibilitySequence`); identical form.**

### Call sites (Phase 6.0) — `map_complEDS'`

Internal use count: **0** (within the NagellLutz project, not counting the declaring file).
External-to-file callers: 1 file, but it is **another copy of the same file**, not a genuine consumer.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1559` | `lemma map_complEDS' (k : ℤ) (n : ℕ) :` — this is the **declaration** of a duplicate copy (`…Original.lean` is a sibling fork of the same mathlib file), not a *use* of the lemma. |

Inline-derivation grep (re-derived elsewhere without using `map_complEDS'`?): none found.

So `map_complEDS'` has **zero real consumers** in the project — consistent with it being dead,
duplicated mathlib code carried along with the EDS fork rather than API the project actually
invokes.

### Composition check (Phase 6)

Can `map_complEDS'` be derived from mathlib in ≤3 chained calls? **Yes, trivially: it IS mathlib.**

Attempt 1: `Mathlib.NumberTheory.EllipticDivisibilitySequence.map_complEDS' (f := f) (b := b) (c := c) (d := d) k n`
  - Mathlib decls used: `map_complEDS'` itself.
  - Result: succeeds — the project statement is definitionally the mathlib statement, so the
    mathlib lemma closes it directly (a 0-step "composition": just use the existing lemma).

Conclusion: this is the degenerate case — not "composable from primitives" but **literally
already present**. The correct bucket is therefore `NO-mathlib-has-it`, which dominates
`NO-composable-from-mathlib` when the exact decl exists.

---

## Verdict: `map_complEDS'`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): no separate literature form for a `@[simp]` naturality glue lemma; the underlying EDS construction is Ward's, already in mathlib (Angdinata).
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's own form over `CommRing`; no weakening or modernisation available.
- Mathlib search (Phase 5): **found in mathlib as `map_complEDS'`** at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:534`; **statement character-for-character identical**.
- Composition check (Phase 6): degenerate — the mathlib lemma closes the goal directly; 0 internal call sites in the project.

**Rationale:**

The NagellLutz project file `LutzNagell/EllipticDivisibilitySequence.lean` is an extended **fork**
of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author attribution to David
Kurniadi Angdinata, line-for-line-matching docstrings, same `IsEllSequence` / `preNormEDS` /
`normEDS` / `complEDS₂` / `complEDS'` / `complEDS` development plus extra `EllSequence`-namespace
material the project adds). `map_complEDS'` is one of the *forked-from-mathlib* declarations, not a
project addition: mathlib already contains it verbatim — same signature
`f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n`, same `@[simp]`, same
`complEDSRec'`-induction proof with the same `simp only` lemma set. The only textual difference is
where the `simp only` argument list wraps across lines.

Because the exact declaration is already in mathlib, no generality, modernisation, or composition
question arises in the project's favour — the work to "add it" was already done upstream. The
declaration has **zero genuine call sites** in NagellLutz (the single grep hit is the *declaration*
of yet another duplicate in the sibling `…Original.lean`). It is duplicated mathlib code that the
fork carries along; the project should depend on mathlib's `map_complEDS'` rather than re-state it.

**WHY not (refactor-actionable):**
mathlib already has this lemma, in the identical form, reachable by `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` (which the repo already uses elsewhere — e.g.
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:11`). The project's copy
is redundant. The right move is to stop forking the mathlib `ComplEDS`/`Map` API and instead import
it; `map_complEDS'` then comes for free with the same name (root namespace, exact match) and `@[simp]`
behaviour.

Existing mathlib decl:        `map_complEDS'` (root namespace of `Mathlib.NumberTheory.EllipticDivisibilitySequence`).
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:534` (`@[simp]` at 533).
Our form follows in ≤1 line (in fact it is the same statement):

```lean
example {R : Type*} [CommRing R] {S : Type*} [CommRing S] (f : R →+* S)
    (b c d : R) (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n :=
  map_complEDS' k n   -- the mathlib lemma, applied directly
```

Call sites in our project (from Phase 6.0): **0** genuine (1 spurious hit = a duplicate declaration
in `…Original.lean`).

Refactor plan:
1. Delete the project-local `map_complEDS'` (lines 1651-1660) from
   `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`.
2. Since there are **0 real consumers**, no call-site rewrites are needed. If/when the project does
   need this naturality, `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and use the
   upstream `map_complEDS'` (same name, same arguments `k n`).
3. Note: this lemma is part of the whole forked `ComplEDS`+`Map` block. The dedup is most naturally
   done wholesale — replace the project's local fork of the upstreamed EDS API with an `import` of
   the mathlib module — rather than lemma-by-lemma. The same `NO-mathlib-has-it` verdict applies to
   its siblings (`map_preNormEDS'`, `map_preNormEDS`, `map_complEDS₂`, `map_normEDS`, `map_complEDS`)
   and to the underlying defs/lemmas wherever they are verbatim mathlib copies.
4. The same applies to the duplicate in `…Original.lean:1559`.

**Caveat for the human:** confirm the fork was *not* deliberately kept divergent (e.g. carrying a
pre-bump snapshot or a patched variant that upstream lacks). The on-disk mathlib pin `d90090f647ca`
already contains `map_complEDS'` identically, so for this lemma there is no divergence — but the
wholesale "import instead of fork" refactor (step 3) is a project-policy call that should go through
the normal cleanup/dedup workflow, not be done blind.

---

## Next step

Delete the project-local `map_complEDS'` (and, as a unit, the forked `ComplEDS`/`Map` EDS block it
belongs to) and depend on `import Mathlib.NumberTheory.EllipticDivisibilitySequence`. No call-site
updates are required (0 genuine consumers). Route the wholesale de-fork through an AINTLIB cleanup
ticket since it spans many verbatim-duplicated declarations.
