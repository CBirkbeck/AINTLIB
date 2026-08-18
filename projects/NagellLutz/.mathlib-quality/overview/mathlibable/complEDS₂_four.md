# /mathlibable report — `complEDS₂_four`

> **Headline:** This declaration — together with the entire `complEDS₂` block around it — is a
> **verbatim fork of mathlib**. `complEDS₂_four` is character-for-character identical to the lemma
> already in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:267` on the pinned mathlib rev
> (`d90090f`). Verdict: **NO-mathlib-has-it**.

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `complEDS₂_four`:    ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:865`
- qualified name:           `complEDS₂_four` — **no namespace prefix**. Between `end IsEllSequence`
                            (line 702) and line 865 there is only `section PreNormEDS` (line 704);
                            sections do not qualify names. Confirmed by grep: no `namespace` opens in
                            that range.
- kind:                     `lemma` (carries `@[simp]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDS and constructs
                            normalised EDSs (`normEDS`) from initial terms; a fork-and-extend of
                            mathlib's file (1667 lines vs mathlib's 547; the first ~half is copied).

### Statement (Phase 1)

`complEDS₂_four` evaluates the **2-complement sequence** `complEDS₂` of a (pre-)normalised EDS at the
index `k = 4`:

> For a commutative ring `R` and parameters `b c d : R`, the 2-complement sequence `complEDS₂ b c d`
> — the witness quotient satisfying `W(k) · complEDS₂(k) = W(2k)` for the pre-normalised EDS
> `W = preNormEDS (b⁴) c d` — takes at `k = 4` the closed-form value
> `complEDS₂(4) = c² · preNormEDS(b⁴,c,d)(6) − preNormEDS(b⁴,c,d)(5)²`.

This is one of a family of base-case evaluations (`complEDS₂_zero = 2`, `_one = b`, `_two = d`,
`_three = …`, `_four = …`) that put the unfolded `complEDS₂` into `@[simp]`-normal form at small
arguments. Mathematically it is the divisibility witness `W(8)/W(4)` written out via the EDS
recursion, with the parity factor `(if Even 4 then 1 else b) = 1` resolved.

Variables / typeclasses involved (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three normalising parameters of the EDS.

Hypotheses (Lean side): none (it is an unconditional evaluation identity).

Conclusion (math): `complEDS₂(4) = c²·W̃(6) − W̃(5)²` where `W̃ = preNormEDS (b⁴) c d`.

Conclusion (Lean):
`complEDS₂ b c d 4 = c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2`

Proof body: `by simp [complEDS₂, if_pos (by decide : Even (4 : ℤ))]` — unfold the definition, discharge
the parity `if` via `decide`, and let `simp` close the resulting numeric `preNormEDS` arithmetic.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` evaluation/base-case lemma — a specialisation of the definition `complEDS₂` at a
fixed small index. Not a named theorem, not a new structure, not a `## Main statements` entry.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (No defeq/diamond exemption analysis needed.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS `W(k) ∣ W(2k)` complement / 2-division / duplication formula                                    | partial | `W(k) ∣ W(2k)` is the *defining* divisibility property of an EDS (since `k ∣ 2k`) | Wikipedia "Elliptic divisibility sequence"; the explicit *quotient* `W(2k)/W(k)` is not separately named in the classical literature |
|  2 | WebSearch (general / named)      | "elliptic divisibility sequence" mathlib normEDS preNormEDS division polynomial Angdinata           | yes  | The `preNormEDS`/`normEDS` design + the 2-complement device are **mathlib's own** (Angdinata) | top hit is the mathlib docs page for this very file; EDS theory itself due to Morgan Ward (1940s) |
|  3 | WebSearch (aliases)              | duplication formula / 2-division polynomial cofactor for EDS                                         | partial | division polynomials `ψ`, the duplication `[2]P`, and `ψ_{2k}/ψ_k` are classical, but `complEDS₂` per se is a Lean implementation name | arxiv 1108.3051 (Stange/valuations), 1909.12654 — division-polynomial valuations, no named "complEDS₂" |
|  4 | ChatGPT MCP                      | standard form + generality + historical evolution of "the 2-complement / cofactor of an EDS"        | n/a  | MCP unavailable this session (per task note)         | covered by channels 1–3 + the decisive mathlib match below |
|  5 | Local references                 | `.mathlib-quality/references/` grep for "complEDS" / "EDS" / "division polynomial"                   | n/a  | references dir not consulted (assessment resolved by exact mathlib match) | the verdict does not turn on the lit standard form — mathlib has the decl identically |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                    | n/a  | not an nLab topic (number-theoretic recurrence, not a categorical concept) | — |
|  7 | nCatLab                          | —                                                                                                  | n/a  | not a categorical concept                            | — |
|  8 | Stacks Project                   | —                                                                                                  | n/a  | not a Stacks/algebraic-geometry-foundations concept (it's a concrete recurrence cofactor) | — |
|  9 | MathOverflow / Math.StackExchange| EDS quotient `W(2k)/W(k)` cofactor                                                                   | partial | discussion of EDS divisibility exists; no canonical name for this cofactor | — |
| 10 | recent arXiv (last 5 years)      | sequences associated to elliptic curves / division-polynomial valuations                            | partial | 1909.12654, 1101.3839 — EDS arithmetic; no `complEDS₂` analogue named | confirms it is an implementation device, not a literature object |

Protocol status: WebSearch ran 3 distinct queries at different generality levels; ChatGPT MCP recorded
`n/a` (down this session) with the gap covered by the exact mathlib match; local refs `n/a` (not
load-bearing here); nLab/nCatLab/Stacks/MO/arXiv each checked or `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: the **2-complement / cofactor sequence** `complEDS₂` of a (pre-)normalised EDS
— i.e. the witness for `W(k) ∣ W(2k)`, equal to `W(2k)/W(k)` up to the even/odd `b`-factor.
Sources agree on the standard form: **the underlying mathematics is classical** (EDS divisibility,
Morgan Ward 1940s; division polynomials), **but the specific object `complEDS₂` and its base-case
evaluations are mathlib's own implementation** (author D. K. Angdinata), not a separately-named
classical construction. `complEDS₂_four` is the `k = 4` evaluation of that mathlib object.
Most general standard form: the divisibility `normEDS k ∣ normEDS (2k)` (mathlib's
`normEDS_dvd_normEDS_two_mul`); `complEDS₂` is the explicit cofactor realising it. `complEDS₂_four`
is a fixed-index numeric corollary — there is no "more general" form of *it* (it is a point
evaluation; generality lives in the parent `complEDS₂` / the divisibility statement, both already in
mathlib).
Disagreement with the literature: none — and immaterial, since mathlib already contains this exact
declaration (Phase 5).

### Generality analysis — `complEDS₂_four`

Literature-standard form (from Phase 3): the EDS 2-divisibility `W(k) ∣ W(2k)` and its explicit
cofactor; `complEDS₂_four` is the cofactor's value at the fixed index `4`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (EDS coefficients live in a comm ring) | NO | already the natural/most-general carrier; `complEDS₂` and `preNormEDS` are defined over any `CommRing` |
| 2 | `(b c d : R)`          | three free ring elements | three free ring elements | NO | maximally general — universally quantified parameters |
| 3 | index `4`              | fixed literal `4` | a fixed small index (base-case enumeration) | NO (by design) | the *whole point* of `_four` is the specific value `k = 4`; the general statement is the parent `complEDS₂` / `preNormEDS_mul_complEDS₂`, both already in mathlib |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it is — a base-case point evaluation over an
arbitrary `CommRing`).
Number of weakening opportunities found: 0.
Cost of restatement: n/a (no restatement warranted).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Notes |
|----|--------------------------------------------------------------------------|----------|-------|
|  1 | bundled hypotheses → typeclasses?                                        | no       | already typeclass-driven (`[CommRing R]`); no bundled "let W be …" preambles |
|  2 | sequences/metric → filters/topology?                                     | no       | finite algebraic identity; no limiting/topological content |
|  3 | construction → universal-property class?                                 | no       | it is a numeric evaluation, not a construction |
|  4 | set+closure-predicate → bundled substructure?                            | no       | no substructure involved |
|  5 | vector-space/field-specific → weaken typeclass?                          | no       | already at `CommRing`, the natural minimum |
|  6 | 1-categorical → higher-categorical?                                      | no       | not categorical |
|  7 | concrete index → arbitrary monoid/group?                                 | no       | the concrete index `4` *is* the content; the index-general statement is the already-in-mathlib parent lemmas |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a fixed-index `@[simp]` evaluation lemma already stated in the
idiomatic mathlib form (it lives in mathlib, authored by a mathlib maintainer). No modernisation move.

### Mathlib search-status: `complEDS₂_four`

[A] Lean-Finder       n/a (resolved by direct source match — see [D])
[B] Loogle            n/a (resolved by direct source match)
[C] LeanSearch        n/a (resolved by direct source match)
[D] Grep mathlib src  `grep -nE "complEDS" .lake/packages/mathlib/.../EllipticDivisibilitySequence.lean`
                      → **HIT**: `complEDS₂_four` at line 267-269, plus the entire `complEDS₂`
                        block (`def` line 246; `_zero/_one/_two/_three/_four/_neg`,
                        `preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`,
                        `normEDS_dvd_normEDS_two_mul`, `complEDS₂_mul_b`).
[E] Name pattern      grep whole mathlib tree for `complEDS` → only this one file. Exact name present.

Searched for both: the user's current form (the `k = 4` evaluation) — **found identically**; and the
literature-standard form (the divisibility / cofactor) — also in mathlib
(`normEDS_dvd_normEDS_two_mul`, `preNormEDS_mul_complEDS₂`).

**Byte-for-byte comparison.** Project lines 844-877 vs mathlib lines 246-279 are *character-for-
character identical* across the whole `complEDS₂` block (verified via side-by-side `sed`). The
specific lemma:

```lean
@[simp]
lemma complEDS₂_four : complEDS₂ b c d 4 =
    c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2 := by
  simp [complEDS₂, if_pos (by decide : Even (4 : ℤ))]
```

is present verbatim in both. Pinned mathlib rev: `d90090f647cae4f4ad4da99c0ac8bab2ca8c34ab`
(`v4.31.0-rc2`, the AINTLIB consolidation rev).

Concluded: **found in mathlib as `complEDS₂_four`** (root namespace), file
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:267`; **identical form** (identical statement
*and* identical proof).

### Call sites — `complEDS₂_four`

Internal use count: **0** (within the NagellLutz project, excluding the two declaring EDS files).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — |

The only two occurrences of the name `complEDS₂_four` in the whole repo are the two copies of the
declaration itself:
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:865` (this decl)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:819` (a second fork copy
  in the project's `…Original.lean`)

Inline-derivation grep (re-derived elsewhere without using `complEDS₂_four`?): none — it is a `@[simp]`
lemma; downstream sites that need it get it implicitly via `simp`, not by name. Its job is to be in the
default simp set, which is *also* true of the mathlib copy.

What the pattern tells us: K = 0 named uses, present only because the **entire `complEDS₂` API block was
copied verbatim from mathlib** into the project's forked file. It is not bespoke project API — it is
duplicated mathlib API. This *reinforces* NO-mathlib-has-it (the fork should track mathlib, not re-host
it).

### Composition check (Phase 6)

Can `complEDS₂_four` be derived from mathlib in ≤3 chained calls? — **Moot, but yes trivially**: it
*is* a mathlib lemma, so the "derivation" is the identity `complEDS₂_four` (0 calls). If one instead
asks whether the statement follows from other mathlib primitives: `by simp [complEDS₂]` (unfold +
`decide` the parity) closes it, exactly as the proof body does — a 1-line trivial simp.

Conclusion: **NOT-COMPOSABLE in the "needs a new lemma" sense is irrelevant** — the lemma already
exists in mathlib verbatim, so the operative verdict is NO-mathlib-has-it, not NO-composable.

## Verdict: `complEDS₂_four`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): `complEDS₂` is mathlib's own implementation device (author D. K.
  Angdinata) for the classical EDS divisibility `W(k) ∣ W(2k)`; `complEDS₂_four` is its `k = 4`
  evaluation. No separately-named classical object.
- Generality analysis (Phase 4): MAXIMALLY GENERAL over `CommRing`; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `complEDS₂_four`**,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:267` — identical statement *and* identical
  proof (byte-for-byte; whole `complEDS₂` block matches).
- Composition check (Phase 6): n/a — the decl already exists upstream.

**Rationale:**

The NagellLutz project deliberately **forks** mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
into `LutzNagell/EllipticDivisibilitySequence.lean` (the project's `DivisionPolynomial.lean:13` comment
states it "imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to
avoid…", and the file is a 1667-line superset whose opening half is copied from mathlib's 547-line
original and then extended with new `complEDS'`/`complEDS`/`Param` machinery). `complEDS₂_four` sits in
that copied opening half. It is **identical — statement and proof, character for character — to the
mathlib lemma of the same name** on the pinned consolidation rev `d90090f`. There is nothing to
contribute: mathlib already has it.

This is the textbook NO-mathlib-has-it case the project context flagged ("this decl may ALREADY be in
mathlib — check those mathlib files first"). The right disposition is not a mathlib PR but de-duplication
within AINTLIB: the project's forked EDS file should, wherever the fork's extension goals allow, re-use
mathlib's `complEDS₂_four` (and the rest of the verbatim-copied block) rather than re-host it. If the
fork must keep its own copy for import-cycle / extension reasons, that copy is still not a mathlib
candidate — it is a maintenance mirror of upstream.

**WHY not (refactor-actionable):**
Mathlib already has this lemma **verbatim**. The user's form *is* mathlib's form — no specialisation
step is even needed; they are the same lemma (same `@[simp]` attribute, same `c ^ 2 * preNormEDS (b^4)
c d 6 - preNormEDS (b^4) c d 5 ^ 2` RHS, same `simp [complEDS₂, if_pos …]` proof).

Existing mathlib decl:        `complEDS₂_four` (root namespace)
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:267`
Our form follows in ≤1 line:  it is literally the same lemma —
```lean
example (b c d : R) : complEDS₂ b c d 4 =
    c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2 :=
  complEDS₂_four            -- mathlib's lemma, if the project imports the mathlib file
```
Call sites in our project (from Phase 6.0):  K = 0 (named); the decl exists only because the whole
`complEDS₂` block was copied into the fork.

Refactor plan (AINTLIB-internal, NOT a mathlib PR):
1. This is a **fork-dedup** task, not a mathlibable-contribution task. Per AINTLIB's CLEANER rules,
   the cross-project dedup lane owns it. The verbatim-copied mathlib block in
   `LutzNagell/EllipticDivisibilitySequence.lean` (the `complEDS₂` def + `_zero/_one/_two/_three/
   _four/_neg`, `preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`,
   `complEDS₂_mul_b`) duplicates `Mathlib.NumberTheory.EllipticDivisibilitySequence`.
2. Determine whether the fork still needs its own copy. The `DivisionPolynomial.lean:13` comment
   suggests the fork exists to *extend* the file (add `complEDS'`/`complEDS`) while avoiding a
   mathlib import constraint. If the extension can instead `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence` and add only the *new* material, delete the
   copied block (including `complEDS₂_four`) and let the mathlib lemma serve. The second copy in
   `…EllipticDivisibilitySequenceOriginal.lean:819` is an even clearer dead duplicate.
3. If the fork genuinely cannot import mathlib's version (true import cycle), keep the copy but mark
   it explicitly as an upstream mirror — it remains a non-candidate for mathlib (mathlib has it).
4. There is **no mathlib PR** to open: opening one would re-submit an existing lemma.

Next action: hand to AINTLIB's cross-project **dedup** cleanup lane (file a `lane:cleanup` GitHub
issue against `CBirkbeck/AINTLIB`): "NagellLutz EDS fork re-hosts mathlib's `complEDS₂` block
verbatim — dedup against `Mathlib.NumberTheory.EllipticDivisibilitySequence` or document as an
upstream mirror." Do **not** open a mathlib PR.

---

## Next step

Hand to AINTLIB's cross-project dedup cleanup lane (`lane:cleanup`): the NagellLutz EDS fork re-hosts
mathlib's `complEDS₂` block (incl. `complEDS₂_four`) verbatim — either re-use
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and delete the copy, or document the fork as a
deliberate upstream mirror. No mathlib PR — mathlib already has this declaration identically.
