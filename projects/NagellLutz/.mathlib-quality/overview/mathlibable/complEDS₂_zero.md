# /mathlibable report — `complEDS₂_zero`

## Verdict: NO-mathlib-has-it

The declaration is a **byte-for-byte duplicate** of a lemma already in mathlib.
The NagellLutz project file is a fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author, same
copyright header, same `complEDS₂` API), and `complEDS₂_zero` is identical in
both — same statement, same `@[simp]` attribute, same proof.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source + mathlib package source.
- decl `complEDS₂_zero`:     resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:849`.
- kind:                      `lemma` (`@[simp]`)
- has sorry:                 no
- enclosing namespace:       none — inside `@[expose] public section` (line 81) and `section PreNormEDS` (704–879), but the `namespace EllSequence` at line 90 was closed at line 597. So the qualified name carries **no namespace prefix**.
- qualified name:            **`complEDS₂_zero`**  (VERIFIED — matches the parsed base name; no namespace)
- module docstring summary:  Elliptic divisibility sequences; defines `IsEllSequence`/`preNormEDS`/`normEDS`/`complEDS₂`/`complEDS`; a fork of mathlib's EDS file extended with the NagellLutz divisibility track.

### Statement (Phase 1)

`complEDS₂_zero` states that the **2-complement sequence** of a normalised EDS,
evaluated at `0`, equals `2`.

The 2-complement `Wᶜ₂ : ℤ → R` of a normalised elliptic divisibility sequence
`W` is the sequence witnessing the divisibility `W(k) ∣ W(2k)`, i.e. the unique
sequence with `W(k) · Wᶜ₂(k) = W(2k)`. In the EDS duplication formulas it is the
"even part" cofactor. Its value at the origin is `2` (matching `W(2k)/W(k) → 2`
in the degenerate/identity case; consistent with `complEDS₂_one = b`,
`complEDS₂_two = d`).

Concretely `complEDS₂ b c d k` is defined (line 844) as
`(preNormEDS (b^4) c d (k-1)^2 * preNormEDS (b^4) c d (k+2) − preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1)^2) * (if Even k then 1 else b)`,
and at `k = 0` the `preNormEDS` initial values (`W(0)=0, W(1)=1, W(2)=1, W(-1)=−1, W(-2)=−1`) collapse this to `1 + 1 = 2`.

Variables (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three initial parameters of the normalised EDS.

Hypotheses: none.

Conclusion (math): `Wᶜ₂(0) = 2`.
Conclusion (Lean): `complEDS₂ b c d 0 = 2`.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: an initial-value (`simp`) lemma for a defined sequence — a one-line
boundary computation, not a structure or a named theorem.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line check **n/a**.
(For the record the proof is a single `simp` line; but 2b only governs defs.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" duplication W(2k) cofactor / 2-complement             | partial | EDS satisfy W(2n) divisibility & duplication recursions (Ward) | the *named* object "2-complement sequence `Wᶜ₂`" is mathlib/Angdinata terminology, not a textbook term |
|  2 | WebSearch (general form)         | Ward elliptic divisibility sequence recurrence W(m+n)W(m-n) ... initial values         | yes  | Ward 1948 "Memoir on elliptic divisibility sequences" | classical source for the EDS recursion; no per-term "complEDS₂(0)=2" naming |
|  3 | WebSearch (named-after / aliases)| Shipsey / Stange "elliptic nets"; division polynomials ψ₂ₙ / ψₙ ratio                  | yes  | elliptic nets generalise EDS; ψ_{2n}=ψ_n·(...) duplication | the cofactor exists in the division-polynomial identities; not separately named |
|  4 | ChatGPT MCP                      | (per task: ChatGPT MCP may be down) — standard form / generality / history of the EDS 2-complement | n/a | — | MCP unavailable; covered by channels 1–3 + the decisive mathlib-source hit |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for EDS / complement           | n/a  | (references dir not consulted; moot)                  | the mathlib-source duplicate is dispositive — lit standard-form is not needed to decide |
|  6 | nLab                             | "elliptic divisibility sequence"                                                       | n/a  | nLab has no dedicated EDS page                         | not a category-theoretic concept |
|  7 | nCatLab (if categorical)         | —                                                                                      | n/a  | —                                                     | not categorical |
|  8 | Stacks Project (if alg geom)     | division polynomial / elliptic divisibility                                            | n/a  | Stacks has no EDS / division-polynomial entry          | EDS is arithmetic, outside Stacks scope |
|  9 | MathOverflow / Math.StackExchange| elliptic divisibility sequence W(2n)/W(n)                                               | partial | discussions of EDS duplication exist                 | no canonical name for the per-term cofactor at 0 |
| 10 | recent arXiv (last 5 years)      | elliptic divisibility sequence / elliptic nets cofactor                                | partial | Stange & successors on elliptic nets                  | the construction is research-level, not a fixed textbook normal form |

### Literature summary (Phase 3)

Concept identified as: the **2-complement** (even cofactor) of a normalised
elliptic divisibility sequence — the sequence `Wᶜ₂` with `W(k)·Wᶜ₂(k)=W(2k)`.
Underlying theory: Ward (1948) elliptic divisibility sequences; division
polynomials ψₙ; Stange's elliptic nets.
Sources agree on the standard form: **no fixed textbook "standard form"** — the
per-term object and its name (`Wᶜ₂`, "2-complement") are mathlib/Angdinata
nomenclature, internal to the EDS division-polynomial development. The value
`Wᶜ₂(0) = 2` is an initial-condition computation specific to this construction,
not a separately named classical result.
This is **moot for the verdict**: the decisive fact is that mathlib already
contains this exact construction and this exact lemma (Phase 5).

### Generality analysis — `complEDS₂_zero`

Literature-standard form: there is no more-general external "standard form" to
target; the object lives over an arbitrary `CommRing R`, which is already the
fully general setting. The lemma is `∀ (R) [CommRing R] (b c d : R), complEDS₂ b c d 0 = 2`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | `preNormEDS` and the EDS recursion are defined over a `CommRing`; already maximal. Mathlib uses the identical typeclass. |
| 2 | `(b c d : R)`          | three ring params | three ring params        | NO                  | intrinsic to a normalised EDS. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's, which is the
canonical form).
Number of weakening opportunities found: 0.

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. This is a finite ring-equation initial value
(`Wᶜ₂(0)=2`) for a concrete sequence; there is no topology to filter-ise, no
construction to replace with a universal property, no vector-space/metric
assumption to weaken. Mathlib's own copy already uses exactly this formulation,
so by definition it is the contemporary mathlib idiom.

### Diamond / defeq risk — `complEDS₂_zero`

n/a — declaration kind is `lemma` (Phase 4.5 runs for `def`/`class`/`instance` only).

### Mathlib search-status: `complEDS₂_zero`

[A] Lean-Finder       "elliptic divisibility sequence complement W(2k)"        — superseded by direct source hit
[B] Loogle            `complEDS₂ _ _ _ 0 = 2` / `complEDS₂`                     — n/a: direct grep of the mathlib package source found the decl verbatim
[C] LeanSearch        "value of 2-complement of EDS at zero is 2"              — superseded by direct source hit
[D] Grep mathlib src  `complEDS₂` / `complEDS₂_zero` in `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — **HIT**
[E] Name pattern      `complEDS₂_zero`                                          — **HIT** (exact name)

Searched for both the user's current form and the general form: they coincide,
and **mathlib has the identical decl**.

Concluded: **found in mathlib as `complEDS₂_zero`; identical form**
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:251`, `@[simp]` at :250).
The parent `def complEDS₂` is at mathlib line 246, also identical. A `diff` of the
project lines 848–850 against mathlib lines 250–252 produced **no output**
(byte-for-byte identical, including the `simp [complEDS₂, one_add_one_eq_two]`
proof).

### Call sites — `complEDS₂_zero`

Internal use count (excluding the declaring file): the name `complEDS₂_zero` is
used at lines 1589 within the **same** project file
(`...complEDS_zero, complEDS₂_zero...` in the `complEDS_even` proof). No uses in
other project files were found. Because this whole file is a fork of the mathlib
file, every consumer is the project's own forked copy of mathlib code — not an
independent downstream need.

| Caller file:line                                            | Usage pattern (one-line excerpt)             |
|-------------------------------------------------------------|----------------------------------------------|
| EllipticDivisibilitySequence.lean:1589 (same file)          | `· simp [complEDS_zero, complEDS₂_zero]`     |

Inline-derivation grep: (none) — no other file re-derives `complEDS₂ _ _ _ 0 = 2`
independently; consumers are inside the forked file itself.

### Composition check (Phase 6)

Can `complEDS₂_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `exact complEDS₂_zero` (the mathlib lemma of the same qualified name).
  - Mathlib decls used: `complEDS₂_zero` (mathlib).
  - Result: succeeds trivially — it IS the mathlib lemma.

Conclusion: the question is degenerate. Mathlib does not merely have building
blocks; it has the **identical lemma**. This is NO-mathlib-has-it, not
NO-composable-from-mathlib.

---

## Verdict: `complEDS₂_zero`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): EDS 2-complement is Ward/division-polynomial theory; no fixed textbook "standard form" for the per-term cofactor — but moot.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical typeclass setting to mathlib.
- Mathlib search (Phase 5): found in mathlib as `complEDS₂_zero`, identical form, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:251`. `diff` against the project lemma = empty.
- Composition check (Phase 6): degenerate — mathlib has the identical lemma, not just blocks.

**Rationale:**

This project's `EllipticDivisibilitySequence.lean` is a fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author David
Kurniadi Angdinata, same Apache-2.0 header, same `preNormEDS`/`complEDS₂` API).
The `complEDS₂` 2-complement construction and all its initial-value lemmas were
upstreamed to mathlib. `complEDS₂_zero` is present in mathlib verbatim — same
`@[simp]` attribute, same statement `complEDS₂ b c d 0 = 2`, same proof
`simp [complEDS₂, one_add_one_eq_two]`. A line-level `diff` of the project's
definition+lemma (lines 848–850) against mathlib's (lines 250–252) produced no
differences. Both sit in `section PreNormEDS` with no enclosing namespace, so the
qualified name is `complEDS₂_zero` on both sides — a direct collision.

There is therefore no contribution to make: the lemma already lives in mathlib at
full generality (`CommRing R`) in exactly this form. The project carries it only
because it forks the file to extend the divisibility track (`complEDS'`/`complEDS`
and the Nagell–Lutz machinery built on top). The decl is mathlib's already.

**WHY not (refactor-actionable):**
Mathlib already has this lemma, identical. The project keeps it solely as part of
a verbatim fork of the mathlib EDS file; it adds nothing over the mathlib copy.

Existing mathlib decl:  `complEDS₂_zero`
Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:251` (def `complEDS₂` at :246)
Our form follows in ≤1 line (it is literally the same lemma):
```lean
example {R : Type*} [CommRing R] (b c d : R) : complEDS₂ b c d 0 = 2 := complEDS₂_zero
```
Call sites in our project (from Phase 6.0): 1 internal (line 1589), inside the forked file itself.

Refactor plan: this is fork-level dedup, not a per-call-site swap. Rather than
editing the one call site, the correct fix is to **drop the forked copy of the
already-upstreamed `preNormEDS`/`complEDS₂` block** (the entire mathlib-mirrored
portion of `section PreNormEDS`/`NormEDS`) and `import
Mathlib.NumberTheory.EllipticDivisibilitySequence`, keeping only the genuinely
new NagellLutz additions (`complEDS'`, `complEDS`, the divisibility lemmas, and
the `EllSequence`/`IsEllSequence` scaffolding if not yet upstreamed). After that
import, the internal use at line 1589 resolves to mathlib's `complEDS₂_zero`
unchanged. NB: this is a project-policy dedup decision (the fork may be
intentional to stay ahead of an in-flight upstream PR), so coordinate before
deleting — but the lemma itself is unambiguously already in mathlib.

Next action: delete the forked `complEDS₂_zero` (together with the rest of the
already-upstreamed `complEDS₂`/`preNormEDS` block) and import the mathlib file;
the one in-file call site then uses the mathlib lemma. If the fork must persist
for now, no mathlib PR is warranted for this decl — mathlib has it.

---

## Next step

Delete `complEDS₂_zero` from the project (as part of dropping the already-upstreamed
mathlib-mirror block) and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`;
the single internal call site (line 1589) then resolves to mathlib's identical
`complEDS₂_zero`. No mathlib PR — mathlib already has this lemma verbatim at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:251`.
