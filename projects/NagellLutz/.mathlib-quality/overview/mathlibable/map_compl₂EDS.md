# /mathlibable report — `map_compl₂EDS`

**Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS)
**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1137`
**Date:** 2026-06-21 (supersedes the 2026-06-18 Step-8 note; same verdict, fuller evidence)

## Verdict: **NO-mathlib-has-it**

Mathlib already contains this lemma verbatim as `map_complEDS₂`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`). NagellLutz
**forks** that David-Angdinata mathlib file and renames the 2-complement
definition `complEDS₂ → compl₂EDS` (subscript moved); `map_compl₂EDS` is the
renamed copy of `map_complEDS₂`. Identical statement, identical one-line proof,
identical underlying definitions (verified byte-for-byte).

---

### Baseline (Phase 0)
- lake build:               not run — pin `09b373db6e24`, build stale per task; reasoned from source (both decls read directly off disk, fork + `.lake/packages/mathlib`)
- decl `map_compl₂EDS`:     ✓ resolved at `…/EllipticDivisibilitySequence.lean:1137`
- kind:                     lemma
- has sorry:                no
- qualified name:           **`map_compl₂EDS`** (root namespace — see note)
- module docstring summary: Elliptic divisibility sequences; normalised EDS from initial terms; division-polynomial link. The file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (identical copyright header + module docstring).

**Namespace note.** No file-level `namespace`. `EllSequence` opens at 90, closes
at 597; `Complement`/`Map` sections at 1010/1116 are top-level. Sibling lemmas
that *do* live in a namespace are written explicitly (`EllSequence.map_compl'`,
`EllSequence.map_compl`). So the fully-qualified name is the bare
**`map_compl₂EDS`** and the def is the bare `compl₂EDS`. Parsed name confirmed.

---

### Statement (Phase 1)

```lean
lemma map_compl₂EDS (n : ℤ) : f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n := by
  simp only [compl₂EDS, map_sub, map_mul, map_pow, map_preNormEDS, apply_ite f, map_one]
```

Ambient variables: `{R S} [CommRing R] [CommRing S]`, `{F} [FunLike F R S]
[RingHomClass F R S] (f : F)`, `{b c d : R}`, `(n : ℤ)`.

`map_compl₂EDS` states: a ring homomorphism `f` **commutes with the
2-complement** of a normalised EDS — `f (compl₂EDS b c d n) = compl₂EDS (f b)
(f c) (f d) n`. The 2-complement `compl₂EDS b c d m` (def, line 1031) is the
witness of `normEDS b c d m ∣ normEDS b c d (2*m)` (it satisfies `W(m)·Wᶜ₂(m) =
W(2m)`), built as the fixed expression
`(p (m-1)^2 * p (m+2) − p (m-2) * p (m+1)^2) * if Even m then 1 else b` with
`p = preNormEDS (b^4) c d`.

Conclusion (math): the polynomial expression defining `compl₂EDS` is preserved
by `f` applied termwise (naturality / functoriality in the base ring).
Conclusion (Lean): `f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a `map_*` naturality glue lemma; routine functoriality of a
polynomial construction over the coefficient ring. Not a named theorem, not a new
structure, not a `## Main statements` entry. (Literature width run EXHAUSTIVE
regardless, per protocol.)

### One-line check (Phase 2b)
n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (The proof body is
itself a single `simp only` line, reinforcing SMALL/glue.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                            | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | EDS normalised ring homomorphism functoriality division polynomial base change                    | yes  | mathlib `complEDS₂` is the #1 result | the concept's canonical home is the mathlib doc page itself |
|  2 | WebSearch (mathlib name)         | Mathlib complEDS₂ map_complEDS₂ EDS ring hom                                                       | yes  | engine reproduced the mathlib `complEDS₂` def verbatim | confirms mathlib owns the concept + the exact def |
|  3 | WebSearch (named-after / Ward)   | Ward EDS division polynomial commutes with ring homomorphism universal                             | partial | Ward classification; division polys are ℤ-coeff | naturality treated as routine; never a *named* result |
|  4 | ChatGPT MCP                      | Is "compl₂EDS commutes with ring homs" a named result or routine polynomial functoriality?         | n/a  | — | MCP/Codex DOWN (task-noted as down); reasoned from literature + source |
|  5 | Local references                 | `.mathlib-quality/references/` for EDS / complement / naturality                                   | n/a  | — | no references dir for this track |
|  6 | nLab                             | elliptic divisibility sequence                                                                     | n/a  | — | nLab has no EDS / division-poly naturality entry; not a categorical concept |
|  7 | nCatLab (categorical)            | —                                                                                                  | n/a  | — | not a categorical concept |
|  8 | Stacks Project (alg geom)        | division polynomial / EDS naturality                                                               | n/a  | — | Stacks has no division-poly / EDS naturality statement |
|  9 | MathOverflow / MSE               | EDS division polynomial base change ring homomorphism                                              | partial | base-change of EDS under ring/field change | only the routine "polynomials are preserved" framing |
| 10 | recent arXiv (≤5 yrs)            | Stange, "Division polynomials for arbitrary isogenies" (2025); p-adic division-poly papers          | partial | division polys are ℤ-coeff ⇒ specialise under any ring map | universally treated as a triviality; never named |

The mathematics of EDS division-polynomial complements is M. Ward, *Memoir on
Elliptic Divisibility Sequences* (the file's own reference) and Silverman, *AEC*
III (division polynomials). Neither states a `map_*` / base-change lemma — that
notion only arises once the sequence is formalised as a function of the ring `R`.

### Literature summary (Phase 3)

Concept identified as: the **2-complement of a normalised EDS** = mathlib's
`complEDS₂` (project rename `compl₂EDS`). The lemma is its **naturality in the
base ring**.
Sources agree on the standard form: yes — `complEDS₂` is mathlib's own concept;
the top hit on every query is the mathlib doc page.
Most general standard form: for any ring hom `f`, the value commutes with `f`,
because `compl₂EDS` is a fixed expression in `preNormEDS`/`+`/`−`/`*`/`^`/`ite`
with integer coefficients, all preserved termwise by ring homs.
Generality dimensions where the literature varies: none of substance. The
statement has **no independent mathematical content** and **no standard name**;
it is the routine "evaluation of an ℤ-coefficient polynomial expression is
preserved by ring homomorphisms." Decisive evidence is the mathlib comparison.
Disagreement with the literature: none.

---

### Generality analysis — `map_compl₂EDS`

Literature/mathlib-standard form: `f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n`.

| # | Parameter / hypothesis                  | Current Lean form                  | Standard form        | Weaker form exists? | Reason |
|---|-----------------------------------------|------------------------------------|----------------------|---------------------|--------|
| 1 | `[FunLike F R S] [RingHomClass F R S]`  | bundled-class ring hom              | ring homomorphism    | NO (already maximal) | needs `map_mul`/`map_sub`/`map_pow`/`map_one`; `RingHomClass` is the minimal carrier. NB mathlib's `map_complEDS₂` uses the *concrete* `(f : R →+* S)` for the whole `map_*` family — the project's class form is *negligibly* more general and mathlib deliberately chose `R →+* S`. |
| 2 | `[CommRing R] [CommRing S]`             | commutative rings                  | commutative rings    | NO                  | `compl₂EDS`/`normEDS` defined only over `CommRing` |
| 3 | `(n : ℤ)`                               | integer index                      | integer index        | NO                  | EDS are intrinsically ℤ-indexed |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (equal to mathlib's `map_complEDS₂`,
modulo the rename and the `RingHomClass`-vs-`RingHom` cosmetic delta that mathlib
intentionally takes the *other* way). Weakening opportunities: 0. Cost: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                          | Applies? | Notes |
|----|---------------------------------------------------|----------|-------|
|  1 | "let X be a foo" → typeclass?                     | no       | already `[RingHomClass F R S]` |
|  2 | sequences/metric → filters/topology?              | no       | purely algebraic identity |
|  3 | construct → universal-property class?             | no       | a naturality equation; nothing to characterise |
|  4 | set+closure → bundled substructure?               | no       | no substructure |
|  5 | vector-space/field-specific → weaken typeclass?   | no       | already at `CommRing` |
|  6 | 1-categorical → higher-categorical?               | no       | a single equation in `S` |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid?          | no       | ℤ is intrinsic to EDS |

Modern idiom available: **no** — the lemma is already in mathlib's exact
contemporary form (it IS that form). No modernisation move.

---

### Diamond / defeq risk — `map_compl₂EDS`

n/a — declaration kind is `lemma` (introduces no definitional equality and no
typeclass-search path).

---

### Mathlib search-status: `map_compl₂EDS`

[A] Lean-Finder       n/a (index stale/offline) — substituted by direct mathlib-source read
[B] Loogle            pattern `?f (compl₂EDS ..) = compl₂EDS (?f _) ..` — n/a: `compl₂EDS` is the project's renamed symbol, not in the index; searched the equivalent `complEDS₂` form by source-grep → HIT
[C] LeanSearch        "2-complement of normalised EDS commutes with ring hom" — n/a (offline); concept resolved via WebSearch #1/#2 → mathlib doc page
[D] Grep mathlib src  `grep -nE "map_|complEDS₂|map_complEDS₂"` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **HIT: `map_complEDS₂` at line 526**, inside a `section Map` (505) that mirrors the project's: `map_preNormEDS'`(510), `map_preNormEDS`(522), `map_complEDS₂`(526), `map_normEDS`(530), `map_complEDS'`(534), `map_complEDS`(544)
[E] Name pattern      grep `complEDS₂` across `Mathlib/` → `def complEDS₂`(246) + `map_complEDS₂`(526); the project spelling `compl₂EDS` appears **nowhere** in `Mathlib/`

Searched for both:
  - the user's current form (`compl₂EDS` / `map_compl₂EDS`) — only in the project fork
  - the mathlib-standard form (`complEDS₂` / `map_complEDS₂`) — **present in mathlib**

Concluded: **found in mathlib as `map_complEDS₂`; identical form.** Underlying
defs are byte-identical:

  mathlib `complEDS₂` (246):  (preNormEDS (b^4) c d (k-1)^2 * preNormEDS (b^4) c d (k+2)
                               − preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1)^2) * if Even k then 1 else b
  project `compl₂EDS` (1031): letI p := preNormEDS (b^4) c d;
                               (p (m-1)^2 * p (m+2) − p (m-2) * p (m+1)^2) * if Even m then 1 else b

— same expression (`letI p` is a local abbreviation). And the upstream
`preNormEDS` (project 176-ish / mathlib 176) and `normEDS` (project 890 / mathlib
289) defs are byte-identical between fork and mathlib (verified:
`n.sign * preNormEDS' b c d n.natAbs` and
`preNormEDS (b^4) c d n * if Even n then b else 1` respectively). Hence
`map_compl₂EDS` ≡ `map_complEDS₂`. Mathlib's lemma is also `@[simp]` and is
consumed inside its own file at line 540 (`map_complEDS'` induction), exactly as
the project's is at line 1160.

---

### Call sites — `map_compl₂EDS`

Internal use count: **7** (within NagellLutz, excluding the declaring line 1137).
External-to-file callers: 2 files (`ZSMul.lean`, `DivisionPolynomialOmega.lean`).

| Caller file:line                              | Usage pattern (one-line excerpt)                                              |
|-----------------------------------------------|-------------------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:123                     | `rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]`       |
| LutzNagell/DivisionPolynomialOmega.lean:112   | `simp_rw [ω, …, map_compl₂EDSAux, …]` (sibling `Aux` lemma — same naturality batch) |
| EllipticDivisibilitySequence.lean:1160        | `· ext x; simp only [Function.comp, map_compl₂EDS]` (inside `map_complEDS`)    |
| EllipticDivisibilitySequence.lean:1194        | `simp_rw [map_compl₂EDS, aeval_X]` (inside `compl₂EDS_eq_aeval`)               |
| EllipticDivisibilitySequence.lean:1425        | `simp only […, map_compl₂EDS, map_normEDS, …]` (inside `redInvarNum` map lemma) |

Inline-derivation grep (re-derived elsewhere without `map_compl₂EDS`?): (none) —
every consumer routes through the lemma. K ≥ 3 with no inline re-derivation ⇒
real, used API. This does **not** argue for a *new* mathlib addition; it argues
the fork should be reconciled onto the mathlib original `map_complEDS₂`.

---

### Composition check (Phase 6)

Can `map_compl₂EDS` be derived from mathlib in ≤3 chained calls?

Attempt 1: `map_complEDS₂ f b c d n` (mathlib), once project `compl₂EDS` is
identified with mathlib `complEDS₂`.
  - Mathlib decls used: `map_complEDS₂`.
  - Result: succeeds — it is literally the same statement.

Conclusion: nothing to compose — mathlib has the lemma outright. Recorded under
NO-mathlib-has-it, not NO-composable. (Even absent the named lemma it is a
one-line `simp [complEDS₂, apply_ite f]`, i.e. trivially composable — but the
operative fact is mathlib already states and `@[simp]`-tags it.)

---

## Verdict: `map_compl₂EDS`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature (Phase 3): concept = mathlib's `complEDS₂`; the naturality statement
  is routine polynomial functoriality, unnamed in Ward/Silverman/arXiv; top hit on
  every web query is the mathlib doc page itself.
- Generality (Phase 4): MAXIMALLY GENERAL; identical to mathlib's form; no
  modern-idiom move (it already IS the mathlib idiom).
- Mathlib search (Phase 5): found in mathlib as `map_complEDS₂`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`); identical form;
  underlying `complEDS₂`/`preNormEDS`/`normEDS` defs byte-identical to the fork.
- Composition (Phase 6): nothing to compose — mathlib has the lemma outright.

**Rationale:**

NagellLutz vendors a fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (same Angdinata copyright
header, same module docstring, same `M Ward` reference), renaming the
2-complement `complEDS₂ → compl₂EDS` and re-deriving its whole `section Map`.
`map_compl₂EDS` is the renamed copy of mathlib's `map_complEDS₂`: same statement,
same one-line `simp` proof, and the underlying `compl₂EDS`/`preNormEDS`/`normEDS`
definitions are byte-for-byte identical to mathlib's
`complEDS₂`/`preNormEDS`/`normEDS`. This is not a candidate for a mathlib
*addition* — it is a consolidation duplicate, exactly the duplicated-track drift
the project context flagged. The only differences are cosmetic: the `compl₂`-vs-
`complEDS₂` subscript rename, and a `RingHomClass`-vs-`RingHom` widening that
mathlib deliberately declines for this entire `map_*` family. The healthy 7
internal call sites confirm genuine API — which strengthens "use the mathlib
original," not "add a copy."

**WHY not (refactor-actionable):**
Mathlib already has it as `map_complEDS₂`. The project's `compl₂EDS` IS mathlib's
`complEDS₂` (identical RHS). Once the def is reconciled, `map_compl₂EDS` follows
in 0 lines — it is the same lemma.

Existing mathlib decl:        `map_complEDS₂`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`
Underlying def equivalence:   project `compl₂EDS` (line 1031) ≡ mathlib `complEDS₂` (line 246)
Our form follows in ≤1 line (once defs are unified):
```lean
example (f : R →+* S) (b c d : R) (n : ℤ) :
    f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n :=
  map_complEDS₂ f b c d n  -- mathlib
```
Call sites in our project (from Phase 6.0): **7** (`ZSMul.lean`,
`DivisionPolynomialOmega.lean`, and 5 within `EllipticDivisibilitySequence.lean`).

Refactor plan (consolidation — this decl cannot be deleted in isolation because
the fork renamed the whole track):
1. Rename `compl₂EDS → complEDS₂` (and sibling renames `compl' → complEDS'`, the
   `complEDS` signature) across `projects/NagellLutz/` so the fork's symbols match
   upstream.
2. Replace the forked `section Map` block (≈1116–1201: `map_preNormEDS'`,
   `map_preNormEDS`, `map_normEDS`, **`map_compl₂EDS`**, `map_compl'`,
   `map_complEDS`) with `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence` and use the upstream
   `map_complEDS₂` etc.
3. At each of the 7 call sites, replace `map_compl₂EDS` with `map_complEDS₂`
   (argument order identical: `f`/typeclass + `b c d` implicit + `n`).
   NOTE: `map_compl₂EDSAux` (line 1421, used at `DivisionPolynomialOmega.lean:112`)
   is a **separate** decl — mathlib has **no** `complEDS₂Aux` analog (grep empty),
   so it is NOT covered by this verdict and must be assessed on its own.

Next action: do NOT delete `map_compl₂EDS` standalone; fold it into the broader
NagellLutz ↔ mathlib EDS reconciliation (rename `compl₂EDS→complEDS₂`, drop the
forked `section Map`, retarget the 7 call sites onto mathlib's `map_complEDS₂`).
Assess the sibling `map_compl₂EDSAux` separately (mathlib has no `complEDS₂Aux`).

---

## Next step

Fold this lemma into the project's EDS-fork reconciliation: rename
`compl₂EDS → complEDS₂` project-wide, delete the duplicated `section Map`
(including `map_compl₂EDS`), `import
Mathlib.NumberTheory.EllipticDivisibilitySequence`, and point the 7 call sites at
mathlib's `map_complEDS₂`.
