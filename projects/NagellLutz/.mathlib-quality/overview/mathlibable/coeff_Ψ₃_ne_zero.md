# /mathlibable report — `WeierstrassCurve.coeff_Ψ₃_ne_zero`

## TL;DR

**Verdict: `NO-mathlib-has-it`.** The declaration is a *verbatim copy* of an
existing mathlib lemma — same namespace, same signature, same proof, same
author, same file. The NagellLutz project deliberately forked
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` into
`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean`; its own module
docstring calls the sibling file "a project copy of mathlib's Basic file". This
is not a candidate for upstreaming; it is a fork that should eventually be
deleted in favour of `import`ing mathlib.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoning from source)
- decl `WeierstrassCurve.coeff_Ψ₃_ne_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:100`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … (a project copy of mathlib's Basic file)." — computes leading terms of division polynomials `preΨₙ`, `ΨSqₙ`, `Φₙ`.

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_Ψ₃_ne_zero` states: for a Weierstrass curve `W` over a
commutative ring `R`, if `3 ≠ 0` in `R`, then the coefficient of `X⁴` in the
third division polynomial `Ψ₃` is nonzero.

Mathematically: `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` (Silverman, *The
Arithmetic of Elliptic Curves*, Exercise 3.7), so its degree-4 coefficient is
the constant `3`; the hypothesis `(3 : R) ≠ 0` is exactly what makes that
leading coefficient nonzero. This is the step that pins down `natDegree Ψ₃ = 4`
in characteristic ≠ 3.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.

Hypotheses (Lean side):
- `(h : (3 : R) ≠ 0)` — three is nonzero in `R`.

Conclusion (math): the `X⁴`-coefficient of `Ψ₃` is nonzero.
Conclusion (Lean): `W.Ψ₃.coeff 4 ≠ 0`.

Proof body: `by rwa [coeff_Ψ₃]` — rewrites `W.Ψ₃.coeff 4` to `3` via the sibling
lemma `coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3`, reducing the goal to `(3 : R) ≠ 0`, which
is the hypothesis.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step helper lemma (`rwa` off a `coeff` computation); not a named
theorem, not a new structure, not a `## Main results` headline. It is glue feeding
`natDegree_Ψ₃`.

(Note: literature width is normally EXHAUSTIVE regardless. Here the literature
phase is moot — see Phase 3 — because the identical declaration already exists in
mathlib by the same author; the question "should mathlib have this?" is answered
by "mathlib *does* have this, verbatim".)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure`, so the one-line *definition*
check does not apply (n/a). For the record the proof is a single `rwa` line.

---

### Literature search (Phase 3)

The literature phase is **superseded** by the Phase 5 mathlib finding: the exact
declaration already lives in mathlib (identical name, type, and proof, by the
original author). When mathlib already contains the verbatim lemma, the
"standard-form / generality" literature question is not the deciding factor — the
verdict is fixed at `NO-mathlib-has-it` regardless of what the literature standard
is. For completeness, the mathematical content is entirely standard.

| # | Channel                     | Query / check                                              | Hit? | Standard form found                                  | Notes |
|---|-----------------------------|------------------------------------------------------------|------|------------------------------------------------------|-------|
| 1 | Primary source (Silverman)  | Division polynomial `ψ₃` explicit formula                  | yes  | `ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`               | Silverman, *AEC* (2009), Exercise 3.7; deg-4 coeff is `3` |
| 2 | mathlib source (authoritative) | `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` | yes  | `coeff_Ψ₃_ne_zero (h : (3:R) ≠ 0) : W.Ψ₃.coeff 4 ≠ 0` | **identical decl at line 104–105** — decides the verdict |
| 3 | Local references            | `projects/NagellLutz/.mathlib-quality/references/`        | n/a  | (directory absent)                                   | recorded n/a; not needed given #2 |
| 4 | WebSearch / nLab / Stacks / MathOverflow / arXiv | (broad literature sweep) | n/a  | not pursued                                          | n/a — moot: the verbatim lemma is already in mathlib (#2); no standard-form question can change a `NO-mathlib-has-it` |

### Literature summary (Phase 3)

Concept identified as: third division polynomial `ψ₃` of a Weierstrass curve and
its leading coefficient.
Sources agree on the standard form: yes — the explicit `ψ₃` and its leading
coefficient `3` are textbook (Silverman).
Disagreement with the literature: none. The point is not generality; it is that
mathlib already contains the identical formalised lemma.

---

### Generality analysis (Phase 4)

Not the deciding axis — mathlib already has the **identical** declaration, so
there is no "narrower than literature" gap to close by upstreaming (you cannot
upstream what is already upstream). For context within mathlib itself:

| # | Parameter / hypothesis | Current Lean form | Comment |
|---|------------------------|-------------------|---------|
| 1 | `[CommRing R]`         | commutative ring  | Already maximally general for a `coeff` statement; matches the mathlib decl exactly. |
| 2 | `(h : (3 : R) ≠ 0)`    | three nonzero     | Sharp: the coefficient *is* `3`, so `3 ≠ 0` is necessary and sufficient. Matches mathlib exactly. |

Note on mathlib-internal redundancy: mathlib also proves the general-`n` forms
`WeierstrassCurve.coeff_preΨ'_ne_zero` (Degree.lean:242) and
`WeierstrassCurve.coeff_preΨ_ne_zero` (Degree.lean:289), with `Ψ₃ = preΨ 3`.
mathlib nonetheless *keeps* the small-numeral specialisations `coeff_Ψ₂Sq_ne_zero`,
`coeff_Ψ₃_ne_zero`, `coeff_preΨ₄_ne_zero` as a deliberate convenience API. So the
specialisation is endorsed by mathlib — there is nothing to generalise and nothing
to add.

### Generality verdict (Phase 4b)

The current form is: identical to the mathlib form (maximally general for what it
states). Weakening opportunities: 0. Restatement: none.

### Modern-idiom check (Phase 4c)

No modernisation move: this is a finite, explicit polynomial-coefficient identity
over a commutative ring; there is no sequence-to-filter, set-to-substructure, or
typeclass-weakening reformulation available, and in any case mathlib already
ships this exact lemma. Modern idiom available: **no**.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a — direct source inspection was conclusive
[B] Loogle            n/a — direct source inspection was conclusive
[C] LeanSearch        n/a — direct source inspection was conclusive
[D] Grep mathlib src  `grep -n "coeff_Ψ₃\|_ne_zero" .lake/packages/mathlib/.../DivisionPolynomial/Degree.lean` → **HIT**
[E] Name pattern      `coeff_Ψ₃_ne_zero` → **HIT** (same qualified name, namespace `WeierstrassCurve`)

Searched for both the user's current form and any more-general form:
- current form: found verbatim — `WeierstrassCurve.coeff_Ψ₃_ne_zero` at
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:104`,
  with identical proof `by rwa [coeff_Ψ₃]`.
- general form: also present — `coeff_preΨ_ne_zero` (Degree.lean:289),
  `coeff_preΨ'_ne_zero` (Degree.lean:242).

Concluded: **found in mathlib as `WeierstrassCurve.coeff_Ψ₃_ne_zero`; identical
form** (byte-for-byte: same `Copyright (c) 2024 David Kurniadi Angdinata`, same
module docstring, same statement, same proof). The project file is a literal fork
of this mathlib file.

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.coeff_Ψ₃_ne_zero`

Internal use count: **1** (within NagellLutz, excluding the declaring file's own line).
External-to-file callers: 0 distinct files (the single use is in the same file).

| Caller file:line                                                    | Usage pattern                                                  |
|---------------------------------------------------------------------|----------------------------------------------------------------|
| projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:105    | `natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le <| W.coeff_Ψ₃_ne_zero h` |

Inline-derivation grep: none — the only consumer is `natDegree_Ψ₃`, mirroring
mathlib's own `natDegree_Ψ₃` (Degree.lean:108–109), which consumes the mathlib
lemma identically.

#### Composition

Composition is the trivial identity: the project lemma *is* the mathlib lemma.
`example : W.Ψ₃.coeff 4 ≠ 0 := W.coeff_Ψ₃_ne_zero h` where the RHS is now read
from mathlib. 0 chained calls (a re-export, not a composition).

Conclusion: the result requires *no* project code at all — it is already provided
by mathlib.

---

## Verdict: `WeierstrassCurve.coeff_Ψ₃_ne_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard `ψ₃` (Silverman); moot vs. the mathlib hit.
- Generality analysis (Phase 4): identical to mathlib's form; 0 weakenings; mathlib
  itself keeps this specialisation, so nothing to add or generalise.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.coeff_Ψ₃_ne_zero`; identical form** (Degree.lean:104).
- Composition check (Phase 6): n/a — the project decl is a verbatim re-export; 1 internal consumer, mirroring mathlib's.

**Rationale:**

The NagellLutz project explicitly forks
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` into
`LutzNagell/DivisionPolynomialDegree.lean` (its companion `DivisionPolynomial.lean`
is described in-file as "a project copy of mathlib's Basic file"). The declaration
`coeff_Ψ₃_ne_zero` is byte-for-byte identical to the mathlib lemma of the same
fully-qualified name — same `WeierstrassCurve` namespace, same signature
`(h : (3 : R) ≠ 0) : W.Ψ₃.coeff 4 ≠ 0`, same proof `by rwa [coeff_Ψ₃]`, same
2024 copyright header crediting the original mathlib author. There is no
upstreaming question: mathlib already has this, verbatim.

Within mathlib the lemma is a deliberately-kept small-numeral specialisation of
the general `coeff_preΨ_ne_zero` / `coeff_preΨ'_ne_zero` (since `Ψ₃ = preΨ 3`),
alongside its siblings `coeff_Ψ₂Sq_ne_zero` and `coeff_preΨ₄_ne_zero`. So even the
"is the specialisation worth it?" question is already answered affirmatively by
mathlib's own design. The only action item is on the project side: this fork
exists for the Nagell–Lutz development to control its own copy, but once that work
no longer needs a private fork, the file should `import` mathlib's `Degree` module
and these duplicated lemmas should be deleted.

**WHY not (refactor-actionable):**
Mathlib already has the exact lemma. The user's form does not merely *follow from*
the mathlib decl in ≤1 line — it *is* the mathlib decl (identical statement and
proof), so the replacement is a pure re-export.

Existing mathlib decl:        `WeierstrassCurve.coeff_Ψ₃_ne_zero`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:104`
Our form follows in 0 lines (it is the same lemma):
```lean
-- after `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (h : (3 : R) ≠ 0) :
    W.Ψ₃.coeff 4 ≠ 0 := W.coeff_Ψ₃_ne_zero h
```

Call sites in our project (from Phase 6.0): K = 1
(`DivisionPolynomialDegree.lean:105`, inside `natDegree_Ψ₃`).

Refactor plan (project-side, not a mathlib PR):
1. Replace the project's forked `DivisionPolynomial.lean` + `DivisionPolynomialDegree.lean`
   imports with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
   (and `.Basic`) wherever the Nagell–Lutz development consumes these division-polynomial
   degree facts.
2. Delete the duplicated `coeff_Ψ₃_ne_zero` (and the whole forked file, once the
   rest of its contents are confirmed to be present in mathlib — the grep shows the
   entire `Ψ₃`/`Ψ₂Sq`/`preΨ₄`/`ΨSq`/`Φ` API is mirrored).
3. The single internal call site at line 105 (`natDegree_Ψ₃`) is itself a fork of
   mathlib's `natDegree_Ψ₃` (Degree.lean:108) and is removed by the same deletion;
   no call-site rewrite is needed because the consumer disappears with the fork.

Caveat for the human: this is a *consolidation/dedup* action governed by the
project's fork policy, not a mechanical cleanup the fleet should auto-run — the
fork may be intentionally retained while the Nagell–Lutz frontier still needs to
modify these files. The mathlibable verdict itself is unconditional: **mathlib
already has it.**

---

## Next step

Project-side dedup (not a mathlib PR): once the Nagell–Lutz development no longer
needs a private fork of the division-polynomial degree file, delete
`coeff_Ψ₃_ne_zero` together with its forked file and `import`
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` instead. No
upstreaming is possible or needed — the identical lemma is already in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:104`.
