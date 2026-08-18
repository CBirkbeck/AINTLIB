# /mathlibable report — `WeierstrassCurve.Affine.CoordinateRing.mk_φ`

**TL;DR verdict: `NO-mathlib-has-it`.** This declaration is a *verbatim copy* of an
existing mathlib lemma. The project file states so in its own module docstring; the
lemma statement, proof, namespace, and fully-qualified name are byte-for-byte
identical to
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`.

---

### Baseline (Phase 0)
- lake build:               (not run — local build stale per task; assessment is by direct source inspection, which is dispositive here)
- decl `WeierstrassCurve.Affine.CoordinateRing.mk_φ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:405`
- kind:                      `lemma` (theorem)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

**Qualified-name verification.** The lemma is written `lemma Affine.CoordinateRing.mk_φ`
inside `namespace WeierstrassCurve` (opened at line 27) within `section φ` (a section,
not a namespace). Therefore the fully-qualified name is
**`WeierstrassCurve.Affine.CoordinateRing.mk_φ`** — exactly as the prompt parsed it.

---

### Statement (Phase 1)

`WeierstrassCurve.Affine.CoordinateRing.mk_φ` is a lemma stating that, for a Weierstrass
curve `W` over a commutative ring `R` and any integer `n`, the bivariate division
polynomial `φₙ ∈ R[X][Y]` and the univariate polynomial `Φₙ ∈ R[X]` become equal once
mapped into the affine coordinate ring `R[W] = R[X][Y] / ⟨W's defining polynomial⟩`:

> In `R[W]`, `mk(φₙ) = mk(C Φₙ)`.

Mathematically: `φₙ` (defined as `C X · ψₙ² − ψₙ₊₁ · ψₙ₋₁`) is the bivariate
"x-numerator" polynomial of the `n`-division/multiplication-by-`n` map on `W`, while
`Φₙ` is its univariate reduction (`X · ΨSqₙ − preΨₙ₊₁ · preΨₙ₋₁ · (1 or Ψ₂Sq)`).
The lemma says the bivariate construction equals the image of the univariate one
in the coordinate ring — i.e. the convenient univariate `Φₙ` correctly represents the
x-coordinate numerator of `[n]` modulo the curve relation.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — base commutative ring.
- `(W : WeierstrassCurve R)` — a Weierstrass curve.
- `(n : ℤ)` — the division index.

Hypotheses: none (pure identity in the coordinate ring).

Conclusion (math): `mk(φₙ) = mk(C Φₙ)` in `R[W]`.
Conclusion (Lean): `mk W (W.φ n) = mk W (C <| W.Φ n)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (a glue/congruence lemma in an existing mathlib API family;
not a named theorem, not a new structure, not a project main result).
Reason: it is one of the `CoordinateRing.mk_*` congruences (`mk_ψ₂_sq`, `mk_Ψ_sq`,
`mk_ψ`, `mk_φ`) that bridge the bivariate and univariate division-polynomial APIs.

(Literature width was still considered EXHAUSTIVE; but see Phase 5 — the decisive
fact is that this exact lemma already exists in mathlib, which short-circuits the
generality/literature questions for the *inclusion* decision.)

### One-line check (Phase 2b)

Kind is `lemma`/`theorem` → one-line check **n/a**. (The proof is a 3-line `simp_rw`,
but the body length of a *theorem* is irrelevant to the mathlib-inclusion signal;
2b applies only to `def`/`abbrev`/`structure`.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

This is a Lean-internal *coordinate-ring congruence* in mathlib's own division-polynomial
formalisation (the `Φₙ`/`φₙ`/`ΨSqₙ` machinery is a mathlib design, due to D. Angdinata,
chosen specifically to avoid ring division by working with univariate polynomials and
mapping into `R[W]`). The "literature-standard form" question is therefore subordinate
to the fact that the construction itself *originates in mathlib*. The relevant classical
background is the theory of elliptic division polynomials / division-polynomial identities
(Ψₙ, Φₙ, ωₙ) as in the references below.

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib WeierstrassCurve Affine CoordinateRing mk_φ division polynomial Φ Angdinata"   | yes  | the mathlib lemma itself | Returns the official mathlib4 docs page for `DivisionPolynomial.Basic`, which hosts `mk_Ψ_sq`/`mk_ψ`/`mk_φ` and the `Φ`/`φ` defs. Decisive. |
|  2 | WebSearch (general form / concept)| division polynomials elliptic curve φ_n Φ_n x-coordinate multiplication-by-n           | yes  | `x([n]P) = φₙ(x)/ψₙ(x)²` | Silverman AEC Ex. 3.7; the bivariate `φₙ`↔univariate `Φₙ` reduction is the mathlib-specific engineering of this classical fact. |
|  3 | WebSearch (named-after / aliases)| division polynomial "φ_n" psi_n omega_n elliptic divisibility sequence identities       | yes  | classical Ψ/Φ/Ω identities | Standard EDS theory (Ward 1948; Silverman). The coordinate-ring `mk` framing is mathlib's. |
|  4 | ChatGPT MCP                      | (MCP down per task environment — fallback to WebSearch #1–3 + direct mathlib source read) | n/a  | —                   | Compensated by reading the actual mathlib source (Phase 5), which is *stronger* evidence than any second opinion for a "does mathlib have it" question. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial" / "mk_φ"                   | n/a  | —                   | NagellLutz references dir not populated with a source paper covering this Lean-internal lemma; recorded n/a. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                 | n/a  | —                   | nLab has no page on this specific coordinate-ring congruence; the concept is classical-arithmetic, covered by #2/#3. |
|  7 | nCatLab (categorical)            | —                                                                                       | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | division polynomial / Weierstrass coordinate ring                                       | n/a  | —                   | Stacks does not cover concrete elliptic-curve division polynomials at this level. |
|  9 | MathOverflow / MSE              | division polynomial φ_n Φ_n relation x-coordinate                                       | yes  | classical            | Confirms `φₙ`/`ψₙ`/`Φₙ` are standard; nothing about mathlib's `mk` framing (which is the actual decl). |
| 10 | recent arXiv (≤5y)              | elliptic divisibility sequence division polynomial formalisation Lean                    | yes  | Angdinata's mathlib work | The mathlib EC formalisation (the source of this very lemma) is the relevant artifact. |

### Literature summary (Phase 3)

Concept identified as: the **coordinate-ring congruence `mk φₙ = mk (C Φₙ)`** in
mathlib's elliptic-curve division-polynomial API (bivariate `φₙ` ↔ univariate `Φₙ`).
Underlying classical content: the x-coordinate numerator of multiplication-by-`n`,
`x([n]P) = φₙ(x)/ψₙ(x)²` (Silverman, *Arithmetic of Elliptic Curves*; Ward's EDS theory).
Sources agree on the standard form: yes — and, crucially, the *Lean* form is itself a
mathlib design that already exists upstream.
Most general standard form: mathlib already states it at maximal generality — over an
arbitrary `CommRing R` and all `n : ℤ` (see Phase 4).
Disagreement with the literature: none.

---

### Generality analysis — `WeierstrassCurve.Affine.CoordinateRing.mk_φ` (Phase 4)

Literature/mathlib-standard form: identity over arbitrary `CommRing R`, all `n : ℤ`.

| # | Parameter / hypothesis | Current Lean form        | Standard form          | Weaker form exists? | Reason |
|---|------------------------|--------------------------|------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | arbitrary commutative ring | arbitrary commutative ring | NO                | `WeierstrassCurve` and its coordinate ring `mk` are defined over `CommRing`; this is already the base-level typeclass. Can't meaningfully weaken (the curve algebra needs a comm ring). |
| 2 | `(n : ℤ)`              | all integers             | all integers           | NO                | Full integer range already covered (handles even/odd and negatives via `φ_neg`, `Ψ₂Sq` parity term). |
| 3 | no hypotheses          | identity, unconditional  | unconditional          | NO                | Nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's, over `CommRing R`,
all `n : ℤ`). Weakening opportunities: 0. This is unsurprising — the form *is* the
mathlib form, copied verbatim.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1 | bundled-hyp → typeclass? | no | No bundled "let X be a foo" preamble. |
| 2 | sequences/metric → filters/topology? | no | Pure algebraic identity; no limits. |
| 3 | construction → universal property? | no | A congruence lemma about an existing construction. |
| 4 | set+closure → bundled substructure? | no | n/a. |
| 5 | vector-space/field → module/(semi)ring? | no | Already at `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index → general additive/monoid? | no | `n : ℤ` is the correct, maximal index here. |

Modern idiom available: **no** — the statement already *is* the contemporary mathlib
idiom (it was written for mathlib). One-line reason: this lemma is the established
mathlib formulation; there is nothing to modernise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths
introduced).

---

### Mathlib search-status: `WeierstrassCurve.Affine.CoordinateRing.mk_φ` (Phase 5)

[A] Lean-Finder       (index per task: same mathlib)        — superseded by direct source hit below
[B] Loogle            `mk _ (?W.φ _) = mk _ (C (?W.Φ _))`    — superseded by direct source hit below
[C] LeanSearch        "coordinate ring phi equals Phi Weierstrass division polynomial" — points to mathlib `DivisionPolynomial.Basic`
[D] **Grep mathlib src** `grep -rn "mk_φ" .lake/packages/mathlib/Mathlib/` → **HIT**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`
[E] Name pattern      `Affine.CoordinateRing.mk_φ`           — **HIT**, same file:line

Searched for both the user's form and the standard form — they are *the same form*.

**Direct byte-diff (decisive evidence):**
```
$ diff <(sed -n '482,485p' .lake/.../DivisionPolynomial/Basic.lean) \
       <(sed -n '405,408p' projects/NagellLutz/LutzNagell/DivisionPolynomial.lean)
  → IDENTICAL (empty diff)
```
The lemma signature **and** its 3-line `simp_rw [...]` proof match the mathlib source
exactly. The enclosing namespace/section structure (`namespace WeierstrassCurve` →
`section φ` → `open WeierstrassCurve (Ψ Φ φ)`) is also identical, so the qualified name
`WeierstrassCurve.Affine.CoordinateRing.mk_φ` is shared. The only difference anywhere
nearby is a cosmetic paren in the unrelated `φ` *def* (`(W.ψ n)` vs `W.ψ n`).

Live-upstream confirmation: the official mathlib4 docs page for
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` hosts this exact
`CoordinateRing.mk_*` family (`mk_ψ₂_sq`, `mk_Ψ_sq`, `mk_ψ`, `mk_φ`).

Concluded: **found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_φ`; identical form** (verbatim copy).

---

### Composition check (+ call sites) (Phase 6)

#### Call sites — `WeierstrassCurve.Affine.CoordinateRing.mk_φ`

Internal use count (project tree, excluding the declaring file): **≥ 9** references across
HasseWeil and NagellLutz. Notable:

| Caller file:line | Usage pattern |
|------------------|---------------|
| `HasseWeil/MulByIntPullback.lean:123` | `exact Affine.CoordinateRing.mk_φ (W := W.toAffine) n` — and the docstring at :119 literally reads **"This follows from `mk_φ` in mathlib."** |
| `HasseWeil/OmegaPullbackCoeff.lean:193` | `exact Affine.CoordinateRing.mk_φ (W := W.toAffine) n` |
| `HasseWeil/EC/GenericPointZsmul.lean:636` | `..., Affine.CoordinateRing.mk_φ]` (rewrite set) |
| `HasseWeil/EC/MulByIntUnramified.lean:122` | `evalEval_eq_of_mk_eq W h_eq (Affine.CoordinateRing.mk_φ (W := W.toAffine) n)` |
| `HasseWeil/EC/IsogenyAG/CovarianceDischarge.lean:491` | `WeierstrassCurve.Affine.CoordinateRing.mk_φ (W := W.toAffine) n` |
| `HasseWeil/Auxiliary/DivisionPolynomial.lean:739` | `evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ (W := W) n)` |
| `NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:56` | `evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ W n)` |

Inline re-derivation grep: none — every consumer calls the lemma by name (and several
resolve `WeierstrassCurve.Affine.CoordinateRing.mk_φ`, which is the *same qualified name*
as mathlib's; they would bind to mathlib's copy unaffected if the local copy were deleted,
since `LutzNagell.DivisionPolynomial` is itself a re-export of the mathlib API).

#### Composition check

Not applicable as a "build it from primitives" exercise — the exact lemma exists in
mathlib, so the correct action is *reuse*, not composition. (For completeness: the proof
itself is a one-shot `simp_rw` over the sibling congruences `mk_ψ`, `mk_Ψ_sq`, `mk_ψ₂_sq`
— but those siblings are *also* mathlib copies in this same forked file.)

Conclusion: **NOT-COMPOSABLE-by-us / N-A — mathlib already has the lemma.**

---

## Verdict: `WeierstrassCurve.Affine.CoordinateRing.mk_φ`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the construction (`φₙ`/`Φₙ` + coordinate-ring `mk`) is a
  mathlib design (D. Angdinata); the classical content is Silverman's `x([n]) = φₙ/ψₙ²`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — and identical to mathlib's form.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_φ`; identical form** (`Basic.lean:482`, verbatim incl. proof).
- Composition check (Phase 6): n/a — reuse mathlib directly.

**Rationale.**
The project's `LutzNagell/DivisionPolynomial.lean` is, by its own module docstring, "a
copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`". The fork
exists for one mechanical reason — it imports the project's local
`EllipticDivisibilitySequence` (to dodge a `normEDS`/`complEDS` name clash) — and has
*nothing* to do with `mk_φ` specifically. A direct `diff` of the lemma block against the
pinned mathlib source returns empty: the signature, the 3-line `simp_rw` proof, the
enclosing `namespace WeierstrassCurve` / `section φ`, and hence the fully-qualified name
`WeierstrassCurve.Affine.CoordinateRing.mk_φ` are all identical to mathlib. The live
upstream mathlib4 docs confirm the lemma (and its whole `CoordinateRing.mk_*` family) is
in mathlib. There is zero new mathematical content here; this is a duplicate, not a
candidate for upstreaming.

**WHY not (refactor-actionable).**
Mathlib already has it: **`WeierstrassCurve.Affine.CoordinateRing.mk_φ`**, at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`. Our copy
follows in 0 lines because it *is* the same declaration (same name, same proof). The
consumers already treat it as mathlib's — `HasseWeil/MulByIntPullback.lean:119` annotates
the call with "This follows from `mk_φ` in mathlib", and several sites invoke the
fully-qualified `WeierstrassCurve.Affine.CoordinateRing.mk_φ`.

Existing mathlib decl:        `WeierstrassCurve.Affine.CoordinateRing.mk_φ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`
Our form follows in ≤1 line:
```lean
example (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) :=
  WeierstrassCurve.Affine.CoordinateRing.mk_φ n   -- the mathlib lemma, verbatim
```
Call sites in our project (Phase 6.0):  ≥ 9 (across HasseWeil + NagellLutz).

**Refactor plan / caveat.**
Do **not** simply delete this lemma in isolation and re-point call sites at mathlib — the
whole `LutzNagell/DivisionPolynomial.lean` file is a *deliberate, coordinated fork* of the
mathlib `Basic` module, forked only to break the `normEDS`/`complEDS` import clash from the
local `EllipticDivisibilitySequence`. `mk_φ` is just one line of that fork. The correct
disposition is a *file-level* decision, not a per-lemma one:
- **Preferred:** retire the entire local fork once the underlying `EllipticDivisibilitySequence`
  name clash is resolved (e.g. by namespacing the local EDS or by upstreaming/aligning it),
  then have the project `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
  directly. All ≥9 call sites already use the mathlib-qualified name and would continue to
  work unchanged.
- **If the fork must stay** (clash unresolved): keep `mk_φ` as-is. It is intentional
  duplication serving the fork's purpose, **not** a mathlib-contribution candidate. Flag it
  as "duplicate-of-mathlib (forked copy)" in the overview inventory rather than as cleanup
  debt to be inlined lemma-by-lemma.

In **no** scenario is this a YES (add/generalise) — mathlib has the identical lemma.

Next action: treat at the file level — plan removal of the `DivisionPolynomial.lean` fork
in favour of importing mathlib's `DivisionPolynomial.Basic` once the local
`EllipticDivisibilitySequence` name clash is eliminated. No mathlib PR; this decl is
already upstream.

---

## Next step

Treat at the file level: this lemma — and the whole `LutzNagell/DivisionPolynomial.lean`
module — is a verbatim fork of mathlib's `DivisionPolynomial.Basic`. Plan to drop the fork
and import mathlib directly once the `normEDS`/`complEDS` clash from the local
`EllipticDivisibilitySequence` is resolved; the ≥9 existing call sites already use the
mathlib-qualified name `WeierstrassCurve.Affine.CoordinateRing.mk_φ` and need no change.
Do not open a mathlib PR — the identical lemma already lives at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`.

Sources:
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
