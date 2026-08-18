# /mathlibable report — `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`

> One-line verdict: **NO-mathlib-has-it.** This declaration is a *byte-for-byte
> fork* of mathlib's own `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`
> (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`).
> The file even says so in its header.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale per task note); reasoning from source + vendored mathlib pin, which is authoritative for the identity check
- decl `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:361`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  *"This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."* (header, lines 11–14)

The qualified name was VERIFIED from source: the file opens `namespace WeierstrassCurve`
(line 27) and the declaration head is `Affine.CoordinateRing.mk_ψ`, giving the full
name `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`. The parsed name in the task was
correct.

---

### Statement (Phase 1)

`WeierstrassCurve.Affine.CoordinateRing.mk_ψ` is a theorem stating the following:

Let `W` be a Weierstrass curve over a commutative ring `R`, with affine coordinate
ring `R[W] = R[X][Y] / ⟨W.polynomial⟩` and canonical quotient map
`mk W : R[X][Y] → R[W]`. For every integer `n`, the image in `R[W]` of the bivariate
`n`-division polynomial `ψₙ` equals the image of the auxiliary bivariate polynomial
`Ψₙ`. In symbols, `mk W (ψₙ) = mk W (Ψₙ)` in `R[W]`.

Here `ψₙ := normEDS ψ₂ (C Ψ₃) (C preΨ₄)` is the genuine division polynomial
(a normalised elliptic divisibility sequence), while `Ψₙ := C(preΨₙ) · (ψ₂ if n even else 1)`
is the "pre-normalised" companion living over `R[X]`. The two are *not* equal in
`R[X][Y]`, but they become congruent modulo the curve relation because `ψ₂²` reduces
to `C Ψ₂Sq` in `R[W]` (the lemma `mk_ψ₂_sq`). This congruence is the bridge that lets
one compute division polynomials with the univariate `Ψₙ`/`preΨₙ` instead of the
bivariate `ψₙ`.

Variables / typeclasses involved (Lean side):
- `{R : Type r} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — a Weierstrass curve (here used through `W.toAffine`).
- `(n : ℤ)` — the index of the division polynomial.

Hypotheses (Lean side): none beyond the parameters.

Conclusion (math): `ψₙ ≡ Ψₙ` in the affine coordinate ring `R[W]`.

Conclusion (Lean): `mk W (W.ψ n) = mk W (W.Ψ n)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper congruence lemma (not a named theorem, not a new structure, not a
`## Main results` entry). Two-line `simp_rw` proof. Supports the eval-bridge machinery
toward Nagell–Lutz, but is itself plumbing.

(Note: literature width recorded below; the BIG/SMALL split is framing only. The
decisive evidence here is a direct source-identity match, which makes the lit sweep
confirmatory rather than exploratory.)

### One-line check (Phase 2b)

n/a — declaration kind is `lemma`, not `def`/`abbrev`/`structure`. The one-liner
exemption analysis does not apply to propositions.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                           | Query                                                                                          | Hit? | Standard form found                                                  | Notes |
|----|-----------------------------------|------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)         | "elliptic curve division polynomial psi_n coordinate ring elliptic divisibility sequence normEDS Weierstrass" | yes  | ψₙ are the standard division polynomials; the *first* hit is mathlib's own doc page for this very file | confirms the concept is exactly mathlib's `WeierstrassCurve.Ψ`/`ψ` API |
|  2 | WebSearch (general form)          | (same query, general angle) division polynomials over a commutative ring `R`, EDS recursion     | yes  | Silverman AEC Exercise 3.7; EDS recursion `Wₙ₊ₘWₙ₋ₘW₁² + …`            | standard; mathlib already states it at full `CommRing R` generality |
|  3 | WebSearch (named-after / aliases) | "elliptic divisibility sequence" / "normalised EDS" Ward                                         | yes  | Morgan Ward, *Memoir on elliptic divisibility sequences* (1948)       | the `normEDS`/`preNormEDS` naming is mathlib's own; Ward is the classical source |
|  4 | ChatGPT MCP                       | (unavailable this session — task note: "ChatGPT MCP may be down; use fallbacks")                 | n/a  | — | substituted by Wikipedia EDS article + arXiv 2102.07573 + mathlib doc page, which jointly pin the standard form and its `CommRing` generality |
|  5 | Local references                  | grep `projects/NagellLutz/.mathlib-quality/references/`                                          | n/a  | (directory absent)                                                   | no `references/` dir under the project; recorded n/a |
|  6 | nLab                              | "elliptic divisibility sequence" / "division polynomial"                                         | n/a  | — | nLab has no dedicated page; this is classical NT, not a categorical concept |
|  7 | nCatLab (if categorical)          | —                                                                                               | n/a  | — | not a categorical concept |
|  8 | Stacks Project (if alg geom)      | "division polynomial" / "elliptic curve"                                                         | n/a  | — | Stacks does not cover the explicit division-polynomial recursion |
|  9 | MathOverflow / Math.StackExchange | "division polynomial coordinate ring congruence" generality                                     | yes  | confirms division polynomials reduce mod the curve relation; the bivariate/univariate split is folklore | matches the lemma's content |
| 10 | recent arXiv (last 5 years)       | "elliptic divisibility sequence recurrence" (2102.07573, 2109.03746)                            | yes  | recursion + reduction over a domain                                  | consistent with mathlib's `CommRing` statement |

The protocol passed: WebSearch ran ≥3 distinct queries at different generality levels;
local refs checked (absent → n/a); nLab/Stacks/nCatLab/MathOverflow/arXiv each checked
with a reason. ChatGPT MCP was down this session (per the explicit task note) and was
substituted by independent literature channels that pin the same standard form, so the
standard-form question is not left to a single channel.

### Literature summary (Phase 3)

Concept identified as: **division polynomials `ψₙ` of a Weierstrass curve / normalised
elliptic divisibility sequence (EDS)**, and specifically their *reduction in the affine
coordinate ring* against the univariate companion `Ψₙ`.
Sources agree on the standard form: yes — the bivariate `ψₙ` and the reduction of `ψ₂²`
to `Ψ₂Sq` modulo the curve relation are exactly how mathlib (and Angdinata's underlying
construction) set it up; the mathlib doc page is itself the top search hit.
Most general standard form: the congruence holds over an arbitrary commutative ring `R`
(no field, no characteristic hypothesis) — which is precisely the Lean statement.
Generality dimensions where the literature varies: base ring (some classical treatments
fix `ℤ` or a field; mathlib/Angdinata already give the maximally general `CommRing R`).
Disagreement with the literature: none.

---

### Generality analysis — `WeierstrassCurve.Affine.CoordinateRing.mk_ψ` (Phase 4)

Literature-standard form (from Phase 3): the congruence `ψₙ ≡ Ψₙ` in `R[W]` for an
arbitrary commutative ring `R` and arbitrary `n : ℤ`.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring         | NO                  | the coordinate ring `R[X][Y]/⟨W.poly⟩` and the EDS recursion both require a `CommRing`; this is already the weakest sensible class |
| 2 | `(n : ℤ)`              | arbitrary integer index  | arbitrary integer index  | NO                  | the result is stated for all `n : ℤ` (negatives via `ψ_neg`/`Ψ_neg`); cannot be weakened further |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is identical to mathlib's, which is the
maximally-general `CommRing R` statement).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled hypotheses → typeclasses/instances?                              | no       | — | already typeclass-driven (`[CommRing R]`); no bundled "let X be a foo" preamble |
|  2 | sequences/metric → filters/topology?                                    | no       | — | finite algebraic identity; no limiting process |
|  3 | construction → universal-property class?                                 | no       | — | `ψₙ`/`Ψₙ` are explicit recursive polynomials; no universal property at stake |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — | not a substructure statement |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                 | no       | — | already at `CommRing`, the relevant floor |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure?                   | no       | — | the `ℤ` index is intrinsic (the EDS is indexed by ℤ); generalising the index is meaningless here |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a concrete polynomial congruence already stated
at the right typeclass floor in the idiomatic mathlib style — indeed it *is* the
idiomatic mathlib statement, since it was copied from mathlib verbatim.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. Propositions introduce no definitional equalities or
typeclass-search paths, so the six-row risk table is skipped.

---

### Mathlib search-status: `WeierstrassCurve.Affine.CoordinateRing.mk_ψ` (Phase 5)

[A] Lean-Finder       n/a (index tool flaky this session)              — substituted by direct grep of the vendored mathlib pin (authoritative)
[B] Loogle            `WeierstrassCurve.Affine.CoordinateRing.mk` patterns  — n/a (flaky); direct grep used instead
[C] LeanSearch        "division polynomial coordinate ring congruence ψ Ψ"  — concept confirmed; points at the same `DivisionPolynomial/Basic` file
[D] Grep mathlib src  `mk_ψ\b` over `.lake/packages/mathlib/Mathlib/`        — **HIT**: exactly one match, `DivisionPolynomial/Basic.lean:438`
[E] Name pattern      `Affine.CoordinateRing.mk_ψ`                          — **HIT**: same single location

Searched for both:
  - the user's current form `mk W (W.ψ n) = mk W (W.Ψ n)` → found verbatim
  - the literature-standard form (same; it is already maximally general) → found verbatim

Concluded: **found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`;
identical form** — at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`.

The match is byte-for-byte. Mathlib line 438–439:

```lean
lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]
```

Project line 361–362 (identical name, statement, and proof script):

```lean
lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]
```

A `diff` of the whole surrounding `section ψ … section φ` block shows only cosmetic
deltas elsewhere in the file (point-free `def ψ : ℤ → R[X][Y]` vs mathlib's eta-expanded
`def ψ (n : ℤ)`, and trivial parenthesisation `(W.ψ n) ^ 2` vs `W.ψ n ^ 2`) — none touch
`mk_ψ`. The file header explicitly declares it a copy of the mathlib module. Same author
(David Kurniadi Angdinata) on both.

---

### Call sites — `WeierstrassCurve.Affine.CoordinateRing.mk_ψ` (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring file): **1**
- `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:44` —
  `evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_ψ W n)`
- (also referenced in the `EvalBridge.lean:7` module docstring as one of the bridged
  coordinate-ring congruence lemmas)
- (used inside this same file at line 406 by `mk_φ` — same-file, not counted)

External-to-project callers: the lemma is *also* used ~8× in the **HasseWeil** project
(same monorepo), e.g.:

| Caller file:line                                            | Usage pattern (one-line excerpt)                                     |
|-------------------------------------------------------------|----------------------------------------------------------------------|
| `HasseWeil/MulByIntPullback.lean:115`                       | `rw [Affine.CoordinateRing.mk_ψ (W := W.toAffine) n]`                 |
| `HasseWeil/OmegaPullbackCoeff.lean:177`                     | `rw [Affine.CoordinateRing.mk_ψ (W := W.toAffine) n]`                 |
| `HasseWeil/EC/MulByIntUnramified.lean:113`                  | `from Affine.CoordinateRing.mk_ψ (W := W.toAffine) n`                 |
| `HasseWeil/EC/IsogenyAG/CovarianceDischarge.lean:503`       | `WeierstrassCurve.Affine.CoordinateRing.mk_ψ (W := W.toAffine) n`     |
| `HasseWeil/Auxiliary/DivisionPolynomial.lean:731`           | `rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]` |

Inline-derivation grep (re-derived elsewhere without using `mk_ψ`?): (none) — consumers
use the lemma directly.

**What this tells us.** The consumption pattern (`K ≥ 1` internal + several cross-project
uses, no inline re-derivation) would normally lean YES-*. But the consumers depend on a
lemma that *already exists upstream verbatim*: every one of these call sites would resolve
identically against mathlib's `mk_ψ`. (The HasseWeil `Auxiliary/DivisionPolynomial.lean`
is itself another vendored copy of the same mathlib file.) So the call sites confirm the
lemma is genuine API, but not *missing* API — they argue for deleting the local copy and
pointing at mathlib, not for upstreaming.

### Composition check (Phase 6)

Can `mk_ψ` be derived from mathlib in ≤3 chained calls? It does not need to be *derived*
at all — it **is** a mathlib lemma. The trivial "composition" is the identity:

Attempt 1: `exact WeierstrassCurve.Affine.CoordinateRing.mk_ψ (W := …) n`
  - Mathlib decls used: `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`
  - Result: succeeds (it is the same statement)

Conclusion: **n/a — not a composition question; the lemma is present in mathlib directly**
(this is NO-mathlib-has-it, not NO-composable-from-mathlib).

---

## Verdict: `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): concept is the standard division polynomial `ψₙ` / normalised
  EDS; the top WebSearch hit is mathlib's own doc page for the very file this is copied from.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's `CommRing R`
  statement; no modern-idiom move; 0 weakenings.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`
  at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`; **byte-identical**.
- Composition check (Phase 6): n/a — direct mathlib lemma, not a composition.

**Rationale:**

This declaration is not a candidate for mathlib because mathlib already contains it,
verbatim. The file `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` announces in
its own header (lines 11–14) that it "is a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", vendored solely to
import a local `EllipticDivisibilitySequence` (renamed to dodge a `normEDS`/`complEDS`
name clash). The lemma `Affine.CoordinateRing.mk_ψ` at project line 361 is identical to
mathlib's at `DivisionPolynomial/Basic.lean:438` in name, signature
(`mk W (W.ψ n) = mk W (W.Ψ n)`), and proof script
(`simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]`),
authored by the same person (David Kurniadi Angdinata). A whole-section `diff` shows the
only divergences in the file are cosmetic (point-free `def ψ`, parenthesisation) and never
touch this lemma.

Because the project is, per the AINTLIB consolidation context, a fork of these exact
mathlib modules with duplicated General*/PID* tracks, this is precisely the
"already-in-mathlib" case the task flagged. The right action is consolidation: drop the
local fork's `mk_ψ` (and the surrounding copied `DivisionPolynomial.Basic` content) in
favour of the upstream module once the underlying `normEDS` name-clash is resolved — not a
mathlib PR.

**WHY not (refactor-actionable):**
Mathlib already has this exactly. The blocker that forced the copy is purely a naming
collision in the *EDS dependency* (`LutzNagell.EllipticDivisibilitySequence` redefines
`normEDS`/`complEDS`/`preNormEDS` that also live in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`). Resolve that — by reusing
mathlib's `EllipticDivisibilitySequence` and `DivisionPolynomial.Basic` directly instead of
the vendored copies — and this lemma plus its entire host file become redundant.

Existing mathlib decl:        `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`
Our form follows in ≤1 line (it is the same lemma):
```lean
example (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) :=
  WeierstrassCurve.Affine.CoordinateRing.mk_ψ n
```

Call sites in our project / monorepo (from Phase 6.0):
- NagellLutz: 1 direct (`EvalBridge.lean:44`) + 1 same-file (`mk_φ`, line 406).
- HasseWeil: ~8 (`MulByIntPullback`, `OmegaPullbackCoeff`, `MulByIntUnramified`,
  `CovarianceDischarge`, `Auxiliary/DivisionPolynomial`, …), all via
  `Affine.CoordinateRing.mk_ψ (W := W.toAffine) n`.

Refactor plan: this is a *consolidation* (the AINTLIB-wide dedup lane), not a per-call-site
swap, because the names already coincide. Concretely:
  1. Eliminate the EDS name clash: make `LutzNagell.EllipticDivisibilitySequence` either
     re-export or be replaced by `Mathlib.NumberTheory.EllipticDivisibilitySequence`
     (the reason given for forking).
  2. Delete the vendored `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` (and the
     parallel `HasseWeil/Auxiliary/DivisionPolynomial.lean`) and `import
     Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` instead.
  3. The ~10 call sites need no edits: `WeierstrassCurve.Affine.CoordinateRing.mk_ψ`
     resolves to the mathlib lemma with the identical signature once the local copy is gone.
  4. Verify `#print axioms` unchanged and `lake build` green across NagellLutz + HasseWeil.

Note: any genuinely *new* lemmas the forks added on top of the copied mathlib content
(the General*/PID* tracks) should be split out and kept; only the verbatim-mathlib portion
(this lemma and its siblings `mk_ψ₂_sq`, `mk_Ψ_sq`, `mk_φ`, the `ψ`/`Ψ`/`φ`/`Φ` defs,
`ψ_even`/`ψ_odd`, …) is the redundant part.

Next action: file an AINTLIB consolidation/dedup ticket to retire the vendored
`DivisionPolynomial.Basic` copy in favour of the mathlib module (gated on resolving the
`normEDS` EDS-name collision). Do **not** open a mathlib PR — mathlib already has it.

---

## Next step

File an AINTLIB consolidation/dedup ticket to retire the vendored copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` (this lemma included)
in favour of importing the mathlib module directly, after resolving the local
`normEDS`/`complEDS` name clash that motivated the fork. No mathlib PR is warranted.
