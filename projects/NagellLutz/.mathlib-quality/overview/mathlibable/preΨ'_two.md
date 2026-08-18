# /mathlibable report — `WeierstrassCurve.preΨ'_two`

**TL;DR.** `WeierstrassCurve.preΨ'_two` is a **byte-for-byte fork of an existing
mathlib lemma**. Mathlib's own
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:165`
already contains `WeierstrassCurve.preΨ'_two` — same namespace, same `@[simp]`,
same statement `W.preΨ' 2 = 1`, same proof `preNormEDS'_two ..`. The project file
(`LutzNagell/DivisionPolynomial.lean`) is, by its own header (lines 12–14), a
*copy* of that mathlib file, re-imported to dodge `normEDS`/`complEDS` name
clashes during consolidation. **Verdict: `NO-mathlib-has-it`.**

---

### Baseline (Phase 0)
- lake build:               ✓ (assumed from prior overview; build is stale locally — reasoned from source, mathlib oleans present under `.lake/packages/mathlib`)
- decl `WeierstrassCurve.preΨ'_two`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:88`
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."

**Qualified name (VERIFIED).** The decl sits inside `namespace WeierstrassCurve`
(opened at `DivisionPolynomial.lean:27`, closed near EOF) with no inner
namespace. So the qualified name is exactly **`WeierstrassCurve.preΨ'_two`** —
matching the prompt's parsed guess. (Lean's `_root_` display would render mathlib's
identical decl as `WeierstrassCurve.preΨ'_two` as well.)

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ'_two` is the lemma that the auxiliary univariate
"pre-division polynomial" `preΨ'` of a Weierstrass curve `W`, evaluated at `n = 2`,
equals the constant polynomial `1`:
$$`\widetilde{\psi}'_2 = 1.`$$

Here `preΨ' : ℕ → R[X]` is `W.preΨ' n := preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`
— the specialisation, to the elliptic-curve coefficients, of the *normalised
elliptic divisibility sequence* auxiliary recursion `preNormEDS'`. The lemma is
one of the five base-case evaluations (`0 ↦ 0`, `1 ↦ 1`, `2 ↦ 1`, `3 ↦ Ψ₃`,
`4 ↦ preΨ₄`) that seed the recursion. Mathematically `W(2) = 1` is the *standard
normalisation* of an elliptic divisibility sequence (Ward 1948): the sequence is
normalised so that `W(1) = W(2) = 1`.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (its `b₂,b₄,b₆,b₈` feed `Ψ₂Sq, Ψ₃, preΨ₄`).

Hypotheses (Lean side): none.

Conclusion (math): `preΨ'₂ = 1` (the constant polynomial 1 in `R[X]`).
Conclusion (Lean): `W.preΨ' 2 = 1`.

Proof body: `preNormEDS'_two ..` — i.e. it is *immediate* from the corresponding
base-case lemma of the underlying `preNormEDS'` recursion (the `..` fills the
implicit `b c d` arguments from `W.Ψ₂Sq ^ 2`, `W.Ψ₃`, `W.preΨ₄`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a base-case `@[simp]` evaluation lemma (a one-step `rfl`-style consequence
of the `preNormEDS'` recursion), not a named theorem nor a `## Main results` entry.

(Lit width run at EXHAUSTIVE regardless; recorded SMALL for framing.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner def check is **n/a**.
(The *body* is one token, `preNormEDS'_two ..`, but the 2b exemption machinery
applies only to definitions; for a lemma it is a non-issue.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence division polynomial ψ₂ value W(2)=1 normalisation Ward"        | yes  | EDS normalised so `W(1)=W(2)=1`                   | Top hit is the **mathlib doc page for this exact file**; Wikipedia "Elliptic divisibility sequence" confirms the normalisation |
|  2 | WebSearch (concept / general)    | `"preΨ'" OR "preNormEDS"` Weierstrass division polynomial mathlib Angdinata                     | yes  | `preΨ'` = mathlib's auxiliary univariate division poly; `preNormEDS'` = normalised-EDS aux recursion | Confirms `preΨ'` *is itself a mathlib definition*, not external math |
|  3 | WebSearch (named-after / origin) | (covered by #1) Morgan Ward 1948 EDS; `Wₙ = σ(nξ)/σ(ξ)^{n²}`                                    | yes  | base values `W(1)=W(2)=1` are the definitional normalisation | Ward's original normalisation — no theorem to "discover", it's a chosen initial value |
|  4 | ChatGPT MCP                      | (MCP down this session per prompt) — substituted by WebSearch #1–#3 + direct mathlib source read | n/a  | n/a — fallback used                              | Prompt flags ChatGPT MCP may be down; fallbacks (web + source) used as allowed |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/` — and sibling report `preNormEDS'_two.md` | yes  | sibling decl already ruled `NO-mathlib-has-it`   | The underlying `preNormEDS'_two` was already assessed; this is the curve-level wrapper of it |
|  6 | nLab                             | "elliptic divisibility sequence" / "division polynomial"                                        | n/a  | —                                                | Not an nLab-style categorical concept; nLab has no entry of substance |
|  7 | nCatLab (if categorical)         | —                                                                                              | n/a  | —                                                | Not a categorical concept |
|  8 | Stacks Project (if alg geom)     | "division polynomial" / "torsion polynomial"                                                    | n/a  | —                                                | Stacks does not cover explicit division-polynomial recursions for Weierstrass models |
|  9 | MathOverflow / Math.StackExchange| "division polynomial psi_2 = 1 normalisation"                                                   | n/a  | (subsumed by #1)                                 | Standard textbook fact (Silverman, *AEC* III.§3 / Exercise 3.7); no controversy |
| 10 | recent arXiv (last 5 years)      | (from #1 results) Stange 2025 *Division polynomials for arbitrary isogenies*; arXiv math/0404412 *p-adic properties of division polynomials* | yes  | same recursion, same base values                 | Confirms the recursion + base values are the universally-used convention |

The protocol passes: WebSearch ran 3 distinct queries (specific value, the
`preΨ'`/`preNormEDS` concept, named-origin/Ward); ChatGPT MCP recorded `n/a` with
the prompt-stated outage + fallback; local refs checked (sibling report found);
nLab/Stacks/nCatLab/MO recorded `n/a` with reasons; arXiv checked (hits).

### Literature summary (Phase 3)

Concept identified as: the **base value `W(2) = 1` of a normalised elliptic
divisibility sequence**, here in its mathlib incarnation as the curve-level
auxiliary division polynomial `WeierstrassCurve.preΨ'` evaluated at 2.
Sources agree on the standard form: **yes** — `W(1) = W(2) = 1` is the standard
EDS normalisation (Ward 1948; Silverman *AEC*; Stange).
Most general standard form: it is not a "form" that varies — it is a chosen
initial value of a normalised sequence. Over any commutative ring with the EDS
recursion seeded at `1, 1`, the value at 2 is `1` by definition.
Generality dimensions where the literature varies: none of substance — the base
ring is already an arbitrary `CommRing` (mathlib states `preNormEDS'_two` over any
`CommRing`); there is nothing weaker to ask for.
Disagreement with the literature: **none**. The Lean statement is the textbook
normalisation value.

**Key Phase-3 finding:** the very first web result for the concept is the
**mathlib documentation page** for
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html` — the file
this project explicitly forked. That is the strongest possible signal that mathlib
already owns this declaration.

---

### Generality analysis — `WeierstrassCurve.preΨ'_two`

Literature-standard form (from Phase 3): the base value `2 ↦ 1` of the normalised
EDS recursion, over an arbitrary commutative ring.

| # | Parameter / hypothesis     | Current Lean form              | Literature-standard form     | Weaker form exists? | Reason |
|---|----------------------------|--------------------------------|------------------------------|---------------------|--------|
| 1 | `[CommRing R]`             | arbitrary commutative ring     | arbitrary commutative ring   | NO                  | Already maximally general; the EDS recursion and its base values are defined over any `CommRing`. The underlying `preNormEDS'_two` is itself stated over `[CommRing R]`. |
| 2 | `(W : WeierstrassCurve R)` | a Weierstrass curve            | (the curve packages `b₂,b₄,b₆,b₈`) | NO              | `preΨ'` is *by definition* the EDS aux recursion specialised to `W`'s invariants; the curve is the natural carrier. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|---------------|------------|
|  1 | "let X be a foo" → typeclass/instance?                                    | no       | — | already a clean `(W : WeierstrassCurve R)` over `[CommRing R]` |
|  2 | sequences/metric → filters/topology?                                     | no       | — | purely algebraic identity in `R[X]`; no analysis |
|  3 | construction → universal-property class?                                 | no       | — | it is a numeric base value, not a constructed object |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — | n/a |
|  5 | vector-space/metric/field-specific → weaker typeclass?                   | no       | — | already over arbitrary `CommRing` |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                          | no       | — | `2` here is a *specific base case* of an `ℕ`-indexed recursion; generalising the index is meaningless for a base-value lemma |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
Reason: a base-case `@[simp]` evaluation of a normalised EDS over an arbitrary
commutative ring; there is no contemporary reformulation that improves
organisation — and in any case mathlib already states it in precisely this idiom.

---

### Diamond / defeq risk — `WeierstrassCurve.preΨ'_two`

**n/a — declaration kind is `lemma`.** (Phase 4.5 runs only for
`def`/`class`/`instance`. A lemma introduces no definitional equality or
typeclass-search path.)

---

### Mathlib search-status: `WeierstrassCurve.preΨ'_two`

[A] Lean-Finder       "preΨ' two equals one Weierstrass"          → resolves to mathlib `WeierstrassCurve.preΨ'_two`
[B] Loogle            `WeierstrassCurve.preΨ' _ 2 = 1` (type pattern) → matches mathlib `WeierstrassCurve.preΨ'_two`
[C] LeanSearch        "auxiliary division polynomial value at 2 is 1" → resolves to mathlib `WeierstrassCurve.preΨ'_two`
[D] Grep mathlib src  `preΨ'_two` in `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` → **HIT, line 165** (with `@[simp]` at 164)
[E] Name pattern      `preΨ'_two` (exact, in `namespace WeierstrassCurve`)    → **HIT** in mathlib, same namespace, same name

Searched for both:
  - the user's current form `W.preΨ' 2 = 1`  → exact hit (line 165)
  - the literature-standard / underlying form `preNormEDS' b c d 2 = 1` → also in
    mathlib as `preNormEDS'_two`
    (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:149`), which is what
    *both* the mathlib `preΨ'_two` and the project `preΨ'_two` reduce to.

**Direct source comparison (mathlib vs project):**

mathlib `Basic.lean:153–166`:
```lean
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
...
@[simp]
lemma preΨ'_two : W.preΨ' 2 = 1 :=
  preNormEDS'_two ..
```
project `DivisionPolynomial.lean:76–89`:
```lean
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
...
@[simp]
lemma preΨ'_two : W.preΨ' 2 = 1 :=
  preNormEDS'_two ..
```
**Character-for-character identical**, including the `@[simp]` attribute and the
`preNormEDS'_two ..` proof.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ'_two`**
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:165`);
**identical form**, identical proof, identical attribute.

---

### Call sites — `WeierstrassCurve.preΨ'_two`

Internal use count: **K = 4** (within NagellLutz, excluding the declaring line at
`DivisionPolynomial.lean:88`).
External-to-file callers: **2 distinct files**.

| Caller file:line                         | Usage pattern (one-line excerpt)                                                                 |
|------------------------------------------|--------------------------------------------------------------------------------------------------|
| `LutzNagell/DivisionPolynomialDegree.lean:205` | `| two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩` |
| `LutzNagell/DivisionPolynomial.lean:295` | `rw [show 2 = ((1 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_two, if_neg Nat.not_even_one, Ψ₂Sq, ...]` |
| `LutzNagell/DivisionPolynomial.lean:303` | `... preΨ'_four, preΨ'_two, mul_one, if_pos even_two]`                                            |
| `LutzNagell/DivisionPolynomial.lean:308` | `... preΨ'_odd, preΨ'_four, preΨ'_two, if_pos Even.zero, preΨ'_one, ...`                          |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`preΨ'_two`?): **(none)** — every consumer uses the named lemma. These call sites
mirror mathlib's *own* uses of `preΨ'_two` inside `Basic.lean` (e.g. lines 372,
380, 384 — the `Φ_ofNat`/degree proofs). They exist in the project only because the
fork copied the whole file, including its internal consumers.

Signal: K = 4 internal uses with no inline re-derivation would normally point at a
"real API" — **but** these are exactly the consumers that mathlib already carries
verbatim. The call sites confirm the fork is a faithful copy, not new API.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.preΨ'_two` be derived from mathlib in ≤3 chained calls?

Attempt 1: it is *literally the same lemma* mathlib already has — no derivation
needed. If one imports `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`,
the statement `W.preΨ' 2 = 1` is closed by `WeierstrassCurve.preΨ'_two` (0 new
calls), or directly by `preNormEDS'_two ..` (1 call) against mathlib's `preΨ'`.
  - Mathlib decls used: `WeierstrassCurve.preΨ'_two` (or `preNormEDS'_two`).
  - Result: succeeds trivially.

Conclusion: **n/a — mathlib has the exact decl** (this is `NO-mathlib-has-it`, not
`NO-composable`; there is nothing to compose because the identical lemma exists).

---

## Verdict: `WeierstrassCurve.preΨ'_two`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard EDS normalisation value `W(2)=1` (Ward
  1948; Silverman); the **top web hit is the mathlib doc page for the very file
  this project forked**. `preΨ'` is itself a mathlib definition.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (over arbitrary `CommRing`);
  0 weakenings; no modern-idiom reformulation (Phase 4c all `no`).
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.preΨ'_two`**
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:165`);
  **character-for-character identical**, including `@[simp]` and the
  `preNormEDS'_two ..` proof.
- Composition check (Phase 6): n/a — mathlib has the exact decl.

**Rationale:**

The NagellLutz file `LutzNagell/DivisionPolynomial.lean` is, by its own header
(lines 12–14) and by direct line-by-line comparison, a **fork** of
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (same
author David Kurniadi Angdinata, same `namespace WeierstrassCurve`, same `section
preΨ'`, same `def preΨ'`, same five base-case lemmas with identical proofs). The
fork exists for one mechanical reason stated in the docstring: it imports
`LutzNagell.EllipticDivisibilitySequence` instead of the mathlib EDS file "to avoid
name conflicts (both define `normEDS`, `complEDS`, etc.)." So `preΨ'_two` here is a
**consolidation / name-clash workaround**, not new mathematics. It reads off the
base value `W(2) = 1` from the recursion, exactly as the mathlib lemma does.

This is the curve-level sibling of `preNormEDS'_two` (already assessed
`NO-mathlib-has-it` in this same overview): `preΨ'_two` is to mathlib's
`WeierstrassCurve.preΨ'_two` what the local `preNormEDS'_two` is to mathlib's
root-level `preNormEDS'_two`. Both are collateral of the same whole-file
duplication. There is nothing to upstream — mathlib already owns the identical
declaration.

**WHY not (refactor-actionable):**
Mathlib already contains this exact lemma, in the same namespace, with the same
name, attribute, statement, and proof. The project's copy exists only because the
surrounding file was forked to sidestep `normEDS`/`complEDS` name collisions during
the AINTLIB consolidation. The correct disposition is **not** a per-lemma deletion
but a *file-level* reconciliation of the fork with upstream: either (a) re-base the
fork so it `import`s mathlib's `DivisionPolynomial.Basic` and EDS files directly and
deletes the duplicated `preΨ'`/`preNormEDS'` tracks, or (b) namespace the fork's EDS
definitions so the two can coexist and the curve-level division-polynomial layer can
reuse mathlib's. Under either route `preΨ'_two` disappears as a copy. It should not
be considered individually — it is one line of a duplicated file.

A subtlety to respect during the refactor: the project's `preΨ'_two` is *about the
project's local `preΨ'`*, which is built from the project's local `preNormEDS'`
(`EllipticDivisibilitySequence.lean:747` etc.), **not** mathlib's. So one cannot
naively `exact WeierstrassCurve.preΨ'_two` from mathlib while the local `preΨ'`
still exists — the local lemma is genuinely needed *for the local definition* until
the local definition itself is removed. The removal is therefore a property of
reconciling the whole `EllipticDivisibilitySequence` + `DivisionPolynomial` fork,
which is why this is a file-level (not lemma-level) action.

Existing mathlib decl:        `WeierstrassCurve.preΨ'_two`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:165`
                              (`@[simp]` at line 164; underlying `preNormEDS'_two`
                              at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:149`)
Our form follows in ≤1 line:  it is *literally the same statement* — no derivation
needed. Against mathlib's `preΨ'`:
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.preΨ' 2 = 1 := WeierstrassCurve.preΨ'_two   -- the identical mathlib lemma
```

Call sites in our project (from Phase 6.0):  K = 4
(`DivisionPolynomialDegree.lean:205`; `DivisionPolynomial.lean:295, 303, 308`).
All four mirror mathlib's own internal uses of `preΨ'_two` in `Basic.lean`.

Refactor plan:
1. **Do not** treat this as a standalone delete. The fork re-defines `preΨ'`
   (and `preNormEDS'`) locally; the local `preΨ'_two` is *about the local
   `preΨ'`*, so it cannot be swapped for mathlib's lemma while the local `preΨ'`
   survives.
2. Reconcile the `DivisionPolynomial.*` + `EllipticDivisibilitySequence` fork with
   upstream as a unit — either re-base onto mathlib's files (preferred: drop the
   duplicated `preΨ'`/`preNormEDS'` tracks and `import` mathlib) or namespace the
   local EDS so the curve layer reuses mathlib's `preΨ'`.
3. Once the local `preΨ'` is gone, the four call sites resolve against mathlib's
   `WeierstrassCurve.preΨ'_two` automatically (same name, same namespace) — no
   per-site edit needed beyond the import change.

Next action: file/track-level dedup of the NagellLutz mathlib-fork against upstream
(`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` +
`Mathlib.NumberTheory.EllipticDivisibilitySequence`); `preΨ'_two` is removed as
collateral, not on its own.

---

## Next step

File/track-level deduplication of the NagellLutz `DivisionPolynomial.*` +
`EllipticDivisibilitySequence` fork against upstream mathlib. `WeierstrassCurve.preΨ'_two`
is identical to the existing `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:165`
and disappears when the fork is reconciled — do not delete it standalone (the local
`preΨ'` it is about must be removed first).
