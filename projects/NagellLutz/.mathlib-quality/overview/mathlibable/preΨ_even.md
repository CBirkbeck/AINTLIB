# /mathlibable report — `WeierstrassCurve.preΨ_even`

> **TL;DR.** This declaration is a **verbatim fork** of mathlib's
> `WeierstrassCurve.preΨ_even`
> (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:225`):
> same qualified name, byte-identical statement, byte-identical proof
> (`preNormEDS_even ..`). The NagellLutz `DivisionPolynomial.lean` file header
> states outright that it is "a copy of
> `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" that only
> swaps the import of `EllipticDivisibilitySequence` to dodge a `normEDS` /
> `complEDS` name clash. Verdict is **`NO-mathlib-has-it`**, decided at
> Phase 0 / Phase 5. The remaining phases are filled in for completeness, but the
> conclusion is not in doubt.

---

### Baseline (Phase 0)
- lake build:               ✓ assumed clean (local build stale; reasoning from source — the decl is a 1-line term-mode wrapper that has shipped in mathlib unchanged, so elaboration is not in question)
- decl `WeierstrassCurve.preΨ_even`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:148`
- kind:                      lemma
- has sorry:                 no  (proof is `preNormEDS_even ..`)
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

**Qualified name (VERIFIED).** Only `namespace WeierstrassCurve` (file line 27) is
open at line 148; the intervening `section preΨ` (line 111) adds no name prefix.
So the base name `preΨ_even` qualifies to **`WeierstrassCurve.preΨ_even`** — exactly
the mathlib name.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ_even` is the **even-index (duplication) recurrence** for the
normalised division polynomials `preΨ` of a Weierstrass curve `W` over a commutative
ring `R`. For every `m : ℤ`:

$$
\operatorname{pre}\Psi_{2m} \;=\; \operatorname{pre}\Psi_{m-1}^{2}\,\operatorname{pre}\Psi_{m}\,\operatorname{pre}\Psi_{m+2}\;-\;\operatorname{pre}\Psi_{m-2}\,\operatorname{pre}\Psi_{m}\,\operatorname{pre}\Psi_{m+1}^{2}.
$$

This is the classical division-polynomial identity
$\psi_{2m}\,\psi_2 = \psi_m\!\left(\psi_{m+2}\psi_{m-1}^2 - \psi_{m-2}\psi_{m+1}^2\right)$,
with the common $\psi_2$ factor stripped (mathlib's `preΨ` is the "pre"-normalised
form that omits the ψ₂ for even indices; the factor reappears in `Ψ`/`ΨSq`).

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — coefficient ring.
- `(W : WeierstrassCurve R)` — the curve (provides `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, the EDS seeds).
- `(m : ℤ)` — the index; the statement holds for **all** integers (negatives handled by `preΨ_neg`).

Hypotheses: none beyond the typeclasses.

Conclusion (math): the even-index recurrence above, valid over any commutative ring.

Conclusion (Lean):
`W.preΨ (2 * m) = W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) - W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2`

The body is `preNormEDS_even ..`, i.e. it is a thin specialisation of the
ring-level EDS lemma `preNormEDS_even b c d (2*m) = …` with `(b,c,d) = (W.Ψ₂Sq^2, W.Ψ₃, W.preΨ₄)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a recurrence lemma about an existing definition (`preΨ`); not a new named
structure, not a person/place-named theorem, not a stated main result of the
project. (It is a structural building block, not a headline result.)

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**.
(For the record, the *proof* is one line, `preNormEDS_even ..`, which is itself the
strongest possible signal that mathlib already carries the content: the project's
lemma is definitionally the mathlib lemma applied to the curve's EDS seeds.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic divisibility sequence duplication formula W(2m) even index recurrence division polynomial" | yes | $\psi_{2n}\psi_2 = \psi_n(\psi_{n+2}\psi_{n-1}^2 - \psi_{n+1}^2\psi_{n-2})$, $n\ge3$ | Wikipedia "Elliptic divisibility sequence"; Ward (1940s); mathlib docs page surfaced directly |
| 2 | WebSearch (general form) | "division polynomial recurrence psi_{2m} psi_{m} even formula Weierstrass elliptic curve" | yes | even: $\psi_{2m}\psi_2 = \psi_{m-1}^2\psi_m\psi_{m+2} - \psi_{m-2}\psi_m\psi_{m+1}^2$; over any base | Silverman AEC Ch. III/Exercises; arXiv:1303.4327 "Homogeneous division polynomials" |
| 3 | WebSearch (named-after / aliases) | EDS / "Ward recurrence" / division-polynomial duplication | yes | same identity; called EDS recurrence, division-poly recursion, Ward's relations | name varies, identity is universal & classical |
| 4 | ChatGPT MCP | (environment: MCP down — recorded n/a) | n/a | — | Fallback channels (WebSearch ×3, Wikipedia, arXiv, mathlib docs) already pin the standard form unambiguously; ChatGPT would add nothing here |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/` | n/a | (no references dir; refs not present locally) | both directories absent — recorded n/a |
| 6 | nLab | "elliptic divisibility sequence" / "division polynomial" | n/a | — | not an nLab-style categorical concept; classical arithmetic recurrence; no clean abstract entry expected |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | — | n/a | — | not the kind of scheme-theoretic statement Stacks catalogues (concrete polynomial recurrence) |
| 9 | MathOverflow / MSE | EDS even recurrence generality / over commutative rings | yes | confirms identity holds formally over any commutative ring (it is a polynomial identity in the seeds) | matches mathlib's `CommRing` generality |
| 10 | recent arXiv (≤5 yr) | "A recurrence relation for elliptic divisibility sequences" (arXiv:2102.07573); "On Elliptic Sequences over Commutative Rings" (arXiv:2604.05280) | yes | same recurrence; the 2604.05280 title explicitly works over **commutative rings** | confirms `CommRing` is the right, already-standard generality |

### Literature summary (Phase 3)

Concept identified as: **the even-index (duplication) recurrence of division polynomials / elliptic divisibility sequences** (Ward's EDS recurrence; Silverman division-polynomial recursion).
Sources agree on the standard form: **yes** — $\psi_{2m}\psi_2 = \psi_{m-1}^2\psi_m\psi_{m+2} - \psi_{m-2}\psi_m\psi_{m+1}^2$, uniformly across Wikipedia, Silverman, Ward, and the arXiv literature.
Most general standard form: a **polynomial identity over an arbitrary commutative ring** in the EDS seeds — exactly what mathlib states via `preNormEDS_even` (ring-level) and `preΨ_even` (curve-level).
Generality dimensions where the literature varies:
  - base ring: from ℤ (classical Ward/Silverman) up to **arbitrary commutative ring** (arXiv:2604.05280, mathlib). The most general is the commutative-ring form, and mathlib already sits there.
  - index range: literature often states $m\ge3$ for the ℕ-form; mathlib gives the **full ℤ** version (all `m`), strictly stronger.
Disagreement with the literature: **none.** Mathlib's `preΨ` simply factors out the ψ₂ (carried separately in `Ψ`/`ΨSq`), which is the standard normalisation, not a deviation.

---

### Generality analysis — `WeierstrassCurve.preΨ_even`

Literature-standard form (from Phase 3): even-index recurrence, polynomial identity over an arbitrary commutative ring, all integer indices.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | **NO** | The recurrence is a genuine polynomial identity requiring subtraction and commutative multiplication; `CommRing` is exactly the literature's most-general base. Already maximal. |
| 2 | `(m : ℤ)` | full integer index | $m\ge3$ (classical) up to all ℤ | NO (already the strong form) | mathlib's ℤ-statement is *stronger* than the classical $m\ge3$ form; negative/edge indices handled via `preNormEDS_neg`. No weakening available — it is already the general one. |
| 3 | `(W : WeierstrassCurve R)` | a Weierstrass curve | a Weierstrass curve | NO | The curve only supplies the three EDS seeds; the truly general statement is the seed-level `preNormEDS_even` (`b c d : R`), which mathlib **also already has**. `preΨ_even` is the intended curve-level specialisation. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to the literature-standard form, and identical to mathlib's own statement).
Number of weakening opportunities found: **0**.
Proposed restatement: none — it already matches both the literature standard and mathlib verbatim.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses/instances? | no | — | already typeclass-driven (`CommRing`) |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic recurrence; no limits/topology |
| 3 | construction → universal-property class? | no | — | it is an identity, not a construction |
| 4 | set+closure-predicate → bundled substructure? | no | — | no substructure involved |
| 5 | vector-space/field-specific → weaken typeclasses? | no | — | already at `CommRing`, the weakest sensible base |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | — | the index is intrinsically ℤ (the curve's ℤ-graded EDS); generalising the index is not a mathlib direction here, and mathlib already uses ℤ |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** This is a finite algebraic recurrence already stated at mathlib's preferred generality (`CommRing`, full ℤ index) and — decisively — **already present in mathlib in this exact idiom**. There is no organisational improvement to make; the contemporary mathlib form *is* the current form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.preΨ_even`

[A] Lean-Finder       (MCP index unavailable in this env)                                   n/a: tool not loaded; superseded by definitive [D] grep hit
[B] Loogle            `WeierstrassCurve.preΨ _ = _ - _` / `preNormEDS _ _ _ (2 * _) = _`     n/a: tool not loaded; superseded by [D]
[C] LeanSearch        "division polynomial even index recurrence Weierstrass curve"          (web hit returned the mathlib docs page for `Mathlib.NumberTheory.EllipticDivisibilitySequence` directly — see Phase 3 row 1)
[D] Grep mathlib src  `preΨ_even` / `preNormEDS_even` in `.lake/packages/mathlib/`           **HIT — definitive**
[E] Name pattern      `lemma preΨ_even` namespace-aware                                       **HIT — `WeierstrassCurve.preΨ_even`, identical qualified name**

Searched for both:
  - the user's current form → mathlib `WeierstrassCurve.preΨ_even`, `Basic.lean:225` — **byte-identical statement and proof**.
  - the literature-standard / more-general seed form → mathlib `preNormEDS_even`, `EllipticDivisibilitySequence.lean:209` — the ring-level lemma that the curve-level one calls.

**Direct source comparison (the decisive evidence):**

Project, `DivisionPolynomial.lean:148–151`:
```lean
lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =
    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  preNormEDS_even ..
```
Mathlib, `Basic.lean:225–228`:
```lean
lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =
    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  preNormEDS_even ..
```
Identical token-for-token (same namespace `WeierstrassCurve`, same signature, same
proof term). The underlying `preNormEDS_even` is likewise a verbatim copy
(project EDS:807 ↔ mathlib EDS:209).

Concluded: **"found in mathlib as `WeierstrassCurve.preΨ_even`; identical form"**
(and the general seed form `preNormEDS_even` is also present, identical).

---

### Call sites — `WeierstrassCurve.preΨ_even`

Internal use count (NagellLutz, excluding the declaring file): **2**
- `LutzNagell/DivisionPolynomial.lean:199` — `rw [ΨSq, preΨ_even, if_pos <| even_two_mul m]` (inside `ΨSq_even`)
- `LutzNagell/DivisionPolynomial.lean:248` — `simp_rw [Ψ, preΨ_even, …]` (inside `Ψ_even`)

External-to-project callers (repo-wide): **HasseWeil** uses the *mathlib-named*
`WeierstrassCurve.preΨ_even` directly (the names coincide, so its `import` resolves
to whichever copy is in scope):
- `HasseWeil/OmegaPullbackCoeff.lean:341, 386, 395` — `WeierstrassCurve.preΨ_even (W := W) (3 : ℤ)` etc.
- `HasseWeil/Verschiebung/Route2Universal.lean:1422, 1434` — references in proof-plan comments.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| DivisionPolynomial.lean:199 | `rw [ΨSq, preΨ_even, if_pos <| even_two_mul m]` |
| DivisionPolynomial.lean:248 | `simp_rw [Ψ, preΨ_even, if_pos <| even_two_mul m, …]` |
| OmegaPullbackCoeff.lean:341 | `WeierstrassCurve.preΨ_even (W := W) (3 : ℤ),` |
| OmegaPullbackCoeff.lean:386 | `WeierstrassCurve.preΨ_even (W := W) (4 : ℤ),` |
| OmegaPullbackCoeff.lean:395 | `…, WeierstrassCurve.preΨ_even (W := W) (3 : ℤ), …` |

Inline-derivation grep (re-derived elsewhere without using `preΨ_even`?): **(none)** —
all consumers go through the lemma. This is genuine internal API; the only reason it
lives in the project at all is the `normEDS`/`complEDS` import clash described in the
file header, not because mathlib lacks it.

Composability signal: K = 2 internal + downstream HasseWeil use → real API. But this
signal points to **keeping the dependency on mathlib's copy**, not to contributing a
new lemma — mathlib already exports exactly this.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.preΨ_even` be derived from mathlib in ≤3 chained calls?

Attempt 1: it **is** mathlib's lemma. The project body is literally
`preNormEDS_even ..`, the same proof mathlib uses, and mathlib additionally exports
the fully-applied curve-level `WeierstrassCurve.preΨ_even` itself.
  - Mathlib decls used: `WeierstrassCurve.preΨ_even` (direct), or `preNormEDS_even` (one specialisation).
  - Result: **succeeds trivially** — zero new content.

Conclusion: **COMPOSABLE / SUPERSEDED** — but the accurate description is stronger
than "composable from primitives": mathlib has the *finished lemma under the same
qualified name*, so the correct bucket is `NO-mathlib-has-it`, not
`NO-composable-from-mathlib`.

---

## Verdict: `WeierstrassCurve.preΨ_even`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the even-index recurrence is the classical Ward/Silverman EDS / division-polynomial duplication identity; standard over any commutative ring; the search even surfaced the mathlib docs page directly.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — `CommRing`, full ℤ index; identical to the literature standard and to mathlib's own statement. No modern-idiom improvement available.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.preΨ_even`** (`Basic.lean:225`), byte-identical statement and proof; the general seed form `preNormEDS_even` is also present (`EllipticDivisibilitySequence.lean:209`).
- Composition check (Phase 6): trivially superseded — the project lemma's body *is* mathlib's proof.

**Rationale.**
This declaration is not a candidate for mathlib because **mathlib already has it,
verbatim, under the very same qualified name** `WeierstrassCurve.preΨ_even`. The
NagellLutz `DivisionPolynomial.lean` file is, by its own header, "a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked solely so
it can import a project-local `EllipticDivisibilitySequence` (to avoid a `normEDS` /
`complEDS` name collision). The lemma's statement, its one-line proof
(`preNormEDS_even ..`), and even the underlying ring-level lemma it delegates to are
all identical to the mathlib originals — I diffed them token-for-token. There is no
new mathematics, no stronger generality, and no alternative formulation on offer; the
literature search merely confirms that mathlib's form is already the standard one.

This is the textbook `NO-mathlib-has-it` case: a project fork of an upstream
declaration. The 2 internal call sites (and the downstream HasseWeil uses of the
same-named lemma) are real, but they are exactly why the fork exists in this build —
not evidence of an mathlib gap. The companion overview report for the seed lemma
`preNormEDS_even.md` reached the same `NO-mathlib-has-it` verdict independently.

**WHY not (refactor-actionable).**
Mathlib already provides this lemma. The only reason a copy lives in NagellLutz is the
deliberate import-swap to a project-local EDS file (header lines 12–17). The "refactor"
is therefore **not** a delete-and-replace at call sites — within this consolidation
monorepo the fork is load-bearing precisely because the project re-defines
`normEDS`/`complEDS` and must keep its `preΨ`-stack consistent with *that* EDS. The
actionable items are upstream-hygiene, not call-site rewrites:

  - **Do not upstream / PR this lemma** — it is already in mathlib unchanged.
  - **Track-toward-dedup:** the genuine cleanup target is the *fork itself*. If/when the
    project's `EllipticDivisibilitySequence` is reconciled with mathlib's (i.e. the
    `normEDS`/`complEDS` name clash is resolved, e.g. by namespacing the project copy or
    by the project switching to mathlib's EDS), the entire `DivisionPolynomial.lean`
    copy — `preΨ_even` included — should be deleted and its consumers pointed back at
    `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. That is a
    file-level (not lemma-level) consolidation ticket and a judgement call for the
    project owner, out of scope for a single-decl mathlibable verdict.
  - Mathlib decl to depend on: **`WeierstrassCurve.preΨ_even`**,
    `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:225`.
  - General seed form (if the curve wrapper is ever bypassed): **`preNormEDS_even`**,
    `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:209`.

Existing mathlib decl:        `WeierstrassCurve.preΨ_even`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:225`
Our form follows in ≤1 line (it is the same lemma):
```lean
example (W : WeierstrassCurve R) (m : ℤ) :
    W.preΨ (2 * m) =
      W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
        W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  WeierstrassCurve.preΨ_even m   -- mathlib's lemma, verbatim
```
Call sites in this project (Phase 6.0): K = 2 (plus downstream HasseWeil uses of the same name).
Refactor plan: this is a forked-file situation, not a per-call-site swap. Resolve at the
**file** level by reconciling the project EDS with mathlib (see the dedup note above);
once reconciled, delete the `DivisionPolynomial.lean` copy and let `import
Mathlib.…DivisionPolynomial.Basic` supply `preΨ_even` to the 2 internal sites and the
HasseWeil consumers.

Next action: keep `preΨ_even` out of any mathlib PR (already upstream). File/track a
**file-level** consolidation ticket to retire the `DivisionPolynomial.lean` fork once
the `EllipticDivisibilitySequence` name clash is resolved; that single action removes
this lemma and its whole sibling stack as duplicates.

---

## Next step

Keep this lemma out of mathlib — it is already there verbatim as
`WeierstrassCurve.preΨ_even`. The real cleanup is a **file-level** dedup of the entire
`DivisionPolynomial.lean` fork (driven by the `normEDS`/`complEDS` import clash), which
is a project-owner judgement call, not a per-declaration refactor.
