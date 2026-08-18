# /mathlibable report — `WeierstrassCurve.map_preΨ'`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> TL;DR: **NO-mathlib-has-it.** This is a verbatim fork of the mathlib lemma of
> the same fully-qualified name. The file's own module docstring says so.

---

### Baseline (Phase 0)
- lake build:               (stale locally — not re-run; reasoned from source, per task brief)
- decl `WeierstrassCurve.map_preΨ'`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:437`
- kind:                      `lemma` (carries `@[simp]`)
- has sorry:                 no
- module docstring summary:  *"This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."*

The qualified name is **`WeierstrassCurve.map_preΨ'`** (namespace opened at line 27
`namespace WeierstrassCurve`; the decl lives in `section Map`, no nested namespace).
The parsed guess in the task brief is correct.

---

### Statement (Phase 1)

`WeierstrassCurve.map_preΨ'` states: for a Weierstrass curve `W` over a commutative
ring `R`, a ring homomorphism `f : R →+* S`, and `n : ℕ`, the `n`-th auxiliary
univariate division polynomial `preΨ'` commutes with the base-change of `W` along
`f`. Concretely, computing `preΨ'ₙ` for the curve `W.map f` over `S` equals applying
`f` coefficient-wise (via `Polynomial.map f`) to `W`'s own `preΨ'ₙ`.

Mathematically: the family `{preΨ'ₙ}` of division-polynomial building blocks is
**natural** in the base ring. The division polynomials are universal polynomial
expressions in the `aᵢ` (equivalently the `bᵢ`) coefficients of the Weierstrass
equation, so applying a ring map to the coefficients and then forming `preΨ'ₙ`
agrees with forming `preΨ'ₙ` first and pushing the coefficients through `f`.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — base ring.
- `{S : Type s} [CommRing S]` — target ring.
- `(W : WeierstrassCurve R)` — the curve.
- `(f : R →+* S)` — ring homomorphism (the section's `variable`).
- `(n : ℕ)` — index.

Hypotheses: none beyond the typeclasses.

Conclusion (math): `preΨ'` is natural — `(W.map f).preΨ' n = Polynomial.map f (W.preΨ' n)`.

Conclusion (Lean): `(W.map f).preΨ' n = (W.preΨ' n).map f`.

Proof body (1 line): `by simp [preΨ', map_preNormEDS', ← coe_mapRingHom]`.
Mathlib's identical lemma uses `by simp [preΨ', ← coe_mapRingHom]` — the only
textual difference is the extra `map_preNormEDS'` simp lemma in the project's set
(cosmetic: the project forks `preΨ'`/`preNormEDS'` into its own EDS file, so the
simp set names the forked unfolding lemma explicitly).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` naturality/compatibility lemma (a "map_" commutation lemma) — a
helper, not a named theorem, not a new structure, not a `## Main results` entry.

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. The body is a one-line
`simp`, but the one-liner heuristic applies to definitions (defeq/diamond/API
concerns), not to proof terms of lemmas. Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" "base change" / commutes with ring homomorphism elliptic curve           | partial | division polys are universal ℤ-polynomials in `aᵢ`; naturality is standard folklore | Silverman AEC III.§3 (exercise-level); no one cites "map_preΨ'" — it's a Lean-internal helper |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence" base change / functoriality `preNormEDS`                       | partial | EDS defined by a recurrence over any comm ring; clearly functorial | Ward (1948); Shipsey thesis; Stange. Functoriality is immediate from the recurrence, never stated as a named result |
|  3 | WebSearch (named-after / aliases)| "psi polynomial" OR "Ψ_n" elliptic curve naturality / "preΨ" Angdinata Lean                     | yes  | This is mathlib's own naming (David Angdinata's division-polynomial library) | "preΨ'" is not classical notation; it is the name in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to reasoning) standard form + generality + history          | n/a  | — | Brief states ChatGPT MCP may be down; substituted WebSearch #1–3 + reasoning. Conclusion unaffected: the result is upstream verbatim, so the standard-form question is settled by mathlib itself |
|  5 | Local references                 | grep `refs/NagellLutz/`, `.mathlib-quality/references/` for "division polynomial"/"preΨ"         | n/a  | — | No references dir populated for this concept in-repo; Silverman AEC is the canonical text |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                         | no   | — | nLab has no dedicated page; not a category-theoretic concept |
|  7 | nCatLab                          | —                                                                                               | n/a  | — | not a categorical concept |
|  8 | Stacks Project                   | division polynomial / Weierstrass equation base change                                           | n/a  | — | Stacks treats elliptic curves abstractly (schemes); does not develop explicit division polynomials |
|  9 | MathOverflow / Math.StackExchange| division polynomials functoriality / reduction mod p                                            | partial | "division polynomials reduce well mod p" — same naturality, stated informally | e.g. threads on `ψ_n mod p`; confirms the fact is considered routine |
| 10 | recent arXiv (last 5 years)      | elliptic divisibility sequence division polynomial formalization Lean                            | yes  | Angdinata–Xu "Elliptic curves in Lean/mathlib" describe exactly this API | confirms `preΨ'` + its `map_` lemmas are the mathlib formalisation, authored upstream |

### Literature summary (Phase 3)

Concept identified as: **naturality / base-change-compatibility of the (auxiliary)
elliptic division polynomials** — i.e. the division polynomials `preΨ'ₙ` are
universal polynomials in the Weierstrass coefficients, hence commute with any ring
homomorphism applied to those coefficients.

Sources agree on the standard form: yes — the *fact* is textbook folklore (Silverman
AEC, Ch. III; the EDS recurrence of Ward/Stange is manifestly functorial). The
*name* `preΨ'` and the precise lemma `map_preΨ'` are **mathlib's own** (David
Kurniadi Angdinata's division-polynomial development), not external literature.

Most general standard form: stated for an arbitrary ring homomorphism `f : R →+* S`
between commutative rings, all `n`. That is already the form here.

Generality dimensions where the literature varies: essentially none — the recurrence
defining `preNormEDS'` lives over any commutative ring, and naturality is
homomorphism-level. There is no "more general" base object than an arbitrary
`CommRing` ring-hom for this statement.

Disagreement with the literature: none.

---

### Generality analysis — `WeierstrassCurve.map_preΨ'`

Literature-standard form (from Phase 3): naturality of `preΨ'ₙ` under an arbitrary
`CommRing` homomorphism `f : R →+* S`.

| # | Parameter / hypothesis      | Current Lean form            | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|------------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`, `[CommRing S]` | comm rings                 | comm rings                   | NO                  | Weierstrass curves and the `bᵢ`/division-polynomial recurrence are defined over `CommRing`; this is mathlib's base typeclass for the whole theory |
| 2 | `(f : R →+* S)`             | ring homomorphism            | ring homomorphism            | NO                  | naturality is exactly a statement about a ring hom; nothing weaker makes sense |
| 3 | `(n : ℕ)`                   | natural-number index         | natural-number index         | NO                  | `preΨ'` is indexed by ℕ by definition (`preΨ` is the ℤ-extension; a separate lemma `map_preΨ` already covers it) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Proposed restatement: none.
Cost of restatement: n/a.

The lemma is already at the maximal generality the concept admits (arbitrary
`CommRing` ring-hom). This is unsurprising — it **is** the mathlib lemma.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclasses/instances?                                | no       | — | already typeclass-driven (`CommRing`); `f` is genuinely data |
|  2 | sequences/metric → filters/topology?                                     | no       | — | purely algebraic; no analytic content |
|  3 | construction → universal-property class?                                 | no       | — | `preΨ'` is a concrete polynomial; naturality is the right statement |
|  4 | set-with-closure → bundled substructure?                                 | no       | — | n/a |
|  5 | vector-space/field-specific → weaken typeclass?                          | no       | — | already at `CommRing` |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | a single commutation equation |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure?                   | no       | — | the ℕ index is intrinsic; the ℤ version is the sibling `map_preΨ` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
Reason: this is mathlib's own already-idiomatic `map_`-naturality lemma; it is the
canonical contemporary form. Indeed the *upstream* lemma is the idiom we'd target.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. No definitional equalities, no typeclass-search
paths introduced. Skipped.

---

### Mathlib search-status: `WeierstrassCurve.map_preΨ'`

[A] Lean-Finder        "division polynomial map ring hom" / "preΨ base change"   → resolves to the mathlib decl (not separately run; superseded by [D] direct hit)
[B] Loogle             `(WeierstrassCurve.preΨ' (WeierstrassCurve.map _ _) _) = Polynomial.map _ _`  → would match `WeierstrassCurve.map_preΨ'`
[C] LeanSearch         "the n-th pre division polynomial commutes with base change of a Weierstrass curve"  → `WeierstrassCurve.map_preΨ'`
[D] Grep mathlib src   `grep "map_preΨ'" .lake/packages/mathlib/.../DivisionPolynomial/Basic.lean`  → **HIT, line 514** (exact name)
[E] Name pattern       `WeierstrassCurve.map_preΨ'`  → exact qualified-name hit in mathlib

Searched for both:
  - the user's current form  → found verbatim
  - the literature-standard form  → identical (no more-general form to find; this is already it)

**Direct evidence (grep, `.lake/packages/mathlib/.../DivisionPolynomial/Basic.lean`):**

```
513  @[simp]
514  lemma map_preΨ' (n : ℕ) : (W.map f).preΨ' n = (W.preΨ' n).map f := by
515    simp [preΨ', ← coe_mapRingHom]
```

Namespace context in mathlib (Basic.lean ≈ lines 489–515): `namespace WeierstrassCurve`
→ `section Map` → `variable (f : R →+* S)`. Identical scoping to the project file
(`namespace WeierstrassCurve` line 27 → `section Map` line 412 → `variable (f : R →+* S)`
line 418). Fully-qualified name in both: **`WeierstrassCurve.map_preΨ'`**.

Mathlib pin: `leanprover/lean4:v4.32.0-rc1`, mathlib `09b373d` (2026-06-21) — current.

Concluded: **"found in mathlib as `WeierstrassCurve.map_preΨ'`; identical form."**

---

### Call sites — `WeierstrassCurve.map_preΨ'`

Internal use count: **1** (within NagellLutz, excluding the declaring file's own line 437).

External-to-file callers: 1 file is itself — the single use is in the *same* file
(`baseChange_preΨ'`, line 489), so external-to-file = 0.

| Caller file:line                                              | Usage pattern (one-line excerpt) |
|--------------------------------------------------------------|----------------------------------|
| projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:489   | `rw [← map_preΨ', map_baseChange]` (inside `baseChange_preΨ'`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `map_preΨ'`?):
  - (none) — no inline re-derivation found anywhere in `projects/`.

Composability reading: the single in-file consumer (`baseChange_preΨ'`) is itself a
verbatim copy of mathlib's `baseChange_preΨ'`. So the *entire* dependency chain
(`preΨ'` → `map_preΨ'` → `baseChange_preΨ'`) is forked wholesale from the mathlib
file; nothing in the project consumes `map_preΨ'` in a way that diverges from
upstream. The lemma is part of a copied block, not project-original API.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.map_preΨ'` be derived from mathlib in ≤3 chained calls?

Attempt 1: It need not be *derived* at all — the **identical lemma already exists**
in mathlib as `WeierstrassCurve.map_preΨ'`. If one instead wanted to re-prove the
*concept* from the mathlib EDS primitive, it is a one-liner:
  - `simp [preΨ', WeierstrassCurve.map_Ψ₂Sq, WeierstrassCurve.map_Ψ₃,
    WeierstrassCurve.map_preΨ₄, ← WeierstrassCurve.coe_mapRingHom]`
    reducing through `EllipticDivisibilitySequence.map_preNormEDS'`.
  - Mathlib decls used: `WeierstrassCurve.preΨ'` (def), `map_preNormEDS'`,
    `coe_mapRingHom`, `map_Ψ₂Sq`/`map_Ψ₃`/`map_preΨ₄`.
  - Result: succeeds (it's mathlib's own proof).

Conclusion: **NOT-COMPOSABLE in the "new lemma" sense — because there is nothing to
compose: the lemma is already in mathlib verbatim.** The relevant bucket is
NO-mathlib-has-it, not NO-composable-from-mathlib.

---

## Verdict: `WeierstrassCurve.map_preΨ'`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): the fact is textbook naturality (Silverman AEC III);
  the *name* `preΨ'`/`map_preΨ'` is mathlib's own (Angdinata division-polynomial library).
- Generality analysis (Phase 4): MAXIMALLY GENERAL — arbitrary `CommRing` ring-hom; 0 weakenings; no modern-idiom move (it *is* the idiom).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_preΨ'`; **identical form** (Basic.lean:514).
- Composition check (Phase 6): nothing to compose — the lemma is upstream verbatim.

**Rationale:**

The NagellLutz project's `DivisionPolynomial.lean` is, by its own module docstring,
a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. The
copy exists for one narrow infrastructure reason: the project also forks
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (into
`LutzNagell.EllipticDivisibilitySequence`) and both files define `normEDS`,
`complEDS`, etc. — so the division-polynomial file is re-imported against the forked
EDS to dodge the name clash. `map_preΨ'` is one line of that copied block. It is
**identical** to the mathlib lemma in name, namespace (`WeierstrassCurve`), section
(`Map`), signature (`(n : ℕ) : (W.map f).preΨ' n = (W.preΨ' n).map f`), `@[simp]`
attribute, and proof shape; the sole textual delta is one extra simp lemma
(`map_preNormEDS'`) in the project's `simp` set, present only because the project's
`preΨ'` routes through its forked `preNormEDS'`.

Mathlib has it. There is no contribution here: the right action is not to upstream
`map_preΨ'` (it is already upstream) but to **collapse the fork** so the project
reuses the mathlib declaration directly.

**WHY not (refactor-actionable detail):**
Mathlib already has `WeierstrassCurve.map_preΨ'` at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:514`, with the
identical statement and `@[simp]` status. The project's copy is a duplicate created
solely to avoid the EDS name clash. The user's form does not merely *follow from* the
mathlib decl — it **is** the mathlib decl.

Existing mathlib decl:        `WeierstrassCurve.map_preΨ'`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:514`
Our form follows in ≤1 line (it is literally the same statement):
```lean
example {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (f : R →+* S) (n : ℕ) : (W.map f).preΨ' n = (W.preΨ' n).map f :=
  WeierstrassCurve.map_preΨ' f n   -- mathlib's lemma, verbatim
```
Call sites in our project (from Phase 6.0):  K = 1 (`baseChange_preΨ'`, same file, line 489).

Refactor plan (project-level, not a single-decl edit):
1. The proper fix is to **delete the entire forked `DivisionPolynomial.lean` block**
   (and the forked `EllipticDivisibilitySequence.lean`) and depend on mathlib
   directly — once the name-clash that motivated the fork is resolved. The clash is
   `normEDS`/`complEDS` etc. being defined in *both* the project's EDS file and
   mathlib's; that is the real ticket. `map_preΨ'` is collateral, not the root.
2. Until the fork is dissolved, the single in-file consumer `baseChange_preΨ'`
   (line 489) needs `map_preΨ'` to exist in *this* namespace — so within the forked
   file the lemma must stay. **This is therefore a project-structure dedup, not a
   call-site swap:** you cannot point line 489 at `Mathlib...map_preΨ'` while
   `preΨ'` itself is the forked `preΨ'` (the two `preΨ'`s are different definitions
   living in the same `WeierstrassCurve` namespace but built on different EDS).
3. Concretely for the cleanup fleet: file a **dedup ticket** against NagellLutz to
   "eliminate the `EllipticDivisibilitySequence` / `DivisionPolynomial` mathlib fork —
   reconcile the duplicated `normEDS`/`complEDS`/`preNormEDS'` names with upstream so
   the whole forked tree (including `map_preΨ'`) can be dropped in favour of
   `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`." Resolving the
   parent fork removes `map_preΨ'` for free.

Next action: do **not** open a mathlib PR for `map_preΨ'` (mathlib has it). Instead
treat this as a fork-dedup: file the project ticket above; the decl disappears when
the EDS fork is reconciled with upstream.

---

## Next step

Do not upstream. File a NagellLutz dedup ticket to reconcile the forked
`EllipticDivisibilitySequence` / `DivisionPolynomial` modules with mathlib (the
`normEDS`/`complEDS` name-clash is the root cause); `WeierstrassCurve.map_preΨ'` —
which already exists verbatim in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:514` — is
removed automatically once the fork is dissolved.
