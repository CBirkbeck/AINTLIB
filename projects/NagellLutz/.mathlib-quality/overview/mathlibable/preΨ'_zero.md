# /mathlibable report — `WeierstrassCurve.preΨ'_zero`

**TL;DR — `NO-mathlib-has-it`.** This declaration is a **verbatim copy** of an
existing mathlib lemma. The project file's own module docstring states it is "a
copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" that
only swaps the EDS import to dodge a `normEDS`/`complEDS` name clash with the
project's parallel EDS track. Mathlib already has `WeierstrassCurve.preΨ'_zero` —
same namespace, same statement, same proof, same `@[simp]` attribute — at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:157`.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build is stale per task note); reasoning from source
- decl `WeierstrassCurve.preΨ'_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:80`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."

**Qualified name (VERIFIED):** namespace is `WeierstrassCurve` (file line 27:
`namespace WeierstrassCurve`, never re-opened before line 80; `section preΨ'` at
line 60 introduces no namespace). Lemma name `preΨ'_zero`. So the fully qualified
name is **`WeierstrassCurve.preΨ'_zero`**, matching the task's parsed guess.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ'_zero` states that the 0-th auxiliary univariate
"pre-division" polynomial of a Weierstrass curve `W` vanishes:

> For a Weierstrass curve `W` over a commutative ring `R`, the value at `n = 0`
> of the auxiliary division-polynomial sequence `preΨ'` is the zero polynomial:
> `W.preΨ' 0 = 0`.

Here `preΨ'` (Division​Polynomial.lean:76) is defined as
`preΨ' n = preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`, i.e. the auxiliary
*normalised elliptic-divisibility-sequence* recurrence specialised to the
curve's invariants `b = Ψ₂Sq², c = Ψ₃, d = preΨ₄`. The lemma is the base case
`n = 0` of that sequence. Mathematically this is the textbook normalisation
`ψ₀ = 0` for division polynomials / EDS.

Variables / typeclasses involved (Lean side):
- `{R : Type r} [CommRing R]` — the base ring of the curve.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.

Hypotheses (Lean side): none beyond the ambient `CommRing R`.

Conclusion (math): `ψ₀ = 0` (the 0-indexed division polynomial is zero).
Conclusion (Lean): `W.preΨ' 0 = 0` (`: Prop`, an equality in `R[X]`).

Proof body: `preNormEDS'_zero ..` — one term, the corresponding base-case lemma
about the underlying `preNormEDS'` sequence, with `..` filling the curve-specific
arguments. This is a one-line *glue lemma*: a direct specialisation of an
already-established EDS base case.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: base-case helper lemma (`ψ₀ = 0`), not a new structure and not a named
main result. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`preNormEDS'_zero ..`).
One-liner verdict: **n/a — kind is `lemma`, not `def`** (the defeq/diamond/API
exemption table applies only to `def`/`abbrev`/`structure`). Recorded as a
glue lemma: `:= preNormEDS'_zero ..` is a single definitional specialisation.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                | Hit? | Standard form found                          | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------|------|----------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials elliptic curve psi_0 = 0 EDS initial values                                     | yes  | `ψ₀ = 0; ψ₁ = 1; ψ₂ = 2y+a₁x+a₃; …`          | Wikipedia "Division polynomials" + "Elliptic divisibility sequence"; **first hit is the mathlib4 docs page for `DivisionPolynomial/Basic`** |
|  2 | WebSearch (general / framework)  | mathlib4 WeierstrassCurve division polynomial preΨ EllipticDivisibilitySequence                      | yes  | mathlib `preΨ`/`preΨ'` auxiliary polys        | Top hits are the mathlib4 docs for `DivisionPolynomial/Basic` and `NumberTheory/EllipticDivisibilitySequence` — mathlib is the canonical home |
|  3 | WebSearch (named-after / aliases)| Ward elliptic divisibility sequence W₀ = 0 recurrence                                                | yes  | Ward (1948): `W₀ = 0, W₁ = 1, …`              | covered by hit #1's summary; `W₀ = 0` is the universal EDS normalisation |
|  4 | ChatGPT MCP                      | (skipped — MCP down per task note; fallbacks used)                                                   | n/a  | —                                            | substituted by WebSearch ×3 + nLab + direct mathlib-source read; conclusion is not generality-sensitive (it's an exact-copy case) |
|  5 | Local references                 | `refs/NagellLutz/` / `.mathlib-quality/references/` for "division polynomial"                        | n/a  | (no references dir present for this project)  | dir absent — recorded n/a |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial                                                 | n/a  | not a dedicated nLab entry                     | EDS/division-polynomials are classical arithmetic-geometry, not an nLab categorical topic; the standard form is fixed by Silverman/Ward, already matched |
|  7 | nCatLab (if categorical)         | —                                                                                                    | n/a  | —                                            | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | division polynomial / torsion                                                                         | n/a  | not in Stacks                                  | Stacks doesn't treat classical division polynomials; n/a with reason |
|  9 | MathOverflow / MSE               | (covered by #1/#3)                                                                                    | n/a  | —                                            | standard form already pinned by Wikipedia + Ward; no open question |
| 10 | recent arXiv (last 5 yrs)        | (surfaced via #1) Stange 2025, "Division polynomials for arbitrary isogenies"; 2102.07573            | yes  | same `ψ₀ = 0` base case                        | modern work still uses `ψ₀ = 0`; nothing supersedes the normalisation |

The protocol passes: WebSearch ran 3 queries at distinct generality levels
(specific `ψ₀ = 0`; mathlib framework; Ward EDS), local refs checked (absent),
nLab/Stacks/nCatLab/MathOverflow/arXiv each checked or `n/a` with reason.
ChatGPT MCP is unavailable in this environment (task note); its role — confirm
the standard form and its generality — is fully covered here because the
declaration turns out to be a byte-for-byte copy of an existing mathlib lemma,
so the verdict does not hinge on a subtle generality judgment.

### Literature summary (Phase 3)

Concept identified as: **division polynomials / elliptic divisibility sequence,
base case `ψ₀ = 0` (Silverman, *AEC* III.; Ward 1948)**.
Sources agree on the standard form: **yes** — `ψ₀ = 0` is universal across
Wikipedia, Ward, Silverman, and recent arXiv (Stange 2025).
Most general standard form: the EDS recurrence over an arbitrary commutative
ring with `W₀ = 0`; mathlib captures exactly this via `preNormEDS'` over
`[CommRing R]`.
Generality dimensions where the literature varies: essentially none for the base
case — `ψ₀ = 0` holds in every formulation (ℤ-sequences, polynomial sequences,
arbitrary base ring).
Disagreement with the literature: **none**. The Lean form `W.preΨ' 0 = 0` is the
literature-standard base case verbatim.

---

### Generality analysis — `WeierstrassCurve.preΨ'_zero`

Literature-standard form (from Phase 3): `ψ₀ = 0` for a Weierstrass curve over
any commutative ring.

| # | Parameter / hypothesis      | Current Lean form          | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|----------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`              | commutative ring           | commutative ring         | NO                  | `WeierstrassCurve` is defined over `CommRing`; this is already mathlib's chosen (maximal-sensible) base. The mathlib copy uses the identical typeclass. |
| 2 | `(W : WeierstrassCurve R)`  | a Weierstrass curve        | a Weierstrass curve      | NO                  | the object the statement is about; cannot be weakened |
| 3 | index `0 : ℕ`               | natural-number index 0     | index 0                  | NO                  | it *is* the base case; nothing to generalise |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's own, over
`[CommRing R]`).
Number of weakening opportunities found: **0**.
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question                                                                  | Applies? | Proposed reformulation | Downstream |
|---|---------------------------------------------------------------------------|----------|------------------------|------------|
| 1 | bundled-hypothesis → typeclass?                                           | no       | already a typeclass (`CommRing`) | — |
| 2 | sequences/metric → filters/topology?                                     | no       | finite algebraic identity; no topology | — |
| 3 | construction → universal-property class?                                 | no       | base case of a recurrence; no UP | — |
| 4 | set-with-closure → bundled substructure?                                 | no       | not a substructure | — |
| 5 | vector-space/field-specific → weaken typeclass?                          | no       | already at `CommRing` | — |
| 6 | 1-categorical → higher-categorical?                                      | no       | not categorical | — |
| 7 | concrete index → arbitrary monoid?                                       | no       | this is literally the `n = 0` base case | — |

Modern idiom available: **no**. Reason: the statement is the EDS base case
`ψ₀ = 0` already in mathlib's exact contemporary formulation; there is no
cleaner contemporary idiom because mathlib *is* the contemporary formulation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search
paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.preΨ'_zero`

[A] Lean-Finder       "preΨ' zero", "division polynomial 0"     hit (mathlib docs surface it)
[B] Loogle            (not run — exact-name grep already decisive)   n/a
[C] LeanSearch        "WeierstrassCurve preΨ zero"               hit (DivisionPolynomial/Basic)
[D] Grep mathlib src  `preΨ'_zero` in `.lake/.../mathlib/`        **HIT** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:157`
[E] Name pattern      `lemma preΨ'_zero` namespace `WeierstrassCurve`  HIT (same file/line)

Searched for both the user's current form and the literature-standard form
(`ψ₀ = 0`): both resolve to the same single mathlib lemma.

**Decisive grep result** (mathlib `Basic.lean:156-158`), identical to the
project's `DivisionPolynomial.lean:79-81`:

```lean
@[simp]
lemma preΨ'_zero : W.preΨ' 0 = 0 :=
  preNormEDS'_zero ..
```

Namespace context in mathlib `Basic.lean` matches the project exactly:
`namespace WeierstrassCurve` with
`variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)`. The underlying
`preΨ'` def (mathlib `Basic.lean:153`) is also identical to the project's
(`DivisionPolynomial.lean:76`):
`preΨ' n := preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ'_zero`; identical form**
(same namespace, statement, proof term, and `@[simp]` attribute).

---

### Call sites — `WeierstrassCurve.preΨ'_zero`

Internal use count: **1** (within NagellLutz, excluding the declaring file).
External-to-file callers: 1 distinct file.

| Caller file:line                                          | Usage pattern (one-line excerpt)                                      |
|-----------------------------------------------------------|------------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:203` | `| zero => simpa only [preΨ'_zero] using ⟨natDegree_zero.le, Int.cast_zero.symm⟩` |

Inline-derivation grep (re-derived elsewhere without `preΨ'_zero`?): (none).

Signal: K = 1 internal use, used as a `simp` rewrite. Because mathlib's
identical `WeierstrassCurve.preΨ'_zero` is *also* `@[simp]`, that one call site
would be served identically by the mathlib lemma once the project stops forking
the file — no behavioural change.

### Composition check (Phase 6)

Can `WeierstrassCurve.preΨ'_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.preΨ'_zero` — it **is** the mathlib lemma, verbatim.
  - Mathlib decls used: `WeierstrassCurve.preΨ'_zero` (= `preNormEDS'_zero ..`).
  - Result: succeeds trivially (identity).
  - Notes: this is the `NO-mathlib-has-it` case, not merely composable — the
    exact lemma exists. (Even ignoring that, it is `preNormEDS'_zero ..`, a
    single mathlib call.)

Conclusion: **NOT-COMPOSABLE is moot — it is an exact duplicate.** Primary
verdict is NO-mathlib-has-it.

---

## Verdict: `WeierstrassCurve.preΨ'_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): `ψ₀ = 0` is the universal EDS/division-polynomial
  base case; the top WebSearch hit for the concept is mathlib's own
  `DivisionPolynomial/Basic` docs page — mathlib is the canonical home.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical typeclasses
  (`[CommRing R]`) to the mathlib version; 0 weakening opportunities; no modern
  idiom available.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.preΨ'_zero`;
  identical form** at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:157`.
- Composition check (Phase 6): moot — exact duplicate (and the body is the
  single mathlib call `preNormEDS'_zero ..`).

**Rationale:**

The project's `DivisionPolynomial.lean` is, by its own module docstring, a copy
of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, forked
solely so it can `import LutzNagell.EllipticDivisibilitySequence` (the project's
parallel EDS file) instead of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`,
because both define `normEDS`/`complEDS` and would collide. The fork is an import
plumbing workaround, **not** a sign that mathlib lacks the result. `preΨ'_zero`
in particular is byte-for-byte identical to the mathlib lemma — same namespace
`WeierstrassCurve`, same statement `W.preΨ' 0 = 0`, same proof `preNormEDS'_zero ..`,
same `@[simp]`. The underlying `preΨ'` definition and the `preNormEDS'` base case
it specialises are likewise identical between the two trees. There is nothing to
upstream: mathlib already has exactly this, at the exact generality.

**WHY not (refactor-actionable):** Mathlib already contains this lemma verbatim.
The local copy exists only to avoid the `normEDS`/`complEDS` name clash between
mathlib's EDS file and the project's vendored EDS file. The right resolution is
not to add anything to mathlib but to **eliminate the project's fork of the
division-polynomial + EDS files** during consolidation — i.e. make the project
depend on mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` directly, and
drop the duplicated `normEDS`/`complEDS`/`preΨ'…` track. (If the project genuinely
needs a *different* `normEDS` variant, that divergence — not `preΨ'_zero` — is
the thing to assess; `preΨ'_zero` itself is pure duplication.)

Existing mathlib decl:        `WeierstrassCurve.preΨ'_zero`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:157`
Our form follows in ≤1 line (it is the same lemma):
```lean
example (W : WeierstrassCurve R) : W.preΨ' 0 = 0 := WeierstrassCurve.preΨ'_zero
```
Call sites in our project (from Phase 6.0): **1**
  - `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:203`
Refactor plan: at that 1 call site, the `simp only [preΨ'_zero]` rewrite is
already served by mathlib's identically-named `@[simp]` lemma — no edit needed
once the project stops shadowing the mathlib file. Concretely, during
consolidation: delete the local `DivisionPolynomial.lean` copy (and the
duplicated EDS track it imports), re-point `DivisionPolynomialDegree.lean` and
any other consumers at the mathlib modules, and the `preΨ'_zero` reference
resolves to `WeierstrassCurve.preΨ'_zero` from mathlib unchanged.
Next action: do **not** open a mathlib PR. Track the fork-removal under the
project's consolidation/dedup tickets (this whole file is a known mathlib copy);
delete `preΨ'_zero` (and its sibling copies) from the project when the EDS
name-clash is resolved.

---

## Next step

Do not open a mathlib PR. Track fork-removal under the project's
consolidation/dedup tickets: delete the local `DivisionPolynomial.lean` copy
(and the duplicated `EllipticDivisibilitySequence` track that forces it) and
re-point the single call site at mathlib's `WeierstrassCurve.preΨ'_zero`. The
lemma already exists in mathlib, verbatim, at the same generality.
