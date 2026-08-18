# /mathlibable report — `WeierstrassCurve.preΨ`

> Step-9 mathlibable assessment for the NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences).
> Mode A, single declaration. Literature width: EXHAUSTIVE.

## Baseline (Phase 0)

- lake build:               not run (local build stale per task brief); reasoning from source
- decl `WeierstrassCurve.preΨ`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:117`
- kind:                      `noncomputable def`
- has sorry:                 no
- module docstring summary:  "This is a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
  `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
  name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for
  full documentation."

The file's own header **declares itself a verbatim copy** of the mathlib module. This is
the decisive context for the whole assessment.

## Statement (Phase 1)

`WeierstrassCurve.preΨ` is a **definition**. For a Weierstrass curve `W` over a commutative
ring `R`, it defines the family of univariate "pre-ψ" polynomials `preΨₙ ∈ R[X]` indexed by
`n ∈ ℤ`. These are the auxiliary polynomials underlying the elliptic **division polynomials**
`ψₙ`: for odd `n`, `Ψₙ = preΨₙ`; for even `n`, `Ψₙ = preΨₙ · ψ₂`. They are produced by feeding
the curve-specific seed data into the abstract normalised elliptic divisibility sequence
recurrence.

Lean definition (verbatim):

```lean
noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

Variables / typeclasses involved (Lean side):
- `{R : Type r} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (dot-notation receiver).
- `(n : ℤ)` — the index.

Hypotheses: none.

Conclusion (math): the value of the normalised EDS attached to `W` (with parameters
`b = Ψ₂Sq²`, `c = Ψ₃`, `d = preΨ₄`) at index `n`, landing in `R[X]`.

Conclusion (Lean): `R[X]` (i.e. `Polynomial R`) — it is a definition, not a proposition.

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a named mathematical construction (the family of division-polynomial
auxiliaries `preΨₙ`) — a `def` of a named concept central to elliptic-curve arithmetic.
(Literature width is EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Body line count: 1 substantive line (`preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | yes      | The whole `DivisionPolynomial` API (`preΨ_even`, `preΨ_odd`, `preΨ_neg`, `map_preΨ`, degree/leading-coeff lemmas) is stated against the *name* `preΨ`, not the unfolded `preNormEDS …`; the sealed name is the API barrier. |
| Avoid typeclass diamonds          | no       | No instance is produced; no competing `Mul`/`Zero` path. |
| Mark semantic intent / API name   | yes      | `preΨ` is the public anchor consumed by ≥6 files (degree theory, `Φ`/`ΨSq`, the Nagell–Lutz prime-order bridge). |

Conclusion: **ONE-LINER WITH-EXEMPTION** — but this is moot: the def is a *copy of an
existing mathlib def*, so the verdict is governed by Phase 5, not Phase 2b.

## Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                           | Query | Hit? | Standard form found | Notes |
|----|-----------------------------------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form)          | "division polynomials elliptic curve psi_n recurrence definition standard" | yes | `ψ₀=0, ψ₁=1, ψ₂=2y, ψ₃=…, ψ₄=…`, with `ψ_{2m+1}=ψ_{m+2}ψ_m³−ψ_{m−1}ψ_{m+1}³` and the even analogue | Standard division-polynomial recurrence; matches mathlib's `preNormEDS'_odd`/`_even` exactly (up to the `ψ₂` normalisation that `preΨ` factors out). |
| 2 | WebSearch (general form)           | "elliptic divisibility sequence" normalised EDS recurrence Ward division polynomial | yes | EDS `h_{m+n}h_{m−n}=h_{m+1}h_{m−1}h_n²−h_{n+1}h_{n−1}h_m²`; normalised: `D₀=0, D₁=1` | Ward (1948); the abstract sequence mathlib calls `normEDS`/`preNormEDS`. One returned result **is the mathlib doc page** `Mathlib.NumberTheory.EllipticDivisibilitySequence`. |
| 3 | WebSearch (aliases / named-after)  | (covered by #2 — "Ward", "normalised", "division polynomial") | yes | "Ward's division polynomials"; `ψ_n(z,L)=σ(nz,L)/σ(z,L)^{n²}` | Confirms the same object across naming conventions. |
| 4 | ChatGPT MCP                        | — | n/a | — | MCP down per task brief; substituted by extra WebSearch generality levels (#1–#3) which already pinned the standard form and its history (Ward 1940s → modern division-polynomial treatment). |
| 5 | Local references                   | grep `.mathlib-quality/references/` | n/a | — | No `references/` directory in this project; no source PDFs present. |
| 6 | nLab                               | "division polynomial" / "elliptic divisibility sequence" | n/a | — | Not an nLab-style categorical concept; the arithmetic/recurrence literature (Silverman, Ward) is the right corpus and is covered by #1–#3. |
| 7 | nCatLab                            | — | n/a | — | Not a categorical concept. |
| 8 | Stacks Project                     | — | n/a | — | Division polynomials of a fixed Weierstrass model are not a Stacks-style scheme-theoretic topic. |
| 9 | MathOverflow / MSE                 | (subsumed by #1–#3 arXiv/Wikipedia hits) | yes | same recurrence | arXiv:2102.07573 "A recurrence relation for elliptic divisibility sequences"; Wikipedia "Elliptic divisibility sequence". |
| 10 | recent arXiv (≤5 yrs)             | "division polynomials arbitrary isogenies", "recurrence relation EDS" | yes | arXiv:2503.15428, arXiv:2102.07573 | Active area; the `preΨ`/EDS formulation is exactly the contemporary standard. |

### Literature summary (Phase 3)

Concept identified as: **division polynomials of an elliptic/Weierstrass curve** (`ψₙ`), with
the `preΨₙ` "pre-normalised" auxiliaries arising from the **normalised elliptic divisibility
sequence** (Ward) recurrence.
Sources agree on the standard form: **yes**. The `preΨ` construction (strip the `ψ₂` factor,
run the EDS recurrence over the polynomial ring) is exactly how mathlib and the literature
organise it.
Most general standard form: the recurrence is purely algebraic over any commutative ring,
which is precisely mathlib's `preNormEDS : R → R → R → ℤ → R` instantiated at `R := R[X]`.
Generality dimensions where the literature varies: classically stated over `ℂ`/`ℚ`/number
fields (Ward, Silverman); mathlib (and this copy) already take the maximally-general
**arbitrary `CommRing R`** route — strictly more general than the literature.
Disagreement with the literature: none.

## Generality analysis — `WeierstrassCurve.preΨ` (Phase 4)

Literature-standard form: division polynomials over a field / number ring. Mathlib's form
(which this copies) is over an arbitrary `CommRing`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | arbitrary comm. ring | field / number ring  | NO | Already maximally general; the EDS recurrence is integral, so `CommRing` is the right home. Can't weaken below `CommRing` (needs `+`, `*`, `-`, the `Ψ₂Sq²/Ψ₃/preΨ₄` seeds). |
| 2 | `(n : ℤ)`              | integer index      | `n ≥ 0` then extended    | NO | The ℤ-indexed `preNormEDS` (sign-extended) is the canonical mathlib form; matching it is correct. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's already-maximal form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | "let X be a foo" → typeclass? | no | — | Already dot-notation on the bundled `WeierstrassCurve`. |
| 2 | sequences/metric → filters/topology? | no | — | Purely algebraic recurrence; no analysis. |
| 3 | construct → universal-property class? | no | — | A division polynomial is an explicit construction; no universal property to abstract. |
| 4 | set+closure → bundled substructure? | no | — | Not a substructure. |
| 5 | vector-space/field → module/ring weakening? | no | — | Already over arbitrary `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general monoid? | no | — | `ℤ` is intrinsic (EDS are ℤ-indexed and use `n.sign`/`n.natAbs`). |

Modern-idiom verdict: **no** — the construction already *is* the contemporary mathlib idiom
(it is literally the mathlib definition). No organisational improvement available.

## Diamond / defeq risk — `WeierstrassCurve.preΨ` (Phase 4.5)

Kind is `def`, so the phase runs. But the def already lives in mathlib unchanged, so any risk
is one mathlib already accepts.

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | Produces a `Polynomial R` value, not an instance. |
| 2 | Reducibility leak | none | Not `@[reducible]`; sealed `noncomputable def`. |
| 3 | Non-canonical unfolding | low | Unfolds to `preNormEDS …`; the curated `simp` lemmas (`preΨ_zero/one/two/…`) are the intended rewrite surface — mathlib's existing design. |
| 4 | Instance priority collision | none | Not an instance. |
| 5 | Universe-polymorphism | none | `R : Type r`; no forced annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

Risk verdict: **NONE/LOW** — and identical to the risk profile mathlib already carries.

## Mathlib search-status: `WeierstrassCurve.preΨ` (Phase 5)

[A] Lean-Finder       — (index tools not run live; build stale) — n/a
[B] Loogle            — n/a (build stale) — superseded by authoritative source grep below
[C] LeanSearch        — corroborating signal: WebSearch returned the mathlib doc page
    `Mathlib.NumberTheory.EllipticDivisibilitySequence` for the EDS query (Phase 3 #2)
[D] **Grep mathlib src** — `grep 'noncomputable def preΨ (' ` over
    `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
    → **HIT at line 194**:
    ```lean
    noncomputable def preΨ (n : ℤ) : R[X] :=
      preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
    ```
    Character-for-character identical body, signature, namespace (`WeierstrassCurve`), and
    docstring. The dependency `preNormEDS` is also mathlib's, at
    `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:176`.
[E] Name pattern      — `preΨ`, `preΨ'`, `preΨ₄`, `Ψ₃`, `Ψ₂Sq` all present in the mathlib
    `DivisionPolynomial/Basic.lean` with the same definitions.

Searched for both the current form and the literature-standard (general) form.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:194`); identical form.**
The project file is an intentional fork (its header says so), forked only so it can import the
project's local `EllipticDivisibilitySequence` copy and dodge a `normEDS`/`complEDS` name clash.

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.preΨ`

Internal use count: **K ≫ 3** (heavily used). External-to-declaring-file callers: ≥6 files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/DivisionPolynomialDegree.lean:269` | `(W.preΨ n).natDegree ≤ …` |
| `LutzNagell/DivisionPolynomialDegree.lean:276,287,296,300,309` | coeff / natDegree / leadingCoeff of `W.preΨ n` |
| `LutzNagell/DivisionPolynomialDegree.lean:312` | `preΨ_ne_zero … : W.preΨ n ≠ 0` |
| `LutzNagell/DivisionPolynomial.lean:441` | `map_preΨ : (W.map f).preΨ n = (W.preΨ n).map f` |
| `LutzNagell/DivisionPolynomial.lean:491` | `baseChange_preΨ` |
| `LutzNagell/.../PIDPrimeOrder.lean:122–127` | `(curveK R K W).preΨ p`, squarefree leading coeff (Nagell–Lutz core) |
| `LutzNagell/.../GeneralPrimeOrder.lean:89–97` | `(curveQ W).preΨ p`, leading coeff `= p` |
| `LutzNagell/.../EvalBridge.lean:63,69` | `(W.Ψ n).evalEval x y = (W.preΨ n).eval x` |

Inline-derivation grep: the consumers depend on the `preΨ` API surface (degree, leading
coefficient, `eval`/`map` bridges) — none re-derive the recurrence inline. This is real,
load-bearing API. **But the API it duplicates is mathlib's own**, so the high call count
argues for *re-pointing the fork at mathlib*, not for upstreaming.

### Composition check

Can `preΨ` be derived from mathlib in ≤3 calls? It is not a "compose at call site" situation —
it is a named construction. But the relevant fact is stronger than composability:

Attempt 1: `WeierstrassCurve.preΨ` already exists in mathlib verbatim.
  - Mathlib decls used: `WeierstrassCurve.preΨ` itself (Basic.lean:194), built on
    `Mathlib.NumberTheory.preNormEDS`.
  - Result: **succeeds trivially** — it is the same declaration.

Conclusion: **NOT-COMPOSABLE in the "inline 3 mathlib calls" sense, because nothing to
compose — mathlib already provides the exact decl.** Routes to NO-mathlib-has-it.

## Verdict: `WeierstrassCurve.preΨ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): division polynomials / normalised EDS (Ward); the `preΨ`
  formulation is the contemporary standard, and one search hit is literally the mathlib EDS
  doc page.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's already-maximal
  `CommRing` form; no modern-idiom improvement (it *is* the idiom).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.preΨ`,
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:194`, identical form.
- Composition check (Phase 6): NOT-COMPOSABLE (nothing to compose — the exact decl already
  exists); K ≫ 3 internal call sites, all on the duplicated API.

**Rationale.**
`WeierstrassCurve.preΨ` in this project is a deliberate, self-documented **copy** of the
identically-named, identically-bodied mathlib declaration
`WeierstrassCurve.preΨ` (Basic.lean:194). The project header states the file "is a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked solely so it can
import the project's local `LutzNagell.EllipticDivisibilitySequence` instead of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and thereby avoid a `normEDS`/`complEDS`
name collision. The underlying recurrence (`preNormEDS`) is also mathlib's. There is nothing
new here mathematically or in Lean form: the literature standard, the maximal generality, and
the exact Lean spelling are all already in mathlib. Hence mathlib unambiguously **has it**.

**WHY not (refactor-actionable).**
Mathlib already contains this declaration verbatim. The project does not need to contribute it;
instead it should — once the local EDS fork is no longer required — drop the copy and import
the mathlib module directly.

  Existing mathlib decl:        `WeierstrassCurve.preΨ`
  Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:194`
  Our form follows in 0 lines (it is the same declaration):
  ```lean
  -- identical signature + body already in mathlib:
  noncomputable def preΨ (n : ℤ) : R[X] :=
    preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
  ```
  Call sites in our project (from Phase 6.0): K ≫ 3 (DivisionPolynomialDegree.lean,
  DivisionPolynomial.lean, PIDPrimeOrder.lean, GeneralPrimeOrder.lean, EvalBridge.lean).

  Refactor plan (consolidation-level, NOT a per-call-site swap — the name `preΨ` is already
  correct):
    1. The blocker is the **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`** in
       `LutzNagell/EllipticDivisibilitySequence.lean` (the `normEDS`/`complEDS` clash the
       header cites). Resolve that first — either delete the local EDS copy in favour of the
       mathlib one, or namespace it so it no longer collides.
    2. Once the local EDS import is gone, delete `LutzNagell/DivisionPolynomial.lean`'s copies
       of `preΨ` (and its siblings `preΨ'`, `preΨ₄`, `Ψ₃`, `Ψ₂Sq`, `ΨSq`, `Ψ`, `Φ`, …) and
       `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` instead.
    3. All K call sites use dot-notation `W.preΨ …` / `WeierstrassCurve.preΨ` / `map_preΨ`,
       which resolve **unchanged** against the mathlib decl (same name, same namespace, same
       signature, same simp-lemma names) — so no call-site edits are expected beyond the
       import swap. Re-point only the project-specific additions in
       `DivisionPolynomialDegree.lean` (e.g. `natDegree_preΨ_le`, `preΨ_ne_zero`) at the
       mathlib `preΨ`.

  Note: this whole `DivisionPolynomial*` track is a known fork (the task brief flags it, and
  the file header confirms it). `preΨ` is one representative decl in that fork; the same
  NO-mathlib-has-it verdict applies to the file's other copied division-polynomial decls. The
  genuine project-specific content lives in the *degree* lemmas
  (`DivisionPolynomialDegree.lean`) and the Nagell–Lutz bridges, not in `preΨ` itself.

  Next action: track de-duplication of the `DivisionPolynomial`/`EllipticDivisibilitySequence`
  fork against mathlib as a cleanup ticket (resolve the EDS name clash, then delete the copied
  defs and import mathlib). `preΨ` requires **no** upstreaming.

---

## Next step

Do not upstream. File/own a consolidation cleanup ticket to remove the
`DivisionPolynomial`/`EllipticDivisibilitySequence` fork: first eliminate the local EDS copy
(the `normEDS`/`complEDS` clash that motivated the fork), then delete the copied `preΨ` (and
sibling division-polynomial defs) and `import` mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` directly. Call sites use the
identical `preΨ` name/namespace and should need only the import swap.
