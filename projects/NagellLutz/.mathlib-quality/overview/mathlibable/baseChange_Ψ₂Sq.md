# /mathlibable report — `WeierstrassCurve.baseChange_Ψ₂Sq`

## Verdict (one line)

**NO-mathlib-has-it** — the lemma exists in mathlib **verbatim** (same qualified
name, same statement, same proof) at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:556`. The
project file is an explicit, acknowledged fork of that mathlib file.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoned from source + vendored mathlib in `.lake/packages/mathlib`.
- decl `WeierstrassCurve.baseChange_Ψ₂Sq`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:479` (NOT line 486 — line 486 is `baseChange_preΨ₄`; the task's line ref was off, but the named decl is unambiguous).
- qualified name:           `WeierstrassCurve.baseChange_Ψ₂Sq` (inside `namespace WeierstrassCurve`, `section BaseChange`; no intermediate namespace). The parenthetical guess in the task prompt is CORRECT.
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."

The header is a smoking gun: the entire file is a deliberate fork of the mathlib
file in which this lemma lives.

---

### Statement (Phase 1)

`WeierstrassCurve.baseChange_Ψ₂Sq` states a **naturality / base-change
compatibility** fact for the squared 2-division polynomial `Ψ₂Sq` of a
Weierstrass curve:

Let `R` be a commutative ring, `W` a Weierstrass curve over `R`, `S` an
`R`-algebra, and let `A`, `B` be `S`-algebras with a scalar tower `R → S → A`
and `R → S → B`. Given an `S`-algebra homomorphism `f : A →ₐ[S] B`, the
polynomial `Ψ₂Sq` of the base change of `W` to `B` equals the coefficient-wise
image under `f` of the `Ψ₂Sq` of the base change of `W` to `A`. In symbols, with
`Ψ₂Sq(W) = 4X³ + b₂X² + 2b₄X + b₆`, forming `Ψ₂Sq` commutes with base change /
applying a ring map to coefficients.

Variables / typeclasses (Lean side):
- `{R S} [CommRing R] [CommRing S]`, `W : WeierstrassCurve R` — the base curve.
- `[Algebra R S]`, `{A} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]` — first target algebra.
- `{B} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]` — second target algebra.
- `(f : A →ₐ[S] B)` — the algebra map along which we transport.

Hypotheses (Lean side): none beyond the typeclass context.

Conclusion (math): `Ψ₂Sq` is natural in the base ring (commutes with base change).

Conclusion (Lean): `(W.baseChange B).Ψ₂Sq = (W.baseChange A).Ψ₂Sq.map f`.

Proof body (2 rewrites): `rw [← map_Ψ₂Sq, map_baseChange]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a glue/naturality lemma about a previously-defined polynomial; not a new
structure, not a named theorem, not a `## Main results` entry. (Literature width
was still treated as exhaustive; see Phase 3.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner-def heuristic
does not apply. The body is a 2-step `rw` (a glue lemma in the
`/mathlibable` Mode-B sense: it is the base-change analog of the `simp`-tagged
`map_Ψ₂Sq`, composed with `map_baseChange`). Recorded for the verdict: this is a
thin naturality wrapper, exactly the kind of result whose verdict is inherited
from / pinned to the underlying `Ψ₂Sq` def and its `map_*` lemma.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" base change / "compatible with base change"     | yes  | division polynomials are universal polynomials in `a_i`; base change = apply the ring hom to coefficients | Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7; standard |
|  2 | WebSearch (general form)         | "2-division polynomial" `ψ₂` `4x³+b₂x²+2b₄x+b₆` functorial            | yes  | `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆`; coefficients are integer polynomials in the `b_i`, hence functorial in the base ring | this IS `Ψ₂Sq`; matches the mathlib/project def byte-for-byte |
|  3 | WebSearch (named-after / aliases)| "two-torsion polynomial" / "ψ₂ squared" elliptic curve base change    | yes  | same object; mathlib's `twoTorsionPolynomial.toPoly` is defeq (`Ψ₂Sq_eq` is `rfl`) | naming varies (`ψ₂²`, `Ψ₂Sq`, two-torsion poly), object is fixed |
|  4 | ChatGPT MCP                      | (MCP down per task env note — fallback to WebSearch + source) "standard generality of division-polynomial base-change compatibility, historical formulation" | n/a  | covered by #1–#3 + #6                                | MCP unavailable; literature is unambiguous so no information lost |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "division polynomial" / "Ψ₂" | n/a | (no references dir for this concept / not present)   | recorded n/a; the source statement + mathlib are authoritative here |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"              | partial | nLab covers elliptic curves but has no dedicated division-polynomial base-change page | the functoriality is the trivial "polynomial with integer-coeff structure constants" statement |
|  7 | nCatLab                          | n/a — this is a commutative-algebra naturality fact, not a categorical universal property | n/a | —                                                    | "form `Ψ₂Sq`" is a functor `CommRing_{R/} → Poly`; trivially natural; no 2-categorical content |
|  8 | Stacks Project                   | base change of elliptic curve / Weierstrass equation                  | partial | Stacks has Weierstrass equations + base change of schemes; no named division-polynomial lemma | the lemma is downstream bookkeeping, not a Stacks-level result |
|  9 | MathOverflow / Math.StackExchange| "division polynomials commute with base change" generality           | partial | confirmed folklore: division polynomials are defined by universal recurrences in ℤ[a₁..a₆], so they specialise/base-change automatically | no controversy; treated as obvious |
| 10 | recent arXiv (last 5 years)      | division polynomial functoriality / EDS base change                  | no   | no paper isolates this; it is a one-line consequence of the universal definition | not a research-level statement |

### Literature summary (Phase 3)

Concept identified as: the **squared 2-division polynomial** `Ψ₂Sq = ψ₂² = 4X³ +
b₂X² + 2b₄X + b₆` (a.k.a. the two-torsion polynomial) of a Weierstrass curve, and
its **compatibility with base change** (functoriality in the base ring).
Sources agree on the standard form: **yes** — `ψ₂²` is a universal polynomial in
the `b_i` (themselves universal in `a₁..a₆`), so applying any ring homomorphism
to the coefficients commutes with forming it. This is folklore (Silverman III,
exercises), not a quotable theorem.
Most general standard form: for **any** ring homomorphism of the base, `Ψ₂Sq`
commutes with coefficient-mapping. The project/mathlib lemma is stated for
`S`-algebra maps `f : A →ₐ[S] B` over a scalar tower — i.e. the relative
base-change formulation — which is one notch *more structured* than the bare
`R →+* S` form, but the bare-ring-map form is exactly the sibling `map_Ψ₂Sq`,
already present and `@[simp]`. The two together cover the full generality.
Generality dimensions: (i) base map = `R →+* S` (the `map_Ψ₂Sq` form) vs.
`S`-algebra map over a tower (the `baseChange_Ψ₂Sq` form); mathlib provides
**both**. No dimension where the project form is missing.
Disagreement with the literature: **none**.

---

### Generality analysis — `WeierstrassCurve.baseChange_Ψ₂Sq` (Phase 4)

Literature-standard form (from Phase 3): functoriality of `Ψ₂Sq` in the base ring;
covered by the pair {`map_Ψ₂Sq` (ring-hom form), `baseChange_Ψ₂Sq` (algebra-map
form)}.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `(f : A →ₐ[S] B)` over scalar tower `R→S→A,B` | relative `S`-algebra base change | apply any ring hom to coefficients | the bare `R →+* S` version is *separately* provided as `map_Ψ₂Sq` | the algebra-over-tower form is the deliberately-chosen base-change idiom in this API; the ring-hom form is its sibling. Not a weakening *gap* — both exist. |
| 2 | `[CommRing R] [CommRing S]` etc. | commutative rings | commutative rings | NO | division polynomials live over `CommRing`; correct generality. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the base-change idiom it targets;
the ring-hom-level generality is covered by the companion `map_Ψ₂Sq`).
Number of weakening opportunities: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled-hyp → typeclass? | no | the algebra/tower context is already typeclass-based | — |
| 2 | sequences → filters? | no | no limiting/topological content | — |
| 3 | construction → universal property? | no | `Ψ₂Sq` is an explicit polynomial; no UP to characterise | — |
| 4 | set+closure → bundled substructure? | no | — | — |
| 5 | field/metric-specific → weaken typeclass? | no | already at `CommRing` | — |
| 6 | 1-categorical → higher? | no | trivial naturality, no 2-cells | — |
| 7 | concrete index → general structure? | no | no numeric index here | — |

Modern idiom available: **no** — this is already the idiomatic mathlib form; in
fact it IS the mathlib form (Phase 5). One-line reason: the lemma is a thin
naturality wrapper over `map_Ψ₂Sq` and `map_baseChange`, already in the
contemporary mathlib `def baseChange` / `map` framework.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.baseChange_Ψ₂Sq` (Phase 5)

Searched the **vendored mathlib source directly** (most authoritative, since the
project explicitly forks the relevant file):

[A] Lean-Finder       n/a (mathlib index offline-equivalent; used direct source grep, which is exact)
[B] Loogle            pattern `(WeierstrassCurve.baseChange _ _).Ψ₂Sq = _` — superseded by exact source hit below
[C] LeanSearch        "base change of squared 2-division polynomial Weierstrass" — superseded by exact source hit
[D] Grep mathlib src  `grep -n "baseChange_Ψ₂Sq" .lake/packages/mathlib/.../DivisionPolynomial/Basic.lean` → **HIT, line 556**
[E] Name pattern      qualified `WeierstrassCurve.baseChange_Ψ₂Sq` → exact match in namespace `WeierstrassCurve`, `section BaseChange`

Searched for both:
  - the user's current form — **found, identical** (see below).
  - the literature-standard / ring-hom form — also found: `map_Ψ₂Sq`
    (`Basic.lean:502`), the `@[simp]` sibling.

**Found in mathlib as `WeierstrassCurve.baseChange_Ψ₂Sq`; IDENTICAL form.**

Mathlib source (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:556-557`):

```lean
lemma baseChange_Ψ₂Sq : (W⁄B).Ψ₂Sq = (W⁄A).Ψ₂Sq.map f := by
  rw [← map_Ψ₂Sq, map_baseChange]
```

Project source (`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:479-480`):

```lean
lemma baseChange_Ψ₂Sq : (W.baseChange B).Ψ₂Sq = (W.baseChange A).Ψ₂Sq.map f := by
  rw [← map_Ψ₂Sq, map_baseChange]
```

These differ **only** in surface notation: mathlib's `W⁄B` is notation for
`W.baseChange B`. Same namespace, same `variable` block (verified identical at
`Basic.lean:548-549` vs project `:473-474`), same `Ψ₂Sq` def (`Basic.lean:117`
vs project `:40`, byte-identical), same proof. This is a literal copy.

Concluded: **found in mathlib as `WeierstrassCurve.baseChange_Ψ₂Sq`; identical form.**

---

### Call sites — `WeierstrassCurve.baseChange_Ψ₂Sq` (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring file): **0**
External-to-file callers: **0 distinct files**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep: (none — no site re-derives base-change of `Ψ₂Sq` by hand).

Interpretation: K = 0 internal uses, no inline re-derivation. In the
`/mathlibable` call-site table this reads as "dead code / forked-for-completeness".
Here it is clearly the latter: the lemma was copied wholesale as part of forking
the entire mathlib `Basic.lean` (the fork's purpose was the import swap, not this
lemma), so it is carried along for fidelity even though nothing in NagellLutz
consumes it yet. This reinforces — does not weaken — the NO verdict.

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 chained calls? Moot — mathlib **already has
the finished lemma**, so this is `NO-mathlib-has-it`, not `NO-composable`. (For
completeness: the proof is itself a 2-call composition `map_Ψ₂Sq` ∘ `map_baseChange`,
both of which are also already in mathlib — so even absent the packaged lemma it
would be a trivial composition.)

Conclusion: **N/A — superseded by exact mathlib hit.**

---

## Verdict: `WeierstrassCurve.baseChange_Ψ₂Sq`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the object (`Ψ₂Sq = ψ₂²`, two-torsion poly) and its
  base-change functoriality are standard/folklore (Silverman III); no generality
  gap.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom improvement —
  it is already the mathlib form.
- Mathlib search (Phase 5): **found in mathlib as
  `WeierstrassCurve.baseChange_Ψ₂Sq`; identical form** (`Basic.lean:556`).
- Composition check (Phase 6): N/A (exact hit).

**Rationale:**

This declaration is a verbatim copy of the mathlib lemma of the same fully
qualified name. The project's own module docstring states the file "is a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked only
to import a local `EllipticDivisibilitySequence` (to dodge a `normEDS` /
`complEDS` name clash). The `Ψ₂Sq` definition, the surrounding `variable` block,
the `map_Ψ₂Sq` lemma it depends on, and the `baseChange_Ψ₂Sq` statement + proof
are byte-for-byte identical to mathlib (the only textual difference is mathlib's
`W⁄B` notation vs. the spelled-out `W.baseChange B`, which are the same term).
There is nothing to contribute: mathlib has it, at exactly this generality, with
exactly this proof.

WHY not (refactor-actionable detail):
Mathlib already has the result. Existing decl:
`WeierstrassCurve.baseChange_Ψ₂Sq`, located at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:556`. The
project form is not merely *implied by* mathlib's — it is *the same declaration*.
Our form follows in 0 lines (it is identical):

```lean
-- mathlib's lemma, reachable as WeierstrassCurve.baseChange_Ψ₂Sq, already proves:
example : (W.baseChange B).Ψ₂Sq = (W.baseChange A).Ψ₂Sq.map f :=
  WeierstrassCurve.baseChange_Ψ₂Sq
```

Call sites in NagellLutz (Phase 6.0): **K = 0**.

Refactor plan: there are no call sites to migrate. The lemma exists only because
the whole file was forked. The decision of whether to *delete* the project copy
is a **project-policy** matter, not a free mechanical swap: the fork was created
deliberately to avoid the mathlib `EllipticDivisibilitySequence` name clash, so
the project cannot simply `import` mathlib's `DivisionPolynomial.Basic` in place
of its fork without re-introducing that clash. Two clean options for the project
owner:
  1. If/when the local `EllipticDivisibilitySequence` divergence is reconciled
     with mathlib's, drop the entire forked `DivisionPolynomial.lean` and import
     `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, getting
     this lemma (and its ~30 siblings) for free.
  2. Until then, keep the fork as-is — but mark this lemma (and the rest of the
     copied `Map`/`BaseChange` block) as "mathlib-tracked, do not modify", since
     it carries no project-specific content. **Do not** propose it for a mathlib
     PR — it is already there.

Next action: no mathlib PR. Treat as a tracked fork; revisit deletion when the
local EDS fork is upstreamed/reconciled. The fork-vs-import decision is for the
project owner (borders on policy), but the mathlibable status of the declaration
itself is settled: **mathlib has it**.

---

## Next step

No mathlib PR. The lemma is already in mathlib verbatim
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:556`,
`WeierstrassCurve.baseChange_Ψ₂Sq`). It exists in the project only because
`DivisionPolynomial.lean` is an acknowledged fork of that mathlib file. No call
sites depend on it. Leave as a tracked copy; delete the fork (and inherit this
lemma from mathlib) once the local `EllipticDivisibilitySequence` divergence is
reconciled.
