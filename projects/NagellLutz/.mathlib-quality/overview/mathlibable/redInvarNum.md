# /mathlibable report — `EllSequence.redInvarNum`

> Step-9 mathlibable assessment (AINTLIB /overview), NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences). Single declaration.
> Re-assessment 2026-06-21 (supersedes the 2026-06-18 pass; all load-bearing evidence re-verified
> against the vendored mathlib tree). Verdict unchanged.
>
> Environment note: local Lean build is stale (read-only assessment from source); mathlib-index
> tools (loogle/leansearch) were unavailable, so Phase 5 methods [B]/[C] fall back to an
> **exhaustive grep over the vendored mathlib tree** (`.lake/packages/mathlib/`), which is
> definitive for an existence question. ChatGPT MCP unavailable — Phase 3 channel #4 recorded
> `n/a`, compensated by 4 WebSearch queries + arXiv source review + nLab/Stacks/Wikipedia.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale locally (reasoned from source; the decl elaborates in the green `main` build per project state)
- decl `EllSequence.redInvarNum`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1364` (docstring at 1362)
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS) — defines EDS and constructs normalised EDSs from initial terms; a **fork/extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`, authored by David Kurniadi Angdinata (the same mathlib EDS author).

**Qualified name verified:** the base name `redInvarNum` sits inside `namespace EllSequence`
(re-opened at line 1356, after earlier `namespace EllSequence … end EllSequence` blocks). Fully
qualified name = **`EllSequence.redInvarNum`**. The parsed-from-prompt name is correct.

---

### Statement (Phase 1)

`EllSequence.redInvarNum` is a **definition** of an algebraic expression in a commutative ring `R`:

```lean
variable (b c d : R) (m : ℤ)
/-- The numerator of the reduced invariant expression
`(W(m-1)²W(m+2) + W(m-2)W(m+1)² + W₂²W(m)³)/W₂`
for a normalised EDS W, obtained by cancelling `W₃W₂ = b*c` from `invarNum`. -/
def redInvarNum : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m
```

In mathematical prose: for a **normalised elliptic divisibility sequence** `W = normEDS b c d`
(with `W₁ = 1`, `W₂ = b`, `W₃ = c`, `W₄ = d·b`), the project defines an "invariant numerator"
`invarNum(1, m) = W(m+2)·W(m−1)² + W(m+1)²·W(m−2) + W(m)³·b²` (the numerator of a ratio
`invarNum(s,n)/invarDenom(s,n)` that is **constant in `n`** — a genuine EDS invariant). This numerator
carries a common factor `W₃·W₂ = c·b`; `redInvarNum b c d m` is the **cofactor after dividing
`invarNum(1,m)` by `b = W₂`**:

> `invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`  (lemma `invarNum_eq_redInvarNum_mul`, line 1372).

Because `b` may be a zero-divisor in a general commutative ring, the quotient cannot be taken
literally; `redInvarNum` is therefore *defined* directly as the division-free polynomial combination
`compl₂EDS + normEDS³·b + 2·compl₂EDSAux`, whose product with `b` recovers `invarNum`. This is the
device that lets the project construct the **ω-division polynomial division-free**:
`ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2`, where the troublesome `ψ₂ₙ/ψₙ` term is expressed through
`compl₂EDS`/`redInvarNum` rather than ring division. (Consumed in `DivisionPolynomialOmega.lean:84`
via the sibling lemma `compl₂EDS_eq_redInvarNum_sub`.)

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (commutative ring; maximal generality already).
- `(b c d : R)` — the three seeds of the normalised EDS (`W₂, W₃, W₄/W₂`).
- `(m : ℤ)` — the index.

Hypotheses: none (a plain `def`, total in `m`).

Conclusion (math): an element of `R` — the reduced-invariant numerator.
Conclusion (Lean): `R` (n/a — definition, no proof obligation).

---

### Size classification (Phase 2a)

**Verdict: SMALL** (BIG-adjacent).
Reason: a `def` of a bespoke intermediate algebraic *expression*, not a named mathematical
*structure* (no new typeclass / topology / category), and not a person-named theorem. It is a building
block in the ω-division-polynomial construction, not a `## Main results` headline. It sits *next to*
genuinely BIG content (the division-free `ω`/`ψc` apparatus), but standing alone it is a helper
definition. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`compl₂EDS … + normEDS … ^3 * b + 2 * compl₂EDSAux …`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | partial  | The companion lemma `compl₂EDS_eq_redInvarNum_sub` (`:= by rw [redInvarNum]; ring`) is the actual API surface consumed downstream; the name seals the expression so `ring`/`simp` rewrites target it deliberately rather than blowing it open. Mild. |
| Avoid typeclass diamonds          | no       | Pure ring expression; no instance-search path involved. |
| Mark semantic intent / API name   | yes      | The name + docstring ("numerator of the reduced invariant, obtained by cancelling `W₃W₂ = b*c`") *is* the contract. Consumers (`compl₂EDS_eq_redInvarNum_sub`, `invarNum_eq_redInvarNum_mul`, `redInvar_normEDS`, `map_redInvarNum`, and `DivisionPolynomialOmega`) depend on the named handle, not the literal RHS. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name). The one-liner bias toward NO
is lifted: this is a named bookkeeping anchor for a multi-lemma construction, not a trivial alias.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS "invariant" numerator denominator division polynomial normalised W(2m)                              | partial | Ward/Stange EDS + ψ-recurrence; no "reduced invariant numerator" | classical EDS invariant exists; the *reduced cofactor* term does not |
|  2 | WebSearch (general / source)     | EDS reduced invariant W(m-1)²W(m+2) division polynomial omega Stange Ward                                | no   | no named "reduced invariant numerator" | hits are generic EDS / division-polynomial expositions (Wikipedia, Stange eprint 2025/521, Shipsey, valuations papers) |
|  3 | WebSearch (named-after / Lean)   | Angdinata division polynomials elliptic curves Lean mathlib normalised EDS omega psi formalisation      | yes  | mathlib `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` | identifies the construction context; ω is the target object, not redInvarNum |
|  4 | ChatGPT MCP                      | (whether "reduced invariant numerator" is a standard named concept; its generality)                     | n/a  | — | MCP unavailable; compensated by extra WebSearch + arXiv review |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` ; `refs/`                                             | n/a  | — | neither directory present (recorded n/a per protocol) |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial                                                    | n/a  | — | nLab has no EDS / reduced-invariant entry; not a categorical concept |
|  7 | nCatLab                          | (categorical reformulation)                                                                             | n/a  | — | not a categorical concept — a ring-element expression |
|  8 | Stacks Project                   | division polynomial / elliptic divisibility sequence                                                    | n/a  | — | Stacks has no EDS / division-polynomial chapter for this |
|  9 | MathOverflow / MSE               | (subsumed by WebSearch #1/#2)                                                                            | no   | — | no thread on a "reduced invariant numerator" of an EDS |
| 10 | recent arXiv (≤5 yr)             | EDS over commutative rings; algebraic division polynomials (Junyan Xu programme; Stange eprint 2025/521) | yes  | algebraic EDS over comm. rings; division polys treated algebraically | the algebraic, division-free programme this apparatus formalises |

### Literature summary (Phase 3)

Concept identified as: **the numerator of the "reduced invariant" of a normalised EDS** — an
intermediate algebraic expression internal to a *division-free, commutative-ring* construction of the
ω-division polynomial. The *underlying* invariant (`invarNum`/`invarDenom`, "for each `s`,
`invarNum s n / invarDenom s n` is constant in `n`") is a genuine, classical EDS invariant in the
Ward/Stange lineage. The **"reduced" numerator specifically** (the cofactor after cancelling
`W₃W₂ = c·b`) is **not a named object in the literature**.

Sources agree on the standard form: **no** — there is no literature-standard "reduced invariant
numerator". The classical EDS invariant is standard; *this particular cancellation-cofactor* is a
formalisation-engineering device.

Most general standard form: the invariant itself is already stated over a general commutative ring in
the project (`invarNum (s n : ℤ) : R`, any `[CommRing R]`). The reduced numerator is a `b`-cofactor of
the `s = 1` case.

Generality dimensions where the literature varies:
  - coefficient ring: classical sources use `ℤ`/`ℂ` (Ward) or a field; **commutative ring is the modern
    (algebraic / mathlib) generality** — the project is already there.
  - index: always `ℤ` (or `ℕ`); no generalisation axis.

Disagreement with the literature: none — the project is *strictly more general* than (and is the
formal backbone of) the literature it cites.

---

### Generality analysis — `EllSequence.redInvarNum`

Literature-standard form (from Phase 3): there is no standalone literature form; the closest anchor is
"the cofactor of `invarNum(1,m)` by `W₂` for a normalised EDS over a commutative ring", which is
exactly what is defined.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`        | commutative ring  | comm. ring (algebraic) / ℤ, field (classical) | **NO** | Already the maximal sensible generality. EDS division-free constructions need a commutative ring; the whole point of the apparatus (vs mathlib's analytic ω) is to drop to `CommRing`. Non-commutative / semiring is meaningless here (subtraction + commutative multiplication are essential to the quartic relations). |
| 2 | `(b c d : R)`         | three free seeds  | three seeds              | NO                  | These ARE the defining data of a normalised EDS; cannot be weakened. |
| 3 | `(m : ℤ)`             | integer index     | integer index            | NO                  | EDS are ℤ-indexed by definition. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0.** The definition is already stated over an arbitrary
commutative ring `R` — the modern (Bourbaki-2.0) generality, strictly above the `ℤ`/field forms in the
classical literature. Cost of restatement: n/a (nothing to restate).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | already typeclass-driven (`[CommRing R]`); seeds `b c d` are genuine data, not a bundleable hypothesis |
|  2 | sequences/metric → filters/topology? | no | — | purely algebraic; no limiting/topological content |
|  3 | construct object → universal-property class? | no | — | an explicit polynomial cofactor; no universal property to characterise |
|  4 | set+closure-predicate → bundled substructure? | no | — | not a set/substructure |
|  5 | vector-space/field-specific → weaken typeclass? | no | — | already at `CommRing`; nothing field-specific to weaken |
|  6 | 1-categorical → higher-categorical? | no | — | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | — | EDS are intrinsically ℤ-indexed |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The definition is already in the contemporary commutative-ring,
division-free idiom (itself the *modernisation* of the classical analytic construction). One mild
observation: the RHS could equivalently be folded so that `compl₂EDS_eq_redInvarNum_sub` is the
primitive and `redInvarNum` the derived rearrangement — but that is a presentation choice within the
project, not a mathlib-idiom upgrade. No real organisational improvement to chase.

---

### Diamond / defeq risk — `EllSequence.redInvarNum` (Phase 4.5, kind = `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | No instance declared; just a ring element. No search path affected. |
| 2 | Reducibility leak | none | Not `@[reducible]`; the body is a sealed ring expression. Downstream uses go through `redInvarNum`-named lemmas, not defeq. |
| 3 | Non-canonical unfolding | low | `simp [redInvarNum]` / `rw [redInvarNum]` unfold it (used deliberately in `compl₂EDS_eq_redInvarNum_sub`, `invarNum_eq_redInvarNum_mul`); behaviour is intended and local. |
| 4 | Instance priority collision | none | Not an instance. |
| 5 | Universe-polymorphism issues | none | `R : Type u`, fully polymorphic; body forces no annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** No HIGH rows. No mitigations required.

---

### Mathlib search-status: `EllSequence.redInvarNum`

[A] Lean-Finder       (unavailable in env)                              n/a: tool not present
[B] Loogle            `_ + _ ^ 3 * _ + 2 * _` over EDS terms; `redInvarNum`; `invarNum` — via exhaustive grep of `.lake/packages/mathlib/`  →  **no hits**
[C] LeanSearch        "reduced invariant numerator EDS"; "invariant numerator normalised EDS" — via grep fallback  →  **no hits**
[D] Grep mathlib src  `redInvarNum|redInvarDenom|invarNum|invarDenom|compl₂EDS|compl₂EDSAux|reducedInvariant` over the whole mathlib tree  →  **ZERO matches** (re-verified 2026-06-21; definitive)
[E] Name pattern      mathlib EDS file def list: `IsEllSequence, IsDivSequence, IsEllDivSequence, preNormEDS'/preNormEDS, complEDS₂, normEDS, normEDSRec'/normEDSRec, complEDS'/complEDS`  →  **no invariant / reduced-invariant / compl₂EDS family at all**

Searched for both:
  - the user's form (`redInvarNum`) — absent;
  - the more general / parent forms (`invarNum`, `invarDenom`, `compl₂EDS`, `compl₂EDSAux`) — all absent.

Note on the fork: mathlib **does** have the `normEDS` / `complEDS₂` / `complEDS` machinery (the project's
`compl₂EDS`/`complEDS`/`normEDS` are a fork of it), but mathlib's `complEDS₂` is the *2-complement
sequence* `Wᶜ₂` (witness of `W(k) ∣ W(2k)` via `normEDS_mul_complEDS₂`), a **different** object from the
project's `compl₂EDS` (whose defining identity is `compl₂EDS b c d m * b = W(m−1)²W(m+2) − W(m−2)W(m+1)²`).
They are not interchangeable, and mathlib has neither `compl₂EDS`, `compl₂EDSAux`, `invarNum`, nor
`redInvarNum`.

Corroborating evidence (re-verified 2026-06-21): mathlib
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines
`ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` in prose (line 30) and **lists `ωₙ` as an open TODO** (line 71:
"TODO: the bivariate polynomials `ωₙ`"; line 83: "TODO: implementation notes for the definition of
`ωₙ`"). So the very construction `redInvarNum` serves is *acknowledged-missing* upstream.

Concluded: **not in mathlib** (all available methods exhausted, including the parent `invarNum`/
`compl₂EDS` forms; the consuming object `ωₙ` is an explicit mathlib TODO).

---

### Call sites — `EllSequence.redInvarNum`

Internal use count (this project, excluding the declaring file): **0 direct uses of `redInvarNum`
itself** — the API is consumed through its sibling lemmas (the named handle's purpose).
External-to-file callers of the redInvarNum *API cluster*: 1 file (`DivisionPolynomialOmega.lean`),
plus a full parallel copy in the HasseWeil project.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `DivisionPolynomialOmega.lean:84` | `rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, …]` — `redInvarNum` enters ω/ψc construction via its sibling lemma |
| `EllipticDivisibilitySequence.lean:1367-1374` (same file) | `compl₂EDS_eq_redInvarNum_sub`, `invarNum_eq_redInvarNum_mul` — the two lemmas that ARE the API surface |
| `EllipticDivisibilitySequence.lean:1502-1513` (same file) | `redInvar_normEDS`: `redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)` — the key reduced-invariant identity |
| `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:852+` | full duplicate (`redInvarNum`, `complEDS₂_eq_redInvarNum_sub`, `map_redInvarNum`, `redInvar_normEDS`, …) — independent copy of the same apparatus |

Within-file dependents of the def: `compl₂EDS_eq_redInvarNum_sub`, `invarNum_eq_redInvarNum_mul`,
`map_redInvarNum`, `redInvar_normEDS` (4 lemmas).

Inline-derivation grep (re-derived elsewhere without `redInvarNum`?): none — the `redInvarNum`
expression is not open-coded anywhere; consumers go through the named lemmas. The duplicate in HasseWeil
is a *copy of the same named def*, not an inline re-derivation — reinforcing that this is shared, reused
apparatus (and itself an AINTLIB intra-repo dedup target).

Signal reading: K = 0 *direct* `redInvarNum` calls, but it is **not dead** — it is a named anchor whose
API is its sibling lemmas, and that API is load-bearing in the ω-division-polynomial construction
(`DivisionPolynomialOmega.lean`) and duplicated across two projects. This is the Phase-2b
"semantic-intent / API-name" pattern, not the "K=0 ⇒ junk" pattern.

### Composition check (Phase 6)

Can `EllSequence.redInvarNum` be derived from mathlib in ≤3 chained calls?

Attempt 1: express `redInvarNum` via mathlib primitives.
  - Mathlib decls available: `normEDS`, `complEDS₂` (mathlib's 2-complement). **But** `compl₂EDS` and
    `compl₂EDSAux` — the two summands defining `redInvarNum` — **do not exist in mathlib** (Phase 5,
    [D]/[E]), and mathlib's `complEDS₂` is a *different* object (see Phase 5 note).
  - Result: **fails.** The building blocks `compl₂EDS`/`compl₂EDSAux` are themselves project-only, so
    there is nothing in mathlib to compose.

Attempt 2: build `redInvarNum` from `invarNum / b`.
  - Result: **fails** — `invarNum` is project-only, and the literal `invarNum/b` quotient is exactly what
    `redInvarNum` exists to *avoid* (`b` can be a zero-divisor).

Conclusion: **NOT-COMPOSABLE.** Not only is the exact form absent from mathlib, so are *all* of its
immediate building blocks (`compl₂EDS`, `compl₂EDSAux`, `invarNum`). There is no ≤3-call mathlib
composition.

---

## Verdict: `EllSequence.redInvarNum`

**Category:** `YES-but-generalise-first`

> Bucket nuance: the *definition itself is already maximally general* (Phase 4b: MAXIMALLY GENERAL,
> 0 weakenings; Phase 4c: no modern-idiom upgrade). Standing alone it would read as `YES-add-as-is`.
> It lands in **YES-but-generalise-first** for a *packaging/grain* reason: `redInvarNum` is a single
> cog in a self-contained subsystem (`invarNum`, `invarDenom`, `compl₂EDS`, `compl₂EDSAux`,
> `redInvarNum`, `redInvarDenom`, `complEDS`, and the ω/ψc division polynomials) that fills the
> **mathlib `ωₙ` TODO**. The correct mathlib contribution is that whole division-free-ω apparatus as a
> coherent extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence` +
> `…/DivisionPolynomial/Basic.lean`, **not** `redInvarNum` as an isolated PR. "Generalise first" here =
> "ship as part of the upstreaming of the parent subsystem, named/located to mathlib conventions",
> which is the human-judgement step.

**Evidence:**
- Literature search (Phase 3): no named "reduced invariant numerator" in Ward/Stange/Shipsey/Silverman;
  the classical EDS *invariant* (`invarNum`/`invarDenom`) is standard, but this *cofactor* is a
  division-free formalisation device backing the algebraic division-polynomial programme.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `[CommRing R]` (above the literature's
  `ℤ`/field); 0 weakenings; no modern-idiom upgrade.
- Mathlib search (Phase 5): **not in mathlib** — `redInvarNum` and its parents `invarNum`/`compl₂EDS`/
  `compl₂EDSAux` are all absent (0 grep hits, re-verified); the consuming object `ωₙ` is an explicit
  mathlib **TODO** (`DivisionPolynomial/Basic.lean:71,83`).
- Composition check (Phase 6): **NOT-COMPOSABLE** — the building blocks themselves are not in mathlib.

**Rationale.**
`redInvarNum` is genuinely missing from mathlib, correctly stated at the maximal (commutative-ring)
generality, and not reconstructible from mathlib primitives — its summands `compl₂EDS`/`compl₂EDSAux`
are themselves project-only. On the narrowest reading those facts are a clean `YES-add-as-is`. The
reason the verdict is `YES-but-generalise-first` rather than `YES-add-as-is` is **grain**: this single
one-line cofactor is meaningless in isolation. Its entire purpose is to make `ψ₂ₙ/ψₙ` division-free so
that `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` can be *defined over a commutative ring* — precisely the `ωₙ`
construction that `Mathlib/.../DivisionPolynomial/Basic.lean` flags as an open TODO. Shipping
`redInvarNum` alone would put an unmotivated helper in mathlib with no consumer; shipping it as one
declaration inside the upstreaming of the parent subsystem (the `compl₂EDS`/`invar`/`ω` cluster) is the
right move. That bundling + final mathlib naming/location is a human-judgement call, which is what
"generalise first" encodes here.

Two project-hygiene facts the human owner should weigh (they do not change the bucket):
(i) this exact apparatus is **duplicated** in `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`
(verbatim `redInvarNum`, `complEDS₂_eq_redInvarNum_sub`, `map_redInvarNum`, `redInvar_normEDS`) — an
AINTLIB intra-repo dedup target; the mathlib upstreaming and the dedup should be coordinated so one
canonical copy is the PR source. (ii) The author of this file is **David Kurniadi Angdinata**, the
mathlib EDS author — so this is almost certainly already on a path toward mathlib; the practical next
action is to confirm the upstreaming plan rather than open a competing PR.

**Reason for the generalisation:** `MODERN-IDIOM`-adjacent **packaging/grain**, not a weakening of
`redInvarNum`'s own hypotheses (those are already maximal). The "more general object" to ship is the
parent subsystem (division-free ω over `CommRing`), of which `redInvarNum` is one leaf.

**Proposed restatement.** No change to `redInvarNum`'s signature or proof is needed; it is already
mathlib-shaped. The "restatement" is *contextual*: present it inside the ω/`compl₂EDS` cluster as the
mathlib extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence`:

```lean
namespace EllSequence
variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)

-- (shipped together as the division-free-ω subsystem)
def compl₂EDS    : R := …
def compl₂EDSAux : R := …
def invarNum (s n : ℤ) : R := …
/-- Numerator of the reduced invariant: cofactor of `invarNum 1 m` by `W₂`. -/
def redInvarNum : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m

theorem invarNum_eq_redInvarNum_mul :
    invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by …
end EllSequence
```

Estimated cost of regeneralisation: **CHEAP** for `redInvarNum` itself (verbatim); the real work is
assembling + cleaning the *surrounding* subsystem for a mathlib PR (MODERATE–EXPENSIVE, but that is the
parent-decls' cost, not this leaf's). Cost does **not** downgrade the verdict.

**Mathlib downstream this enables (required for the generalisation):**
- Completes the **`ωₙ` TODO** in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
  — bivariate ω-division polynomials over a commutative ring, division-free.
- Gives mathlib the EDS **invariant** API (`invarNum`/`invarDenom`, the "`invarNum s n / invarDenom s n`
  is constant in `n`" theorem) that its current EDS file lacks — useful for torsion / Nagell–Lutz and
  Hasse–Weil developments (two AINTLIB projects already consume it).
- Provides the `compl₂EDS` "complement of `W(m)` in `W(2m)`" witness, strengthening mathlib's
  divisibility-sequence story alongside `normEDS_dvd_normEDS_two_mul`.

**Next action:** treat `redInvarNum` as part of the **`compl₂EDS`/`invar`/`ω` upstreaming bundle**, not a
standalone PR. Concretely: (1) confirm the upstreaming plan with the file's author (D. K. Angdinata) —
this is plausibly already mathlib-bound; (2) first resolve the **intra-AINTLIB duplication** (HasseWeil
copy) so there is one canonical source; (3) run `/mathlibable` on the *parent* defs (`compl₂EDS`,
`compl₂EDSAux`, `invarNum`) and the ω-division-polynomial result to fix the PR grain; (4) then
`/generalise` + `/cleanup` the bundle and open one feat PR
(`feat(NumberTheory/AlgebraicGeometry): division-free ω-division polynomials and the EDS reduced
invariant over a commutative ring`).

---

## Next step

Treat `EllSequence.redInvarNum` as one leaf of the division-free-ω subsystem and upstream that bundle
(coordinating with the mathlib `ωₙ` TODO and the file's mathlib author), not as a standalone PR. First
deduplicate the parallel copy in HasseWeil inside AINTLIB, then assess the parent defs to set the PR
grain.
