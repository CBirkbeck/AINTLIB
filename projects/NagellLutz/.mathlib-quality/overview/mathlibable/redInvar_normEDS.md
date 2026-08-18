# /mathlibable report — `redInvar_normEDS`

> Step-9 mathlibable assessment (AINTLIB /overview), NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences). Single declaration,
> Mode A (full 10-phase workflow).
> Re-assessment 2026-06-21 (supersedes the 2026-06-18 pass). **Verdict unchanged
> (`YES-but-generalise-first`), but the fully-qualified name is CORRECTED** — see Baseline.
>
> Environment note: local Lean build is stale (read-only assessment reasoned from source); the
> mathlib-index tools (loogle / leansearch) were unavailable, so Phase 5 methods [B]/[C] fall back
> to an **exhaustive grep over the vendored mathlib tree** (`.lake/packages/mathlib/`), which is
> definitive for an existence question and was cross-checked against the live `mathlib4_docs`.
> ChatGPT MCP unavailable — Phase 3 channel #4 recorded `n/a`, compensated by 2 fresh WebSearch
> queries + the sibling `redInvarNum.md` literature sweep (Ward / Stange eprint 2025/521 / Wikipedia
> EDS / arXiv valuations papers).

---

### Baseline (Phase 0)
- lake build:               ⚠ stale locally (reasoned from source; the decl elaborates in the green `main` build per project state)
- decl `redInvar_normEDS`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1509` (private helper `redInvar_normEDS_of_mem_nonZeroDivisors` at 1501)
- kind:                      `lemma` (a theorem — the reduced-invariant **identity**, not a `def`)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS) — defines EDS and constructs normalised EDSs from initial terms; a **fork/extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`, authored by David Kurniadi Angdinata (the same mathlib EDS author).

**Qualified name — CORRECTED to `redInvar_normEDS` (bare, NO namespace).**
The prompt said "VERIFY". The base name `redInvar_normEDS` is declared at line 1509 inside
`section NormEDS` (opened line 881) → bare `section` (1462) → bare `section` (1203). It is **not**
inside any `namespace`. The namespace stack was computed mechanically over lines 1..1509:

```
90:namespace EllSequence      ↦ closed by  597:end EllSequence
643:namespace IsEllSequence    ↦ closed by  702:end IsEllSequence
1079:namespace EllSequence     ↦ closed by 1112:end EllSequence
1356:namespace EllSequence     ↦ closed by 1431:end EllSequence
```
⇒ **open-namespace stack at line 1509 = EMPTY.** Fully-qualified name = **`redInvar_normEDS`**.

> Correction note: the 2026-06-18 pass recorded the FQN as `EllSequence.redInvar_normEDS`, reasoning
> that the *top-level* `namespace EllSequence` (line 90) was "still open at 1504". It is **not** — it
> closes at `end EllSequence` (line 597). What *is* in scope at 1509 is an `open EllSequence`
> (line 884, inside `section NormEDS`), which governs name **resolution** of the RHS symbols
> (`redInvarNum`/`redInvarDenom` resolve to `EllSequence.redInvarNum`/`EllSequence.redInvarDenom`)
> but does **not** prefix the **declared** name. Hence the declared name is the bare `redInvar_normEDS`.
> This matches the report filename and the ledger key. (The sibling defs `redInvarNum`/`redInvarDenom`
> ARE inside `namespace EllSequence` at 1356, so they are correctly `EllSequence.redInvarNum` etc. —
> different line, different scope.)

---

### Statement (Phase 1)

`redInvar_normEDS` is a **lemma** (an identity) over an arbitrary commutative ring:

```lean
variable {R : Type u} [CommRing R] (b c d : R)
open EllSequence   -- so redInvarNum/redInvarDenom below are EllSequence.redInvarNum/…

lemma redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D) ?_ ?_ m))
  · simpa only [map_redInvarNum, map_mul, map_add, map_pow, map_redInvarDenom, aeval_X] using this
  all_goals exact mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)
```

In mathematical prose: for the **normalised elliptic divisibility sequence** `W = normEDS b c d`
(seeds `W₁ = 1`, `W₂ = b`, `W₃ = c`, `W₄ = d·b`), the project builds a genuine EDS *invariant*: by
`invar_of_net`, for each `s` the ratio `invarNum(s,n) / invarDenom(s,n)` is **constant in `n`**.
Specialising `s = 1` and reading off `n = 2` (where `invarNum(1,2) = (d+b⁴)·b` and
`invarDenom(1,2) = c·b`, lemmas `invarNum_normEDS_two` / `invarDenom_normEDS_two`) gives the
cross-multiplied invariant `invarNum(1,m) · (c·b) = invarNum(1,2) · invarDenom(1,m)`. Both sides
carry the common factor `W₃W₂ = c·b`; cancelling it (the `redInvar*` numerator/denominator are
exactly the `÷b÷c` cofactors, `invarNum(1,m) = redInvarNum·b`, `invarDenom(1,m) = redInvarDenom·b·c`)
collapses the invariant to the clean **reduced-invariant identity**

> `redInvarNum b c d m = redInvarDenom b c d m · (d + b⁴)`,   for **all** `m : ℤ`, over **any** `[CommRing R]`.

Here `d + b⁴` is the value of the EDS invariant `invarNum(1,2)/invarDenom(1,2)` stripped of `c`
(morally `W₅/(W₃W₂)`-flavoured data of the curve). This identity is the **division-free engine**:
it is what lets `ψ₂ₙ/ψₙ` be rewritten without ring division, so that the bivariate
`ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2` can be **defined over a commutative ring**.

Proof shape (a textbook mathlib idiom): prove it first **assuming `b, c ∈ R⁰`** (non-zero-divisors)
via the private `redInvar_normEDS_of_mem_nonZeroDivisors` (which just cancels `b`, `c` off
`invar₂_normEDS`), then transfer to an **arbitrary** ring by interpreting it on the **universal
curve** over `MvPolynomial Param ℤ` — where the generators `X B, X C, X D` are non-zero-divisors —
and pushing forward through `aeval (Param.rec b c d)` (the ring hom `B,C,D ↦ b,c,d`), using the
`map_redInvarNum` / `map_redInvarDenom` naturality lemmas. "Prove over the generic ring, specialise
by `aeval`" — the same device mathlib's own `normEDS`/division-polynomial development uses.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (commutative ring; already maximal generality).
- `(b c d : R)` — the three seeds of the normalised EDS (`W₂, W₃, W₄/W₂`).
- `(m : ℤ)` — the index.

Hypotheses: **none** (no `R⁰` side conditions — that is the whole achievement of the `aeval`
transfer; the unconditional form is strictly stronger than the `_of_mem_nonZeroDivisors` helper).

Conclusion (math): the reduced-invariant identity `redInvarNum = redInvarDenom · (d + b⁴)`.
Conclusion (Lean): the `Prop` equality above.

---

### Size classification (Phase 2a)

**Verdict: SMALL** (BIG-adjacent).
Reason: a single named *identity* (`lemma`), not a `## Main results` headline theorem, not a named
mathematical structure, not a person-named theorem. It is the keystone identity of the division-free
ω apparatus, and sits *next to* genuinely BIG content (the `ωₙ`/`ψc` construction that fills a
standing mathlib TODO), but standing alone it is a supporting lemma. (Literature width run EXHAUSTIVE
regardless, via the sibling `redInvarNum.md` sweep + 2 fresh WebSearches.)

### One-line check (Phase 2b)

Body: a 4-line `aeval`-transfer proof (`have congr(aeval …)`; `simpa only […]`; `all_goals exact …`).
Statement: a one-line equality. **Not** a trivial one-liner — the proof carries real content
(universal-curve transfer to drop the `R⁰` hypotheses). One-liner bias toward NO does **not** apply:
this is a load-bearing theorem with a non-trivial proof, consumed downstream. **NOT a throwaway alias.**

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS invariant `W(n+2s)W(n-s)²` division polynomial omega normalised reduced                              | partial | classical EDS relation (Ward/Stange); no "reduced invariant identity" | the quartic EDS relation + ψ/φ/ω normalisation are standard; the *reduced-invariant equation* is not a named result |
|  2 | WebSearch (named-after / Lean)   | mathlib4 EllipticDivisibilitySequence normEDS IsEllDivSequence invarNum redInvarNum PR omega             | no   | mathlib has `IsEllSequence`/`normEDS`/`complEDS`; ω an open TODO | confirms `invarNum`/`redInvarNum` are NOT upstream; live `mathlib4_docs` corroborate the vendored grep |
|  3 | WebSearch (general / source)     | (covered by sibling `redInvarNum.md` #1/#2) reduced invariant W(m-1)²W(m+2) Stange Ward Shipsey          | no   | no named "reduced invariant" identity | hits = generic EDS / division-polynomial expositions (Wikipedia, Stange eprint 2025/521, Shipsey, valuations papers) |
|  4 | ChatGPT MCP                      | (whether the reduced-invariant identity is a standard named result; its generality)                     | n/a  | — | MCP unavailable; compensated by #1/#2 + sibling sweep |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` ; `refs/`                                             | n/a  | — | neither directory present (recorded n/a per protocol) |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial / EDS invariant                                    | n/a  | — | nLab has no EDS / invariant entry; not a categorical concept |
|  7 | nCatLab                          | (categorical reformulation)                                                                             | n/a  | — | not categorical — a ring-element identity |
|  8 | Stacks Project                   | division polynomial / elliptic divisibility sequence                                                    | n/a  | — | Stacks has no EDS / division-polynomial chapter for this |
|  9 | MathOverflow / MSE               | (subsumed by WebSearch #1/#3)                                                                            | no   | — | no thread on a "reduced invariant identity" of an EDS |
| 10 | recent arXiv (≤5 yr)             | algebraic EDS over commutative rings; division polys (Junyan Xu programme; Stange eprint 2025/521)       | yes  | algebraic EDS / division polys over comm. rings | the division-free, commutative-ring programme this identity formalises |

### Literature summary (Phase 3)

Concept identified as: **the reduced-invariant identity of a normalised EDS** — the closed-form value
of the (classical) EDS invariant `invarNum(s,n)/invarDenom(s,n)` at `s = 1`, after cancelling the
common factor `W₃W₂ = c·b`. The *underlying* invariant (constancy of `invarNum s n / invarDenom s n`
in `n`) is a genuine, classical EDS fact in the Ward/Stange lineage. The **specific equation**
`redInvarNum = redInvarDenom · (d + b⁴)` is a **formalisation-engineering identity**, not a named
result in the literature: its purpose is to make the `ψ₂ₙ/ψₙ` term division-free.

Sources agree on the standard form: **no** — there is no literature-standard "reduced invariant
identity". The EDS invariant is classical; this *particular cancelled equation over a commutative
ring* is the project's division-free device.

Most general standard form: the invariant is already stated over a general commutative ring in the
project; the reduced identity is the `s = 1`, factors-cancelled, hypothesis-free specialisation.

Generality dimensions where the literature varies:
  - coefficient ring: classical sources use `ℤ`/`ℂ` (Ward) or a field; **commutative ring is the
    modern (algebraic / mathlib) generality** — the project is already there, and crucially the
    lemma is **unconditional** (no `R⁰` hypotheses) thanks to the universal-curve transfer.
  - index: always `ℤ`; no generalisation axis.

Disagreement with the literature: none — the project is *strictly more general* than (and is the
formal backbone of) the literature it cites.

---

### Generality analysis — `redInvar_normEDS`

Literature-standard form (Phase 3): no standalone literature form; the closest anchor is "the value
of the EDS invariant at `s = 1`, cancelled of `W₃W₂`, for a normalised EDS over a commutative ring",
which is exactly what is proved — and proved **without** the `R⁰` side conditions.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`        | commutative ring  | comm. ring (algebraic) / ℤ, field (classical) | **NO** | Already the maximal sensible generality. The EDS quartic relations need a commutative ring (subtraction + commutative multiplication essential); non-commutative / semiring is meaningless here. |
| 2 | `(b c d : R)`         | three free seeds  | three seeds              | NO                  | These ARE the defining data of a normalised EDS; cannot be weakened. |
| 3 | `(m : ℤ)`             | integer index     | integer index            | NO                  | EDS are ℤ-indexed by definition. |
| 4 | (`b, c ∈ R⁰`?)        | **absent**        | typically needs `W₂,W₃` non-zero-div to cancel | **already removed** | The `_of_mem_nonZeroDivisors` helper *has* these hypotheses; `redInvar_normEDS` **drops them** via the universal-curve `aeval` transfer. This is the lemma's value-add — it is already at the strongest (hypothesis-free) form. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0.** Stated over an arbitrary commutative ring `R` — the
modern (Bourbaki-2.0) generality, strictly above the classical `ℤ`/field forms — **and** already
hypothesis-free (the `R⁰` conditions of the helper are eliminated). Nothing left to weaken.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | already typeclass-driven (`[CommRing R]`); `b c d` are genuine data |
|  2 | sequences/metric → filters/topology? | no | — | purely algebraic; no limiting content |
|  3 | construct object → universal-property class? | no | — | an identity between explicit ring elements; no universal property |
|  4 | set+closure-predicate → bundled substructure? | no | — | not a set/substructure |
|  5 | vector-space/field-specific → weaken typeclass? | no | — | already at `CommRing`; nothing field-specific |
|  6 | 1-categorical → higher-categorical? | no | — | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | — | EDS intrinsically ℤ-indexed |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The lemma is already in the contemporary commutative-ring,
division-free, hypothesis-free idiom (itself the modernisation of the classical analytic
construction). No organisational upgrade to chase.

---

### Diamond / defeq risk — `redInvar_normEDS` (Phase 4.5, kind = `lemma`)

A `Prop`-valued lemma: no instance, no `def`, no reducibility surface. Diamond/defeq/instance-priority
risks are **N/A**. The only consideration is that the RHS symbols (`redInvarNum`, `redInvarDenom`)
resolve via `open EllSequence`; the *declared* name carries no namespace (see Baseline). Overall
risk: **NONE.**

---

### Mathlib search-status: `redInvar_normEDS`

[A] Lean-Finder       (unavailable in env)                                                          n/a: tool not present
[B] Loogle            `redInvarNum _ _ _ _ = redInvarDenom _ _ _ _ * _`; via exhaustive grep of `.lake/packages/mathlib/`  →  **no hits**
[C] LeanSearch        "reduced invariant identity EDS"; "normalised EDS invariant `d + b^4`" — via grep fallback           →  **no hits**
[D] Grep mathlib src  `redInvar_normEDS|redInvarNum|redInvarDenom|invarNum|invarDenom|invar_of_net|\bnet\b|compl₂EDS|compl₂EDSAux|EllSequence` over the whole mathlib tree  →  **ZERO matches** for the EDS-invariant family (re-verified 2026-06-21; definitive)
[E] Name pattern      mathlib EDS file def list: `IsEllSequence, IsDivSequence, IsEllDivSequence, preNormEDS'/preNormEDS, complEDS₂, normEDS, normEDSRec'/normEDSRec, complEDS'/complEDS`  →  **no invariant / reduced-invariant / `net` / `compl₂EDS` family at all**

Searched for both:
  - the user's form (`redInvar_normEDS`) — absent;
  - the parent / supporting forms (`redInvarNum`, `redInvarDenom`, `invarNum`, `invarDenom`,
    `invar_of_net`, `net`, `compl₂EDS`, `compl₂EDSAux`) — **all absent**.

Note on the fork: mathlib **does** have the `normEDS` / `complEDS₂` / `complEDS` machinery (the
project forks it), and mathlib's EDS file even **lists the relevant facts as open TODOs**:
> `EllipticDivisibilitySequence.lean:44` — "TODO: prove that `normEDS` satisfies `IsEllDivSequence`."
> `EllipticDivisibilitySequence.lean:45` — "TODO: prove that a normalised sequence satisfying
>   `IsEllDivSequence` can be given by `normEDS`."
Mathlib's `complEDS₂` is the *2-complement sequence* `Wᶜ₂` (witness of `W(k) ∣ W(2k)`), a **different**
object from the project's `compl₂EDS` (defining identity
`compl₂EDS b c d m · b = W(m−1)²W(m+2) − W(m−2)W(m+1)²`). They are not interchangeable, and mathlib has
**none** of `net`, `invarNum`, `invarDenom`, `invar_of_net`, `redInvarNum`, `redInvarDenom`, or
`redInvar_normEDS`.

Corroborating (re-verified 2026-06-21, incl. live `mathlib4_docs`): mathlib
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines
`ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` in prose and **lists `ωₙ` as an open TODO** ("TODO: the bivariate
polynomials `ωₙ`" / "TODO: implementation notes for the definition of `ωₙ`"). The reduced-invariant
identity `redInvar_normEDS` is precisely the lemma that makes `ψ₂ₙ/ψₙ` division-free for that `ωₙ`
construction — so the result is *acknowledged-missing* upstream.

Concluded: **not in mathlib** (all available methods exhausted, including the supporting
`invarNum`/`net`/`compl₂EDS` forms; the consuming object `ωₙ` is an explicit mathlib TODO).

---

### Call sites — `redInvar_normEDS`

Internal-to-repo consumers (excluding the declaring file), grep over `projects/`:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:84` | `rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, mul_assoc (C _), …]` — the identity enters the ω/ψc division-polynomial construction (division-free) |
| `HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:104` | `rw [ψc, complEDS₂_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, …]` — the **HasseWeil twin** of the same rewrite |
| `HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:997` | full duplicate `lemma redInvar_normEDS` (+ its `_of_mem_nonZeroDivisors` helper at 990) — independent copy of the same apparatus |

Within-file: the public `redInvar_normEDS` (1509) is the `aeval`-transfer of the private
`redInvar_normEDS_of_mem_nonZeroDivisors` (1501); both sit atop `invar₂_normEDS` (1491) →
`invar_normEDS` (1478) → `invar_of_net` (149) / `net_normEDS` (1465).

Inline-derivation grep (re-derived elsewhere without `redInvar_normEDS`?): none — consumers `rw` the
named lemma. The HasseWeil copy is a *verbatim duplicate of the same lemma*, not an inline
re-derivation — reinforcing that this is shared, reused apparatus (and an AINTLIB intra-repo dedup
target).

Signal reading: **K = 2 external call sites** (one per project, in each project's ω-division-polynomial
file), plus the duplicate definition — i.e. genuinely load-bearing in **both** the NagellLutz and
HasseWeil division-polynomial developments. Not dead, not a one-off; the "K small ⇒ lean toward
NO-composable" heuristic is overridden because (a) it is consumed in the headline ω construction in
two projects, and (b) it is *not composable* from mathlib at all (Phase 6).

### Composition check (Phase 6)

Can `redInvar_normEDS` be derived from mathlib in ≤3 chained calls?

Attempt 1: assemble the identity from mathlib EDS primitives.
  - It is an equality between `redInvarNum` and `redInvarDenom · (d+b⁴)`. **Both** sides name
    project-only objects (`redInvarNum`, `redInvarDenom`) whose very *definitions* use project-only
    building blocks (`compl₂EDS`, `compl₂EDSAux`, `complEDS`) absent from mathlib (Phase 5).
  - Result: **fails** — there is nothing in mathlib to even state the two sides, let alone prove their
    equality.

Attempt 2: derive it from a mathlib EDS-invariant lemma.
  - Result: **fails** — mathlib has **no** EDS invariant API (`invarNum`/`invarDenom`/`invar_of_net`
    are all project-only; mathlib's EDS file flags the related divisibility facts as open TODOs).

Attempt 3: obtain it as a corollary of `normEDS_dvd_normEDS_two_mul` / `complEDS₂` lemmas.
  - Result: **fails** — those concern divisibility witnesses, not the reduced invariant; different
    object (mathlib's `complEDS₂` ≠ project's `compl₂EDS`).

Conclusion: **NOT-COMPOSABLE.** Neither the statement nor any proof path is reconstructible from
mathlib's ≤3 primitives — the entire supporting stack (`net`, `invarNum`, `invar_of_net`,
`compl₂EDS`, `redInvarNum`, `redInvarDenom`) is project-only.

---

## Verdict: `redInvar_normEDS`

**Category:** `YES-but-generalise-first`

> Bucket nuance: the lemma is genuinely missing from mathlib, stated at the maximal
> (commutative-ring) generality, **hypothesis-free** (the `R⁰` conditions are eliminated via the
> universal-curve transfer — a real proof achievement, not a triviality), and not composable from
> mathlib primitives. On the narrowest reading those four facts read as a clean **`YES-add-as-is`**.
> It lands in **`YES-but-generalise-first`** for a *packaging / grain* reason — **not** because any
> hypothesis of this lemma can be weakened (they cannot; Phase 4b found 0 weakenings). `redInvar_normEDS`
> is one keystone identity inside a self-contained subsystem (`net`, `rel₄`, `invarNum`, `invarDenom`,
> `invar_of_net`, `compl₂EDS`, `compl₂EDSAux`, `redInvarNum`, `redInvarDenom`, `complEDS`, and the
> ω/ψc division polynomials) that fills the **mathlib `ωₙ` TODO** and discharges the standing
> **`normEDS`-`IsEllDivSequence` TODOs** in `Mathlib.NumberTheory.EllipticDivisibilitySequence`. The
> correct mathlib contribution is that whole division-free-ω + EDS-invariant apparatus as a coherent
> extension, **not** `redInvar_normEDS` as an isolated PR. "Generalise first" here = "ship as part of
> the upstreaming of the parent subsystem, named/located to mathlib conventions" — the human-judgement
> step.

**Evidence:**
- Literature search (Phase 3): no named "reduced invariant identity" in Ward / Stange / Shipsey /
  Silverman; the EDS *invariant* (constancy of `invarNum s n / invarDenom s n`) is classical, but this
  cancelled equation over a commutative ring is the project's division-free device.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `[CommRing R]` (above the literature's
  `ℤ`/field) **and hypothesis-free**; 0 weakenings; no modern-idiom upgrade.
- Mathlib search (Phase 5): **not in mathlib** — `redInvar_normEDS` and its supporting stack
  (`invarNum`/`invar_of_net`/`net`/`compl₂EDS`/`redInvarNum`/`redInvarDenom`) are all absent (0 grep
  hits, re-verified against vendored tree + live `mathlib4_docs`); the consuming object `ωₙ` is an
  explicit mathlib **TODO**, as is the `normEDS`-`IsEllDivSequence` fact this subsystem proves.
- Composition check (Phase 6): **NOT-COMPOSABLE** — neither statement nor proof is expressible from
  mathlib's ≤3 primitives; the whole supporting stack is project-only.

**Rationale.**
`redInvar_normEDS` is the reduced-invariant identity `redInvarNum = redInvarDenom·(d+b⁴)` for a
normalised EDS, proved unconditionally over any commutative ring by the universal-curve `aeval`
transfer. It is genuinely missing from mathlib, already at maximal generality, hypothesis-free, and
not reconstructible from mathlib primitives — on the narrowest reading a clean `YES-add-as-is`. The
verdict is `YES-but-generalise-first` because of **grain**: this single identity is meaningless in
isolation. Its entire purpose is to make `ψ₂ₙ/ψₙ` division-free so that
`ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2` can be *defined over a commutative ring* — precisely the `ωₙ`
construction that `Mathlib/.../DivisionPolynomial/Basic.lean` flags as an open TODO, and it lives in
the same fork that discharges the `normEDS`-satisfies-`IsEllDivSequence` TODOs. Shipping
`redInvar_normEDS` alone would put an unmotivated identity in mathlib with no statable RHS (its symbols
don't exist upstream); shipping it as one lemma inside the upstreaming of the parent subsystem (the
`net`/`invar`/`compl₂EDS`/`ω` cluster) is the right move. That bundling + final mathlib naming/location
is a human-judgement call, which is what "generalise first" encodes here.

Two project-hygiene facts the human owner should weigh (they do not change the bucket):
(i) this exact lemma (and its whole apparatus) is **duplicated** in
`HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:997` (verbatim `redInvar_normEDS` +
`_of_mem_nonZeroDivisors` helper) and consumed by `HasseWeil/Auxiliary/DivisionPolynomial.lean:104` —
an AINTLIB intra-repo dedup target; the mathlib upstreaming and the dedup should be coordinated so one
canonical copy is the PR source. (ii) The author of this file is **David Kurniadi Angdinata**, the
mathlib EDS author — so this is almost certainly already on a path toward mathlib; the practical next
action is to confirm the upstreaming plan rather than open a competing PR.

**Reason for the generalisation:** `MODERN-IDIOM`-adjacent **packaging/grain**, not a weakening of
`redInvar_normEDS`'s own hypotheses (it has none to weaken — already maximal and hypothesis-free). The
"more general object" to ship is the parent subsystem (division-free ω + EDS invariant over `CommRing`),
of which `redInvar_normEDS` is one keystone leaf.

**Proposed restatement.** No change to `redInvar_normEDS`'s signature or proof is needed; it is already
mathlib-shaped (note it should be **namespaced** under `EllSequence` when upstreamed — currently it is
a bare top-level name, which would not pass mathlib naming review; the sibling defs `redInvarNum`/
`redInvarDenom` are already in `namespace EllSequence`). The "restatement" is *contextual*: present it
inside the ω/`compl₂EDS`/invariant cluster as the mathlib extension of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`:

```lean
namespace EllSequence
variable {R : Type*} [CommRing R] (b c d : R)

-- (shipped together as the division-free-ω + EDS-invariant subsystem)
def net (p q r s : ℤ) : R := …
def invarNum  (s n : ℤ) : R := …
def invarDenom (s n : ℤ) : R := …
theorem invar_of_net (h : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by …
def redInvarNum   : R := …
def redInvarDenom : R := …

/-- Reduced-invariant identity for a normalised EDS (over any commutative ring). -/
theorem redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by …
end EllSequence
```

Estimated cost of regeneralisation: **CHEAP** for `redInvar_normEDS` itself (verbatim, modulo adding
the `EllSequence.` namespace); the real work is assembling + cleaning the *surrounding* subsystem for a
mathlib PR (MODERATE–EXPENSIVE, but that is the parent-decls' cost, not this leaf's). Cost does **not**
downgrade the verdict.

**Mathlib downstream this enables (required for the generalisation):**
- Completes the **`ωₙ` TODO** in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
  — bivariate ω-division polynomials over a commutative ring, division-free (this identity is the
  division-free hinge).
- Discharges the **`normEDS`-satisfies-`IsEllDivSequence` TODOs** in
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` (lines 44–45) — the divisibility/invariant story
  this subsystem proves.
- Gives mathlib the EDS **invariant** API (`invarNum`/`invarDenom`/`invar_of_net`, "for each `s`,
  `invarNum s n / invarDenom s n` is constant in `n`") that its current EDS file lacks — useful for
  torsion / Nagell–Lutz and Hasse–Weil developments (two AINTLIB projects already consume exactly this).

**Next action:** treat `redInvar_normEDS` as part of the **`net`/`invar`/`compl₂EDS`/`ω` upstreaming
bundle**, not a standalone PR. Concretely: (1) confirm the upstreaming plan with the file's author
(D. K. Angdinata) — plausibly already mathlib-bound; (2) first resolve the **intra-AINTLIB duplication**
(the verbatim HasseWeil copy) so there is one canonical source; (3) run `/mathlibable` on the parent
defs (`net`, `invarNum`, `invarDenom`, `compl₂EDS`, `redInvarNum`, `redInvarDenom`) and the
ω-division-polynomial result to fix the PR grain; (4) then `/generalise` + `/cleanup` the bundle and
open one feat PR (`feat(NumberTheory/AlgebraicGeometry): division-free ω-division polynomials and the
EDS reduced-invariant identity over a commutative ring`). When upstreaming, **namespace the lemma under
`EllSequence`**.

---

## Next step

Treat `redInvar_normEDS` as one keystone leaf of the division-free-ω + EDS-invariant subsystem and
upstream that bundle (coordinating with the mathlib `ωₙ` TODO and the `normEDS`-`IsEllDivSequence`
TODOs, and with the file's mathlib author), **not** as a standalone PR. First deduplicate the verbatim
HasseWeil copy inside AINTLIB, then assess the parent defs to set the PR grain. On upstreaming, add the
`EllSequence.` namespace (the decl is currently a bare top-level name).
