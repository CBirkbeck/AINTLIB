# /mathlibable report — `EllSequence.invarDenom_eq_redInvarDenom_mul`

> Step-9 mathlibable assessment, run from `/overview`. Single declaration.
> Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> Repo: `/Users/mcu22seu/Documents/GitHub/aintlib-main` (AINTLIB consolidation monorepo).

## Verdict: **BORDERLINE-needs-human**

One-line rationale: the *result it serves* (bivariate ωₙ division polynomial) is an explicit
mathlib TODO and belongs upstream, but **this** lemma is an internal bookkeeping step that should
ship as part of the ω construction PR, possibly in a different form — a packaging/taste call.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; reasoning from source — permitted)
- decl `EllSequence.invarDenom_eq_redInvarDenom_mul`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1388`
- qualified name:           **`EllSequence.invarDenom_eq_redInvarDenom_mul`** (VERIFIED: inside
  `namespace EllSequence` opened at line 1356, `variable (b c d)` at 1360, closed at 1431)
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) and construction of normalised
  EDSs from initial terms." Forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` and extends it
  with an `invar`/`redInvar`/`compl₂EDS`/`ω` apparatus absent from mathlib.

---

### Statement (Phase 1)

The exact Lean statement:

```lean
lemma invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c
```

where (same file):
- `invarDenom W s m := W (m + s) * W m * W (m - s)`  (line 145) — so `invarDenom (normEDS b c d) 1 m`
  is `W(m+1)·W(m)·W(m−1)` for the normalised EDS `W = normEDS b c d`, with `W 2 = b`, `W 3 = c`,
  `W 4 = d·b`.
- `redInvarDenom b c d m` (line 1377) is a *reduced denominator*: a 6-way case split on `m % 6`,
  built from `complEDS` (the project's 2-arg `W(n·m)/W(m)` reduction), `normEDS`, and
  `r₆ := normEDS b c d 5 − d² = W₆/(W₃W₂)`. Morally it is `W(m+1)·W(m)·W(m−1)` with the factor
  `W(3)·W(2) = c·b` divided out (an *exact* polynomial division).

Math statement: for a normalised EDS, the triple product `W(m+1)·W(m)·W(m−1)` factors as
(its reduced form) `× W(2) × W(3)`. Equivalently, `W₂W₃ = b·c` divides `W(m+1)W(m)W(m−1)` and the
quotient is the explicit polynomial `redInvarDenom`.

Conclusion (Lean): an equation in `R` (`R` a `CommRing`).
Role: the algebraic certificate that the *reduced* denominator used in defining the bivariate
ω-division-polynomial recombines to the genuine product after multiplying back the cancelled
`W₃W₂ = c·b`. It is consumed in `redInvar_normEDS` (line 1504) and in the ω-recurrence proof
`ω_spec` (`DivisionPolynomialOmega.lean:85`).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (helper / internal algebraic identity).
Reason: not a named theorem, not a `## Main statements` entry, not a new structure — it is one
bookkeeping step inside the construction of `ω`. (Note: it *serves* a BIG result — the ωₙ
construction — but the decl itself is a helper. Literature width was run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → n/a. (The companion `def redInvarDenom` is the
multi-line definition; this is a lemma about it.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                         | Query                                                                                          | Hit? | Standard form found | Notes |
|----|---------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)       | "EDS omega division polynomial Weierstrass W(m+1)W(m)W(m−1) construction"                       | yes  | ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2; ψₙ a normalised EDS | matches mathlib's own ω formula and `ω_spec`; the W(m+1)W(m)W(m−1) triple product is the EDS invariant-denominator, standard (Ward/Silverman) |
| 2  | WebSearch (general form)         | "division polynomials elliptic curve psi phi omega scalar multiplication reduced denominator"   | partial | φₙ, ψₙ, ωₙ families; Pₙ,Qₙ,Vₙ degree bookkeeping | literature treats ωₙ as a polynomial via ψ₂ₙ/ψₙ; no standalone "reduced denominator" lemma surfaced |
| 3  | WebSearch (named-after/aliases)  | (covered by #1: Ward's σ-function formula ψₙ = σ(nz)/σ(z)^{n²}; Silverman AEC division polys)   | yes  | classical EDS / division-polynomial theory | triple product = invariant denominator; the *reduction by W₃W₂* is implementation, not a named result |
| 4  | ChatGPT MCP                      | "Does W(m+1)W(m)W(m−1)=reduced·W(2)W(3) have a name? Would a clean ωₙ need it?"                  | n/a  | —                   | **Codex/Codex-exec FAILED (MCP down, as the task warned). Recorded n/a.** Compensated by WebSearch ×3 + mathlib source + nLab below. |
| 5  | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                         | n/a  | —                   | no references dir for this project on this checkout; recorded n/a |
| 6  | nLab                             | "elliptic divisibility sequence" / "division polynomial"                                        | n/a  | —                   | nLab has no page at the level of this reduction; not a categorical concept |
| 7  | nCatLab (categorical)            | —                                                                                              | n/a  | —                   | not categorical (concrete poly identity) |
| 8  | Stacks Project (alg geom)        | "division polynomial" / "elliptic divisibility"                                                 | n/a  | —                   | Stacks does not cover explicit division-polynomial recurrences / EDS normalisation |
| 9  | MathOverflow / MSE               | "omega division polynomial well-defined polynomial psi_{2n}/psi_n"                              | yes (via #1/#2) | ωₙ integral because ψₙ ∣ ψ₂ₙ | confirms W(m)∣W(2m) and W₃W₂ ∣ triple product are folklore, not separately named |
| 10 | recent arXiv (≤5y)               | arXiv 2503.15428 "Division polynomials for arbitrary isogenies"; 1108.3051 (valuations of div polys) | yes | general isogeny division polys | even modern treatments keep ωₙ via ψ₂ₙ/ψₙ; no isolated "reduced denominator" lemma |

### Literature summary (Phase 3)

Concept identified as: the **invariant denominator of an elliptic divisibility sequence**
(`W(m+1)·W(m)·W(m−1)`), and its **exact division by `W₃·W₂`**, used to realise the bivariate
ω-division-polynomial `ωₙ` (Silverman *AEC*; Ward, *Memoir on EDS*; Stange).
Sources agree on the standard form: **yes** for ωₙ itself (= mathlib's formula); the specific
identity `W(m+1)W(m)W(m−1) = redInvarDenom · W₂W₃` has **no independent name** — it is the
integrality/bookkeeping step *inside* "ωₙ is a polynomial."
Most general standard form: ωₙ for an arbitrary Weierstrass curve over a commutative ring, via the
universal curve and a single exact polynomial division of `ψ₂ₙ` by `ψₙ`.
Generality dimensions where the literature varies: ring of definition (field → comm ring → universal
`ℤ[A₁..A₆]`); whether ωₙ is built by explicit recurrence (this project) or by a one-shot universal
division (the abstraction the literature/mathlib note gesture at).
Disagreement with the literature: none — the project's form is a *correct, more explicit* route to
the standard ωₙ. The `mod 6` case structure is a Lean-implementation artifact, not mathematics.

---

### Generality analysis (Phase 4)

Literature-standard form: ωₙ over an arbitrary Weierstrass curve / commutative ring (the project is
already at `R` a `CommRing`, parametrised by `b c d`, indexed by `m : ℤ` — maximally general on the
ring axis).

| # | Parameter / hypothesis     | Current Lean form        | Literature-standard form  | Weaker exists? | Reason |
|---|----------------------------|--------------------------|---------------------------|----------------|--------|
| 1 | `[CommRing R]` (ambient)   | commutative ring         | commutative ring          | NO             | EDS/division-poly identities are genuinely ring-level; already maximal |
| 2 | `b c d : R`                | the three EDS parameters | curve coefficients        | NO             | intrinsic to normalised EDS / Weierstrass data |
| 3 | `m : ℤ`                    | arbitrary integer        | arbitrary integer         | NO             | already general |
| 4 | shape of statement         | `= redInvarDenom·b·c`    | "W₃W₂ ∣ triple product"   | n/a            | could be a `Dvd` + quotient, but the equational form is what downstream `ω` needs |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on every typeclass/parameter axis.
Weakening opportunities: 0.
The only "generalisation" available is *structural*, not assumption-weakening: replace the explicit
`mod 6` recurrence route with a universal-curve single-division construction of ωₙ (see 4c). That is
a reformulation of the *whole track*, not of this lemma's hypotheses.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream this enables |
|---|----------|----------|------------------------|-------------------------|
| 1 | bundled hyps → typeclasses? | no | — | already typeclass-clean (`CommRing R`) |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity; nothing to filter-ise |
| 3 | construct object → universal-property class? | **yes (track-level)** | define ωₙ via the universal curve `ℤ[A₁..A₆]` + one exact `ψ₂ₙ/ψₙ` division, then specialise — which may *eliminate* `redInvarDenom` and this lemma | a single clean ωₙ API instead of a 6-way `mod 6` apparatus |
| 4 | set+closure → bundled substructure? | no | — | n/a |
| 5 | field/metric → weaken typeclass? | no | — | already at `CommRing` |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general algebraic index? | no | — | `ℤ` index is intrinsic to EDS |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but at the level of the whole `ω` construction, not this lemma.**
A mathlib-grade ωₙ would likely be built via the universal Weierstrass curve and a single polynomial
division (the route the mathlib `DivisionPolynomial/Basic.lean` TODO and the literature both point
at), in which case `redInvarDenom` and `invarDenom_eq_redInvarDenom_mul` could be **restructured or
removed**. This is exactly why the verdict is BORDERLINE rather than YES-add-as-is: the decl is a
correct piece of *one specific* implementation, and whether mathlib wants *this* implementation (vs.
the universal-division one) is a reviewer/taste decision.
Cost: reproving the recurrence the project currently uses — MODERATE/EXPENSIVE, not a mechanical rewrite.
Real mathematical improvement: the universal route gives ωₙ once, cleanly, with no `mod 6` casework.

---

### Mathlib search-status (Phase 5)

Five-method search. (loogle / leansearch / lean-finder indices were **not available** in this
environment; Codex/ChatGPT MCP down. Substituted with exhaustive direct grep over the pinned mathlib
source at `.lake/packages/mathlib/Mathlib/`, plus the WebSearch hit on the official mathlib doc page.)

```
[A] Lean-Finder       n/a — index tool unavailable in this environment
[B] Loogle            n/a — index tool unavailable; substituted source grep (below)
[C] LeanSearch        n/a — index tool unavailable; substituted source grep (below)
[D] Grep mathlib src  invarDenom | redInvarDenom | invarNum | redInvarNum |
                      compl₂EDS | compl₂EDSAux | complEDSAux₂ | "reduced … denom" |
                      "def ω" | WeierstrassCurve.ω | normEDS_six
                      → NO HITS anywhere in mathlib (NumberTheory/EllipticDivisibilitySequence.lean
                        and AlgebraicGeometry/EllipticCurve/DivisionPolynomial/*)
[E] Name pattern      grep for the qualified name + dot-notation → only the project files
```

Searched for both forms:
- user's form (`invarDenom … = redInvarDenom · b · c`): not in mathlib.
- literature-standard form (the ωₙ construction / `ψ₂ₙ/ψₙ` integral division): **mathlib explicitly
  does NOT have it** — `DivisionPolynomial/Basic.lean:71` reads `* TODO: the bivariate polynomials
  ωₙ.` and line 83 `TODO: implementation notes for the definition of ωₙ.` Mathlib defines `ψ`, `φ`,
  `Ψ`, `preΨ`, `ΨSq` but **no `ω`**.

Mathlib's EDS file additionally has a *different* `complEDS` (signature `complEDS b c d k n`, a
4-arg `W(k) ∣ W(n·k)` witness) — NOT the project's 2-arg `complEDS b c d m`. So even the building
block `complEDS` here is a project-specific re-definition, not the mathlib one.

Concluded: **not in mathlib (source-exhausted, both the user's form and the literature-standard ωₙ
form; the latter is an open mathlib TODO).**

---

### Composition check (Phase 6)

#### Call sites — `EllSequence.invarDenom_eq_redInvarDenom_mul` (Phase 6.0)

Internal use count (NagellLutz, excluding declaring lines 1388–1389): **2**
External-to-file callers within the project: **2 distinct files** (plus a sibling-project twin below
as evidence of genuine cross-project reuse).

| Caller file:line | Usage pattern (excerpt) |
|------------------|-------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1504` | `… ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]` (proving `redInvar_normEDS`) |
| `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:85` | `… ψ, invarDenom_eq_redInvarDenom_mul, ω, …` (in `ω_spec`, the defining recurrence of the ω division polynomial) |

Cross-project twin (re-derivation elsewhere): **yes** — `HasseWeil/Auxiliary/
EllipticDivisibilitySequence.lean:877` has a near-identical lemma
`invarDenom_normEDS_eq_redInvarDenom_mul` with the same statement and proof skeleton. Known
consolidation duplicate; for the *mathlibable* question it confirms the result is real and reused.

Inline-derivation grep: no site re-derives `W(m+1)W(m)W(m−1) = redInvarDenom·b·c` by hand instead of
calling the lemma → no bypass.

Composability signal: K = 2 internal uses + a sibling-project twin, no inline bypass → **real API**.
Leans toward a YES-family bucket *for the apparatus*. But (Phase 4c) the apparatus itself is one
implementation among possible ones.

#### Composition attempt (Phase 6a)

Can `invarDenom_eq_redInvarDenom_mul` be derived from *mathlib* in ≤3 calls? **NO.**
- Its statement mentions `redInvarDenom` and the project's `complEDS`/`compl₂EDS` track — **none of
  which exist in mathlib** — so there is nothing to compose against. The proof (lines 1396–1410) is a
  genuine 6-way `split_ifs` over `m % 6`, each branch rewriting via `normEDS_mul_complEDS_div` and
  `normEDS_six_eq_mul` then `ring`. That is a real proof, not a 1–3-call composition.

Conclusion: **NOT-COMPOSABLE** (the building blocks themselves are project-local).

---

## Verdict: `EllSequence.invarDenom_eq_redInvarDenom_mul`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): the *served* result (ωₙ) is standard and is mathlib's own formula; *this*
  identity has no independent name — it is integrality bookkeeping inside "ωₙ is a polynomial".
- Generality (Phase 4): MAXIMALLY GENERAL on all hyps; but Phase 4c flags a track-level
  universal-curve reformulation of ωₙ that could restructure/remove this lemma.
- Mathlib search (Phase 5): not in mathlib; moreover ωₙ itself is an explicit mathlib **TODO**
  (`DivisionPolynomial/Basic.lean:71,83`) — mathlib has `ψ,φ,Ψ` but no `ω`, no `invar`/`redInvar`,
  no `compl₂EDS`.
- Composition (Phase 6): NOT-COMPOSABLE from mathlib (building blocks are project-local); genuinely
  used (2 NagellLutz sites + a HasseWeil twin).

**Rationale.**
This lemma sits at an awkward but important spot. On one hand, the *thing it is part of* — the
bivariate ω division polynomials of a Weierstrass curve — is squarely wanted in mathlib: the mathlib
source literally carries `TODO: the bivariate polynomials ωₙ`. The NagellLutz `invar`/`redInvar`/
`compl₂EDS`/`ω` apparatus, of which this lemma is the integrality certificate, is exactly a discharge
of that TODO, and it is real, sorry-free, and reused (including an independent twin in HasseWeil). So
"throw it away, mathlib has it" is wrong (NO-mathlib-has-it fails — Phase 5 found no ω at all), and
"inline a 3-call mathlib composition" is wrong (NO-composable fails — the building blocks are
project-local). On the other hand, `invarDenom_eq_redInvarDenom_mul` is **not a standalone
mathematical statement**: `redInvarDenom` is an implementation device (a 6-way `m mod 6` split tied
to the `(b,c,d)` normalisation), and this lemma is one bookkeeping step (cancel/restore
`W₃W₂ = c·b`). It is meaningful only bundled with `redInvarDenom`, `compl₂EDSAux`, `redInvar_normEDS`
and the ω definition. Whether it reaches mathlib *as written* depends on a judgment the skill cannot
make: does mathlib want **this** explicit-recurrence construction of ωₙ, or the universal-curve
single-division construction the literature and the mathlib TODO note gesture at (Phase 4c) — which
could eliminate this very lemma? That is a maintainer/taste decision about packaging and approach,
which is the definition of BORDERLINE. It should be decided as part of an ωₙ PR, not for this helper
in isolation.

**Numbered questions for the human (≤4):**
1. Should the whole NagellLutz/HasseWeil `invar`/`redInvar`/`compl₂EDS`/`ω` track be upstreamed to
   mathlib to close the `ωₙ` TODO in `DivisionPolynomial/Basic.lean`? (If yes, this lemma goes with
   it; if no, it stays project-internal.)
2. If upstreaming ωₙ: keep **this explicit `mod 6` recurrence** construction, or rebuild ωₙ via the
   universal curve + a single `ψ₂ₙ/ψₙ` polynomial division (which may remove `redInvarDenom` and this
   lemma entirely)?
3. NagellLutz and HasseWeil currently carry **twin copies** (`invarDenom_eq_redInvarDenom_mul` vs.
   `invarDenom_normEDS_eq_redInvarDenom_mul`). Consolidate to one shared `Common/` lemma first
   (AINTLIB dedup) before any mathlib discussion — agreed?
4. If kept as-is, is the equational form (`= redInvarDenom·b·c`) the desired API, or should mathlib
   instead expose `W₃W₂ ∣ W(m+1)W(m)W(m−1)` (a `Dvd` statement) with `redInvarDenom` as the quotient
   accessor?

**Next action:** answer Q1–Q4 (chiefly Q1/Q2 — the ωₙ-upstreaming approach). Independently of mathlib,
the AINTLIB consolidation step is Q3: dedupe the NagellLutz/HasseWeil twins into one shared lemma.
Then, if upstreaming, treat this lemma as a *line item inside an ωₙ PR*, not a standalone contribution;
re-run `/mathlibable` on the chosen ωₙ formulation.

---

## Provenance / caveats
- Local Lean build was stale (per task); verdict reasoned from source + pinned mathlib tree at
  `.lake/packages/mathlib/`. No `.lean` files were modified.
- ChatGPT/Codex MCP was **down** in this environment (Codex exec failed) — Phase 3 channel #4 recorded
  n/a; compensated with 3 WebSearch queries + direct mathlib-source grep + the official mathlib doc page.
- loogle / leansearch / lean-finder index tools were **not available** here; Phase 5 substituted an
  exhaustive grep over the pinned mathlib source (decisive for an absence result — mathlib has no
  `ω`/`invarDenom`/`redInvarDenom` at all).
