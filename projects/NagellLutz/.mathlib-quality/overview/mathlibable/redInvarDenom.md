# /mathlibable report — `EllSequence.redInvarDenom`

> Step-9 mathlibable assessment (AINTLIB /overview), NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences). Single declaration.
> **Re-assessment 2026-06-21** — supersedes the 2026-06-18 pass. All load-bearing evidence
> re-verified against the vendored mathlib tree; verdict **changed** from `BORDERLINE-needs-human`
> to `YES-but-generalise-first` to align with the twin decl `redInvarNum` (re-assessed same day) —
> see "Why the verdict changed" below.
>
> Environment note: local Lean build is stale (read-only assessment from source). Mathlib-index
> tools (loogle/leansearch) unavailable, so Phase 5 methods [A]–[C] fall back to an **exhaustive
> grep over the vendored mathlib pin** (`.lake/packages/mathlib/`), which is definitive for an
> existence question (the fork's exact upstream is on disk). ChatGPT MCP unavailable — Phase 3
> channel #4 records `n/a`, compensated by WebSearch + arXiv source review + nLab/Stacks/Wikipedia.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale locally (reasoned from source; the decl elaborates in the green `main` build per project state).
- decl `EllSequence.redInvarDenom`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1377` (docstring at 1376).
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms." The file is a substantial **fork/extension** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (mathlib: 547 lines; this file: 1672 lines), authored by **David Kurniadi Angdinata** (the same author as the upstream mathlib EDS + DivisionPolynomial files), adding the `net`/`rel₄`/`invar*`/`redInvar*`/`compl₂EDS`/`ω`-division-polynomial layer on top of the upstream base.

**Qualified-name verification.** The `def` at line 1377 sits inside `namespace EllSequence` (re-opened line 1356, after the earlier `namespace EllSequence … end` block that opened at line 90 / 1079 and closed before). The body returns `R`; it is a plain public `def` (no `private`/`protected`). Confirmed fully-qualified name: **`EllSequence.redInvarDenom`** (the parsed-from-prompt name is correct).

---

### Statement (Phase 1)

`EllSequence.redInvarDenom b c d m` is **a definition** (an `R`-valued function of the EDS seeds `b c d : R` and an index `m : ℤ`). Docstring: *"The expression `W(m+1)·W(m)·W(m−1) / (W₃·W₂)` for a normalised EDS."*

Mathematically: for the normalised EDS `W = normEDS b c d` (with `W₁ = 1`, `W₂ = b`, `W₃ = c`, `W₄ = d·b`), the classical "invariant denominator" is `invarDenom(W,1,m) = W(m+1)·W(m)·W(m−1)` (the denominator of the ratio `invarNum(s,n)/invarDenom(s,n)` that is **constant in `n`** — a genuine EDS invariant, `invar_of_net`). This triple product carries a common factor `W₃·W₂ = c·b`; `redInvarDenom b c d m` is exactly that product **after cancelling `W₃·W₂`**, realised as an honest element of an arbitrary `CommRing R` (no ring division). The companion lemma (line 1388):

```
invarDenom (normEDS b c d) 1 m  =  redInvarDenom b c d m * b * c          -- invarDenom_eq_redInvarDenom_mul
```

Because `b·c` may be a zero-divisor in a general commutative ring, the quotient cannot be taken literally. To stay division-free the body is a **6-way case split on `m mod 6`**, each branch expressing the cancelled quotient as a product of complement-sequence values `complEDS b c d k (...)`, `normEDS b c d (...)`, and the factor `r₆ := normEDS b c d 5 − d²` (`= W₆/(W₃W₂)`):

```
if m % 6 = 0 → r₆ · C 6 (m/6)     · W(m+1) · W(m−1)
if m % 6 = 1 → r₆ · C 6 ((m−1)/6) · W(m+1) · W m
if m % 6 = 5 → r₆ · C 6 ((m+1)/6) · W m     · W(m−1)
if m % 6 = 2 → C 3 ((m+1)/3) · C 2 (m/2)     · W(m−1)
if m % 6 = 4 → C 3 ((m−1)/3) · C 2 (m/2)     · W(m+1)
if m % 6 = 3 → C 3 (m/3)     · C 2 ((m−1)/2) · W(m+1)
else 0          (where C = complEDS b c d, W = normEDS b c d)
```

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring. Already maximal: a bare commutative ring.
- `(b c d : R)` — the three normalised-EDS seeds (`W₂ = b`, `W₃ = c`, `W₄ = d·b`).
- `(m : ℤ)` — the index.

Hypotheses: none (a total `def`; the case split is exhaustive with an `else 0`).

Conclusion (math): the value `W(m+1)W(m)W(m−1)/(W₃W₂)` exhibited as a division-free `R`-element.
Conclusion (Lean): `R` — n/a, this is a definition.

**Downstream role.** `redInvarDenom` is the integral leading term of the **second division polynomial `ω`** (the Y-coordinate numerator of `[n]P` in Jacobian coordinates):
- `NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:74-75` — `protected def W.ω (n) := redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n * … `
- `HasseWeil/.../Auxiliary/DivisionPolynomial.lean:93-94` — the same, in the twin track.

Paired with its numerator twin `redInvarNum` via `redInvar_normEDS` (line 1509):
`redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)`. HasseWeil even proves a dedicated degree bound `natDegree_redInvarDenom_three_le` (`Verschiebung/QthRoots.lean:2459`) about its `m=3` branch.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (substantive helper; BIG-adjacent).
Reason: not a named theorem, not a new mathematical *structure*/typeclass/topology/category, not a person-named result, not a `## Main results` headline. It is an auxiliary `def` — a division-free, index-reduced repackaging of the classical invariant denominator, purpose-built as the leading term of `ω`. It sits next to genuinely BIG content (the division-free `ω` apparatus). (Literature width run EXHAUSTIVE regardless — the surrounding object `ω` is BIG and the protocol forces the wider sweep for the cluster.)

### One-line check (Phase 2b)

Body line count: **6 substantive lines** (a six-branch `if … then … else` chain plus three `letI` bindings).
One-liner verdict: **MULTI-LINE** (kind is `def`; body is a genuine multi-branch `mod 6` case analysis). The Phase-2b one-liner-⇒-NO signal does not apply.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve omega division polynomial second division polynomial Y-coordinate W(m+1)W(m)W(m−1) EDS invariant" | yes (concept) | `ωₙ = (ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)/(4v)`; also `ωₘ = ψ₂ₘ/(2ψₘ)` | Stange eprint 2025/521, Wikipedia EDS, arXiv 1909.12654, MSP ANT. The standard named object is `ω`, **not** a "reduced invariant denominator". |
| 2 | WebSearch (general form) | EDS invariant `W(n+1)W(n)W(n−1)` Ward memoir reduced invariant | **no** | — | Wikipedia EDS / Ward lineage / arXiv 1909.12654. The triple product `W(n+1)W(n)W(n−1)` is the classical invariant denominator, but its **"reduced" (÷W₃W₂), division-free, mod-6-cased** form is not a named literature object. |
| 3 | WebSearch (named-after / Lean) | division polynomial ω defined without division, integral form, normalised EDS, Angdinata mathlib | partial | mathlib prose `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` | identifies the construction context; `ω` is the target, `redInvarDenom` is its leading-term leaf. No literature object named for `redInvarDenom`. |
| 4 | ChatGPT MCP | (standard form / generality / historical evolution of the invariant denominator) | n/a — MCP down per task brief | — | Compensated by WebSearch + direct read of the vendored mathlib source (stronger evidence here — the fork's upstream is literally on disk). |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/`, `refs/` | n/a | — | Directory absent (`No such file or directory`). |
| 6 | nLab | "elliptic divisibility sequence / division polynomial" | no | — | No `redInvarDenom`-style page; only general EDS/division-polynomial mentions. |
| 7 | nCatLab | — | n/a — not a categorical concept | — | A concrete ring-coefficient computation; no categorical content. |
| 8 | Stacks Project | "elliptic curve division polynomial omega" | n/a — not covered | — | Stacks covers the moduli stack (tag 072K/072V), not explicit division-polynomial coordinate formulas. |
| 9 | MathOverflow / MSE | (folded into WebSearch #1–#3) | no | — | No Q/A names this object. |
| 10 | recent arXiv (≤5 yr) | Stange 2025/521 + 2503.15428 ("Division polynomials for arbitrary isogenies"); 1909.12654; 2102.07573 | no | — | These give EDS / `ψ` / `ω` / isogeny division polynomials; none isolates `W(m+1)W(m)W(m−1)/(W₃W₂)` as a reduced, `mod 6`-cased, division-free object. |

### Literature summary (Phase 3)

Concept identified as: the **denominator of the EDS invariant** `invarDenom(W,1,m) = W(m+1)W(m)W(m−1)`, divided through by `W₃W₂` — i.e. an *intermediate quantity inside the construction of the second division polynomial `ω`*. The literature has `ω` itself (`ωₘ = (ψₘ₊₂ψₘ₋₁² − ψₘ₋₂ψₘ₊₁²)/4v`, or `ψ₂ₘ/2ψₘ`) and Ward's invariant theory, but **no standard named object** equal to `redInvarDenom`.
Sources agree on the standard form: **no** — there is no literature-standard form for *this* object; it is a formalisation-driven repackaging. The nearest standard object is `ω`.
Most general standard form: `ω` is well-defined in `R[X,Y]` over any commutative `R` (mathlib's `Basic.lean` docstring, via the universal characteristic-0 ring trick). `redInvarDenom` is already at that maximal generality (arbitrary `CommRing R`).
Generality dimensions where the literature varies: only the base ring — classically a field (char ≠ 2 so `/2ψ` makes sense), modernised (mathlib / this project) to an arbitrary commutative ring via division-free / universal-ring constructions. `redInvarDenom` is on the maximal (arbitrary-`CommRing`) end.
Disagreement with the literature: none — but the object is *below* the literature's granularity. The literature names `ω`; `redInvarDenom` is one of several gears the project built to construct `ω` without ring division.

---

### Generality analysis — `EllSequence.redInvarDenom`

Literature-standard form (from Phase 3): there is no literature object at this granularity; the enclosing literature object is `ω`, stated for an arbitrary commutative ring in the modern (mathlib) treatment.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]` | arbitrary commutative ring | (for `ω`) arbitrary commutative ring | **NO** | already maximal; `normEDS`/`complEDS` and the whole EDS layer live over `CommRing`. Cannot weaken to non-commutative or to semiring: subtractions (`m − 1`, `r₆ = W₅ − d²`) and the `W₃W₂` cancellation all need additive inverses + commutativity. |
| 2 | `(b c d : R)` | three ring seeds | `ψ₂, ψ₃, preΨ₄` initial data | NO | these are exactly the normalised-EDS seeds; no slack. |
| 3 | `(m : ℤ)` | integer index | integer index | NO | EDS are ℤ-indexed by definition; the `mod 6` / `/2` / `/3` arithmetic is ℤ-specific. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (arbitrary `CommRing R`; the modern, division-free formulation already matches the most general base mathlib uses for the surrounding `ψ`/`Φ`/`ΨSq` family).
Number of weakening opportunities found: **0**.
Proposed restatement: none required on generality grounds.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | bundled-hypotheses → typeclasses? | no | — | parameters are ring elements, not a "let X be a foo" preamble. |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic; no limits/topology. |
| 3 | construction → universal-property class? | no | — | `redInvarDenom` itself *supports* the universal-ring proof of `ω`; it is not a universal property to abstract. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no substructure. |
| 5 | field/metric-specific → weaken typeclasses? | no | already `CommRing` | the modernisation (division-free over arbitrary `CommRing`) is *already applied* — that is the entire reason the `mod 6` split + `redInvarDenom`/`redInvarNum` exist instead of `ω = ψ₂ₘ/2ψₘ`. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general additive structure? | no | `m : ℤ` is intrinsic | EDS are ℤ-indexed; the `mod 6` arithmetic is ℤ-specific. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — the contemporary mathlib idiom (division-free construction over an arbitrary commutative ring, via a `mod`-cased complement-sequence repackaging) is *already what `redInvarDenom` is*. There is nothing more idiomatic to migrate to; this object is itself the idiom-level plumbing.

---

### Diamond / defeq risk — `EllSequence.redInvarDenom` (Phase 4.5, kind = `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | not an instance; introduces no typeclass-search path. Plain `def` returning `R`. |
| 2 | Reducibility leak | none | not `@[reducible]`; sealed. Unfolded explicitly only in the small base-case `simp` lemmas. |
| 3 | Non-canonical unfolding | low | `@[simp] redInvarDenom_{zero,one,two}` are the controlled API; the def is unfolded only behind `split_ifs` in `invarDenom_eq_redInvarDenom_mul` (source comments it "slow"). No surprising auto-unfold. |
| 4 | Instance priority collision | none | not an instance. |
| 5 | Universe-polymorphism issues | none | single universe `u` for `R`; no forced annotations. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE / LOW**. No HIGH rows. The existing `@[simp]` base-case lemmas already give a clean unfolding API.

---

### Mathlib search-status: `EllSequence.redInvarDenom`

Performed by direct grep over the on-disk vendored mathlib tree `.lake/packages/mathlib/Mathlib/` (the fork's actual upstream), plus name/concept search. Stronger than Loogle/LeanSearch here because the question is precisely "is this object in *this* mathlib pin?" and the pin is present locally.

[A] Lean-Finder       n/a (offline) — substituted by direct source grep below.
[B] Loogle            n/a (offline) — substituted by direct source grep below.
[C] LeanSearch        n/a (offline) — substituted by direct source grep below.
[D] Grep mathlib src  `redInvarDenom|redInvarNum|invarDenom|invarNum|invar_of_net|compl₂EDS|compl₂EDSAux|def ω|\.ω\b` over the whole mathlib tree
    - `redInvar*` in mathlib:            **0 hits** (re-verified 2026-06-21; definitive)
    - `invarDenom` / `invarNum` / `invar_of_net` in mathlib:  **0 hits**
    - `compl₂EDS` / `compl₂EDSAux` in mathlib:  **0 hits**
    - `complEDS` in mathlib:  hits — but it is the **upstream base sequence** (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:427`, `complEDS b c d k n`), the thing `redInvarDenom` is *built from*, not `redInvarDenom` itself. (The project even ships its own variant `EllSequence.complEDS b c d m` at line 1568.)
    - `def ω` (the y-coordinate division polynomial) in mathlib:  **0 hits** — all `ω` matches are unrelated (`LucasLehmer.ω`, `OmegaCompletePartialOrder.ωSup`, `CategoryTheory …ω₁/ω₂`, RootSystem `ω`). Mathlib's `DivisionPolynomial/Basic.lean` *describes* `ωₙ` in its docstring (line 30) but **lists it as an open TODO** (line 71 "TODO: the bivariate polynomials `ωₙ`"; line 83 "TODO: implementation notes for the definition of `ωₙ`"). The actual `def ω` exists only in the projects (`DivisionPolynomialOmega.lean:74`, HasseWeil `Auxiliary/DivisionPolynomial.lean:93`).
[E] Name pattern      mathlib EDS def list: `IsEllSequence, IsDivSequence, IsEllDivSequence, preNormEDS'/preNormEDS, complEDS₂, normEDS, normEDSRec'/normEDSRec, complEDS'/complEDS` → **no invariant / reduced-invariant / compl₂EDS family at all**.

Searched for both:
  - the user's current form (`redInvarDenom`) — **not in mathlib**;
  - the enclosing literature-standard form (`ω`, the second division polynomial) — **also not in mathlib**, and **explicitly flagged as a TODO** there.

Concluded: **not in mathlib**, and the consuming object `ωₙ` it serves is an **acknowledged-missing** upstream item. Building blocks `normEDS`/`complEDS` are upstream; the `invar*`/`redInvar*`/`ω` layer is entirely the project's extension. (Intra-AINTLIB: `redInvarDenom` is *also* defined in `HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:866` — a parallel-track duplicate, not a mathlib hit.)

---

### Call sites — `EllSequence.redInvarDenom`

Internal use count (NagellLutz, excluding the declaring file): the `redInvarDenom` API (def + `_zero/_one/_two` + `map_redInvarDenom` + `redInvar_normEDS`) is consumed by:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:75` | `redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n * …` — **leading term of `def W.ω`** |
| `NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:85,112` | `… invarDenom_eq_redInvarDenom_mul …`, `… map_redInvarDenom …` (ω correctness + ring-hom transport) |
| `NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1502,1509` | `redInvar_normEDS`: `redInvarNum = redInvarDenom · (d + b^4)` (the reduced-invariant factor identity) |

Cross-project (same Lake workspace — genuine `import` consumers):

| Caller file:line | Usage pattern |
|------------------|----------------|
| `HasseWeil/.../Auxiliary/DivisionPolynomial.lean:94,105,117,121,138,352` | builds `W.ω` from `redInvarDenom …`; `redInvarDenom_{zero,one,two}` base cases; `map_redInvarDenom` |
| `HasseWeil/.../Verschiebung/QthRoots.lean:964, 2455-2473` | `rw [WeierstrassCurve.ω, redInvarDenom_two, …]`; a dedicated `natDegree_redInvarDenom_three_le` degree-bound theorem about the `m=3` branch |

Inline-derivation grep: the equivalent quantity is **not** re-derived inline elsewhere — consumers always go through `redInvarDenom` (+ its `invarDenom_eq_redInvarDenom_mul` bridge). The multiple *definitions* across files are the project's forked-track duplication, not bypass.

**Signal:** K ≥ 3 internal + cross-project uses, no inline bypass → **real, depended-upon API** (the leading term of `WeierstrassCurve.ω`, with its own degree lemma downstream). Strong "keep it" signal; not dead code. The only NO direction is "mathlib already has it / composes it", which Phase 5–6 rule out. (Note: `redInvarDenom` is *more* directly depended-upon than its numerator twin `redInvarNum`, which has K=0 direct uses.)

### Composition check (Phase 6)

Can `EllSequence.redInvarDenom` be reproduced from mathlib in ≤3 chained calls?

Attempt 1: define it as `invarDenom (normEDS b c d) 1 m` divided by `b*c`.
  - Mathlib decls available: `normEDS` (yes). `invarDenom` — **not in mathlib** (the `invar*` layer is the project's). Ring division by `b*c` — not available in an arbitrary `CommRing` and is *exactly what the whole construction exists to avoid*.
  - Result: **fails**. Reconstructing it from `normEDS` alone requires the `mod 6` case analysis plus the complement-sequence identities (`normEDS_mul_complEDS_div`), which is the multi-`rw`/`ring` proof of `invarDenom_eq_redInvarDenom_mul` — a real proof, not a composition.

Attempt 2: as the literature `ω`-denominator `ψₘ₊₂ψₘ₋₁² − …` divided through.
  - Mathlib has neither `ω` nor `invarDenom`, and again this needs division. Fails for the same reason.

Conclusion: **NOT-COMPOSABLE**. No ≤3-mathlib-call expression exists; the building blocks above `normEDS`/`complEDS` (`invarDenom`, the reduced cancellation, the `mod 6` split, `r₆`) are all project-local, and the defining identity is a genuine `split_ifs … ring` proof.

---

## Why the verdict changed (2026-06-18 → 2026-06-21)

The 2026-06-18 pass landed **BORDERLINE-needs-human**, on the ground that whether this exact `def` belongs in mathlib hinges on *how `ω` is eventually upstreamed* and *whether the `mod 6` division-free decomposition is the formulation mathlib's curve-author wants*. The same-day re-assessment of the **numerator twin `redInvarNum`** surfaced two load-bearing facts that resolve that hinge and were not weighed in the 18-Jun `redInvarDenom` pass:

1. **The consuming object `ωₙ` is an explicit mathlib TODO**, not merely absent: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines `ωₙ` in prose (line 30) and flags it as open (line 71 "TODO: the bivariate polynomials `ωₙ`"; line 83). So the upstreaming target is a *documented mathlib want*, and `redInvarDenom` is the **leading term** of it — i.e. directly enabling a known gap, not speculative.
2. **The file's author is David Kurniadi Angdinata**, the mathlib EDS / DivisionPolynomial author — so this apparatus is plausibly already on a path to mathlib; the practical question is "confirm the upstreaming plan", not "is this wanted".

Given (1)+(2), the BORDERLINE questions are answered in the affirmative direction, and the correct call matches the twin: ship as part of the division-free-ω bundle. Holding `redInvarDenom` at BORDERLINE while its co-defined numerator `redInvarNum` is `YES-but-generalise-first` would be an inconsistent split of one numerator/denominator pair (joined by `redInvar_normEDS`). Hence the verdict is brought into line: **YES-but-generalise-first**.

---

## Verdict: `EllSequence.redInvarDenom`

**Category:** `YES-but-generalise-first`

> Bucket nuance: the *definition itself is already maximally general* (Phase 4b: MAXIMALLY GENERAL,
> 0 weakenings; Phase 4c: no modern-idiom upgrade). Standing alone on its own hypotheses it would read
> `YES-add-as-is`. It lands in **YES-but-generalise-first** for a *packaging/grain* reason: `redInvarDenom`
> is one cog in a self-contained subsystem (`invarNum`, `invarDenom`, `compl₂EDS`, `compl₂EDSAux`,
> `redInvarNum`, `redInvarDenom`, `complEDS`, and the `ω`/`ψc` division polynomials) that fills the
> **mathlib `ωₙ` TODO**. The correct mathlib contribution is that whole division-free-`ω` apparatus as a
> coherent extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence` + `…/DivisionPolynomial/Basic.lean`,
> **not** `redInvarDenom` as an isolated PR. "Generalise first" here = "ship as part of the parent-subsystem
> upstreaming, named/located to mathlib conventions" — the human-judgement step.

**Evidence:**
- Literature search (Phase 3): no named "reduced invariant denominator" in Ward/Stange/Silverman/Sutherland; the classical EDS *invariant* (`invarNum`/`invarDenom`) is standard, but the *reduced, division-free, mod-6-cased* form is a formalisation-engineering device. The enclosing named object is the second division polynomial `ω` (`ωₘ = (ψₘ₊₂ψₘ₋₁² − ψₘ₋₂ψₘ₊₁²)/4v`).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `[CommRing R]` (above the literature's field form); 0 weakenings; no modern-idiom upgrade (the division-free repackaging *is* the modern idiom).
- Mathlib search (Phase 5): **not in mathlib** — neither `redInvarDenom` nor `invarDenom`/`invar*`/`compl₂EDS`, nor even the enclosing `ω` (mathlib's `DivisionPolynomial` stops at `ψ/Φ/ΨSq`); the consuming object `ωₙ` is an explicit mathlib **TODO** (`Basic.lean:71,83`). Building blocks `normEDS`/`complEDS` are upstream.
- Composition check (Phase 6): **NOT-COMPOSABLE** (no ≤3-call mathlib expression; the defining identity is a real `split_ifs … ring` proof). Call-sites: real cross-project API — it is the **leading term of `WeierstrassCurve.ω`**, with a dedicated degree lemma `natDegree_redInvarDenom_three_le` in HasseWeil.

**Rationale.**
`redInvarDenom` is genuinely missing from the pinned mathlib (the whole `invar*`/`redInvar*`/`ω` layer is the project's extension of the upstream EDS file), correctly stated at the maximal (commutative-ring) generality, and not reconstructible from mathlib primitives — its building blocks (`invarDenom`, the `mod 6` cancellation, `r₆`) are themselves project-only and the literal `÷(b·c)` quotient is exactly what the construction exists to avoid. On the narrowest reading those facts are a clean `YES-add-as-is`. The verdict is `YES-but-generalise-first` rather than `YES-add-as-is` for **grain**: this `def` is the leading term of `ω` and is meaningless shipped alone. Its entire purpose is to make the Y-coordinate division polynomial *division-free over a commutative ring* — precisely the `ωₙ` construction that `Mathlib/.../DivisionPolynomial/Basic.lean` flags as an open TODO. Shipping `redInvarDenom` alone would put an unmotivated helper in mathlib with no consumer; shipping it as one declaration inside the upstreaming of the parent `compl₂EDS`/`invar`/`ω` cluster (jointly with its numerator twin `redInvarNum`, to which it is bound by `redInvar_normEDS`) is the right move. That bundling + final mathlib naming/location is the human-judgement call "generalise first" encodes.

Two project-hygiene facts the human owner should weigh (they do not change the bucket):
(i) this exact apparatus is **duplicated** in `HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:866` (verbatim `redInvarDenom`, `redInvarDenom_{zero,one,two}`, `map_redInvarDenom`, plus its own `ω` track) — an AINTLIB intra-repo dedup target; the mathlib upstreaming and the dedup should be coordinated so one canonical copy is the PR source.
(ii) The author of this file is **David Kurniadi Angdinata**, the mathlib EDS author — so this is almost certainly already on a path toward mathlib; the practical next action is to confirm the upstreaming plan rather than open a competing PR.

**Reason for the generalisation:** `MODERN-IDIOM`-adjacent **packaging/grain**, not a weakening of `redInvarDenom`'s own hypotheses (those are already maximal). The "more general object" to ship is the parent subsystem (division-free `ω` over `CommRing`), of which `redInvarDenom` is the leading-term leaf.

**Proposed restatement.** No change to `redInvarDenom`'s signature or proof is needed; it is already mathlib-shaped. The "restatement" is *contextual* — present it (with `redInvarNum`, `invarNum`, `invarDenom`, `compl₂EDS`, `compl₂EDSAux`) inside the `ω`/`compl₂EDS` cluster as the mathlib extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence`:

```lean
namespace EllSequence
variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)

-- (shipped together as the division-free-ω subsystem)
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)
/-- `W(m+1)·W(m)·W(m−1) / (W₃·W₂)` for a normalised EDS, division-free (mod-6 case split). -/
def redInvarDenom : R := …
theorem invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by …
end EllSequence
```

Estimated cost of regeneralisation: **CHEAP** for `redInvarDenom` itself (verbatim); the real work is assembling + cleaning the *surrounding* subsystem for a mathlib PR (MODERATE–EXPENSIVE, but that is the parent decls' cost, not this leaf's). Cost does **not** downgrade the verdict.

**Mathlib downstream this enables (required for the generalisation):**
- Completes the **`ωₙ` TODO** in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` — `redInvarDenom` is the integral leading term of `ωₙ`, so it is on the critical path for the bivariate ω-division polynomials over a commutative ring, division-free.
- Gives mathlib the EDS **invariant** API (`invarNum`/`invarDenom` + "`invarNum s n / invarDenom s n` is constant in `n`") its current EDS file lacks — useful for torsion / Nagell–Lutz and Hasse–Weil (two AINTLIB projects already consume it).

**Next action:** treat `redInvarDenom` as one leaf (the `ω`-denominator) of the **`compl₂EDS`/`invar`/`ω` upstreaming bundle**, jointly with its numerator twin `redInvarNum`, not as a standalone PR. Concretely: (1) confirm the upstreaming plan with the file's author (D. K. Angdinata) — plausibly already mathlib-bound; (2) first resolve the **intra-AINTLIB duplication** (the HasseWeil copy) so there is one canonical source; (3) run `/mathlibable` on the parent defs (`invarDenom`, `compl₂EDS`, `compl₂EDSAux`, `invarNum`) and the `ω`-division-polynomial result to fix the PR grain; (4) then `/generalise` + `/cleanup` the bundle and open one feat PR (`feat(NumberTheory/AlgebraicGeometry): division-free ω-division polynomials and the EDS reduced invariant over a commutative ring`).

---

## Next step

Treat `EllSequence.redInvarDenom` as the ω-denominator leaf of the division-free-ω subsystem and upstream that bundle (coordinating with the mathlib `ωₙ` TODO and the file's mathlib author), not as a standalone PR. First deduplicate the parallel HasseWeil copy inside AINTLIB, then assess the parent defs to set the PR grain.

---

### Sources
- Stange, "Division Polynomials for Arbitrary Isogenies" — https://eprint.iacr.org/2025/521.pdf and https://arxiv.org/pdf/2503.15428
- "Sequences associated to elliptic curves" — https://arxiv.org/pdf/1909.12654
- "A recurrence relation for elliptic divisibility sequences" — https://arxiv.org/pdf/2102.07573
- Elliptic divisibility sequence — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- mathlib (vendored pin): `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`; `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (ωₙ TODO, lines 30/71/83)
