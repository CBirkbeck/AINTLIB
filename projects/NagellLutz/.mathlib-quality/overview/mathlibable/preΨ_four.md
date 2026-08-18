# /mathlibable report — `WeierstrassCurve.preΨ_four`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).

---

## Baseline (Phase 0)

- lake build:               not run (local build stale per task brief; reasoning from source + mathlib tree on pin `d90090f`)
- decl `WeierstrassCurve.preΨ_four`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:141`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  *"This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."*

**Verified qualified name:** `WeierstrassCurve.preΨ_four` (base name `preΨ_four`, inside
`namespace WeierstrassCurve`). The parsed name in the task brief is correct.

Exact source (lines 140–142):

```lean
@[simp]
lemma preΨ_four : W.preΨ 4 = W.preΨ₄ :=
  preNormEDS_four ..
```

---

## Statement (Phase 1)

`WeierstrassCurve.preΨ_four` is a **boundary/initial-value lemma** for the auxiliary
("pre") univariate division polynomials of a Weierstrass curve `W` over a commutative
ring `R`. It states that the value of the integer-indexed family `preΨ` at `n = 4`
equals the explicitly-given degree-6 polynomial `preΨ₄`.

Mathematically: the `n`-division polynomials `ψₙ` of an elliptic curve satisfy
`ψ₄ = ψ₂ · preΨ₄` where
`preΨ₄ = 2x⁶ + b₂x⁵ + 5b₄x⁴ + 10b₆x³ + 10b₈x² + (b₂b₈ − b₄b₆)x + (b₄b₈ − b₆²)`.
The family `preΨ : ℤ → R[X]` is built as a (pre-)normalised elliptic divisibility
sequence `preNormEDS (Ψ₂Sq²) Ψ₃ preΨ₄`, whose value at the seed index 4 is, by the
EDS construction, exactly its fourth generator `preΨ₄`. This lemma records that
boundary identity.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (`W.preΨ`, `W.preΨ₄` are its fields/defs).

Hypotheses: none.

Conclusion (math): `preΨ` evaluated at 4 is the explicit polynomial `preΨ₄`.

Conclusion (Lean): `W.preΨ 4 = W.preΨ₄`.

Proof: `preNormEDS_four ..` — the EDS boundary lemma `preNormEDS b c d 4 = d`
applied through the `def preΨ (n) := preNormEDS (W.Ψ₂Sq^2) W.Ψ₃ W.preΨ₄ n`. One step,
definitional.

---

## Size classification (Phase 2a)

Verdict: **SMALL**

Reason: a one-step `@[simp]` boundary lemma evaluating a recursively-defined family at
a fixed small index; not a named theorem, not a new structure, not a project main result.

(Literature width run EXHAUSTIVE regardless; recorded SMALL for framing only.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**.
(For the record the body is a single term `preNormEDS_four ..`; this is a glue lemma —
see verdict.)

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve psi_4 four-division polynomial recurrence Weierstrass" | yes | `ψ₄ = ψ₂·(2x⁶ + b₂x⁵ + 5b₄x⁴ + 10b₆x³ + 10b₈x² + (b₂b₈−b₄b₆)x + (b₄b₈−b₆²))` | Standard `ψ₄` factorisation; the second factor is exactly `preΨ₄`. Multiple arXiv refs (1108.3051, 1303.4327, 2102.07573). |
|  2 | WebSearch (general form / EDS)   | (same query, EDS recurrence sources) | yes | EDS recurrence `ψ_{2m+1}`, `ψ₂ψ_{2m}` initial terms `ψ₁,ψ₂,ψ₃,ψ₄` | arXiv 2102.07573 "A recurrence relation for elliptic divisibility sequences" — confirms `ψ₄` as a seed term. |
|  3 | WebSearch (mathlib / named-after)| "mathlib WeierstrassCurve preΨ division polynomial formalization Angdinata" | yes | `WeierstrassCurve.preΨ` family in mathlib | leanprover-community mathlib4_docs DivisionPolynomial/Basic; Angdinata–Xu ITP 2023. **Confirms this exact API is mathlib's.** |
|  4 | ChatGPT MCP                      | n/a | n/a | — | MCP flagged possibly-down in brief; **not needed** — Phase 5 establishes byte-identical mathlib source, which is conclusive far beyond what a second opinion adds. |
|  5 | Local references                 | `.mathlib-quality/references/` (NagellLutz) | n/a | — | No references dir consulted; the mathlib source identity makes literature-standard-form moot. |
|  6 | nLab                             | "division polynomial" | n/a | — | nLab has no dedicated division-polynomial entry; concept is classical, well-covered by #1–#3; the verdict does not turn on the standard form. |
|  7 | nCatLab                          | — | n/a | — | Not a categorical concept. |
|  8 | Stacks Project                   | — | n/a | — | Division polynomials of a fixed Weierstrass model are not a Stacks-level scheme-theoretic concept; n/a. |
|  9 | MathOverflow / MSE              | division polynomial ψ₄ explicit | n/a (covered) | — | The explicit `ψ₄`/`preΨ₄` formula is textbook (Silverman, *AEC* Ex. 3.7); #1 already returns it. |
| 10 | recent arXiv (≤5y)              | (covered by #1–#2) | yes | EDS/division-polynomial recurrences | 2102.07573 (2021), eprint 2025/521 (Stange) — `ψ₄` is a standard seed term. |

### Literature summary (Phase 3)

Concept identified as: **the 4th (auxiliary/pre-) division polynomial of a Weierstrass curve**,
i.e. the cofactor in `ψ₄ = ψ₂·preΨ₄`; equivalently the 4th seed of the normalised EDS.

Sources agree on the standard form: **yes** — `preΨ₄ = 2x⁶ + b₂x⁵ + 5b₄x⁴ + 10b₆x³ + 10b₈x² + (b₂b₈−b₄b₆)x + (b₄b₈−b₆²)` is the standard `ψ₄` cofactor (Silverman, and the project/mathlib `preΨ₄` def matches it term-for-term).

Most general standard form: over an arbitrary commutative ring `R` (the `bᵢ` are integer
polynomials in the `aᵢ`), as a polynomial identity — which is **exactly** the Lean form.

Generality dimensions where the literature varies: none that bear on this lemma — it is a
fixed polynomial identity, already at full `CommRing R` generality.

Disagreement with the literature: none.

---

## Generality analysis — `WeierstrassCurve.preΨ_four`

Literature-standard form (Phase 3): polynomial identity `preΨ(4) = preΨ₄` over any `CommRing R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (`bᵢ` ∈ ℤ[aᵢ]) | NO | The seed/boundary identity holds verbatim over any `CommRing`; this is already maximal. Mathlib states the same lemma at the same generality. |
| 2 | index `4` | the literal `(4 : ℤ)` | the seed index 4 | NO | The lemma *is* the boundary case at 4; generalising the index gives the (separate) recurrence lemmas `preΨ_even`/`preΨ_odd`, which already exist alongside it (project lines 148–156; mathlib 225–233). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Cost of restatement: n/a — already maximal and identical to mathlib's.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | bundled-hyp → typeclass? | no | — | No bundled "let X be a foo" preamble; `W` is already a structure. |
| 2 | sequences/metric → filters/topology? | no | — | Pure polynomial identity; nothing to filter-ise. |
| 3 | construction → universal-property class? | no | — | A concrete boundary value, not a constructed object. |
| 4 | set+closure → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclass? | no | — | Already at `CommRing`, the natural floor (needs `+`,`*`,`b₈ = b₂b₆/... ∈ ℤ[aᵢ]`). |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general index? | no | — | This is *the* index-4 boundary case; the index-general statements are the separate recurrence lemmas (which mathlib already has). |

#### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite polynomial seed-value identity, already
stated in mathlib's own contemporary `preΨ`/`preNormEDS` formulation. There is no
organisational improvement to make — the project lemma is a verbatim copy of that very
formulation.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `WeierstrassCurve.preΨ_four`

[A] Lean-Finder       n/a (mathlib index tool) — superseded by direct source hit below
[B] Loogle            n/a — superseded by direct source hit below
[C] LeanSearch        "preΨ four division polynomial Weierstrass" → routes to DivisionPolynomial.Basic (confirmed via mathlib4_docs WebSearch #3)
[D] Grep mathlib src  `grep -n "preΨ_four\|preNormEDS_four\|def preΨ"` over `.lake/packages/mathlib/.../DivisionPolynomial/Basic.lean` → **DIRECT HIT** (see below)
[E] Name pattern      `WeierstrassCurve.preΨ_four` → exact qualified-name match in mathlib

Searched for both the user's current form and the literature-standard form — they coincide,
and **both are present in mathlib verbatim**.

### The decisive finding — byte-for-byte identity

Mathlib (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`, lines 217–219):

```lean
@[simp]
lemma preΨ_four : W.preΨ 4 = W.preΨ₄ :=
  preNormEDS_four ..
```

This is **identical** — same name `WeierstrassCurve.preΨ_four`, same `@[simp]`, same
statement, same proof term — to the project lemma at `DivisionPolynomial.lean:141`.

The supporting defs are identical too:
- `def preΨ (n : ℤ) := preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` — mathlib `Basic.lean:194–195` == project `DivisionPolynomial.lean:117–118` (verbatim).
- `def preΨ₄ := 2*X^6 + C b₂*X^5 + 5*C b₄*X^4 + 10*C b₆*X^3 + 10*C b₈*X^2 + C (b₂b₈−b₄b₆)*X + C (b₄b₈−b₆²)` — mathlib `Basic.lean:147–149` == project `DivisionPolynomial.lean:70–72` (verbatim).
- underlying glue `lemma preNormEDS_four : preNormEDS b c d 4 = d` — mathlib `NumberTheory/EllipticDivisibilitySequence.lean:202` == project `LutzNagell/EllipticDivisibilitySequence.lean:800` (verbatim).

Both files carry the same header: *Copyright (c) 2024 David Kurniadi Angdinata … Authors:
David Kurniadi Angdinata.* The project file's module docstring states outright it **is a
copy** of the mathlib file, forked only to import the project's local
`EllipticDivisibilitySequence` (to dodge a `normEDS`/`complEDS` name clash) — **not**
because the lemma is new.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ_four`; identical form** (same
namespace, same statement, same proof, same author).

---

## Call sites — `WeierstrassCurve.preΨ_four`

Internal use count (project, excluding declaring file): **3** (all `@[simp]`-set/`simp only [...]` mentions; 1 prose-comment mention not counted)
External-to-file callers: **1 distinct file** — `projects/HasseWeil/HasseWeil/OmegaPullbackCoeff.lean`

| Caller file:line | Usage pattern |
|------------------|---------------|
| HasseWeil/OmegaPullbackCoeff.lean:293 | `simp only [… WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two, WeierstrassCurve.preΨ_four]` |
| HasseWeil/OmegaPullbackCoeff.lean:349 | `simp only [… WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four]` |
| HasseWeil/OmegaPullbackCoeff.lean:405 | `simp only [… WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four]` |

Inline-derivation grep: (none — the identity is never re-derived by hand; callers use it as the named `@[simp]` rewrite).

**Composability signal.** ≥3 external `simp`-set uses → it is real API. But that does *not*
push toward a YES bucket here, because the API it provides **already exists in mathlib under
the identical qualified name**. Note: those HasseWeil call sites resolve to whichever
`WeierstrassCurve.preΨ_four` is in scope; once the NagellLutz fork drops the copy and the
project depends on mathlib's, the identical name keeps every call site compiling unchanged.

---

## Composition check (Phase 6)

Can `WeierstrassCurve.preΨ_four` be derived from mathlib in ≤3 chained calls?

Attempt 1: `preNormEDS_four ..` (mathlib's own `EllipticDivisibilitySequence.preNormEDS_four`,
unfolding `WeierstrassCurve.preΨ`).
- Mathlib decls used: `preNormEDS_four`, `WeierstrassCurve.preΨ` (def).
- Result: **succeeds** — this is literally mathlib's own proof, one call.

Conclusion: **the result is not merely composable — it is present verbatim.** Composition
is moot: NO-mathlib-has-it dominates (we don't compose what already exists under the same
name). For completeness it is a 1-call derivation from mathlib's `preNormEDS_four`.

---

## Verdict: `WeierstrassCurve.preΨ_four`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard `ψ₄ = ψ₂·preΨ₄` cofactor; mathlib4_docs confirms the `preΨ` API is mathlib's (Angdinata–Xu).
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom move (it already *is* mathlib's contemporary form).
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.preΨ_four`; byte-for-byte identical** (`DivisionPolynomial/Basic.lean:217–219`), incl. identical supporting defs and underlying `preNormEDS_four`.
- Composition check (Phase 6): NOT-COMPOSABLE-relevant — it exists verbatim; trivially also a 1-call derivation.

**Rationale:**

The project lemma is a verbatim copy of an existing mathlib declaration — same qualified
name (`WeierstrassCurve.preΨ_four`), same `@[simp]` statement `W.preΨ 4 = W.preΨ₄`, same
one-line proof `preNormEDS_four ..`, same author (Angdinata, 2024). The entire file
`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` is, by its own module docstring, "a
copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked solely so
it imports the project's local `EllipticDivisibilitySequence` (which redefines `normEDS` /
`complEDS`) instead of mathlib's. The fork is a build/namespace workaround inside this
consolidation monorepo, not a new contribution: the surrounding `preΨ`, `preΨ₄` defs and the
underlying `preNormEDS_four` glue lemma are likewise identical to mathlib's. There is nothing
to upstream — mathlib has had this since the original Angdinata–Xu division-polynomial PR.

**WHY not (refactor-actionable):**
Mathlib already has it, verbatim, under the same name. The NagellLutz `DivisionPolynomial.lean`
exists only to break the local `normEDS`/`complEDS` name clash with the project's forked
`EllipticDivisibilitySequence`. The right long-term fix is to delete the whole fork and have
the project reuse mathlib's `DivisionPolynomial.Basic` once the `EllipticDivisibilitySequence`
divergence is reconciled (e.g. upstream the project's EDS additions or rename them) — at which
point `preΨ_four` and its siblings simply come from mathlib.

- Existing mathlib decl:  `WeierstrassCurve.preΨ_four`
- Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:218`
- Our form follows in 0 lines — it *is* the same decl:
  ```lean
  example : W.preΨ 4 = W.preΨ₄ := WeierstrassCurve.preΨ_four
  ```
- Call sites in our project (Phase 6.0): **3** (all in `HasseWeil/OmegaPullbackCoeff.lean`, as `simp` lemmas).
- Refactor plan: this is a fork-level dedup, not a per-call-site edit. Track it as a
  *cleanup* concern for the NagellLutz ↔ mathlib `DivisionPolynomial`/`EllipticDivisibilitySequence`
  divergence. Steps: (1) reconcile the project's `LutzNagell/EllipticDivisibilitySequence.lean`
  with mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` (the `normEDS`/`complEDS`
  clash is the only stated reason for the fork); (2) drop `LutzNagell/DivisionPolynomial.lean`
  in favour of `import Mathlib.…DivisionPolynomial.Basic`; (3) the 3 HasseWeil `simp only [… preΨ_four]`
  call sites need **no change** — the qualified name is identical, so they resolve to mathlib's
  lemma automatically. Do **not** delete the lemma in isolation while the fork stands, or the
  copy's siblings (`preΨ_three`, `ΨSq_*`, etc.) lose their neighbour and the file breaks.
- Next action: file/keep an AINTLIB *cleanup-dedup* ticket on the NagellLutz division-polynomial
  fork vs. mathlib (the whole file, not this lemma alone).

---

## Next step

File/keep an AINTLIB cleanup-dedup ticket targeting the NagellLutz
`LutzNagell/DivisionPolynomial.lean` (+ `EllipticDivisibilitySequence.lean`) fork: reconcile
the local EDS divergence with `Mathlib.NumberTheory.EllipticDivisibilitySequence`, then
replace the forked `DivisionPolynomial.lean` with `import
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. The 3 `preΨ_four` call
sites in HasseWeil resolve to mathlib's identical lemma with no edit. Nothing to upstream —
`WeierstrassCurve.preΨ_four` is already in mathlib verbatim.
