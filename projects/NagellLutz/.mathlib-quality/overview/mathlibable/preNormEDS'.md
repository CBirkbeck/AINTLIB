# /mathlibable report — `preNormEDS'`

Single-declaration, full 10-phase assessment. Step-9 overview context (NagellLutz / Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic divisibility sequences).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); decl read directly from source.
- decl `preNormEDS'`:        ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:710`
- qualified name:            `preNormEDS'` (in `section PreNormEDS` at line 704; the preceding `namespace IsEllSequence` is closed at line 702, so there is **no enclosing namespace** — base name = qualified name)
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms." Copyright header: David Kurniadi Angdinata (the mathlib EDS author) — this file is a **fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`**.

---

### Statement (Phase 1)

`preNormEDS'` is the **definition** of the auxiliary integer-indexed sequence underlying a *normalised* elliptic divisibility sequence (Ward's EDS), over a commutative ring `R`.

Given `b c d : R`, it builds `W : ℕ → R` with seed values `W 0 = 0`, `W 1 = 1`, `W 2 = 1`, `W 3 = c`, `W 4 = d`, extended by the standard EDS double-up recurrence: writing `m = n / 2`, the term `W (n+5)` is given by the odd-doubling formula `W(m+4)·W(m+2)³·[Even m ? b : 1] − W(m+1)·W(m+3)³·[Even m ? 1 : b]` when `n` is even, and by the even-doubling formula `W(m+2)²·W(m+3)·W(m+5) − W(m+1)·W(m+3)·W(m+4)²` when `n` is odd. The extra parameter `b` is the normalisation knob that tracks the `W₂` factor differing between odd and even indices.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (from `variable` at line 85; specialised binder `(b c d : R)` at line 706).
- `(b c d : R)` — the three free parameters (the normalised initial data `W₃ = c`, `W₄ = d`, plus normalisation `b`).

Hypotheses (Lean side): none (it is a total recursive definition on `ℕ`).

Conclusion (math): the auxiliary normalised-EDS sequence `ℕ → R`.
Conclusion (Lean): `ℕ → R` (n/a — definition).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a `def` of a named mathematical object (the auxiliary sequence of a normalised elliptic divisibility sequence — a Ward EDS), and it is the foundational definition the whole file is built on (`## Main definitions` lists it).

(Literature width run regardless — see Phase 3.)

### One-line check (Phase 2b)

Body line count: ~16 substantive lines (a 5-case recursion with a well-founded branch).
One-liner verdict: **MULTI-LINE** — check skipped. (Not a wrapper; a genuine recursive construction with termination obligations.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence normalised initial terms recurrence Ward auxiliary sequence" | yes  | Ward EDS; `W₀=0, W₁=1`; determined by `W₂,W₃,W₄` with `W₂\|W₄` | Wikipedia "Elliptic divisibility sequence"; Silverman–Stephens "sign of an EDS" |
|  2 | WebSearch (general form)         | (same query, generality lens — ring vs ℤ)                                                  | yes  | classically over `ℤ`; mathlib generalises to any `CommRing` | recurrence `W_{2n+1}=W_{n+2}W_n³−W_{n−1}W_{n+1}³`, `W_{2n}W₂=W_n(W_{n+2}W_{n−1}²−W_{n−2}W_{n+1}²)` matches the def exactly |
|  3 | WebSearch (named-after / aliases)| "Ward elliptic sequence" / "normalized divisibility sequence" (in result set)              | yes  | "normalized": `D₀=0, D₁=1`        | named after Morgan Ward (1948) |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch #1–3 + mathlib docs)                       | n/a  | covered by #1–3 + mathlib docstring | MCP unavailable; standard form already pinned by 3 web channels + the mathlib module |
|  5 | Local references                 | `.mathlib-quality/references/` for "EDS"/"divisibility"                                    | n/a  | (no references dir present for this project) | recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                                            | n/a  | not an nLab topic                 | EDS is number-theoretic, not categorical — nLab has no page |
|  7 | nCatLab (if categorical)         | —                                                                                          | n/a  | not categorical                   | n/a |
|  8 | Stacks Project (if alg geom)     | "division polynomial" / "elliptic divisibility"                                            | n/a  | Stacks has elliptic curves but not the EDS recurrence / division-polynomial sequences | recorded n/a |
|  9 | MathOverflow / Math.StackExchange| (surfaced via WebSearch #1 result cluster)                                                 | yes  | confirms `W₂\|W₄` integrality criterion | consistent with #1 |
| 10 | recent arXiv (last 5 years)      | result cluster: arXiv:1001.5303, math/0402415, 1610.08109, 1505.00194                      | yes  | EDS actively studied; same recurrence | "An elliptic sequence is not a sampled linear recurrence" etc. — all use Ward's normalisation |

### Literature summary (Phase 3)

Concept identified as: **the auxiliary sequence of a normalised elliptic divisibility sequence (Ward EDS)**; mathlib calls it `preNormEDS'` and `normEDS b c d n = preNormEDS' (b⁴) c d n · (if Even n then b else 1)`.
Sources agree on the standard form: **yes** — `W₀=0, W₁=1`, seed `W₂,W₃,W₄`, the double-up recurrences above; classical (Ward) over `ℤ`.
Most general standard form: the recurrence makes sense over any commutative ring; mathlib already states it that way (`[CommRing R]`).
Generality dimensions where the literature varies: only the coefficient domain (`ℤ` classically → any `CommRing` in mathlib). The `b`-parametrisation (`preNormEDS'` vs `normEDS`) is mathlib's own device for keeping the recurrence polynomial; it is not a generality dimension in the literature.
Disagreement with the literature: none.

**Critical literature observation:** WebSearch result #1's auxiliary-sequence snippet ("...auxiliary sequence, which are equal when n is odd, and which differ by a factor of b when n is even") is a verbatim paraphrase of **the mathlib `EllipticDivisibilitySequence` module docstring** — i.e. the concept already lives in mathlib under this exact name. This is decisive for Phase 5.

---

### Generality analysis — `preNormEDS'`

Literature-standard form (from Phase 3): the normalised-EDS auxiliary recurrence over a commutative ring, seeded by `b, c, d`.

| # | Parameter / hypothesis | Current Lean form     | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-----------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`        | commutative ring      | comm. ring (mathlib); ℤ (classical) | NO | the recurrence uses subtraction and is symmetric/polynomial; `CommRing` is already the natural minimal home and matches mathlib's own `preNormEDS'` |
| 2 | `(b c d : R)`         | three ring elements   | the normalised seed data | NO | these are the defining data of the object |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's own generality — `CommRing R`).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclass? | no | already a plain `def` over `[CommRing R]` | — |
| 2 | sequences/metric → filters/topology? | no | finite recursive identity; no limiting notion | — |
| 3 | construction → universal property? | no | EDS is an explicit recurrence; no universal property to characterise | — |
| 4 | set+closure → bundled substructure? | no | not a substructure | — |
| 5 | vector-space/field-specific → weaken typeclass? | no | already at `CommRing`, the right level | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index → general monoid? | no | indexed by `ℕ` essentially (the EDS recurrence is ℕ/ℤ-specific via even/odd doubling); `preNormEDS` already extends to `ℤ` | — |

Modern idiom available: **no**. This is already the contemporary mathlib formulation — because **it literally is the mathlib definition** (same author, same signature).

---

### Diamond / defeq risk — `preNormEDS'` (Phase 4.5)

Kind is `def`, so the phase runs; but since the project decl is byte-for-byte mathlib's existing `preNormEDS'`, any risk is exactly mathlib's accepted status quo.

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | no instances introduced; plain `def : ℕ → R` |
| 2 | Reducibility leak | none | not `@[reducible]`; sealed recursive def, same as mathlib |
| 3 | Non-canonical unfolding | low | `simp` lemmas (`preNormEDS'_zero/one/two/three/four/even/odd`) gate unfolding — identical set to mathlib's |
| 4 | Instance priority collision | none | not an instance |
| 5 | Universe-polymorphism | none | `R : Type u`, no forced annotation |
| 6 | Coercion ambiguity | none | no coercion |

### Risk verdict (Phase 4.5): **NONE** (equals mathlib's accepted definition).

---

### Mathlib search-status: `preNormEDS'`

[A] Lean-Finder       n/a (index offline) — superseded by direct source hit below
[B] Loogle            `preNormEDS'` / `?b → ?c → ?d → ℕ → ?R`     hit (direct source read more authoritative)
[C] LeanSearch        "auxiliary sequence normalised elliptic divisibility sequence"  hit — `Mathlib.NumberTheory.EllipticDivisibilitySequence.preNormEDS'` (confirmed via WebSearch result #6: the mathlib4_docs page)
[D] Grep mathlib src  `grep "preNormEDS'" .lake/packages/mathlib/...`  **HIT** — defined at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:124`
[E] Name pattern      `def preNormEDS'`                            **HIT** — exact name, no namespace, in `section PreNormEDS`

Searched for both the current form and the literature-standard form — both resolve to the same mathlib decl.

**Concluded: found in mathlib as `preNormEDS'` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:124`); identical form.**

Side-by-side confirmation:
- Same signature: `def preNormEDS' : ℕ → R` under `variable {R : Type u} [CommRing R]` + `variable (b c d : R)`, in `section PreNormEDS`, no enclosing namespace — in **both** files.
- Same five base cases (`0↦0, 1↦1, 2↦1, 3↦c, 4↦d`) and same two recurrence branches (even-`n` odd-doubling with the `b`/`1` parity switch; odd-`n` even-doubling). The only differences are cosmetic/termination-internal: the project uses `letI m := n/2` and writes out the `h1…h4 : _ < n+5` bounds and an explicit `0 < n` step; mathlib uses `let m := n/2` and a one-line `gcongr` termination proof. These do not change the type, the definitional unfolding, or the simp-normal form.
- The companion API is also duplicated identically: `preNormEDS'_{zero,one,two,three,four,even,odd}`, `preNormEDS`, `preNormEDS_ofNat`, `map_preNormEDS'` all exist in both files with matching statements.

---

### Call sites — `preNormEDS'`

Internal use count (within NagellLutz, excluding the declaring file and the `…Original.lean` backup): the only consumer is the project's **own** forked `DivisionPolynomial.lean`:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:77` | `preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:81–107` | `preNormEDS'_{zero,one,two,three,four,even,odd} ..` |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:438` | `… map_preNormEDS']` |

Inline-derivation grep: none re-derive the recurrence; they call the def/lemmas directly.

**Interpretation:** the consumers live entirely inside the *forked* portion of the project (`DivisionPolynomial.lean` is itself a fork of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`). They would resolve against mathlib's `preNormEDS'` unchanged if the local fork were dropped. So this is **not** evidence of new API — it is the fork referencing itself.

---

### Composition check (Phase 6)

Can `preNormEDS'` be "derived from mathlib in ≤3 calls"? Not applicable in the usual sense — it is a definition, and the relevant fact is that mathlib **already contains the identical definition**. There is nothing to compose: the result is `Mathlib...preNormEDS'` itself.

Conclusion: **n/a — mathlib already has the exact decl** (see Phase 5). Not COMPOSABLE-from-primitives; it simply *is* the mathlib primitive.

---

## Verdict: `preNormEDS'`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): the concept is Ward's normalised-EDS auxiliary sequence; the standard-form snippet returned by WebSearch is itself a paraphrase of the mathlib module docstring.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical generality to mathlib (`[CommRing R]`); no modern-idiom improvement (it already is the modern form).
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS'`** at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:124`; identical form (same name, namespace, signature, base cases, recurrence, and surrounding API).
- Composition check (Phase 6): n/a — it is the mathlib decl, not a composition.

**Rationale:**

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is an in-tree **fork of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`** (same Apache header, same author David Kurniadi Angdinata, same `## Main definitions`). `preNormEDS'` is reproduced character-for-character up to a cosmetic `let`/`letI` and a hand-expanded termination proof; the type, the definitional content, the simp-normal form, and the entire companion lemma block (`preNormEDS'_zero/one/two/three/four/even/odd`, `preNormEDS`, `map_preNormEDS'`) all match mathlib. Mathlib unquestionably already has this — it is where the definition originates. The only local consumers sit in the project's *own* forked `DivisionPolynomial.lean`, which is likewise a fork of mathlib's division-polynomial file and would bind to mathlib's `preNormEDS'` unchanged.

The task framing flags exactly this: the project forks `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and `Mathlib.NumberTheory.EllipticDivisibilitySequence`, so the decl was expected to already be in mathlib — and it is. There is no contribution here; the right end-state is to drop the fork and depend on mathlib (the consolidation goal). (Note: the project's `EllSequence` *namespace* track — `Rel₃`, `HaveSameParity₄`, `rel₄`, `net`, `invar`, the `IsEllSequence`-as-odd-function lemmas, `complEDS` — is genuinely new relative to mathlib and is where any mathlibable content in this file would live; but `preNormEDS'` specifically is pure duplication.)

**WHY not (refactor-actionable):**
Mathlib already defines `preNormEDS'` with the identical signature and body. The project copy is redundant duplication created by forking the mathlib module.

Existing mathlib decl:   `preNormEDS'`
Located at:              `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:124`
Our form follows in 0 lines — it is the same declaration:
```lean
-- after dropping the local fork, this resolves to the mathlib decl unchanged:
example (R : Type*) [CommRing R] (b c d : R) (n : ℕ) : R := preNormEDS' b c d n
```
Call sites in our project (from Phase 6.0): the `preNormEDS'`/`preNormEDS'_*`/`map_preNormEDS'` references in `DivisionPolynomial.lean` (lines 77, 81, 85, 89, 93, 97, 102, 107, 438) — all inside the project's own forked division-polynomial file.

Refactor plan:
1. Delete the forked `preNormEDS'` (and the duplicated `preNormEDS'_*`, `preNormEDS`, `map_preNormEDS'`, etc.) from `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, replacing them with `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`.
2. The `DivisionPolynomial.lean` call sites need **no change** — name, argument order, and the `..` ellipsis-style lemma applications are identical to mathlib's; they will bind to the mathlib decls directly once the local copies are removed.
3. Keep only the genuinely-new `EllSequence`/`HaveSameParity₄`/`Rel₄`/`net`/`complEDS` material (assess those declarations separately — they are *not* in mathlib).

**Next action:** delete the forked `preNormEDS'` from the project and import `Mathlib.NumberTheory.EllipticDivisibilitySequence` instead; the `DivisionPolynomial.lean` call sites carry over unchanged.

---

## Next step

Delete `preNormEDS'` (and its duplicated companion lemmas) from the NagellLutz fork and depend on mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:124` instead. No mathlib PR — this is a de-duplication / consolidation task, not a contribution. Route the file's genuinely-novel `EllSequence`-namespace declarations through their own `/mathlibable` runs.
