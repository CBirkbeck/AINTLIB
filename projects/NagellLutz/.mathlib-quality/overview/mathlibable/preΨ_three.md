# /mathlibable report — `WeierstrassCurve.preΨ_three`

Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
curves; division polynomials; elliptic divisibility sequences).

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoning from source
- decl `WeierstrassCurve.preΨ_three`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:136–138`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

**Qualified name (VERIFIED).** The file opens `namespace WeierstrassCurve`
(DivisionPolynomial.lean:27) with `variable {R …} [CommRing R] (W : WeierstrassCurve R)`
(line 29). The lemma is declared `lemma preΨ_three : W.preΨ 3 = W.Ψ₃`, so dot-notation
`W.preΨ`/`W.Ψ₃` resolve to `WeierstrassCurve.preΨ`/`WeierstrassCurve.Ψ₃`, and the
fully-qualified lemma name is **`WeierstrassCurve.preΨ_three`** — matching the prompt's
guess exactly.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ_three` is a `@[simp]` evaluation lemma asserting that the auxiliary
univariate division polynomial `preΨ` of a Weierstrass curve `W`, evaluated at the integer
index `3`, equals the (already-defined) `3`-division polynomial `Ψ₃`. In the theory of
elliptic divisibility sequences, `preΨ` is the integer-indexed `preNormEDS` recursion
`preNormEDS (W.Ψ₂Sq^2) W.Ψ₃ W.preΨ₄`, whose third term is by construction the second
generator `c = Ψ₃`. So this lemma simply reads off the base case of the normalised EDS at
`n = 3`.

Variables / typeclasses involved (Lean side):
- `{R : Type r}` with `[CommRing R]` — coefficient ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.

Hypotheses (Lean side): none.

Conclusion (math): `preΨ₃ = Ψ₃` (the curve's `3`-division polynomial as a univariate
polynomial in `R[X]`).

Conclusion (Lean): `W.preΨ 3 = W.Ψ₃`.

Proof body: `preNormEDS_three ..` (one term; `..` fills `W.Ψ₂Sq^2`, `W.Ψ₃`, `W.preΨ₄`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `@[simp]` base-case evaluation lemma; not a named theorem, not a new
structure, not a `## Main results` goal. (Literature width run regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line.
One-liner verdict: n/a — kind is `lemma`, not `def`. (The 2b def-exemption machinery does
not apply; recorded for completeness.)

---

### Literature search table (Phase 3)

The "concept" here is a recursion-unfolding identity (`preNormEDS … 3 = c`), specialised to
the division-polynomial generators. It is the value of the second initial term of a normalised
elliptic divisibility sequence — book-keeping, not a named theorem. The genuinely-named
mathematical object is the **3-division polynomial ψ₃** of an elliptic curve; that is exactly
what the RHS `Ψ₃` already denotes, and mathlib's own statement is `W.preΨ 3 = W.Ψ₃`.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | division polynomial ψ₃ explicit formula elliptic curve                | yes  | `ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈` | Silverman AEC III.3.6; matches `def Ψ₃` exactly |
|  2 | WebSearch (general form)         | elliptic divisibility sequence normalised initial terms               | yes  | EDS normalised so W₁=1, and the recursion's generators are the base data | Ward 1948; the "3rd term = a generator" is definitional, not a theorem |
|  3 | WebSearch (named-after/aliases)  | "division polynomial" psi_3 third recurrence base case                | yes  | same as #1          | The named object is ψ₃; "preΨ₃ = Ψ₃" is an internal link, never named in the literature |
|  4 | ChatGPT MCP                      | standard form/generality/history of "third division polynomial equals normalised-EDS third term" | n/a  | — | ChatGPT MCP unavailable this environment (per task note); covered by #1/#2 + decisive mathlib hit below |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial"/"EDS"    | n/a  | — | No references dir present for NagellLutz; recorded n/a |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial                  | n/a  | — | nLab has no page treating the per-index recursion base case as a result; not a categorical concept |
|  7 | nCatLab                          | —                                                                     | n/a  | — | Not a categorical concept |
|  8 | Stacks Project                   | division polynomial                                                    | n/a  | — | Stacks does not develop classical division polynomials / EDS in this form |
|  9 | MathOverflow / Math.SE           | division polynomial recurrence base values                            | yes  | confirms ψ₂,ψ₃ are the base data of the recurrence | The "= ψ₃" identity is universally treated as definitional, never stated as a lemma |
| 10 | recent arXiv (≤5y)               | elliptic divisibility sequence division polynomial mathlib            | n/a  | — | No new formulation; the relevant artifact is mathlib's own `DivisionPolynomial.Basic` (Angdinata) |

### Literature summary (Phase 3)

Concept identified as: the **value of the normalised-EDS recursion at index 3** = its second
initial generator, which here is the **3-division polynomial ψ₃**.
Sources agree on the standard form: yes — ψ₃ is the classical 3-division polynomial; its
appearance as the n=3 term of `preNormEDS` is a definitional consequence of how mathlib
(and the literature) seed the recursion.
Most general standard form: the recursion identity `preNormEDS b c d 3 = c` over any commutative
ring (this is `preNormEDS_three`, the genuinely-general statement — see Phase 5); the
division-polynomial specialisation `W.preΨ 3 = W.Ψ₃` is one instantiation `b := Ψ₂Sq², c := Ψ₃, d := preΨ₄`.
Generality dimensions where the literature varies: none of consequence — ψ₃'s formula is fixed
over any base ring; the seeding convention is standard.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): for an arbitrary commutative ring and recursion data,
`preNormEDS b c d 3 = c`; the curve-specific corollary specialises `b,c,d` to the curve's
division-polynomial seeds.

| # | Parameter / hypothesis | Current Lean form           | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-----------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`        | commutative ring            | commutative ring                 | NO                  | `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preNormEDS` are all defined over `CommRing`; this is already the base generality |
| 2 | `(W : WeierstrassCurve R)` | a Weierstrass curve     | curve fixes the recursion seeds  | (by design)         | The lemma is *about* `W.preΨ`; the curve-free generality is `preNormEDS_three`, already in mathlib |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the curve-specialised statement; it is an exact
copy of mathlib's, over `CommRing R`). The strictly-more-general curve-free statement is
`preNormEDS_three`, which mathlib **also already has** — so there is no generalisation to perform.
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | already class-based (`CommRing`) |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic identity |
| 3 | construction → universal property? | no | — | `Ψ₃` is a concrete polynomial by design |
| 4 | set+closure → bundled substructure? | no | — | n/a |
| 5 | vector-space/field → module/(semi)ring? | no | — | already at `CommRing`, the natural floor |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → arbitrary monoid/group? | no | — | the index is the literal `3`; the index-general object is `preNormEDS` itself, already present |

Modern idiom available: **no.** This is an exact copy of the current mathlib idiom (David
Angdinata's `DivisionPolynomial.Basic`); there is nothing to modernise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.preΨ_three` (Phase 5)

[A] Lean-Finder       "preΨ three division polynomial"      n/a (index offline locally) — superseded by decisive grep hit
[B] Loogle            `WeierstrassCurve.preΨ _ 3 = _`        n/a (index offline locally) — superseded by decisive grep hit
[C] LeanSearch        "third division polynomial equals Ψ₃" n/a (index offline locally) — superseded by decisive grep hit
[D] Grep mathlib src  `grep -n "preΨ_three" .lake/packages/mathlib/.../DivisionPolynomial/Basic.lean`  →  **DIRECT HIT** (see below)
[E] Name pattern      `WeierstrassCurve.preΨ_three`         →  **HIT** — same namespace, same name

Searched for both:
  - the user's current form `W.preΨ 3 = W.Ψ₃` — **found, identical**
  - the literature-standard (curve-free) form `preNormEDS b c d 3 = c` — **also found** as
    `preNormEDS_three` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the proof
    term `preNormEDS_three ..` *is* this lemma).

Decisive evidence:
```
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean
  142  noncomputable def Ψ₃ : R[X] :=
  143    3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈   -- == project :65–67
  194  noncomputable def preΨ (n : ℤ) : R[X] :=
  195    preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n                                       -- == project :117–118
  213  @[simp]
  214  lemma preΨ_three : W.preΨ 3 = W.Ψ₃ :=
  215    preNormEDS_three ..                                                          -- == project :136–138
```
The project lemma (DivisionPolynomial.lean:136–138) is **byte-for-byte identical** to mathlib
lines 213–215: same namespace `WeierstrassCurve`, same `@[simp]`, same statement, same proof
term. Its two supporting defs (`preΨ`, `Ψ₃`) are likewise verbatim copies of the mathlib defs.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ_three`; identical form.**

---

### Call sites — `WeierstrassCurve.preΨ_three` (Phase 6)

Internal use count: **2** (within NagellLutz, excluding the declaring file).
External-to-file callers: 2 distinct files.

| Caller file:line                                              | Usage pattern (one-line excerpt)                                   |
|--------------------------------------------------------------|---------------------------------------------------------------------|
| LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:88     | `simp [even_two, WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_one]` |
| LutzNagell/LutzNagellTheorem/PIDMain.lean:293                | `simp [even_two, WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_one]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without the lemma?): (none) —
both consumers use it as a `simp` lemma, exactly as mathlib's `@[simp]` version would fire.

### Composition check (Phase 6a)

Can `WeierstrassCurve.preΨ_three` be derived from mathlib in ≤3 chained calls? Moot — mathlib
*is* this lemma. For completeness: `example : W.preΨ 3 = W.Ψ₃ := WeierstrassCurve.preΨ_three`
(0 extra calls; it is the same decl). The underlying one-step content is `preNormEDS_three ..`.

Conclusion: **NOT-COMPOSABLE-NEEDED** — it already exists verbatim; no composition required.

---

## Verdict: `WeierstrassCurve.preΨ_three`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the named object is ψ₃; the "= ψ₃" link is definitional, never a separate literature lemma. The relevant artifact is mathlib's own `DivisionPolynomial.Basic`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (exact copy over `CommRing`); the curve-free generalisation `preNormEDS_three` is *also* already in mathlib. No modern-idiom move (4c: no).
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.preΨ_three`; identical form** (Basic.lean:214–215, byte-for-byte equal to the project copy, including namespace and `@[simp]`).
- Composition check (Phase 6): N/A — it is literally the same declaration.

**Rationale.**

This declaration is part of an intentional, file-level **fork** of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. The project's own module docstring says so outright: the file is "a copy of `Mathlib.…DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)." The fork exists purely to dodge a *naming* collision in the project's parallel EDS development — not because of any mathematical difference. Accordingly `WeierstrassCurve.preΨ_three`, its statement, its `@[simp]` attribute, its proof term (`preNormEDS_three ..`), and both supporting defs (`preΨ`, `Ψ₃`) are reproduced **verbatim** from mathlib (project lines 136–138 / 117–118 / 65–67 == mathlib lines 214–215 / 194–195 / 142–143). Mathlib's bar is "is this the right statement at the right generality, not already there" — and here it is already there, in the very same namespace, under the very same name. There is nothing to upstream.

**WHY not (refactor-actionable).**
Mathlib already has this lemma, identically, as `WeierstrassCurve.preΨ_three`. The project copy is a duplicate produced by the EDS-naming fork. It contributes no new mathematical content; the curve-free generalisation it is built on (`preNormEDS_three`) is likewise already upstream. There is no mathlib API gap, TODO, or missing reformulation that this fills.

Existing mathlib decl:        `WeierstrassCurve.preΨ_three`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:214–215`
Our form follows in 0 lines (it is the same statement):
```lean
example (W : WeierstrassCurve R) : W.preΨ 3 = W.Ψ₃ := WeierstrassCurve.preΨ_three
```
Call sites in our project (from Phase 6): K = 2 (GeneralDiscriminant.lean:88, PIDMain.lean:293).

**Refactor plan.** This is a *fork-level* duplicate, not a stray helper — do **not** delete
this single lemma in isolation. The whole `DivisionPolynomial.lean` + `EllipticDivisibilitySequence.lean`
fork exists only to rename around the project's parallel `normEDS`/`complEDS` definitions; if the
fork is ever retired (project switches to mathlib's EDS API), this file is dropped wholesale and the
two call sites then resolve to mathlib's `WeierstrassCurve.preΨ_three` *unchanged* — the `simp`
calls at GeneralDiscriminant.lean:88 and PIDMain.lean:293 already name `WeierstrassCurve.preΨ_three`
and would bind to the mathlib lemma with no edit. Until that fork-retirement happens, leave this
decl exactly as is: it must stay for the forked file to compile, and editing it in isolation would
break both consumers. The consolidation action lives at the *fork* grain (a de-fork ticket), not at
this lemma.

Next action: no per-decl action. Record under a single "retire the DivisionPolynomial /
EllipticDivisibilitySequence fork; adopt mathlib's EDS API" consolidation ticket; this lemma (and its
`_one/_two/_four/zero/neg/even/odd/ofNat` siblings, `preΨ`, `Ψ₃`, etc.) all disappear with the fork.

---

## Next step

No per-declaration action. `WeierstrassCurve.preΨ_three` is a verbatim copy of the existing
mathlib lemma of the same name, kept alive only by the project's deliberate EDS-naming fork.
Folder it into a single "de-fork `DivisionPolynomial` / `EllipticDivisibilitySequence`" ticket
rather than touching this lemma on its own (deleting it in isolation breaks the two `simp` call
sites and the rest of the forked file).
