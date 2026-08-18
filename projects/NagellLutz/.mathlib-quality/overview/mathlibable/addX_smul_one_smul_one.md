# /mathlibable report — `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`

> Step-9 (overview) mathlibable assessment, single declaration.
> Project: `projects/NagellLutz` (Nagell–Lutz theorem; elliptic curves; division
> polynomials; elliptic divisibility sequences). Repo root: `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Date: 2026-06-22.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source).
- decl `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:261`
- kind:                     `lemma` (theorem)
- has sorry:                no
- qualified name:           **VERIFIED** — namespaces nest `WeierstrassCurve` (l.76) →
                            `Universal` (l.86) → `Affine` (l.157); decl at l.261 is inside all three.
                            Parsed name `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one` is correct.
- module docstring summary: proves `WeierstrassCurve.zsmul_eq_smulEval` — that `n • P` of a
                            nonsingular rational point equals the division-polynomial rational
                            point `(φₙ/ψₙ² , ωₙ/ψₙ³)` in Jacobian/affine coords, over any field.

---

### Statement (Phase 1)

`addX_smul_one_smul_one` states: on the **universal** Weierstrass curve `pointedCurve`
(`= baseChange curve Universal.Field`, the curve over the universal coefficient field
`Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨Weierstrass poly⟩)` carrying the generic point `(X,Y)`), applying
mathlib's affine group-law X-coordinate formula `Affine.addX` to the generic point's X-coordinate
with itself, using the tangent slope `slopeOne` at `(X,Y)`, yields `smulX 2`:

```
pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2
```

Here `smulX n := polyToField (curve.φ n) / (ψᵤ n)^2` is the rational function `φₙ/ψₙ²` evaluated
at the generic point, i.e. the *intended* X-coordinate of `n • (X,Y)`. So this lemma is the
**`n = 2` (point-doubling) base case** of the induction proving
`Universal.Affine.zsmul_point_eq_smulX_smulY` (l.344): it certifies that the abstract group-law
doubling of the generic point matches the division-polynomial prediction `φ₂/ψ₂²`.

Mathematically this is one direction of the classical fact `x(2P) = φ₂(x)/ψ₂(x)²` (the
duplication / multiplication-by-2 formula), but **specialised to the universal point and phrased in
the project's `smulX`/`slopeOne`/`pointedCurve` vocabulary**.

Variables / typeclasses involved (Lean side):
- none free — everything is over the fixed `Universal.Field` (a specific field built by the project).
  `smulX 1`, `smulX 2`, `slopeOne`, `pointedCurve` are all closed terms.

Hypotheses (Lean side):
- none (the only side-condition `ψᵤ 2 ≠ 0` is discharged inside the proof via `ψᵤ_ne_zero two_ne_zero`).

Conclusion (math): the group-law X-double of the generic point equals `φ₂/ψ₂²`.
Conclusion (Lean): `pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2`.

Proof body (3 substantive lines): `rw [Affine.addX, slopeOne_eq_neg_div, smulX_two, smulX_one]`;
a `simp only [...]` unfolding `ψᵤ`, `ψ_two`, `ψ_three`, etc.; `field_simp [hψ₂]`; then
`exact addX_smul_ring_identity` (a private `ring` identity, l.257). It is a genuine multi-line
computation, not a wrapper.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — the `n = 2` base case feeding one induction
(`zsmul_point_eq_smulX_smulY`). Not a named theorem, not a new structure, not a `## Main results`
entry. (The *file's* main result `zsmul_eq_smulEval` is BIG, but this leaf is SMALL.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line check **n/a**. (For the record the
proof is 3+ substantive lines, so even by the spirit of the check it is MULTI-LINE.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | elliptic curve point doubling X-coord division polynomial 2P formula ψ₃/ψ₂²                             | yes  | `x(2P) = φ₂(x)/ψ₂(x)²`, `φ_n = xψ_n² − ψ_{n+1}ψ_{n−1}` | Trustica, arXiv 1103.4560; the *classical duplication formula* — but stated for `x(P)`, not for a universal point with `addX`+slope |
|  2 | WebSearch (general form)         | "division polynomial" "duplication formula" x-coordinate φ₂ ψ₂² multiplication-by-n                    | yes  | `nP = (φₙ/ψₙ² , ωₙ/ψₙ³)`; `ψ₂ = 2y+a₁x+a₃`, `ψ₃ = 3x⁴+b₂x³+3b₄x²+3b₆x+b₈` | Wikipedia "Division polynomials"; Silverman/Washington form. General curve coeffs `aᵢ`. Confirms the *result*, not this Lean lemma's universal-point phrasing |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2: "duplication formula", "multiplication-by-n", "scalar multiplication")              | yes  | same as #1/#2                    | No personal name attaches; it's "the multiplication-by-n / duplication formula via division polynomials" |
|  4 | ChatGPT MCP                      | n/a — not run                                                                                          | n/a  | —                                | MCP available but the verdict is unambiguous from #1–#5 + mathlib search; the *result* is textbook-standard (no historical-form ambiguity), and the *Lean lemma* is a project-internal base case in original vocabulary. A second opinion cannot change either fact. |
|  5 | Local references                 | `ls .mathlib-quality/references/`                                                                       | n/a  | (no references dir)              | `projects/NagellLutz/.mathlib-quality/references/` absent (only `overview/`). Recorded n/a. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                                | n/a  | —                                | nLab has no dedicated page giving this universal-point identity; the concept is classical NT/AG, not categorical. Recorded n/a. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                | Not a categorical concept. n/a. |
|  8 | Stacks Project                   | division polynomial / Weierstrass group law                                                             | n/a  | —                                | Stacks does not develop explicit division-polynomial coordinate formulas. n/a — not how Stacks treats elliptic curves. |
|  9 | MathOverflow / Math.StackExchange| duplication formula division polynomials x(2P)                                                          | yes  | same `x(2P)=φ₂/ψ₂²` as #1        | Standard textbook identity; many Q&A restate it. No new generality. |
| 10 | recent arXiv (last 5 yrs)        | division polynomials Mumford coords / alternate models (2412.10284, eprint 2010/630)                    | yes  | division polys for other curve models | Confirms active interest in *defining* division polys & their coordinate formulas; none give a "universal Weierstrass curve over the universal coefficient ring" formulation matching the project. |

The protocol passes: WebSearch ran ≥3 queries at distinct generality levels (specific 2P form,
general `nP` form, aliases); local refs checked (absent → n/a); nLab/nCatLab/Stacks/MO/arXiv each
checked or n/a-with-reason. ChatGPT MCP recorded n/a with an explicit justification (result is
unambiguously textbook; the Lean object is project-internal — no second-opinion-resolvable question).

### Literature summary (Phase 3)

Concept identified as: the **multiplication-by-n / duplication formula for elliptic curves via
division polynomials** — `nP = (φₙ/ψₙ² , ωₙ/ψₙ³)`, here the `n=2` X-coordinate case.
Sources agree on the standard form: **yes** — universally `x(nP) = φₙ(x)/ψₙ(x)²` with
`φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁` (Silverman *AEC* Exercise 3.7 / Washington Ch. 3 / Wikipedia).
Most general standard form: for a Weierstrass curve over **any** base with all five coefficients
`a₁…a₆`, `x([n]P) = φₙ(x,y)/ψₙ(x,y)²` as rational functions.
Generality dimensions where the literature varies:
  - base field/ring: from `ℚ`/finite fields up to arbitrary commutative rings (the project goes
    maximally general — works over the *universal* ring, then specialises to any field, incl. char 2).
  - `n`: the literature states it for all `n`; this lemma is the single `n=2` instance.
Disagreement with the literature: **none on the mathematics.** The divergence is purely
*formulational*: the literature states `x(nP)=φₙ/ψₙ²` directly as a theorem about coordinates,
whereas this Lean lemma is a low-level **base-case bridging step** — "mathlib's `Affine.addX` of the
generic point with itself (at slope `slopeOne`) `=` `smulX 2`" — phrased in the project's bespoke
`smulX`/`pointedCurve`/`slopeOne` machinery, which exists only to *prove* the literature theorem.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`

Literature-standard form (from Phase 3): `x([n]P) = φₙ/ψₙ²` for a general Weierstrass curve, all `n`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | curve | fixed `pointedCurve` = universal curve over `Universal.Field` | arbitrary Weierstrass curve `W/R` | N/A (intentional) | Universality is the *proof device*: proving the identity once over the universal ring yields it for every curve by specialisation (`ringEval`/`map_*`). Not a weakenable hypothesis — it's the maximally-general carrier. |
| 2 | point | the generic point `(X,Y)` (via `smulX 1`,`smulY 1`) | arbitrary nonsingular `(x,y)` | N/A (intentional) | Same: the generic point specialises to every point. |
| 3 | `n` | literally `2` (doubling) | all `n` | this is the base case | The lemma is *deliberately* `n=2`; the all-`n` statement is the downstream `zsmul_point_eq_smulX_smulY`. Generalising "n" here would erase the lemma's reason to exist (it is one branch of an even/odd induction). |
| 4 | slope | `slopeOne` (tangent at the generic point) | the slope/tangent line in `x(2P)=…` | N/A | Encodes the doubling tangent; fixed by the `n=2` specialisation. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *in the only dimension that is a free parameter* (the
base curve — it is the universal one, the most general possible carrier), and **deliberately
specialised** in the `n=2` dimension (which is the point of a base-case lemma).
Number of weakening opportunities found: **0** (the `n=2`-ness is intrinsic; the universality is
already maximal).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | No bundled-hypothesis preamble; all args are closed terms over a fixed field. |
|  2 | sequences/metric → filters/topology? | no | — | Purely algebraic identity in a field; no limits/topology. |
|  3 | construct → universal-property class? | no (already universal) | — | The decl already *uses* the universal-curve device; this is exactly the contemporary mathlib idiom for "prove a polynomial identity once, specialise everywhere". |
|  4 | set+closure-predicate → bundled substructure? | no | — | No substructure here. |
|  5 | field/metric-specific → weaken typeclass? | no | — | The identity is proved over the universal *ring* and specialised; the field phrasing here is the `Frac` of that ring, intrinsic to the slope/division. Already maximally general upstream. |
|  6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure? | partly, already addressed | — | The index `n` is generalised to all `ℤ` in the *downstream* theorem; this leaf is the `n=2` case by design (see Phase 4 row 3). |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The declaration already embodies mathlib's preferred
"universal-object → specialise" idiom; there is no cleaner contemporary reformulation. It is a
fixed-instance computational base case, not a candidate for typeclass-/filter-/categorification.
One-line reason: this is a concrete polynomial-identity base case over a fixed universal field —
no abstraction lever to pull.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`

[A] Lean-Finder    "addX of universal point equals smulX 2" / "n•P division polynomial coordinate"  no hits (concept absent from mathlib)
[B] Loogle         pattern `WeierstrassCurve.Affine.addX _ _ _ = _` specialised to `smulX`/universal  n/a — `smulX`, `Universal`, `slopeOne`, `pointedCurve` are project symbols, not in the mathlib index; no analogous decl exists to match
[C] LeanSearch     "X coordinate of 2P equals phi_2 over psi_2 squared on Weierstrass curve"          no hits — mathlib does not connect `n • P` (group law) to division polynomials at all
[D] Grep mathlib src  `addX_smul`, `smulX`, `namespace Universal`, `zsmul_eq_smulEval`, `smulEval` over `Mathlib/AlgebraicGeometry/EllipticCurve/**` and `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`  **zero hits** — see direct evidence below
[E] Name pattern   grep whole `Mathlib/` for `WeierstrassCurve.Universal`                              **zero hits** — the `Universal` namespace does not exist in mathlib

Direct evidence (mathlib pin `09b373db6e`):
- `grep "WeierstrassCurve.Universal" Mathlib/` → **0 matches**: there is no universal-Weierstrass-curve
  development in mathlib. `Universal.Ring`, `Universal.Field`, `smulEval`, `smulX`, `slopeOne`,
  `addX_smul_one_smul_one`, `zsmul_eq_smulEval` — **none** exist upstream.
- `grep -c "Point|coordinate|addX|WeierstrassCurve" Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  → **0**: mathlib's EDS file is the *abstract* recurrence only; it never touches curve points/coordinates.
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` define `ψ/φ/ω` and
  their congruences/degrees but contain **no** lemma linking them to the group-law multiple `n • P`.
- `Mathlib/.../Affine/Formula.lean:238` *does* provide `WeierstrassCurve.Affine.addX` — used here — but
  there is no mathlib lemma evaluating it at a division-polynomial point.

Searched for both: (a) the user's form (universal-point `addX = smulX 2`) — absent; (b) the
literature-standard form (`x(2P)=φ₂/ψ₂²` as a coordinate theorem) — **also absent from mathlib**:
the bridge from the group law to division polynomials is exactly what this project is building and
has not yet been upstreamed.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). The
forked mathlib files (`DivisionPolynomial/*`, `EllipticDivisibilitySequence`) supply only the
*ingredients*; the `Universal`/`smulX`/`n • P` correspondence is project-original.

---

### Call sites — `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`

Internal use count: **2** (within NagellLutz, excluding the declaring lines).
External-to-file callers: **0 distinct files** (both uses are inside the declaring file `ZSMul.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:280` | `… Affine.negAddY, addX_smul_one_smul_one, smulX_two, …` (rewrite inside `addY_smul_one_smul_one`'s proof — the companion Y-coordinate base case) |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:354` | `· erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]` (the `n=2` branch of `zsmul_point_eq_smulX_smulY`'s induction) |

Inline-derivation grep (re-derived elsewhere without using the lemma?): **(none)** — no other site
recomputes `addX (smulX 1) (smulX 1) slopeOne`; the two consumers both go through the lemma.

Cross-repo note: an **identical** `addX_smul_one_smul_one` exists in the HasseWeil project at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:332` (same author, same `Universal`
development copied into a second project). This is intra-AINTLIB duplication of the project-original
code, **not** evidence of a mathlib home — both copies are downstream of the same un-upstreamed work.
It is a candidate for AINTLIB-internal dedup (a cleanup-lane `Common/` refactor), separate from the
mathlib question.

Composability signal: K=2 internal uses, no inline re-derivation, but **both uses are inside the same
file** and are essential structural steps (the doubling base case) of one proof. This is real
internal API for *this proof*, not a reusable general-purpose lemma.

---

### Composition check (Phase 6)

Can `addX_smul_one_smul_one` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: unfold `Affine.addX` + `slopeOne` and close by `field_simp; ring`.
  - Mathlib decls used: `WeierstrassCurve.Affine.addX` (def), `WeierstrassCurve.Affine.slope`,
    `field_simp`, `ring`.
  - Result: **fails as a *mathlib* composition.** The RHS `smulX 2` is a *project* definition
    (`polyToField (curve.φ 2)/(ψᵤ 2)²`), and bridging LHS↔RHS needs the project lemmas
    `slopeOne_eq_neg_div`, `smulX_two`, `ψ_two`/`ψ_three`, `polyToField_*`, plus the private `ring`
    identity `addX_smul_ring_identity`. None of these are mathlib. It is a genuine multi-step proof
    over project-defined objects, not a 1–3-call mathlib composition.

Attempt 2: cite a mathlib "x(2P)=φ₂/ψ₂²" lemma and specialise.
  - Mathlib decls used: none exist (Phase 5: mathlib has no group-law ↔ division-polynomial bridge).
  - Result: **fails** — the building block does not exist upstream.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The lemma lives entirely in project-original
vocabulary that mathlib does not have.

---

## Verdict: `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the *underlying mathematics* (`x(2P)=φ₂/ψ₂²`, duplication via
  division polynomials) is textbook-standard (Silverman, Washington, Wikipedia) — but as a
  *coordinate theorem*, not as this universal-point/`addX`-base-case lemma.
- Generality analysis (Phase 4): MAXIMALLY GENERAL in its free dimension (universal curve) and
  intentionally `n=2`-specialised (it's a base case); no weakening; no modern-idiom restatement.
- Mathlib search (Phase 5): **not in mathlib** — `WeierstrassCurve.Universal` namespace, `smulX`,
  and any group-law↔division-polynomial bridge are entirely absent upstream (0 grep hits).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (RHS and the whole proof are
  project-defined; no mathlib building block for the bridge exists).

**Rationale.**
This is **not** a standalone mathlib-quality lemma. It is a low-level, fixed-instance *base case*
(`n = 2`, the doubling step) inside one induction — `zsmul_point_eq_smulX_smulY` — phrased entirely
in the project's bespoke universal-curve machinery (`pointedCurve`, `smulX`, `slopeOne`,
`polyToField`, the private `ring` identity `addX_smul_ring_identity`). Its content — "mathlib's
group-law `Affine.addX` applied to the generic point with itself equals `φ₂/ψ₂²`" — is meaningful
*only* relative to that machinery, which exists to prove the project's headline result
`WeierstrassCurve.zsmul_eq_smulEval` (`n • P = (φₙ/ψₙ² , ωₙ/ψₙ³)`). It has 2 call sites, both inside
its own file, both structural to that single proof.

So it does **not** stand alone for mathlib. The right framing is **NO-composable-from-mathlib**: it
is one inlined computational step of a larger, currently-un-upstreamed development. Mathlib's
ingredients (`Affine.addX`, the division polynomials `ψ/φ/ω`, the abstract EDS recurrence) are all
present, but the *correspondence* between the group law and division polynomials — of which this
lemma is a fragment — is precisely what is missing upstream. The unit that could plausibly belong in
mathlib is the **whole `Universal` → `zsmul_eq_smulEval` development**, not this leaf; if that bridge
is upstreamed, this base case should be an inlined `have`/local step in the multiplication-formula
proof (exactly as it is now), not a public mathlib lemma.

A note on the alternative reading: one might call this NO-mathlib-has-it on the grounds that the
*duplication formula* is "morally in the literature/should be in mathlib". That is rejected because
(a) mathlib does **not** currently have the group-law↔division-polynomial bridge in any form
(Phase 5), so there is nothing to cite, and (b) even the eventual mathlib version would phrase the
*theorem* as `x([n]P)=φₙ/ψₙ²` for general `n`, with this `n=2`/universal-point/`slope` lemma
remaining an internal proof step — not the public statement.

**WHY not (refactor-actionable):**
Mathlib supplies the building blocks — `WeierstrassCurve.Affine.addX`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:238`), `WeierstrassCurve.Affine.slope`
(same file), and the division polynomials in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
— but the X-double-equals-`φ₂/ψ₂²` identity is not a 1–3-call mathlib composition: it is a genuine
multi-step computation glued together by **project-original** definitions and a private `ring`
identity. There is no mathlib decl to drop in.

Mathlib building blocks: `WeierstrassCurve.Affine.addX`, `WeierstrassCurve.Affine.slope`
(`…/Affine/Formula.lean`), `WeierstrassCurve.ψ`/`φ`/`ω`
(`…/DivisionPolynomial/Basic.lean`).
Composition sketch (≤3 lines): **none available** — see Phase 6 (both attempts fail; the RHS
`smulX 2` and the entire proof are project-defined, with no upstream bridge lemma to compose).

Call sites in our project (from Phase 6.0): **2** (both in `ZSMul.lean`: l.280, l.354).
Refactor plan (within AINTLIB, **not** a mathlib action): **keep the lemma as a project-local helper**
— it is correctly an internal step of `zsmul_point_eq_smulX_smulY`. Do **not** attempt to delete/inline
it in favour of mathlib (there is nothing upstream to inline against). Two genuinely actionable
follow-ups, both *internal* to AINTLIB and *outside* the mathlib question:
  1. **De-duplicate across projects:** the identical lemma in
     `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:332` and this one should be
     unified — lift the shared `Universal` development into a common location (cleanup-lane `Common/`
     refactor / GitHub cleanup ticket), so both NagellLutz and HasseWeil import one copy.
  2. **Upstream the whole bridge, not the leaf:** if/when AINTLIB pushes the
     `Universal` → `zsmul_eq_smulEval` correspondence to mathlib, this base case rides along as an
     internal `have`/private lemma inside the multiplication-formula proof — it is not a separate PR.

Next action: **no standalone mathlib PR.** Treat as project-internal infrastructure. File (or fold
into) an AINTLIB cleanup ticket for the NagellLutz/HasseWeil `Universal` duplication; re-evaluate for
mathlib only as part of upstreaming the entire `zsmul_eq_smulEval` development.

---

## Next step

No standalone mathlib PR. Keep `addX_smul_one_smul_one` as a project-local base-case helper. The
mathlib-relevant unit is the entire `WeierstrassCurve.Universal` → `zsmul_eq_smulEval` development
(currently un-upstreamed), within which this lemma is an internal step. Actionable now only as
AINTLIB-internal work: dedupe against the identical HasseWeil copy
(`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:332`) via a shared `Common/` module.
