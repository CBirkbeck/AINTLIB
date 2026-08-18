# /mathlibable report — `WeierstrassCurve.invar`

## Verdict: BORDERLINE-needs-human

One-line: a one-line auxiliary `def` (`6X² + b₂X + b₄`, K=0 external call sites,
no Phase-2b exemption) that is genuine glue for the **ω-division-polynomial
family** — a development that fills mathlib's *explicit* `ωₙ` TODO. Should travel
upstream *with* the ω family, not alone and not deleted. The packaging call is a
human one.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task brief); reasoned from source
- decl `WeierstrassCurve.invar`: ✓ resolved at projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:48
- kind:                      `def`  (noncomputable section)
- has sorry:                 no
- module docstring summary:  "extends the division polynomial development from mathlib with the `ω`
                              family of division polynomials, the complement `ψc`, and the invariant
                              `invar`, which are needed for the `ZSMul` proof."

Qualified name VERIFIED: `WeierstrassCurve.invar` (inside `namespace WeierstrassCurve`, line 35).
NB: there is an *unrelated* `WeierstrassCurve.EllSequence.invar` lemma (about `invarNum`/`invarDenom`)
in `EllipticDivisibilitySequence(.Original).lean:699/665` — a different declaration, not this target.

---

### Statement (Phase 1)

`WeierstrassCurve.invar` is the **definition** of a univariate polynomial attached to a Weierstrass
curve `W` over a commutative ring `R`:

> `invar := 6X² + b₂·X + b₄ ∈ R[X]`,

where `b₂, b₄` are the standard b-invariants of `W` (`b₂ = a₁²+4a₂`, `b₄ = 2a₄+a₁a₃`). Despite the
docstring calling it "the invariant", it is an **implementation auxiliary**: the docstring states it
"is equal to the quotient `(ψ(n-1)²ψ(n+2)+ψ(n-2)ψ(n+1)²+ψ₂²ψ(n)³)/ψ(n+1)ψ(n)ψ(n-1)` for arbitrary `n`
modulo the Weierstrass polynomial." Its mathematical role is captured by the very next lemma,
`preΨ₄_add_Ψ₂Sq_sq` (line 60): **`preΨ₄ + Ψ₂Sq² = invar · Ψ₃`** — i.e. `invar` is the cofactor that
exhibits `Ψ₃ = ψ₃` as a divisor of `preΨ₄ + Ψ₂Sq²`. This factorisation is the algebraic identity that
makes the bivariate `ω n` (second Jacobian coordinate of `[n]`) a genuine polynomial.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — the base ring; maximally general (any commutative ring).
- `(W : WeierstrassCurve R)` — a Weierstrass curve (long form, all five `aᵢ`).

Hypotheses: none.

Conclusion (math): defines `6X² + b₂X + b₄`.
Conclusion (Lean): `R[X]` (n/a — it's a definition).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper `def` — a single scalar cofactor polynomial; not a named theorem, not a new
mathematical structure, not a `## Main results` headline. (The *headline* of the surrounding file is
the ω family + `isEllSequence_ψ`; `invar` is plumbing underneath it.)

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1** substantive line (`6 * X ^ 2 + C W.b₂ * X + C W.b₄`).
One-liner verdict: **ONE-LINER**.

Exemption check:
| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | **no**   | The opposite — every use immediately `rw [invar]` to unfold it (lines 61, 85). It is *not* sealed against unfolding; it has no defeq-barrier role. |
| Avoid typeclass diamonds         | **no**   | It is a `Polynomial` value, not an instance/structure; no `Mul`/`Zero`/`AddCommMonoid` search path turns on it. |
| Mark semantic intent / API name  | **no**   | No consumer outside the declaring file depends on the name (K=0, see Phase 6). The name is local shorthand, not a stable API surface. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION.** Carried into Phase 7: biases against a standalone YES;
a YES on this decl alone would need explicit justification at the gate.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | EC division poly ω formula ψ(n-1)²ψ(n+2) invariant b₂ b₄                                        | partial | ω_n = (ψ_{n-1}²ψ_{n+2} − ψ_{n-2}ψ_{n+1}²)/(4y); 4yω_n recursion | Wikipedia "Division polynomials"; Silverman AEC Ch.III/Exercises. The ω **family** is standard; a scalar `6X²+b₂X+b₄` named "invar" is not surfaced. |
|  2 | WebSearch (general/most-general)  | "6x^2"/"6X²" EC division poly b2 b4 invariant ψ ω second coordinate                            | no   | — | Returned scalar-multiplication-via-division-polynomials papers (SubramanyaRao, Chen IET); none names this cofactor. |
|  3 | WebSearch (named-after / source)  | Silverman AEC ω_n recursion long Weierstrass "6x²+b₂x+b₄" ψ₄ ψ₃                                 | no (direct) | b₂,b₄ b-invariants; Ψ₃,Ψ₄ recursions confirmed | `6X²+b₂X+b₄` is not a *named* literature object; it is the implementation cofactor in `preΨ₄+Ψ₂Sq² = invar·Ψ₃`. |
|  4 | WebSearch (provenance)            | Junyan Xu / Angdinata Lean mathlib EC ω division poly Jacobian scalar mult                      | yes  | ITP 2023 group-law paper; mathlib EC dir | Confirms `invar` is part of the Xu–Angdinata ω development (file authors: "Junyan Xu, David Kurniadi Angdinata"); an in-flight upstreaming, not a textbook concept. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                            | n/a  | (dir absent) | No `references/` dir for NagellLutz, and no `refs/` store on this machine — recorded n/a. |
|  6 | nLab                             | division polynomial / elliptic divisibility sequence                                          | n/a  | — | nLab has no entry for the long-Weierstrass division-polynomial cofactors; not a categorical concept. Brief check only. |
|  7 | nCatLab                          | —                                                                                              | n/a  | — | Not a categorical concept. |
|  8 | Stacks Project                   | division polynomial / Weierstrass ω                                                            | n/a  | — | Stacks does not develop explicit division-polynomial cofactors; n/a. |
|  9 | MathOverflow / MSE               | ω division polynomial generality long Weierstrass form                                         | partial | confirms ω-family generality over any base | No named `invar`; consistent with #1–#3. |
| 10 | recent arXiv (≤5 yr)             | EC division polynomial recurrence / sequences (1909.12654, 2102.07573, 1303.4327 homogeneous)  | partial | homogeneous/EDS treatments | The cofactor appears only implicitly inside ω constructions; never isolated + named. |

The protocol passed: WebSearch ran 4 distinct queries (specific form, most-general "6x²" form,
named-after/Silverman, provenance); local refs checked (n/a, dir absent); nLab/Stacks/nCatLab checked
and recorded n/a with reasons; MathOverflow/arXiv channels checked. **ChatGPT MCP: unavailable this
session (per task brief — MCP down); compensated with the extra provenance WebSearch (#4) and direct
mathlib source reading.** This single gap is noted; it does not change the verdict, which rests on the
mathlib-source evidence (the ω TODO) and the K=0 call-site fact.

### Literature summary (Phase 3)

Concept identified as: the **scalar cofactor `6X²+b₂X+b₄`** in the factorisation
`preΨ₄ + Ψ₂Sq² = invar·Ψ₃`, internal to the construction of the **ω division polynomials**
(`ω_n`, second Jacobian coordinate of `[n]P`).
Sources agree on the standard form: the **ω family** is standard (Silverman AEC, Washington, Wikipedia,
PARI/GP `elldivpol`); the **scalar `invar` cofactor is NOT a named literature object** — it is an
implementation artifact specific to a formalisation that works over the *long* Weierstrass form.
Most general standard form: `ω_n` defined for a Weierstrass curve over any commutative ring (mathlib
already states `ψ`, `φ`, `Ψ₃`, `preΨ₄`, `Ψ₂Sq` at this generality).
Generality dimensions where the literature varies: base ring (`ℚ`/field in classical texts → arbitrary
commutative ring in mathlib; the project already takes the general `[CommRing R]`).
Disagreement with the literature: none on the math; the literature simply does not isolate `invar`.

This is the documented "literature returns no named object for the exact decl" signal: it pushes toward
NO-composable or BORDERLINE rather than YES-add-as-is *for this decl in isolation*.

---

### Generality analysis — `WeierstrassCurve.invar`

Literature-standard form (Phase 3): the ω family over an arbitrary commutative ring; `invar` itself is
not separately standardised.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]`        | commutative ring  | commutative ring (mathlib EC division-poly generality) | **NO** | Already maximally general for this API; `b₂,b₄,X,C` all need exactly `CommRing`. Matches mathlib `Ψ₂Sq`/`Ψ₃`/`preΨ₄` verbatim. |
| 2 | `(W : WeierstrassCurve R)` | long Weierstrass curve | long Weierstrass form | **NO** | The whole point of `invar` is to handle the *long* form (`6X²+b₂X+b₄` collapses to `6X²` only in short form); cannot weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical typeclass footprint to its mathlib siblings).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | bundled-hyp → typeclass/instance | no | — | `W : WeierstrassCurve R` is already the right bundling; this is a `def`, not a "let X be a foo" preamble. |
| 2 | sequences/metric → filters/topology | no | — | Purely algebraic polynomial identity; no limits. |
| 3 | construct → universal-property class | no | — | A concrete cofactor polynomial; no universal property to characterise. |
| 4 | set+closure-pred → bundled substructure | no | — | Not a substructure. |
| 5 | vector-space/field-specific → weaken typeclass | no | — | Already at `CommRing`. |
| 6 | 1-categorical → higher-categorical | no | — | Not categorical. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid | no | — | No index; it's a fixed degree-2 polynomial. |

Modern idiom available: **no.** One-line reason: `invar` is already in the contemporary mathlib idiom
its siblings use (`Ψ₂Sq`, `Ψ₃`, `preΨ₄` are all `R[X]` defs over `[CommRing R]` with `C`/`X`); there is
no cleaner reformulation — if anything the question is whether it should exist as a *named* def at all,
which is the Phase 6/7 packaging question, not a generality one.

---

### Diamond / defeq risk — `WeierstrassCurve.invar`  (Phase 4.5; kind = def)

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | Returns an `R[X]` value; introduces no instance, so no search path/diamond. |
| 2 | Reducibility leak | none | Not `@[reducible]`; semireducible like its siblings. Body is unfolded explicitly via `rw [invar]`, so no surprise `rfl`-unfolding downstream. |
| 3 | Non-canonical unfolding | low | No `@[simp]`; `simp` won't unfold it spontaneously. Authors always `rw` it deliberately. |
| 4 | Instance priority collision | none | Not an instance. |
| 5 | Universe issues | none | Monomorphic in `R : Type*`; same as `Ψ₂Sq`. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)
Overall risk: **NONE.** Top risks: none. (So risk does not constrain Phase 7.)

---

### Mathlib search-status: `WeierstrassCurve.invar`

[A] Lean-Finder       n/a this session (index tool intermittent) — compensated by [D]/[E] over the actual pinned mathlib tree
[B] Loogle            n/a this session — compensated by direct source grep of the pinned mathlib (authoritative for "is it there")
[C] LeanSearch        n/a this session — compensated by [D]
[D] Grep mathlib src  `invar` over `Mathlib/` → only `mainVar`/"invariant"-in-prose/`is_equiv_invariant` (unrelated); `6 * X` over whole `Mathlib/` → **zero hits**; `Ψ₂Sq ^ 2` over `Mathlib/` → **zero hits**.  ⇒ no hit
[E] Name pattern      `def invar`, `WeierstrassCurve.invar`, qualified, in mathlib EC tree → **zero hits**

Searched for both:
  - the user's current form (`invar = 6X²+b₂X+b₄`) — not in mathlib.
  - the literature-standard target (the **ω family** and the relation `preΨ₄+Ψ₂Sq²=invar·Ψ₃`) — mathlib
    has `ψ`, `φ`, `Ψ₃`, `preΨ₄`, `Ψ₂Sq`, `ΨSq`, `Φ` but **NOT `ω`** and **NOT** this factorisation. The
    mathlib file `DivisionPolynomial/Basic.lean` carries the literal TODOs:
    line 71 `* TODO: the bivariate polynomials ωₙ.` and line 83 `TODO: implementation notes for the
    definition of ωₙ.`

Concluded: **not in mathlib (grep/name-pattern exhausted over the pinned tree, plus the
literature-standard ω target). Moreover mathlib has an explicit open TODO for exactly the ω development
that `invar` underpins.**

NB on provenance: the project's own `DivisionPolynomial.lean`/`EllipticDivisibilitySequence.lean` are
deliberate *copies* of the mathlib files (renamed to avoid `normEDS` clashes); `invar` is added only in
the *new* `DivisionPolynomialOmega.lean`, so it is not "already in mathlib via the fork" — it is net-new
relative to mathlib.

---

### Call sites — `WeierstrassCurve.invar`

Internal use count (excluding the declaring file): **0**
External-to-file callers: **0 files**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside DivisionPolynomialOmega.lean) | — |

Within the declaring file, `invar` is used 3×: `preΨ₄_add_Ψ₂Sq_sq` (L60, the defining factorisation),
`preΨ₄_add_ψ₂_pow_four` (L65), and `ω_spec` (L85, via `rw [..., invar, ...]`). All three are the ω-family
plumbing. No project file outside `DivisionPolynomialOmega.lean` references the `invar` polynomial.

Inline-derivation grep (was `6X²+b₂X+b₄` re-derived elsewhere without `invar`?): **none** — the literal
`6 * X` appears nowhere else in the repo or mathlib.

Call-sites signal: **K = 0 external, ≥3 internal-same-file uses, no external re-derivation.** Per the
skill's table this is the "one-liner with K=0, no exemption" pattern → strong pull toward
NO-composable/inline — *except* that all uses sit inside a coherent, mathlib-wanted unit (the ω family),
which is the tension Phase 7 must resolve rather than mechanically inline.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.invar` be replaced by a ≤3-call mathlib composition at its (in-file) call sites?

`invar` is a *definition*, so "composition" means: can the 3 in-file lemmas that use it be written
*without* a named `invar`, by inlining `6X²+b₂X+b₄` (or `(preΨ₄+Ψ₂Sq²)/Ψ₃`) directly?

Attempt 1 — inline the literal `6 * X ^ 2 + C W.b₂ * X + C W.b₄` at each of the 3 sites.
  - Mathlib decls used: `Polynomial.C`, `Polynomial.X`, `WeierstrassCurve.b₂`, `WeierstrassCurve.b₄`
    (all exist in mathlib).
  - Result: **succeeds mechanically** — the `rw [invar]` steps become the inlined polynomial, and the
    `linear_combination … ; ring` / `C_simp; ring` proofs go through identically (the proofs already
    unfold `invar` immediately, so inlining changes nothing structurally).
  - Notes: this would make the three lemma statements/proofs more verbose but removes the named def.

Conclusion: **COMPOSABLE in the narrow sense** (the def is inlineable; it carries no defeq/diamond/API
weight). BUT this is the *wrong frame for this decl*: `invar` is not a standalone wrapper consumers
bypass — it is internal scaffolding for the **ω family**, which is itself a wanted mathlib addition
(open TODO). Deleting `invar` and inlining is only correct *if the ω family is not upstreamed*; if the ω
family goes to mathlib (the natural outcome), keeping a small named cofactor (or the equivalent) is a
reasonable authorial choice. Hence the composability is real but does not, by itself, dictate "delete" —
it feeds the BORDERLINE packaging question.

---

## Verdict: `WeierstrassCurve.invar`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the **ω family** is standard (Silverman/Washington/Wikipedia/PARI); the
  scalar `invar = 6X²+b₂X+b₄` is **not** a named literature object — it is an implementation cofactor of
  the long-Weierstrass-form ω construction (Xu–Angdinata, ITP 2023 lineage).
- Generality (Phase 4): **MAXIMALLY GENERAL** (identical `[CommRing R]` footprint to mathlib `Ψ₂Sq`/`Ψ₃`);
  Phase 4c: no modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib**; and mathlib's `DivisionPolynomial/Basic.lean` has an
  **explicit open TODO for `ωₙ`** (lines 71, 83) that this exact development fills.
- Composition (Phase 6): the def is **inlineable** (COMPOSABLE narrowly), and has **K=0 external call
  sites**; it is a `ONE-LINER WITHOUT-EXEMPTION`.

**Rationale:**

Two signals point in opposite directions, and resolving them is a packaging/taste judgment rather than a
fact the skill can settle. (a) *Pro-inline/NO:* `invar` is a one-line `def` with zero call sites outside
its own file, no defeq-barrier or diamond-anchor or stable-API-name exemption, and is unfolded by `rw`
at every use — exactly the profile of a helper that could be inlined into its three sibling lemmas with
no loss. (b) *Pro-keep/YES:* those three lemmas are the scaffolding of the **ω division-polynomial
family**, and mathlib's own `DivisionPolynomial/Basic.lean` carries a literal *TODO* for `ωₙ`. So the
*surrounding unit* is a genuine, explicitly-wanted mathlib contribution — and `invar` is the cofactor
that makes the central identity `preΨ₄ + Ψ₂Sq² = invar·Ψ₃` (hence the polynomiality of `ω n`) legible.
Whether a degree-2 cofactor that exists only to state that one factorisation deserves to survive as a
*named* mathlib def, or should be inlined into the ω-family lemmas during upstreaming, is precisely the
kind of micro-API decision the mathlib reviewer of the ω PR will make. The skill must not pre-empt it:
`invar` in isolation reads as NO-composable, but as part of the ω contribution it is defensible glue —
and it would be wrong to either "ship `invar` alone" or "delete it" without deciding the ω-family
question first.

**Numbered questions (≤5):**

1. **Is the ω-division-polynomial development (`ω`, `ψc`, `invar`, `ω_spec`, …) intended for upstreaming
   to mathlib** (it fills mathlib's open `ωₙ` TODO in `DivisionPolynomial/Basic.lean`)? If **yes**, this
   is assessed *as part of that PR*, not standalone.
2. If the ω family is upstreamed, **do you want `invar` to remain a named `def`**, or be **inlined** into
   `preΨ₄_add_Ψ₂Sq_sq` / `ω_spec` (it has K=0 external uses and is `rw`-unfolded everywhere)? A named
   cofactor aids readability of the `preΨ₄+Ψ₂Sq²=invar·Ψ₃` identity; inlining removes a one-liner.
3. If kept as a def, **should it be renamed**? "invar"/"invariant" is misleading (it is a cofactor, not
   an invariant of the curve, and it collides in spirit with the unrelated `EllSequence.invar` lemma);
   e.g. `omegaCofactor` / `preΨ₄AddΨ₂SqSqFactor` would be clearer.
4. If the ω family is **not** upstreaming, do you accept the alternative verdict **NO-composable-from-
   mathlib** for `invar` *as a standalone decl* — i.e. inline `6X²+b₂X+b₄` at its three in-file sites and
   drop the def?

**Next action:** answer Q1 first. If Q1 = yes (the natural reading — this is the Xu–Angdinata ω
development targeting mathlib's TODO), assess `invar` *inside* the ω-family PR via `/cleanup`/`/generalise`
on the whole `DivisionPolynomialOmega.lean` unit, and treat Q2/Q3 as that PR's reviewer questions. If
Q1 = no, re-run with the decision and the verdict resolves to **NO-composable-from-mathlib** (inline the
degree-2 polynomial at the 3 call sites; building blocks `Polynomial.C`, `Polynomial.X`,
`WeierstrassCurve.b₂`, `WeierstrassCurve.b₄`).

---

## Method gaps (honesty note)
- **ChatGPT MCP** unavailable this session (per task brief); compensated with an extra provenance
  WebSearch and direct reading of the pinned mathlib source. The verdict does not hinge on the missing
  channel — it rests on the mathlib `ωₙ` TODO + the K=0 call-site fact, both verified directly.
- **lake build** not run (local build stale per brief); the decl statement was read from source and its
  type is unambiguous (`def invar : R[X] := …`). No `sorry`.
- **Loogle/LeanSearch/Lean-Finder** intermittent; the authoritative "is it in mathlib" check is the grep
  over the pinned `.lake/packages/mathlib` tree, which is exhaustive for this purpose.
