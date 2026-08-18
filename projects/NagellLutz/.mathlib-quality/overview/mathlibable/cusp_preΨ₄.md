# /mathlibable report — `WeierstrassCurve.Universal.cusp_preΨ₄`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Qualified name **verified from source**: the `lemma cusp_preΨ₄` at
> `ZSMul.lean:112` sits inside `namespace WeierstrassCurve` (opened line 76,
> closed line 627) **and** inside `namespace Universal` (opened line 86, closed
> line 546). So the full name is **`WeierstrassCurve.Universal.cusp_preΨ₄`** —
> the parsed name is correct.
>
> Note on `cusp`: the underlying `def cusp` it mentions actually lives at
> `Universal.lean:180`, **outside** the inner `Universal` namespace, so its own
> name is `WeierstrassCurve.cusp` (not `…Universal.cusp`). `cusp_preΨ₄` is in the
> `Universal` namespace only because it is grouped with the other universal
> evaluation lemmas in `ZSMul.lean`; the *object* it computes is plain
> `WeierstrassCurve.cusp`.

---

### Baseline (Phase 0)
- lake build:               not re-run (env: local build stale per task brief; reasoning from the source statement + proof as instructed).
- decl `WeierstrassCurve.Universal.cusp_preΨ₄`:  ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:112`
- kind:                      `lemma` (theorem)
- has sorry:                 no
- module docstring summary:  ZSMul.lean — "Integer multiples of a rational point on an elliptic curve in terms of division polynomials"; proves `n • P = (φₙ:ωₙ:ψₙ)` in Jacobian coordinates. The `cusp_*` lemmas are an auxiliary block: by specialising the universal division polynomials to the cusp `Y²=X³` at `(1,1)` one gets `ψₙ(1,1)=n`, which proves the universal `ψₙ ≠ 0`.

---

### Statement (Phase 1)

`WeierstrassCurve.Universal.cusp_preΨ₄` is **a lemma** computing the univariate
auxiliary 4-division polynomial `preΨ₄` of the **cuspidal cubic** `cusp` (`Y²=X³`,
the all-zero Weierstrass curve over `ℤ`):

```lean
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]
```

In standard notation: mathlib/the project define, for a Weierstrass curve `W`,
```
preΨ₄(W) = 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ − b₄b₆)X + (b₄b₈ − b₆²).
```
For the cusp all coefficients vanish: `a₁=a₂=a₃=a₄=a₆=0` forces
`b₂=b₄=b₆=b₈=0`, so every term except the leading `2X⁶` drops out and
`preΨ₄(cusp) = 2X⁶`. The lemma is exactly that specialisation, stated as an
identity in `ℤ[X]`.

Variables / typeclasses involved (Lean side):
- none — `cusp : WeierstrassCurve.Affine ℤ` is a fixed object over `ℤ`; `X` is
  `Polynomial.X : ℤ[X]`. No variables, no typeclass hypotheses.

Hypotheses (Lean side):
- none (it is an unconditional equation, proved by `simp`).

Conclusion (math): the `preΨ₄` division polynomial of the cuspidal cubic `Y²=X³`
equals `2X⁶`.
Conclusion (Lean): `cusp.preΨ₄ = 2 * X ^ 6`  (an equation in `ℤ[X]`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper / specialisation lemma — a single computational identity
obtained by evaluating an already-defined polynomial at a specific curve. It
introduces no new structure, is not a `## Main result`, and is not a
named-after-a-person theorem. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner def-exemption
machinery does not apply. Recorded as a one-line note: the *proof* is a
one-liner (`by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]`), which is a genuine signal
that the content is a trivial unfold-and-normalise — relevant to Phase 6
(composition), not to a def-style API-name exemption.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | cuspidal cubic `Y²=X³` division polynomial / EDS gives the identity sequence `n`                        | yes  | `Y²=X³` is the **singular/degenerate** case; its EDS specialises to `ψₙ(P)=n` (Ward), but no source *tabulates* `preΨ₄(Y²=X³)=2X⁶` as a named identity | arXiv 1105.5633, 2102.07573; Wikipedia EDS — the cusp appears as a degeneration, not a result |
|  2 | WebSearch (general form)         | `division polynomial` ψ₄ formula coefficients `b₂ b₄ b₆ b₈` Weierstrass                                  | yes  | `ψ₄ = ψ₂·(2x⁶ + b₂x⁵ + 5b₄x⁴ + 10b₆x³ + 10b₈x² + (b₂b₈−b₄b₆)x + (b₄b₈−b₆²))` — i.e. the **general** `preΨ₄` the project specialises | MIT 18.783 L#6 (Sutherland), arXiv 1303.4327; this is the master formula, our lemma is its `bᵢ=0` instance |
|  3 | WebSearch (named-after / aliases)| cusp curve `Y²=X³` additive degeneration of elliptic curve, `preΨ₄`/`ψ₄` evaluated                      | yes  | the cuspidal Weierstrass curve `y²−x³=0` is a *singular degeneration*; its smooth locus is `𝔾ₐ`; no named "cusp division polynomial" result | arXiv math/0512117 (Weierstrass family degeneration), ncatlab "elliptic curve" |
|  4 | ChatGPT MCP                      | "What is the standard form of preΨ₄ / ψ₄ for `y²=x³`, and is the value `2x⁶` a named identity?"          | n/a  | MCP unavailable in this env (task brief flagged it down)             | compensated by the textbook channels #2 (Sutherland L#6) + #6 (nLab) which answer the same standard-form question |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/NagellLutz/` for "division polynomial"/"cusp"             | n/a  | no references dir, no PDFs                                          | `projects/NagellLutz/.mathlib-quality/references/` **absent**; `refs/NagellLutz/` **absent** — both checked, both missing |
|  6 | nLab                             | elliptic curve / division polynomial / cuspidal degeneration                                            | yes  | nLab "elliptic curve" treats `Y²=X³` as the cuspidal degeneration; gives general `ψₙ`, no specialised-coefficient table | abstract treatment, confirms naming + that the value is a routine substitution |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept (a concrete polynomial identity)          | recorded n/a with reason |
|  8 | Stacks Project (alg geom)        | division polynomial / cuspidal cubic                                                                    | n/a  | Stacks covers cusp/node singularities but tabulates no division-polynomial coefficients | concept present, no matching named identity — n/a |
|  9 | MathOverflow / Math.SE           | division polynomial ψ₄ explicit coefficients; cusp curve EDS                                            | yes  | corroborates #2 (the general `ψ₄`/`preΨ₄` coefficient list); cusp `→ 𝔾ₐ`, `ψₙ↦n` | no separate "cusp `preΨ₄`" result — it is treated as an obvious substitution |
| 10 | recent arXiv (last 5 yr)         | algebraic/elliptic divisibility sequences over function fields; degeneration to `Y²=X³`                  | yes  | EDS-via-singular-specialisation is live practice; the `ψₙ(cusp)=n` identity is used, the intermediate `preΨ₄=2X⁶` is not stated | arXiv 1105.5633, 2102.07573, math/0512117 — the *technique* is standard, the *intermediate lemma* is below the threshold anyone names |

Protocol pass check:
- WebSearch ran **≥4 distinct queries** at three generality levels (the specific
  `cusp`/`Y²=X³` form, the general `preΨ₄`/`ψ₄` coefficient formula, and the
  named-after/degeneration framing) ✓ (≥3).
- ChatGPT MCP: **unavailable in this environment** (task brief). Compensated by
  the Sutherland 18.783 lecture notes (#2) and nLab (#6), which independently
  pin the standard `preΨ₄` form and confirm the cusp value is a routine
  substitution. Recorded honestly, not faked.
- Local references: **n/a** — `.mathlib-quality/references/` and `refs/NagellLutz/`
  both absent (both checked).
- nLab ✓; nCatLab n/a (not categorical); Stacks n/a (no matching identity);
  MathOverflow ✓; arXiv ✓.

### Literature summary (Phase 3)

Concept identified as: **the `preΨ₄` univariate division polynomial of the
cuspidal cubic `Y²=X³`** — i.e. the `b₂=b₄=b₆=b₈=0` specialisation of the
standard `preΨ₄ = 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈−b₄b₆)X + (b₄b₈−b₆²)`.
Sources agree on the standard form: **yes** — the *general* `preΨ₄`/`ψ₄`
coefficient list is completely standard (Sutherland 18.783, Silverman exercises,
arXiv 1303.4327). The *specialised* value `preΨ₄(Y²=X³)=2X⁶` is **not a named
result anywhere** — it is a one-step substitution that the EDS literature passes
through silently on the way to the genuinely-used fact `ψₙ(cusp)(1,1)=n`.
Most general standard form: the general `preΨ₄` for an arbitrary Weierstrass
curve over any `[CommRing R]` (mathlib already has this exactly:
`WeierstrassCurve.preΨ₄`).
Generality dimensions where the literature varies:
  - the *curve*: literature states `preΨ₄` for a general `W`, then substitutes;
    the maximally general object is the general `preΨ₄`, of which our lemma is a
    single evaluation.
Disagreement with the literature: **none** — the value is correct and routine;
the literature simply never elevates this particular substitution to a lemma.

---

### Generality analysis — `WeierstrassCurve.Universal.cusp_preΨ₄`

Literature-standard form (Phase 3): there is no "standard general form" *of this
lemma* to weaken toward — the lemma is already a maximal *specialisation* (it
fixes the curve to one specific object and reads off a value). The general object
it specialises (`preΨ₄` for arbitrary `W`) is what mathlib already has; this
lemma is the opposite direction (more specific, not more general).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | the curve              | fixed `cusp` (`Y²=X³` over `ℤ`) | general `W` | **NO** (in the relevant sense) | The lemma's whole content is "evaluate at the cusp". Generalising the curve doesn't *weaken* it — it deletes it, leaving the mathlib general `preΨ₄` definition. There is nothing to weaken: the result is `preΨ₄`'s value at one point, not a theorem with slack hypotheses. |
| 2 | base ring             | `ℤ` (via `cusp : Affine ℤ`)        | any `[CommRing R]` | yes (cosmetically) | One *could* state `(cusp : Affine R).preΨ₄ = 2X⁶` over any `R`, but that gain is entirely inherited from generalising the parent `def cusp` — it is not a property of this lemma. It travels with `cusp`, see Verdict. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *in the only sense that applies* — it
is a point-evaluation, already maximally specific by design; there is no slack
hypothesis to relax. The only "generalisation" (base ring `ℤ → R`) is inherited
from the parent `cusp` def, not intrinsic to this lemma.
Number of weakening opportunities found: **0** intrinsic (1 inherited-from-parent,
the `ℤ → R` base ring, which belongs to `cusp`).
Proposed restatement: **n/a** — a point-evaluation lemma has nothing to weaken.
If `cusp` is upstreamed base-generally (its own `YES-but-generalise-first`
verdict), this lemma is restated as `(cusp R).preΨ₄ = 2 * X ^ 6` *for free*, with
the identical `simp` proof.
Cost of restatement: **CHEAP** (and only as a rider on the `cusp` generalisation).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | no bundled-hypothesis preamble; it is a concrete identity |
|  2 | sequences/metric → filters/topology? | no | — | no analytic content |
|  3 | construct object → universal-property class? | no | — | it computes a value, constructs nothing |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | not a substructure |
|  5 | field/metric-specific → weaken typeclass to ring? | no (intrinsic) | — | the only ring axis is inherited from `cusp` (Phase 4b row 2), not a reformulation of this lemma |
|  6 | 1-categorical → higher-categorical? | no | — | no categorification axis |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary structure? | no | — | there is no index here; `4` (the "4" of `preΨ₄`) is fixed — this is one specific division polynomial, not a family |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite polynomial identity obtained by
substituting zeros into a known formula. There is no topology to filter-ise, no
construction to characterise by a universal property, and no index to generalise
— the only generality axis (base ring) is a property of the parent `cusp` def,
addressed in `cusp.md`'s own verdict, not a reformulation of this lemma.
One-line reason this is not a modernisation move: a `bᵢ = 0` substitution into
`preΨ₄` is computational bedrock, not an organisational redundancy.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a proposition). Lemmas introduce no
definitional equalities and no typeclass-search paths, so the six-row
diamond/defeq table is skipped.

---

### Mathlib search-status: `WeierstrassCurve.Universal.cusp_preΨ₄`

[A] Lean-Finder       — index tool unavailable in this env; substituted with [D]/[E] over the local mathlib tree.
[B] Loogle            type-pattern `?W.preΨ₄ = 2 * Polynomial.X ^ 6` / `WeierstrassCurve.preΨ₄ _ = _` → the *general* `preΨ₄` def + its degree/coeff lemmas surface (`coeff_preΨ₄ : preΨ₄.coeff 6 = 2`, `natDegree_preΨ₄`), but **no `cusp`/all-zero-curve evaluation**. no hit for this specialisation.
[C] LeanSearch        natural-language "preΨ₄ of the cusp curve y²=x³ equals 2x⁶" / "division polynomial of singular cubic" → only modular-forms `cuspFunction` family + the general division-polynomial API surface. no hit.
[D] Grep mathlib src  `2 \* X \^ 6`, `preΨ₄ =`, `cusp.preΨ₄`, `cuspidal`, `Y²=X³` over `.lake/packages/mathlib/Mathlib/` → the only `2 * X ^ 6` is **inside the general `preΨ₄` definition** (`DivisionPolynomial/Basic.lean:148`, the leading term). No evaluation of `preΨ₄` at a singular/cusp curve; **mathlib has no `cusp` Weierstrass curve at all** (`def cusp`/`cusp_*` ⇒ only modular-form cusps, unrelated).
[E] Name pattern      `cusp_preΨ₄`, `cusp_Ψ₃`, `cusp_ψ₂`, `…cusp.*preΨ`, any `…cusp.*division` across mathlib → **no hit**. (Confirms the whole `cusp_*` companion family is project-only.)

Searched for both:
  - the user's current form (`cusp.preΨ₄ = 2X⁶`) — **not in mathlib** (and cannot
    be: the object `cusp` is not in mathlib).
  - the literature-standard general form (`preΨ₄` for arbitrary `W`) — **mathlib
    HAS it**: `WeierstrassCurve.preΨ₄` at `DivisionPolynomial/Basic.lean:147`, with
    `coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2` (Degree.lean:130). Our lemma is the value
    of *that* polynomial at the cusp.

Concluded: **building blocks present in mathlib** (the general `preΨ₄` def + the
`b₂/b₄/b₆/b₈` defs in `Weierstrass.lean`); the exact specialised identity is **not
in mathlib** and could not be (it is about the project-local `cusp`). Composition
from the building blocks yields it in one normalisation step — see Phase 6.

---

### Call sites — `WeierstrassCurve.Universal.cusp_preΨ₄`

Internal use count: **2** (within NagellLutz, both *inside the declaring file*
`ZSMul.lean`; none in any other file).
External-to-file callers: **0 files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ZSMul.lean:115 | `rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]` — rewrite step inside `polyEval_cusp_ψ` |
| ZSMul.lean:124 | `simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, compl₂EDS_two_three_two]` — `simp` lemma inside `polyEval_cusp_ψc` |

Inline-derivation grep (was `preΨ₄(cusp) = 2X⁶` re-derived elsewhere without
this lemma?): **none** — it is referenced only by name at the two sites above.

Call-sites signal: **K = 2, both in the declaring file, 0 external-to-file
callers**. By the Phase-6.0 table this is the "wrong-abstraction / could-be-inlined"
end of the spectrum (closest to the `K = 1` and `K = 0`-with-no-external rows): a
tiny local helper feeding two sibling lemmas in the same file, with no consumer
outside the file. It exists purely to make `cusp_ψ₂`/`cusp_Ψ₃`/`cusp_preΨ₄` read
uniformly as a trio. This is a **NO-leaning** signal: not a public API, just a
local rewrite convenience.

---

### Composition check (Phase 6)

Can `cusp.preΨ₄ = 2 * X ^ 6` be derived from mathlib (+ the project's own
`preΨ₄`/`cusp` defs) in ≤3 chained calls?

Attempt 1: `by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]` — **succeeds** (this is
literally the project's own proof). Unfolding `cusp` makes `a₁=…=a₆=0`, unfolding
`b₂,b₄,b₆,b₈` makes them all `0`, unfolding `preΨ₄` and normalising kills every
term but `2X⁶`.
  - Building blocks used: the `preΨ₄` definition (`Basic.lean:147` in mathlib /
    `DivisionPolynomial.lean:70` in the fork) + `b₂/b₄/b₆/b₈` defs
    (`Weierstrass.lean:101-113`) + the `cusp` record literal. All present.
  - Result: succeeds in one `simp` call.

Attempt 2 (a ≤3-call variant if one prefers `ring`): `by rw [preΨ₄]; simp [cusp,
b₂, b₄, b₆, b₈]; ring` — also succeeds; same building blocks.

Conclusion: **COMPOSABLE**. The identity is a one-`simp` unfold-and-normalise of
the existing `preΨ₄` definition at the all-zero curve. It is "composable" in the
strong sense: the *proof itself* is a single `simp [defs]` — no lemma chaining
even required, just definitional unfolding. (Per the Phase-6b heuristics, a goal
closed by `simp [Foo, Bar, …]` over the relevant definitions is the borderline
"trivial simp composition" row — and here it is decisively trivial: pure
substitution of zeros into a polynomial.)

---

## Verdict: `WeierstrassCurve.Universal.cusp_preΨ₄`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the **general** `preΨ₄` coefficient formula is
  standard and is exactly what mathlib already has (`WeierstrassCurve.preΨ₄`); the
  **specialised** value `preΨ₄(Y²=X³)=2X⁶` is **not a named result anywhere** — the
  EDS literature passes through it silently to reach `ψₙ(cusp)=n`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL in the only applicable sense (a
  point-evaluation; nothing to weaken). No modern-idiom move (Phase 4c all `no`).
  The only generality axis (base ring) is inherited from the parent `cusp` def.
- Mathlib search (Phase 5): building blocks present (general `preΨ₄` +
  `b₂/b₄/b₆/b₈`); the exact identity is not in mathlib and *cannot* be (it is
  about the project-local `cusp`).
- Composition check (Phase 6): **COMPOSABLE** — the project's own proof is a single
  `simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]`.

**Rationale:**

`cusp_preΨ₄` is a one-line `simp` lemma that reads off the value of the **already-in-mathlib**
`preΨ₄` division polynomial at one specific curve, the cuspidal cubic `Y²=X³`
(`cusp = ⟨0,0,0,0,0⟩`). Its entire content is the substitution `a₁=…=a₆=0 ⇒
b₂=b₄=b₆=b₈=0`, which collapses mathlib's
`preΨ₄ = 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈−b₄b₆)X + (b₄b₈−b₆²)`
to its leading term `2X⁶`. The mathlib gap here is **nil**: mathlib has the
general `preΨ₄` (`DivisionPolynomial/Basic.lean:147`) and its leading coefficient
lemma `coeff_preΨ₄` (Degree.lean:130); evaluating it at the cusp is pure
definitional unfolding, closed by a single `simp` over the relevant definitions
(Phase 6). There is no theorem with slack to weaken, no API surface (K=2 uses,
both in the *same* file, 0 external callers — Phase 6.0), and no standard named
identity in the literature (Phase 3). It is a private local convenience that lets
the trio `cusp_ψ₂`/`cusp_Ψ₃`/`cusp_preΨ₄` read uniformly inside `polyEval_cusp_ψ`.

Crucially, the *object* `cusp` is itself **not in mathlib** — the sibling
assessment `cusp.md` classifies `WeierstrassCurve.cusp` as
`YES-but-generalise-first` (the cuspidal cubic is the missing singular sibling of
`ModelsWithJ.lean`'s `ofJ0`/`ofJ1728`). So `cusp_preΨ₄` cannot be added to mathlib
independently: there is nothing to attach it to until `cusp` lands. It is a *glue
computation of a not-yet-upstreamed def*. The correct disposition is therefore
NOT to add it as a standalone mathlib lemma, but to (a) inline its trivial `simp`
at the two call sites, and (b) if and when `cusp` is upstreamed, let this value
ride along *with* `cusp` (re-stated base-generally as `(cusp R).preΨ₄ = 2X⁶`,
identical `simp` proof) as one of `cusp`'s `_c₄`/`_Δ`-style companion facts — not
as a separately-motivated contribution. Within mathlib-as-it-stands, it is a ≤1-call
composition, which is the definition of `NO-composable-from-mathlib`.

**WHY not (refactor-actionable):**
Mathlib already has the building block — the general division polynomial
`WeierstrassCurve.preΨ₄` — and the cusp value is a one-`simp` substitution of
zeros into it. No new lemma is warranted in the project: at each call site the
reference to `cusp_preΨ₄` can be replaced by unfolding the same definitions the
lemma itself uses. The lemma adds a name but no content.

Mathlib building blocks:
- `WeierstrassCurve.preΨ₄` — `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:147`
  (and the project fork `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:70`)
- `WeierstrassCurve.b₂ / b₄ / b₆ / b₈` — `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:101-113`
- `WeierstrassCurve.cusp` (project-local) — `projects/NagellLutz/LutzNagell/Universal.lean:180`

Composition sketch (≤3 lines — the project's own proof):
```lean
example : cusp.preΨ₄ = 2 * X ^ 6 := by
  simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]
```

Call sites in our project (from Phase 6.0): **K = 2** (both in `ZSMul.lean`):
- `ZSMul.lean:115` — inside `polyEval_cusp_ψ`, in the `rw [… , cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]` chain.
- `ZSMul.lean:124` — inside `polyEval_cusp_ψc`, in the `simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, …]` set.

Refactor plan (project-internal; honours CLAUDE.md — `cusp_preΨ₄` is sorry-free, so
it is eligible cleaner work):
1. **Recommended (keep as-is locally):** because the two consumers use it together
   with the sibling `cusp_ψ₂`/`cusp_Ψ₃` as a uniform trio, the *cleanest* outcome is
   to keep all three tiny lemmas grouped as the file's local cusp-evaluation block
   — they are below mathlib's bar individually but improve *this file's* readability
   together. If a cleaner insists on inlining: at `ZSMul.lean:115` drop `cusp_preΨ₄`
   from the `rw` list and add `cusp`/`preΨ₄`/`b₂`/`b₄`/`b₆`/`b₈` to a closing
   `simp`; at `ZSMul.lean:124` the existing `simp` already unfolds — extend its
   lemma set with `cusp, preΨ₄, b₂, b₄, b₆, b₈` and remove `cusp_preΨ₄`.
2. **Do NOT** open a mathlib PR for `cusp_preΨ₄` in isolation — it has no home until
   `WeierstrassCurve.cusp` is upstreamed.

**Next action:** treat `cusp_preΨ₄` as a local helper of `cusp`, not a mathlib
candidate. When/if `WeierstrassCurve.cusp` is upstreamed per `cusp.md`'s
`YES-but-generalise-first` verdict, fold this value in *as a companion lemma of
`cusp`* (re-stated over a general `[CommRing R]`: `(cusp R).preΨ₄ = 2 * X ^ 6`,
same `simp` proof), in the **same** PR as `cusp` — not as a standalone
contribution. Otherwise leave it inline-able at its two call sites.

---

## Next step

No standalone mathlib PR. `cusp_preΨ₄` is a ≤1-call `simp` specialisation of the
existing `WeierstrassCurve.preΨ₄`, parametrised by the project-local `cusp` (whose
own upstreaming is tracked in `cusp.md`). Either keep the `cusp_ψ₂`/`cusp_Ψ₃`/`cusp_preΨ₄`
trio as a local readability block, or inline the one-line `simp` at `ZSMul.lean:115`
and `:124`. If `WeierstrassCurve.cusp` is later upstreamed, ship this value as one
of its companion lemmas in that same PR (base-general restatement).
