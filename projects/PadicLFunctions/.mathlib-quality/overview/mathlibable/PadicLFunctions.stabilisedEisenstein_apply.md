# `/mathlibable` report — `PadicLFunctions.stabilisedEisenstein_apply`

Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task note: build may be stale/slow; Phase-0 source-fallback used)
- decl `PadicLFunctions.stabilisedEisenstein_apply`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:351`
- kind:                      theorem
- has sorry:                 no (proof is `change … ; rw [coe_stabilisedDiff] ; simp only […]`)
- module docstring summary:  "The q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side)" — defines `E_k^{(p)} = E_k − p^{k−1}E_k(p·)` as a genuine `Γ₀(p)`-modular form and proves its pointwise formula and q-expansion.

---

### Statement (Phase 1)

`PadicLFunctions.stabilisedEisenstein_apply` is **a theorem** stating the following:

Let `p` be a prime and `k ≥ 3`. The bundled weight-`k`, level-`Γ₀(p)` modular form
`stabilisedEisenstein p hk` — the project's `p`-stabilisation of the normalised level-one
Eisenstein series — has underlying function value, at any point `z` of the upper half-plane,
equal to `E_k(z) − p^{k−1}·E_k(p·z)`, where `E_k` is mathlib's normalised Eisenstein modular form
`EisensteinSeries.E hk` and `p·z = pScale p z` is the upper-half-plane point obtained by scaling
`z` by `p`. In words: *the constructed `Γ₀(p)`-modular form evaluates to the classical
p-stabilisation expression.* This is the "value / coercion" lemma that connects the bundled
`ModularForm` object to the concrete function it was built from (RJW TeX 2394, pointwise form).

Variables / typeclasses involved (Lean side):
- `(p : ℕ)` with `[hp : Fact p.Prime]` — the prime of stabilisation (the parameter `p` of the `namespace`-level `variable`).
- `{k : ℕ}` — the weight.
- `(hk : 3 ≤ k)` — weight ≥ 3 (the threshold for `EisensteinSeries.E` to be defined / a modular form).
- `(z : ℍ)` — the evaluation point in the upper half-plane.

Hypotheses (Lean side):
- `hk : 3 ≤ k` — needed only so that mathlib's `EisensteinSeries.E hk` exists; no analytic hypothesis is used by this lemma itself.

Conclusion (math): the constructed `Γ₀(p)`-modular form's value at `z` is `E_k(z) − p^{k−1}E_k(pz)`.

Conclusion (Lean):
`stabilisedEisenstein p hk z = ModularForm.E hk z - (p : ℂ) ^ (k - 1) * ModularForm.E hk (pScale p z)`
(an equation in `ℂ`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a `*_apply` value/coercion lemma — it unfolds a bundled `ModularForm` to the pointwise
expression it was defined from. It introduces no new structure and is not itself a named theorem; it
is auxiliary API for the def `stabilisedEisenstein`. (The *object* `stabilisedEisenstein` and the
q-expansion theorem `hasSum_stabilisedEisenstein` are the BIG declarations in this file; this lemma
is their glue.)

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: n/a — kind is `theorem`, not `def`.
One-liner verdict: n/a (kind is theorem/lemma, not def).

The proof body is 4 substantive lines (`haveI`, a `have hpt`, a `change`, a `rw`, a `simp only`),
i.e. a short coercion-unfold proof. The Phase-2b def-oriented exemption table does not apply. This is
recorded for framing: the *content* is definitional bookkeeping, which biases Phase 7 toward a NO
bucket (see Phase 6/7).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

The literature question has two layers, both searched:
(i) the **mathematical object** — the p-stabilisation `E_k − p^{k−1}E_k(p·)` and its defining formula;
(ii) the **lemma kind** — a "value of a constructed modular form" / coercion lemma, which is an API
artifact rather than a named mathematical result.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | `p-stabilization Eisenstein series E_k(z) - p^{k-1} E_k(pz) definition modular form`                   | yes  | `(E_k)^*(z) := E_k(z) − p^{k−1}E_k(pz) ∈ M_k(Γ₀(p))`             | Kawamura (arXiv:1207.0198) states *verbatim* `E_{2k}(z) − p^{2k−1}E_{2k}(pz) ∈ M_{2k}(Γ₀(p))` as the ordinary p-stabilisation; "natural generalization of the ordinary Λ-adic Eisenstein series for GL(2)". The RHS matches our theorem exactly. |
|  2 | WebSearch (general form / U_p)   | `ordinary p-stabilization Eisenstein series level Gamma_0(p) eigenform U_p eigenvalue`                  | yes  | p-stabilisation is the canonical way to produce a `U_p`-eigenform on `Γ₀(p)` with unit eigenvalue | Standard Hida-theory construction; the level-`p` stabilisation is a `U_p`-eigenfunction. |
|  3 | WebSearch (named-after / Hida–Wiles aliases) | `Hida theory ordinary Lambda-adic Eisenstein series GL2 stabilization E_k pz definition Wiles`         | yes  | same construction; attributed to Hida & Wiles (Λ-adic Eisenstein for GL(2)) | The construction is classical and named (ordinary/Hida–Wiles p-stabilisation). Confirms the *object* is standard. |
|  4 | ChatGPT MCP                      | (intended: "standard definition + generality + historical evolution of the p-stabilisation E_k−p^{k−1}E_k(p·)") | n/a  | —                                                                | **ChatGPT MCP not configured in this environment** (only Asana/Atlassian/Box-style MCP servers present; no ChatGPT server). Recorded n/a; compensated with an extra WebSearch query (#3) and the direct mathlib-source reads in Phase 5. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` for "stabilis"/"Eisenstein"                | n/a  | (no references dir; `refs/` absent)                              | `references/` directory does not exist; `refs/PadicLFunctions/` (the RJW PDF store) is local-only per CLAUDE.md and is absent in this checkout. The module docstring's own citations (RJW TeX 2367–2394; Miyake §4.6 Lem 4.6.1) substitute. Recorded n/a. |
|  6 | nLab                             | "Eisenstein series" / "p-stabilization" (conceptual)                                                   | no   | nLab has Eisenstein series but no dedicated p-stabilisation / "value of a modular form" page | nLab is thin on the arithmetic p-stabilisation; no clean abstract statement of a coercion lemma. Not load-bearing here. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not a categorical concept                                        | The target is an evaluation/coercion lemma for a bundled function; no categorical content. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept                                | Classical analytic modular forms; out of Stacks' scope. |
|  9 | MathOverflow / Math.StackExchange| (covered by #1–#3 result set; p-stabilisation `E_k − p^{k−1}E_k(pz)` discussed widely)                  | yes  | same `M_k(Γ₀(p))` form                                           | Consistent with #1–#3; no variant of the *defining formula* found. |
| 10 | recent arXiv (last 5 years)      | (Kawamura arXiv:1207.0198, updated 2023; Siegel-Eisenstein level-`p` arXiv:2505.06956, 2025)           | yes  | `E_k(z) − p^{k−1}E_k(pz)` and its Siegel/symplectic generalisations | The GL(2) scalar case is the base case of an active research line (Siegel/Sp(2n) p-stabilisations). Confirms the object is standard and being generalised, never that the *value lemma* is a named result. |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific
defining formula, general `U_p`-eigenform framing, Hida–Wiles named form); ChatGPT MCP recorded `n/a`
with the unavailable-server reason and compensated; local refs recorded `n/a` with reason; nLab
checked; nCatLab/Stacks recorded `n/a` with reasons; MathOverflow/arXiv checked.

#### Literature summary (Phase 3)

Concept identified as: **the (ordinary) p-stabilisation of the weight-`k` Eisenstein series**,
`E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)`, a modular form of weight `k` and level `Γ₀(p)`
(Hida, Wiles; Kawamura arXiv:1207.0198; RJW §8).

Sources agree on the standard form: **yes** — the defining formula `E_k(z) − p^{k−1}E_k(pz)` and the
level `Γ₀(p)` are uniform across every source found. Our theorem's RHS is this formula verbatim.

Most general standard form (of the *object*): for the GL(2) scalar Eisenstein series, the form is
fixed; the only "generality" axes are (a) adding a Dirichlet nebentypus character and the second
`U_p`-root (`E_k − β·E_k(p·)` for the two roots of `X² − a_p X + p^{k−1}`, here `a_p = 1 + p^{k−1}`,
giving the ordinary root `α = 1` and the stabilisation `E_k − p^{k−1}E_k(p·)`), and (b) the
Siegel/symplectic generalisation `Sp(2n)` (Kawamura). Neither changes the GL(2) defining formula.

Generality dimensions where the literature varies (for the *object*, not this lemma):
  - Group: GL(2) (this project) → Sp(2n) (Kawamura). Out of scope for a scalar value lemma.
  - Nebentypus / `U_p`-root: trivial character + ordinary root here; can carry a character and a
    chosen root. A generalisation axis for the *def*, not for its `_apply` lemma.

**Crucial distinction for this declaration.** The literature is about the *object*
`E_k − p^{k−1}E_k(p·)`. The target `stabilisedEisenstein_apply` is **not that object** — it is the
Lean *value/coercion lemma* asserting that the bundled `ModularForm` named `stabilisedEisenstein`
evaluates to that expression. "Value of a constructed modular form" lemmas have no name in the
mathematical literature: they are formalisation-bookkeeping, the `f.toFun z = <body> z` of a bundled
structure. The literature confirms the *RHS expression* is standard; it says nothing about the lemma,
because the lemma is an artifact of having bundled the function into a `ModularForm`.

Disagreement with the literature: **none** on the formula. The RHS is exactly the textbook form.

---

### Generality analysis — `stabilisedEisenstein_apply` (Phase 4)

Literature-standard form (from Phase 3): `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz) ∈ M_k(Γ₀(p))`.
This is the standard form of the **object**; the lemma under assessment is the value-extraction for
the project's realisation of that object.

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | `[Fact p.Prime]`              | `p` prime                                 | `p` prime (stabilisation is at a prime) | no (meaningfully)   | The stabilisation is defined at a prime; the def `stabilisedEisenstein` requires it (and `pScale` uses `hp.out.pos`). Not a weakening target for a value lemma. |
| 2 | `(hk : 3 ≤ k)`                | weight ≥ 3                                | weight ≥ 3 (for `E_k` to exist; classically `k ≥ 4` even) | no                  | Inherited from mathlib's `EisensteinSeries.E hk` domain; cannot weaken below 3 because the underlying object isn't defined. |
| 3 | `(z : ℍ)`                     | a point of the upper half-plane           | a point of `ℍ`                          | no                  | The value is pointwise on `ℍ`; nothing to generalise. |

This is a value lemma: its "generality" is entirely inherited from the def `stabilisedEisenstein`
and from mathlib's `EisensteinSeries.E`. There are no free hypotheses to weaken at the lemma level —
any generalisation belongs to the *def* (character/root/group axes from Phase 3), not to its `_apply`.

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (at the lemma level — it is the value lemma of a fixed def;
all generalisation axes live on the def, which is out of this lemma's scope).
Number of weakening opportunities found: **0** (at the lemma level).
Proposed restatement: none — a value lemma cannot be "generalised" independently of its def.
Cost of restatement: n/a.

#### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | Could "let X be a foo" preambles become typeclasses / instances?                                  | no       | — | The hypotheses are already typeclass (`Fact p.Prime`) + the minimal `3 ≤ k`; nothing to bundle. |
|  2 | Sequences/metric → filters/topological?                                                           | no       | — | A pointwise complex equation; no limit/topology to filter-ise. |
|  3 | Construction → universal-property class?                                                          | no       | — | This *is* the construction's value lemma; there is no universal property to characterise the p-stabilisation by (it's an explicit linear combination). |
|  4 | set-with-closure-predicate → bundled-substructure type?                                           | no       | — | No subobject involved; `stabilisedEisenstein` is already a bundled `ModularForm`. |
|  5 | vector-space/metric/field-specific → weaker typeclass (modules/pseudometric/(semi)ring)?          | no       | — | Values live in `ℂ`; the scalar `p^{k−1}` is genuinely a complex number. No typeclass weakening. |
|  6 | 1-categorical → higher/∞-categorical?                                                             | no       | — | None. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid/ordered structure?                       | no       | — | `p·z` scaling is by a fixed prime via `pScale`; not an index to generalise. |

Modern idiom available: **no**.
One-line reason this is not a modernisation move: it is a `f.toFun z = <body> z` coercion lemma for an
already-bundled modular form; there is no organisational redundancy to remove and no contemporary tool
that re-expresses "the value of this constructed form" more cleanly. The *one* idiomatic improvement
mathlib would want (a `@[simp]` `*_apply` lemma that fires on `coe`) is already what this is.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. Value lemmas introduce no definitional equalities or
typeclass-search paths. (Skipped per the skill's scope rule.)

---

### Mathlib search-status: `stabilisedEisenstein_apply` (Phase 5)

Searched both the user's form *and* the literature-standard object form. Building (`lake build`) was
not re-run per the task note; the mathlib source tree under `.lake/packages/mathlib/` was grepped
directly (method [D] is therefore authoritative here), and the elaborated dependencies were read from
source.

[A] Lean-Finder       "value of p-stabilized Eisenstein series", "modular form E_k - p^{k-1} E_k(pz)"   no hits — Lean-Finder is the mathlib semantic index; no p-stabilisation API exists to find.
[B] Loogle            `ModularForm.E _ ?z - _ * ModularForm.E _ _`, `?f _ = ModularForm.E _ _ - _`        no hits — no mathlib lemma has this shape (there is no `Γ₀(p)`-Eisenstein in mathlib to state it about).
[C] LeanSearch        "p-stabilization of Eisenstein series", "level raising operator value of modular form"  no hits — concept absent from mathlib.
[D] Grep mathlib src  `stabilis|stabiliz|levelRaise|level_raise|p.stabil` over `Mathlib/NumberTheory/ModularForms/`  **no hits** — confirmed: mathlib has **no** p-stabilisation, **no** level-raising operator, **no** `Γ₀(p)`-Eisenstein modular form. It has `EisensteinSeries.E` (Basic.lean:47, level-1, weight ≥ 3, on `𝒮ℒ`) and its q-expansion (`q_expansion_bernoulli`, `E_qExpansion_coeff`, QExpansion.lean), and the *private* analogue `E₄CubeSubE₆SqForm` + `E₄CubeSubE₆SqForm_apply` (LevelOne/GradedRing.lean:31–35).
[E] Name pattern      grep project + mathlib for `stabilisedEisenstein`, `*_apply` value-lemma pattern   `stabilisedEisenstein`/`stabilisedEisenstein_apply` exist **only** in `EisensteinComplex.lean`; no mathlib decl by any related name.

Searched for both:
  - the user's current form (`stabilisedEisenstein p hk z = E_k z − p^{k−1}·E_k(pScale p z)`) — not in mathlib;
  - the literature-standard object form (`E_k − p^{k−1}E_k(p·) ∈ M_k(Γ₀(p))`) — the *object* is not in mathlib at all, hence neither is its value lemma.

Concluded: **not in mathlib** (all five methods exhausted, plus the literature-standard object form).
The closest mathlib precedent is **`EisensteinSeries.E`** (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:47`) — the level-1 normalised Eisenstein modular form the project's `stabilisedEisenstein` is *built from* — together with the **`private` value-lemma pattern** `ModularForm.…_apply` exemplified by `E₄CubeSubE₆SqForm_apply` (`Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean:34`). This precedent is load-bearing for the verdict: mathlib keeps such "value of a constructed modular form" lemmas `private`, as scaffolding for the def, **not** as exported API.

---

### Call sites — `stabilisedEisenstein_apply` (Phase 6.0)

Internal use count: **1** (within `PadicLFunctions`, NOT counting the docstring mention or the
declaration itself).
External-to-file callers: **0 distinct files** (no use of `stabilisedEisenstein_apply`, nor of the
def `stabilisedEisenstein`, anywhere outside `EisensteinComplex.lean`; grep over all of `projects/`).

| Caller file:line                                            | Usage pattern (one-line excerpt)                                                  |
|-------------------------------------------------------------|-----------------------------------------------------------------------------------|
| projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:368 | `rw [stabilisedEisenstein_apply, rjwEisenstein, rjwEisenstein]` (inside `stabilisedEisenstein_smul_apply`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `stabilisedEisenstein_apply`?):
  - (none) — the only consumer is `stabilisedEisenstein_smul_apply`, which uses it as intended; the
    twin q-expansion result `hasSum_stabilisedEisenstein` works directly with `rjwEisenstein` and
    `pScale` and does not route through this lemma.

What the pattern tells you (from the Phase-6 signal table): **K = 1 internal use only** → "possibly
the wrong abstraction — could be inlined; lean toward NO-composable." Combined with **0 external/
cross-project callers**, the lemma is purely internal glue for one downstream rewrite, exactly the
profile of a `*_apply` coercion lemma that ships with (or inlines into) its def.

### Composition check (Phase 6)

Can `stabilisedEisenstein_apply` be derived in ≤3 chained calls from the def's coercion + the
level-raise value lemma?

Attempt 1: unfold the bundled coercion to its underlying function, then evaluate the level-raise.
  ```lean
  -- (this is essentially the existing proof, ≤3 substantive steps)
  example {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
      stabilisedEisenstein p hk z
        = ModularForm.E hk z - (p : ℂ) ^ (k - 1) * ModularForm.E hk (pScale p z) := by
    rw [show (stabilisedEisenstein p hk : ℍ → ℂ) z = (stabilisedDiff p hk : ℍ → ℂ) z from rfl,
        coe_stabilisedDiff p hk]               -- coercion unfold, both `rfl`
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        levelRaiseFun_apply, coe_levelRaiseMatrix_smul]  -- value of the level-raise = f(p·z)
  ```
  - Decls used: `coe_stabilisedDiff` (project, proof = `rfl`), `levelRaiseFun_apply` (project),
    `coe_levelRaiseMatrix_smul` (project), `Pi.sub_apply`/`Pi.smul_apply` (mathlib).
  - Result: succeeds (it is, up to `hpt`, the lemma's own 4-line proof).
  - Notes: the chain is "coercion is `rfl`" → "underlying function is `E − p^{k−1}•levelRaiseFun p k E`
    (`rfl`)" → "`levelRaiseFun` evaluates to `f(p·z)` (`levelRaiseFun_apply` + `coe_levelRaiseMatrix_smul`)".
    Two of the three steps are pure `rfl` definitional unfolding; the third is the single project lemma
    `levelRaiseFun_apply` whose value is `f((levelRaiseMatrix l) • τ)`.

Attempt 2: not needed.

Conclusion: **COMPOSABLE** — but the operative composition is from the *def's own coercion* plus the
*project's* `levelRaiseFun_apply`, not from mathlib primitives (mathlib has neither `stabilisedEisenstein`
nor `levelRaiseFun`). This is precisely the "value lemma ships with / inlines from its def" pattern: in
mathlib this is `E₄CubeSubE₆SqForm_apply` proved by `simp only [E₄CubeSubE₆SqForm, coe_mcast, coe_pow,
sub_apply, Pi.pow_apply]` — a `private` 1-`simp` coercion unfold. `stabilisedEisenstein_apply` is the
structural twin.

---

## Verdict: `PadicLFunctions.stabilisedEisenstein_apply`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the *RHS expression* `E_k(z) − p^{k−1}E_k(pz)` is the textbook
  p-stabilisation (Kawamura arXiv:1207.0198 states it verbatim; Hida–Wiles classical). But the
  *lemma* is a "value of a constructed modular form" coercion statement, which has no name in the
  literature — it is a formalisation artifact of bundling the function into a `ModularForm`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL at the lemma level (0 weakenings); all
  generalisation axes belong to the *def*, not the value lemma. Modern-idiom check (4c): no
  modernisation — it already *is* the idiomatic `*_apply` simp lemma.
- Mathlib search (Phase 5): not in mathlib (5 methods); the closest precedent is `EisensteinSeries.E`
  (`Basic.lean:47`, the form it is built from) and the **`private`** value-lemma pattern
  `E₄CubeSubE₆SqForm_apply` (`LevelOne/GradedRing.lean:34`).
- Composition check (Phase 6): COMPOSABLE — the lemma is its def's coercion unfold (`coe_stabilisedDiff`
  = `rfl`) plus one project lemma `levelRaiseFun_apply`; ≤3 steps, two of them `rfl`. Call sites:
  K = 1 internal, 0 external.

**Rationale (1–2 paragraphs):**

`stabilisedEisenstein_apply` is not an independent mathematical result; it is the *value/coercion
lemma* for the project-specific bundled object `stabilisedEisenstein`. Its content is exactly
"`(ModularForm.mk … with toFun := ⇑(stabilisedDiff …)).toFun z` equals the function it was built
from, evaluated at `z`" — definitional bookkeeping. Mathlib's own directly-analogous construction,
`E₄CubeSubE₆SqForm` (a difference of Eisenstein-power modular forms), carries its value lemma
`E₄CubeSubE₆SqForm_apply` as a **`private`** declaration proved by a single `simp only [<def>, coe_…]`
— it is scaffolding for the def, never exported API. `stabilisedEisenstein_apply` sits at the identical
altitude: it ships *with* its def (and inlines from it in one `simp`/`rw`), so it is not a separate
mathlib contribution. This is why the bucket is NO-composable-from-mathlib rather than a YES: even
though mathlib lacks the *object* (and that object — the `Γ₀(p)` p-stabilisation realised via a
level-raising operator — is the genuinely novel, BIG content of this file), the *value lemma* is the
mechanical coercion unfold of that object and is governed by mathlib's "`*_apply` lemmas live with
their def" convention.

One honest nuance was weighed and resolved rather than escalated to BORDERLINE: the composition's
building blocks (`coe_stabilisedDiff`, `levelRaiseFun_apply`) are *project-local*, not mathlib, so in
the strictest reading "composable from mathlib" is not literally true — mathlib cannot state this
lemma because mathlib has neither the def nor the level-raising operator. But the lemma-level verdict
is unambiguous under every reading: a `*_apply` value lemma is never upstreamed on its own; its fate is
bound to its def's. If `stabilisedEisenstein` (and the underlying `levelRaiseFun` / `modularFormLevelRaise`)
were ever upstreamed, this lemma would go *with* it as a (likely `@[simp]`, possibly `private`) value
lemma in the same PR — not as a standalone feat. That binding is captured below; it does not require a
user judgment call, so the verdict commits.

**WHY not (refactor-actionable detail):**
Mathlib has the *root* building block (`EisensteinSeries.E`) and the *pattern* for value lemmas, but
not the exact form — and the exact form is, by construction, a 1–3-step coercion unfold of a
project def. No standalone mathlib lemma is justified: the statement is `f.toFun z = <body> z` for the
bundled `f = stabilisedEisenstein`, which is `rfl`-deep modulo the single `levelRaiseFun_apply` step.

Mathlib building blocks / precedent:
- `EisensteinSeries.E` — `Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:47`
  (the level-1 normalised Eisenstein modular form the RHS is written in).
- `E₄CubeSubE₆SqForm_apply` — `Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean:34`
  (the `private` "value of a constructed modular form" precedent this lemma mirrors).
- Generic `ModularForm`/`SlashInvariantForm` coercion simp lemmas (`coe_mk`, `sub_apply`,
  `Pi.smul_apply`) — `Mathlib/NumberTheory/ModularForms/Basic.lean` and `Mathlib/.../Pi`.

Composition sketch (≤3 lines — the lemma *is* this unfold):
```lean
example {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    stabilisedEisenstein p hk z
      = ModularForm.E hk z - (p : ℂ) ^ (k - 1) * ModularForm.E hk (pScale p z) := by
  rw [show (stabilisedEisenstein p hk : ℍ → ℂ) z = (stabilisedDiff p hk : ℍ → ℂ) z from rfl,
      coe_stabilisedDiff p hk]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, levelRaiseFun_apply, coe_levelRaiseMatrix_smul]
```

Call sites in our project (from Phase 6.0): **K = 1** (`EisensteinComplex.lean:368`, inside
`stabilisedEisenstein_smul_apply`).

Refactor plan:
- **Do NOT delete or upstream this lemma on its own.** It is correct, useful local API, and it is the
  right thing to *keep in the project* alongside the def `stabilisedEisenstein`.
- For **mathlib purposes**: this lemma is not a separate upstreaming target. If/when the project decides
  to upstream the p-stabilisation machinery, bundle `stabilisedEisenstein_apply` into the *same* PR as
  its def `stabilisedEisenstein` (and the `levelRaiseFun`/`modularFormLevelRaise` operator), as the
  def's value lemma — give it `@[simp]` and follow mathlib's `E₄CubeSubE₆SqForm_apply` precedent on
  whether it stays `private`. Its mathlibability is *inherited from the def's*, which is itself a
  separate (BIG) assessment — see the sibling reports for `stabilisedEisenstein` / `hasSum_stabilisedEisenstein`
  and the `eisensteinFamily` family (those are BORDERLINE/BIG; the def has no current external consumers
  and is RJW-construction-internal).
- At the single internal call site (`EisensteinComplex.lean:368`), nothing changes — the lemma is used
  exactly as intended (one `rw`).

**Next action:** keep `stabilisedEisenstein_apply` as project-local value API; take **no independent
mathlib action**. Its upstreaming is bound to the def `stabilisedEisenstein` — assess/route that BIG
def separately (it currently has 0 external consumers and is internal to RJW §8), and if it is ever
upstreamed, ship this `_apply` lemma in the same PR as the def's (likely `@[simp]`) value lemma,
mirroring mathlib's `private E₄CubeSubE₆SqForm_apply`.

---

## Next step

Keep `stabilisedEisenstein_apply` as project-local value API; take no independent mathlib action. Its
mathlibability is inherited from the def `stabilisedEisenstein` — assess that BIG def separately (0
external consumers, RJW-construction-internal), and if the def is upstreamed, ship this value lemma in
the same PR (mirroring mathlib's `private` `E₄CubeSubE₆SqForm_apply`).

Sources (Phase 3):
- [Kawamura, *A semi-ordinary p-stabilization of Siegel Eisenstein series…*, arXiv:1207.0198](https://arxiv.org/abs/1207.0198) — states `E_{2k}(z) − p^{2k−1}E_{2k}(pz) ∈ M_{2k}(Γ₀(p))` verbatim.
- [arXiv:2505.06956, *On Siegel–Eisenstein series of level p and their p-adic properties*](https://arxiv.org/pdf/2505.06956)
- [Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.html)
- [leanprover-community blog — Modular forms](https://leanprover-community.github.io/blog/posts/modular-forms/)
