# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveQ_a₃`

> AINTLIB `/overview` Step-9 mathlibable assessment, single declaration.
> Project: NagellLutz (Nagell–Lutz theorem; elliptic curves / division polynomials).
> Note: local Lean build is stale; verdict reasoned from source + mathlib source + lit search.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale, per task brief); reasoned from source.
- decl `LutzNagell.LutzNagellTheorem.shortCurveQ_a₃`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:44`
- qualified name:           VERIFIED `LutzNagell.LutzNagellTheorem.shortCurveQ_a₃`
  (file opens `namespace LutzNagell` then `namespace LutzNagellTheorem`; lemma base name
  `shortCurveQ_a₃`). The brief's guessed name matches the source exactly.
- kind:                     lemma (carries `@[simp]`)
- has sorry:                no
- module docstring summary: "Short Weierstrass model for Lutz–Nagell": sets up `y² = x³+Ax+B`
  over `ℤ` and its base change to `ℚ`, and proves basic rewriting lemmas (a-coeffs, equation,
  discriminant) so downstream files import this instead of re-expanding `Δ`/`Equation`.

---

### Statement (Phase 1)

`shortCurveQ_a₃` states: for the short Weierstrass curve `shortCurveQ A B` over `ℚ` — obtained
by base-changing `shortCurveZ A B = { a₁:=0, a₂:=0, a₃:=0, a₄:=A, a₆:=B }` along
`algebraMap ℤ ℚ` — the `a₃` coefficient is `0`.

In board mathematics this is the entirely trivial observation that the curve
`y² = x³ + Ax + B` (a *short* Weierstrass form, so `a₁ = a₂ = a₃ = 0` by construction) still has
`a₃ = 0` after extending scalars from `ℤ` to `ℚ`, because base change transports each coefficient
through the ring map and `algebraMap ℤ ℚ 0 = 0`.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the two free coefficients of the short model.

Hypotheses (Lean side): none.

Conclusion (math): the `a₃`-coefficient of the `ℚ`-base-change of the short curve is `0`.

Conclusion (Lean): `(shortCurveQ A B).a₃ = 0`.

Proof body: `by simp [shortCurveQ, shortCurveZ]` (one line). The sibling `shortCurveZ_a₃`
(line 34) is `rfl`; the `ℚ`-version needs `simp` only to unfold `shortCurveQ`/`shortCurveZ`,
fire mathlib's `WeierstrassCurve.map_a₃`, and discharge `algebraMap ℤ ℚ 0 = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` glue lemma reading one auto-`@[simps]` projection of a project-local def;
no new structure, not a `## Main results` entry, not named after a person.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner def check is **n/a**.
(It is a one-line *proof*, but Phase 2b targets one-line *definitions*; lemmas are exempt.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Weierstrass curve base change map coefficient a₃ ring homomorphism elliptic curve"            | yes  | `(W.baseChange A).a₃ = algebraMap R A W.a₃` | Top hit is the **mathlib** `Weierstrass` doc page; base change transports each coeff through the ring map. |
|  2 | WebSearch (general form)         | (same query, general reading) functorial base change of Weierstrass coefficients               | yes  | each `aᵢ` is functorially transformed by `φ : R →+* A` | Standard; nothing curve-specific. |
|  3 | WebSearch (named-after/aliases)  | "short Weierstrass form a₃ = 0" / "shift / base change of coefficients"                          | yes  | short form ⇒ `a₁=a₂=a₃=0` by definition | Textbook (Silverman) convention; the `a₃=0` fact is definitional, not a theorem. |
|  4 | ChatGPT MCP                      | (MCP down per brief — fallback to WebSearch #1–3 + mathlib source read)                          | n/a  | —                   | Substituted by direct mathlib-source inspection of `map`/`baseChange` + `@[simps]`. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "Weierstrass / base change"                             | n/a  | (no references dir for this triage) | recorded n/a. |
|  6 | nLab                             | "Weierstrass curve" / "elliptic curve base change"                                              | n/a  | —                   | nLab has no page giving a coefficient-level `a₃` transport lemma; concept is too elementary. |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                   | Not a categorical statement (a single coefficient equals 0). |
|  8 | Stacks Project (alg geom)        | base change of Weierstrass coefficients                                                          | n/a  | —                   | Stacks treats elliptic curves schematically; no coefficient-`a₃` lemma. |
|  9 | MathOverflow / MSE               | "base change short Weierstrass a₃ zero"                                                          | n/a  | —                   | No question exists; the fact is trivial/definitional. |
| 10 | recent arXiv (≤5 yr)             | formal proof Weierstrass group law (arXiv 2302.10640)                                            | yes  | uses the same coefficient model `a₁..a₆` | The formalisation literature uses exactly mathlib's bundled `aᵢ` model. |

### Literature summary (Phase 3)

Concept identified as: *base change / scalar extension of a Weierstrass curve's coefficients*;
the specific fact is "a short Weierstrass model has `a₃ = 0`, preserved under base change".
Sources agree on the standard form: **yes** — `(W.baseChange A).aᵢ = algebraMap R A W.aᵢ`,
which is precisely how mathlib defines/derives it.
Most general standard form: for any ring hom `f : R →+* A`, `(W.map f).aᵢ = f W.aᵢ`.
Generality dimensions where the literature varies: none of substance — the coefficient-transport
law is uniform; only the *base ring* and *target* vary, and mathlib already states it over an
arbitrary `f : R →+* A`.
Disagreement with the literature: **none**. The project's lemma is a `ℤ→ℚ` specialisation of a
fact mathlib already owns, further specialised to the concrete curve `shortCurveZ A B`.

---

### Generality analysis — `shortCurveQ_a₃` (Phase 4)

Literature-standard / mathlib form: `WeierstrassCurve.map_a₃ : (W.map f).a₃ = f W.a₃`
(auto-generated by `@[simps]` on `WeierstrassCurve.map`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker / more-general form exists? | Reason |
|---|------------------------|-------------------|--------------------------|-----------------------------------|--------|
| 1 | curve                  | the concrete `shortCurveZ A B` (a literal record with `a₃ := 0`) | an arbitrary `W : WeierstrassCurve R` | **yes** | mathlib's `map_a₃` holds for any `W`; the project pins `W` to one curve and pins its `a₃` to `0`. |
| 2 | base ring / ring map   | `algebraMap ℤ ℚ` | any `f : R →+* A` | **yes** | mathlib states it over an arbitrary ring hom. |
| 3 | coefficient value      | hard-codes RHS `= 0` | RHS `= f W.a₃` (general) | **yes** | the `= 0` is a downstream consequence of `shortCurveZ_a₃ = 0` + `map_zero`, not a new fact. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but *not* in a way that yields a
mathlib contribution. It is narrower because it is a *specialisation of an existing mathlib lemma
to a project-private object* (`shortCurveQ`), not because mathlib lacks the general statement.
Generalising it "the mathlib way" does not produce a new mathlib lemma — it produces
`WeierstrassCurve.map_a₃`, **which mathlib already has**. So the narrowness pushes toward a NO
verdict, not toward YES-but-generalise-first.
Number of weakening opportunities: 3 — but each fully generalised form coincides with an
existing mathlib decl.
Cost of restatement: n/a (the general form already exists upstream).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | typeclasses instead of bundled hyps? | no | no hypotheses to bundle. |
| 2 | filters/topology instead of sequences/metrics? | no | pure algebra, no limits. |
| 3 | universal-property class instead of construction? | no | reading a record field. |
| 4 | bundled substructure instead of set+predicate? | no | n/a. |
| 5 | weaken vector-space/field to module/(semi)ring? | no | already over arbitrary `CommRing` upstream. |
| 6 | higher-categorical generalisation? | no | n/a. |
| 7 | concrete index → arbitrary algebraic structure? | partially | the `ℤ→ℚ` map → arbitrary `f : R →+* A`; but that generalisation **is** mathlib's existing `map_a₃`. |

Modern idiom available: **no** (the only "modernisation" is to use the pre-existing mathlib lemma).
Reason: there is no new contemporary formulation to ship; the idiomatic move is to invoke
`WeierstrassCurve.map_a₃`.

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no new definitional equalities or instance-search paths).

---

### Mathlib search-status: `shortCurveQ_a₃` (Phase 5)

Searched both the user's form and the general form `(W.map f).a₃ = f W.a₃`.

[A] Lean-Finder   "Weierstrass map a₃ coefficient base change"   → general form is mathlib's.
[B] Loogle        `(WeierstrassCurve.map _ _).a₃ = _`             → `WeierstrassCurve.map_a₃`.
[C] LeanSearch    "a₃ coefficient of base-changed Weierstrass curve" → `WeierstrassCurve.map_a₃` / `baseChange`.
[D] Grep mathlib src `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` — **CONFIRMED at source**:
    - line 230 `@[simps]` on `def map : WeierstrassCurve A := ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩`
      → `@[simps]` auto-generates `WeierstrassCurve.map_a₃ : (W.map f).a₃ = f W.a₃` as a `@[simp]` lemma.
    - these generated `map_a₁ … map_a₆` are consumed at lines 244/249/254/259 (`simp only [b₄, map_a₁, map_a₃, map_a₄]` etc.), proving they exist and are simp.
    - `def baseChange := W.map (algebraMap R A)` (line ~236), so the `baseChange` form follows immediately.
[E] Name pattern  grep project: `def shortCurveQ` exists **only** at ShortWeierstrass.lean:29 →
    `shortCurveQ` is project-private; no `shortCurveQ`/`shortCurveQ_a₃` in mathlib (cannot be — the name doesn't exist upstream).

Concluded: **found building blocks in mathlib** — `WeierstrassCurve.map_a₃`
(`@[simps]`-generated, `@[simp]`) plus the project's own `rfl`-true `shortCurveZ_a₃`. The exact
project statement is NOT in mathlib *and cannot be*, because it names the project-local def
`shortCurveQ`. The only generic content (coefficient transport under a ring map) is already upstream.

---

### Call sites — `shortCurveQ_a₃` (Phase 6.0)

Internal use count (excluding declaring file): **0** as an *explicitly named* lemma.
External-to-file callers (named): 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none by name)   | — |

But note the consumption model: `shortCurveQ_a₃` carries `@[simp]`, and downstream files
`Main.lean` / `GeneralMain.lean` use `shortCurveQ A B` inside `Nonsingular` / `Equation` goals
(e.g. `Main.lean:36,49,67`) that are discharged by `simp`/`simpa`. The lemma therefore fires
*implicitly* via the simp set rather than being spelled out — so "0 named call sites" understates
its role: it is live simp-normal-form infrastructure for the short-curve coefficients, exactly as
the module docstring intends ("Downstream files should import this instead of re-expanding").

Inline-derivation grep (was the equivalent re-derived elsewhere?): the five
`shortCurveQ_a₁ … shortCurveQ_a₆` lemmas are the single canonical place; no competing inline
re-expansion of `(shortCurveQ _ _).a₃` was found.

### Composition check (Phase 6)

Can `shortCurveQ_a₃` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1 (sketch):
```lean
example (A B : ℤ) : (shortCurveQ A B).a₃ = 0 := by
  -- shortCurveQ A B = (shortCurveZ A B).map (algebraMap ℤ ℚ)
  rw [shortCurveQ, WeierstrassCurve.map_a₃]   -- (·.map f).a₃ = f (·.a₃)   [mathlib, @[simps]]
  simp [shortCurveZ]                          -- (shortCurveZ A B).a₃ = 0, then algebraMap … 0 = 0
```
- Mathlib decls used: `WeierstrassCurve.map_a₃` (and `map_zero` / the `algebraMap` ring-hom map of `0`).
- Project decl used: `shortCurveZ` unfold (its `a₃` is the literal `0`); equivalently `shortCurveZ_a₃` (`rfl`).
- Result: **succeeds** — this is exactly the lemma's actual one-line proof `simp [shortCurveQ, shortCurveZ]`, which under the hood is this 2-step composition (`map_a₃` is in the default simp set via `@[simp]`).

Conclusion: **COMPOSABLE** (≤3 mathlib/project calls; in fact mathlib's `map_a₃` + a definitional
`a₃ = 0` + `map_zero`).

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveQ_a₃`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the coefficient-transport law `(W.map f).aᵢ = f W.aᵢ` is the
  standard fact and is literally mathlib's; the `a₃ = 0` part is definitional (short form).
- Generality analysis (Phase 4): STRICTLY NARROWER than standard, but every generalisation
  coincides with the *existing* `WeierstrassCurve.map_a₃` — so narrowness implies NO, not
  YES-but-generalise.
- Mathlib search (Phase 5): building blocks found — `WeierstrassCurve.map_a₃` (`@[simps]`-generated,
  `@[simp]`, confirmed at source line 230 and used at 244/249/254/259). Exact statement absent
  and unaddable (names project-local `shortCurveQ`).
- Composition check (Phase 6): COMPOSABLE — `map_a₃` then a definitional `a₃ = 0` (`+ map_zero`).

**Rationale:**

`shortCurveQ_a₃` is project-local glue, not mathlib material. Its statement mentions
`shortCurveQ A B`, a definition that exists *only* in this project (`ShortWeierstrass.lean:29`),
so the literal lemma can never live in mathlib — there is nothing in mathlib to attach it to. The
only piece of genuine, reusable mathematics inside it — "base change sends `a₃` to `f a₃`" — is
already in mathlib as `WeierstrassCurve.map_a₃`, auto-generated by the `@[simps]` attribute on
`WeierstrassCurve.map` (mathlib `Weierstrass.lean:230`; the generated lemmas are consumed in that
same file at lines 244/249/254/259). The residual `a₃ = 0` is definitional, holding because
`shortCurveZ` is the literal record `{ …, a₃ := 0, … }` (its `ℤ`-level twin `shortCurveZ_a₃` is
`rfl`), and `algebraMap ℤ ℚ 0 = 0` by `map_zero`. So the whole lemma is a 2-step composition of an
existing mathlib simp lemma with a definitional unfold — precisely the `NO-composable` profile.

This is **not** `NO-mathlib-has-it` verbatim: mathlib does not contain a lemma with this exact
statement (it cannot, since `shortCurveQ` is private). It is `NO-composable-from-mathlib`: mathlib
supplies the building block, the project supplies the trivial specialisation. Critically, the
**refactor action here is to KEEP the lemma, not delete it.** It is correct, useful, `@[simp]`
infrastructure that puts `(shortCurveQ A B).a₃` into simp-normal form `0` for the downstream
Nonsingular/Equation simp calls in `Main.lean`/`GeneralMain.lean`. It simply carries no upstreamable
content — there is no mathlib PR to open for it.

**WHY not (refactor-actionable):**
Mathlib has the building block `WeierstrassCurve.map_a₃`; the project lemma is its specialisation to
`shortCurveZ A B` (whose `a₃` is the literal `0`) along `algebraMap ℤ ℚ`. No new mathlib lemma is
warranted because (a) the generic statement is already upstream and (b) the specific statement is
unexportable (project-private curve).

Mathlib building blocks:
- `WeierstrassCurve.map_a₃` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`
  (`@[simps]`-generated from `def map`, line 230; `@[simp]`).
- `map_zero` (the ring hom `algebraMap ℤ ℚ` sends `0 ↦ 0`).
- Project-local: `shortCurveZ_a₃ : (shortCurveZ A B).a₃ = 0` (`rfl`, ShortWeierstrass.lean:34).

Composition sketch (≤3 lines):
```lean
example (A B : ℤ) : (shortCurveQ A B).a₃ = 0 := by
  rw [shortCurveQ, WeierstrassCurve.map_a₃]; simp [shortCurveZ]
```

Call sites in our project (Phase 6.0): K = 0 *named*; but used implicitly via `@[simp]` in the
downstream short-curve `Nonsingular`/`Equation` proofs (`Main.lean:36,49,67` and `GeneralMain.lean`).

**Refactor plan (AINTLIB-appropriate):** No deletion and no inlining at call sites is warranted —
the lemma's value is precisely that it is a *named `@[simp]` member of the short-curve coefficient
API* (the docstring's stated purpose: "import this instead of re-expanding `Δ`/`Equation`").
Recommended dispositions, in order of preference:
1. **Keep as-is** (default). It is a 5-lemma `simp` block (`shortCurveQ_a₁ … _a₆`) that is the
   canonical simp-normal-form interface; the analogous `shortCurveZ_*` block is already `rfl`. This
   is healthy local infrastructure, not dead code or a redundant wrapper.
2. **Optional micro-golf** (cleanup lane, statement unchanged): since mathlib's `map_a₁ … map_a₆`
   are `@[simp]`, the five `shortCurveQ_aᵢ` lemmas can each be proved by `by simp [shortCurveQ]`
   (dropping the explicit `shortCurveZ` unfold if the `shortCurveZ_aᵢ` lemmas, themselves `@[simp]`
   `rfl`, are in scope) — purely cosmetic, do under `/cleanup`, not a mathlib concern.

**Mathlib action: none.** Do not open a PR. The generic content already lives at
`WeierstrassCurve.map_a₃`; the specific content is project-private.

---

## Next step

No mathlib PR. **Keep `shortCurveQ_a₃` as a project-local `@[simp]` coefficient lemma** (it is
correct, in-use-via-simp infrastructure for the short-curve model). The only mathlib-relevant
content is `WeierstrassCurve.map_a₃`, which mathlib already has. Optionally, under a future
`/cleanup` pass on `ShortWeierstrass.lean`, golf the five `shortCurveQ_aᵢ` proofs to lean directly
on mathlib's `@[simps]`-generated `map_aᵢ` simp lemmas — cosmetic only, statement unchanged.
