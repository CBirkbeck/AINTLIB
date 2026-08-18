# /mathlibable report — `WeierstrassCurve.Universal.polyToField_polynomial`

### Baseline (Phase 0)
- lake build:               (not re-run — repo states local build stale; decl reasoned from source)
- decl `WeierstrassCurve.Universal.polyToField_polynomial`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:120`
- kind:                      lemma, `@[simp]`, 1-line proof (3 rewrites)
- has sorry:                 no
- live mathlib commit:       `09b373db6e` (pkg `.lake/packages/mathlib`)
- module docstring summary:  Additions to `Affine.Point` and the construction of the **universal
  elliptic curve** over `ℤ[A₁,A₂,A₃,A₄,A₆]`; defines `Universal.Poly`, `Universal.Ring`
  (= `curve.CoordinateRing`), `Universal.Field` (= `Frac(Universal.Ring)`) and the ring hom
  `polyToField : Poly →+* Universal.Field`.

**True qualified name (VERIFIED from source):** the lemma sits inside
`namespace WeierstrassCurve` (Universal.lean:69) → `namespace Universal` (Universal.lean:75). So the
parsed name `WeierstrassCurve.Universal.polyToField_polynomial` is **correct**.

---

### Statement (Phase 1)

```lean
@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]
```

In prose: the Weierstrass polynomial `P = curve.polynomial` of the **universal** Weierstrass curve
maps to `0` under the canonical ring homomorphism
`polyToField : ℤ[A₁,…,A₆,X,Y] → Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`.

This is the **defining property of the quotient**: `polyToField` is built (Universal.lean:108) as
`(algebraMap Universal.Ring _).comp (AdjoinRoot.mk curve.polynomial)`, i.e. "reduce mod ⟨P⟩, then
include into the fraction field." The class of `P` in `Poly/⟨P⟩ = AdjoinRoot P` is zero because `P`
*is* the relation being quotiented out (`AdjoinRoot.mk f f = 0`), and the `algebraMap` then sends
`0 ↦ 0`. The web literature states this verbatim: "the coordinate ring is the quotient
`R[X,Y]/⟨W(X,Y)⟩`, which means the Weierstrass polynomial `W(X,Y)` becomes zero in this ring **by
definition of the quotient construction**."

Variables / typeclasses: none beyond the fixed project types `Universal.Poly`, `Universal.Ring`,
`Universal.Field` (all `noncomputable` concrete types — no free `[CommRing R]`).
Hypotheses: none.
Conclusion (Lean): `polyToField curve.polynomial = 0`.

Proof factors (all mathlib primitives except the first, which is a project `rfl` unfold):
- `polyToField_apply` — project-local, `:= rfl` (unfolds `polyToField` to the composite).
- `AdjoinRoot.mk_self` — **mathlib** `Mathlib/RingTheory/AdjoinRoot.lean:217`, `@[simp]`,
  `mk f f = 0`. **Does the real work.**
- `map_zero` — **mathlib**, generic `@[simp]` (`algebraMap … 0 = 0`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` glue lemma (3-rewrite proof) recording a quotient's defining property for one
fixed polynomial; not a named theorem, not a new structure, not a `## Main results` goal. (Literature
width still run per protocol; the surrounding *mathematics* — universal curve / coordinate ring /
function field — is standard and well-documented but belongs to the construction, not this lemma.)

### One-line check (Phase 2b)
Body line count: effectively 1 (a single `rw` chain). Kind is `lemma`, not `def`, so the 2b
def-exemption table does not apply. Relevant signal is the composition check (Phase 6).

---

### Literature search table

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|----------------------|-------|
|  1 | WebSearch (specific form)        | universal Weierstrass curve coordinate ring AdjoinRoot Weierstrass polynomial maps to zero fraction field | yes | "coordinate ring `= R[X,Y]/⟨W⟩` ⇒ `W` becomes zero **by definition of the quotient**" | Confirms it is a defining property, NOT a theorem with content. Mathlib `Affine.Point` docs + arXiv:1303.4327 / 0810.2853 corroborate the construction. |
|  2 | WebSearch (general primitive)    | image of generator/defining relation in quotient ring is zero AdjoinRoot mk_self                    | yes  | `AdjoinRoot.mk f f = 0` | The general fact: the adjoined polynomial vanishes in `AdjoinRoot f`. Mathlib `mk_self`. |
|  3 | WebSearch (convention)           | mathlib `@[simp]` lemma push ring hom through specific element vanishing                            | yes  | local `@[simp]` "this element ↦ 0" lemmas are project glue | `simp`-normal-form convenience for a fixed polynomial under a fixed map; not standalone math. |
|  4 | ChatGPT MCP                      | "Is `polyToField_polynomial` more than `AdjoinRoot.mk_self` + `map_zero` specialised?"              | n/a  | — | MCP server down in this environment (per task note). Settled by source + grep: see Phase 5/6. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                 | n/a  | — | Directory absent for this project (only `overview/` exists). n/a. |
|  6 | nLab / Stacks                    | function field of a curve = Frac of coordinate ring; quotient kills defining relation               | n/a  | — | Stacks/nLab have the *construction*; no lemma corresponds to a Lean `simp` fact "this fixed `P ↦ 0`". |
|  7 | MathOverflow / MSE               | —                                                                                                  | n/a  | — | No research-level question = "the defining relation is zero in the quotient"; one-step triviality. |
|  8 | recent arXiv (≤5 yrs)            | universal Weierstrass curve / division polynomials constructions                                    | yes  | arXiv:1303.4327, 0810.2853 (universal curve / EDS) | Concern the mathematics the *construction* supports (division polys, EDS), not this `simp` lemma. |

### Literature summary (Phase 3)
Concept identified as: **"the defining polynomial maps to zero in the quotient (and onward into its
fraction field)"** — i.e. `AdjoinRoot.mk_self` (the relation vanishes), then `map_zero`. The
surrounding mathematics (universal Weierstrass curve, `CoordinateRing = AdjoinRoot polynomial`,
function field `= Frac(CoordinateRing)`) is standard and well-documented, but it pertains to the
*definitions* `curve` / `Universal.Ring` / `Universal.Field` / `polyToField`, **not** to this lemma.
Most general standard form: for any commutative ring and any `f`, `AdjoinRoot.mk f f = 0` — mathlib
already states this maximally generally (`mk_self`). Disagreement with literature: none; there is no
mathematical theorem here, only a quotient's defining property instantiated at one polynomial and
pushed through one ring hom.

---

### Generality analysis — `WeierstrassCurve.Universal.polyToField_polynomial`

Literature-standard form: `AdjoinRoot.mk f f = 0` (`mk_self`), for arbitrary `[CommRing R]`,
`f : R[X]`. The user's lemma is the **fully specialised** instance with `R[X] := Universal.Poly`,
`f := curve.polynomial`, post-composed with `algebraMap Universal.Ring Universal.Field` (and using
`map_zero` to carry the `0` across).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | the polynomial         | the specific `curve.polynomial` | arbitrary `f : R[X]` | yes (already exists) | The general form is `AdjoinRoot.mk_self`; the user's lemma is its specialisation to `curve.polynomial`. No new generality to add. |
| 2 | the ring hom           | the specific `polyToField` (= `algebraMap ∘ mk`) | bare `mk` (general), or any ring hom + `map_zero` | yes (already exists) | The "carry `0` through a ring hom" half is `map_zero` (fully general). Composite is just `mk_self` then `map_zero`. |
| 3 | base ring / curve      | the concrete universal curve over `MvPolynomial Coeff ℤ` | any `W : Affine R` over `[CommRing R]` | yes in principle | One *could* state, for general `W`, that `algebraMap … (AdjoinRoot.mk W.polynomial W.polynomial) = 0`; but that is still literally `mk_self`+`map_zero`, and `polyToField` is defined only for the universal curve. Mathlib already has the general primitive. |

### Generality verdict (Phase 4b)
The current form is **STRICTLY NARROWER THAN STANDARD** (a full specialisation of `AdjoinRoot.mk_self`
followed by `map_zero`), but the general form is **already in mathlib**. This is a "mathlib already
has the general primitive" situation, not a "generalise-then-add" one. K = 0 new weakenings worth
adding. Proposed restatement: none — the maximally-general statement is `AdjoinRoot.mk_self`, present.

### Modern-idiom check (Phase 4c)
No bundled-hyp/typeclass, no analysis→filters, no construction→universal-property, no
set+closure→substructure, no field-specific→weaker-typeclass, no 1-cat→higher-cat, no concrete-index
opportunity applies. The contemporary mathlib idiom for "the defining relation is zero in the
quotient" is exactly `AdjoinRoot.mk_self`; the lemma is already at that altitude (it merely pushes
the resulting `0` through `algebraMap` via `map_zero`). Modern idiom available: **no** improvement.

---

### Diamond / defeq risk — Phase 4.5
n/a — kind is `lemma` (a proof). It introduces no new definitional equality or instance-search path.

---

### Mathlib search-status: `WeierstrassCurve.Universal.polyToField_polynomial`

(Index servers lean_loogle / lean_leansearch are unavailable in this environment — per task note —
so [A]–[C] are reasoned from the source and corroborated by grep [D]/[E] over the live mathlib tree
at commit `09b373db6e`.)

[A] Concept search   "Weierstrass polynomial vanishes in coordinate ring / function field" → the
                     primitive is `AdjoinRoot.mk_self` (relation ↦ 0) + `map_zero`. The EC-specific
                     statement is project-local.
[B] Loogle pattern   `AdjoinRoot.mk ?f ?f = 0` → exact match **`AdjoinRoot.mk_self`**
                     (`Mathlib/RingTheory/AdjoinRoot.lean:217`). `?g ?poly = 0` over a `FractionRing`
                     universal field → no mathlib decl named `polyToField`.
[C] LeanSearch       "image of a ring's defining polynomial in its quotient (and fraction field) is
                     zero" → `AdjoinRoot.mk_self`, `AdjoinRoot.mk_eq_zero`, `map_zero`.
[D] Grep mathlib src `grep -rn "polyToField" .lake/packages/mathlib/Mathlib/` → **0 hits**.
                     `polyToField`, `Universal.Field`, `Universal.Ring`, `Universal.Poly`,
                     `namespace Universal` (under `EllipticCurve/`) do not exist in mathlib — the
                     universal-pointed-curve construction is **not upstream**; this file forks/extends
                     `Mathlib.AlgebraicGeometry.EllipticCurve.*`. Moreover mathlib keeps **no named**
                     `mk W.polynomial W.polynomial = 0` lemma: in `Affine/Point.lean` it uses
                     `AdjoinRoot.mk_self` / `AdjoinRoot.mk_eq_mk` **inline** (e.g. lines 166, 409).
                     The mathlib `_polynomial`-named lemmas (`evalEval_polynomial_zero`
                     Affine/Basic.lean:142; `eval_polynomial_of_Z_ne_zero` Jacobian/Basic.lean:252)
                     are about polynomial **evaluation**, a different statement. Confirmed
                     `AdjoinRoot.mk_self` at `RingTheory/AdjoinRoot.lean:217` (`@[simp]`).
[E] Name pattern     `polyToField_polynomial` appears only in `projects/NagellLutz/` (declaring file +
                     ZSMul.lean uses) and the `projects/HasseWeil/` fork copy. Not in mathlib.

Searched for both:
  - the user's current form (`polyToField_polynomial`) — **not in mathlib** (subject is project-local).
  - the literature-standard primitive (`AdjoinRoot.mk_self`) — **in mathlib**,
    `Mathlib/RingTheory/AdjoinRoot.lean:217`, `@[simp]`, maximally general.

Concluded: **found the building blocks** `AdjoinRoot.mk_self` + `map_zero`; the user's form is their
specialisation/composition for the project-local map `polyToField` and the fixed polynomial
`curve.polynomial`. The named lemma is not (and cannot be) in mathlib because its subject is a
project-local definition over the not-upstreamed universal curve.

---

### Call sites — `WeierstrassCurve.Universal.polyToField_polynomial`

Internal NagellLutz use count: **3** total — 1 in the declaring file (Universal.lean:147, inside
`equation_point`), 2 in `ZSMul.lean` (155, 267; plus a `simp only [... polyToField_polynomial ...]`
at 282). Also `@[simp]`, so it fires implicitly in `simp` calls. (The `projects/HasseWeil/` fork
keeps its own identical copy with the same call pattern — that is a separate consolidation/dedup
concern, not a mathlib one.)

| Caller file:line       | Usage pattern (one-line excerpt) |
|------------------------|-----------------------------------|
| Universal.lean:147     | `rw [Affine.map_polynomial, this, polyToField_polynomial]` (kills the Weierstrass term ⇒ `equation_point`) |
| ZSMul.lean:155         | `rw […, map_mul, polyToField_polynomial, mul_zero, add_zero]` (drops the `·(polynomial)` summand) |
| ZSMul.lean:267         | `rw […, map_pow, map_ofNat, polyToField_polynomial]` |
| ZSMul.lean:282         | `simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero, …]` |

Call-sites signal: a `@[simp]` "the Weierstrass relation vanishes in the universal field" rewrite —
genuinely useful **local** API for `polyToField`, used to discharge the `·P`-summand whenever an
identity is pushed into `Universal.Field`. But the API is about a **project-local def**, so it lives
and dies with `polyToField`; not mathlib material.

---

### Composition check (Phase 6)

Can `polyToField_polynomial` be derived from mathlib in ≤3 chained calls? **Yes — its own proof is
exactly such a derivation: 2 mathlib primitives after a `rfl` unfold.**

Attempt 1 (the actual proof):
```lean
rw [polyToField_apply,        -- project `rfl` unfold of polyToField (≡ RingHom.comp_apply)
    AdjoinRoot.mk_self,       -- mathlib: mk curve.polynomial curve.polynomial = 0
    map_zero]                 -- mathlib: algebraMap _ _ 0 = 0
```
  - Mathlib decls used: **`AdjoinRoot.mk_self`** (`RingTheory/AdjoinRoot.lean:217`) and **`map_zero`**
    — 2 calls. The `polyToField_apply` step is a project-local `rfl` (itself just `RingHom.comp_apply`).
  - Result: **succeeds** (2 mathlib primitives; ≤3 budget).
  - Equivalent one-liner: `by simp` would close it, since both `mk_self` and `map_zero` are `@[simp]`.

Conclusion: **COMPOSABLE** (2 mathlib calls, under the ≤3 budget).

---

## Verdict: `WeierstrassCurve.Universal.polyToField_polynomial`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature (Phase 3): the only content is "the defining polynomial is zero in the quotient" =
  `AdjoinRoot.mk_self`, then `map_zero`; web sources confirm this is a defining property of the
  coordinate-ring quotient, not a theorem. Surrounding math (universal curve) belongs to the *defs*.
- Generality (Phase 4): STRICTLY NARROWER than standard, but the general form (`AdjoinRoot.mk_self`)
  is already in mathlib; no new generalisation to ship. Modern-idiom: none.
- Mathlib search (Phase 5): found the building blocks `AdjoinRoot.mk_self`
  (`Mathlib/RingTheory/AdjoinRoot.lean:217`, `@[simp]`) and `map_zero`; `polyToField` / `Universal.*`
  have **0 hits** in mathlib (project-local, not upstreamed); mathlib keeps no named
  `mk polynomial polynomial = 0` lemma (uses `mk_self` inline).
- Composition (Phase 6): COMPOSABLE — the lemma's own 1-line proof is a 2-call derivation
  (`AdjoinRoot.mk_self` + `map_zero`); `by simp` also closes it.

**Rationale:**
`polyToField_polynomial` is a `@[simp]` glue lemma stating that the universal Weierstrass polynomial
`curve.polynomial` maps to `0` under the project-local ring hom
`polyToField := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk curve.polynomial)`. This is the
defining property of the quotient `Poly/⟨P⟩`: the relation `P` is exactly what is quotiented out, so
its class is `0` (`AdjoinRoot.mk_self`), and `algebraMap` carries that `0` into the fraction field
(`map_zero`). There is zero mathematical content beyond those two mathlib primitives, and the proof
itself is the ≤3-call composition — so no new lemma is warranted on composability grounds.

Independently and decisively, the lemma **cannot go to mathlib at all**: its subject `polyToField`
(and the types `Universal.Field/Ring/Poly` and `curve`) are project-local — `grep` over the whole
mathlib tree returns 0 hits for `polyToField`, and there is no `Universal` namespace under
`EllipticCurve/`. This file is precisely the project's fork/extension of
`Mathlib.AlgebraicGeometry.EllipticCurve.*`; the universal-pointed-curve machinery is not upstream.
A `@[simp]` lemma about a non-mathlib definition is not itself a mathlib candidate. Verdict: **NO**,
and the right local action is to **keep** it as a useful `@[simp]` convenience for `polyToField`.

Mathlib building blocks:
- `AdjoinRoot.mk_self` — `Mathlib/RingTheory/AdjoinRoot.lean:217` (`mk f f = 0`, `@[simp]`)
- `map_zero` — generic `@[simp]` (`f 0 = 0`)
- (the `polyToField_apply` unfold is the project's `rfl` for `RingHom.comp_apply`)

Composition sketch (the existing proof, ≤3 lines):
```lean
example : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]   -- or: by simp
```

Call sites in our project (Phase 6.0): K = 3 NagellLutz uses (Universal.lean:147; ZSMul.lean:155,
267; +`simp only` at 282), plus implicit `@[simp]` firing. Refactor plan (LOCAL, not a mathlib
action): none required — a `@[simp]` "defining relation vanishes" lemma for a project def is
idiomatic project style and worth keeping for the readability of the ZSMul/`equation_point` proofs.
A cleaner could inline `AdjoinRoot.mk_self`/`map_zero` (or `simp`) at the few sites, but that is
optional polish, not an upstreaming action. **Cross-project note:** `projects/HasseWeil/` carries an
identical copy — a consolidation/dedup candidate for `main`, still not a mathlib candidate.

Next action: **no mathlib PR.** Keep `polyToField_polynomial` as a local `@[simp]` lemma; mathlib
already provides the only general content it expresses (`AdjoinRoot.mk_self` + `map_zero`), and its
subject is project-local and not upstreamed.

---

## Next step
No mathlib PR. The declaration is a `@[simp]` glue lemma for the project-local `def polyToField`,
recording the quotient's defining property at the universal Weierstrass polynomial; mathlib already
provides the general content (`AdjoinRoot.mk_self`, `Mathlib/RingTheory/AdjoinRoot.lean:217`, plus
`map_zero`). Recommended: leave it in place as a useful `@[simp]` convenience. It must not be
upstreamed — its subject (`polyToField`, `Universal.Field/Ring/Poly`, `curve`) is not in mathlib.
