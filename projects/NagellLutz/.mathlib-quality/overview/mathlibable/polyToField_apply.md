# /mathlibable report — `WeierstrassCurve.Universal.polyToField_apply`

### Baseline (Phase 0)
- lake build:               (not re-run — repo states local build stale; decl reasoned from source)
- decl `WeierstrassCurve.Universal.polyToField_apply`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:110`
- kind:                      lemma (glue / `:= rfl`)
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` and the construction of the **universal
  elliptic curve** over `ℤ[A₁,A₂,A₃,A₄,A₆]`; defines `Universal.Poly`, `Universal.Ring`
  (= coordinate ring), `Universal.Field` (= its fraction field) and the ring hom `polyToField`
  between them.

**True qualified name (VERIFIED from source):** the lemma sits inside
`namespace WeierstrassCurve` → `namespace Universal` (Universal.lean:69, 75). So the parsed name
`WeierstrassCurve.Universal.polyToField_apply` is correct.

---

### Statement (Phase 1)

`polyToField_apply` states that applying the project-local ring homomorphism
`polyToField : Universal.Poly →+* Universal.Field` to a polynomial `p` equals applying its two
component maps in sequence: first the quotient map `AdjoinRoot.mk W.polynomial`, then the
`algebraMap` of the coordinate ring into its field of fractions.

In prose: for the universal pointed Weierstrass curve, the canonical map
`ℤ[A₁,…,A₆,X,Y] → Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)` is, on each element, the composite "reduce mod the
Weierstrass relation, then include into the fraction field." This is a pure **definitional
unfolding** of `polyToField`, which is *defined* (Universal.lean:108) as exactly that composite
`(algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)`.

Variables / typeclasses involved (Lean side):
- none beyond the fixed project types `Universal.Poly`, `Universal.Ring`, `Universal.Field`
  (all `noncomputable` concrete types — no free `[CommRing R]` etc.).

Hypotheses (Lean side):
- `(p : Poly)` — the polynomial being mapped. No other hypotheses.

Conclusion (math): the composite map agrees with sequential application of its two factors.
Conclusion (Lean): `polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p)`.

Source (Universal.lean:108, 110–111):
```lean
def polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := rfl
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A `:= rfl` `_apply`/unfolding lemma for a project-local `def`. Not a named theorem, not a
new structure, not a `## Main results` goal. (Literature width still run EXHAUSTIVE per protocol.)

### One-line check (Phase 2b)

Body line count: 1 (`:= rfl`).
One-liner verdict: n/a — kind is `lemma`, not a `def`. The 2b def-exemption table does not apply to
lemmas. Recorded note: this is an unfolding lemma whose entire content is `rfl`; the relevant signal
is the composition check (Phase 6), not the def-exemption rows.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|----------------------|-------|
|  1 | WebSearch (specific form)        | ring homomorphism composition application "comp_apply" defeq Lean mathlib                       | yes  | `(g∘f)(x)=g(f(x))` — `RingHom.comp_apply` | The only "concept" present is composite-morphism application; no mathematical theorem named after this |
|  2 | WebSearch (general / context)    | universal elliptic curve coordinate ring AdjoinRoot field of fractions Weierstrass polynomial   | yes  | `R[W]:=AdjoinRoot W.polynomial`, `R(W):=Frac(R[W])` | Confirms the *def* `polyToField` is a standard construction; but this lemma is just its unfolding |
|  3 | WebSearch (convention / aliases) | mathlib "def" unfolding lemma rfl simp-normal form ring hom composition convention              | yes  | `def` is semireducible ⇒ projects add an `_apply` unfolding lemma | Confirms `_apply` lemmas are a *local* convenience, not standalone math |
|  4 | ChatGPT MCP                      | "Is `polyToField_apply` more than a specialization of `RingHom.comp_apply`? Any math content?"  | n/a  | — | MCP server down in this environment (Codex exec failed); fallbacks used. The question is settled by source: see Phase 6 |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                              | n/a  | — | Directory absent for this project (only `overview/` exists). Recorded n/a. |
|  6 | nLab                             | "ring homomorphism composition" / "composite of morphisms"                                       | n/a  | — | Composition of morphisms is category-theory-trivial; nLab has no dedicated page for "apply a composite ring hom". No nontrivial concept to look up. |
|  7 | nCatLab                          | —                                                                                                | n/a  | — | Not a categorical concept beyond ordinary composition; nothing to add. |
|  8 | Stacks Project                   | coordinate ring / function field of a curve                                                      | n/a  | — | Stacks has the *construction* (function field = Frac of coordinate ring), but no lemma corresponding to a Lean definitional-unfolding `rfl`. n/a for this lemma. |
|  9 | MathOverflow / Math.StackExchange| —                                                                                                | n/a  | — | No research-level question corresponds to "apply a composite ring hom"; it is a one-step formal triviality. |
| 10 | recent arXiv (last 5 years)      | homogeneous / division polynomials universal Weierstrass curve                                   | yes  | universal curve constructions (e.g. arXiv:1303.4327, 0810.2853) | These concern the *mathematics* the def supports (division polynomials, EDS), not this unfolding lemma. |

### Literature summary (Phase 3)

Concept identified as: **application of a composite ring homomorphism** — i.e. an instance of
`RingHom.comp_apply`. The surrounding mathematics (universal Weierstrass curve, coordinate ring
`AdjoinRoot W.polynomial`, function field `Frac`) is standard and well-documented, but it pertains
to the *definition* `polyToField`, not to this `rfl` lemma.
Sources agree on the standard form: yes — `(g∘f)(x) = g(f(x))`; universally trivial.
Most general standard form: for any two composable (ring) homomorphisms, applying the composite =
applying them in sequence. Mathlib already states this maximally generally as `RingHom.comp_apply`.
Generality dimensions where the literature varies: none of mathematical substance — the only
variation is the morphism class (`RingHom`, `MonoidHom`, `AlgHom`, plain `Function.comp`), each of
which mathlib already provides a `comp_apply` for.
Disagreement with the literature: none. There is no mathematical theorem here; the lemma is a
formal-library convenience exposing a semireducible `def`.

---

### Generality analysis — `WeierstrassCurve.Universal.polyToField_apply`

Literature-standard form (from Phase 3): `RingHom.comp_apply : (g.comp f) x = g (f x)`, stated for
arbitrary `α β γ` ring homs. The user's lemma is the *fully specialised* instance with
`g := algebraMap Universal.Ring Universal.Field`, `f := AdjoinRoot.mk curve.polynomial`,
`x := p`, and the composite `g.comp f` named `polyToField`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | the two factor maps    | the two *specific* maps `algebraMap …` and `AdjoinRoot.mk …` | arbitrary composable ring homs `g`, `f` | yes (already exists) | The general form is exactly `RingHom.comp_apply`; the user's lemma is its specialisation to fixed maps. No new generality to add — mathlib has the general form. |
| 2 | base ring / curve      | the concrete `MvPolynomial Coeff ℤ` universal curve | any `W : Affine R` over `[CommRing R]` | yes in principle | One *could* state `(W.polyToField …) p = algebraMap … (AdjoinRoot.mk …)` for a general `W`, but `polyToField` itself is defined only for the universal curve and only as a `comp`; the general statement is still just `RingHom.comp_apply`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is a full specialisation of
`RingHom.comp_apply`), but the more general form is **already in mathlib**, so this is not a
"generalise-then-add" situation — it is a "mathlib already has the general primitive" situation.
Number of weakening opportunities found: the only "weakening" is to recover `RingHom.comp_apply`
itself, which exists. K = 0 *new* weakenings worth adding.
Proposed restatement: none worth adding — the maximally general statement is `RingHom.comp_apply`,
already present.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | bundled-hyp → typeclass? | no | — | No "let X be a foo" preamble; the maps are fixed. |
|  2 | sequences/metric → filters/topology? | no | — | No analysis here; pure algebra. |
|  3 | construction → universal-property class? | no | — | The *construction* (`polyToField` via `comp`) is fine; the lemma is its unfolding. Universal-property phrasing would not change a `rfl` unfolding lemma. |
|  4 | set+closure-pred → bundled substructure? | no | — | No substructure involved. |
|  5 | vector-space/field-specific → weaker typeclass? | no | — | Already at the `RingHom` level; `RingHom.comp_apply` is the idiomatic primitive. |
|  6 | 1-categorical → higher-categorical? | no | — | Ordinary composition; no categorification target. |
|  7 | concrete index → general monoid/group? | no | — | No numeric index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The contemporary mathlib idiom for "apply a composite ring hom" is
precisely `RingHom.comp_apply` (or `RingHom.coe_comp` + `Function.comp_apply`). The user's lemma is
already at that altitude; there is no organisational improvement to make — except to *use the
primitive directly* rather than ship a renamed specialisation.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (a proof, not a `def`/`class`/`instance`). It introduces no new
definitional equality or typeclass-search path. (The *def* `polyToField` would be the object of such
an assessment, but it is out of scope for this lemma and is itself project-local, not a mathlib
candidate.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.polyToField_apply`

[A] Lean-Finder       "apply composite ring homomorphism" / "comp apply ring hom" — general hit: `RingHom.comp_apply` (the primitive). The *specific* `polyToField_apply` is project-local; n/a in mathlib.
[B] Loogle            `RingHom.comp _ _ _ = _ _` pattern → `RingHom.comp_apply`; `?g.comp ?f ?x = ?g (?f ?x)` → exact match `RingHom.comp_apply`. No mathlib decl named `polyToField`.
[C] LeanSearch        "applying a composition of ring homomorphisms equals applying them one after another" → `RingHom.comp_apply` / `MonoidHom.comp_apply` / `AlgHom.comp_apply`.
[D] Grep mathlib src  `grep -rn "polyToField" .lake/packages/mathlib/` → **0 hits**. `polyToField`, `Universal.Field`, `Universal.Ring` do not exist anywhere in mathlib. The whole universal-pointed-curve construction (this file) is the project forking/extending `Mathlib.AlgebraicGeometry.EllipticCurve.*`; the `Universal` namespace is not upstream. `RingHom.comp_apply` confirmed at `Mathlib/Algebra/Ring/Hom/Defs.lean:554` (`:= rfl`).
[E] Name pattern      `polyToField_apply` — only in `projects/NagellLutz/` (declaring file + 2 ZSMul.lean uses). Not in mathlib.

Searched for both:
  - the user's current form (`polyToField_apply`) — **not in mathlib** (subject is project-local).
  - the literature-standard form (`RingHom.comp_apply`) — **in mathlib**, `Mathlib/Algebra/Ring/Hom/Defs.lean:554`, proved `:= rfl`, maximally general.

Concluded: **found the building block** `RingHom.comp_apply` (and `RingHom.coe_comp`); the user's
form is the specialisation of that primitive to the project-local maps. The user's *named* lemma is
not (and cannot be) in mathlib because its subject `polyToField` is a project-local definition over
the not-upstreamed universal curve.

---

### Call sites — `WeierstrassCurve.Universal.polyToField_apply`

Internal use count: **3** total — 1 in the declaring file, 2 external to the declaring file.
External-to-file callers: **1** distinct file (`ZSMul.lean`).

| Caller file:line               | Usage pattern (one-line excerpt) |
|--------------------------------|-----------------------------------|
| Universal.lean:121             | `rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]` (proof of `polyToField_polynomial`) |
| ZSMul.lean:143                 | `rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h` |
| ZSMul.lean:149                 | `rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h` |

Inline-derivation grep (was the equivalent re-derived without using `polyToField_apply`?):
  - (none found) — but note every use is a `rw [polyToField_apply, …]` whose purpose is to *unfold*
    `polyToField` so that `AdjoinRoot.mk` / `algebraMap` lemmas (`mk_self`, `map_eq_zero_iff` with
    `IsFractionRing.injective`) can fire. Each is exactly the kind of "expose the composite then peel
    off `IsFractionRing.injective`" step that `RingHom.comp_apply` would serve.

Call-sites signal: K = 3 internal uses, no external-to-project consumers. The lemma is a *local
unfolding convenience* for `polyToField`. Per the Phase-6 table this is a "real local API" pattern,
but the API is about a **project-local def**, so it is not mathlib material — it lives and dies with
`polyToField`.

---

### Composition check (Phase 6)

Can `polyToField_apply` be derived from mathlib in ≤3 chained calls? **Yes — a single call.**

Attempt 1: `RingHom.comp_apply (algebraMap Universal.Ring Universal.Field) (AdjoinRoot.mk curve.polynomial) p`
  - Because `polyToField` is *definitionally* `(algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)`,
    the goal `polyToField p = algebraMap … (AdjoinRoot.mk … p)` is *exactly* the statement of
    `RingHom.comp_apply` after unfolding `polyToField`. Indeed the proof is `rfl`, and
    `RingHom.comp_apply` is itself `rfl`.
  - Mathlib decls used: `RingHom.comp_apply` (single call). Equivalently `by rw [polyToField,
    RingHom.comp_apply]` or just `rfl`.
  - Result: **succeeds** (1 call).
  - Notes: no glue, no `have` chain, no `ring`/`simp` — a one-step definitional fact.

Conclusion: **COMPOSABLE** (1 mathlib call, well under the ≤3 budget).

---

## Verdict: `WeierstrassCurve.Universal.polyToField_apply`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the only concept is "apply a composite ring hom" = `RingHom.comp_apply`; no standalone mathematical theorem; surrounding math (universal curve) belongs to the *def*, not this lemma.
- Generality analysis (Phase 4): STRICTLY NARROWER than standard, but the general form (`RingHom.comp_apply`) is already in mathlib; no new generalisation to ship. Modern-idiom: none.
- Mathlib search (Phase 5): found the building block `RingHom.comp_apply` (`Mathlib/Algebra/Ring/Hom/Defs.lean:554`, `:= rfl`); `polyToField`/`Universal.*` have 0 hits in mathlib (project-local, not upstreamed).
- Composition check (Phase 6): COMPOSABLE in a single call to `RingHom.comp_apply` (the lemma is `rfl`).

**Rationale:**

`polyToField_apply` is a `:= rfl` unfolding lemma for the project-local definition
`polyToField := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)`. Its statement is *literally*
mathlib's `RingHom.comp_apply` specialised to the two concrete factor maps — both the lemma and
`RingHom.comp_apply` are proved by `rfl`, so there is exactly one step and zero mathematical content
beyond "applying a composite ring homomorphism equals applying its factors in sequence." It is a
one-call composition from a mathlib primitive, so no new lemma is warranted on composability grounds.

Independently and decisively, the lemma **cannot go to mathlib at all**: its subject `polyToField`
(and the types `Universal.Field`, `Universal.Ring`, `Universal.Poly`) are project-local — `grep`
over the whole mathlib tree returns 0 hits for `polyToField`. This file is precisely the project's
fork/extension of `Mathlib.AlgebraicGeometry.EllipticCurve.*`; the universal-pointed-curve
machinery is not upstream. An `_apply` lemma about a non-mathlib definition is not itself a mathlib
candidate. So the verdict is NO — and the right local action is simply to *keep* it as the standard
semireducible-`def` unfolding convenience (or, equivalently, replace each `rw [polyToField_apply]`
with `rw [polyToField, RingHom.comp_apply]`). It is correct, idiomatic project code; it is just not
a mathlib contribution.

WHY not (refactor-actionable detail):
- Mathlib has the building block `RingHom.comp_apply`. The user's lemma is its specialisation to
  `g := algebraMap Universal.Ring Universal.Field`, `f := AdjoinRoot.mk curve.polynomial`. Because
  `polyToField` is defined as that very `comp`, the unfolding is `rfl`.

Mathlib building blocks:
- `RingHom.comp_apply` — `Mathlib/Algebra/Ring/Hom/Defs.lean:554` (`(g.comp f) x = g (f x) := rfl`)
- (alt) `RingHom.coe_comp` — `Mathlib/Algebra/Ring/Hom/Defs.lean:551` + `Function.comp_apply`

Composition sketch (≤3 lines):
```lean
-- the named lemma is unnecessary as a standalone; inline at call sites:
example (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) :=
  RingHom.comp_apply _ _ p          -- or: rfl
```

Call sites in our project (from Phase 6.0): K = 3 (Universal.lean:121; ZSMul.lean:143, 149).
Refactor plan (LOCAL, not a mathlib action): this is project-local, so the "delete + inline"
refactor is **optional polish, not required** — a `:= rfl` unfolding lemma for a semireducible
`def` is itself idiomatic mathlib *style*. If a cleaner wishes to remove the wrapper, then at each of
the 3 sites replace `rw [polyToField_apply, …]` with `rw [polyToField, RingHom.comp_apply, …]`
(verify nothing downstream relies on the `polyToField_apply` name; the rewrites at 143/149 then
continue into `map_eq_zero_iff _ (IsFractionRing.injective _ _)` unchanged). Net: the lemma stays in
the project as a local convenience; it is **not** upstreamed to mathlib.

Next action: no mathlib PR. Keep `polyToField_apply` as a local unfolding lemma (recommended), or
optionally inline `RingHom.comp_apply` at the 3 call sites. No action toward mathlib is taken — the
declaration is project-local glue, and mathlib already has the only general fact it expresses
(`RingHom.comp_apply`).

---

## Next step

No mathlib PR. The declaration is a `rfl` unfolding lemma for the project-local `def polyToField`;
mathlib already provides the only general content (`RingHom.comp_apply`, `Mathlib/Algebra/Ring/Hom/Defs.lean:554`).
Recommended: leave it in place as the standard semireducible-`def` unfolding convenience. Optionally,
a cleaner may inline `RingHom.comp_apply` at its 3 call sites — but it must not be upstreamed, since
its subject (`polyToField`, `Universal.Field/Ring/Poly`) is not in mathlib.
