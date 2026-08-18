# /mathlibable report — `WeierstrassCurve.baseChange_Φ`

> One-line verdict: **NO-mathlib-has-it.** This is a *verbatim fork* of
> `WeierstrassCurve.baseChange_Φ` from
> `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:577`.
> Same statement, same proof, same `Φ` definition. The whole file is, by its own
> docstring, "a copy of `Mathlib...DivisionPolynomial.Basic`".

---

### Baseline (Phase 0)
- lake build:               not run (sandbox build stale; reasoned from source — decl text + deps confirmed by grep)
- decl `WeierstrassCurve.baseChange_Φ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:500`
  (the prompt cited line 507, but line 507 is the *sibling* `baseChange_φ`; the lowercase-φ vs uppercase-Φ pair; the
  intended target by base name `baseChange_Φ` is line **500**)
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
  that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
  (both define `normEDS`, `complEDS`, etc.)."

The qualified name resolves cleanly: the file opens `namespace WeierstrassCurve` (line 27) and closes it at
line 511, with no intervening namespace, so the fully-qualified name is **`WeierstrassCurve.baseChange_Φ`** (the
`section BaseChange` does not add to the name path).

---

### Statement (Phase 1)

`WeierstrassCurve.baseChange_Φ` is a *functoriality / naturality* lemma for the univariate division polynomial
`Φₙ` of a Weierstrass curve under base change along an algebra homomorphism.

Setup: `R` a commutative ring, `W : WeierstrassCurve R`; `S` an `R`-algebra; `A, B` two `S`-algebras that are
also `R`-algebras compatibly (`[IsScalarTower R S A]`, `[IsScalarTower R S B]`); and an `S`-algebra homomorphism
`f : A →ₐ[S] B`. Then base-changing `W` to `B` and forming `Φₙ` gives the same univariate polynomial as
base-changing `W` to `A`, forming `Φₙ`, and pushing its coefficients along `f`:

  $$(W_B).\Phi_n \;=\; \big((W_A).\Phi_n\big).\mathrm{map}\,f \qquad (n \in \mathbb Z).$$

Here `Φₙ ∈ R[X]` is the univariate "numerator" polynomial congruent to `φₙ`, defined by
`Φₙ = X·ΨSqₙ − preΨ(n+1)·preΨ(n−1)·(if Even n then 1 else Ψ₂Sq)`. The lemma is the special case (for `Φ`) of the
general principle that division polynomials, being built from *universal* integer recurrences in the Weierstrass
coefficients `aᵢ`, commute with every ring map.

Variables / typeclasses (Lean side):
- `R S A B : Type _` `[CommRing _]` — the coefficient rings.
- `[Algebra R S]`, `[Algebra R A]`, `[Algebra S A]`, `[Algebra R B]`, `[Algebra S B]` — the algebra structures.
- `[IsScalarTower R S A]`, `[IsScalarTower R S B]` — compatibility so `W.baseChange A`, `W.baseChange B` make sense.
- `W : WeierstrassCurve R` — the curve.
- `f : A →ₐ[S] B` — the algebra hom along whose coefficient action `Φ` is transported.

Hypotheses: none beyond the typeclass context; `n : ℤ` is universally quantified.

Conclusion (math): `Φₙ` is natural in the base ring — it commutes with base change followed by coefficient map.
Conclusion (Lean): `(W.baseChange B).Φ n = ((W.baseChange A).Φ n).map f`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step naturality/glue lemma (`rw [← map_Φ, map_baseChange]`) about an existing mathlib object; not a
named theorem, not a project main result, introduces no new structure. (Literature width was still run to protocol.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-line *definition* check does not apply. (For the record
the *proof* is a single line, `rw [← map_Φ, map_baseChange]`, which reinforces that it is glue over existing API.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                     | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve base change ring homomorphism commute compatibility"  | yes  | division polys ψₙ,φₙ ∈ ℤ[x,y,{aᵢ}] → commute with ring maps | universal-coefficient construction; base-change functoriality standard |
|  2 | WebSearch (general / naturality) | (same query, "general ring" / "arbitrary ring" facet of results)                          | yes  | `α_n,β_n,γ_n` homogeneous div. polys over arbitrary ring (arXiv:1303.4327); SageMath builds `Φₙ` over base ring | confirms div. polys are defined over an arbitrary commutative ring, hence natural |
|  3 | WebSearch (named-after / aliases)| "division polynomial" functorial base change field extension E(F)→E(K) (arXiv:2302.10640) | yes  | group-law formalisation treats base change to field ext. | naturality of the algebraic data under base change is explicitly handled |
|  4 | ChatGPT MCP                      | n/a — MCP server down this session (per task note); compensated with extra WebSearch facets + primary-source reasoning | n/a | — | Silverman, *Arithmetic of Elliptic Curves* (2nd ed.) Exercise 3.7 / III §3 defines ψₙ by integer recurrences ⇒ stable under base change |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` (and `refs/`) for "division polynomial" / base change | n/a | no references dir present for this concept | recorded n/a — directory absent; concept settled by mathlib itself |
|  6 | nLab                             | "division polynomial"                                                                       | n/a  | nLab has no dedicated division-polynomial page          | not an nLab-shaped (categorical) concept; naturality here is elementary |
|  7 | nCatLab (categorical)            | —                                                                                          | n/a  | —                                                     | not a categorical concept; no functor/2-cat content to chase |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                       | n/a  | Stacks has no division-polynomial entry                 | Stacks is scheme-theoretic foundations; div. polys are a concrete construction not in scope there |
|  9 | MathOverflow / Math.StackExchange| "division polynomial defined over ℤ base change"                                            | yes  | folklore: ψₙ universal over ℤ[aᵢ], so any ring map sends ψₙ(W) ↦ ψₙ(W') | corroborates the universal-coefficient argument |
| 10 | recent arXiv (last 5y)           | "homogeneous division polynomials Weierstrass" (arXiv:1303.4327, 2013) + group-law (2302.10640, 2023) | yes | div. polys over arbitrary rings; base-change-stable | modern treatments keep the over-any-ring formulation |

### Literature summary (Phase 3)

Concept identified as: the **(univariate) division polynomial `Φₙ`** of a Weierstrass curve, and the **naturality
of division polynomials under base change / ring maps**.
Sources agree on the standard form: **yes** — division polynomials are universal polynomials with integer
coefficients in the Weierstrass coefficients `aᵢ` (Silverman III §3 / Ex. 3.7; arXiv:1303.4327; arXiv:2302.10640;
SageMath `ell_generic`). Being universal, they are *defined over an arbitrary commutative ring* and therefore
**commute with every ring homomorphism** — equivalently, they are natural under base change. This naturality is
folklore; it is the content of `baseChange_Φ`.
Most general standard form: for a Weierstrass curve over any commutative ring and any ring map of the coefficient
ring, the division polynomials transport along the map. The mathlib statement (over an `R`-algebra tower with an
`S`-algebra hom `f`) is exactly this naturality, packaged for the base-change operation.
Generality dimensions where the literature varies:
  - coefficient ring: literature uses *arbitrary commutative ring* — matches mathlib (`CommRing`), no field/PID assumed.
  - the map: literature uses *any ring homomorphism*; mathlib phrases it as base change + coefficient `.map f`,
    the standard packaging.
Disagreement with the literature: **none.** mathlib's form is the literature-standard naturality, at full generality.

---

### Generality analysis — `WeierstrassCurve.baseChange_Φ`

Literature-standard form (from Phase 3): division polynomials over an *arbitrary commutative ring* commute with
*arbitrary ring maps* (base change). No field, no domain, no PID, no algebraically-closed hypothesis.

| # | Parameter / hypothesis                         | Current Lean form                | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------------|----------------------------------|------------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]` (and `S A B`)                    | arbitrary commutative ring       | arbitrary commutative ring         | NO                  | already maximally general for the coefficient ring |
| 2 | `f : A →ₐ[S] B`                                 | `S`-algebra homomorphism         | any ring map of coefficients       | borderline          | the *base-change* packaging is the canonical mathlib idiom; the even-more-primitive `map_Φ` (along a plain ring hom) already exists upstream and `baseChange_Φ` is the tower-relative corollary. Not a defect — it is the intended specialisation siblinged with `map_Φ`. |
| 3 | `n : ℤ`                                          | integer index                    | integer index                      | NO                  | division polynomials are indexed by ℤ; correct index type |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it *is* mathlib's own form, verbatim).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                         | no       | already fully typeclass-driven (`Algebra`, `IsScalarTower`) | — |
|  2 | sequences/metric → filters/topology?                                                        | no       | purely algebraic identity; no topology | — |
|  3 | construction → universal-property class?                                                    | no       | this is a naturality equation, not a construction | — |
|  4 | set-with-closure → bundled substructure?                                                     | no       | no substructure content | — |
|  5 | vector-space/metric/field-specific → weaken typeclass?                                       | no       | already at `CommRing`; nothing to weaken | — |
|  6 | 1-categorical → higher-categorical?                                                          | no       | elementary polynomial identity | — |
|  7 | concrete index → general additive structure?                                                | no       | `ℤ` is the correct, intrinsic index for division polynomials | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The lemma is already the contemporary mathlib formulation (it is the mathlib
declaration itself). No organisational improvement is possible — there is nothing to modernise about copy of upstream.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instances introduced).

---

### Mathlib search-status: `WeierstrassCurve.baseChange_Φ`

[A] Lean-Finder       n/a (mathlib-index tools available but unnecessary — direct source hit below)
[B] Loogle            type `(W.baseChange _).Φ _ = _` — n/a; superseded by exact-source grep
[C] LeanSearch        "division polynomial base change algebra hom" — n/a; superseded by exact-source grep
[D] Grep mathlib src  `grep -rn "baseChange_Φ" .lake/packages/mathlib/` → **HIT**
[E] Name pattern      `baseChange_Φ` in `WeierstrassCurve` namespace → **HIT**

Direct source evidence:
```
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:577:
  lemma baseChange_Φ (n : ℤ) : (W⁄B).Φ n = ((W⁄A).Φ n).map f := by
    rw [← map_Φ, map_baseChange]
```
This is *identical* to the project decl modulo notation: mathlib writes `W⁄B` for `W.baseChange B`
(`⁄` is mathlib's base-change notation). The project's underlying `Φ` definition (line 272) is **byte-identical**
to mathlib's (line 349), and the two proof dependencies both exist upstream and are forked too:
- `WeierstrassCurve.map_Φ` — `DivisionPolynomial/Basic.lean:531` (project copy: `DivisionPolynomial.lean:454`)
- `WeierstrassCurve.map_baseChange` — `EllipticCurve/Weierstrass.lean:285` (imported from mathlib unchanged; not
  re-defined in the project file).

Searched for both:
  - the user's current form `(W.baseChange B).Φ n = ((W.baseChange A).Φ n).map f` → found, identical.
  - the more-primitive form `map_Φ` (along a plain ring hom) → also found upstream; `baseChange_Φ` is its tower corollary.

Concluded: **found in mathlib as `WeierstrassCurve.baseChange_Φ`; identical form** (verbatim fork, same statement
and same proof).

---

### Call sites — `WeierstrassCurve.baseChange_Φ`

Internal use count: **0** (within the NagellLutz project, excluding the declaring file).
External-to-file callers: 0 `.lean` files.

| Caller file:line               | Usage pattern (one-line excerpt) |
|--------------------------------|----------------------------------|
| (none)                         | — |

Grep `baseChange_Φ` across `projects/**.lean` (excluding `.lake`) returns *only* the declaration site
(`DivisionPolynomial.lean:500`); every other hit is in `.mathlib-quality/` markdown (overview/inventory docs),
not Lean code.

Inline-derivation grep (was the equivalent re-derived elsewhere?): (none) — no project code uses `Φ` base change at all.

Interpretation: `K = 0`, no inline re-derivation. This is **forked dead-weight** — the lemma is present only
because the whole `DivisionPolynomial.Basic` file was copied to dodge the `normEDS` import clash; nothing in the
project consumes it. There is a sibling precedent in this same folder: `baseChange_ψ₂.md` already reached the
identical conclusion ("a wholesale copy of mathlib's" file).

---

### Composition check (Phase 6)

Can `baseChange_Φ` be derived from mathlib in ≤3 chained calls? — **It IS mathlib**, so trivially yes; the
mathlib-native proof is the 2-call composition:

Attempt 1: `by rw [← map_Φ, map_baseChange]`
  - Mathlib decls used: `WeierstrassCurve.map_Φ` (`DivisionPolynomial/Basic.lean:531`),
    `WeierstrassCurve.map_baseChange` (`Weierstrass.lean:285`).
  - Result: succeeds (this is verbatim the upstream proof).
  - Notes: but composition is moot — the *fully assembled* lemma already exists upstream under the same name, so
    the correct action is to reuse the mathlib decl, not to inline its proof.

Conclusion: the form is **already in mathlib verbatim** (a strictly stronger fact than "composable"). The verdict
is NO-mathlib-has-it, not NO-composable-from-mathlib: when mathlib has the *assembled, identically-named* lemma,
the refactor is "delete the fork and use upstream", not "inline a composition".

---

## Verdict: `WeierstrassCurve.baseChange_Φ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): division-polynomial naturality under base change is standard folklore (universal
  integer coefficients ⇒ commute with ring maps); mathlib already encodes it. No generality gap.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it is mathlib's own statement, at `CommRing`, no idiom gap (4c: no).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.baseChange_Φ`, identical form
  (`DivisionPolynomial/Basic.lean:577`); proof deps `map_Φ`/`map_baseChange` also upstream.
- Composition check (Phase 6): the assembled lemma already exists upstream verbatim (stronger than composable).

**Rationale:**

This declaration is a **verbatim fork** of `WeierstrassCurve.baseChange_Φ` from mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`. The statement is identical (the project
spells `W.baseChange B` where mathlib uses the notation `W⁄B` for the same term), the proof is identical
(`rw [← map_Φ, map_baseChange]`), the underlying `Φ` definition is byte-identical, and both proof dependencies
exist upstream (one of them, `map_baseChange`, is not even re-defined in the project — it is imported from mathlib
unchanged). The file's own module docstring states it is "a copy of `Mathlib...DivisionPolynomial.Basic`", forked
solely to import the project's local `EllipticDivisibilitySequence` (to avoid the `normEDS`/`complEDS` name clash)
rather than mathlib's. Mathlib does not need this — mathlib *is* the source. The literature search (run to protocol
despite the open-and-shut source hit) confirms there is no generality the fork adds: division polynomials are
universal polynomials over `ℤ[{aᵢ}]`, so their commuting with ring maps is the maximally-general standard fact, and
mathlib already states it at `CommRing`.

**WHY not (refactor-actionable):**
Mathlib already has the exact result — same name, same statement, same proof, same `Φ`. The project's copy exists
purely as collateral of copying the entire `DivisionPolynomial.Basic` file to swap one import. The proper resolution
is the project-level one (drop the fork once the upstream `normEDS` clash is otherwise managed), not a per-lemma
edit; but as a mathlibable verdict, this lemma contributes nothing new to mathlib.

Existing mathlib decl:        `WeierstrassCurve.baseChange_Φ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:577`
Our form follows in ≤1 line (it is the *same* lemma — exact reuse, not even a specialisation):
```lean
example {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) [Algebra R S]
    {A : Type*} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    {B : Type*} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[S] B) (n : ℤ) :
    (W.baseChange B).Φ n = ((W.baseChange A).Φ n).map f :=
  WeierstrassCurve.baseChange_Φ f n   -- the mathlib lemma, used directly
```
Call sites in our project (from Phase 6.0):  **K = 0**.
Refactor plan: there are no in-project consumers to migrate. The decl is dead-weight carried by the file copy.
The correct fix is the file-level one — eliminate the fork of `DivisionPolynomial.Basic` (and its siblings
`baseChange_ψ₂`, `baseChange_Ψ₂Sq`, `baseChange_Ψ₃`, `baseChange_preΨ₄`, `baseChange_preΨ'`, `baseChange_preΨ`,
`baseChange_ΨSq`, `baseChange_Ψ`, `baseChange_φ`, plus the whole `map_*`/`Φ`/etc. copies) by resolving the
`EllipticDivisibilitySequence` import clash (e.g. namespacing the project's `normEDS`/`complEDS`, or importing
mathlib's), then importing mathlib's `DivisionPolynomial.Basic` directly so `WeierstrassCurve.baseChange_Φ`
resolves to the upstream lemma. No call-site rewrites are needed for *this* lemma specifically since it has none.
Next action: do **not** PR this to mathlib (it is already there). Track it under the project-level
"de-fork `DivisionPolynomial.Basic`" cleanup, not a mathlib submission.

---

## Next step

This lemma is already in mathlib verbatim (`WeierstrassCurve.baseChange_Φ`,
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:577`). Nothing to upstream. Fold it into the
file-level de-fork cleanup of the copied `DivisionPolynomial.Basic` (the import-clash workaround), alongside its
identically-forked `baseChange_*` / `map_*` / `Φ` siblings; it has zero in-project call sites, so no consumer
migration is required for this decl.
