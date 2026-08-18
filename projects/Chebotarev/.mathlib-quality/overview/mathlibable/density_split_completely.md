# Mathlibable assessment: `Chebotarev.density_split_completely`

**Verdict: BORDERLINE-needs-human**

## Declaration

Qualified name (verified from source): **`Chebotarev.density_split_completely`**
File: `projects/Chebotarev/CebotarevDensity/Main.lean:151`

```lean
/-- **Density of completely split primes** (Sharifi 7.1.14, as a corollary of
Chebotarev applied to the identity conjugacy class).

The Dirichlet density of primes `𝔭` of `𝓞 K` that split completely in `L`
equals `1 / [L : K]`. -/
theorem density_split_completely :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk 1}
      ((Module.finrank K L : ℝ)⁻¹) := by
  have h := chebotarev_density (ConjClasses.mk (1 : Gal(L/K)))
  rw [ConjClasses_mk_one_carrier_card_eq_one Gal(L/K), IsGalois.card_aut_eq_finrank K L] at h
  simpa using h
```

Ambient context (`namespace Chebotarev`):
`variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]`.

It is a 3-line corollary of the project's main result `Chebotarev.chebotarev_density`
specialised to the identity conjugacy class `ConjClasses.mk 1`.

## What the statement actually says

The Dirichlet density of the set of unramified primes `𝔭` of `𝓞 K` whose Frobenius
conjugacy class is trivial (= the identity class) equals `1/[L:K]`. By the
standard dictionary (`unramified + trivial Frobenius ⟺ splits completely`), this
is the density-of-completely-split-primes statement. **However** the set is
written using the project's own `frobeniusClass K L 𝔭 = ConjClasses.mk 1`, *not*
a mathlib-native "splits completely" predicate.

## Literature search (concept: density of completely-split primes)

| Source | Statement of the standard form |
|---|---|
| Wikipedia, *Chebotarev density theorem* | Primes splitting completely in a finite Galois `F/ℚ` have density `1/[F:ℚ]`; the conjugacy class with `k` elements occurs with frequency `k/n`. |
| Stevenhagen–Lenstra, *Chebotarëv and his density theorem* (Appendix) | Frobenius classes equidistribute; identity class ⇒ completely split ⇒ density `1/n`. |
| Sharifi, *Algebraic Number Theory*, **Thm 7.1.14 / 7.2.2** (the cited source) | Density of primes of `K` splitting completely in `L` is `1/[L:K]`; corollary of the conjugacy-class form at the identity class. |
| MIT 18.785 Lecture 28 (global CFT + Chebotarev) | Same: identity-class specialisation of Chebotarev. |
| Conrad, *Dirichlet density for global fields* | Same density statement, framed via Dirichlet density (matching this project's `HasDirichletDensity`). |

**Conclusion:** the *mathematical content* is exactly the literature-standard form
(finite Galois extension of number fields, density `1/[L:K]`). Generality is
correct and standard — no under- or over-generalisation. The statement is the
canonical corollary of Chebotarev at the identity class.

## Mathlib search (5 methods)

- **WebSearch / arXiv** ("Formalizing zeta and L-functions in Lean", arXiv 2503.00959):
  mathlib has the analytic-NT infrastructure (zeta/L-functions, ongoing
  Dirichlet-AP), but **Chebotarev's density theorem is not in mathlib**, and
  there is **no** density-of-completely-split-primes result.
- **Dirichlet density**: mathlib has **no** `HasDirichletDensity` / analytic
  density of prime ideals. The notion used here (`primeIdealZetaSum S s /
  primeIdealZetaSum univ s → δ` as `s ↓ 1`) is **defined locally** in
  `CebotarevDensity/Density.lean:64`.
- **Frobenius class of a prime**: `frobeniusClass` is **defined locally**
  (`CebotarevDensity/Frobenius.lean:188`), as is `UnramifiedIn`
  (`Frobenius.lean:62`). Mathlib has `IsArithFrobAt` (used to *build* these) but
  no packaged `frobeniusClass : ConjClasses Gal(L/K)`.
- **"splits completely" predicate**: mathlib has splitting/ramification API on
  `Ideal` (`Ideal.ramificationIdx`, `inertiaDeg`, `primesOver`, …), and a sibling
  AINTLIB project even defines `BernoulliRegular.Ideal.SplitsCompletely`. But this
  theorem does **not** use any of these; it encodes "splits completely" as
  `frobeniusClass = ConjClasses.mk 1`.
- **leansearch/loogle (mathlib index)**: nothing matching this combined
  shape (Dirichlet density + Frobenius class + `1/[L:K]`).

Net: **every symbol in the statement except `Module.finrank`, `Ideal`,
`IsPrime`, `ConjClasses.mk`, and `𝓞 K` is a project-local definition.** The
statement does not speak mathlib's vocabulary.

## Generality analysis

Against the literature-standard form, the hypotheses are exactly right: finite
Galois `L/K` of number fields, conclusion density `1/[L:K]`. Nothing to weaken or
strengthen mathematically. The *only* generality concern is presentational:
"splits completely" is encoded as trivial Frobenius class rather than via a
mathlib `Ideal`-splitting predicate, which a reviewer would likely want
restated (e.g. in terms of `Ideal.primesOver` cardinality `= [L:K]`, or an
`⟺ SplitsCompletely` bridge) before this lands in mathlib.

## Composition check (≤3 calls?)

Yes — but **from project code, not from mathlib**. The proof is literally:

1. `chebotarev_density (ConjClasses.mk 1)`  ← **project-local** main theorem,
2. `rw [ConjClasses_mk_one_carrier_card_eq_one …]`  ← project-local (`|C| = 1`),
3. `rw [IsGalois.card_aut_eq_finrank K L]`  ← mathlib (`|Gal(L/K)| = [L:K]`),
4. `simpa`.

So it is a one-line specialisation of the project's own Chebotarev theorem. It is
**not** composable from *mathlib* primitives, because its essential input
(`chebotarev_density`, and the whole `HasDirichletDensity` framework) is **not in
mathlib**. Within the project it is a trivial corollary and would never warrant a
standalone mathlib entry independent of the framework it rides on.

## Verdict rationale → BORDERLINE-needs-human

This is not a clean YES, NO, or composable-from-mathlib case:

- **Not NO-mathlib-has-it**: mathlib has neither Chebotarev, Dirichlet density,
  nor the completely-split-density corollary.
- **Not NO-composable-from-mathlib**: it cannot be reconstructed from mathlib —
  its inputs (`chebotarev_density`, `HasDirichletDensity`, `frobeniusClass`) are
  all project-local and absent upstream.
- **Not YES-add-as-is**: the statement is phrased entirely in project vocabulary
  and encodes "splits completely" as trivial Frobenius class; it cannot be added
  to mathlib without first upstreaming the Dirichlet-density + Frobenius-class +
  Chebotarev framework it depends on.
- **Not (yet) YES-but-generalise-first**: generality is already correct; the
  blocker is the absent upstream framework, not an assumption to weaken.

The right disposition is a **human decision tied to the parent development**: the
*entire* Chebotarev package (Dirichlet density → `chebotarev_density` →
this corollary) is a strong mathlib candidate as a unit, and once that lands,
`density_split_completely` should accompany it **restated mathlib-natively** (a
mathlib `Ideal` splits-completely predicate in the set-builder, rather than
`frobeniusClass = ConjClasses.mk 1`). As an isolated declaration, judged on its
own, it is a thin project-internal corollary that should not be PR'd standalone.
Hence **BORDERLINE-needs-human**.
