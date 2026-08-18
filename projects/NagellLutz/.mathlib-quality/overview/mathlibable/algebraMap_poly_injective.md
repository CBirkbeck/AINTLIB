# /mathlibable report — `WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:45`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source + repo mathlib tree at `.lake/packages/mathlib` (rev `09b373db6e24`, toolchain `v4.32.0-rc1`).
- decl `WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:45`.
- qualified name (VERIFIED from source): `WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective` — namespace `WeierstrassCurve.Affine.CoordinateRing` opened at line 38, `open Polynomial` at line 40, `variable {R} [CommRing R] {W' : WeierstrassCurve.Affine R}` at line 42, lemma at line 45.
- kind:                      lemma (theorem).
- has sorry:                 no.
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — explicitly "lemmas missing from the released mathlib that are needed for the division polynomial / ZSMul development". (This is a forked-from-mathlib supplement file.)

---

### Statement (Phase 1)

`algebraMap_poly_injective` states: for any commutative ring `R` and any Weierstrass curve
`W'` in affine coordinates over `R`, the algebra-structure map

$$ \operatorname{algebraMap} : R[X] \longrightarrow R[W'] = R[X][Y]/\langle p_{W'}\rangle $$

from the univariate polynomial ring `R[X]` into the **affine coordinate ring** `W'.CoordinateRing`
is **injective**. Here `p_{W'}` is the (monic, degree-2 in `Y`) Weierstrass polynomial
`Y² + a₁XY + a₃Y − (X³ + a₂X² + a₄X + a₆)`.

Mathematically: `R[W']` is a **free** `R[X]`-module with basis `{1, Y}` (the power basis of the
monic quadratic), so the constant inclusion `R[X] ↪ R[W']` (which sends `f ↦ f·1`) is injective —
the coefficient of the basis vector `1` cannot vanish for a nonzero `f`. No integral-domain
hypothesis is needed because the freeness comes from monicity, not from `R` being a domain.

Variables / typeclasses (Lean side):
- `{R : Type*}` with `[CommRing R]` — the base ring, **arbitrary commutative ring** (line 42).
- `{W' : WeierstrassCurve.Affine R}` — a Weierstrass curve in affine coordinates over `R`.

Hypotheses (Lean side): none beyond the typeclass `[CommRing R]`.

Conclusion (math): the inclusion `R[X] ↪ R[W']` is injective.

Conclusion (Lean): `Function.Injective (algebraMap R[X] W'.CoordinateRing)`.

Proof body (line 46–48):
```lean
(injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
  smul_basis_eq_zero (W' := W') (q := 0) <| by
    rwa [Algebra.smul_def, mul_one, zero_smul, add_zero]
```
i.e. it feeds `algebraMap p = p • 1 = p • 1 + 0 • Y = 0` to mathlib's
`smul_basis_eq_zero` (linear independence of the basis `![1, Y]`) and reads off `p = 0`.
Carries `set_option backward.isDefEq.respectTransparency false in` (line 44) — a transparency
guard for the elaboration of this specific proof; not a semantic part of the statement.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper injectivity lemma about an existing mathlib construction (`CoordinateRing`),
not a named theorem and not a new structure. (Literature width run EXHAUSTIVE regardless;
this is an infrastructure fact rather than a board-level theorem, so several literature
channels are legitimately `n/a`.)

### One-line check (Phase 2b)
Body line count: 3 substantive lines (a `.mpr` of `injective_iff_map_eq_zero` whose witness is a
non-trivial `smul_basis_eq_zero` application with a `rwa` normalisation).
One-liner verdict: **n/a — kind is lemma/theorem, not def.** (No defeq/diamond/API-name concerns;
this is a proof, not a sealed definition.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib WeierstrassCurve CoordinateRing algebraMap injective division polynomial"     | partial | mathlib EC docs (DivisionPolynomial, Weierstrass); no named injectivity lemma | confirms `R[W]` is the affine coordinate ring `R[X][Y]/⟨p⟩` |
|  2 | WebSearch (general form)         | "AdjoinRoot.of injective monic polynomial mathlib power basis free module base ring"   | yes | `AdjoinRoot.of.injective_of_degree_ne_zero` ([IsDomain]); `Polynomial.Monic.free_adjoinRoot`; `powerBasis'` | general route needs a DOMAIN; monic ⇒ free over any ring |
|  3 | WebSearch (named-after / aliases)| (subsumed in #1/#2) "coordinate ring elliptic curve free module {1, Y}"                | yes | Angdinata–Xu "Group Law on Weierstrass Curves" (arXiv 2302.10640) — the source of mathlib's `CoordinateRing` API | this lemma family (`smul_basis_eq_zero`, `map_injective`) originates there |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to WebSearch #2/#3 + direct mathlib source reading) | n/a | — | substituted by reading `AlgebraTower.lean`, `AdjoinRoot.lean`, `Basis/Basic.lean` directly |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                 | n/a | (no PDF refs found in that dir; overview/analysis notes reviewed instead) | overview already flags this decl "general — and mathlib-bound" |
|  6 | nLab                             | "coordinate ring of elliptic curve" / "free module over polynomial ring injection"     | n/a | — | not an nLab-style abstract concept; it is a concrete free-module injectivity fact |
|  7 | nCatLab (categorical)            | —                                                                                      | n/a | — | not a categorical statement |
|  8 | Stacks Project (alg geom)        | "coordinate ring" "free module" injection                                              | n/a | — | Stacks works scheme-theoretically; this affine-coordinate-ring injectivity is an algebra fact, not a Stacks tag |
|  9 | MathOverflow / Math.SE           | "is the base ring injecting into a finite free algebra" generality                     | yes (folklore) | a faithfully-flat / free module over `R` injects `R`; for a basis containing `1`, no domain needed | this is the maximally-general fact the Lean lemma instantiates |
| 10 | recent arXiv (≤5y)               | "elliptic curve coordinate ring formalization Lean"                                    | yes | arXiv 2302.10640 (Angdinata–Xu) | the formalization paper behind mathlib's `WeierstrassCurve.Affine.CoordinateRing` |

### Literature summary (Phase 3)

Concept identified as: **injectivity of the structural inclusion of the base ring into a free
finite algebra** — here `R[X] ↪ R[X][Y]/⟨monic Weierstrass poly⟩`. Folklore /
commutative-algebra-textbook fact; the Lean realization descends from Angdinata–Xu's
group-law formalization (arXiv 2302.10640), which is exactly the provenance of mathlib's
`WeierstrassCurve.Affine.CoordinateRing` API.

Sources agree on the standard form: yes — a module that is **free with a basis containing the
unit `1`** has the base ring inject into it; over an integral domain this is the standard
"torsion-free ⇒ faithful ⇒ `algebraMap` injective" chain.

Most general standard form: *Let `S` be an `R`-algebra that is free as an `R`-module with a basis
`b` such that some `b i₀ = 1` (equivalently `algebraMap r = r • b i₀`). Then `algebraMap R S` is
injective — for **any** commutative (semi)ring `R`, no domain needed.* The integral-domain
hypothesis appears in the textbook statement only because it is usually phrased through
torsion-freeness/faithful flatness.

Generality dimensions where the literature varies:
  - **base ring**: arbitrary `CommRing` (when the basis contains `1`) ⟶ `IsDomain` (when routed
    through torsion-free/faithful). The maximally-general form needs no domain.
  - **module structure**: "free with `1` in the basis" (this case) ⟶ "torsion-free" ⟶
    "faithfully flat". The lemma here sits at the cheapest, most elementary end (explicit basis).

Disagreement with the literature: none. The Lean form is the maximally-general (no-domain) form;
the literature's domain hypothesis is an artifact of the usual proof route, which this lemma
bypasses via the explicit basis.

---

### Generality analysis — `algebraMap_poly_injective`

Literature-standard form (from Phase 3): base ring injects into a free finite algebra whose basis
contains `1`; **no integral-domain hypothesis required**.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | arbitrary comm ring | arbitrary comm (semi)ring | marginally (CommSemiring) | the whole `CoordinateRing`/`AdjoinRoot` API is built on `CommRing`; semiring weakening is not meaningful here (quotient by an ideal needs a ring). Effectively MAXIMAL. |
| 2 | `W' : Affine R`        | a Weierstrass curve  | "monic quadratic / free quadratic extension" | the *concept* is narrower than "any monic poly" | but the lemma is intentionally about `CoordinateRing`; the general-poly version is `AdjoinRoot`+basis, see Phase 6. As a `CoordinateRing` lemma it is at the right grain. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for a lemma scoped to `WeierstrassCurve.Affine.CoordinateRing`).
Number of weakening opportunities found: 0 meaningful (CommSemiring is vacuous — quotient ring API needs `CommRing`).
Proposed restatement: none at the `CoordinateRing` scope.
Cost of restatement: n/a.

Crucially, the lemma is **strictly more general than the closest mathlib lemma**
`Module.Basis.algebraMap_injective`, which carries `[IsDomain R]` (see Phase 5/6). The project
form holds over **arbitrary** `CommRing R`. That extra generality is real and is *exercised* by
call sites (e.g. `HasseWeil/EC/MulByIntUnramified.lean` uses it over coordinate-ring bases that
are not assumed domains in that context).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | no | — | already typeclass-driven (`[CommRing R]`, bundled `Affine`). |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic; no topology. |
| 3 | construct an object where a universal-property class characterises it? | no | — | it is a property (injectivity), not a construction. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | vector-space/field-specific → module/(semi)ring weakening? | **yes (in the *mathlib* lemma, not this one)** | generalise mathlib's `Module.Basis.algebraMap_injective` to drop `[IsDomain]` when the basis contains `1` (or via `Basis.repr` injectivity directly) | this `algebraMap_poly_injective` becomes a one-line `(CoordinateRing.basis W').algebraMap_injective`; **and** every other "free algebra with 1 in the basis over a non-domain" gets injectivity for free. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | — | n/a. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it lives one level up, in mathlib's `Module.Basis` API, not in
this lemma.** The contemporary move is to *weaken mathlib's existing*
`Module.Basis.algebraMap_injective` (`RingTheory/AlgebraTower.lean:178`) to **drop `[IsDomain R]`**,
because `Basis.isTorsionFree` (`LinearAlgebra/Basis/Basic.lean:288`) already needs no domain, and
when `algebraMap r = r • (b i₀)` with `b i₀` a basis vector, injectivity follows from
`Basis.repr.injective` directly. Then:
  - Proposed mathlib-idiomatic restatement of the *project* lemma:
    ```lean
    -- after the mathlib generalisation, in Affine/Point.lean:
    lemma algebraMap_poly_injective : Function.Injective (algebraMap R[X] W'.CoordinateRing) :=
      (CoordinateRing.basis W').algebraMap_injective   -- ≤1 line
    ```
  - Cost: MODERATE (the *mathlib* generalisation of `Module.Basis.algebraMap_injective` is the work;
    once done, the EC lemma is one line).
  - Mathlib downstream this enables: any free finite algebra over a **non-domain** base with `1` in
    the basis gets `algebraMap` injectivity (quotient/adjoin-root constructions over `R[X]`,
    `ℤ/nℤ`-bases, product rings, etc.).
  - Real mathematical improvement: removes a spurious `IsDomain` hypothesis from a fundamental
    library lemma — genuine de-restriction, not cosmetic.

This modern-idiom observation does **not** by itself flip the verdict to NO, because the
generalised mathlib lemma **does not exist yet**; today, at `CommRing` generality, the result is
not available from mathlib (see Phase 6). It *does* shape the recommended pre-PR action.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is **lemma** (a `Prop`-valued proof). No definitional equalities,
no typeclass-search paths, no coercions introduced.

---

### Mathlib search-status: `algebraMap_poly_injective`

[A] Lean-Finder       (index unavailable offline)        n/a: substituted by direct mathlib-tree grep ([D]/[E]) + WebSearch.
[B] Loogle            `Function.Injective (algebraMap _[X] (WeierstrassCurve.Affine.CoordinateRing _))` ; `Basis _ _ _ → Function.Injective (algebraMap _ _)`  → general hit `Module.Basis.algebraMap_injective` (but `[IsDomain]`); no EC-specific hit.
[C] LeanSearch        "injectivity of algebraMap from polynomial ring into Weierstrass coordinate ring"  → no EC-specific hit; surfaces the basis/AdjoinRoot family.
[D] Grep mathlib src  `algebraMap_poly_injective` / `algebraMap_injective'` over whole tree  → **0 hits** (not in mathlib). `CoordinateRing.*inject*` → **0 hits**.
[E] Name pattern      grep `AlgebraicGeometry/EllipticCurve/Affine/Point.lean` for injectivity  → mathlib HAS `map_injective` (line 186, the `R[W]→S[W']` map), `smul_basis_eq_zero` (144), `exists_smul_basis_eq` (150) — but **NOT** `algebraMap`-from-`R[X]` injectivity.

Searched for both:
  - the user's current form `Function.Injective (algebraMap R[X] W'.CoordinateRing)` — **not in mathlib**.
  - the literature-standard general form (basis ⇒ `algebraMap` injective) — mathlib has
    `Module.Basis.algebraMap_injective` (`RingTheory/AlgebraTower.lean:178`) **but only under
    `[IsDomain R]`** (section header line 176: `[CommRing R] [IsDomain R] [Ring S] [Nontrivial S]`).
    Also `AdjoinRoot.of.injective_of_degree_ne_zero` (`AdjoinRoot.lean:265`) — also `[IsDomain R]`.
    `AdjoinRoot.coe_injective` / `coe_injective'` (538/542) — require a **field** `K`.

Concluded: **not in mathlib at the stated generality.** The exact EC lemma is absent; the closest
general mathlib lemma (`Module.Basis.algebraMap_injective`) is **strictly narrower** (needs
`[IsDomain R]`, i.e. `R[X]` a domain, i.e. `R` a domain), so it does not yield the project's
arbitrary-`CommRing` statement. Mathlib also already hosts the sibling lemmas of this exact API
family (`smul_basis_eq_zero`, `map_injective`) in `Affine/Point.lean` — the natural home.

---

### Call sites — `algebraMap_poly_injective`

Internal use count (NagellLutz project, excluding declaring file): the lemma's primary *live*
consumers are in the **HasseWeil** project (same monorepo), where the same `Universal.lean`
supplement is forked. Counting across the workspace:

External-to-file callers: **≥10 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/Universal.lean:51` | `(CoordinateRing.algebraMap_poly_injective (W' := W')).comp C_injective` (defines `algebraMap_injective'`) |
| `HasseWeil/HasseWeil/Basic.lean:256, 274` | `Affine.CoordinateRing.algebraMap_poly_injective` |
| `HasseWeil/HasseWeil/FrobeniusIsogeny.lean:120, 137` | idem |
| `HasseWeil/HasseWeil/MulByIntPullback.lean:310` | `(IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective` |
| `HasseWeil/HasseWeil/OmegaPullbackCoeff.lean:185, 714, 793` | idem (composed with `IsFractionRing.injective`) |
| `HasseWeil/HasseWeil/OrdAtInftyBridge.lean:188` | `Affine.CoordinateRing.algebraMap_poly_injective` |
| `HasseWeil/HasseWeil/EC/MulByIntUnramified.lean:197, 542` | `... hq (Affine.CoordinateRing.algebraMap_poly_injective (h.trans (map_zero _).symm))` |
| `HasseWeil/HasseWeil/EC/WronskianGeneral.lean:65` | `(IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective` |
| `HasseWeil/HasseWeil/Verschiebung/{Genuine,QthRoots}.lean` | `Affine.CoordinateRing.algebraMap_poly_injective` |
| `HasseWeil/HasseWeil/Curves/FiniteOverKx.lean:65, 92, 155` | `apply Affine.CoordinateRing.algebraMap_poly_injective (W' := C.toAffine)` |

Inline-derivation grep: (none found re-deriving it without the lemma — consumers uniformly call the
named lemma, often `.comp`-ed with `IsFractionRing.injective` / `C_injective`).

Composability signal: **K ≥ 3 external callers, no inline re-derivation ⇒ real, load-bearing API.**
Leaning: YES-* bucket. (The decl is duplicated across two projects' `Universal.lean` files — a
classic "this should be upstream so both projects import it from one place" signal.)

---

### Composition check (Phase 6)

Can `algebraMap_poly_injective` be derived from **current** mathlib in ≤3 chained calls, **at its
stated `CommRing` generality**?

Attempt 1: `(CoordinateRing.basis W').algebraMap_injective`
  - Mathlib decls used: `WeierstrassCurve.Affine.CoordinateRing.basis` (mathlib `Affine/Point.lean:117`),
    `Module.Basis.algebraMap_injective` (`AlgebraTower.lean:178`).
  - Result: **fails** at the stated generality. `Module.Basis.algebraMap_injective` requires
    `[IsDomain R]` (where `R` here = `R[X]`, the basis's base ring). The project lemma has only
    `[CommRing R]`. Under an added `[IsDomain R]` it would succeed — but that is a strictly stronger
    hypothesis than the project (and the call sites) use.

Attempt 2: route through `smul_basis_eq_zero` (`Affine/Point.lean:144`) with `q := 0`.
  - This is **exactly the project's proof**, and it works over any `CommRing` — but
    `smul_basis_eq_zero` is itself a (mathlib) lemma about the *specific* `CoordinateRing` basis,
    and the wrapper is precisely the new named lemma. It is not a generic ≤3-call mathlib
    composition that one would inline at 10+ call sites; it is the API lemma those sites depend on.

Attempt 3: `AdjoinRoot.of.injective_of_degree_ne_zero` / `AdjoinRoot.coe_injective`.
  - Both require `[IsDomain R]` (or a field). Same generality failure as Attempt 1.

Conclusion: **NOT-COMPOSABLE** at the stated `[CommRing R]` generality from *current* mathlib.
(The result is only ≤1-line-composable *after* either (a) adding `[IsDomain R]` — which narrows it
and breaks call sites, or (b) generalising `Module.Basis.algebraMap_injective` to drop `[IsDomain]`
— which is itself a mathlib contribution that does not yet exist.)

---

## Verdict: `WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): standard free-algebra-injectivity fact; maximally-general (no-domain)
  form matches the Lean statement; provenance = Angdinata–Xu (arXiv 2302.10640), the same paper
  behind mathlib's `CoordinateRing` API.
- Generality analysis (Phase 4): MAXIMALLY GENERAL at the `CoordinateRing` scope; **strictly more
  general than** the nearest mathlib lemma (`Module.Basis.algebraMap_injective`, which needs `[IsDomain]`).
- Mathlib search (Phase 5): **not in mathlib**; siblings `smul_basis_eq_zero`, `map_injective`,
  `exists_smul_basis_eq` already live in `Affine/Point.lean` (the home this lemma belongs in).
- Composition check (Phase 6): **NOT-COMPOSABLE** at `[CommRing R]` from current mathlib.

**Rationale:**

Mathlib's `WeierstrassCurve.Affine.CoordinateRing` API in `Affine/Point.lean` already contains the
entire neighbourhood of this lemma — the free power basis `CoordinateRing.basis W' : Basis (Fin 2)
R[X] _`, its linear-independence corollary `smul_basis_eq_zero`, the spanning corollary
`exists_smul_basis_eq`, and the *induced-map* injectivity `map_injective` (for `R[W]→S[W']`) — all
stated over arbitrary `[CommRing R]` and all proved by the same one-or-two-line pattern this lemma
uses. The one obviously-missing member of that family is injectivity of the **base inclusion**
`algebraMap R[X] → R[W]`. The general basis lemma `Module.Basis.algebraMap_injective` exists but is
gated by `[IsDomain R]`, so it cannot supply the arbitrary-`CommRing` statement that this lemma and
its 10+ call sites actually require (e.g. coordinate rings over non-domain base rings in the
HasseWeil mul-by-`n` / Verschiebung developments). The lemma is therefore neither in mathlib nor
composable from it at the needed generality; it fills a concrete, named gap directly adjacent to
existing API, and it is heavily reused across two projects of the monorepo — the textbook profile
of a result that should be upstreamed.

**WHY add it (refactor-actionable):**
- *New content / the specific gap.* `Affine/Point.lean` has `map_injective` (the functorial map
  `R[W]→S[W']`) and the basis machinery, but **no** lemma that `algebraMap R[X] ↪ R[W]` is
  injective. That is a genuine hole: the base-ring inclusion is the most basic injectivity one
  wants about a coordinate ring, and downstream "transcendence of `X` in `R[W]`" arguments
  (WronskianGeneral, MulByIntUnramified, OrdAtInftyBridge) all route through it. It cannot be
  obtained from `Module.Basis.algebraMap_injective` because that lemma's `[IsDomain R]` is exactly
  the hypothesis these uses want to avoid.
- *How it composes.* Once present, it `.comp`s cleanly with `C_injective` (giving
  `algebraMap R → R[W]` injective, the project's `algebraMap_injective'`) and with
  `IsFractionRing.injective` (giving injectivity into the fraction field, used ~6× in HasseWeil) —
  precisely the compositions the call sites already perform by hand.

Proposed mathlib location:   `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
  (immediately after `smul_basis_eq_zero` / `exists_smul_basis_eq`, before/near `map_injective`).
Proposed PR title:           `feat(AlgebraicGeometry/EllipticCurve): add CoordinateRing.algebraMap_poly_injective (and algebraMap_injective')`
PR grouping:                 ship together with the sibling one-liner
  `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'`
  (`= algebraMap_poly_injective.comp C_injective`, also in this `Universal.lean`) as **one** PR —
  they are the missing base-inclusion injectivity pair for the existing `Point.lean` API.

Pre-PR checklist before opening:
  - [ ] Run `/generalise WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective` — and
        in particular evaluate the **stronger** upstream move surfaced in Phase 4c: generalise
        mathlib's `Module.Basis.algebraMap_injective` to **drop `[IsDomain R]`** (it routes through
        `Basis.isTorsionFree`, which needs no domain; the missing step is "torsion-free + `1` in the
        basis ⇒ `algebraMap` injective over any `CommRing`"). If that generalisation lands, the EC
        lemma collapses to `(CoordinateRing.basis W').algebraMap_injective` and the PR should add it
        in that one-line form. If the reviewer prefers to keep the basis lemma domain-gated, add the
        EC lemma with its current `smul_basis_eq_zero` proof. **Either way the EC lemma is wanted;**
        the choice is only about which proof line it carries.
  - [ ] Run `/cleanup` on the lemma (it carries `set_option backward.isDefEq.respectTransparency
        false in` — confirm that guard is still needed under current mathlib elaboration, or drop it).
  - [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/` history
        (the `CoordinateRing` API authors — Angdinata / Xu).

**Note on the one borderline edge.** A reasonable reviewer could argue the *cleanest* mathlib
contribution is the general no-domain `Module.Basis.algebraMap_injective` generalisation, after
which this EC lemma is a one-liner and arguably "NO-composable". I did not pick that verdict because
(i) that generalisation does **not exist in mathlib today**, so right now the result is genuinely
unavailable at `[CommRing R]`; and (ii) even after it lands, the EC-named lemma is still a wanted
convenience sitting next to its already-present siblings (`smul_basis_eq_zero`, `map_injective`),
with 10+ consumers. The generalisation is captured as the first pre-PR checklist item, which is the
right place for it.

---

## Next step

Run `/generalise WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective` to settle whether
to (a) upstream-generalise mathlib's `Module.Basis.algebraMap_injective` to drop `[IsDomain]` (then
add the EC lemma as a one-liner) or (b) add the EC lemma with its current `smul_basis_eq_zero` proof;
then open one `feat(AlgebraicGeometry/EllipticCurve)` PR adding `algebraMap_poly_injective` together
with `algebraMap_injective'` to `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, after
`/cleanup` on the pair.
