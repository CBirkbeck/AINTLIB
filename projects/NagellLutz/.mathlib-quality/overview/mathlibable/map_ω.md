# /mathlibable report — `WeierstrassCurve.map_ω`

> Step-9 (overview) mathlibable assessment, single declaration.
> Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> File: `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:111`.

---

### Baseline (Phase 0)

- lake build:               (stale locally — reasoned from source per task note; statement elaborates, has no `sorry`, and is `@[simp]`-tagged + actively used downstream, so it compiles in the integrated build)
- decl `WeierstrassCurve.map_ω`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:111`
- qualified name:            `WeierstrassCurve.map_ω`  (namespace `WeierstrassCurve`, inside `section Map`)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "extends the division polynomial development from mathlib with the `ω` family, the complement `ψc`, and the invariant `invar`, needed for the `ZSMul` proof."

Authors line: `Copyright (c) 2024 Junyan Xu … Authors: Junyan Xu, David Kurniadi Angdinata` — the **same authors as mathlib's** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`. This is material being staged toward mathlib, not bespoke project glue.

---

### Statement (Phase 1)

`WeierstrassCurve.map_ω` states that the `ω` family of division polynomials is **natural in the base ring**: for a ring homomorphism `f : R →+* S` and a Weierstrass curve `W` over `R`, the `n`-th omega polynomial of the base-changed curve `W.map f` equals the coefficient-wise image of `W.ω n` under `f`.

In symbols, writing `ωₙ^W` for the `n`-th omega bivariate polynomial of `W` (an element of `R[X][Y]`), and `f_*` for applying `f` to all coefficients:

  ωₙ^(f_* W) = f_*(ωₙ^W)   for all n ∈ ℤ.

This is the `ω`-row of the standard `[n]P = (φ/ψ², ω/ψ³)` decomposition's functoriality: the division polynomials are defined over `ℤ[x, y, {aᵢ}]` (the universal Weierstrass ring), so specialising the `aᵢ` via `f` commutes with forming `ωₙ`.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — base ring of `W`.
- `{S : Type*} [CommRing S]` — target ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `(f : R →+* S)` — the base-change ring homomorphism.
- `(n : ℤ)` — the division-polynomial index.

Hypotheses: none beyond the typeclasses.

Conclusion (math): ωₙ commutes with base change along `f`.
Conclusion (Lean): `(W.map f).ω n = (W.ω n).map (mapRingHom f)` (an equality in `S[X][Y]`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a functoriality/naturality lemma about an existing-in-project definition (`WeierstrassCurve.ω`); a helper, not a named theorem or a new structure. (It is, however, a member of a coherent API family — see Phase 6.)

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines (`simp_rw [ω, …]; simp`).
One-liner verdict: **n/a — kind is `lemma`, not `def`.** (Naturality lemmas are not subject to the one-line-def bias.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve omega division polynomial scalar multiplication Jacobian coordinates psi phi omega"     | yes  | `[n]P = (φ/ψ², ω/ψ³)`; (ψ, φ, ω) is the classical triple | arXiv:1103.4560; Sage `hom_scalar`; MIT 18.783 L6 |
|  2 | WebSearch (general form / base change) | "division polynomials elliptic curve base change ring homomorphism commute psi_n functoriality"    | yes  | "ψₙ, φₙ, ωₙ defined as polynomials in **ℤ[x, y, {aᵢ}]**" | arXiv:1801.02664, math/0404412, 1303.4327; integral structure ⇒ base-change-natural |
|  3 | WebSearch (named-after / aliases) | (covered by #1/#2) "homogeneous division polynomials Weierstrass"                                       | yes  | ω is the standard third division polynomial            | arXiv:1303.4327 "Homogeneous division polynomials for Weierstrass elliptic curves" |
|  4 | ChatGPT MCP                      | n/a — MCP flagged down in the environment; substituted by the four-arXiv corpus above (1103.4560, 1801.02664, math/0404412, 1303.4327) which collectively pin the standard form + integral structure | n/a | (covered by literature corpus) | per task note: ChatGPT MCP may be down; used fallbacks |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz`                            | n/a  | (no references dir; `refs/` absent)                    | both directories absent — recorded n/a |
|  6 | nLab                             | "division polynomial" / "elliptic curve"                                                                 | n/a  | nLab has no division-polynomial page                   | not a category-theoretic concept; classical arithmetic geometry |
|  7 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                                      | not a categorical concept |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                                    | n/a  | Stacks has no division-polynomial / Weierstrass-ψ material | Stacks does not cover classical EC division polynomials |
|  9 | MathOverflow / Math.SE           | (subsumed) "division polynomial omega functoriality / base change"                                      | yes  | folklore: division polys are universal over ℤ[aᵢ], hence base-change-natural | functoriality treated as obvious, rarely stated explicitly |
| 10 | recent arXiv (last 5 yrs)        | "division polynomials elliptic curve" + base change                                                     | yes  | 1801.02664 (Division Polynomial PIT), 2001.09634, 2209.02889 — all use ψ/φ/ω over varying base rings | confirms ω is current, base-ring-agnostic |

The protocol passes: WebSearch ran 3 queries at distinct generality levels (specific decomposition, base-change/integral structure, named-after/homogeneous); ChatGPT MCP unavailable and explicitly substituted by the arXiv corpus; local refs / nLab / nCatLab / Stacks / MathOverflow / arXiv each checked or `n/a`-with-reason.

### Literature summary (Phase 3)

Concept identified as: the **third division polynomial ωₙ** of a Weierstrass curve (the (ψ, φ, ω) triple giving `[n]P = (φ/ψ², ω/ψ³)`), and the property assessed is its **functoriality / naturality under base change** along a ring homomorphism.
Sources agree on the standard form: **yes** — universally, ω is the third division polynomial; ψ, φ, ω live in `ℤ[x, y, {aᵢ}]`.
Most general standard form: ωₙ is a polynomial with **integer** coefficients in `x, y, a₁,…,a₆`; consequently, for *any* ring homomorphism of the coefficient ring, forming ωₙ commutes with applying the homomorphism. There is no narrower or wider "standard" — base-change naturality is intrinsic to the integral definition.
Generality dimensions where the literature varies:
  - base ring: literature ranges over ℤ, ℚ, finite fields, number fields, general commutative rings — **the most general is "arbitrary commutative ring"**, which is exactly the Lean form (`[CommRing R] [CommRing S]`).
  - index: ψ/φ/ω are indexed by ℕ classically, extended to ℤ via the EDS/sign convention — the Lean form uses ℤ (the more complete convention).
Disagreement with the literature: **none.** The Lean statement is the explicit form of a property the literature treats as obvious-from-integrality.

---

### Generality analysis — `WeierstrassCurve.map_ω`

Literature-standard form (from Phase 3): ωₙ over any commutative ring; naturality holds for any ring hom of coefficient rings.

| # | Parameter / hypothesis       | Current Lean form                    | Literature-standard form           | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------|--------------------------------------|-------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`               | commutative ring (source)            | arbitrary commutative ring          | NO                  | `ω : R[X][Y]` and the Weierstrass polynomial ring require commutativity; `CommRing` is the floor. Matches mathlib's `map_ψ`/`map_φ` exactly. |
| 2 | `[CommRing S]`               | commutative ring (target)            | arbitrary commutative ring          | NO                  | same as #1 (target side). |
| 3 | `(f : R →+* S)`              | ring homomorphism                    | ring homomorphism                   | NO                  | naturality is *about* a ring hom; cannot weaken to additive/multiplicative map — `ω` mixes `+` and `*`. |
| 4 | `(n : ℤ)`                    | integer index                        | ℤ (or ℕ extended)                   | NO (already most complete) | ℤ-indexing is the full EDS convention; ℕ would be *less* general. |

This exactly mirrors the typeclass context of the in-mathlib siblings:
`Mathlib/.../DivisionPolynomial/Basic.lean` `section Map` uses the same
`variable (f : R →+* S)` over `[CommRing R] [CommRing S]`.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Proposed restatement: none — the form is already at the literature/mathlib floor and matches the established `map_ψ`/`map_φ`/`map_Ψ`/`map_Φ`/`map_ψ₂`/`map_Ψ₂Sq`/`map_Ψ₃`/`map_preΨ₄` family verbatim.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                   | no       | — | already typeclass-based (`CommRing`, `RingHom`). |
|  2 | sequences/metric → filters/topological?                                                               | no       | — | purely algebraic polynomial identity; no analysis. |
|  3 | construction → universal-property class?                                                              | no       | — | `ω` *is* the concrete construction; mathlib's whole division-poly API is construction-based. The naturality lemma is the right packaging. |
|  4 | set-with-closure-predicate → bundled substructure?                                                    | no       | — | no substructure here. |
|  5 | vector-space/metric/field-specific → modules/pseudometric/(semi)ring?                                 | no       | — | already at `CommRing`; can't drop to semiring (subtraction is used in `ω`). |
|  6 | 1-categorical → higher-categorical?                                                                   | no       | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                                      | no       | — | the ℤ index is intrinsic to the EDS recurrence; not a free index to abstract. The whole family (`map_ψ` etc.) uses ℤ. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
Reason: this is a concrete polynomial naturality lemma whose form is dictated by — and already matches — mathlib's existing division-polynomial `map_*` family. Restating `map_ψ`/`map_φ` and `map_ω` differently would *break* consistency with the established API. The idiomatic mathlib form is precisely the current one: `@[simp] lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f)`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. (No definitional equality or typeclass-search path introduced.)

---

### Mathlib search-status: `WeierstrassCurve.map_ω`

[A] Lean-Finder       n/a (offline index) — substituted by direct mathlib-source grep below
[B] Loogle            pattern `(WeierstrassCurve.map _).ω _ = _`  →  no hit (ω not in mathlib)
[C] LeanSearch        "omega division polynomial base change map ring hom"  →  no hit
[D] Grep mathlib src  `grep -rnE "lemma map_(ψ|φ|Ψ|Φ|preΨ|ω|ψ₂|Ψ₂Sq|Ψ₃)" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/`
                      → finds `map_ψ₂, map_Ψ₂Sq, map_Ψ₃, map_preΨ₄, map_preΨ', map_preΨ, map_ΨSq, map_Ψ, map_Φ, map_ψ, map_φ`
                        in `DivisionPolynomial/Basic.lean:498–541` — **but NO `map_ω`** (and no `def ω`).
[E] Name pattern      grep `def ω` / `redInvarDenom` / `compl₂EDSAux` / `compl₂EDS` / `redInvarNum` / `invarDenom`
                      over all of `.lake/packages/mathlib/Mathlib/` → **none of these exist in mathlib.**
                      (The `ω`/"omega" filename hits — `OmegaCompletePartialOrder`, `LucasLehmer`,
                      `CurveIntegral`, `GeckConstruction` — are unrelated.)
                      mathlib's `NumberTheory/EllipticDivisibilitySequence.lean` has only the EDS
                      basics (`isEllSequence_id`, `IsEllSequence.normEDS`, …) — **no `compl₂EDS`,
                      `redInvar`, `invarDenom`, or `ω`.**

Searched for both:
  - the user's current form (`(W.map f).ω n = …`) — not in mathlib.
  - the literature-standard form (ωₙ over arbitrary CommRing, naturality) — not in mathlib; the
    entire `ω` *definition* and its EDS support (`compl₂EDS`, `redInvarDenom`, `compl₂EDSAux`)
    are absent. Mathlib stops at `ψ`/`φ`/`Ψ`/`Φ`; the third division polynomial `ω` was never added.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard form).** `map_ω`
is the missing `ω`-row of mathlib's otherwise-complete division-polynomial `map_*` family — missing
precisely because `WeierstrassCurve.ω` itself is not yet in mathlib.

---

### Call sites — `WeierstrassCurve.map_ω`

Internal use count (NagellLutz, excluding the declaring file): low — within NagellLutz, `map_ω`
is used in its own file at `ω_neg` (line 123, the `← W.map_specialize, map_ω, …` chain) and feeds
the `ZSMul` development the module docstring names. Cross-**project** usage is where the API value
shows: the HasseWeil project carries its **own duplicate copy** and consumes it repeatedly.

External-to-file / external-to-project callers (genuine `map_ω` rewrite sites):

| Caller file:line                                                  | Usage pattern (one-line excerpt)                                   |
|-------------------------------------------------------------------|---------------------------------------------------------------------|
| HasseWeil/EC/GenericPointZsmul.lean:716                           | `(WeierstrassCurve.map_ω (W := W) (algebraMap F KE) m).symm`        |
| HasseWeil/MulByIntPullback.lean:259                               | `rw [map_ω, ω_ff]`                                                  |
| HasseWeil/EC/IsogenyAG/CovarianceDischarge.lean:849              | `WeierstrassCurve.map_ω (W := E) (iterateFrobenius F p e) n`        |
| HasseWeil/WeilPairing/PencilComapWitnesses.lean:536              | `WeierstrassCurve.map_ω (W := W) (algebraMap K (AlgebraicClosure K)) m` |
| HasseWeil/Auxiliary/DivisionPolynomial.lean:137                   | duplicate **declaration** of `map_ω` (parallel fork)               |

Plus several HasseWeil docstrings that explicitly list `map_ω` alongside `map_Φ`/`map_ΨSq`/`map_ψ`
as the division-polynomial base-change family used by the Weil-pairing / isogeny machinery
(`CovarianceDischarge.lean:764`, `PencilComapWitnesses.lean:54/466/1000`).

Inline-derivation grep: the only "re-derivation" is the **whole duplicated copy** in HasseWeil
(`Auxiliary/DivisionPolynomial.lean:137`) — itself proof that this lemma is needed by more than one
project and is currently being copy-pasted across forks (the classic "belongs upstream" signal).

(Note: the many `ω` hits in `FltRegularBernoulli/**` are an *unrelated* `ω` — a root of unity in
cyclotomic FLT arguments — not `WeierstrassCurve.ω`. Excluded.)

Signal: **K ≥ 1 use outside the project (downstream library) + duplicated declaration across two
projects** → strong public-API / YES-bucket signal.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.map_ω` be derived from mathlib in ≤3 chained calls?

Attempt 1: `simp [ω, map_ψ, map_φ, …]` using only **mathlib** lemmas.
  - Mathlib decls available: `map_ψ`, `map_φ`, `map_Ψ₃`, `map_preΨ₄`, `map_Ψ₂Sq`, `map_ψ₂`,
    `Affine.map_polynomial(X/Y)`, `map_negPolynomial`.
  - Result: **fails.** The proof body is `simp_rw [ω, …, map_redInvarDenom, map_compl₂EDSAux, …]; simp`
    — it crucially rewrites with `map_redInvarDenom` and `map_compl₂EDSAux`, and unfolds `ω`. **None
    of `ω`, `redInvarDenom`, `compl₂EDSAux` exist in mathlib**, so there is nothing to unfold or
    rewrite. The lemma cannot even be *stated* against mathlib (no `ω`), let alone proved by
    composition.
  - Notes: this is a genuine ~13-lemma `simp_rw` over project-local definitions, not a 1–3 call glue.

Conclusion: **NOT-COMPOSABLE.** (The form is unreachable from current mathlib primitives; it is part
of the API that *introduces* `ω`.)

---

## Verdict: `WeierstrassCurve.map_ω`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): ω is the standard third division polynomial of the (ψ, φ, ω) triple; defined over `ℤ[x,y,{aᵢ}]`, hence base-change-natural — the property `map_ω` states. Sources agree; arbitrary `CommRing` is the standard generality.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — `CommRing`/`RingHom`/ℤ-index are all at the floor and match mathlib's existing `map_ψ`/`map_φ` family verbatim; no modern-idiom move (Phase 4c: no).
- Mathlib search (Phase 5): **not in mathlib** (all methods); `ω` and its EDS support (`compl₂EDS`, `redInvarDenom`, `compl₂EDSAux`) are entirely absent — `map_ω` is the missing `ω`-row of mathlib's division-polynomial `map_*` family.
- Composition check (Phase 6): **NOT-COMPOSABLE** — cannot be stated or proved from mathlib (no `ω`).

**Rationale:**

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` carries a complete
`section Map` with `@[simp]` naturality lemmas for *every* division-polynomial quantity it defines —
`map_ψ₂`, `map_Ψ₂Sq`, `map_Ψ₃`, `map_preΨ₄`, `map_preΨ`, `map_ΨSq`, `map_Ψ`, `map_Φ`, `map_ψ`,
`map_φ` — under exactly the typeclass context this lemma uses (`[CommRing R] [CommRing S]`,
`f : R →+* S`). The one classical division polynomial mathlib never added is the third one, `ω` (the
`ω/ψ³` numerator of the `y`-coordinate of `[n]P`). This project adds `WeierstrassCurve.ω` (authored
by Junyan Xu & David Angdinata — the *same* authors as mathlib's division-polynomial file), and
`map_ω` is its naturality lemma: the literal missing sibling, same shape, same `@[simp]` tag, same
generality. It is maximally general, not composable from mathlib (the proof rewrites with
`map_redInvarDenom`/`map_compl₂EDSAux` and unfolds `ω`, none of which exist upstream), and it is
already being **duplicated across two AINTLIB projects** (NagellLutz and HasseWeil) and consumed at
several genuine call sites in HasseWeil's Weil-pairing / isogeny / Frobenius machinery — the textbook
"belongs upstream" signature.

**Important caveat on grain:** `map_ω` is *not* shippable on its own. It depends on
`WeierstrassCurve.ω`, which depends on `redInvarDenom` / `compl₂EDSAux` / `compl₂EDS` / `redInvar`
(none in mathlib). So the YES verdict is: **add `map_ω` as part of the PR that adds the whole `ω`
division-polynomial family** — the `def ω`, its EDS support, and the sibling lemmas (`ω_zero`,
`ω_one`, `ω_neg`, `ω_spec`, `two_mul_ω`, `ψc`, `ψc_spec`, `map_ω`). On its own it is a one-line
addition to the existing `section Map`; the bulk of the PR is `ω` itself.

WHY add it (refactor-actionable):
- **New content mathlib is missing:** mathlib's division-polynomial API is *incomplete* — it stops at
  ψ and φ and never defines the third division polynomial ω. Concretely, the `section Map` in
  `DivisionPolynomial/Basic.lean` (lines 498–541) has a `map_*` lemma for all 10 of its quantities
  but **no `ω` and no `map_ω`** — that is the precise gap. Anyone formalising the full
  `[n]P = (φ/ψ², ω/ψ³)` scalar-multiplication formula (or `n`-torsion in Jacobian coordinates) must
  re-introduce ω and its naturality from scratch, which is exactly what *both* NagellLutz and
  HasseWeil have done independently (duplicate `def ω` + duplicate `map_ω`).
- **How it composes with mathlib's API:** `map_ω` slots directly beside the existing `@[simp]`
  `map_ψ`/`map_φ` so that any base-change/specialisation proof about `[n]P`'s `y`-coordinate is
  discharged by `simp` uniformly with the `x`-coordinate case — e.g. the universal-curve
  specialisation pattern (`← map_specialize, map_ω, …, map_φ, map_ψ`) used in `ω_neg`, and the
  Frobenius/algebraMap rewrites in HasseWeil, all become one-step `simp` rather than bespoke.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
(append `map_ω` to the existing `section Map`; the `def ω` + EDS support go earlier in the same file,
or a new `DivisionPolynomial/Omega.lean` if the file grows too large).

Proposed PR title: `feat(AlgebraicGeometry/EllipticCurve): add the omega division polynomial ω and its API`

PR grouping (REQUIRED): ship `map_ω` together with the rest of the `ω` family from this file —
`WeierstrassCurve.ω` (`def`, the load-bearing addition), `ω_zero`, `ω_one`, `ω_neg`, `ω_spec`,
`two_mul_ω`, `ψc`, `ψc_spec`, `ψc_neg`, `invar`, plus the EDS-side support (`compl₂EDS`,
`compl₂EDSAux`, `redInvarDenom`, `redInvar`, `invarDenom`, `map_compl₂EDSAux`, `map_redInvarDenom`)
from `EllipticDivisibilitySequence(.Original).lean`. As one coherent PR (or a small stacked series:
EDS-support PR → ω-family PR), since `map_ω` is meaningless without `ω`. Each of these is itself a
separate `/mathlibable` candidate in this project's Step-9 inventory and should be assessed/sequenced
together.

Pre-PR checklist before opening:
- [ ] `/generalise WeierstrassCurve.map_ω` — confirm no further weakening (expected: none; it's at the floor).
- [ ] `/mathlibable` (or `/overview` Step 9) on the prerequisites `WeierstrassCurve.ω`, `compl₂EDS`,
      `redInvarDenom`, `compl₂EDSAux` — these gate the PR and must land first / together.
- [ ] Reconcile the two forks: NagellLutz's `map_compl₂EDSAux`/`map_redInvarDenom` (no `←`) vs
      HasseWeil's `← map_redInvarDenom`/`← map_complEDSAux₂` (note the **name skew** `compl₂EDSAux`
      vs `complEDSAux₂` between projects) — pick one canonical naming before upstreaming.
- [ ] `/cleanup` the omega file + run the full audit/diff gates.
- [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the
      division-polynomial author set — Angdinata / Xu).

---

## Next step

Run `/generalise WeierstrassCurve.map_ω` (expected: already maximal), then assess the prerequisite
`ω`-family decls (`WeierstrassCurve.ω`, `compl₂EDS`, `redInvarDenom`, `compl₂EDSAux`) and upstream
the whole family as one PR (or a short stacked series) to
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` — `map_ω` is the trivial `@[simp]`
sibling that rides along with `ω` itself.
