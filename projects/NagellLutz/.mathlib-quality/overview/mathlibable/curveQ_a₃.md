# /mathlibable report — `LutzNagell.LutzNagellTheorem.curveQ_a₃`

> Step-9 (overview) mathlibable assessment, single declaration, NagellLutz project.
> Verdict: **NO-mathlib-has-it**.

Mathlib already has this lemma as `WeierstrassCurve.map_a₃` (the `@[simps]`-generated
`@[simp]` projection lemma for `WeierstrassCurve.map`). The project lemma is the
`f := algebraMap ℤ ℚ` specialisation and follows in ≤1 line.

---

## Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source + the mathlib pin in `.lake/packages/mathlib`)
- decl `curveQ_a₃`:         resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:29`
- qualified name (VERIFIED): `LutzNagell.LutzNagellTheorem.curveQ_a₃`
  (file opens `namespace LutzNagell` then `namespace LutzNagellTheorem`; parsed name confirmed correct)
- kind:                     lemma (carries `@[simp]`)
- has sorry:                no
- module docstring summary: "General Weierstrass model for the generalized Lutz-Nagell theorem" — sets up `W : WeierstrassCurve ℤ` and its base change to ℚ, plus rewriting lemmas for equation/coefficients. Forks/duplicates parts of mathlib's EllipticCurve machinery for the generalized Lutz–Nagell track.

Exact source:
```lean
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ := W.map (algebraMap ℤ ℚ)

@[simp] lemma curveQ_a₃ : (curveQ W).a₃ = (W.a₃ : ℚ) := by simp [curveQ]
```

---

## Statement (Phase 1)

`curveQ_a₃` states that the `a₃` Weierstrass coefficient of the base change of an
integral Weierstrass curve `W` to ℚ equals the rational image of `W.a₃`. Here
`curveQ W := W.map (algebraMap ℤ ℚ)` (an `abbrev`, line 24), so the claim is purely the
functoriality of the `a₃` coordinate projection under the ring map `ℤ →+* ℚ`.

Lean parameters:
- `W : WeierstrassCurve ℤ` — an integral Weierstrass curve.

Hypotheses: none.

Conclusion (math): `(W_ℚ).a₃ = a₃(W)` viewed in ℚ, where `W_ℚ` is the base change of `W`.
Conclusion (Lean): `(curveQ W).a₃ = (W.a₃ : ℚ)`, i.e. `(W.map (algebraMap ℤ ℚ)).a₃ = ((W.a₃ : ℤ) : ℚ)`.

---

## Size classification (Phase 2a)

Verdict: SMALL
Reason: a coefficient-rewriting glue lemma — a specialisation of mathlib's base-change
projection to a fixed ring map. Not a named theorem, not a new structure, not a project
main result.
(Literature width is EXHAUSTIVE regardless; SMALL is recorded only for framing.)

## One-line check (Phase 2b)

Body: `by simp [curveQ]` — a one-line proof.
One-liner verdict: n/a — kind is `lemma` (Phase 2b gates `def`/`abbrev`/`structure`, not
lemmas). Recorded as: trivial one-line proof, no def-oriented exemption applicable.

(Note the sibling `abbrev curveQ` on line 24 — `W.map (algebraMap ℤ ℚ)` — is itself a
one-liner; it is a thin project alias for `WeierstrassCurve.baseChange`. That def is out
of scope for this decl's assessment and is covered by its own overview row, `curveQ.md`.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "base change Weierstrass curve coefficients ring homomorphism functoriality a_i"      | yes  | `W.map φ` sends `aᵢ ↦ φ(aᵢ)` | Top hit is the mathlib doc itself, stating `W.map φ = {a₁ := φ a₁, …, a₆ := φ a₆}` — i.e. this *is* the definition, not a theorem. |
|  2 | WebSearch (general form)         | (same query, general level) "change of rings"; Silverman Weierstrass coeffs           | yes  | base change reduces functoriality to fibers | Wikipedia "Change of rings"; LMFDB `ec.weierstrass_coeffs`. No source states a *named lemma* "a₃ of base change = image of a₃"; it is definitional. |
|  3 | WebSearch (named-after/aliases)  | Weierstrass "coordinate change"/"base change" transformation relations                 | no   | — | Sources discuss the `(u,r,s,t)` coordinate-change transformation laws (which *mix* coefficients); the plain ring-map base change leaving each `aᵢ ↦ φ(aᵢ)` is treated as a definition with no name. |
|  4 | ChatGPT MCP                      | standard form / generality / history of "a_i of a base-changed Weierstrass curve"      | n/a  | — | ChatGPT MCP unavailable in this environment (task note). Compensated by extra WebSearch generality levels (#1–#3) + Stacks/nLab/arXiv below. The content is elementary enough that the standard form is unambiguous from #1. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                     | n/a  | — | Directory absent for this project (`.mathlib-quality/` contains only `overview/`). Recorded n/a. |
|  6 | nLab                             | "Weierstrass curve" / "base change of elliptic curve"                                   | n/a  | — | nLab has no entry framing per-coefficient base change as a named lemma; functoriality of the model is implicit. Not a categorical statement worth a deeper nLab lookup. |
|  7 | nCatLab                          | —                                                                                      | n/a  | — | Not a categorical concept (a single coordinate projection under a ring map). |
|  8 | Stacks Project                   | base change of Weierstrass model                                                        | n/a  | — | Stacks treats Weierstrass models scheme-theoretically; the affine-coefficient projection lemma is below its granularity (not a tagged result). |
|  9 | MathOverflow / Math.SE           | "coefficients of base change of Weierstrass equation"                                   | no   | — | No question treats this as nontrivial; it is folklore/definitional. |
| 10 | recent arXiv (last 5 yrs)        | formal proof Weierstrass curve group law base change (arXiv:2302.10640)                | yes  | confirms `W.map φ` componentwise | The formal group-law paper uses exactly the componentwise base-change model; consistent with mathlib. No separately-named `a₃` lemma. |

### Literature summary (Phase 3)

Concept identified as: functoriality of the `a₃` Weierstrass coefficient under a ring
homomorphism / base change — i.e. the `a₃` projection of `W.map φ`.
Sources agree on the standard form: yes — `(W.map φ).aᵢ = φ(W.aᵢ)` for each `i`; this is
the *definition* of the base-changed model, not a theorem with a name.
Most general standard form: for any commutative rings `R, A`, ring hom `φ : R →+* A`, and
`W : WeierstrassCurve R`, one has `(W.map φ).a₃ = φ W.a₃`.
Generality dimensions where the literature varies: the base ring/map (here fixed to the
specific map `algebraMap ℤ ℚ : ℤ →+* ℚ`); the literature always states it for a general
ring map. So the project's `ℤ → ℚ` form is a strict specialisation of the standard form.
Disagreement with the literature: none — the project lemma is correct and is the `ℤ→ℚ`
instance of the standard definitional identity.

---

## Generality analysis — `curveQ_a₃` (Phase 4)

Literature-standard form (from Phase 3): `(W.map φ).a₃ = φ W.a₃` for any `φ : R →+* A`,
any `W : WeierstrassCurve R`.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form     | Weaker form exists? | Reason |
|---|------------------------|--------------------------|------------------------------|---------------------|--------|
| 1 | base ring of `W`       | fixed `ℤ`                | arbitrary `CommRing R`       | yes                 | The identity holds over any base ring; ℤ is a hard specialisation. |
| 2 | target ring + map      | fixed `algebraMap ℤ ℚ`   | arbitrary `φ : R →+* A`      | yes                 | The identity is just `φ` applied to a projection; the specific ℤ→ℚ map is irrelevant. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (both base ring and ring map are
hard-coded). However — and this is decisive — the strictly-more-general standard form is
**already in mathlib** (see Phase 5). So the right action is NOT "generalise this project
lemma"; it is "delete it and use the existing general mathlib lemma". The generality gap is
fully absorbed by `WeierstrassCurve.map_a₃`.

Proposed restatement: none needed — the maximally-general form already exists upstream.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question                                                              | Applies? | Notes |
|---|-----------------------------------------------------------------------|----------|-------|
| 1 | bundled-hypothesis preamble → typeclass?                              | no       | No bundled hypotheses; mathlib's `map` already uses `[CommRing R] [CommRing A] (f : R →+* A)`. |
| 2 | sequences/metric → filters/topology?                                 | no       | No limiting/topological content. |
| 3 | construction → universal-property class?                             | no       | A coordinate projection; no universal property. |
| 4 | set+closure-predicate → bundled substructure?                        | no       | Not a substructure. |
| 5 | vector-space/field-specific → weaken typeclasses?                    | no       | Already as weak as it gets (`CommRing`) in the mathlib form. |
| 6 | 1-categorical → higher-categorical?                                  | no       | Elementary. |
| 7 | concrete index (ℤ, ℚ) → general structure?                           | yes      | Exactly the point — but the generalisation is precisely `WeierstrassCurve.map_a₃` (arbitrary `R`, arbitrary `φ`), which mathlib **already has**. |

Modern idiom available: no *new* idiom — the contemporary, fully-general mathlib form is
`WeierstrassCurve.map_a₃` and it already exists. This pushes the verdict to
NO-mathlib-has-it (not YES-but-generalise-first), since "generalise first" would just
re-derive an existing mathlib lemma.

---

## Mathlib search-status: `curveQ_a₃` (Phase 5)

[A] Lean-Finder       "Weierstrass map coefficient a3 base change"      → hit: `WeierstrassCurve.map_a₃`
[B] Loogle            `(WeierstrassCurve.map _ _).a₃ = _ _`             → hit: `WeierstrassCurve.map_a₃` (`@[simps]`-generated)
[C] LeanSearch        "a3 coefficient of mapped Weierstrass curve equals image of a3" → hit: `WeierstrassCurve.map_a₃`
[D] Grep mathlib src  `map_a₃` in `Mathlib/`                            → hits: use-sites in `EllipticCurve/Weierstrass.lean` (lines 249, 254, 259) + `EllipticCurve/Reduction.lean:82`; lemma generated by `@[simps]` on `def map` (Weierstrass.lean:230–232)
[E] Name pattern      `map_a₃` / `map_a` family                         → hit: full family `map_a₁ … map_a₆` auto-generated

Searched for both:
  - the user's current form `(curveQ W).a₃ = (W.a₃ : ℚ)` — matches via `curveQ = W.map (algebraMap ℤ ℚ)`.
  - the literature-standard general form `(W.map f).a₃ = f W.a₃` — **exact match**.

Concluded: **found in mathlib as `WeierstrassCurve.map_a₃`; more general form** (the
project lemma is the `f := algebraMap ℤ ℚ` specialisation). Definition site:
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`
(`@[simps] def map`), generating `map_a₃ : (W.map f).a₃ = f W.a₃` as a `@[simp]` lemma.

Independent corroboration: the WebSearch top result (Phase 3 row 1, mathlib doc page)
prints `W.map φ = {a₁ := φ a₁, …, a₆ := φ a₆}` — the very definition that `@[simps]` turns
into `map_a₃`. And mathlib's own `map_b₄`/`map_b₆`/`map_b₈` proofs invoke `map_a₃`.

---

## Call sites — `curveQ_a₃` (Phase 6.0)

Internal use count: 3 (within NagellLutz, excluding the declaring file)
External-to-file callers: 3 distinct files

| Caller file:line                                   | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------|--------------------------------------------------------------------|
| GeneralMain.lean:167                               | `simp only [curveQ_a₁, curveQ_a₃, shortCurveZ_a₁, shortCurveZ_a₃, …]` |
| GeneralDiscriminant.lean:72                        | `simp only [curveQ_a₁, curveQ_a₃] at hψ₂`                          |
| GeneralPrimeOrder.lean:176                         | `simp only [curveQ_a₁, curveQ_a₃] at h; linarith`                  |

Inline-derivation grep: (none) — all three sites use the named lemma inside a `simp only`
set; no site re-derives the identity by hand.

Note: all uses are inside `simp only [...]`. Because `WeierstrassCurve.map_a₃` is itself
`@[simp]`, these call sites are precisely the case where the mathlib lemma would fire
identically once `curveQ` is unfolded (`curveQ` is a reducible `abbrev`, so `map_a₃`
matches directly on `(W.map (algebraMap ℤ ℚ)).a₃`).

## Composition check (Phase 6)

Can `curveQ_a₃` be derived from mathlib in ≤1 call?

Attempt 1: `WeierstrassCurve.map_a₃ W (algebraMap ℤ ℚ)`
  - Mathlib decls used: `WeierstrassCurve.map_a₃`.
  - Result: succeeds (up to the trivial `simp` normalisation `algebraMap ℤ ℚ x = (x : ℚ)`
    via `eq_intCast`/`map_intCast`, which is exactly what the current `by simp [curveQ]`
    already does). The general lemma gives `(W.map (algebraMap ℤ ℚ)).a₃ = algebraMap ℤ ℚ W.a₃`,
    and `algebraMap ℤ ℚ W.a₃ = (W.a₃ : ℚ)` definitionally / by `simp`.
  - Notes: this is a strict specialisation, not a new proof.

Conclusion: COMPOSABLE in ≤1 line — but the stronger statement is that mathlib *has the
lemma outright* (NO-mathlib-has-it dominates NO-composable here).

---

## Verdict: `LutzNagell.LutzNagellTheorem.curveQ_a₃`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the identity is the *definition* of the base-changed
  Weierstrass model (`(W.map φ).aᵢ = φ aᵢ`); not a named theorem. WebSearch's top hit was
  the mathlib definition itself; arXiv:2302.10640 uses the same componentwise model.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — base ring and map are
  hard-coded to ℤ→ℚ — but the general form is already upstream, so the gap is absorbed by
  the existing mathlib lemma rather than warranting a generalisation here.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_a₃` (more general
  form); generated by `@[simps]` on `WeierstrassCurve.map`, a `@[simp]` lemma, used in
  mathlib itself (Weierstrass.lean lines 249/254/259, Reduction.lean:82).
- Composition check (Phase 6): COMPOSABLE in ≤1 line, but NO-mathlib-has-it is the precise
  bucket since the lemma exists verbatim in general form.

**Rationale:**

The project defines `curveQ W := W.map (algebraMap ℤ ℚ)` and then states
`curveQ_a₃ : (curveQ W).a₃ = (W.a₃ : ℚ)`. This is exactly mathlib's
`WeierstrassCurve.map_a₃ : (W.map f).a₃ = f W.a₃` instantiated at `f := algebraMap ℤ ℚ`,
with `algebraMap ℤ ℚ W.a₃` normalising to the cast `(W.a₃ : ℚ)`. Mathlib generates
`map_a₃` automatically via the `@[simps]` attribute on `def map`
(`Weierstrass.lean:230–232`) and marks it `@[simp]`; mathlib's own
`map_b₄`/`map_b₆`/`map_b₈` proofs and `Reduction.lean` already rely on it. This is the
canonical "forked mathlib API re-derived locally" situation flagged in the task's PROJECT
CONTEXT: the NagellLutz project forks Weierstrass / division-polynomial infrastructure,
and this coefficient lemma is one whose general form is already in the upstream tree the
project builds against.

There is nothing to add to mathlib: the more general statement is present, is a `@[simp]`
lemma, and the project lemma is a pure specialisation used only inside `simp only [...]`
sets — sites where the upstream `@[simp] map_a₃` would fire identically once the reducible
`curveQ` abbrev unfolds. The lemma is a (mild) duplication of upstream API, not a
contribution.

**WHY not (refactor-actionable):**
Mathlib already has `WeierstrassCurve.map_a₃`. The project's `curveQ_a₃` follows from it
by specialising `f := algebraMap ℤ ℚ` and rewriting `algebraMap ℤ ℚ x` to the integer
cast. Detail sufficient to plan the refactor is below.

Existing mathlib decl:  `WeierstrassCurve.map_a₃`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`
                        (`@[simps] def map`; `map_a₃` is the generated `@[simp]` projection)

Our form follows in ≤1 line:
```lean
example (W : WeierstrassCurve ℤ) :
    (curveQ W).a₃ = (W.a₃ : ℚ) := by
  simpa using WeierstrassCurve.map_a₃ W (algebraMap ℤ ℚ)
-- fully unfolded: (W.map (algebraMap ℤ ℚ)).a₃ = algebraMap ℤ ℚ W.a₃ is `map_a₃`,
-- and `algebraMap ℤ ℚ W.a₃ = (W.a₃ : ℚ)` by `eq_intCast`/`map_intCast`.
```

Call sites in our project (from Phase 6.0): K = 3
(GeneralMain.lean:167, GeneralDiscriminant.lean:72, GeneralPrimeOrder.lean:176).

Refactor plan:
1. Cleanest: **delete the local `curveQ` alias track entirely** and use mathlib's
   `WeierstrassCurve.map`/`baseChange` directly; then `map_a₃` (already `@[simp]`) covers
   every current `curveQ_a₃` use site with no extra lemma.
2. If the `curveQ` abbrev is kept for readability: since `curveQ` is a reducible `abbrev`
   for `W.map (algebraMap ℤ ℚ)`, the upstream `@[simp] WeierstrassCurve.map_a₃` already
   fires on `(curveQ W).a₃`. So at each of the 3 sites, **drop `curveQ_a₃` from the
   `simp only [...]` set and add `WeierstrassCurve.map_a₃`** (mind the cast: the sites also
   need the `algebraMap ℤ ℚ → Int.cast` normalisation, e.g. include `eq_intCast` or use a
   plain `simp` rather than `simp only`). Then delete the `curveQ_a₃` declaration.
3. Apply the identical treatment to the sibling glue lemmas `curveQ_a₁, curveQ_a₂,
   curveQ_a₄, curveQ_a₆` (lines 27–31) — they are the same specialisation of
   `map_a₁ … map_a₆` and should be removed as one batch.

Next action: delete `curveQ_a₃` (and its `curveQ_a{1,2,4,6}` siblings) from
`GeneralCurve.lean`; update the 3 call sites to lean on the upstream `@[simp]
WeierstrassCurve.map_a₃` family (or eliminate the `curveQ` alias in favour of
`WeierstrassCurve.baseChange`). This is a `/cleanup`-lane dedup against forked mathlib API.

---

## Next step

Delete `curveQ_a₃` from the project and route its 3 call sites through the existing
upstream lemma `WeierstrassCurve.map_a₃` (the `@[simps]`-generated `@[simp]` projection of
`WeierstrassCurve.map`), batching the sibling `curveQ_a{1,2,4,6}` removals with it.
