# Mathlibable assessment — `WeierstrassCurve.Universal.Jacobian.addXYZ_smulRing`

- **Date:** 2026-06-22
- **Project:** NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS)
- **Source:** `projects/NagellLutz/LutzNagell/ZSMul.lean:524`
- **Author of file:** Junyan Xu (per copyright header; also the author of mathlib's
  `DivisionPolynomial/*` and co-author of mathlib's Jacobian group-law file)
- **Verdict:** **BORDERLINE-needs-human**

---

## Phase 0 — Baseline

- lake build: not re-run here (local build stale per task note); the decl elaborates as part of the
  committed `main`-style tree and is read directly from source.
- decl `WeierstrassCurve.Universal.Jacobian.addXYZ_smulRing`: ✓ resolved at `ZSMul.lean:524`.
- kind: `lemma`.
- has sorry: no.
- module docstring summary: proves `WeierstrassCurve.zsmul_eq_smulEval` — that `n • P` on a Weierstrass
  curve equals the division-polynomial triple `(φₙ(x,y), ωₙ(x,y), ψₙ(x,y))` in Jacobian coordinates,
  via an even–odd induction whose two recurrences are the doubling formula `dblXYZ` and the addition
  formula `addXYZ`, lifted through a "universal" Weierstrass curve.

## Phase 1 — Statement (verified from source)

Qualified name verified against the namespace stack `WeierstrassCurve` (l.76) → `Universal` (l.86) →
`Jacobian` (l.395): **`WeierstrassCurve.Universal.Jacobian.addXYZ_smulRing`**. ✓ matches the parsed name.

```lean
lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.comp_smul]; exact addXYZ_smulField
```

with `{m n : ℤ}` implicit (`variable {m n : ℤ}`, l.97).

### Mathematical content
On a Weierstrass curve, the multiplication-by-`n` map in Jacobian coordinates is
`n • P = (φₙ : ωₙ : ψₙ)`. This lemma is the **universal-ring incarnation of the addition recurrence**:
applying mathlib's Jacobian point-addition formula `addXYZ` to the division-polynomial triples for
`m` and `n` gives the triple for `n + m`, scaled by `ψ(n − m)`:

  `addXYZ ( (φₘ,ωₘ,ψₘ) , (φₙ,ωₙ,ψₙ) ) = ψ(n−m) • (φₙ₊ₘ, ωₙ₊ₘ, ψₙ₊ₘ)`,

as a **polynomial identity in the universal coefficient ring**
`Universal.Ring = ℤ[a₁,a₂,a₃,a₄,a₆,X,Y] / ⟨Weierstrass polynomial⟩` (the universal Weierstrass curve
carrying a generic point `(X,Y)`). Here `•` is the Jacobian scaling action `u•(x,y,z)=(u²x,u³y,uz)`.

Variables / typeclasses (Lean side):
- `m n : ℤ` — the two multiples being added (generic integers).
- Ambient: the fixed `Universal.Ring` and `Universal.Field = Frac(Universal.Ring)`, the universal
  curves `curveRing := curve.baseChange Universal.Ring`, `curveField := curve.baseChange Universal.Field`,
  and `curve : Affine (MvPolynomial Coeff ℤ)` the universal Weierstrass curve (`Universal.lean:84`).

Hypotheses: none (a clean polynomial identity over the universal ring).

Conclusion (math): the Jacobian addition formula on the `m`- and `n`-division-polynomial triples equals
the `(n+m)`-triple scaled by `ψ(n−m)`, in the universal ring.
Conclusion (Lean): `addXYZ curveRing (smulRing m) (smulRing n) = mk(ψ(n−m)) • smulRing (n+m)`.

### Proof
A **one-liner transport**: the result over `Universal.Field` (`addXYZ_smulField`, l.499 — the genuine
~20-line case analysis) is pushed back to `Universal.Ring` because `Ring → Field = Frac(Ring)` is
injective. Concretely `(IsFractionRing.injective Ring Field).comp_left` reduces the ring identity to
its image under the algebra map, and `simp_rw [← map_addXYZ, Jacobian.comp_smul]` shows that image is
exactly `addXYZ_smulField`. All mathlib calls here (`IsFractionRing.injective`, `Function.Injective.comp_left`,
`map_addXYZ`, `Jacobian.comp_smul`) are trivial plumbing; the mathematical weight lives in
`addXYZ_smulField`, which descends through `zsmul_point_eq_smulField`, `equiv_iff_eq_of_Z_eq`,
`add_point_of_ne_eq_addXYZ`, `addZ_smulPoly`, `ψᵤ_ne_zero` — all project-local.

## Phase 2 — Preliminary checks

### 2a. Size classification
**Verdict: BIG.** It is the **primary carrier** of one of the two recurrences (`## Main results`
docstring lines 24–56 name `addXYZ_smulRing` explicitly) that drive the headline theorem
`zsmul_eq_smulEval`. It is the universal-ring form from which both the consecutive-multiples corollary
`addXYZ_smulRing₁` and the general curve-level `addXYZ_smulEval` are derived. (Literature width is
EXHAUSTIVE regardless.)

### 2b. One-line check
Kind is `lemma`, not `def`/`abbrev`/`structure` — **n/a**. (The body is a one-line term-mode transport,
but the one-liner heuristic targets definitions; a proof being short is not a negative signal.)

## Phase 3 — Literature search (exhaustive protocol)

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "division polynomials multiplication by n Jacobian coordinates psi_n addition formula" | yes | `nP=(φₙ:ωₙ:ψₙ)`; `(ψₙ₊ₘψₙ₋ₘ)/(ψₙ²ψₘ²)=x∘[n]−x∘[m]` | MIT 18.783 Lecture 6 (Sutherland); Wikipedia "Division polynomials"; arXiv 2412.10284 (Mumford coords) |
| 2 | WebSearch (general / universal form) | "universal Weierstrass curve division polynomials addition formula psi(n-m) phi omega Silverman" | partial | affine recurrence `φₙ=xψₙ²−ψₙ₋₁ψₙ₊₁`, `ωₙ=(ψₙ₋₁²ψₙ₊₂−ψₙ₋₂ψₙ₊₁²)/4y`, `n(x,y)=(φₙ/ψₙ², ωₙ/ψₙ³)` | Silverman, *AEC* GTM 106 is the named reference; the `ψ(n−m)`-scaled Jacobian form is not foregrounded — it is the projective shadow of the affine identity |
| 3 | WebSearch (named-after / aliases) | "mathlib Lean elliptic curve division polynomial scalar multiplication smul point Jacobian Angdinata Xu formalization" | yes (background) | mathlib defines ψ/φ/ω via EDS; ITP 2023 (Angdinata–Xu) formalized the Jacobian/projective **group law** | confirms mathlib has the polynomials and the group law, but **no bridge** `n•P = division-poly triple` |
| 4 | ChatGPT MCP | (two attempts, high + medium effort) | n/a | — | **Codex/ChatGPT MCP is down** in this environment (confirmed by two failed invocations — matches the task's "ChatGPT MCP may be down" warning). Fell back to WebSearch + textbook knowledge. |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/references/` | n/a | — | directory absent; `refs/` symlink absent — recorded n/a |
| 6 | nLab | "division polynomial elliptic curve" | n/a | — | nLab has no dedicated division-polynomial page; concept is classical AG/number theory, covered by Silverman, not nLab's categorical focus |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | — | n/a | — | division polynomials / explicit Weierstrass multiplication formulae are not in Stacks (it does not treat explicit EC division polynomials) |
| 9 | MathOverflow / MSE | covered transitively by query 1 (the MO "Motivation for Jacobian coordinates" thread surfaced) | yes | confirms Jacobian coords are the standard home for the explicit `[n]` map | reinforces that the Jacobian-coordinate `[n]` formula is the textbook object |
| 10 | recent arXiv (≤5y) | covered by query 1 → arXiv:2412.10284 "Division polynomials in Mumford coordinates"; arXiv:2503.15428 "Division polynomials for arbitrary isogenies" | yes | active research area; all treat the *mathematics*, none a Lean formalization of the universal-ring Jacobian identity | confirms novelty of the *formalization*, not the math |

### Literature summary
- **Concept identified as:** the division-polynomial / elliptic-divisibility-sequence **addition
  formula**, equivalently one recurrence step of the multiplication-by-`n` map `nP=(φₙ:ωₙ:ψₙ)` in
  Jacobian coordinates.
- **Sources agree on the standard form:** yes — `nP=(φₙ:ωₙ:ψₙ)` (Jacobian) and the affine
  `n(x,y)=(φₙ/ψₙ², ωₙ/ψₙ³)`, with the cross-relation
  `ψₙ₊ₘψₙ₋ₘ = φₘψₙ² − φₙψₘ²` (Silverman GTM 106; Washington §3.2; Wikipedia; MIT 18.783).
- **Most general standard form:** the polynomials are defined over an arbitrary base ring (mathlib
  already does this via EDS), so the *coefficient-maximal* statement is over a generic/universal
  curve — exactly the `Universal.Ring` chosen here. The textbook usually states it over a field, but
  the universal-ring form is strictly more general and specialises to every field/ring instance.
- **Generality dimensions where the literature varies:** (a) base — field (textbook) vs. arbitrary
  ring / universal ring (mathlib EDS, this file); (b) coordinates — affine (textbook) vs. Jacobian
  (this file, matching mathlib's group-law file); (c) scaling — the `ψ(n−m)•` projective normalisation
  (this file) vs. the un-normalised affine cross-relation (textbook).
- **Disagreement with the literature:** none. The lemma is a faithful, more-general (universal-ring,
  Jacobian) rendering of the classical addition formula.

**The *mathematics* is classical and standard. The *formalization* — a universal-ring Jacobian-coordinate
identity stated via the `addXYZ`/`smulRing` API — is formalization-native and has no published prior
formalization** (the search found mathlib's polynomials + the ITP-2023 group law, but not this bridge).

## Phase 4 — Generality analysis

Literature-standard maximal form (Phase 3): the addition formula over the most general base, i.e. a
generic/universal Weierstrass curve, in Jacobian coordinates — which is *precisely* what this lemma
states.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | base ring | the universal ring `ℤ[a₁..a₆,X,Y]/⟨W⟩` | arbitrary ring (textbook: a field) | **NO** | the universal ring is the *initial* / most-general instance; every nonsingular point over any `CommRing`/field is a specialisation via `ringEval` (`ringEval_comp_smulRing`, l.557). Cannot be made more general. |
| 2 | curve | `curveRing` = universal curve | a generic Weierstrass curve | NO | same — it is the generic curve. |
| 3 | `m n : ℤ` | arbitrary integers | arbitrary integers | NO | already fully general. |
| 4 | coordinates | Jacobian (`addXYZ`, `smulRing`) | Jacobian (matches mathlib group law) | NO | matches the mathlib EC group-law representation; affine would be *less* composable with mathlib's `Jacobian.Point`. |

### 4b. Generality verdict
**MAXIMALLY GENERAL** in the mathematical content (base, curve, indices). The current statement is the
universal-ring form — the most general carrier. **0 weakening opportunities.** The only open axis is not
*generality* but *packaging granularity* for upstreaming (handled in 4c / Phase 7): whether the public
mathlib API should be this ring identity, the field identity, or the downstream curve-level `…Eval`
form — and whether the universal-ring lemmas should be `private` engine vs. exported.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" → typeclasses/instances? | no | — | already typeclass-driven (`CommRing`, `IsFractionRing`); no bundled-hypothesis preamble to convert. |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic identity; no limits/topology. |
| 3 | construct an object → universal-property class? | **partially relevant** | The `Universal.Ring` *is* a universal-property construction (the initial Weierstrass-coefficient ring). It is already used as the universal object; the question is only whether mathlib wants it exposed. | the universal ring lets every concrete identity be proved once and transported — this is already the idiom in use. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclasses? | **yes, already done** | the lemma is stated over the *ring* (not just the field); the field version `addXYZ_smulField` is the special case, and this ring form is the weakening | this is the right direction — `addXYZ_smulRing` weakens `addXYZ_smulField` from `Universal.Field` to `Universal.Ring`. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | no | — | the indices `m,n` are genuinely integers (multiples of a point); generalising the index away from ℤ is not meaningful here. |

**Modern-idiom verdict:** no *new* modernisation move is available — the lemma already embodies the
relevant ones (universal-object transport; ring-over-field weakening). The only genuine question is the
**granularity at which the family is exposed upstream**, which is a packaging decision, not a
reformulation. One-line reason: the statement is already in the maximally-general, idiomatic form; what
remains is a maintainer call on public-vs-private and which member of the `{Ring, Field, …₁, …Eval}`
family is the headline API.

## Phase 4.5 — Diamond / defeq risk
**n/a — declaration kind is `lemma`** (introduces no definitional equalities or typeclass-search paths).

## Phase 5 — Mathlib search (five methods)

Searched the pinned mathlib at `.lake/packages/mathlib/`.

- **[A] Lean-Finder / [B] Loogle / [C] LeanSearch:** the live mathlib index tools are unavailable in
  this environment (local build stale per task note; `lean_loogle`/`lean_leansearch` not loadable).
  Substituted with exhaustive source grep ([D]/[E]) + the mathlib-docs WebSearch (Phase 3 #3), which
  directly confirms `DivisionPolynomial/Basic` defines ψ/φ/ω and that the ITP-2023 group-law file
  exists but contains **no** division-polynomial↔scalar-multiple bridge.
- **[D] Grep mathlib src:**
  - `addXYZ_smulRing | smulRing | smulField | smulPoly | smulEval | zsmul_eq_smulEval | dblXYZ_smulRing`
    across all of `Mathlib/` → **zero hits**.
  - `namespace Universal | Universal.Ring | Universal.Field | curveRing | curveField` in
    `Mathlib/AlgebraicGeometry/` → **zero hits** (only the unrelated `UniversallyOpen.lean`,
    `UniversalEnveloping.lean`).
  - Building blocks **present**: `addXYZ`, `addZ`, `addXYZ_smul`, `addXYZ_self`, `addXYZ_neg`,
    `map_addXYZ`, `dblXYZ`, `map_dblXYZ`, `Jacobian.comp_smul` (`Jacobian/Formula.lean`,
    `Jacobian/Basic.lean`); `IsFractionRing.injective`, `Function.Injective.comp_left`;
    division-polynomial/EDS theory `DivisionPolynomial/{Basic,Degree}.lean`,
    `NumberTheory/EllipticDivisibilitySequence.lean` (`ψ`, `φ`, `ω`, `ψ_one`, `normEDS`, `IsEllSequence`).
- **[E] Name pattern:** no `*smulRing*` / `*smulField*` / `Universal.*` EC names anywhere in mathlib.
- Searched for **both** the user's form (ring identity) **and** the literature-standard form (the
  scalar-multiple / addition formula over any base, in any coordinates). Neither is present.

**Concluded:** *not in mathlib* (grep-exhausted, plus the literature-standard form). Mathlib has the
primitives (`addXYZ_*`, `map_addXYZ`, `Jacobian.comp_smul`, `IsFractionRing.injective`) and the
polynomials (ψ/φ/ω via EDS) but **lacks the bridge** connecting the division polynomials to point
scalar-multiplication `n • P` in Jacobian coordinates — and lacks the entire `Universal`/`smul*` API
this lemma is phrased in. The content is genuinely new. **Additionally it is DUPLICATED VERBATIM across
two AINTLIB projects** (see Phase 6).

## Phase 6 — Composition check (+ call sites)

### 6.0. Call sites — `addXYZ_smulRing`
Internal use count (NagellLutz, excluding declaring lines 524–528): **2**.
External-to-file callers within NagellLutz: 0 (both uses are in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| NagellLutz `ZSMul.lean:539` | `rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, …]` (in `addXYZ_smulRing₁`, the consecutive-multiples corollary) |
| NagellLutz `ZSMul.lean:576` | `rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]` (in `addXYZ_smulEval`, the **general curve-level public form**, l.572) |

**Cross-project duplication:** the identical lemma + proof exists **verbatim in HasseWeil**
(`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:598`), with identical consumers there
(`addXYZ_smulRing₁` at l.612, `addXYZ_smulEval` at l.648). Byte-for-byte the same statement and proof.

Inline-derivation grep: the entire lemma is re-derived inline in HasseWeil (a full second copy) — the
strongest possible composability-redundancy signal: the same content is maintained twice across projects.

Call-site reading: **K = 2 internal uses, no inline re-derivation within NagellLutz** → this is **real
API**, the primary carrier of the addition recurrence (it feeds both the `…₁` corollary and the
general `…Eval` form). Combined with cross-project duplication, this is shared infrastructure that
currently lives in two places and should live in one (ideally upstream).

### 6a. Composition attempt (≤3 mathlib calls?)
- **Attempt 1:** compose mathlib's `addXYZ_smul` + `addXYZ_self` + `addXYZ_neg` + `map_addXYZ`.
  Result: **fails.** Those cover only degenerate shapes (scaled / equal / negated inputs). The generic
  case (`m≠n`, `n≠−m`) of the *field* engine `addXYZ_smulField` needs `equiv_iff_eq_of_Z_eq` (project),
  `zsmul_point_eq_smulField` (project theorem, itself nontrivial), `add_point_of_ne_eq_addXYZ` (project),
  and the EDS Z-coordinate identity `addZ_smulPoly` — none in mathlib.
- **Attempt 2:** transport-only — the body *is* `(IsFractionRing.injective _ _).comp_left <| by …; exact
  addXYZ_smulField`. That is ≤3 mathlib calls **on top of `addXYZ_smulField`**, but `addXYZ_smulField`
  is not a mathlib decl, so the composition does not bottom out in mathlib. Result: **fails as a mathlib
  composition.**

**Conclusion: NOT-COMPOSABLE.** The transport wrapper is cheap, but the engine (`addXYZ_smulField` →
`zsmul_point_eq_smulField` → the `Universal` curve construction) is entirely project-local; mathlib
cannot produce this in ≤3 calls.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.addXYZ_smulRing`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the *mathematics* (division polynomials compute `n•P`; the
  addition/EDS recurrence) is classical and standard (Silverman GTM 106; Washington; MIT 18.783;
  Wikipedia). The *universal-ring Jacobian-coordinate form* is formalization-native and has no prior
  formalization. ChatGPT MCP was down (two failed calls); WebSearch + textbook knowledge substituted.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (universal ring = initial/most-general base;
  Jacobian coordinates matching mathlib's group law; 0 weakenings). Phase 4c: already idiomatic; the
  open axis is packaging granularity, not reformulation.
- Mathlib search (Phase 5): **NOT in mathlib**; building blocks present (`addXYZ_*`, `map_addXYZ`,
  `Jacobian.comp_smul`, `IsFractionRing.injective`, ψ/φ/ω) but no `smul*` API and no
  division-polynomial↔scalar-multiple bridge.
- Composition check (Phase 6): **NOT-COMPOSABLE** (engine is project-local); call sites **K=2** real
  consumers (the `…₁` corollary and the general `…Eval` form) + **verbatim duplication in HasseWeil**.

**Rationale:**

The result is clearly mathlib-*worthy in spirit*. It is a load-bearing step in the missing bridge
between mathlib's `DivisionPolynomial/Basic` (which defines ψ/φ/ω) and mathlib's Jacobian group law
(Angdinata–Xu, ITP 2023): that `n • P` is literally computed by division-polynomial coordinates,
headlined by `zsmul_eq_smulEval`. That bridge is a textbook theorem (Silverman, *AEC*) with no mathlib
counterpart, written by the same author who built mathlib's group-law file, and it is **already
duplicated verbatim across two AINTLIB projects** (NagellLutz `ZSMul.lean:524` and HasseWeil
`Auxiliary/DivisionPolynomial.lean:598`) — the canonical "this should be shared, ideally upstream"
signal. The statement itself is maximally general and idiomatic (universal ring, Jacobian coordinates),
so this is **not** `NO-mathlib-has-it` (verified absent, Phase 5) and **not** `NO-composable-from-mathlib`
(the engine is project-local, Phase 6).

What keeps the verdict BORDERLINE rather than a clean YES is **packaging granularity**, a maintainer
judgment the skill must not make alone. `addXYZ_smulRing` is the *primary universal-ring carrier* of the
addition recurrence: its two consumers are `addXYZ_smulRing₁` (consecutive multiples) and the
general curve-level `addXYZ_smulEval` (arbitrary `W`, ring, point — the form a mathlib *user* actually
wants). So three packagings are defensible, and they must be decided **as one PR** for the whole
`{dblXYZ_smulRing, addXYZ_smulRing, addXYZ_smulField, …₁, …Eval, zsmul_eq_smulEval}` family rather than
lemma-by-lemma: (a) export the whole `Universal` division-polynomial-Jacobian apparatus (so
`addXYZ_smulRing` ships as a named public lemma); (b) lead with the *ring* identity `addXYZ_smulRing`
as the primary statement, the field version as a `private` step, and the curve-level `…Eval` lemmas as
the user API; or (c) export only `zsmul_eq_smulEval` + the `…Eval` corollaries with the entire
universal-ring/field layer `private`. This is a genuine design call, not cost-driven (the proofs all
exist; repackaging is CHEAP). It is exactly the same open question already recorded for the sibling
engine `addXYZ_smulField` (BORDERLINE) — and `addXYZ_smulRing` is even more central, being the carrier
both `…₁` and `…Eval` are built from. Independently of the upstream decision, the **cross-project
verbatim duplication should be de-duplicated into an AINTLIB `Common/` module** as a cleanup ticket.

This is **not** `YES-but-generalise-first`: there is no narrower-than-standard hypothesis to weaken
(Phase 4b = MAXIMALLY GENERAL) and no concrete modern-idiom restatement (Phase 4c = none) — the only
"generalise/repackage" axis is the public-API-granularity question, which is precisely a human call.
(Note: the trivial sibling `addXYZ_smulRing₁`, a one-line specialisation with a single consumer, was
adjudicated `YES-but-generalise-first` toward its `…Eval₁` form; `addXYZ_smulRing` differs in being the
*primary multi-consumer carrier* whose own public-vs-private status is the open packaging question,
matching `addXYZ_smulField`'s BORDERLINE.)

**Numbered questions (≤5):**
  1. Should the upstream unit be the **whole** division-polynomial↔Jacobian bridge (`smulPoly/Ring/Field`,
     `dblXYZ_smul*`, `addXYZ_smul*`, `…Eval`, `zsmul_eq_smulEval`) as a single new mathlib file
     (e.g. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Jacobian.lean`)? (yes/no)
  2. Should the **ring** identity `addXYZ_smulRing` (over the universal coord ring) be the *primary*
     public statement, with the field version `addXYZ_smulField` as a `private` step — i.e. should the
     PR lead with the ring form? (yes/no)
  3. Or should mathlib export **only** the curve-level results (`addXYZ_smulEval`, `zsmul_eq_smulEval`)
     and keep the entire universal-ring/field layer (`addXYZ_smulRing` included) `private`/section-local? (yes/no)
  4. The lemma is **duplicated verbatim in HasseWeil** (`Auxiliary/DivisionPolynomial.lean:598`).
     Regardless of upstreaming, should this be de-duplicated into an AINTLIB `Common/` module first
     (a cleanup ticket)? (yes/no)
  5. The project **forks** mathlib's `EllipticDivisibilitySequence` / `DivisionPolynomial` (to swap the
     EDS implementation). Must that fork be reconciled with mathlib before any of this can be upstreamed,
     and is that a blocker or a parallel track? (blocker / parallel)

Next action: user/maintainer answers 1–5 (packaging granularity + dedup + fork reconciliation). The
mathematics is mathlib-worthy and NOT in mathlib (the division-polynomial ↔ Jacobian-group-law bridge is
a genuine gap); the open issues are (i) the right public-API unit/granularity for upstreaming the
`smul*` family as one PR, and (ii) resolving the verbatim NagellLutz/HasseWeil duplication into a shared
`Common/` location. Decide the family together, not this lemma in isolation.

---

## Next step

Answer questions 1–5 above. Decide the upstream packaging for the whole `smul*` / `…Eval` /
`zsmul_eq_smulEval` family as **one** PR (this lemma is the primary universal-ring carrier within it),
and file an AINTLIB cleanup ticket to de-duplicate the NagellLutz/HasseWeil verbatim copies into `Common/`.
