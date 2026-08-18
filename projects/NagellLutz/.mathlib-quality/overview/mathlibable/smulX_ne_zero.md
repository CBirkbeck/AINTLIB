# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_ne_zero`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.
> ChatGPT MCP down; `lean_loogle`/`lean_leansearch` not loadable in this env → Phase 5 done by
> exhaustive grep over the synced mathlib pin (`.lake/packages/mathlib/`). WebSearch + the
> existing sibling reports in this directory used for the literature/composition cross-check.
> Local lake build stale — reasoned from source, which elaborates in the committed tree.

## Baseline (Phase 0)

- lake build:               stale (not re-run, per task).
- decl `WeierstrassCurve.Universal.Affine.smulX_ne_zero`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:203`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Integer multiples of a rational point on an elliptic curve in terms
                             of division polynomials" — proves `WeierstrassCurve.zsmul_eq_smulEval`,
                             i.e. `n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coords. Author: Junyan Xu.

**Qualified name VERIFIED from source.** The parsed name
`WeierstrassCurve.Universal.Affine.smulX_ne_zero` is correct: namespace nesting is
`namespace WeierstrassCurve` (ZSMul.lean:76) → `namespace Universal` (:86) →
`namespace Affine` (:157); the declaration sits at :203.

---

## Statement (Phase 1)

Verbatim source (ZSMul.lean:162–164, 203–204):

```lean
/-- The rational function φₙ/ψₙ², which we will show to be the `X`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2
…
lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)
```

with the supporting abbreviation (ZSMul.lean:131–132):

```lean
/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)
```

**What it says.** On the *universal* pointed Weierstrass curve — the curve over the field of
fractions `Universal.Field` of the universal coefficient ring
`Universal.Ring = ℤ[a₁,…,a₆,X,Y]/⟨Weierstrass⟩`, with tautological point `(X,Y)` — write
`smulX n = φₙ/ψₙ²` (the candidate X-coordinate of `n • (X,Y)`, proved correct downstream by
`zsmul_eq_smulEval`). Then for every `n ≠ 0`, `smulX n ≠ 0`.

Mathematically: the X-coordinate `x([n]P) = φₙ(P)/ψₙ(P)²` of a nonzero integer multiple of the
*generic* point `P = (X,Y)` is a nonzero element of the function field. Equivalently, neither the
numerator `φₙ` nor the denominator `ψₙ` vanishes generically — which holds because the universal
point `(X,Y)` has **infinite order** (no `n • (X,Y)` is the point at infinity for `n ≠ 0`).

Variables / typeclasses: none free — everything lives in the fixed field `Universal.Field`;
`n : ℤ` is the multiplier; the single hypothesis is `h0 : n ≠ 0`.

**Proof (1 line).** `div_ne_zero` (a quotient `a/b` is nonzero when both `a ≠ 0` and `b ≠ 0`)
applied to:
- `polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0` — the **numerator** is nonzero
  (ZSMul.lean:148; proved by specializing the generic `φₙ` to the cuspidal cubic `Y²=X³` at
  `(1,1)`, where `polyEval_cusp_φ` gives `φₙ ↦ 1 ≠ 0`); and
- `pow_ne_zero _ (ψᵤ_ne_zero h0) : (ψᵤ n) ^ 2 ≠ 0` — the **denominator** is nonzero, from
  `ψᵤ_ne_zero : n ≠ 0 → ψᵤ n ≠ 0` (ZSMul.lean:142; proved by the same cusp specialization, where
  `polyEval_cusp_ψ` gives `ψₙ(1,1) = n ≠ 0` — this is exactly "the universal point has infinite
  order").

So the lemma is the trivial *combination*: `div_ne_zero (numerator ≠ 0) (denominator ≠ 0)`. All the
mathematical weight is in the two ingredient nonvanishing facts, both of which are project-local.

---

## Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a one-line `div_ne_zero` glue lemma asserting well-definedness/nonvanishing of a
project-local definition (`smulX`). It is not a named theorem in the literature; the *named* facts
in this vicinity are the multiplication formula `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` and the coprimality
`gcd(φₙ, ψₙ²) = 1` — both stronger/different, and neither is *this* nonvanishing one-liner.
(Literature width still run below for completeness; the matched siblings `smulX_zero`,
`polyToField_φ_ne_zero` are already EXHAUSTIVE-searched in this directory.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — **n/a**.

---

## Literature search table (Phase 3)

| #  | Channel                         | Query                                                                            | Hit? | Standard form found                                                  | Notes |
|----|---------------------------------|----------------------------------------------------------------------------------|------|----------------------------------------------------------------------|-------|
|  1 | WebSearch (specific)            | division polynomial `x(nP)=φ_n/ψ_n²` numerator/denominator nonvanishing           | partial | `[n]P=(φ_n/ψ_n², ω_n/ψ_n³)`; nonvanishing is implicit well-definedness | Wikipedia "Division polynomials"; Silverman AEC Ex. 3.7 |
|  2 | WebSearch (named fact)          | `gcd(φ_n, ψ_n²)=1` coprimality division polynomials                                | yes  | `φ_n` and `ψ_n²` are **coprime** (so `x(nP)` is in lowest terms)      | Silverman AEC III; arXiv 1108.3051 / 1801.02664 — the *named* fact is coprimality, stronger than `≠0` |
|  3 | WebSearch (infinite order)      | universal/generic elliptic point infinite order `ψ_n≠0` `n≠0`                     | yes  | generic point has infinite order ⇒ `ψ_n ≠ 0` for `n ≠ 0` (EDS non-degeneracy) | Sutherland MIT 18.783 L5; Stange EDS; cuspidal-specialization trick standard |
|  4 | WebSearch (EDS nonvanishing)    | elliptic divisibility sequence `ψ_n=0 ⇔ n=0` non-degenerate                        | yes  | for a non-degenerate EDS, `ψ_n = 0 ⇔ n = 0`                          | Ward 1948; Wikipedia EDS; matches `polyEval_cusp_ψ: ψ_n(1,1)=n` |
|  5 | Sibling reports (this dir)      | `smulX_zero.md`, `polyToField_φ_ne_zero.md`, `smulX_sub_smulX.md` (EXHAUSTIVE)     | yes  | confirm: no `smulX`/`Universal`/`polyToField` upstream; no standalone `φ_n≠0`/`ψ_n≠0` named thm | reuse of the already-run exhaustive sweeps for the same family |
|  6 | ChatGPT MCP                     | —                                                                                | n/a  | server down (task flagged) — covered by #1–#5                        | fallback |
|  7 | nLab / Stacks                   | division polynomial nonvanishing / x-coordinate of multiple                       | n/a  | not covered (not categorical; Stacks omits explicit EC multiplication) | n/a |

### Literature summary (Phase 3)

Concept: **nonvanishing of the X-coordinate `φₙ/ψₙ²` of `n • P`** — i.e. the well-definedness
half of the classical division-polynomial multiplication formula. The literature treats this as
routine bookkeeping subordinate to two named facts: (i) the multiplication formula
`[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`, and (ii) the **coprimality** `gcd(φₙ, ψₙ²) = 1`. The denominator half
(`ψₙ ≠ 0 ⇔ n ≠ 0`) is the standard **non-degeneracy of the division-polynomial EDS**, equivalent to
"the (generic) point has infinite order" — exactly what the project's cusp specialization
(`ψₙ(1,1) = n`) proves. There is **no standalone, citable "`φₙ/ψₙ² ≠ 0`" theorem**; it is a
corollary of the above. Sources agree on the standard form (the stronger coprimality); the
universal/generic curve is the maximal-generality anchor. **No disagreement** with the literature.

---

## Generality analysis (Phase 4)

Literature-standard form: for any Weierstrass curve `W/F` and any point `P` of infinite order (or
generically), `x([n]P) = φₙ(P)/ψₙ(P)²` is well-defined and nonzero — strengthened in the literature
to the coprimality `gcd(φₙ, ψₙ²) = 1` over the parametric base.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | the curve / point | the *universal* curve over `Universal.Field`, tautological point `(X,Y)` | any `W/F`, point `P` of infinite order | **STRICTLY NARROWER in expression** | The mathlib-worthy kernel is the **parametric** `Φₙ ≠ 0` / `IsCoprime (Φₙ) (ΨSqₙ)` over an arbitrary base `W : WeierstrassCurve R`. The current decl pins to a single project-local universal object (`polyToField`/`curve`/`ψᵤ`). The universal framing *is* the maximal generality (every concrete curve specialises by a ring hom), but the **statement names fork-only objects**. |
| 2 | `h0 : n ≠ 0` | nonzero | nonzero (else `ψₙ = 0`, denom vanishes, `smulX 0 = 0`) | NO | Essential: at `n = 0`, `ψ₀ = 0` and `smulX 0 = 0` (its `@[simp]` sibling `smulX_zero`). The complement of this lemma is literally false at `n = 0`. Tight. |
| 3 | the conclusion strength | `smulX n ≠ 0` (numerator and denom each ≠ 0) | `gcd(φₙ, ψₙ²) = 1` (coprime — strictly stronger) | — | The literature's named fact is coprimality; mathlib wants *that* (parametric), not this weaker per-point ≠0. A separate, stronger, generalise-first target. |

### Generality verdict (Phase 4b)

The form is **STRICTLY NARROWER in expression** than the mathlib-worthy object: it is the
universal-case glue used to make `smulX`/`smulY` well-defined, not a parametric statement. The
genuinely mathlib-able kernel is the **parametric** nonvanishing/coprimality of the division
polynomials (`Φₙ ≠ 0`, `IsCoprime (Φₙ) (ΨSqₙ)` for `W : WeierstrassCurve R`) — a **different
declaration** (cost EXPENSIVE), and exactly the natural next layer above mathlib's existing
`natDegree_Φ`/`leadingCoeff_Φ`. Number of in-place weakenings of *this* decl: 0 (h0 is tight; the
universal framing is intrinsic to the fork's strategy).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | "Let X be a foo" → typeclass? | no | already typeclass-free (fixed field) |
| 3 | construction → universal-property class? | partial | the **universal curve** `Universal` *is* the corepresented-functor device; the *package* (`curve`/`polyToField`/`ringEval`) could one day be a `WeierstrassCurve.IsUniversal`-style class — but that reshapes the whole `Universal.*` layer, **not** this one nonvanishing lemma |
| 5 | field-specific → weaken typeclasses? | no | lives in `Universal.Field` by necessity (need division); concrete curves arrive by base-change ring hom |
| 7 | concrete index ℤ → several points (elliptic nets)? | tangential | Stange's net theory is a larger separate development; not a restatement of this `≠0` glue |

Modern-idiom available for **this declaration as scoped**: **no**. (The umbrella idiom — a
universal-property class for the whole package — is the real idiomatic home for `curve`/`ringEval`,
not for this corollary.)

---

## Diamond / defeq risk (Phase 4.5)

n/a — kind is `lemma` (introduces no definitional equalities or instance-search paths). Skipped.

---

## Mathlib search-status (Phase 5)

[A] Lean-Finder    not loadable in env → n/a (covered by grep [D] + sibling reports).
[B] Loogle         not loadable in env → n/a (covered by grep [D]).
[C] LeanSearch     not loadable in env → n/a (covered by grep [D]).
[D] **Grep mathlib src** (decisive) over the synced pin `.lake/packages/mathlib/Mathlib/`:
    - `smulX` / `smulY` / `polyToField` / `ψᵤ` — **0 hits in all of mathlib**. The subject objects
      do not exist upstream.
    - `namespace Universal` under `EllipticCurve/` — **0 hits** (the only `namespace Universal` in
      mathlib is `AlgebraicGeometry/Morphisms/UniversallyOpen.lean`, unrelated). No universal
      pointed Weierstrass curve upstream.
    - **General division-polynomial / EDS nonvanishing** `ψₙ ≠ 0` (resp. `normEDSₙ ≠ 0`) for
      `n ≠ 0`: searched `EllipticDivisibilitySequence.lean` and
      `DivisionPolynomial/{Basic,Degree}.lean` for `normEDS.*ne_zero`, `ψ.*≠ 0`,
      `IsEllSequence.*ne_zero` — **no general statement**. The only `≠0` facts are
      degree/leading-coefficient ones (`Ψ₂Sq_ne_zero` under the *specific* hypothesis `(4:R) ≠ 0`,
      `coeff_Ψ₂Sq_ne_zero`, `natDegree_Φ`, `leadingCoeff_Φ`) — there is **no** `Φₙ ≠ 0`, no
      `IsCoprime (Φₙ) (ΨSqₙ)`, and **no** "the EDS vanishes iff the index is 0".
    - `div_ne_zero`, `pow_ne_zero` (the two mathlib steps) — **present**
      (`Algebra/GroupWithZero/Units/Basic.lean:284`, `Algebra/GroupWithZero/Basic.lean:258`).
[E] Name pattern  `smulX_ne_zero` — exists in exactly two project files (NagellLutz `ZSMul.lean:203`
    + a verbatim **duplicate** in HasseWeil `Auxiliary/DivisionPolynomial.lean:261`); **0** in mathlib.

Searched for both forms:
  - the user's current form (`smulX n ≠ 0`) — subject `smulX`/`ψᵤ`/`polyToField`/`Universal.Field`
    is **project-local; 0 mathlib hits**.
  - the literature-standard parametric kernel (`Φₙ ≠ 0` / `IsCoprime (Φₙ) (ΨSqₙ)` over a base) —
    **also absent**: mathlib's `DivisionPolynomial` stops at degrees + leading coefficients.

What mathlib HAS / does NOT have:
- HAS: `DivisionPolynomial/{Basic,Degree}` (`ψ, preΨ, Ψ, φ, ω` + recurrences/degrees/base-change),
  `NumberTheory/EllipticDivisibilitySequence` (`IsEllSequence`, `normEDS`, `preNormEDS` — abstract
  sequences), `{Affine,Jacobian,Projective}/Point` (the group law), and the primitives
  `div_ne_zero`/`pow_ne_zero`.
- DOES NOT HAVE: the `Universal` curve framework, `smulX`/`smulY`/`polyToField`/`ψᵤ`, the
  multiplication formula `n • P = (φₙ/ψₙ², ωₙ/ψₙ³)`, any general nonvanishing `ψₙ ≠ 0`/`Φₙ ≠ 0`, or
  the coprimality `gcd(φₙ, ψₙ²) = 1`. (The project even *forks* `EllipticDivisibilitySequence` into a
  richer `net`/`rel₄`/`Rel₃` API that is itself not yet upstream.)

Concluded: **not in mathlib** under either form — the subject objects and both non-trivial
ingredient lemmas are fork-local; mathlib supplies only the two generic combinators
`div_ne_zero`/`pow_ne_zero`. → **not NO-mathlib-has-it.**

---

## Call sites (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring line): **1** direct.
External-to-repo: the lemma is **duplicated verbatim** in HasseWeil.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:208` | `rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm` — base case of `smulX_ne_smulX` |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:210` | `rw [smulX_zero]; exact smulX_ne_zero ne` — other base case of `smulX_ne_smulX` |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:261–262` | **duplicate declaration** (HasseWeil fork copy of the identical lemma) |

Inline-derivation grep: the structurally **identical twin** `smulX_zero` (the `n = 0` complement)
sits two declarations above; `smulX_ne_zero` is its `n ≠ 0` counterpart, and together they feed
`smulX_ne_smulX` / `smulX_eq_smulX_iff` (injectivity of `n ↦ x([n]P)` up to sign). The lemma is
**fork-internal scaffolding** for `smulX` injectivity, not a broadly-consumed exported API.

Signal: **K = 1 internal use** + a **cross-project duplicate** → leans NO/BORDERLINE; this is a
consolidation/dedup candidate on `main`, not a standalone mathlib export.

---

## Composition check (Phase 6)

Can `smulX n ≠ 0` be derived from **mathlib alone** in ≤3 chained calls? **No.**

The proof is literally `div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)` — two
mathlib combinators wrapped around **two fork-local nonvanishing facts**:

| Step | Decl | In mathlib? |
|------|------|-------------|
| outer | `div_ne_zero` | ✅ mathlib (`GroupWithZero/Units/Basic`) |
| denom | `pow_ne_zero` | ✅ mathlib (`GroupWithZero/Basic`) |
| numerator ≠ 0 | `polyToField_φ_ne_zero` | ❌ **fork-local** — its own report (`polyToField_φ_ne_zero.md`) → **BORDERLINE / NOT-COMPOSABLE-from-mathlib-alone**; proved via the cusp specialization `polyEval_cusp_φ` (also fork-local, NO-composable), needing `cusp`/`ringEval`/`polyToField`/`curve` |
| denom ≠ 0 | `ψᵤ_ne_zero` | ❌ **fork-local** — proved via `polyEval_cusp_ψ : ψₙ(1,1) = n` (the universal point's infinite order); mathlib has **no** general `ψₙ ≠ 0`/`normEDSₙ ≠ 0` for `n ≠ 0` (Phase 5 [D]) |

Attempt 1 (mirror the proof): fails as a *mathlib-only* composition — both `polyToField_φ_ne_zero`
and `ψᵤ_ne_zero` are project-local, and the absent-from-mathlib cusp/`ringEval`/universal apparatus
is load-bearing in each.

Attempt 2 (rebuild from mathlib's parametric API): mathlib's `natDegree_Φ`/`leadingCoeff_Φ` would
give `Φₙ ≠ 0` and the EDS degree theory would give `ψₙ ≠ 0` — but only for the **parametric**
`W.Φ`/`W.ψ` over a suitable base, a **different statement** about a different object; bridging to the
project-local `smulX = polyToField(curve.φ n)/(ψᵤ n)²` needs the (absent) universal-curve plumbing.
Not a ≤3-mathlib-call composition of *this* statement.

Conclusion: **NOT-COMPOSABLE from mathlib alone.** (It *is* a clean 3-leaf composition from
**fork + mathlib** — `div_ne_zero` ∘ (`polyToField_φ_ne_zero`, `pow_ne_zero ∘ ψᵤ_ne_zero`) — but
"fork + mathlib" is not the NO-composable bar, which requires mathlib-only.)

> Contrast with the `@[simp]` twin `smulX_zero` (verdict: **NO-composable-from-mathlib**): there the
> two ingredients were `ψ_zero` and `div_zero`, **both genuine mathlib primitives**, so `smulX 0 = 0`
> *is* a mathlib-only composition modulo unfolding the definition. Here the two ingredients
> (`polyToField_φ_ne_zero`, `ψᵤ_ne_zero`) are **fork-local and themselves not mathlib-composable** —
> so the symmetric "ne_zero" lemma falls on the other side of the NO-composable gate.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX_ne_zero`

**Category: BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): nonvanishing of `φₙ/ψₙ²` is routine well-definedness bookkeeping subordinate
  to two *named* facts — the multiplication formula `[n]P=(φₙ/ψₙ², ωₙ/ψₙ³)` and the coprimality
  `gcd(φₙ, ψₙ²)=1`. **No standalone citable "`smulX n ≠ 0`" theorem**; the denominator half is the
  standard EDS non-degeneracy ("generic point has infinite order"), which the cusp trick proves.
- Generality (Phase 4): **STRICTLY NARROWER in expression** — pinned to the single project-local
  universal object (`smulX`/`ψᵤ`/`polyToField`/`curve`), not a parametric `W : WeierstrassCurve R`.
  The mathlib-worthy kernel is the **parametric** `Φₙ ≠ 0` / `IsCoprime (Φₙ)(ΨSqₙ)` over an
  arbitrary base — a *different, stronger* declaration (cost EXPENSIVE). h0 is tight; modern-idiom
  (4c) = none for this lemma alone.
- Mathlib search (Phase 5): **absent** under both forms. `smulX`/`ψᵤ`/`polyToField`/`Universal` have
  **0** mathlib hits; mathlib's `DivisionPolynomial` has degrees + leading coefficients but **no**
  general `ψₙ ≠ 0`/`Φₙ ≠ 0`/coprimality. Only the generic combinators `div_ne_zero`/`pow_ne_zero`
  exist. → not NO-mathlib-has-it.
- Composition (Phase 6): **NOT-COMPOSABLE from mathlib alone** — both non-trivial leaves
  (`polyToField_φ_ne_zero`, `ψᵤ_ne_zero`) are fork-local and themselves not mathlib-composable
  (the cusp/infinite-order/`ringEval` apparatus is absent upstream). It is only a *fork + mathlib*
  composition, which the NO-composable gate explicitly excludes.

**Rationale.**
`smulX_ne_zero` is **fork-internal scaffolding**, not an independent mathlib candidate, and it sits
in exactly the configuration of its direct dependency `polyToField_φ_ne_zero` (verdict
BORDERLINE-needs-human). Its very *statement* names project-only objects — `smulX` (= `φₙ/ψₙ²` in the
universal function field), `ψᵤ`, `polyToField`, `Universal.Field`, `curve` — **every one absent from
mathlib** (0 grep hits; the universal-pointed-curve apparatus is precisely the part of the fork of
`Mathlib.AlgebraicGeometry.EllipticCurve.*` that is not upstream). So it cannot be proposed to
mathlib as written → **not NO-mathlib-has-it**.

Nor is it a clean mathlib composition. Although the proof reads as one `div_ne_zero`, its two leaves
— `polyToField_φ_ne_zero` (numerator ≠ 0) and `ψᵤ_ne_zero` (denominator ≠ 0) — are **both fork-local
and not mathlib-composable**: each is established by specializing the generic curve to the cuspidal
cubic at `(1,1)` (`polyEval_cusp_φ = 1`, `polyEval_cusp_ψ = n`), i.e. by the universal-point
infinite-order argument, all of which (`cusp`, `ringEval`, `polyEval_cusp_*`) is absent upstream.
This is **decisively different from the `@[simp]` twin `smulX_zero`** (verdict NO-composable): there
the two ingredients (`ψ_zero`, `div_zero`) were genuine mathlib primitives, so the boundary lemma was
a mathlib-only one-`simp`; here the symmetric ne_zero lemma's ingredients are fork lemmas, so it fails
the NO-composable gate (which requires Phase 6 to conclude COMPOSABLE-from-mathlib-**alone**).

With the subject objects absent, the proof not mathlib-composable, and the only mathlib content being
the two generic combinators `div_ne_zero`/`pow_ne_zero`, what remains is a **judgment call about the
fork's universal-curve strategy** — precisely the BORDERLINE situation. The genuinely mathlib-able
object nearby is the **parametric** nonvanishing/coprimality of the division polynomials
(`Φₙ ≠ 0`, `IsCoprime (Φₙ)(ΨSqₙ)` for any `W : WeierstrassCurve R`), which mathlib lacks and which is
the natural next layer above its `natDegree_Φ`/`leadingCoeff_Φ` — a **separate, generalise-first /
future-PR** target, not this decl.

**WHY (refactor-actionable) — supporting the BORDERLINE call.**
This whole NagellLutz/ZSMul development (`zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ, ψₙ)`) fills a known
gap in mathlib's elliptic-curve API — mathlib defines `ψ, φ, ω` but **nowhere** proves they compute
the multiplication-by-`n` map, and a fortiori nowhere proves the attendant nonvanishing. If and only
if that whole `WeierstrassCurve.Universal.Affine` layer is upstreamed (it is Junyan Xu's
mathlib-PR-in-progress: Apache header, mathlib style, a richer `EllipticDivisibilitySequence` fork),
`smulX_ne_zero` rides along as a trivial well-definedness companion next to `smulX`/`smulX_zero` — it
is **never a standalone candidate**. The atomic PR grain is the development (with siblings
`smulX_eq`, `smulX_sub_smulX`, `smulX_ne_smulX`, `smulY_*`, and the capstone `zsmul_eq_smulEval`),
gated behind upstreaming the forked richer `net`/`rel₄` EDS API first. The decision a human owns:
whether to upstream the universal-curve strategy at all (vs. proving the parametric coprimality
`gcd(φₙ, ψₙ²) = 1` directly over an arbitrary base, from which both nonvanishing halves follow without
any universal-curve / cusp machinery).

**Numbered questions (BORDERLINE — ≤5):**
1. Upstream the **whole** universal-curve / `zsmul_eq_smulEval` development (carrying `smulX_ne_zero`
   along as glue), or instead prove the **parametric** division-polynomial nonvanishing/coprimality
   (`Φₙ ≠ 0`, `IsCoprime (Φₙ)(ΨSqₙ)` over any base) and derive everything from that?
2. Is the cuspidal-specialization proof of `ψₙ ≠ 0` (`ψₙ(1,1) = n`) the strategy mathlib wants, or
   should mathlib first get a general "`normEDS`/`ψ` is non-degenerate: `ψₙ = 0 ⇔ n = 0`" lemma
   (currently absent, Phase 5) that this could consume?
3. Prerequisite ordering: the forked richer `EllipticDivisibilitySequence` (`net`/`rel₄`/`Rel₃`) is a
   dependency and is itself not upstream — land it first?
4. Dedup: the verbatim HasseWeil copy (`Auxiliary/DivisionPolynomial.lean:261`) — consolidate the
   shared `Universal` layer into `Common/` on `main` before any upstreaming?

**Bucket: `BORDERLINE-needs-human`.**

---

## Next step

Human call: decide Q1 (universal-curve strategy vs. parametric coprimality). Treat `smulX_ne_zero`
**not** as a standalone PR but as one trivial well-definedness piece of the larger ZSMul /
universal-curve upstreaming (with the richer EDS `net` API as a prerequisite PR), and fold the
HasseWeil duplicate via a `Common/` dedup on `main` first.
