# /mathlibable report — `WeierstrassCurve.Universal.evalEval_ψ₂`

## Verdict: **NO-composable-from-mathlib**

> **One-line.** A one-line glue lemma whose **statement mentions the project-local `polyEval`
> and `Universal.curve`** (neither in mathlib). Its mathematical content — `ψ₂` commutes with the
> specialization map — is already mathlib's `WeierstrassCurve.map_ψ₂`; the lemma is the exact
> ≤3-call composition `map_ψ₂` + `map_specialize` + the project's own `polyEval_apply`
> (which is itself `Polynomial.eval₂_eval₂RingHom_apply`). Cannot be upstreamed as-is (its subject
> is a downstream def); the building blocks already live upstream. **Identical shape and disposition
> to its decided siblings** `evalEval_Ψ₃`, `evalEval_preΨ₄`, `polyEval_apply`. The live human
> question — "upstream the whole universal-curve scaffold?" — is owned by the package anchors
> `specialize.md` / `curve.md` (both BORDERLINE), not by this glue lemma.

> Step-9 (overview) mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration. Generated 2026-06-22.
> Repo root `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Source: `projects/NagellLutz/LutzNagell/ZSMul.lean:88`.

---

## Baseline (Phase 0)

- lake build:                stale (per task brief; local build not re-run). HOWEVER the upstream
  mathlib sources are present under `.lake/packages/mathlib/` (pin `leanprover/lean4:v4.32.0-rc1`),
  so **every mathlib claim below was VERIFIED against actual upstream source**, not merely reasoned.
- decl `WeierstrassCurve.Universal.evalEval_ψ₂`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:88`.
- **qualified name VERIFIED:** the prompt's parse `WeierstrassCurve.Universal.evalEval_ψ₂` is
  **correct**. The lemma sits inside `namespace WeierstrassCurve` (opened `ZSMul.lean:76`) →
  `namespace Universal` (opened `ZSMul.lean:86`), under
  `variable {R S} [CommRing R] [CommRing S] (W : WeierstrassCurve R)` and `variable {x y : R}`.
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Integer multiples of a rational point on an elliptic curve in terms of
  division polynomials" — proves `WeierstrassCurve.zsmul_eq_smulEval` (`n • P` in Jacobian
  coordinates via division polynomials), routed through the **universal Weierstrass curve** and the
  `polyEval`/`ringEval` specialization machinery defined in `LutzNagell/Universal.lean`.

**Exact statement (source, `ZSMul.lean:88–89`):**
```lean
lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]
```

---

## Statement (Phase 1)

`WeierstrassCurve.Universal.evalEval_ψ₂` is a **naturality / compatibility lemma** for the
2-division polynomial under specialization of the *universal* Weierstrass curve.

In prose: let `curve` be the universal Weierstrass curve over `ℤ[A₁,A₂,A₃,A₄,A₆]` (its
`aᵢ = MvPolynomial.X Aᵢ`), and let `W` be any Weierstrass curve over a commutative ring `R`. The
universal 2-division polynomial `curve.ψ₂ ∈ (ℤ[A₁,…,A₆])[X][Y]` can be pushed to `R` in two ways
that agree:

* **left side** — first form `W`'s own 2-division polynomial `W.ψ₂ ∈ R[X][Y]`, then evaluate it at
  the point `(x,y)` (the bivariate `evalEval`);
* **right side** — apply `polyEval W x y` to `curve.ψ₂`, i.e. specialize the coefficient variables
  `Aᵢ ↦ W.aᵢ` (the ring hom `W.specialize`) **and** evaluate `X,Y ↦ x,y` in one combined step.

So the lemma says `ψ₂` *commutes with the curve-specialization map* — the `φ = W.specialize`
instance of "division polynomials are natural under base change."

Variables / typeclasses involved (Lean side):
- `{R S : Type*}` `[CommRing R]` `[CommRing S]` — base rings (only `R` is used here).
- `(W : WeierstrassCurve R)` — an arbitrary Weierstrass curve over `R`.
- `{x y : R}` — coordinates of a point in the affine plane over `R`.

Project-local objects in the statement (**NONE of which are in mathlib**):
- `WeierstrassCurve.Universal.curve : Affine (MvPolynomial Coeff ℤ)` — the universal curve
  (`Universal.lean:84`). `Coeff` is a project-local 5-element inductive (`Universal.lean:73`).
- `WeierstrassCurve.Universal.polyEval W x y : Poly →+* R` — point-evaluation specialization hom,
  `= eval₂RingHom (eval₂RingHom W.specialize x) y` (`Universal.lean:203`); `Poly := (MvPolynomial Coeff ℤ)[X][Y]`.
- (used in proof) `WeierstrassCurve.specialize`, `map_specialize`, `polyEval_apply`.

Mathlib objects in the statement:
- `WeierstrassCurve.ψ₂` — the 2-division polynomial `2Y + a₁X + a₃`
  (`Mathlib/.../DivisionPolynomial/Basic.lean:113`; here forked into `LutzNagell/DivisionPolynomial.lean:36`).
- `Polynomial.evalEval` — bivariate evaluation `R[X][Y] → R` (`Mathlib/Algebra/Polynomial/Bivariate.lean`).

Hypotheses (Lean side): none beyond the typeclasses.

Conclusion (math): `evalEval_{(x,y)}(ψ₂^W) = (σ_W ⊗ ev_{(x,y)})(ψ₂^{E_univ})` — `ψ₂` is natural for
the specialization `σ_W = W.specialize`.

Conclusion (Lean): `W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂` (an equality in `R`).

Proof body (3 rewrites): `simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]`.
- `polyEval_apply` ⟶ RHS becomes `(curve.ψ₂.map (mapRingHom W.specialize)).evalEval x y`.
- `← map_ψ₂` ⟶ `curve.ψ₂.map (mapRingHom W.specialize) = (curve.map W.specialize).ψ₂`.
- `map_specialize` ⟶ `curve.map W.specialize = W`, so RHS = `W.ψ₂.evalEval x y` = LHS. ∎

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper/glue lemma — the naturality of `ψ₂` for one specific ring map, consumed
internally to rewrite `normEDS`/`complEDS₂` expansions of `ψ`/`ψc`. Not a named theorem, not a main
result, introduces no new structure. (Literature width was run EXHAUSTIVE regardless.) Note: this is
the `ψ₂`-rung of a fixed triple `{evalEval_ψ₂, evalEval_Ψ₃, evalEval_preΨ₄}` used together; the
*concept-carrying* members of this track are the defs `Universal.curve` / `specialize` (BIG/anchor),
assessed separately.

## One-line check (Phase 2b)

Body line count: 1 substantive line — but kind is **lemma**, so the one-liner-**def** heuristic does
not apply. A `lemma`/`theorem` with a one-line proof is normal and carries no negative inclusion
signal. n/a.

Conclusion: n/a — declaration kind is lemma, not def. (The negative signal for this track lives on
the *defs* `polyEval`/`specialize`, handled in their own reports.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomial Weierstrass curve compatible with base change specialization universal curve         | yes  | `ψ_n ∈ Z[a₁..a₆,x,y]`; "designed to work functorially across specializations of the universal curve" | confirms the *setup* (universal ring, base-change compatibility) but no isolated named lemma for the σ_W-evaluation identity |
|  2 | WebSearch (general form)         | universal Weierstrass curve division polynomial evaluation specialization homomorphism coefficients       | yes  | universal curve over `Frac(Z[a₁..a₆])`; named transform is the **coordinate-change scaling law** `ψ_n(x',y',E') = u^{n²−1}ψ_n(x,y,E)` | the *named* base-change result is the `u`-scaling law — a **different** statement from "natural under σ_W" |
|  3 | WebSearch (named-after / aliases)| "division polynomial" naturality base change ring homomorphism map functorial elliptic curve lemma        | yes  | (sources: MIT 18.783 L5, Stange, Ayad/Cassels)   | explicitly: results "**don't specifically address the functorial properties w.r.t. ring homomorphisms / naturality**" — i.e. it is treated as implicit/folklore, not a standalone theorem |
|  4 | ChatGPT MCP                      | "Is the σ_W-specialization-evaluation compatibility for ψ₂ a named citable theorem or a trivial corollary of base-change functoriality? + most-general form + historical evolution" | n/a  | —                                                | **MCP unavailable** (Codex backend down, per task brief — error returned). Fallback = WebSearch #1–3 + decided local siblings; the question is already answered conclusively by #2/#3 (folklore corollary, not a named theorem). |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial" / "specialize"                              | n/a  | (no `references/` dir in NagellLutz)             | directory absent — recorded n/a |
|  6 | nLab                             | division polynomial / universal elliptic curve                                                          | n/a  | —                                                | nLab has no division-polynomial naturality page; this is classical NT, not a categorical concept it indexes |
|  7 | nCatLab                          | —                                                                                                       | n/a  | —                                                | not a higher-categorical concept |
|  8 | Stacks Project                   | division polynomial                                                                                      | n/a  | —                                                | Stacks has no elliptic-curve division-polynomial material; not its scope |
|  9 | MathOverflow / Math.SE           | division polynomial commutes with base change / ring homomorphism                                         | yes  | scattered: "division polynomials are universal / defined over `Z[a_i]`, so base change is automatic" | community treats σ_W-compatibility as obvious-by-universality — confirms folklore status |
| 10 | recent arXiv (last 5 yrs)        | Stange 2025 "Division polynomials for arbitrary isogenies"; Ayad; "p-adic properties of division polys"   | yes  | division polys = "generic EDS over `Q[x,y,A,B]/(…)`" | the universal/generic framing is standard; nobody isolates the evaluation-at-σ_W identity as a result |

### Literature summary (Phase 3)

Concept identified as: **functoriality / naturality of division polynomials under base change**
(specifically the `φ = W.specialize` instance), with the universal/generic curve over `ℤ[a₁,…,a₆]`
as the representing object.
Sources agree on the standard form: **yes** — division polynomials live in `ℤ[a₁,…,a₆,x,y]` and are
the *generic* sequence, from which any curve's `ψ_n` is obtained by specializing `aᵢ`. The
σ_W-compatibility is therefore automatic.
Most general standard form: `ψ_n` **commutes with arbitrary ring homomorphisms** `φ : R → S`:
`(φ.map W).ψ_n = (W.ψ_n).map φ` — i.e. `ψ_n` is a natural transformation of the base-change functor.
**Mathlib already encodes exactly this** as `WeierstrassCurve.map_ψ₂` (and `map_ψ`, `map_Ψ₃`, …).
Generality dimensions where the literature varies:
  - **kind of map**: classical sources state only the *admissible coordinate-change scaling law*
    `ψ_n(x',y',E') = u^{n²−1}ψ_n(x,y,E)` (a NAMED result); the modern statement weakens this to
    *any* ring map `φ` with the trivial `u=1` naturality being `map_ψ_n`. Our lemma is the latter,
    specialized to `φ = σ_W` and then post-composed with evaluation.
Disagreement with the literature: **none** — the lemma is a correct, trivial instance of the
standard naturality; it just is not a *named* standalone result (the named result is the `u`-scaling
law, which this is not).

**Signal:** the literature has the *general naturality* (= mathlib's `map_ψ₂`) and the *named scaling
law* (different), but **nothing names the evaluate-after-specialize identity** for a fixed `ψ₂`. That
points away from "novel standalone contribution" and toward "trivial corollary of `map_ψ₂` + the
universal-curve packaging."

---

## Generality analysis (Phase 4)

Literature-standard / mathlib-idiomatic form (from Phase 3): `ψ₂` is natural under arbitrary ring
maps — `WeierstrassCurve.map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)` (upstream).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker / more-general form exists? | Reason |
|---|---|---|---|---|---|
| 1 | the ring map | hard-coded to `W.specialize : ℤ[A₁..A₆] → R` (via `polyEval`/`curve`) | arbitrary `f : R →+* S` | **YES — already upstream** | the general naturality is `map_ψ₂` for any `f`; this lemma is the `f = W.specialize` instance, *plus* post-composition with `evalEval x y`. The general statement is strictly more general and already in mathlib. |
| 2 | the curve | fixed to `Universal.curve` (the representing object) | any `W` | n/a | universal curve is the most general *source*; but that is the `polyEval`/`curve` packaging, not a hypothesis to weaken on this lemma |
| 3 | `[CommRing R]` | comm ring | comm ring | NO | already maximal for division polynomials |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**, but *not in a way that yields a YES-but-
generalise-first target* — because the strictly-more-general statement (naturality of `ψ₂` under an
arbitrary ring map) **already exists upstream as `map_ψ₂`**. There is nothing to *prove* by
generalising; the general form is mathlib's and this lemma is a downstream *instantiation +
evaluation* of it. So the relevant axis is composition (Phase 6), not generalisation.
Number of weakening opportunities that produce a new upstreamable lemma: **0**.
Cost of "restatement": n/a — the general lemma is already in mathlib.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
|  1 | bundled-hyp → typeclass? | no | — | no "let X be a foo" preamble; it is an equation |
|  2 | sequences/metric → filters/topology? | no | — | purely algebraic identity |
|  3 | construction → universal-property class? | **partly** | the *whole track* is a universal-curve construction; the universal property is already `map_specialize`. For **this lemma**, the modern idiom is simply "use `map_ψ₂` (arbitrary `f`) + `eval₂_eval₂RingHom_apply`", not ship a `σ_W`-specific wrapper | composes with the full `map_*`/`eval₂RingHom` API |
|  4 | set+closure → bundled substructure? | no | — | n/a |
|  5 | field/metric-specific → weaken typeclass? | no | — | already `CommRing` |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index → general monoid/group? | no | — | `ψ₂` is the fixed index-2 polynomial |

Modern idiom available: **no new upstreamable form.** The "modern" move is exactly to **not** have a
`W.specialize`-bundled lemma and instead apply the already-general `map_ψ₂` + the bivariate
evaluation lemma at the call site — which is the NO-composable conclusion, not a YES-but-generalise
target. One-line reason: the general statement is already `map_ψ₂`; the only thing this lemma adds is
the `polyEval`/`curve` packaging, whose fate is the BORDERLINE package question, not a modernisation.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (a `Prop`-valued equality). It introduces no definitional
equality, no typeclass-search path, no instance, no coercion. (The defs that *do* carry such risk —
`polyEval`, `specialize`, `curve` — are assessed in their own reports.)

---

## Mathlib search — five-method (Phase 5)

Target forms searched: (a) the user's `σ_W`-evaluation identity for `ψ₂`; (b) the general naturality
`(W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)`; (c) the bivariate "specialize-coeffs-then-evaluate" lemma.

```
[A] Lean-Finder       "ψ₂ commutes with base change / map"        → general form HIT: map_ψ₂
[B] Loogle            (W.map f).ψ₂ = _ ; eval₂RingHom ∘ eval₂RingHom → HITS: map_ψ₂; eval₂RingHom_eval₂RingHom
[C] LeanSearch        "division polynomial under ring homomorphism" → HIT: WeierstrassCurve.map_ψ₂
[D] Grep mathlib src  "map_ψ₂", "eval₂_eval₂RingHom_apply", "polyEval", "Universal.curve", "evalEval_ψ" → see below
[E] Name pattern      evalEval_ψ₂ / polyEval / Universal in Mathlib/AlgebraicGeometry → NO hits (not upstream)
```

Grep facts (VERIFIED against `.lake/packages/mathlib/`, pin `v4.32.0-rc1`):
- `WeierstrassCurve.map_ψ₂` — **upstream**, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:498`:
  `(W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)`. This is the **general naturality** of which our lemma is
  an instance. (The project's `LutzNagell/DivisionPolynomial.lean:421` is a verbatim fork of it.)
- `Polynomial.eval₂_eval₂RingHom_apply` — **upstream**, `Mathlib/Algebra/Polynomial/Bivariate.lean:194`:
  `eval₂RingHom (eval₂RingHom f x) y p = (p.map (mapRingHom f)).evalEval x y`. This is **exactly the
  project's `polyEval_apply`** (whose entire proof is `eval₂_eval₂RingHom_apply _ _ _ _`).
- `Polynomial.eval₂RingHom_eval₂RingHom` (`Bivariate.lean:189`), `Polynomial.evalEval` /
  `evalEvalRingHom` (`Bivariate.lean:151/388`) — all upstream.
- `polyEval`, `Universal.curve`, `Coeff`, `specialize`, `evalEval_ψ₂` in
  `Mathlib/AlgebraicGeometry/EllipticCurve/**` → **NONE** (grep empty). The entire `Universal`
  namespace is a project addition; its module docstring states it provides "lemmas missing from the
  released mathlib," and `DivisionPolynomial/Basic.lean` only *TODO*s the universal `ωₙ` morphism.

Concluded: **"not in mathlib as a standalone lemma"** for the user's `σ_W`-evaluation form (its very
subjects `polyEval`/`curve` are not upstream). BUT mathlib has **every building block**: the general
naturality `map_ψ₂`, the universal-property `map_specialize` analogue input, and the bivariate
specialize-evaluate lemma `eval₂_eval₂RingHom_apply`. So the honest classification is *composable*,
not "already present verbatim."

---

## Composition check + call-sites (Phase 6)

### Call sites — `WeierstrassCurve.Universal.evalEval_ψ₂`

Internal use count (NagellLutz, excluding the declaring line `ZSMul.lean:88`): **K = 2**
External-to-file callers: 0 outside `ZSMul.lean` within NagellLutz; **1 verbatim twin in HasseWeil**.

| Caller file:line                  | Usage pattern (one-line excerpt)                                                        |
|-----------------------------------|------------------------------------------------------------------------------------------|
| `LutzNagell/ZSMul.lean:115`       | `rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, …]` (in `polyEval_cusp_ψ`) |
| `LutzNagell/ZSMul.lean:123`       | `rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]` (in `polyEval_cusp_ψc`) |

Both sites use it **only as part of the fixed triple** `{evalEval_ψ₂, evalEval_Ψ₃, evalEval_preΨ₄}`,
to rewrite the `normEDS`/`compl₂EDS` form of `ψ`/`ψc` on the cusp curve into per-coordinate
evaluations. Real (if small) internal API; **no inline re-derivation** bypasses it.

Inline-derivation grep (re-derived without `evalEval_ψ₂`?): none in NagellLutz.

Duplication signal: `evalEval_ψ₂` is **duplicated verbatim** in
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:163` (with the same `polyEval`/`curve`
scaffold under `HasseWeil/Auxiliary/Universal.lean`). Independent AINTLIB dedup concern (→ `Common/`).

### Composition (Phase 6a)

Can `evalEval_ψ₂` be derived from mathlib (+ the package's own glue) in ≤3 chained calls? **Yes — the
source proof literally is that composition.**

```
Attempt 1 (the actual proof):
  simp_rw [polyEval_apply,   -- = Polynomial.eval₂_eval₂RingHom_apply   (UPSTREAM, Bivariate.lean:194)
           ← map_ψ₂,          -- = WeierstrassCurve.map_ψ₂              (UPSTREAM, Basic.lean:498)
           map_specialize]    -- universal property of `curve`         (package glue; the curve-side input)
  Mathlib decls used: Polynomial.eval₂_eval₂RingHom_apply, WeierstrassCurve.map_ψ₂.
  Package glue used:  polyEval_apply (= the upstream lemma instantiated), map_specialize.
  Result: succeeds — exactly 3 rewrites, no `ring`/`aesop`/new reasoning.
```

Conclusion: **COMPOSABLE.** Two of the three rewrites are upstream mathlib lemmas; the third
(`map_specialize`) and the wrapper `polyEval_apply` are members of the *same un-upstreamed
universal-curve package*. No new mathematical content is created by `evalEval_ψ₂` — it bundles
`map_ψ₂` + the package's specialization-evaluation into one named convenience step. (Composition
heuristic table: this is the "`Foo.bar (Bar.baz hx)` / `simp_rw [3 named lemmas]`" pattern — yes,
composable; not a disguised proof.)

---

## Verdict (Phase 7)

## Verdict: `WeierstrassCurve.Universal.evalEval_ψ₂`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature (Phase 3): the general naturality of `ψ₂` under ring maps is standard and = mathlib's
  `map_ψ₂`; the only *named* base-change result is the `u^{n²−1}` coordinate-change scaling law
  (a different statement). No source names the evaluate-after-specialize identity — folklore.
- Generality (Phase 4): STRICTLY NARROWER than the standard naturality, but the more-general form
  **already exists upstream** (`map_ψ₂`) → no YES-but-generalise target; 0 new upstreamable weakenings.
- Mathlib search (Phase 5): not upstream as-is (subjects `polyEval`/`curve` aren't in mathlib), but
  **all building blocks are** — `map_ψ₂` (`Basic.lean:498`) + `eval₂_eval₂RingHom_apply`
  (`Bivariate.lean:194`), the latter being exactly the project's `polyEval_apply`.
- Composition (Phase 6): **COMPOSABLE** — the source proof is the ≤3-call composition itself.

**Rationale.**
`evalEval_ψ₂` cannot go into mathlib *as written*, because its statement names two objects that are
not in mathlib and (per the sibling assessments) may never be: `Universal.curve` and `polyEval`.
But it is not a contribution mathlib is *missing* either — its entire mathematical content is the
naturality `(W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)`, which is already upstream as
`WeierstrassCurve.map_ψ₂`. The lemma merely instantiates that at `f = W.specialize` and post-composes
with bivariate evaluation, a step mathlib already packages as `Polynomial.eval₂_eval₂RingHom_apply`
(= the project's own `polyEval_apply`). The three-rewrite proof `simp_rw [polyEval_apply, ← map_ψ₂,
map_specialize]` *is* the composition. So as a standalone declaration the disposition is
NO-composable-from-mathlib: keep it locally as a one-line convenience for the `polyEval` track, but
there is nothing here to upstream beyond what `map_ψ₂` already provides.

This verdict is **explicitly consistent with its decided siblings.** `evalEval_Ψ₃.md`,
`evalEval_preΨ₄.md` (identical shape — `map_Ψ₃`/`map_preΨ₄` in place of `map_ψ₂`) and `polyEval.md` /
`polyEval_apply` were all assessed **NO-composable-from-mathlib** for exactly this reason
(statement is about `polyEval`/`curve`; content is a single upstream lemma applied). `evalEval_Ψ₃.md`
even names `evalEval_ψ₂` by hand as sharing its disposition. The decl rides *below* the genuinely-
borderline **anchors** of the same track — `specialize.md` and `curve.md`, both
**BORDERLINE-needs-human** on the one real question: *should the whole universal-curve scaffold
(`Coeff`, `Universal.curve`, `specialize`/`map_specialize`, `polyEval`/`ringEval`, closing the `ωₙ`
TODO in `DivisionPolynomial/Basic.lean`) be upstreamed as one package?* If yes, `evalEval_ψ₂` rides
along as a package member; if no, it is inlined/dropped. Either way it adds no upstreamable content
of its own, so the single-declaration verdict is NO-composable-from-mathlib — the package decision is
not re-litigated here (that would double-count `specialize.md`'s BORDERLINE).

**WHY not (refactor-actionable).**
Mathlib has the building blocks; `evalEval_ψ₂` is a ≤3-call composition of them.
- Mathlib building blocks:
  - `WeierstrassCurve.map_ψ₂` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:498`
  - `Polynomial.eval₂_eval₂RingHom_apply` — `Mathlib/Algebra/Polynomial/Bivariate.lean:194`
    (this is precisely the project's `polyEval_apply`, `Universal.lean:206`)
  - package input: `WeierstrassCurve.map_specialize` (`Universal.lean:194`) — the universal property
    of `Universal.curve` (itself BORDERLINE under `curve.md`/`specialize.md`)
- Composition sketch (= the actual proof):
  ```lean
  example : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
    simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]
  ```
- Call sites in our project (Phase 6.0): **K = 2** — `ZSMul.lean:115`, `ZSMul.lean:123`, both inside
  the `{evalEval_ψ₂, evalEval_Ψ₃, evalEval_preΨ₄}` triple.
- **Refactor plan (conditional — do NOT delete unilaterally).** This lemma's fate is *tied to the
  package* (`specialize.md` Q1), so the action is gated:
  1. **If the universal-curve scaffold is upstreamed** (per `specialize.md`/`curve.md`): `evalEval_ψ₂`
     ships as-is alongside `polyEval_apply`/`map_specialize` as a package convenience lemma. No change.
  2. **If the scaffold is inlined/dropped**: at the K=2 call sites, the triple `← evalEval_ψ₂,
     ← evalEval_Ψ₃, ← evalEval_preΨ₄` is the bridge from `W.ψ₂.evalEval x y` to
     `polyEval W x y curve.ψ₂`; replace each with the inline `simp_rw [polyEval_apply, ← map_ψ₂,
     map_specialize]` (resp. `map_Ψ₃`, `map_preΨ₄`) — i.e. inline this lemma's one-line proof at use
     sites — and delete `evalEval_ψ₂`.
  3. **Independently of the mathlib decision** (AINTLIB cleanup): the lemma + its scaffold are
     **duplicated verbatim** in `HasseWeil/Auxiliary/DivisionPolynomial.lean:163` — file a dedup
     ticket to lift the shared `Universal`/division-polynomial glue into `Common/`.

**Next action:** none blocking for `evalEval_ψ₂` as a single decl (NO-composable). The live human
decision is the **package-level** one tracked in `specialize.md` (Q1: upstream the whole
universal-curve scaffold vs. inline the `aeval`/`eval₂RingHom` idiom). Separately, dedup the
NagellLutz ↔ HasseWeil verbatim copy into `Common/`.

---

## Cross-references
- **Package anchors (the real BORDERLINE questions):** `specialize.md`, `curve.md`,
  `polyEval.md` (NO-composable), `map_specialize.md` (BORDERLINE), `ringEval.md`.
- **Identical-shape siblings (same NO-composable disposition):** `evalEval_Ψ₃.md`,
  `evalEval_preΨ₄.md`, `polyEval_apply` — the `{ψ₂, Ψ₃, preΨ₄}` evaluation triple. Distinguish from
  the *within-curve* `evalEval_*_eq_*` lemmas (`evalEval_ψ_eq_evalEval_Ψ`, `evalEval_eq_of_mk_eq`,
  `evalEval_Ψ_sq_eq_eval_ΨSq`), also NO-composable but via `AdjoinRoot.evalEval_mk`/`mk_ψ₂_sq`.
- **Upstream lemma that subsumes the math content:** `WeierstrassCurve.map_ψ₂`
  (`Mathlib/.../DivisionPolynomial/Basic.lean:498`).
