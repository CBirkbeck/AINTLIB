# /mathlibable report — `WeierstrassCurve.Universal.polyEval_apply`

> Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> This project **forks** parts of mathlib (`…EllipticCurve.DivisionPolynomial.*`,
> `…EllipticDivisibilitySequence`) and carries a duplicated `Universal.lean`
> (identical copy in `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:209`).

---

### Baseline (Phase 0)
- lake build:               (stale per prompt — reasoned from source; the decl is a one-liner that elaborates against an in-mathlib lemma, see Phase 5)
- decl `WeierstrassCurve.Universal.polyEval_apply`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:206`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Defines the universal Weierstrass curve over `ℤ[A₁..A₆]`, the specialization hom `W.specialize`, and the point-evaluation homs `polyEval`/`ringEval`; supplies Point.lean additions missing from released mathlib.

---

### Statement (Phase 1)

`polyEval_apply` is a lemma. With `W : WeierstrassCurve R` (`R` a comm ring) and a
point `(x, y) ∈ R²`, the project defines

```
polyEval W x y : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y
```

where `Poly = (MvPolynomial Coeff ℤ)[X][Y] = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]` and
`W.specialize : ℤ[A₁..A₆] →+* R` sends each coefficient variable `Aᵢ` to `W.aᵢ`.
The lemma states that evaluating a bivariate polynomial `p` through this composite
equals first mapping its coefficient ring through `W.specialize` and then doing the
ordinary bivariate evaluation `evalEval` at `(x, y)`:

  `polyEval W x y p = (p.map (mapRingHom W.specialize)).evalEval x y`.

Variables / typeclasses (Lean side):
- `R : Type*`, `[CommRing R]` — the target ring of definition.
- `W : WeierstrassCurve R` — supplies `W.specialize` (project-local def).
- `x y : R` — the affine-plane point.
- `p : Poly` — the bivariate polynomial being evaluated.

Hypotheses: none.

Conclusion (math): the two-step nested `eval₂` of a bivariate polynomial through a
ring hom `f` (here `f = W.specialize`) equals `map f` followed by `evalEval` at the point.

Conclusion (Lean): `polyEval W x y p = (p.map (mapRingHom W.specialize)).evalEval x y`.

**Crucial structural fact.** `polyEval W x y p` is *definitionally* `eval₂ (eval₂RingHom W.specialize x) y p`. So the lemma is exactly the instance of the general bivariate identity at `f := W.specialize`, with `f` ranging over an arbitrary ring hom in the general statement. The proof is one term:

```
polyEval_apply p := eval₂_eval₂RingHom_apply _ _ _ _
```

i.e. mathlib's `Polynomial.eval₂_eval₂RingHom_apply` applied with `f := W.specialize, x, y, p`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A glue/unfolding lemma for the project-local `polyEval`; not a named theorem, not a `Main results` entry, not a new structure. (Lit width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`eval₂_eval₂RingHom_apply _ _ _ _`).
One-liner verdict: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (The Phase 2b
def-exemption table is for definitions; a one-line *lemma* is simply a strong
"reuse mathlib" signal, recorded for Phase 7.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | universal Weierstrass curve specialization homomorphism polynomial ring coefficients division polynomial | yes | universal curve over `ℤ[a₁..a₆][x,y]`; specialize `ρ:R→S`; expansion commutes with base change | arXiv 1303.4327, 1303.5002, 2109.10233 — the *content* (division polys under specialization), never names this trivial eval identity |
| 2 | WebSearch (general form) | bivariate polynomial eval2 ring homomorphism evalEval base change map nLab | yes | `evalEval`/`evalEvalRingHom` = bivariate evaluation as ring hom | Mathlib4 docs (Bivariate); PlanetMath/ProofWiki give the 1-var evaluation-hom universal property; nLab "polynomial" |
| 3 | WebSearch (named-after / aliases) | "eval₂RingHom" composition map evalEval Mathlib bivariate polynomial elliptic curve | yes | `eval₂ (eval₂RingHom f x) y p = evalEval x y (map (mapRingHom f) p)` | **mathlib4 docs return the exact general lemma** — this is `Polynomial.eval₂_eval₂RingHom_apply` |
| 4 | ChatGPT MCP | (server down per prompt — fallback) | n/a | — | Compensated with extra WebSearch passes (#1–#3) at three generality levels + direct mathlib-source read (Phase 5 [D]) |
| 5 | Local references | `.mathlib-quality/references/` in NagellLutz | n/a | (no references dir present) | Only `overview/` exists under `.mathlib-quality/` |
| 6 | nLab | "polynomial" / evaluation homomorphism | yes (weak) | polynomial ring = free comm algebra; evaluation = the universal-property counit | Confirms `eval₂`/`evalEval` is the standard universal-property evaluation; no special name for the nesting identity |
| 7 | nCatLab | (categorical?) | n/a | — | Not a categorical concept; it is concrete polynomial-algebra bookkeeping |
| 8 | Stacks Project | base change of polynomial evaluation | n/a | — | Concept = elementary `R[X][Y]` evaluation; below Stacks' granularity (no scheme-theoretic content here) |
| 9 | MathOverflow / MSE | nested polynomial evaluation as composition of maps | n/a (none specific) | — | No MO/MSE question isolates this identity; it is "obvious" folklore (functoriality of evaluation) |
| 10 | recent arXiv (≤5y) | (covered by #1) division polynomials universal curve specialization | yes | base-change-commutes statements for division polys | arXiv 2109.10233 (Gušić–Tadić specialization), 1303.5002 — content level, not this lemma |

Protocol pass check: WebSearch ran 3 distinct queries at three generality levels (specific
universal-curve form #1, general bivariate-eval form #2, exact-spelling/aliases #3) — PASS.
ChatGPT MCP unavailable (prompt: down) — compensated per the table. Local refs checked (absent).
nLab checked. Stacks/nCatLab/MO/arXiv each checked or `n/a` with reason. PASS.

### Literature summary (Phase 3)

Concept identified as: **functoriality of bivariate polynomial evaluation** — nested
`eval₂` through a coefficient ring hom `f` equals "map coefficients by `f`, then evaluate".
The *surrounding* mathematics (specialization of the universal Weierstrass curve, base change
of division polynomials) is well documented (arXiv 1303.4327, 1303.5002, 2109.10233); this
particular lemma is the trivial substitution step inside that story.

Sources agree on the standard form: yes — both the literature (evaluation as the
universal-property counit) and mathlib agree the canonical statement is over an arbitrary
ring hom `f : R →+* S`, not a curve-specific `specialize`.
Most general standard form: for any `f : R →+* S`, `x y : S`, `p : R[X][Y]`:
`eval₂ (eval₂RingHom f x) y p = (p.map (mapRingHom f)).evalEval x y`.
Generality dimensions where the literature varies:
  - the coefficient map: literature/mathlib state it for **any** ring hom `f`; the project's
    lemma fixes `f = W.specialize` — strictly narrower (a specialisation, not a generalisation).
Disagreement with the literature: none. The project form is the general form with `f` instantiated.

---

### Generality analysis — `WeierstrassCurve.Universal.polyEval_apply`

Literature-standard form (Phase 3): `eval₂ (eval₂RingHom f x) y p = (p.map (mapRingHom f)).evalEval x y`, any `f : R →+* S`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | the coefficient map `W.specialize` | a *specific* hom `ℤ[A₁..A₆] →+* R` baked into `polyEval` | an **arbitrary** `f : R →+* S` | yes — fully generalisable | The proof uses nothing about `specialize`; it is `eval₂_eval₂RingHom_apply` verbatim. The general form already exists in mathlib (Phase 5). |
| 2 | base ring `R` | `[CommRing R]` | `[CommSemiring R] [CommSemiring S]` (mathlib's actual context) | yes | mathlib's `eval₂_eval₂RingHom_apply` lives in the comm-semiring section — even weaker than this lemma's `CommRing`. |
| 3 | `Poly = ℤ[A₁..A₆][X][Y]` | fixed coefficient ring `MvPolynomial Coeff ℤ` | any `R[X][Y]` | yes | nothing uses the MvPolynomial structure. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (a specialisation of mathlib's general lemma).
Number of weakening opportunities found: K = 3 — but each weakening *lands exactly on the
already-existing mathlib lemma* `Polynomial.eval₂_eval₂RingHom_apply`. Generalising
`polyEval_apply` does not yield a new mathlib lemma; it yields mathlib's existing one.
Proposed restatement: n/a as a mathlib contribution — the maximally-general form **is already in mathlib**.
Cost of restatement: n/a (CHEAP to drop; nothing to re-prove — the general lemma exists).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | already plain ring hom + elements |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic |
| 3 | construct → universal-property class? | no | — | `eval₂`/`evalEval` already *are* the universal-property evaluation maps |
| 4 | set+closure-pred → bundled substructure? | no | — | no substructure |
| 5 | vector-space/field-specific → weaken typeclass? | partially | mathlib's version already uses `CommSemiring` | the modernisation (weaken `CommRing`→`CommSemiring`, `specialize`→arbitrary `f`) is **precisely the existing mathlib lemma** |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general algebra? | no | — | no numeric index |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no (as a *new* contribution) — the contemporary, maximally-general
formulation already exists in mathlib as `Polynomial.eval₂_eval₂RingHom_apply`. There is no
modernised statement to add; the modern statement is upstream already.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.Universal.polyEval_apply`

[A] Lean-Finder       "nested eval2 bivariate equals map then evalEval"   → (index): general lemma surfaces (see [C]/[D])
[B] Loogle            `eval₂ (eval₂RingHom _ _) _ _ = Polynomial.evalEval _ _ _` / `?p.map (mapRingHom ?f) |>.evalEval`  → hits `Polynomial.eval₂_eval₂RingHom_apply`
[C] LeanSearch        "evaluate bivariate polynomial nested eval2 equals map coefficients then evalEval"  → `Polynomial.eval₂_eval₂RingHom_apply` (mathlib4 docs returned by WebSearch #3)
[D] Grep mathlib src  `grep -rn "eval₂_eval₂RingHom_apply"` →  **`Mathlib/Algebra/Polynomial/Bivariate.lean:194`** (definition); also `:189 eval₂RingHom_eval₂RingHom`
[E] Name pattern      `polyEval` / `specialize` / `Universal.curve` in `.lake/.../Mathlib/AlgebraicGeometry/EllipticCurve/`  →  **no hits** (the `Universal.curve`/`specialize`/`polyEval` track does NOT exist in mathlib)

Searched for both:
  - the user's current form (`polyEval`, `specialize`) → only in this project + the duplicated HasseWeil copy; **not in mathlib**.
  - the literature-standard general form → **found in mathlib**: `Polynomial.eval₂_eval₂RingHom_apply` at `Mathlib/Algebra/Polynomial/Bivariate.lean:194-196`, stated for arbitrary `f : R →+* S` over comm-semirings:
    `eval₂ (eval₂RingHom f x) y p = (p.map <| mapRingHom f).evalEval x y`.

Concluded: **the user's `polyEval` def is NOT in mathlib, but the *content* of `polyEval_apply`
is — its general form is `Polynomial.eval₂_eval₂RingHom_apply`. The lemma is a one-call
specialisation of that mathlib lemma to the project-local `polyEval`/`specialize`.**

---

### Call sites — `WeierstrassCurve.Universal.polyEval_apply`

Internal use count: **6** (within NagellLutz, excluding the declaring file) — all in
`projects/NagellLutz/LutzNagell/ZSMul.lean`.
External-to-file callers: 1 file (`ZSMul.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ZSMul.lean:89  | `simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]` |
| ZSMul.lean:92  | `simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]` |
| ZSMul.lean:95  | `simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]` |
| ZSMul.lean:100 | `simp_rw [polyEval_apply, ← map_ψ, map_specialize]` |
| ZSMul.lean:103 | `simp_rw [polyEval_apply, ← map_φ, map_specialize]` |
| ZSMul.lean:106 | `simp_rw [polyEval_apply, ← map_ω, map_specialize]` |

Inline-derivation grep: none — call sites use the named lemma, not an inline re-derivation.

Composability signal: the lemma *is* used (6×), so it is genuine local API — but every use is
a `simp_rw` rewrite that unfolds `polyEval` into `map (mapRingHom specialize) |>.evalEval`.
Because `polyEval W x y p` is **defeq** to `eval₂ (eval₂RingHom W.specialize x) y p`, each of
these `simp_rw [polyEval_apply]` rewrites can equally be `simp_rw [polyEval, eval₂_eval₂RingHom_apply]`
(unfold the def, then apply the mathlib lemma). So the lemma is a *local convenience wrapper*
over a mathlib lemma, not new content.

---

### Composition check (Phase 6)

Can `polyEval_apply` be derived from mathlib in ≤3 chained calls?

Attempt 1: `polyEval_apply p := eval₂_eval₂RingHom_apply _ _ _ _`  ← **this is literally the existing proof in the source.**
  - Mathlib decls used: `Polynomial.eval₂_eval₂RingHom_apply` (1 call).
  - Result: **succeeds** — `polyEval W x y p` is defeq `eval₂ (eval₂RingHom W.specialize x) y p`,
    so the mathlib lemma at `f := W.specialize` closes the goal directly.
  - Notes: zero intervening reasoning; a single application of one mathlib lemma.

Conclusion: **COMPOSABLE** (1 mathlib call — the minimal possible).

### Composition heuristics check
Pattern = "one function call `eval₂_eval₂RingHom_apply _ _ _ _`" → row "one function call" → **composable: yes**. Not a disguised proof.

---

## Verdict: `WeierstrassCurve.Universal.polyEval_apply`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the general identity is folklore functoriality of evaluation; the surrounding universal-curve specialization story is in arXiv 1303.4327 / 2109.10233, but this exact step is the trivial substitution inside it.
- Generality analysis (Phase 4): STRICTLY NARROWER — the lemma is the `f := W.specialize` specialisation of a strictly more general statement; that general statement already exists in mathlib.
- Mathlib search (Phase 5): the def `polyEval` is **not** in mathlib, but the lemma's general form **is** — `Polynomial.eval₂_eval₂RingHom_apply` (`Mathlib/Algebra/Polynomial/Bivariate.lean:194`).
- Composition check (Phase 6): COMPOSABLE — exactly one mathlib call (`eval₂_eval₂RingHom_apply _ _ _ _`), which is the verbatim source proof.

**Rationale.**
`polyEval_apply` is not a mathlib candidate because its statement is *about* `polyEval`, a
project-local construction (`eval₂RingHom (eval₂RingHom W.specialize x) y`) tied to the
NagellLutz/HasseWeil "universal Weierstrass curve + specialization" track, which does not exist
in mathlib (Phase 5[E]: no `Universal.curve`/`specialize`/`polyEval` in mathlib's EllipticCurve
directory). One cannot upstream a lemma whose subject is a downstream def. Meanwhile the actual
mathematical content — "nested `eval₂` = map-coefficients-then-`evalEval`" — is already in
mathlib in full generality as `Polynomial.eval₂_eval₂RingHom_apply` (any ring hom `f`, comm-semiring
base). Since `polyEval W x y p` is *definitionally* `eval₂ (eval₂RingHom W.specialize x) y p`, the
project lemma is the `f := W.specialize` instance of that mathlib lemma, proved by a single
application of it. That is the textbook NO-composable-from-mathlib signature: mathlib supplies the
building block, the project form is a 1-call specialisation, and no new lemma is warranted upstream.

It is *not* NO-mathlib-has-it, because mathlib does not have a lemma named for `polyEval` (the
exact form mentions a non-mathlib def); the right framing is "mathlib has the building block, inline
it". The lemma does have 6 internal uses, so locally it is reasonable convenience API — but those
uses are all `simp_rw` rewrites that could equally cite `[polyEval, eval₂_eval₂RingHom_apply]`.

**WHY not (refactor-actionable).**
Mathlib already provides the building block `Polynomial.eval₂_eval₂RingHom_apply`. The project
lemma is the 1-call specialisation `eval₂_eval₂RingHom_apply _ _ _ _` at `f := W.specialize`.
No new mathlib lemma is needed; the content lives upstream.

Mathlib building blocks:
  - `Polynomial.eval₂_eval₂RingHom_apply` — `Mathlib/Algebra/Polynomial/Bivariate.lean:194`
  - (and its `RingHom`-level companion `Polynomial.eval₂RingHom_eval₂RingHom` — same file, line 189)

Composition sketch (≤3 lines, = the existing source proof):
```lean
example (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  Polynomial.eval₂_eval₂RingHom_apply _ _ _ _
```

Call sites in our project (from Phase 6.0): K = 6 (all in `LutzNagell/ZSMul.lean:89,92,95,100,103,106`).

Refactor plan (project-internal cleanup — NOT a mathlib PR):
  - This lemma is best understood as a **thin local alias** for a mathlib lemma applied to
    `polyEval`. Two equally valid dispositions:
    1. **Keep it** as a 1-line convenience wrapper (it has 6 consumers and reads well), but
       there is nothing to upstream — mark it clearly as "= `eval₂_eval₂RingHom_apply` for
       `polyEval`" and do not propose it for mathlib.
    2. **Inline it**: at each of the 6 `ZSMul.lean` sites, replace `simp_rw [polyEval_apply, …]`
       with `simp_rw [polyEval, eval₂_eval₂RingHom_apply, …]` (unfold the def, then the mathlib
       lemma), and delete `polyEval_apply`. Verify the `← map_ψ`/`map_specialize` follow-on
       rewrites still fire (they should — same normal form).
  - Either way: **do not add `polyEval_apply` to mathlib.** If anything is upstreamed from this
    file it is the `Universal.curve` / `specialize` *track itself* (a separate, larger question),
    not this glue lemma.

Next action: no mathlib PR for this decl. Optionally inline the 6 call sites against
`Polynomial.eval₂_eval₂RingHom_apply` and drop the wrapper (project cleanup ticket, not upstreaming).

Note (duplication): an identical `polyEval_apply` exists at
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:209`. The two should be deduplicated into a
shared `Common/` module on `main` regardless of the mathlib verdict — but that is cross-project
cleanup, orthogonal to mathlibability.

---

## Next step

No mathlib PR. The content is already upstream as `Polynomial.eval₂_eval₂RingHom_apply`
(`Mathlib/Algebra/Polynomial/Bivariate.lean:194`); `polyEval_apply` is its 1-call specialisation
to the project-local `polyEval`. Either keep it as a thin local wrapper or inline the 6 `ZSMul.lean`
call sites against the mathlib lemma and delete it. Separately, deduplicate against the identical
HasseWeil copy.
