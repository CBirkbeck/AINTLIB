# /mathlibable report — `WeierstrassCurve.Universal.polyEval`

## Verdict: NO-composable-from-mathlib

Body is one nested mathlib call — `eval₂RingHom (eval₂RingHom W.specialize x) y` — and the general form is already mathlib's `Polynomial.eval₂RingHom_eval₂RingHom`. (Rides along as YES only if the whole `specialize`/universal-curve package is upstreamed — that packaging call is owned by `specialize.md`.)

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task); decl read from source.
- decl:                     `WeierstrassCurve.Universal.polyEval` ✓ resolved at
                            `projects/NagellLutz/LutzNagell/Universal.lean:203`
- qualified name VERIFIED:  the prompt's guess `WeierstrassCurve.Universal.polyEval` is correct.
  The def sits inside `namespace WeierstrassCurve` → `namespace Universal`, under
  `variable {R} [CommRing R] (W : WeierstrassCurve R)` and `variable (x y : R)`.
- kind:                     `def` (noncomputable section)
- duplicate:                **verbatim copy** at
  `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:~203` (docstring there says
  "Ported from the LutzNagell project"). Independent AINTLIB dedup concern (see Q4).

### The declaration

```lean
open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y
```

where `Poly := (MvPolynomial Coeff ℤ)[X][Y]` and
`W.specialize : MvPolynomial Coeff ℤ →+* R` is `(MvPolynomial.aeval (Coeff.rec a₁ a₂ a₃ a₄ a₆)).toRingHom`.

**Mathematics.** Given a Weierstrass curve `W/R` and a point `(x,y)` in the affine plane over `R`,
`polyEval W x y` is the ring hom `ℤ[A₁..A₆][X][Y] →+* R` that sends `Aᵢ ↦ aᵢ`, `X ↦ x`, `Y ↦ y`.
It is the evaluation-at-a-point specialization of universal-curve polynomials (division polynomials
`ψₙ, φₙ, ωₙ`) to their values on an actual point. Companion lemma:
`polyEval_apply : polyEval W x y p = (p.map (mapRingHom W.specialize)).evalEval x y`, whose proof is
the single line `eval₂_eval₂RingHom_apply _ _ _ _`.

---

### Phase 1 — Literature search

- No named concept "polyEval" / "point-evaluation specialization ring hom for universal Weierstrass
  curves" exists in the literature. Silverman (*AEC* III.4, Exer. 3.7), Lang, Washington, and the
  Ayad/Cassels EDS sources evaluate division polynomials at points implicitly; none isolates "the
  ring hom `ℤ[Aᵢ][X,Y] → R` from a point" as a named object — it is the universal property of a
  polynomial ring, applied.
- The *only* place this machinery is even gestured at is mathlib's own file
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (lines 36–38, 71): it
  describes "the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`" used to
  define `ωₙ`, and leaves `ωₙ` as an explicit **TODO**. That morphism is `R[X,Y]`-valued, not
  `R`-valued; `polyEval` is its further evaluation at the point `(x,y)`. So even the closest mathlib
  hint is about a *sibling* map, not `polyEval` itself.

Conclusion: zero literature support for `polyEval` as a standalone named object.

### Phase 2 — Mathlib search (five methods)

Target: is the ring hom `eval₂RingHom (eval₂RingHom f x) y : R[X][Y] →+* S` (with `f := W.specialize`)
already in mathlib, or a more general form of it?

1. **Loogle / leansearch (index)** — `Polynomial.eval₂RingHom (f : R →+* S) (x : S) : R[X] →+* S`
   (`Mathlib/Algebra/Polynomial/Eval/Defs.lean:213`) is the building block, used **twice** here.
   `Polynomial.evalEvalRingHom (x y : R) : R[X][Y] →+* R`
   (`Mathlib/Algebra/Polynomial/Bivariate.lean:151`) is the `R`-coefficient special case.
2. **grep mathlib for the exact shape** — the iterated form is a *named lemma*:
   `Polynomial.eval₂RingHom_eval₂RingHom` (`Bivariate.lean:189`):
   ```
   eval₂RingHom (eval₂RingHom f x) y = (evalEvalRingHom x y).comp (mapRingHom (mapRingHom f))
   ```
   This is **literally the body of `polyEval`** (LHS) characterised in mathlib terms (RHS).
   The companion `Polynomial.eval₂_eval₂RingHom_apply` (`Bivariate.lean:194`) is exactly
   `polyEval_apply` un-specialized — and indeed `polyEval_apply`'s entire proof is
   `eval₂_eval₂RingHom_apply _ _ _ _`.
3. **Universal Weierstrass curve in mathlib?** — `grep`/`find` over
   `Mathlib/AlgebraicGeometry/EllipticCurve/**`: **none**. No `Universal.curve`, no `Coeff`, no
   `specialize`, no `polyEval`. The only `universal` hit is the prose TODO above. The entire
   `Universal` namespace (and `polyEval` with it) is a project addition; the module docstring states
   it provides "lemmas missing from the released mathlib".
4. **aeval/MvPolynomial side** — `polyEval` is, after unfolding `specialize`, the bivariate `eval₂`
   wrapper around `MvPolynomial.aeval (Coeff.rec a₁..a₆)`. Mathlib's idiom for "evaluate a
   polynomial-over-a-polynomial-ring at concrete data" is exactly nested `eval₂RingHom` / `aeval`;
   there is no missing primitive.
5. **DivisionPolynomial files** — the project forks `DivisionPolynomial.*` /
   `EllipticDivisibilitySequence`; those provide `ψ, φ, Ψ, preΨ, …` as polynomials but **do not**
   provide the point-evaluation hom. `polyEval` is the project's own glue to feed those polynomials
   to a point.

Result: the **general** ring hom is in mathlib (`eval₂RingHom`, characterised by
`eval₂RingHom_eval₂RingHom`); only the project-specific *bundling with `W.specialize`* is local.

### Phase 3 — Generality analysis

- `polyEval` is **strictly less general** than the mathlib primitive it is built from: it hard-codes
  the coefficient map to `W.specialize` (i.e. `aeval (Coeff.rec a₁..a₆)`) and the source to
  `Universal.Poly`, whereas `Polynomial.eval₂RingHom`/`eval₂RingHom_eval₂RingHom` work for an
  arbitrary `f : R →+* S` and arbitrary `R[X][Y]`. The maximally-general statement is already
  upstream; `polyEval` is a specialization of it, not a generalization.
- So there is no "weaken-the-hypotheses" upstream target here — the general form exists; `polyEval`
  is a downstream instantiation.

### Phase 4 — Composition check (can ≤3 mathlib calls give it?)

Yes — in **one** call.

- Definition: `polyEval W x y := eval₂RingHom (eval₂RingHom W.specialize x) y`. This is a single
  nested application of the existing mathlib def `Polynomial.eval₂RingHom`. (1 mathlib construction.)
- Characterisation: `= (evalEvalRingHom x y).comp (mapRingHom (mapRingHom W.specialize))` is exactly
  `Polynomial.eval₂RingHom_eval₂RingHom W.specialize x y`. (1 mathlib lemma.)
- Application lemma: `polyEval_apply` is `Polynomial.eval₂_eval₂RingHom_apply` instantiated, proof
  `eval₂_eval₂RingHom_apply _ _ _ _`. (1 mathlib lemma.)

Every fact about `polyEval` is a ≤1-call mathlib statement. This is the canonical
NO-composable-from-mathlib signature: a named wrapper whose definitional content and whose lemmas are
single mathlib expressions.

### Phase 4b — The packaging tension (why not simply NO)

`polyEval` is **not standalone**: it lives inside the `Coeff` / `Universal.curve` / `specialize` /
`ringEval` ensemble — a coherent universal-curve API that mathlib genuinely lacks and *explicitly
TODOs* (the `ωₙ` / universal-morphism note in `DivisionPolynomial/Basic.lean`). It has ~10 internal
consumers (`evalEval_ψ/φ/ω/ψ₂/Ψ₃/preΨ₄`, `polyEval_cusp_ψ/φ/ψc/ω`, the cusp `ψₙ(1,1)=n` trick) and
no inline re-derivation that bypasses it — a real API surface, not dead code.

But within that package the **named anchor** carrying the semantic intent is `specialize` (the
`ℤ[A₁..A₆] → R` map), already assessed **BORDERLINE-needs-human** in `specialize.md`. By contrast,
`polyEval` is the *mechanical* member: "apply the already-named `eval₂RingHom ∘ eval₂RingHom` to
`specialize`." The package-vs-inline maintainer decision is owned by `specialize.md` (its Q1). For
**this** declaration assessed singly (the skill's mandate), the composition verdict dominates:
- if the whole package is upstreamed → `polyEval` rides along as a package member
  (then YES-but-generalise-first is moot — it is already the right instantiation and would be added
  as-is alongside `specialize`/`ringEval`);
- if mathlib prefers the inline `eval₂RingHom (eval₂RingHom (aeval (Coeff.rec …)) x) y` idiom (the
  Angdinata DivisionPolynomial track may well build `ωₙ`'s morphism that way) → `polyEval` is dropped
  and inlined.

Either branch keeps `polyEval` *non-additive as an independent lemma*: it is glue, gated on the
`specialize` packaging call, never a freestanding mathlib contribution on its own merits.

---

## Five-bucket decision

| bucket | fit |
|---|---|
| YES-add-as-is | No — body is a bare mathlib composition; not a freestanding result. |
| YES-but-generalise-first | No — the *general* form already exists upstream (`eval₂RingHom_eval₂RingHom`); `polyEval` is the specialization, nothing to generalise toward. |
| NO-mathlib-has-it | Close but not exact — mathlib has the **general** hom + its characterising lemma, not this `W.specialize`-bundled wrapper verbatim. The honest call is composable, not "already present." |
| **NO-composable-from-mathlib** | **Yes** — `= eval₂RingHom (eval₂RingHom W.specialize x) y` (1 call); `polyEval_apply = eval₂_eval₂RingHom_apply` (1 call). ≤3 mathlib calls reproduce it exactly. |
| BORDERLINE-needs-human | Only as a *package rider* — but the packaging question is already escalated under `specialize.md`; duplicating the BORDERLINE here would double-count one decision. |

**Verdict: NO-composable-from-mathlib.**

The exact composition: `polyEval W x y` **is** `Polynomial.eval₂RingHom (Polynomial.eval₂RingHom W.specialize x) y`, characterised by `Polynomial.eval₂RingHom_eval₂RingHom` and applied via `Polynomial.eval₂_eval₂RingHom_apply` — both already in `Mathlib/Algebra/Polynomial/Bivariate.lean`.

### Caveat / cross-reference
`polyEval` is a member of the un-upstreamed universal-curve package whose **anchor** `specialize` is
**BORDERLINE-needs-human** (`specialize.md`). If the maintainer upstreams that whole scaffold
(`Coeff`, `Universal.curve`, `specialize`/`map_specialize`, `polyEval`/`ringEval`, closing the `ωₙ`
TODO), `polyEval` ships **as-is** as part of it. Re-run this assessment if/when that packaging
decision (Q1 of `specialize.md`) is made; until then, the single-declaration verdict is
NO-composable-from-mathlib.

### Independent AINTLIB cleanup note
`polyEval` is duplicated **verbatim** between `projects/NagellLutz/LutzNagell/Universal.lean` and
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean`. Regardless of the mathlib decision, file a
dedup ticket to refactor the shared `Universal` scaffold into `Common/`.

## Next step
None blocking for `polyEval` as a single decl (NO-composable). The live human decision is the
package-level one tracked in `specialize.md` (Q1: upstream the whole universal-curve scaffold vs.
inline the `aeval`/`eval₂RingHom` idiom). Separately, dedup the NagellLutz ↔ HasseWeil verbatim copy.
