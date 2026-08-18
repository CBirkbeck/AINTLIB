# Mathlibable assessment: `WeierstrassCurve.Universal.evalEval_ψ`

- **Project:** NagellLutz (Nagell–Lutz theorem; division polynomials; elliptic divisibility sequences)
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:99`
- **Qualified name (verified from source):** `WeierstrassCurve.Universal.evalEval_ψ`
- **Date:** 2026-06-22
- **Verdict:** **BORDERLINE-needs-human**

---

## 1. Exact statement and proof

```lean
namespace WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)
variable {x y : R} {m n : ℤ}
namespace Universal

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]
```

**Meaning.** `curve.ψ n` is the `n`‑th division polynomial of the project's *universal*
Weierstrass curve `Universal.curve : Affine (MvPolynomial Coeff ℤ)` (the curve with generic
coefficients `A₁,…,A₆`). `polyEval W x y : Poly →+* R` is the homomorphism
`ℤ[A₁,…,A₆,X,Y] → R` that first specializes the `Aᵢ` to `W`'s coefficients (`W.specialize`)
and then evaluates `X ↦ x`, `Y ↦ y`. The lemma says: forming the universal `ψ n`, specializing
to `W`, and evaluating at `(x,y)`, gives the same element of `R` as directly evaluating the
concrete curve's division polynomial `W.ψ n` at `(x,y)`. It is the basic compatibility (bridge)
lemma that lets the whole `ZSMul` development reason about the universal curve and then transport
results to any concrete `W` by specialization.

The proof is a 1-liner: rewrite `polyEval` as `(·.map (mapRingHom W.specialize)).evalEval x y`
(`polyEval_apply`), pull the specialization map inside the division polynomial backwards via
mathlib's functoriality lemma `map_ψ` (`(W.map f).ψ n = (W.ψ n).map (mapRingHom f)`), and close
with `map_specialize : Universal.curve.map W.specialize = W`.

## 2. Literature search

The mathematical content — "evaluating the division polynomial at a rational point on the curve
recovers its definition, and the universal/generic curve over `ℤ[A₁,…,A₆]` specializes to any
curve" — is standard. It underlies the explicit valuation results in Stange / Ayad and is the
framing in:

- arXiv:1108.3051, *Integral points on elliptic curves and explicit valuations of division
  polynomials* — division polynomials as elements of the universal ring `ℤ[A₁,…,A₆][X,Y]`,
  specialized per curve.
- arXiv:math/0404412, *p-adic properties of division polynomials and elliptic divisibility
  sequences*.
- D. Angdinata et al., *An Elementary Formal Proof of the Group Law on Weierstrass Elliptic
  Curves in Any Characteristic* (ITP 2023) — the origin of mathlib's division-polynomial design,
  whose module docstring explicitly invokes "the characteristic 0 universal ring
  `𝓡[X,Y] := ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]`" and "the associated universal morphism `𝓡[X,Y] → R[X,Y]`
  mapping `Aᵢ` to `aᵢ`."

So the *idea* is firmly in the literature and was explicitly in the mathlib authors' minds — but
mathlib chose a different formalization (see §3): functoriality `map_ψ` instead of a reified
universal-curve object plus an evaluation homomorphism.

## 3. Mathlib search (five methods)

mathlib pin: `09b373db6e24`, toolchain `v4.32.0-rc1`. Searched
`.lake/packages/mathlib/Mathlib/...`.

- **`Universal` namespace / a reusable universal-curve object** — NONE. mathlib's
  `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` only *mentions* the universal
  ring `ℤ[A₁,…,A₆][X,Y]` in its docstring; it never builds `Universal.curve`,
  `MvPolynomial Coeff ℤ`, `Coeff.rec`, etc. as an object. (grep for `MvPolynomial Coeff` /
  `Coeff.rec` / `Universal.curve` over Mathlib: no hits; the apparent `Degree.lean` hit is an
  unrelated private `expCoeff_rec`.)
- **`polyEval` / `specialize`** — NONE in mathlib (`def polyEval`, `def specialize`: 0 hits).
  Both are defined in the project at `LutzNagell/Universal.lean:190` (`specialize`) and `:203`
  (`polyEval`). `polyEval_apply` (`Universal.lean:206`) is likewise project-only.
- **The LHS/RHS primitives that DO exist in mathlib:**
  - `Polynomial.evalEval` — `Mathlib/Algebra/Polynomial/Bivariate.lean:44`.
  - `WeierstrassCurve.ψ` (division polynomial) — `.../DivisionPolynomial/Basic.lean:401`.
  - `WeierstrassCurve.map_ψ` (functoriality) — `.../DivisionPolynomial/Basic.lean:536`:
    `(W.map f).ψ n = (W.ψ n).map (mapRingHom f)`.
  - `Polynomial.eval₂_eval₂RingHom_apply` — `.../Algebra/Polynomial/Bivariate.lean:194` (this is
    what `polyEval_apply` invokes).
- **The exact lemma `evalEval_ψ`** — NOT in mathlib (it cannot be: its very statement names the
  project-only objects `polyEval` and `curve`).

**Note (in-repo duplication).** An identical lemma exists in the HasseWeil project
(`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:174`), with the same proof and
the same `open Universal`. So at least two AINTLIB projects independently carry this universal
scaffold and this bridge lemma — evidence it is genuinely useful infrastructure, but useful
*within the fork's universal-curve idiom*, which mathlib does not share.

## 4. Generality analysis

The statement is already at maximal natural generality for its setting: arbitrary commutative
ring `R` (no field/PID/char hypotheses), arbitrary index `n : ℤ`, arbitrary affine point
`(x, y) : R × R` (no `Equation`/`Nonsingular` hypothesis needed — it is a pure polynomial
identity). There is no assumption to weaken. The `φ` and `ω` analogues sit immediately below
(`evalEval_φ`, `evalEval_ω`) and the `ψ₂` / `Ψ₃` / `preΨ₄` base cases just above, so if upstreamed
it would go as a small family, not a singleton.

## 5. Composition check (≤ 3 mathlib calls?)

*As proved*, the body is literally three rewrites — `polyEval_apply`, `← map_ψ`, `map_specialize`
— but **only one of the three (`map_ψ`) is a mathlib lemma**; the other two are project-defined.
More fundamentally, the lemma **cannot be phrased in mathlib at all today**, because both sides
reference objects (`polyEval`, `Universal.curve`) that do not exist in mathlib. So it is *not*
"composable from mathlib primitives" in the NO-composable sense: there is no mathlib spelling of
the statement to compose toward. The genuinely mathlib-native fact in this neighbourhood is the
already-present `map_ψ`; `evalEval_ψ` is the corollary you get *after* you have added a universal
curve and an evaluation homomorphism.

## 6. Verdict and rationale

**BORDERLINE-needs-human.**

- Not `NO-mathlib-has-it`: mathlib has `map_ψ` and `evalEval`, but neither the lemma nor its
  ambient objects (`polyEval`, `Universal.curve`, `specialize`) are present.
- Not cleanly `NO-composable-from-mathlib`: the statement isn't even expressible in mathlib
  without first importing the project's universal-curve scaffold; "compose 3 mathlib calls" does
  not apply to a statement mathlib cannot state.
- Not `YES-add-as-is` / `YES-but-generalise-first` in isolation: shipping this one glue lemma
  alone is pointless. Its value is entirely contingent on the surrounding `Universal` evaluation
  framework (`Universal.curve` + `specialize` + `polyEval` + `polyEval_apply`) and the larger
  `ZSMul` result it serves — `n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coordinates — which *is*
  plausibly mathlib-worthy and matches the ITP-2023 authors' stated universal-ring intent.

The real decision is a packaging/scope call: **should mathlib reify the universal pointed
Weierstrass curve and its specialization/evaluation homomorphisms** (and with them the
division-polynomial-evaluation point-multiplication formula)? If yes, `evalEval_ψ` rides along as
a trivial, maximally-general bridge lemma (with `evalEval_φ`, `evalEval_ω`, and the `ψ₂/Ψ₃/preΨ₄`
base cases) and the HasseWeil duplicate collapses into it. That upstream/no-upstream judgment on
the whole scaffold is exactly the kind of architectural decision that needs a human maintainer,
hence BORDERLINE.

**Recommendation to a human reviewer:** evaluate the *whole* `Universal` evaluation framework +
the `ZSMul` multiplication-by-`n` formula as a mathlib contribution; if accepted, take this lemma
family with it and dedupe HasseWeil against it. Do not upstream `evalEval_ψ` standalone.

---

### Sources

- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- [Integral points on elliptic curves and explicit valuations of division polynomials (arXiv:1108.3051)](https://arxiv.org/pdf/1108.3051)
- [An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves in Any Characteristic (ITP 2023)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf)
- [p-adic properties of division polynomials and elliptic divisibility sequences (arXiv:math/0404412)](https://arxiv.org/pdf/math/0404412)
