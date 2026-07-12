# Zulip draft — Y₁(N) announcement (paste-ready; Zulip markdown with spoiler blocks)

**The modular curve Y₁(N) in Lean 4: representability, smoothness, affineness — axiom-clean**

We've formalized the first modular curve as a moduli space. Over any commutative ring `R` in
which `N` is invertible (`N ≥ 4`), the Γ₁(N) moduli problem — elliptic curves with a point of
exact order N — is representable, and the representing scheme is smooth and affine over
`Spec R`:

```lean
theorem gammaOneNaive_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap)
```

with `#print axioms` = `[propext, Classical.choice, Quot.sound]`, and the witness named:

```lean
theorem yOne_representable_smooth_affine … :
    Nonempty ((gammaOneNaiveProblem R N).RepresentableBy (yOneEllObj R N)) ∧
      Smooth (yOneStructMap R N) ∧ IsAffineHom (yOneStructMap R N)

theorem gammaOneNaive_representable_zInv …   -- the literal ℤ[1/N] form (Loeffler Thm 3.4.4)
```

Code: `github.com/CBirkbeck/AINTLIB`, branch `dev/modular-curves-y1`,
`projects/ModularCurves/` (headline: `ModularCurve/YOneTatePoint.lean`). PR to the
integrated branch: #5256.

A statement like this is only as meaningful as its definitions, so rather than dump the
library, here is the **complete definitional trail** of the statement — every project-defined
notion it mentions, what it says, and the *proven sanity theorem* that pins its meaning to
mathlib vocabulary. Everything bottoms out in mathlib's `Scheme`, `IsProper`,
`SmoothOfRelativeDimension`, `IsAffineHom`, and `WeierstrassCurve`.

```spoiler What is an "elliptic curve over a scheme" here?
`EllipticCurveGeom S` is a scheme `E` with a proper, smooth-of-relative-dimension-1 morphism
`π : E ⟶ S` (mathlib classes), a section `zero`, and a **local-model field**: Zariski-locally
on `S`, `(E, π, zero)` is the projective model of a mathlib `WeierstrassCurve` with unit
discriminant. So "elliptic curve" is anchored to mathlib's Weierstrass equations, not to a
new abstract notion. Sanity theorems: `fibrewiseElliptic` (every geometric fibre is a genus-1
pointed curve, so the record is at least as strong as Deligne–Rapoport II.1.1 / KM 2.1.1);
and the group structure carried by the working record `EllipticCurve S` is **canonically
unique** (`grpObj_mul_unique`: any two pointed group structures on such a curve agree — so
no data was smuggled in).
```

```spoiler What is the moduli problem?
`EllObj R` packages a base `R`-scheme `S` with an elliptic curve over it; morphisms are
cartesian squares compatible with the zero sections (Loeffler Def 3.7.1). A moduli problem is
literally a presheaf: `ModuliProblem R := (EllObj R)ᵒᵖ ⥤ Type u`, and `Representable` /
`RepresentableBy` are thin wrappers over mathlib's `Functor.RepresentableBy`. The Γ₁ problem
sends `(S, E)` to the set of sections `P` with `IsNaiveGammaOne N P`.
```

```spoiler What does "point of exact order N" mean, and why trust it?
`IsNaiveGammaOne N P` says `(N : ℤ) • P = 0` globally, and on **every geometric fibre**
(every base point valued in an algebraically closed field) the pulled-back point has exact
order `N` — `a • P ≠ 0` for `0 < a < N`. Two sanity anchors: (1)
`geomFibrePointAddEquiv : E.Point (geomPoint) ≃+ (W.baseChange k).toAffine.Point` — a
**proven additive group isomorphism** between our scheme-theoretic fibre points and mathlib's
own `WeierstrassCurve.Point` group, so "order of a point" means exactly what it means in
mathlib; (2) `isGammaOne_iff_naive` — over bases with `N` invertible this naive notion is
**provably equivalent** to the Katz–Mazur/Drinfeld definition (`IsGammaOne`, via Cartier
divisors: the divisor `Σ_{a ∈ ℤ/N} [aP]` is a subgroup scheme), which is also formalized and
is the definition of record over arbitrary bases.
```

```spoiler What is the representing scheme, concretely?
`yOne R N` is explicit: inside the universal Tate curve (the projective model of the
Tate-normal Weierstrass curve `Y² + (1−c)XY − bY = X³ − bX²` over
`R[b,c][1/Δ]` — a mathlib `WeierstrassCurve` over an explicit localized polynomial ring),
take the closed locus where `N • P₀ = 0` for the marked point `P₀ = (0,0)`, and inside that
the open locus where `P₀` has exact fibrewise order `N`. No quotients, no descent in the
definition itself — an open subscheme of a closed subscheme of an explicit projective model.
```

**Selected theorems proven along the way** (each of independent interest, all on the branch):

- The Bosma–Lenstra–style group law is a **scheme morphism over every base ring** with full
  base-change naturality, and it computes mathlib's `WeierstrassCurve.Projective.Point.add`
  on all field points (`mulModelHom_specPoints`).
- `E[N] → S` is finite, flat, and étale for `N` invertible (`torsionπ_etale'`,
  `torsionπ_isFinite_of_nIsInvertible`, `mulByHom_flat_of_nIsInvertible` — the KM 2.3.1
  package in the invertible case; the quasi-finiteness leg goes through a cross-project
  bridge to an independent HasseWeil development in the same workspace).
- The classifying theorem `exists_tatePoint` (Loeffler Cor 3.3.5): every `(E, P)` with `P`
  nowhere of geometric order ≤ 3 classifies **uniquely** through the marked Tate curve.
- Infrastructure grown for this and re-usable: `AlgebraicGeometry.Scheme.Pic` with a
  contravariant group-functor `Pic.map`; sheaf-of-modules duals and pole sheaves; a glued
  Grassmannian scheme; Hopf–Galois descent for finite free Hopf algebras (Stacks 03BM);
  agreement/vanishing loci of maps into étale morphisms are clopen.

**How to check it** (nothing to trust beyond Lean + mathlib):

```
git clone https://github.com/CBirkbeck/AINTLIB && cd AINTLIB
git checkout dev/modular-curves-y1
lake exe cache get
lake build ModularCurves.ModularCurve.YOneTatePoint
# then in a scratch file:
#   #print axioms ModularCurves.gammaOneNaive_representable
#   #print axioms ModularCurves.exists_tatePoint
```

Honesty notes: (1) the wider repository is a live workspace and *does* contain `sorry`s in
in-progress files — none are on the axiom trail of the theorems above, which is what the
`#print axioms` check certifies; (2) this is the *naive* moduli problem in the invertible-`N`
regime, where it provably agrees with the Katz–Mazur one — the integral Drinfeld theory
(regularity over ℤ at primes dividing N, KM Ch. 5) is a separate stream we've started but
not claimed; (3) this library is developed by AI agents (a coordinated fleet of Claude
instances) with human direction — statements were transcribed from Loeffler's notes and
Katz–Mazur with source-quoting discipline, and the axiom audit above is the verification
mechanism we'd ask you to rely on, not our say-so.

Feedback very welcome — especially on the definitional choices (the local-model field for
elliptic curves, the zero-compatibility clause in `EllHom`) and on anything you'd want as an
additional sanity theorem before believing a statement of this shape. Next targets in
flight: Y(N), Γ_H = KM 7.1 quotient problems, Γ₀(N)/n-isogeny, and the Weil pairing.
