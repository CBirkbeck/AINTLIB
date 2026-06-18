# T-II-2-009: #φ⁻¹(Q) = deg_s(φ) for almost all Q ★★ DOMINANT-BLOCKER

**Status**: PARTIAL — Pieces 1–8 (stream A, worker-A, 2026-04-22);
Piece 9 (inertiaDeg = 1 over alg-closed) closed (commit fd2e61e)
via LinearEquiv transport, sidestepping the Module.Free diamond.
Remaining: existence of unramified Q at the generic level (Pieces 1–5
provide it over abstract Dedekind towers; specialisation to CurveMap
uses Piece 8's witness form)
**Silverman**: II.2.6(b) (Proposition)

**Priority** (2026-05-08, post-reviewer): this ticket is now the **dominant
mathematical blocker** for the bound. Closing it via the
generic-fibre + translation-bootstrap chain unlocks `pc_fiber_witness`
(III.4.10(c) for `1−π`) AND the separable case of dual isogeny existence
(III.6.1 Case 1). See "Reviewer-driven plan" below.
**Module**: `HasseWeil/Curves/GenericFiber.lean` (Pieces 1–8),
`HasseWeil/Curves/ResidueFieldAtSmoothPoint.lean` (Piece 9)
**Owner**: worker-A (Pieces 1–8), Claude (Piece 9 closure)
**Estimated lines**: 100 (delivered ~300 across all pieces)
**Difficulty**: hard
**Stream**: A

## Depends on
- T-II-2-007, T-II-2-008
- T-II-2-004 (deg_s definition)

## Blocks
- T-III-4-012 (#φ⁻¹(Q) = deg_s for isogenies)
- T-III-4-015 (separable ⇒ #ker = deg)

## Statement (Silverman II.2.6(b))
For all but finitely many Q ∈ C₂,

```
#φ⁻¹(Q) = deg_s(φ).
```

This is **THE critical foundational fact** for the kernel-degree formula used in
the Hasse-Weil proof.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- For all but finitely many points Q, the fiber size equals the separable degree.
    Reference: Silverman II.2.6(b). -/
theorem Morphism.fiber_card_eq_sepDegree_almost_everywhere
    (φ : Morphism C₁ C₂) (hφ : ¬ IsConst φ) :
    ∃ S : Set C₂.SmoothPoint, S.Finite ∧
      ∀ Q ∉ S, Fintype.card (φ.fiber Q) = φ.degreeSep

end HasseWeil.Curves
```

## Notes
- This is a deep theorem in algebraic geometry. The proof in Silverman references
  external sources (Chevalley, Hartshorne).
- Key idea: for a separable extension, the splitting of primes is governed by
  embeddings into K̄. For purely inseparable, every fiber has size 1. The "for
  almost all Q" allows us to ignore the finitely many ramified points.
- mathlib has `Field.finSepDegree_eq_of_isAlgClosed` which relates separable
  degree to embeddings into the algebraic closure. Combine with the fact that
  the fiber over a generic point is the set of K̄-embeddings of the function
  field.

## Reviewer-driven plan (2026-05-08)

External mathematical reviewer confirmed the Silverman spine:

```
T-II-2-009 (II.2.6(b)) → III.4.10(a),(c) → III.6.1 separable case
                                         → III.6.1 Frobenius case (via [p]*ω = 0 + II.2.12)
                                         → III.6.3 → Hasse
```

`pc_fiber_witness` reduces via III.4.10(c) to T-II-2-009 + a translation-
bootstrap step. The bootstrap is small and clean:

1. Use the shipped `Σ e·f = n` (T-II-2-008) over Dedekind domains.
2. For separable φ, the unramified locus is open and dense, so `#fiber = deg_s`
   for almost all Q (Silverman II.2.6(b)).
3. For elliptic-curve isogenies (group homomorphisms), use the translation
   bootstrap: pick `R` with `φ(R) = Q − Q'`; the map `P ↦ P + R` is a bijection
   `φ⁻¹(Q') → φ⁻¹(Q)`. So if `#fiber = deg_s` at one Q, it holds at every Q.
4. Set `Q = O` to get `#ker φ = deg_s φ`.
5. For separable φ, `deg_s = deg`, so `#ker = deg`.

### SCOPE WARNING (geometric points)

The reviewer explicitly flagged: **the fibre theorem must be stated over
the geometric point set** (or after base change to `\overline{\mathbb F_q}`).
Over `F_q` itself, residue degrees and rationality issues will obscure the
statement.

Implication: when consuming this for `pc_fiber_witness`, verify that
`HasseWitnesses.pc_fiber_witness` resolves to geometric points, not
`F_q`-points. If currently stated over `W.toAffine.Point` (which is
typically `F_q`-rational), reframe.

### Narrower alternative (Plan-B if T-II-2-009 stalls)

For separable isogenies of elliptic curves specifically, prove "every
ramification index is 1" via translation invariance of invariant differentials
(Silverman III.5.1 + the fact that ω is non-vanishing for separable φ).
Then `Σ e_φ = #fiber` becomes `#fiber = deg_s` directly, no generic-fibre
machinery needed. May be shorter if the Kähler / ω infrastructure is stronger
than the generic-fibre infrastructure.

### Plan-C fallback (if Plan-B also stalls)

Pole-divisor proof for `γ = 1 − π` specifically (per first reviewer
response). Tickets: T-POLE-DIVISOR-* (see INDEX.md). This avoids the
fibre theorem entirely but is bound-specific (only works for `1 − π`,
not general separable isogenies).

## Progress log

- **2026-04-21** (worker-I scoping audit): after IC-003ii unconditional
  (worker-I, 2026-04-21) and worker-K's `exists_smoothPoint_of_isMaximal`
  + `smoothPointEquivMaxIdeal`, the geometric-side infrastructure for this
  ticket is in place:
  - Every maximal ideal of `F[C]` (= every nonzero prime, by `DimensionLEOne`)
    corresponds bijectively to a smooth F-rational point, under `[IsAlgClosed F]`
    + `[IsElliptic]`.
  - Worker-K's `sum_ramificationIdx_eq_finrank` gives the Σ e = [K(C):K(x)] = 2
    version of II.2.6(a) for the coordinate function `x`.

  **What's still missing for general `CurveMap φ`**: the generic-fiber
  sepDeg cardinality argument (Silverman II.2.6(b)). The abstract algebraic
  side is `Field.finSepDegree F E = Nat.card (E →ₐ[F] K̄)` (mathlib's
  `finSepDegree_eq_of_isAlgClosed`). Connecting this to point cardinality
  over `F_q` requires:
  1. A bridge from algebraic embeddings `K(C) →ₐ[K(x)] K̄(x)` to smooth
     F-rational preimages of a generic `Q ∈ C`.
  2. The "almost all" qualification (exclude ramification points).

  **Consumer gap reminder**: `HasseWeil/Hasse/BoundOfWitnesses.lean`'s
  `hasse_bound_of_all_witnesses` needs `h_pc_fiber_witness :
  ∃ P₀ : W.toAffine.Point, Nat.card {P // β_pc P = β_pc P₀} = β_pc.sepDegree`
  for `β_pc = 1 − π`. For a **separable** isogeny over `F_q` with finite
  kernel (automatic via `[Fintype W.toAffine.Point]`), this reduces by
  `fiber_card_eq_kernel_card` (existing) to showing
  `|ker β_pc| = β_pc.sepDegree`. That is equivalent to
  `|ker β_pc| = β_pc.degree` via separability, which is the **ker = deg**
  theorem (Silverman III.4.15) — itself a downstream consequence of
  T-II-2-009. So the Hasse chain over `F_q` essentially needs a direct
  proof of `|ker| = deg` for separable isogenies, rather than going
  through the general fiber-size argument.

  Possible shortcut routes (not yet evaluated in depth):
  - Direct: `#E(F_q) = |ker(1−π)|` from `pointCount_eq_of_hom_kernel_witness`
    + showing `|ker(1−π)| = deg(1−π)` via the quadratic form trick.
  - Via `Algebra.Etale` on the separable side to lift the characterisation.
  - Via explicit computation using `Ideal.sum_ramification_inertia` plus the
    ramification-index analysis.

- **2026-04-21** (worker-I): delivered a **bridge theorem** that reduces
  `h_pc_fiber_witness` to the `|ker| = sepDeg` equality:
  `Isogeny.fiber_witness_of_ker_card_eq_sepDegree` in
  `HasseWeil/EC/IsogenyKernel.lean` (axiom-clean, ~10 lines). Given
  `Nat.card φ.kernel = φ.sepDegree`, picks `P₀ := 0` and concludes the
  fiber-over-0 has `sepDeg` points via `fiber_card_eq_kernel_card`. This
  changes the upstream obligation from "prove the generic fiber has
  `sepDeg` points" (Silverman II.2.6(b), hard) to "prove
  `|ker φ| = sepDeg φ`" (classical but still requires the ker-deg story).
  Useful for downstream chains that construct `|ker| = sepDeg` by
  finite-group / Frobenius-specific arguments rather than the abstract
  generic-fiber route.

- **2026-04-22** (worker-I): delivered the **algebraic direction of
  T-II-2-009** in new `HasseWeil/Curves/GenericFiber.lean` (~115 lines,
  axiom-clean):
  - `primesOverFinset_card_eq_degree_of_unramified` — given a maximal
    `p ⊂ C₂.CoordinateRing` together with a witness
    `∀ P ∈ primesOver p, e_P · f_P = 1` (i.e. `p` is unramified and has
    trivial residue-field degrees), the count of primes above `p`
    equals `φ.degree`. Follows from
    `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree` (T-II-2-008,
    worker-I 2026-04-22) + `Finset.sum_const`.
  - `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified` —
    same conclusion in terms of `sepDegree` under the separability
    hypothesis (uses `Field.finSepDegree_dvd_finrank` + `deg_i = 1` to
    get `sepDeg = deg`).

  **Remaining gap** (the hard direction): exhibiting an unramified prime
  `p` with trivial residue degrees requires the primitive-element-plus-
  discriminant construction — the "almost all" content of Silverman
  II.2.6(b). Outlined in `GenericFiber.lean`'s docstring, with a pointer
  to the `Algebra.IsUnramifiedAt ↔ ¬ p ∣ differentIdeal` bridge in
  mathlib's `DedekindDomain.Different`. Estimated ~200 lines of further
  algebraic-geometric infrastructure; the primitive element
  (`Field.exists_primitive_element`) and discriminant
  (`Polynomial.disc_ne_zero_of_separable`) pieces are present in mathlib,
  but the connection "discriminant nonzero at `p` ⇒ unramified at `p`"
  over an arbitrary Dedekind extension needs to be extracted + applied.

  **Effect on HOLE D**: provides the structural piece, but **HOLE D is
  still circular for the specific β_pc = oneSubFrobeniusIsog W under the
  current `isogOneSub` placeholder** (where `deg β_pc = 1`). The generic-
  fiber existence lemma still requires either the primitive-element
  construction or stream-D's `AdditionPullback.lean` landing.
