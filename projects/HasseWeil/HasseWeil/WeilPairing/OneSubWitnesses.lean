/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.FrobeniusFixedPoint
import HasseWeil.WeilPairing.IsogenyBaseChangeConcrete

/-!
# Discharging the point/divisor witnesses of `OneSubScalingData` over `K̄` (CoordHom-free)

This file connects the abstract base-changed isogeny `(1 − π)_{K̄}` of
`OneSubScaling.lean`/`IsogenyBaseChangeConcrete.lean` to the concrete **geometric Frobenius**
machinery of `Curves/FrobeniusFixedPoint.lean`, and uses that connection to **prove** several of
the genuinely-deep K̄-level geometric witnesses that `mkOneSubScalingDataConcrete` consumes,
isolating precisely the ones that remain open.

## The linchpin: `frobeniusHomBaseChange = geomFrobeniusPoint`

The point map carried by `oneSubFrobeniusIsogBaseChange` is `id − π̄` with
`π̄ = frobeniusHomBaseChange W p r L`
(`= (frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom`,
the iterated relative `p`-Frobenius point map).  Over `L = AlgebraicClosure K` this is the same map
as the **geometric Frobenius** `geomFrobeniusPoint W` of `FrobeniusFixedPoint.lean` (mathlib's
`Affine.Point.map (frobeniusAlgHom K K̄)`, the literal `q`-power on coordinates), but the two are
*not* definitionally equal — `frobeniusHomBaseChange` is built through a `cast` over `r` iterations
of the relative Frobenius.  `frobeniusHomBaseChange_eq_geomFrobeniusPoint` proves the equality by:

* `iterate_apply_some_heq` — an induction on `r` showing the iterated relative Frobenius point map
  sends `(x, y) ↦ (x^{p^r}, y^{p^r})` (transporting the codomain-curve `cast` at each step via the
  generic `isogeny_cast_apply_heq`/`some_heq_of_curve_eq` `HEq` lemmas), then
* peeling the outer `charP_pow` `cast` and matching with `geomFrobeniusPointFun_some`
  (`x^{p^r} = x^{#K}` since `#K = p^r`).

This is **axiom-clean** (`[propext, Classical.choice, Quot.sound]`).

## What is proved vs. isolated

With the connection, `(1 − π)_{K̄}`'s kernel becomes the geometric-Frobenius fixed locus
`ker(id − π̄) = ker(oneSubGeomFrobHom) = Fix(π̄) = range(includePointBC) ≅ E(𝔽_q)`:

* **`finiteKer` — PROVED** (axiom-clean): the kernel is the image of the finite `E(𝔽_q)` under the
  base-change inclusion (`fixedLocus_geomFrobenius_eq_range_includePointBC` + `Set.finite_range`).
* **`hkerdeg` — REDUCED to V.1.3**: `#ker(id − π̄) = #E(𝔽_q) = pointCount` is *proved* clean
  (`ncard_ker_oneSubGeomFrobHom_eq_pointCount`), so `hkerdeg : #ker = φ_L.degree` follows once
  `φ_L.degree = pointCount` — which is exactly Silverman V.1.3
  (`isogOneSub_negFrobenius_degree_eq_pointCount`, the known sharp residual carrying `sorryAx`).
  `hkerdeg_of_degree_eq_pointCount` packages this reduction, taking the degree-identity as a
  hypothesis so the V.1.3 dependence is explicit and the lemma itself is axiom-clean.

* **`hsurj` — REDUCED to the dual** (axiom-clean reduction): surjectivity of `id − π̄` is *not*
  reachable from the fixed-locus kernel facts, but it **is** reachable from the divisor-pushforward
  dual via its *other* composition `φ ∘ δ = [#ker]`: given `Q`, pick `R` with `[#ker] R = Q` (the
  *shipped* `mulByInt_point_surjective`, Silverman III.4.10b over `K̄`); then `φ (δ R) = Q`.
  `hsurj_of_self_comp_dual` packages this, so once the dual is bundled as a genuine `IsDualOf`
  (carrying *both* `δ ∘ φ = [#ker]` and `φ ∘ δ = [#ker]`), `hsurj` comes for free alongside `hdc`.

The genuinely-deep residuals that remain open (each a named hypothesis), not reachable from the
fixed-locus / `[ℓ]`-surjectivity machinery:

* **`δ`/`hdc`/`hself`** — the divisor-pushforward dual `1 − V̄` as an `IsDualOf`, i.e. *both*
  composition identities `δ ∘ φ = [#ker φ]` and `φ ∘ δ = [#ker φ]` (Silverman III.6.2(a)); needs
  the base-change of the `K`-level Verschiebung dual relation;
* **`hproj`** — `ProjOrdTransport` (the multiplicity-free divisor-pullback functoriality);
* **`hcomm'`** — the translation covariance (Silverman III.8.2).

`mkOneSubScalingDataConcrete_of_witnesses` assembles the full `OneSubScalingData` over
`L = AlgebraicClosure K` consuming **only** the still-open residuals (`δ`/`hdc`/`hself`, `hproj`,
`hcomm'`) plus the V.1.3 degree identity, with `finiteKer`, `hkerdeg`, `hsurj`, and `hdeg_bc`
(the curve-free base-change-of-finrank, now proved as `finrankBaseChange`) discharged internally.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10a/c, III.6.2(a), III.8.2, III.8.6.1,
  V.1.1.
* `HasseWeil/Curves/FrobeniusFixedPoint.lean` (the geometric-Frobenius fixed-locus theory).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

/- `frobeniusIsog_baseChange_charP_pow` and `frobeniusIsog_relative_iterate` carry their codomain
through a `cast` over a *propositional* curve equality.  Evaluating the point map of such a `cast`
on a point requires transporting across the curve equality; the three `HEq` helpers below do that. -/

/-- **Cast-transport for `Isogeny.toAddMonoidHom`** (`HEq` form).  When the codomain curve equality
`A₂ = A₂'` holds, casting an isogeny `A₁ → A₂` to `A₁ → A₂'` and applying its point map at `P`
is heterogeneously equal to applying the original point map at `P`. -/
theorem isogeny_cast_apply_heq {F : Type*} [Field F] [DecidableEq F] {A₁ A₂ A₂' : WeierstrassCurve F}
    [A₁.toAffine.IsElliptic] [A₂.toAffine.IsElliptic] [A₂'.toAffine.IsElliptic]
    (φ : Isogeny A₁.toAffine A₂.toAffine) (hcurve : A₂ = A₂')
    (hisog : Isogeny A₁.toAffine A₂.toAffine = Isogeny A₁.toAffine A₂'.toAffine)
    (P : A₁.toAffine.Point) :
    HEq ((cast hisog φ).toAddMonoidHom P) (φ.toAddMonoidHom P) := by
  subst hcurve; rfl

/-- **`HEq` of `.some` points across a curve equality.** -/
theorem some_heq_of_curve_eq {F : Type*} [Field F] [DecidableEq F] {A A' : WeierstrassCurve F}
    [A.toAffine.IsElliptic] [A'.toAffine.IsElliptic] (hAA : A = A') {x y : F}
    (h : A.toAffine.Nonsingular x y) (h' : A'.toAffine.Nonsingular x y) :
    HEq (Affine.Point.some x y h : A.toAffine.Point)
      (Affine.Point.some x y h' : A'.toAffine.Point) := by
  subst hAA; rfl

/-- **`HEq` of `0` points across a curve equality.** -/
theorem zero_heq_of_curve_eq {F : Type*} [Field F] [DecidableEq F] {A A' : WeierstrassCurve F}
    [A.toAffine.IsElliptic] [A'.toAffine.IsElliptic] (hAA : A = A') :
    HEq (0 : A.toAffine.Point) (0 : A'.toAffine.Point) := by
  subst hAA; rfl

section Iterate

variable {K : Type*} [Field K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime] [ExpChar K p]

/-- **Nonsingularity of `(x^{p^n}, y^{p^n})` on `E.map (iterateFrobenius K p n)`** from
nonsingularity of `(x, y)` on `E`, via the ring-hom nonsingularity transfer (`iterateFrobenius` is
injective) together with `iterateFrobenius K p n a = a^{p^n}`. -/
theorem hns_iter (E : WeierstrassCurve K) [E.toAffine.IsElliptic] (n : ℕ) {x y : K}
    (h : E.toAffine.Nonsingular x y) :
    (E.map (iterateFrobenius K p n)).toAffine.Nonsingular (x ^ p ^ n) (y ^ p ^ n) :=
  (WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine)
    (f := iterateFrobenius K p n) (RingHom.injective _) x y).mpr h

/-- **The iterated relative `p`-Frobenius point map on `.some`** (`HEq` form, transporting the
codomain `cast`).  `(frobeniusIsog_relative_iterate p E r).toAddMonoidHom (x, y) = (x^{p^r}, y^{p^r})`
on `E.map (iterateFrobenius K p r)`.

Induction on `r`: the base case is the identity (after the `cast` over `E.map id = E`), and the step
applies one more relative `p`-Frobenius `(a ↦ a^p)` to the inductive `(x^{p^n}, y^{p^n})`, giving
`(x^{p^{n+1}}, y^{p^{n+1}})`; the `cast` at each level is peeled by `isogeny_cast_apply_heq`. -/
theorem iterate_apply_some_heq (E : WeierstrassCurve K) [E.toAffine.IsElliptic] (r : ℕ) (x y : K)
    (h : E.toAffine.Nonsingular x y)
    (h' : (E.map (iterateFrobenius K p r)).toAffine.Nonsingular (x ^ p ^ r) (y ^ p ^ r)) :
    HEq ((Isogeny.frobeniusIsog_relative_iterate p E r).toAddMonoidHom (.some x y h))
      (Affine.Point.some (x ^ p ^ r) (y ^ p ^ r) h') := by
  induction r generalizing x y with
  | zero =>
    rw [Isogeny.frobeniusIsog_relative_iterate]
    have hc0 : E = E.map (iterateFrobenius K p 0) := by
      rw [iterateFrobenius_zero, WeierstrassCurve.map_id]
    refine HEq.trans (isogeny_cast_apply_heq (Isogeny.id E.toAffine) hc0 ?_ (.some x y h)) ?_
    · congr 1
    · change HEq (Affine.Point.some x y h) (Affine.Point.some (x ^ p ^ 0) (y ^ p ^ 0) h')
      refine HEq.trans (some_heq_of_curve_eq hc0 h ?_) ?_
      · rw [show (x : K) = x ^ p ^ 0 by rw [pow_zero, pow_one],
          show (y : K) = y ^ p ^ 0 by rw [pow_zero, pow_one]]
        exact h'
      · congr 1 <;> rw [pow_zero, pow_one]
  | succ n ih =>
    rw [Isogeny.frobeniusIsog_relative_iterate]
    have hcs : (E.map (iterateFrobenius K p n)).frobeniusTwist p =
        E.map (iterateFrobenius K p (n + 1)) := by
      change (E.map (iterateFrobenius K p n)).map (frobenius K p) = _
      rw [WeierstrassCurve.map_map]
      congr 1
      rw [show iterateFrobenius K p (n + 1) = (iterateFrobenius K p 1).comp (iterateFrobenius K p n)
            by rw [add_comm n 1]; exact iterateFrobenius_add K p 1 n, iterateFrobenius_one]
    refine HEq.trans (isogeny_cast_apply_heq
      ((frobeniusIsog_relative p (E.map (iterateFrobenius K p n))).comp
        (Isogeny.frobeniusIsog_relative_iterate p E n)) hcs ?_ (.some x y h)) ?_
    · congr 1
    rw [Isogeny.comp_apply]
    have hns_n : (E.map (iterateFrobenius K p n)).toAffine.Nonsingular (x ^ p ^ n) (y ^ p ^ n) :=
      hns_iter p E n h
    rw [eq_of_heq (ih x y h hns_n), frobeniusIsog_relative_apply_some]
    have hxp : (frobenius K p) (x ^ p ^ n) = x ^ p ^ (n + 1) := by
      change (x ^ p ^ n) ^ p = x ^ p ^ (n + 1); rw [← pow_mul, pow_succ]
    have hyp : (frobenius K p) (y ^ p ^ n) = y ^ p ^ (n + 1) := by
      change (y ^ p ^ n) ^ p = y ^ p ^ (n + 1); rw [← pow_mul, pow_succ]
    refine HEq.trans ?_ (some_heq_of_curve_eq hcs ?_ h')
    · congr 1
    · rw [← hxp, ← hyp]
      exact (WeierstrassCurve.Affine.map_nonsingular (W := (E.map (iterateFrobenius K p n)).toAffine)
        (f := frobenius K p) (RingHom.injective _) (x ^ p ^ n) (y ^ p ^ n)).mpr hns_n

end Iterate

section Connection

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqAC : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- **The linchpin** (axiom-clean): over the algebraic closure, the base-changed Frobenius point map
`frobeniusHomBaseChange` (the iterated relative `p`-Frobenius, carried through a `cast`) equals the
**geometric Frobenius** `geomFrobeniusPoint W` (mathlib's `Affine.Point.map (frobeniusAlgHom K K̄)`,
the literal `q`-power on coordinates).

Both send `0 ↦ 0` and `(x, y) ↦ (x^{#K}, y^{#K})`; the proof peels the outer `charP_pow` `cast`
(`isogeny_cast_apply_heq`), applies `iterate_apply_some_heq` (`(x, y) ↦ (x^{p^r}, y^{p^r})`), and
matches `geomFrobeniusPointFun_some` using `#K = p^r`. -/
theorem frobeniusHomBaseChange_eq_geomFrobeniusPoint
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] :
    frobeniusHomBaseChange W p r (AlgebraicClosure K) = geomFrobeniusPoint W := by
  haveI : ExpChar (AlgebraicClosure K) p := ExpChar.prime Fact.out
  have hcz : (W.baseChange (AlgebraicClosure K)).map (iterateFrobenius (AlgebraicClosure K) p r) =
      W.baseChange (AlgebraicClosure K) :=
    Isogeny.frobeniusTwistIterate_baseChange_eq_self_of_charP_pow (k := K) p r W (AlgebraicClosure K)
  ext P
  change (Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K)).toAddMonoidHom P
    = geomFrobeniusPointFun W P
  rw [Isogeny.frobeniusIsog_baseChange_charP_pow]
  rcases P with _ | ⟨x, y, h⟩
  · refine eq_of_heq (HEq.trans (isogeny_cast_apply_heq _ hcz ?_ Affine.Point.zero) ?_)
    · congr 1
    · change HEq ((Isogeny.frobeniusIsog_relative_iterate p (W.baseChange (AlgebraicClosure K)) r).toAddMonoidHom 0)
        (geomFrobeniusPointFun W 0)
      rw [map_zero, geomFrobeniusPointFun_zero]
      exact zero_heq_of_curve_eq hcz
  · have hns' : ((W.baseChange (AlgebraicClosure K)).map
        (iterateFrobenius (AlgebraicClosure K) p r)).toAffine.Nonsingular (x ^ p ^ r) (y ^ p ^ r) :=
      hns_iter p (W.baseChange (AlgebraicClosure K)) r h
    refine eq_of_heq (HEq.trans (isogeny_cast_apply_heq _ hcz ?_ (Affine.Point.some x y h)) ?_)
    · congr 1
    refine HEq.trans (iterate_apply_some_heq p (W.baseChange (AlgebraicClosure K)) r x y h hns') ?_
    rw [geomFrobeniusPointFun_some]
    have hq : Fintype.card K = p ^ r := Fact.out
    have hax : (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) x = x ^ p ^ r := by
      rw [FiniteField.coe_frobeniusAlgHom, hq]
    have hay : (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) y = y ^ p ^ r := by
      rw [FiniteField.coe_frobeniusAlgHom, hq]
    refine HEq.trans (some_heq_of_curve_eq (A' := W.baseChange (AlgebraicClosure K)) hcz hns' ?_) ?_
    · rw [← hcz]; exact hns'
    · refine heq_of_eq ?_
      congr 1 <;> simp only [hax, hay]

/-- **The base-changed `(1 − π)_{K̄}` point map is `id − geomFrobenius`** (= `oneSubGeomFrobHom`),
over `L = AlgebraicClosure K`.  Combines the constructional `toAddMonoidHom = id − π̄`
(`oneSubFrobeniusIsogBaseChange_toAddMonoidHom`) with the linchpin `π̄ = geomFrobeniusPoint`. -/
theorem oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom =
      oneSubGeomFrobHom W := by
  rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom, frobeniusHomBaseChange_eq_geomFrobeniusPoint]
  rfl

end Connection

section Witnesses

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqAC' : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- **Witness 1 — `finiteKer`** (PROVED, axiom-clean): the kernel of `(1 − π)_{K̄}` is finite.

Via the linchpin, `ker(id − π̄) = ker(oneSubGeomFrobHom)`, whose underlying set is the
geometric-Frobenius fixed locus `= range(includePointBC)` (Step S2/S3 of `FrobeniusFixedPoint.lean`),
i.e. the image of the **finite** point set `E(𝔽_q) = W.toAffine.Point` under the base-change
inclusion — hence finite. -/
theorem oneSubFrobeniusIsogBaseChange_finiteKer
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    Finite (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom.ker := by
  rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom]
  have hset : ((oneSubGeomFrobHom W).ker : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point) =
      Set.range (includePointBC W) := by
    rw [ker_oneSubGeomFrobHom_eq_fixedLocus, fixedLocus_geomFrobenius_eq_range_includePointBC]
  have hfin : (Set.range (includePointBC W)).Finite := Set.finite_range _
  rw [← hset] at hfin
  exact hfin.to_subtype

/-- **`#ker(1 − π)_{K̄} = pointCount W`** (PROVED, axiom-clean).  Via the linchpin the kernel is the
geometric-Frobenius fixed locus, whose cardinality is the `𝔽_q`-rational point count
(`ncard_ker_oneSubGeomFrobHom_eq_pointCount`).  This is the *clean half* of `hkerdeg`. -/
theorem oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom.ker =
      pointCount W.toAffine := by
  rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom]
  have hcard : Nat.card ↥(oneSubGeomFrobHom W).ker =
      ((oneSubGeomFrobHom W).ker : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [hcard, ncard_ker_oneSubGeomFrobHom_eq_pointCount]
  rfl

/-- **Witness 3 — `hkerdeg`, reduced to V.1.3** (axiom-clean reduction).  Given the degree identity
`φ_L.degree = pointCount W` (Silverman V.1.3, `isogOneSub_negFrobenius_degree_eq_pointCount`
base-changed through `hdeg_bc` — the project's known sharp residual), the separable degree match
`#ker(1 − π)_{K̄} = φ_L.degree` follows from the *proved* clean count
`#ker = pointCount`.

The V.1.3 degree identity is taken as a hypothesis so this reduction is itself axiom-clean and the
V.1.3 dependence is explicit (the caller supplies `hdeg_eq` from
`(oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange W p r L hq).trans
  (isogOneSub_negFrobenius_degree_eq_pointCount W hq)` once `hq` is available). -/
theorem oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).degree =
        pointCount W.toAffine) :
    Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom.ker =
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).degree := by
  rw [oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount, hdeg_eq]

/-- **Witness 2 — `hsurj` from the dual composition `φ ∘ δ = [N]`** (axiom-clean reduction).  For
any `N` with `(N : K̄) ≠ 0`, surjectivity of `[N]` on `E(K̄)`-points (`mulByInt_point_surjective`)
turns the dual composition `φ ∘ δ = [N]` into surjectivity of `φ`.  This is the second consequence
(alongside `hdc`) of bundling the divisor-pushforward dual as an `IsDualOf`. -/
theorem oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (δ : (W.baseChange (AlgebraicClosure K)).toAffine.Point →+
      (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (N : ℤ) (hN : (N : AlgebraicClosure K) ≠ 0)
    (hself :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom.comp δ =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine N).toAddMonoidHom) :
    Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom := by
  intro Q
  obtain ⟨R, hR⟩ := mulByInt_point_surjective (W.baseChange (AlgebraicClosure K)) N hN Q
  refine ⟨δ R, ?_⟩
  have hval := DFunLike.congr_fun hself R
  rw [AddMonoidHom.comp_apply] at hval
  rw [hval]
  rwa [mulByInt_apply] at hR ⊢

end Witnesses

section Assemble

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqAC'' : DecidableEq (AlgebraicClosure K) := Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

/-- **Assemble `OneSubScalingData` over `K̄` from only the still-open witnesses.**

Discharges `pullback_L` (concrete `oneSubFrobeniusPullback_L`), `hdeg_bc` (proved, no hypothesis),
`finiteKer` (proved), `hkerdeg` (from the V.1.3 identity `hdeg_eq`), and `hsurj` (from the dual composition
`hself` + `mulByInt_point_surjective`).  The caller supplies only the genuinely-deep divisor-level
residuals: the dual `δ` with *both* composition identities `hdc`/`hself` (an `IsDualOf`), the
divisor-pullback functoriality `hproj`, and the translation covariance `hcomm'`. -/
noncomputable def mkOneSubScalingDataConcrete_of_witnesses (hq : 2 ≤ Fintype.card K)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine)
    (hproj : ProjOrdTransport
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)))
    (δ : (W.baseChange (AlgebraicClosure K)).toAffine.Point →+
      (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (hdc :
      δ.comp (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine
          (Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hself :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.comp δ =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine
          (Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hNne :
      ((Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker : ℤ)
        : AlgebraicClosure K) ≠ 0)
    (hcomm' :
      ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
        (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
        (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) •
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T = 0),
        translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
              (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                  (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT)) =
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
              ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom S)
              (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                  (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT))) :
    OneSubScalingData W p r (AlgebraicClosure K) hq :=
  mkOneSubScalingDataConcrete W p r (AlgebraicClosure K) hq
    (oneSubFrobeniusIsogBaseChange_finiteKer W p r (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    hproj δ hdc (oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) δ _ hNne hself)
    (oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) hdeg_eq) hcomm'

end Assemble

end HasseWeil.WeilPairing
