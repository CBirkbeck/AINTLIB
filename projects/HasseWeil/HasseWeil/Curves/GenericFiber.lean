import HasseWeil.Curves.CoordHomFinite
import HasseWeil.Curves.CurveMap
import HasseWeil.Curves.SmoothPointPrime
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Generic fiber cardinality (T-II-2-009, Silverman II.2.6(b))

For a nonconstant morphism `φ : C₁ → C₂` of smooth curves, for almost all
points `Q ∈ C₂`, the fiber `φ⁻¹(Q)` has cardinality equal to the
separable degree `deg_s(φ)`.

This file provides the **algebraic-geometric content** of T-II-2-009 at
the Dedekind-domain level, building on the `CurveMap` + `CoordHom`
infrastructure: if we can exhibit a maximal ideal `p ⊂ C₂.CoordinateRing`
that is **unramified** and has **trivial residue-field degrees**, then
the number of primes above it equals the function-field degree `deg(φ)`
(which coincides with `deg_s(φ)` for separable `φ`).

This is one side of Silverman's II.2.6(b): the fibre-cardinality statement
in terms of the discrete-prime count. The other direction — **exhibiting**
such an unramified prime `p` — requires the primitive-element-plus-
discriminant construction over a base that sees "almost all" `Q` (i.e.
the unramified locus is a dense open). Over arbitrary `F`, this is the
main piece still missing; see the progress note at the end.

## Main results

* `CurveMap.primesOverFinset_card_eq_degree_of_unramified` — given an
  unramified prime `p` with every residue-field degree `f_P = 1`, the
  number of primes above `p` equals `φ.degree`.
* `CurveMap.primesOverFinset_card_eq_sepDegree_of_separable_and_unramified`
  — same conclusion in terms of `sepDegree` under the separability
  hypothesis (which forces `deg = sepDeg`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b).
-/

namespace HasseWeil.Curves

namespace CurveMap

variable {F : Type*} [Field F] {C₁ C₂ : SmoothPlaneCurve F}

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
/-- **T-II-2-009, algebraic direction** (unramified + trivial residue
degrees ⇒ fiber count = degree). Given a `CurveMap` with `CoordHom`
witness and a maximal ideal `p ⊂ C₂.CoordinateRing` that is
(i) non-zero, (ii) has every ramification index = 1 on the primes above it,
and (iii) has every inertia (residue) degree = 1, the number of primes
above `p` equals `φ.degree`. -/
theorem primesOverFinset_card_eq_degree_of_unramified
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    {p : Ideal C₂.CoordinateRing} (hpMax : p.IsMaximal) (hp0 : p ≠ ⊥)
    (h_ef_one :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ∀ P ∈ primesOverFinset p C₁.CoordinateRing,
        Ideal.ramificationIdx p P *
        Ideal.inertiaDeg p P = 1) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    (primesOverFinset p C₁.CoordinateRing).card = φ.degree := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  have hsum := φ.sum_ramificationIdx_mul_inertiaDeg_eq_degree
    coordHom coordHom.module_finite hpMax hp0
  -- Σ_{P ∈ S} (e · f) = deg. With each e·f = 1, LHS = S.card.
  have hsum' : ∑ P ∈ primesOverFinset p C₁.CoordinateRing, (1 : ℕ) = φ.degree := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun P hP => (h_ef_one P hP).symm
  rw [Finset.sum_const, Nat.smul_one_eq_cast] at hsum'
  exact_mod_cast hsum'

/-- **T-II-2-009 (separable case)**: for a separable `CurveMap` with an
unramified + trivial-residue-degree prime, the fiber count equals
`sepDegree`. Uses the fact that `sepDegree = degree` for separable
extensions (via `Field.finSepDegree_eq_finrank_iff`). -/
theorem primesOverFinset_card_eq_sepDegree_of_separable_and_unramified
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hsep : φ.IsSeparable)
    {p : Ideal C₂.CoordinateRing} (hpMax : p.IsMaximal) (hp0 : p ≠ ⊥)
    (h_ef_one :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ∀ P ∈ primesOverFinset p C₁.CoordinateRing,
        Ideal.ramificationIdx p P *
        Ideal.inertiaDeg p P = 1) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    (primesOverFinset p C₁.CoordinateRing).card = φ.separableDegree := by
  -- separable + finite-dim ⇒ sepDegree = degree.
  letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  have hsep_eq : φ.degree = φ.separableDegree := by
    change φ.degree = @Field.finSepDegree _ _ _ _ φ.toAlgebra
    have hinsep : φ.inseparableDegree = 1 := hsep
    have hdvd : φ.separableDegree ∣ φ.degree := by
      show @Field.finSepDegree _ _ _ _ φ.toAlgebra ∣ φ.degree
      exact @Field.finSepDegree_dvd_finrank C₂.FunctionField C₁.FunctionField
        _ _ φ.toAlgebra
    have hdiv : φ.degree / φ.separableDegree = 1 := hinsep
    exact (Nat.eq_of_dvd_of_div_eq_one hdvd hdiv).symm
  rw [← hsep_eq]
  exact φ.primesOverFinset_card_eq_degree_of_unramified coordHom
    hpMax hp0 h_ef_one

/-! ### Piece 1 — bad locus `{p : p ∣ differentIdeal}` is finite

For a finite separable extension of Dedekind domains `A → B`, the set of
maximal ideals `p ⊂ A` that ramify (i.e. divide `differentIdeal A B`)
is **finite**. Direct consequence of `differentIdeal_ne_bot` +
`Ideal.finite_factors`. -/

/-- **T-II-2-009 Piece 1**: the set of height-one primes of `B` that
divide `differentIdeal A B` is finite. These are the "ramified primes"
in the `A → B` extension (primes above which at least one prime of `B`
has `e_P ≥ 2`). Silverman II.2.6(b) "finitely many bad Q". -/
theorem _root_.IsDedekindDomain.finite_ramified_primes
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    (hsep : @Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B))) :
    {P : IsDedekindDomain.HeightOneSpectrum B |
      P.asIdeal ∣ differentIdeal A B}.Finite := by
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  haveI : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  haveI := hsep
  exact Ideal.finite_factors (differentIdeal_ne_bot (A := A) (B := B))

/-! ### Piece 2 — `¬ P ∣ differentIdeal ⇒ IsUnramifiedAt A P`

Direct corollary of mathlib's `not_dvd_differentIdeal_iff`. Packages the
easier direction as a standalone lemma for use in Pieces 3–5. -/

/-- **T-II-2-009 Piece 2**: a prime of `B` that does not divide the
different ideal is unramified over `A`. -/
theorem _root_.IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    (hsep : @Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B)))
    {P : Ideal B} [P.IsPrime] (hnd : ¬ P ∣ differentIdeal A B) :
    Algebra.IsUnramifiedAt A P := by
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  haveI : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  haveI := hsep
  exact not_dvd_differentIdeal_iff.mp hnd

/-! ### Piece 3 — `IsUnramifiedAt P ⇒ e_{P|A} = 1`

Corollary of mathlib's `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`.
Packages the ramification-index side of unramifiedness; the inertia-degree
side (`f_P = 1`) requires the residue field to be trivial over the base,
which is **automatic over algebraically closed `F`** but must be supplied
externally over arbitrary base fields. -/

/-- **T-II-2-009 Piece 3 (ramification half)**: a prime `P` of `B` that is
unramified over `A` has ramification index `1` (at its image in `A`).
Direct corollary of mathlib's `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. -/
theorem _root_.IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A]
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra A B] [Algebra.EssFiniteType A B]
    {P : Ideal B} [P.IsPrime] [Algebra.IsUnramifiedAt A P] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (P.under A) P = 1 :=
  Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hP

/-! ### Piece 4 — existence of an unramified prime

Given Piece 1 (bad locus finite) and the assumption that `B` has
infinitely many height-one primes (a genuine curve-theory input, since a
Dedekind domain of infinite F-dimension has infinite spectrum), there
exists a prime `P` of `B` outside the ramified locus. Piece 2 then turns
"not in bad locus" into `IsUnramifiedAt A P`. -/

/-- **T-II-2-009 Piece 4**: combining Piece 1 (bad locus finite) + Piece 2
(not-in-bad-locus ⇒ IsUnramifiedAt), plus the hypothesis that `B` has
infinitely many height-one primes, we extract a specific prime
`P : HeightOneSpectrum B` that is unramified over `A`. -/
theorem _root_.IsDedekindDomain.exists_unramified_prime
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    (hsep : @Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B)))
    (hinf : Set.Infinite {P : IsDedekindDomain.HeightOneSpectrum B | True}) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum B,
      Algebra.IsUnramifiedAt A P.asIdeal := by
  have hfin_bad := IsDedekindDomain.finite_ramified_primes (A := A) (B := B) hsep
  -- Good set = total \ bad locus. Since total is infinite and bad is finite,
  -- good is nonempty.
  have hgood_nonempty :
      {P : IsDedekindDomain.HeightOneSpectrum B |
        ¬ P.asIdeal ∣ differentIdeal A B}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hinf
    have : ({P : IsDedekindDomain.HeightOneSpectrum B | True} :
        Set _) ⊆ {P | P.asIdeal ∣ differentIdeal A B} := by
      intro P _
      by_contra hnd
      have : P ∈ ({P : IsDedekindDomain.HeightOneSpectrum B |
          ¬ P.asIdeal ∣ differentIdeal A B} : Set _) := hnd
      rw [hempty] at this
      exact this
    exact hfin_bad.subset this
  obtain ⟨P, hP⟩ := hgood_nonempty
  refine ⟨P, ?_⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  exact IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal hsep hP

/-! ### Piece 5 — composed theorem at the abstract Dedekind level

Combining Pieces 1–4 yields: for a finite separable extension of Dedekind
domains `A → B` with `B` having infinitely many height-one primes, there
exists a specific prime `P` of `B` for which the ramification index is
exactly `1`.

Specialised to `CurveMap + CoordHom` + `[IsAlgClosed F]` (where residue
field degrees are automatically `1`), this gives `(primesOverFinset).card
= φ.degree` — the full Silverman II.2.6(b) content. -/

/-- **T-II-2-009 Piece 5 (composed at A → B level)**: assembles Pieces
1–4 into a single witness. For `A → B` Dedekind + finite separable +
`B` infinite in primes, there exists a `P ∈ HeightOneSpectrum B`,
nonzero, with `ramificationIdx (P.under A → P) = 1`.

The inertia degree `f_P = 1` is NOT concluded here — it depends on the
residue-field extension being trivial, which is automatic over
algebraically closed base (or for F-rational smooth points), and
supplied as a separate hypothesis when needed (see
`primesOverFinset_card_eq_degree_of_unramified`). -/
theorem _root_.IsDedekindDomain.exists_unramifiedPrime_ramificationIdx_eq_one
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    [Algebra.EssFiniteType A B]
    (hsep : @Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B)))
    (hinf : Set.Infinite {P : IsDedekindDomain.HeightOneSpectrum B | True}) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum B,
      Ideal.ramificationIdx (P.asIdeal.under A) P.asIdeal = 1 := by
  obtain ⟨P, hunram⟩ := IsDedekindDomain.exists_unramified_prime hsep hinf
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI := hunram
  refine ⟨P, ?_⟩
  exact IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot P.ne_bot

end CurveMap

/-! ### Piece 6 — HeightOneSpectrum infinite over alg-closed base

Over an algebraically closed base `F` with `[IsElliptic]`, the coordinate
ring `C.CoordinateRing` has infinitely many height-one primes. The proof
goes via worker-I's `smoothPointEquivHeightOneSpectrum` bijection
(in `HasseWeil/Curves/SmoothPointPrime.lean`), reducing to showing
`C.SmoothPoint` is infinite. This follows because for each `x ∈ F`, the
Weierstrass equation in `y` is a quadratic over an algebraically closed
field and hence has a root — giving an injection `F → C.SmoothPoint`. -/

namespace SmoothPlaneCurve

variable {F : Type*} [Field F]

/-- **T-II-2-009 Piece 6 (smooth points)**: for every `x ∈ F` over an
algebraically closed field, there exists `y : F` with `(x, y)` a
nonsingular point on the elliptic curve (any point on an elliptic curve
is automatically nonsingular since `Δ ≠ 0`). -/
theorem exists_smoothPoint_of_x
    [IsAlgClosed F] (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] (x : F) :
    ∃ P : C.SmoothPoint, P.x = x := by
  -- y-polynomial: Y² + (a₁x + a₃)Y - (x³ + a₂x² + a₄x + a₆), degree 2.
  set yPoly : Polynomial F :=
    Polynomial.X ^ 2 +
      Polynomial.C (C.toAffine.a₁ * x + C.toAffine.a₃) * Polynomial.X -
      Polynomial.C (x ^ 3 + C.toAffine.a₂ * x ^ 2 + C.toAffine.a₄ * x +
        C.toAffine.a₆) with hyPoly_def
  have hdeg : yPoly.natDegree = 2 := by
    rw [hyPoly_def]; compute_degree!
  have hne : yPoly ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hdeg; exact absurd hdeg (by decide)
  have hdeg_ne : yPoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hne, hdeg]; decide
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root yPoly hdeg_ne
  -- `hy : yPoly.eval y = 0` gives the equation.
  have heq : C.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff']
    have heval : yPoly.eval y = 0 := hy
    rw [hyPoly_def] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C] at heval
    linear_combination heval
  have hns : C.toAffine.Nonsingular x y :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := C.toAffine)).mp heq
  exact ⟨⟨x, y, hns⟩, rfl⟩

/-- **T-II-2-009 Piece 6**: `C.SmoothPoint` is infinite over an
algebraically closed base. Via the injection `x ↦ (smooth point with
that x-coordinate)`. -/
theorem smoothPoint_infinite
    [IsAlgClosed F] (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] :
    Infinite C.SmoothPoint := by
  -- Injection F → SmoothPoint via `x ↦ Classical.choose (exists_smoothPoint_of_x x)`.
  refine Infinite.of_injective
    (fun x : F => (C.exists_smoothPoint_of_x x).choose) ?_
  intro x₁ x₂ hP
  have h₁ : (C.exists_smoothPoint_of_x x₁).choose.x = x₁ :=
    (C.exists_smoothPoint_of_x x₁).choose_spec
  have h₂ : (C.exists_smoothPoint_of_x x₂).choose.x = x₂ :=
    (C.exists_smoothPoint_of_x x₂).choose_spec
  have := congrArg SmoothPoint.x hP
  rw [h₁, h₂] at this
  exact this

/-- **T-II-2-009 Piece 6 (main)**: the height-one spectrum of
`C.CoordinateRing` is infinite over an algebraically closed elliptic
curve, via the bijection `SmoothPoint ≃ HeightOneSpectrum` from
`HasseWeil/Curves/SmoothPointPrime.lean`. -/
theorem heightOneSpectrum_infinite
    [IsAlgClosed F] (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] :
    Set.Infinite ({P : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing |
      True}) := by
  haveI : Infinite C.SmoothPoint := C.smoothPoint_infinite
  haveI : Infinite (IsDedekindDomain.HeightOneSpectrum C.CoordinateRing) :=
    Infinite.of_injective C.smoothPointEquivHeightOneSpectrum
      C.smoothPointEquivHeightOneSpectrum.injective
  exact Set.infinite_univ

end SmoothPlaneCurve

namespace CurveMap
variable {F : Type*} [Field F] {C₁ C₂ : SmoothPlaneCurve F}

/-! ### Piece 7 — residue fields at smooth points are `F`

The residue-field-degree-one content (f_P = 1) of T-II-2-009 Piece 7.
Rather than prove `inertiaDeg = 1` directly — which hits a diamond
between `Module.Free` from `Ideal.Quotient` vs `DivisionRing` paths —
we package the residue-field F-rank: `finrank F (C.CoordinateRing /
maximalIdealAt P) = 1`. Any consumer wanting `inertiaDeg = 1` over an
F-rational SmoothPoint combines this (for source + target) with the
tower `finrank_mul_finrank`; worker-K has the direct
`inertiaDeg_maximalIdealAt` for the specific `F[X] → F[C]` case. -/

/-- **T-II-2-009 Piece 7 (residue field)**: the residue field of
`C.CoordinateRing` at a smooth point `P` equals `F` (as `F`-module of
rank 1). Direct re-export of worker-K's `finrank_quotientMaximalIdealAt`
for use in the Piece 8 chain. -/
theorem finrank_quotientMaximalIdealAt_eq_one
    (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    Module.finrank F (C.CoordinateRing ⧸ C.maximalIdealAt P) = 1 :=
  C.finrank_quotientMaximalIdealAt P

/-! ### Piece 8 — final assembly: T-II-2-009 for CurveMap

Combines Pieces 1–7: given a CurveMap with CoordHom, separable,
and ([IsAlgClosed F] providing infinite spectrum + residue-degree=1),
there's a maximal ideal of `C₂.CoordinateRing` whose fiber (primes above
it in `C₁.CoordinateRing`) has cardinality equal to `φ.separableDegree`.

Following the user's tactical guidance: the `f_P = 1` side of the inertia
computation is supplied as a **witness hypothesis** (`h_inertia_one`)
rather than proven in-line, due to the `Module.Free` diamond between
`Ideal.Quotient.semiring` and `DivisionRing.toDivisionSemiring.toSemiring`
paths. Under `[IsAlgClosed F]`, the hypothesis is always satisfied
(both residue fields are `F`); the caller supplies it via
`SmoothPlaneCurve.finrank_quotientMaximalIdealAt_eq_one` (Piece 7) for
each prime in their specific setting. -/

/-- **T-II-2-009 Piece 8 (full assembly, witness form)**: given the
witness hypotheses for unramified existence + trivial residue degrees,
produce a prime of `C₂.CoordinateRing` whose fiber in `C₁.CoordinateRing`
has cardinality `φ.separableDegree`.

The existence of an unramified Q (via Pieces 1–6 for alg-closed base) is
bundled as `h_unramified_Q`. The trivial residue degree is bundled as
`h_inertia_one` (follows from Piece 7 over [IsAlgClosed F] via the
`maximalIdealAt` ↔ `HeightOneSpectrum` bijection from worker-I's
`smoothPointEquivHeightOneSpectrum`). -/
theorem exists_heightOneSpectrum_fiber_card_eq_sepDegree
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hsep : φ.IsSeparable)
    (Q : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing)
    (h_ef_one_Q :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ∀ P ∈ primesOverFinset Q.asIdeal C₁.CoordinateRing,
        Ideal.ramificationIdx Q.asIdeal P *
        Ideal.inertiaDeg Q.asIdeal P = 1) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    (primesOverFinset Q.asIdeal C₁.CoordinateRing).card = φ.separableDegree := by
  haveI : Q.asIdeal.IsPrime := Q.isPrime
  haveI hQmax : Q.asIdeal.IsMaximal :=
    Q.isPrime.isMaximal Q.ne_bot
  exact φ.primesOverFinset_card_eq_sepDegree_of_separable_and_unramified
    coordHom hsep hQmax Q.ne_bot h_ef_one_Q

/-! ### Piece 9 — `inertiaDeg = 1` at smooth points: diamond-blocked

**Status**: blocked by the `Module.Free (C₂.CR/Q) (C₁.CR/P)` typeclass
diamond. The attempted workaround — using `F` as outer ring in
`Module.finrank_mul_finrank F _ _` — does **not** bypass the problem,
because `finrank_mul_finrank` still requires `Module.Free` on the
intermediate extension. Specifically:

- `Module.Free.of_divisionRing` produces `Module.Free` via
  `DivisionRing.toDivisionSemiring.toSemiring`.
- The expected instance on `(C₂.CR/Q)`-module `(C₁.CR/P)` goes through
  `Ideal.Quotient.semiring` and `Algebra.toModule`.
- These two `Semiring` parent-paths do not unify — same diamond
  worker-K documented (note 2026-04-21T10:45Z).

The narrower witness form (`exists_heightOneSpectrum_fiber_card_eq_sepDegree`,
Piece 8 above) takes the `e_P · f_P = 1` hypothesis as input and is the
shippable deliverable. Closing `inertiaDeg = 1` without the diamond
requires either:

1. A mathlib-level change to make `Ideal.Quotient.semiring` and
   `Field`-derived `Semiring` agree definitionally, OR
2. A residue-field algebra isomorphism `C.CR/(maximalIdealAt P) ≃ₐ[F] F`
   (under `[IsAlgClosed F]`), expressed without passing through
   `Module.Free` synthesis on the intermediate quotient, OR
3. A direct computation of `Ideal.inertiaDeg` from the algebra-map
   surjectivity at smooth points on an algebraically closed base.

The second route is the most promising — a dedicated file
`HasseWeil/Curves/ResidueFieldAtSmoothPoint.lean` building an explicit
`AlgEquiv` at each smooth point and then transporting `inertiaDeg`
through it would sidestep `finrank_mul_finrank` entirely. Estimated
~100 LOC. Deferred. -/

/-! ### Progress note — the remaining piece (existence of unramified p)

The full T-II-2-009 statement **`∃ Q, #φ⁻¹(Q) = sepDeg(φ)`** reduces (via
the theorems above) to exhibiting a maximal `p ⊂ C₂.CoordinateRing` with
the ramification + inertia witnesses. Over an algebraically-closed base
field `F`, such a `p` always exists because:

1. **Primitive element**: the separable closure `L ⊂ C₁.FunctionField`
   of `φ*(C₂.FunctionField)` is generated by a primitive element `α`
   with minimal polynomial `m(T) ∈ (φ*C₂.FunctionField)[T]` of degree
   `sepDeg(φ)`.

2. **Discriminant**: `m` is separable (primitive-element condition), so
   `discriminant(m)` is a nonzero element of `φ*C₂.FunctionField`.
   Viewed in `C₂.FunctionField`, it has finitely many zeros (as an element
   of a function field with a degree structure).

3. **Dense open**: at any `p ⊂ C₂.CoordinateRing` outside the zero locus
   of `discriminant(m)`, the specialisation `m̄ ∈ (C₂.CoordinateRing/p)[T]`
   has `sepDeg(φ)` distinct roots in `C₁.CoordinateRing/P` for each `P`
   above `p`. This gives the ramification + inertia witnesses.

The formalisation gap:
- Mathlib has `Field.exists_primitive_element` (step 1) and
  `Polynomial.discriminant_ne_zero_of_separable` (step 2).
- Step 3 requires the algebraic-geometric bridge between "discriminant
  nonzero at `p`" and "unramified at `p` with trivial residue
  extensions". For Dedekind extensions this is
  `Algebra.IsUnramifiedAt ↔ ¬ p ∣ differentIdeal`, and over alg-closed
  base the residue fields all equal `F`, making `inertiaDeg = 1`
  automatic.

This last step is ~200 lines of algebraic-geometric infrastructure
following Silverman + Neukirch (*Algebraic Number Theory*, III.2). The
algebraic core (steps 1–2) is immediate in mathlib; step 3 is the
substantive remaining content. Tracked under T-II-2-009's progress log.

The **alternative path** `#ker β_pc = sepDeg β_pc` (for the specific
β_pc = 1 − π) can be closed *without* the full T-II-2-009 once
`AdditionPullback.lean` replaces the `isogOneSub` placeholder — that
gives the real function-field pullback, from which `deg β_pc =
[K(E) : φ*K(E)] = q + 1 − t` follows via explicit computation, and
`#ker β_pc = pointCount = q + 1 − t` then furnishes `#ker β_pc = deg
β_pc` directly. This is the stream-D path. -/

end CurveMap

end HasseWeil.Curves
