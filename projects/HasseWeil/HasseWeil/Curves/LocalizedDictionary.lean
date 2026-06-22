/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.GoodAffineLocus
import HasseWeil.Curves.GenericFiber
import HasseWeil.Curves.NormValuation
import HasseWeil.Curves.Infinity
import HasseWeil.Curves.PointFunctor
import Mathlib.Algebra.Polynomial.Lifts

/-!
# The localized fibre dictionary (ROUTE-W, ticket W-3b)

**The good-fibre count without a global coordinate-ring witness.**  For a finite separable
extension `K(C₁) / K(C₂)` of smooth-curve function fields (e.g. the pullback of a separable
isogeny of degree `> 1`, which has *no* global `CoordHom` because the pullback has poles at
the affine kernel points), we localize: `Af` is the coordinate ring of `C₂` away from a
single denominator `f`, and `D := integralClosure Af K(C₁)` is the corresponding Dedekind
extension (`GoodAffineLocus`).  The maximal ideals of `D` over a good maximal ideal of `Af`
are then put in bijection with smooth points of `C₁` *evaluating* to the chosen target point:

1. **`f` swallows the minimal-polynomial denominators** of the coordinate functions
   `x₁, y₁ ∈ K(C₁)`, so `x₁, y₁` are integral over `Af` and the whole coordinate ring
   `F[C₁]` lands in `D` (`coordRing_mem_integralClosure`).
2. **Residue fields are trivial** over an algebraically closed base: `Af⧸q ≅ F` for the
   good maximal ideals `q` (`residue_away_bijective`) and `D⧸P ≅ F` for every maximal `P`
   over `q` (`residue_closure_bijective`), giving inertia degree `1`
   (`inertiaDeg_eq_one_of_under_eq`).
3. **Each maximal `P` of `D` is a point**: the residue character `F[C₁] → D⧸P ≅ F` has a
   maximal kernel, which is `maximalIdealAt` of a smooth point `pointAt P`
   (`exists_smoothPoint_of_isMaximal`); the valuation of that point is `< 1` on all of `P`
   (`pointValuation_lt_one_of_mem_prime`) — the place of `P` *is* the place of the point.
   The engine is the intermediate-ring maximality of a discrete valuation ring in its
   fraction field (`le_one_of_forall_le_one_mem_of_ne_top`).
4. **Counting**: `Σ e·f = [K(C₁):K(C₂)]` at `(Af, D)` (mathlib's
   `Ideal.sum_ramification_inertia`) with `e = 1` away from the finite different-ideal
   locus (`GoodAffineLocus.exists_finite_ramification_locus`) and `f = 1` (step 2), and the
   point assignment of step 3 is injective (`pointAt_injective`), produces a target point
   `Q` avoiding any prescribed finite set together with `[K(C₁):K(C₂)]` distinct smooth
   points of `C₁` at which the pulled-back coordinate functions of `C₂` evaluate to the
   coordinates of `Q` (`exists_good_fiber_points` — the W-3b headline).

`HasseWeil/EC/KernelCountGeneral.lean` consumes the headline through the cofinite
`PullbackEvaluation` coherence to conclude `#ker β = deg β` for general separable
isogenies.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), II.2.7, III.4.10(c).
-/

open scoped nonZeroDivisors

namespace HasseWeil.Curves.LocalizedDictionary

/-! ### The intermediate-ring lemma

A discrete valuation ring is maximal among proper subrings of its fraction field: if a
subring `R` of `L` contains the valuation ring `{v ≤ 1}` of a `ℤᵐ⁰`-valued valuation and
is not all of `L`, then `R` is contained in (hence equal to) the valuation ring.  The
proof is the classical anti-uniformizer generation: from one element of value `> 1` and
the valuation ring one reaches every element of `L`. -/

/-- **DVR maximality, valuation form**: a subring `R ⊆ L` containing the valuation ring
of `v` (`hO`) and different from `L` (`hR`) is contained in the valuation ring.  If some
`z ∈ R` had `1 < v z`, then any `w : L` would satisfy `w = (w · z⁻ᵏ) · zᵏ ∈ R` for `k`
with `v w ≤ (v z)ᵏ`, forcing `R = ⊤`. -/
theorem le_one_of_forall_le_one_mem_of_ne_top {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) {R : Subring L}
    (hO : ∀ x : L, v x ≤ 1 → x ∈ R) (hR : R ≠ ⊤) :
    ∀ z ∈ R, v z ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hzR, hz⟩ := hcon
  refine hR (eq_top_iff.mpr fun w _ ↦ ?_)
  rcases le_or_gt (v w) 1 with hw | hw
  · exact hO w hw
  · -- both `v z` and `v w` exceed `1`; pick `k` with `v w ≤ (v z)ᵏ`
    have hz0 : v z ≠ 0 := ne_of_gt (lt_trans zero_lt_one hz)
    have hw0 : v w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v w ≤ (v z) ^ k := by
      set a := WithZero.unzero hz0 with ha
      set b := WithZero.unzero hw0 with hb
      have hva : v z = (a : WithZero (Multiplicative ℤ)) := (WithZero.coe_unzero hz0).symm
      have hvb : v w = (b : WithZero (Multiplicative ℤ)) := (WithZero.coe_unzero hw0).symm
      have ha1 : (0 : ℤ) < a.toAdd := by
        have := hz
        rw [hva, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt,
          toAdd_one] at this
        exact this
      refine ⟨b.toAdd.toNat, ?_⟩
      rw [hva, hvb, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
        toAdd_pow, nsmul_eq_mul]
      have h1 : b.toAdd ≤ (b.toAdd.toNat : ℤ) := Int.self_le_toNat _
      have h2 : (b.toAdd.toNat : ℤ) * 1 ≤ (b.toAdd.toNat : ℤ) * a.toAdd :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      rw [mul_one] at h2
      linarith
    -- write `w = (w / zᵏ) · zᵏ` with the first factor in the valuation ring
    have hzne : z ≠ 0 := fun h ↦ hz0 (h ▸ map_zero v)
    have hzkne : z ^ k ≠ 0 := pow_ne_zero _ hzne
    have hwdec : w = w / z ^ k * z ^ k := (div_mul_cancel₀ w hzkne).symm
    rw [hwdec]
    refine R.mul_mem (hO _ ?_) (R.pow_mem hzR k)
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hk (zero_le)

variable {F : Type*} [Field F]

/-! ### The coordinate generators in the function field -/

section CoordFun

variable (C₁ : SmoothPlaneCurve F)

/-- The image of the coordinate generator `X` of `C₁` in `K(C₁)`. -/
noncomputable abbrev coordXFun : C₁.FunctionField :=
  algebraMap C₁.CoordinateRing C₁.FunctionField
    (WeierstrassCurve.Affine.CoordinateRing.mk C₁.toAffine (Polynomial.C Polynomial.X))

/-- The image of the coordinate generator `Y` of `C₁` in `K(C₁)`. -/
noncomputable abbrev coordYFun : C₁.FunctionField :=
  algebraMap C₁.CoordinateRing C₁.FunctionField
    (WeierstrassCurve.Affine.CoordinateRing.mk C₁.toAffine Polynomial.X)

end CoordFun

variable (C₂ : SmoothPlaneCurve F) (f : C₂.CoordinateRing)
variable (Af : Type*) [CommRing Af] [Algebra C₂.CoordinateRing Af] [IsLocalization.Away f Af]

/-! ### Residue fields of the good affine coordinate ring

For a smooth point `Q` of `C₂` with `f ∉ m_Q`, the extension `q := m_Q · Af` is a
nonzero maximal ideal of `Af` lying over `m_Q`, and the residue map `F → Af⧸q` is
bijective over an algebraically closed base (`f` is a unit in `Af`, so the residue of any
`a/fⁿ` is reached from residues of coordinate-ring elements). -/

section Residue

variable {C₂} (Q : C₂.SmoothPoint)

/-- The maximal ideal of the good affine coordinate ring `Af` at a smooth point `Q` of
`C₂` off the locus `{f = 0}`: the extension of `maximalIdealAt Q`. -/
noncomputable abbrev awayIdealAt : Ideal Af :=
  Ideal.map (algebraMap C₂.CoordinateRing Af) (C₂.maximalIdealAt Q)

/-- The powers of `f` avoid `m_Q` when `f ∉ m_Q` (it is prime). -/
theorem disjoint_powers_maximalIdealAt (hfQ : f ∉ C₂.maximalIdealAt Q) :
    Disjoint (Submonoid.powers f : Set C₂.CoordinateRing) (C₂.maximalIdealAt Q) := by
  rw [Set.disjoint_left]
  rintro x ⟨n, rfl⟩ hxQ
  exact hfQ ((C₂.maximalIdealAt_isPrime Q).mem_of_pow_mem n hxQ)

/-- `awayIdealAt Q` lies over `m_Q`. -/
theorem awayIdealAt_under (hfQ : f ∉ C₂.maximalIdealAt Q) :
    (awayIdealAt Af Q).under C₂.CoordinateRing = C₂.maximalIdealAt Q :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) Af
    (C₂.maximalIdealAt_isPrime Q) (disjoint_powers_maximalIdealAt f Q hfQ)

theorem awayIdealAt_isPrime (hfQ : f ∉ C₂.maximalIdealAt Q) :
    (awayIdealAt Af Q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Af _
    (C₂.maximalIdealAt_isPrime Q) (disjoint_powers_maximalIdealAt f Q hfQ)

theorem awayIdealAt_ne_bot (hf : f ≠ 0) : awayIdealAt Af Q ≠ ⊥ := by
  intro hbot
  have hker : C₂.maximalIdealAt Q ≤ RingHom.ker (algebraMap C₂.CoordinateRing Af) :=
    (Ideal.map_eq_bot_iff_le_ker _).mp hbot
  have hinj : Function.Injective (algebraMap C₂.CoordinateRing Af) :=
    IsLocalization.injective Af
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hf))
  rw [RingHom.injective_iff_ker_eq_bot] at hinj
  rw [hinj, le_bot_iff] at hker
  exact C₂.maximalIdealAt_ne_bot Q hker

theorem awayIdealAt_isMaximal [IsIntegrallyClosed C₂.CoordinateRing] (hf : f ≠ 0)
    (hfQ : f ∉ C₂.maximalIdealAt Q) :
    (awayIdealAt Af Q).IsMaximal := by
  haveI := GoodAffineLocus.isDedekindDomain_away C₂ f Af hf
  exact (awayIdealAt_isPrime f Af Q hfQ).isMaximal (awayIdealAt_ne_bot f Af Q hf)

/-- The concrete residue map `F → Af ⧸ q` along `F → F[C₂] → Af → Af⧸q` (no `F`-algebra
structure on `Af` is assumed). -/
noncomputable def residueAway : F →+* Af ⧸ awayIdealAt Af Q :=
  (Ideal.Quotient.mk (awayIdealAt Af Q)).comp
    ((algebraMap C₂.CoordinateRing Af).comp (algebraMap F C₂.CoordinateRing))

/-- Every residue of a coordinate-ring element in `Af⧸q` is a scalar: for `g : F[C₂]`
there is `c : F` with `residueAway c = mk (algebraMap g)`.  This is `F → F[C₂]⧸m_Q`
bijective (`hbij2`, from `IsAlgClosed F`) transported across `q ∩ F[C₂] = m_Q`
(`awayIdealAt_under`). -/
private theorem residueAway_eq_mk_algebraMap [IsAlgClosed F]
    (hfQ : f ∉ C₂.maximalIdealAt Q) (g : C₂.CoordinateRing) :
    ∃ c : F, residueAway Af Q c =
      Ideal.Quotient.mk (awayIdealAt Af Q) (algebraMap C₂.CoordinateRing Af g) := by
  have hbij2 := C₂.algebraMap_bijective_quotient_of_maximal (C₂.maximalIdealAt_isMaximal Q)
  obtain ⟨c, hc⟩ := hbij2.2 (Ideal.Quotient.mk (C₂.maximalIdealAt Q) g)
  refine ⟨c, ?_⟩
  have hle : C₂.maximalIdealAt Q ≤
      (awayIdealAt Af Q).comap (algebraMap C₂.CoordinateRing Af) :=
    le_of_eq (awayIdealAt_under f Af Q hfQ).symm
  have happ := congrArg
    (Ideal.quotientMap (awayIdealAt Af Q) (algebraMap C₂.CoordinateRing Af) hle) hc
  rw [show (algebraMap F (C₂.CoordinateRing ⧸ C₂.maximalIdealAt Q)) c =
    Ideal.Quotient.mk (C₂.maximalIdealAt Q) (algebraMap F C₂.CoordinateRing c) from rfl,
    Ideal.quotientMap_mk, Ideal.quotientMap_mk] at happ
  exact happ

/-- **Surjectivity** of the residue map `F → Af⧸q`.  Any element of `Af` is `a/fⁿ`; the
residue of `a` is a scalar `ca` and the residue of `f` is a nonzero scalar `cf` (both via
`residueAway_eq_mk_algebraMap`; `cf ≠ 0` since `f` is a unit in `Af`), so `a/fⁿ` has
scalar residue `ca / cfⁿ`. -/
private theorem residueAway_surjective [IsAlgClosed F]
    (hfQ : f ∉ C₂.maximalIdealAt Q) :
    Function.Surjective (residueAway Af Q) := by
  classical
  haveI hqprime : (awayIdealAt Af Q).IsPrime := awayIdealAt_isPrime f Af Q hfQ
  haveI : IsDomain (Af ⧸ awayIdealAt Af Q) := inferInstance
  intro w
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨⟨a, s⟩, h1⟩ := IsLocalization.surj (Submonoid.powers f) z
  obtain ⟨n, hsn⟩ := s.2
  obtain ⟨ca, hca⟩ := residueAway_eq_mk_algebraMap f Af Q hfQ a
  obtain ⟨cf, hcf⟩ := residueAway_eq_mk_algebraMap f Af Q hfQ f
  -- `mk z · (mk f-image)ⁿ = mk a-image` from the localization relation
  have hspec := congrArg (Ideal.Quotient.mk (awayIdealAt Af Q)) h1
  rw [map_mul, show ((s : Submonoid.powers f) : C₂.CoordinateRing) = f ^ n from hsn.symm,
    map_pow, map_pow] at hspec
  -- the residue of `f` is a nonzero scalar
  have hfu : IsUnit (Ideal.Quotient.mk (awayIdealAt Af Q)
      (algebraMap C₂.CoordinateRing Af f)) :=
    (IsLocalization.map_units Af (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)).map _
  have hcf0 : cf ≠ 0 := by
    rintro rfl
    rw [map_zero] at hcf
    exact hfu.ne_zero hcf.symm
  refine ⟨ca / cf ^ n, ?_⟩
  have hcfu : IsUnit (residueAway Af Q (cf ^ n)) := by
    rw [map_pow, hcf]
    exact hfu.pow n
  refine hcfu.mul_right_cancel ?_
  rw [← map_mul, div_mul_cancel₀ ca (pow_ne_zero n hcf0), hca, map_pow, hcf, ← hspec]

/-- **Residue triviality for the good affine open over `K̄`**: the residue map
`F → Af⧸q` at a smooth point off `{f = 0}` is bijective.  Surjectivity: any element of
`Af` is `a/fⁿ`; the residue of `a` is a scalar (`F → F[C₂]⧸m_Q` is bijective), the
residue of `f` is a nonzero scalar (`f` is a unit in `Af`), so `a/fⁿ` has scalar
residue. -/
theorem residue_away_bijective [IsAlgClosed F]
    (hfQ : f ∉ C₂.maximalIdealAt Q) :
    Function.Bijective (residueAway Af Q) := by
  haveI hqprime : (awayIdealAt Af Q).IsPrime := awayIdealAt_isPrime f Af Q hfQ
  haveI : IsDomain (Af ⧸ awayIdealAt Af Q) := inferInstance
  exact ⟨(residueAway Af Q).injective, residueAway_surjective f Af Q hfQ⟩

end Residue

/-! ### The coordinate ring of `C₁` lands in the integral closure -/

section Extension

variable {C₁ : SmoothPlaneCurve F}
variable [algKL : Algebra C₂.FunctionField C₁.FunctionField]
  [finKL : FiniteDimensional C₂.FunctionField C₁.FunctionField]
  [algAfK : Algebra Af C₂.FunctionField]
  [twAfK : IsScalarTower C₂.CoordinateRing Af C₂.FunctionField]
  [algAfL : Algebra Af C₁.FunctionField]
  [twAfKL : IsScalarTower Af C₂.FunctionField C₁.FunctionField]
  [twFKL : IsScalarTower F C₂.FunctionField C₁.FunctionField]

-- Instance resolution on the subalgebra `integralClosure Af C₁.FunctionField` needs to
-- identify `Module`/`Algebra` structures along different projection paths, exactly as in
-- `HasseWeil/Curves/GoodAffineLocus.lean` (same idiom).
set_option backward.isDefEq.respectTransparency false

include C₂ in
omit finKL in
/-- Scalars of `F` are integral over `Af` (each `c : F` is a root of `X − c` with the
constant viewed in `Af` through `F → F[C₂] → Af`). -/
theorem scalar_mem_integralClosure (c : F) :
    algebraMap F C₁.FunctionField c ∈ integralClosure Af C₁.FunctionField := by
  set a₀ : Af := algebraMap C₂.CoordinateRing Af (algebraMap F C₂.CoordinateRing c) with ha₀
  have hval : algebraMap Af C₁.FunctionField a₀ = algebraMap F C₁.FunctionField c := by
    rw [ha₀, IsScalarTower.algebraMap_apply Af C₂.FunctionField C₁.FunctionField,
      ← IsScalarTower.algebraMap_apply C₂.CoordinateRing Af C₂.FunctionField,
      ← IsScalarTower.algebraMap_apply F C₂.CoordinateRing C₂.FunctionField,
      ← IsScalarTower.algebraMap_apply F C₂.FunctionField C₁.FunctionField]
  exact ⟨Polynomial.X - Polynomial.C a₀, Polynomial.monic_X_sub_C a₀, by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, hval, sub_self]⟩

omit twFKL in
/-- The denominator-swallowing criterion: if every coefficient of the minimal polynomial
of `z ∈ K(C₁)` over `K(C₂)` becomes integral after one multiplication by `f`, then `z` is
integral over `Af = F[C₂][1/f]` (lift the monic minimal polynomial along
`Af → K(C₂)` via `Polynomial.lifts_and_degree_eq_and_monic`). -/
theorem isIntegral_of_denominator (hf : f ≠ 0) (z : C₁.FunctionField)
    (hden : ∀ i, ∃ a : C₂.CoordinateRing,
      (minpoly C₂.FunctionField z).coeff i * algebraMap C₂.CoordinateRing C₂.FunctionField f
        = algebraMap C₂.CoordinateRing C₂.FunctionField a) :
    IsIntegral Af z := by
  have hzint : IsIntegral C₂.FunctionField z := IsIntegral.of_finite _ z
  have hmonic : (minpoly C₂.FunctionField z).Monic := minpoly.monic hzint
  have hfK : algebraMap C₂.CoordinateRing C₂.FunctionField f ≠ 0 :=
    fun h ↦ hf ((map_eq_zero_iff _
      (IsFractionRing.injective C₂.CoordinateRing C₂.FunctionField)).mp h)
  -- every coefficient of the minimal polynomial is in the image of `Af`
  have hrange : ∀ i, (minpoly C₂.FunctionField z).coeff i ∈
      Set.range (algebraMap Af C₂.FunctionField) := by
    intro i
    obtain ⟨a, ha⟩ := hden i
    refine ⟨IsLocalization.mk' Af a (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f), ?_⟩
    have hsp := IsLocalization.mk'_spec Af a
      (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)
    have hps := congrArg (algebraMap Af C₂.FunctionField) hsp
    rw [map_mul, ← IsScalarTower.algebraMap_apply C₂.CoordinateRing Af C₂.FunctionField,
      ← IsScalarTower.algebraMap_apply C₂.CoordinateRing Af C₂.FunctionField] at hps
    exact mul_right_cancel₀ hfK (hps.trans ha.symm)
  -- lift the monic minimal polynomial along `Af → K(C₂)`
  have hlift : minpoly C₂.FunctionField z ∈
      Polynomial.lifts (algebraMap Af C₂.FunctionField) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ hrange i
  obtain ⟨q, hq_map, _, hq_monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  have h0 : Polynomial.aeval z (minpoly C₂.FunctionField z) = 0 := minpoly.aeval _ _
  rw [← hq_map, Polynomial.aeval_map_algebraMap] at h0
  exact ⟨q, hq_monic, by simpa [Polynomial.aeval_def] using h0⟩

include C₂ in
omit finKL in
/-- If the coordinate generators `x₁, y₁` of `C₁` are integral over `Af`, the whole
coordinate ring `F[C₁] = F[x₁, y₁]` lands in the integral closure `D`. -/
theorem coordRing_mem_integralClosure
    (hX : coordXFun C₁ ∈ integralClosure Af C₁.FunctionField)
    (hY : coordYFun C₁ ∈ integralClosure Af C₁.FunctionField)
    (r : C₁.CoordinateRing) :
    algebraMap C₁.CoordinateRing C₁.FunctionField r ∈ integralClosure Af C₁.FunctionField := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective r
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    exact add_mem hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
    refine mul_mem ?_ (pow_mem hY n)
    -- the coefficient `a : F[X]` itself: induct again
    induction a using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.C_add, map_add, map_add]
      exact add_mem hp hq
    | monomial m c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow,
        map_mul, map_mul, map_pow, map_pow]
      refine mul_mem ?_ (pow_mem hX m)
      have hc : algebraMap C₁.CoordinateRing C₁.FunctionField
          (AdjoinRoot.mk C₁.toAffine.polynomial (Polynomial.C (Polynomial.C c))) =
          algebraMap F C₁.FunctionField c := by
        rw [IsScalarTower.algebraMap_apply F C₁.CoordinateRing C₁.FunctionField]
        rfl
      rw [hc]
      exact scalar_mem_integralClosure C₂ Af c

/-! ### The residue character of a maximal ideal of `D` and its smooth point -/

section Prime

variable (hX : coordXFun C₁ ∈ integralClosure Af C₁.FunctionField)
  (hY : coordYFun C₁ ∈ integralClosure Af C₁.FunctionField)
  (P : Ideal (integralClosure Af C₁.FunctionField))

/-- The coordinate ring of `C₁` mapped into the integral closure `D` (under the
membership hypotheses for the two generators). -/
noncomputable def coordRingToClosure :
    C₁.CoordinateRing →+* integralClosure Af C₁.FunctionField where
  toFun r := ⟨algebraMap C₁.CoordinateRing C₁.FunctionField r,
    coordRing_mem_integralClosure C₂ Af hX hY r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The scalars of `F` mapped into the integral closure `D`. -/
noncomputable def scalarsToClosure : F →+* integralClosure Af C₁.FunctionField where
  toFun c := ⟨algebraMap F C₁.FunctionField c, scalar_mem_integralClosure C₂ Af c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The concrete residue map `F → D ⧸ P`. -/
noncomputable def residueClosure : F →+* (integralClosure Af C₁.FunctionField) ⧸ P :=
  (Ideal.Quotient.mk P).comp (scalarsToClosure C₂ Af)

variable {P} {Q : C₂.SmoothPoint}

include C₂ in
omit finKL in
/-- The scalar `c : F`, pushed through `F → F[C₂] → Af → K(C₁)`, is the scalar `c` of
`K(C₁)`. -/
theorem algebraMap_scalar_eq (c : F) :
    algebraMap Af C₁.FunctionField
        (algebraMap C₂.CoordinateRing Af (algebraMap F C₂.CoordinateRing c)) =
      algebraMap F C₁.FunctionField c := by
  rw [IsScalarTower.algebraMap_apply Af C₂.FunctionField C₁.FunctionField,
    ← IsScalarTower.algebraMap_apply C₂.CoordinateRing Af C₂.FunctionField,
    ← IsScalarTower.algebraMap_apply F C₂.CoordinateRing C₂.FunctionField,
    ← IsScalarTower.algebraMap_apply F C₂.FunctionField C₁.FunctionField]

omit finKL in
/-- The scalar map into the closure is the `Af`-algebra map of the `Af`-scalar. -/
theorem scalarsToClosure_eq_algebraMap (c : F) :
    scalarsToClosure C₂ Af c =
      algebraMap Af (integralClosure Af C₁.FunctionField)
        (algebraMap C₂.CoordinateRing Af (algebraMap F C₂.CoordinateRing c)) := by
  refine Subtype.ext ?_
  have h1 : ((algebraMap Af (integralClosure Af C₁.FunctionField)
      (algebraMap C₂.CoordinateRing Af (algebraMap F C₂.CoordinateRing c)) :
        integralClosure Af C₁.FunctionField) : C₁.FunctionField) =
      algebraMap Af C₁.FunctionField
        (algebraMap C₂.CoordinateRing Af (algebraMap F C₂.CoordinateRing c)) :=
    (IsScalarTower.algebraMap_apply Af (integralClosure Af C₁.FunctionField)
      C₁.FunctionField _).symm
  rw [h1, algebraMap_scalar_eq C₂ Af c]
  rfl

omit finKL in
/-- Pushing `residueAway` through the quotient algebra map lands on `residueClosure`
(for `P` lying over the good maximal ideal). -/
theorem algebraMap_quotient_residueAway (hPq : P.under Af = awayIdealAt Af Q) (c : F) :
    letI : P.LiesOver (awayIdealAt Af Q) := ⟨hPq.symm⟩
    algebraMap (Af ⧸ awayIdealAt Af Q) ((integralClosure Af C₁.FunctionField) ⧸ P)
        (residueAway Af Q c) =
      residueClosure C₂ Af P c := by
  letI : P.LiesOver (awayIdealAt Af Q) := ⟨hPq.symm⟩
  have h1 : residueAway Af Q c = Ideal.Quotient.mk (awayIdealAt Af Q)
      (algebraMap C₂.CoordinateRing Af (algebraMap F C₂.CoordinateRing c)) := rfl
  rw [h1, Ideal.Quotient.algebraMap_mk_of_liesOver]
  change Ideal.Quotient.mk P _ = Ideal.Quotient.mk P (scalarsToClosure C₂ Af c)
  rw [scalarsToClosure_eq_algebraMap C₂ Af c]

set_option synthInstance.maxHeartbeats 400000 in
-- Typeclass search through the quotient of the subalgebra `integralClosure Af K(C₁)` is
-- heartbeat-heavy, exactly as in `HasseWeil/Curves/GoodFiber.lean` (same bumps).
set_option maxHeartbeats 1600000 in
-- The module-finiteness chain through the quotient needs the matching elaboration budget.
/-- **Residue triviality for `D` over `K̄`**: for a prime `P` of `D` lying over the good
maximal ideal `q = awayIdealAt f Q`, the residue map `F → D⧸P` is bijective.  `D⧸P` is a
field, module-finite over `Af⧸q ≅ F` (Krull–Akizuki finiteness of `D` over `Af`), hence
integral over `F`, hence equal to `F` since `F` is algebraically closed. -/
theorem residue_closure_bijective [IsAlgClosed F] [IsIntegrallyClosed C₂.CoordinateRing]
    [Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]
    (hf : f ≠ 0) (hfQ : f ∉ C₂.maximalIdealAt Q)
    (hPp : P.IsPrime) (hPq : P.under Af = awayIdealAt Af Q) :
    Function.Bijective (residueClosure C₂ Af P) := by
  classical
  haveI := hPp
  haveI hPover : P.LiesOver (awayIdealAt Af Q) := ⟨hPq.symm⟩
  haveI hqmax : (awayIdealAt Af Q).IsMaximal := awayIdealAt_isMaximal f Af Q hf hfQ
  haveI hMF : Module.Finite Af (integralClosure Af C₁.FunctionField) :=
    GoodAffineLocus.module_finite_integralClosure C₂ f Af hf
  haveI : Nontrivial ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    Ideal.Quotient.nontrivial_of_liesOver_of_isPrime P (awayIdealAt Af Q)
  -- the `F`-algebra structures via the concrete residue maps
  letI algFq : Algebra F (Af ⧸ awayIdealAt Af Q) := (residueAway Af Q).toAlgebra
  letI algFP : Algebra F ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    (residueClosure C₂ Af P).toAlgebra
  -- module-finiteness chain `F → Af⧸q → D⧸P`
  haveI h1 : Module.Finite Af ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Af P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective Af P)
  haveI h2 : Module.Finite (Af ⧸ awayIdealAt Af Q)
      ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    Module.Finite.of_restrictScalars_finite Af _ _
  haveI h3 : Module.Finite F (Af ⧸ awayIdealAt Af Q) :=
    Module.Finite.of_surjective (Algebra.linearMap F (Af ⧸ awayIdealAt Af Q))
      (residue_away_bijective f Af Q hfQ).2
  haveI tower : IsScalarTower F (Af ⧸ awayIdealAt Af Q)
      ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    IsScalarTower.of_algebraMap_eq fun c ↦
      (algebraMap_quotient_residueAway C₂ Af hPq c).symm
  haveI h4 : Module.Finite F ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    Module.Finite.trans (Af ⧸ awayIdealAt Af Q) _
  haveI : Algebra.IsIntegral F ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    Algebra.IsIntegral.of_finite F _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **`f = 1` at the localized pair**: the inertia degree of a prime of `D` over a good
maximal ideal of `Af` is `1` over an algebraically closed base. -/
theorem inertiaDeg_eq_one_of_under_eq [IsAlgClosed F] [IsIntegrallyClosed C₂.CoordinateRing]
    [Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]
    (hf : f ≠ 0) (hfQ : f ∉ C₂.maximalIdealAt Q)
    (hPp : P.IsPrime) (hPq : P.under Af = awayIdealAt Af Q) :
    Ideal.inertiaDeg (awayIdealAt Af Q) P = 1 := by
  classical
  haveI := hPp
  haveI hPover : P.LiesOver (awayIdealAt Af Q) := ⟨hPq.symm⟩
  haveI hqmax : (awayIdealAt Af Q).IsMaximal := awayIdealAt_isMaximal f Af Q hf hfQ
  haveI : Nontrivial ((integralClosure Af C₁.FunctionField) ⧸ P) :=
    Ideal.Quotient.nontrivial_of_liesOver_of_isPrime P (awayIdealAt Af Q)
  letI : Field (Af ⧸ awayIdealAt Af Q) := Ideal.Quotient.field _
  have hbijP := residue_closure_bijective C₂ f Af hf hfQ hPp hPq
  -- the quotient algebra map is bijective
  have hbij' : Function.Bijective (algebraMap (Af ⧸ awayIdealAt Af Q)
      ((integralClosure Af C₁.FunctionField) ⧸ P)) := by
    constructor
    · exact (algebraMap (Af ⧸ awayIdealAt Af Q)
        ((integralClosure Af C₁.FunctionField) ⧸ P)).injective
    · intro w
      obtain ⟨c, hc⟩ := hbijP.2 w
      exact ⟨residueAway Af Q c,
        (algebraMap_quotient_residueAway C₂ Af hPq c).trans hc⟩
  rw [Ideal.inertiaDeg_algebraMap]
  have he := (AlgEquiv.ofBijective (Algebra.ofId (Af ⧸ awayIdealAt Af Q)
      ((integralClosure Af C₁.FunctionField) ⧸ P)) hbij').toLinearEquiv.finrank_eq
  rw [← he, Module.finrank_self]

omit finKL

/-- The residue character `F[C₁] → F` of a maximal ideal `P` of `D` with trivial residue
field: evaluation of coordinate-ring elements through `D ⧸ P ≅ F`. -/
noncomputable def residueChar (hbij : Function.Bijective (residueClosure C₂ Af P)) :
    C₁.CoordinateRing →+* F :=
  ((RingEquiv.ofBijective (residueClosure C₂ Af P) hbij).symm : _ →+* F).comp
    ((Ideal.Quotient.mk P).comp (coordRingToClosure C₂ Af hX hY))

/-- The residue value `D → F` of a maximal ideal `P` of `D` with trivial residue field. -/
noncomputable def residueValue (hbij : Function.Bijective (residueClosure C₂ Af P)) :
    integralClosure Af C₁.FunctionField → F :=
  fun d ↦ (RingEquiv.ofBijective (residueClosure C₂ Af P) hbij).symm (Ideal.Quotient.mk P d)

theorem residueClosure_residueValue (hbij : Function.Bijective (residueClosure C₂ Af P))
    (d : integralClosure Af C₁.FunctionField) :
    residueClosure C₂ Af P (residueValue C₂ Af hbij d) = Ideal.Quotient.mk P d :=
  (RingEquiv.ofBijective (residueClosure C₂ Af P) hbij).apply_symm_apply
    (Ideal.Quotient.mk P d)

set_option synthInstance.maxHeartbeats 400000 in
-- `map_sub` instance search through the subalgebra quotient exceeds the default
-- typeclass budget (same situation as `HasseWeil/Curves/GoodFiber.lean`).
/-- `d − residueValue d` lies in `P`. -/
theorem sub_residueValue_mem (hbij : Function.Bijective (residueClosure C₂ Af P))
    (d : integralClosure Af C₁.FunctionField) :
    d - scalarsToClosure C₂ Af (residueValue C₂ Af hbij d) ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
  have h : Ideal.Quotient.mk P (scalarsToClosure C₂ Af (residueValue C₂ Af hbij d)) =
      Ideal.Quotient.mk P d := residueClosure_residueValue C₂ Af hbij d
  rw [h, sub_self]

/-- The coordinate-ring map into the closure sends scalars to scalars. -/
theorem coordRingToClosure_algebraMap (c : F) :
    coordRingToClosure C₂ Af hX hY (algebraMap F C₁.CoordinateRing c) =
      scalarsToClosure C₂ Af c := by
  refine Subtype.ext ?_
  change algebraMap C₁.CoordinateRing C₁.FunctionField (algebraMap F C₁.CoordinateRing c) =
    algebraMap F C₁.FunctionField c
  rw [← IsScalarTower.algebraMap_apply F C₁.CoordinateRing C₁.FunctionField]

/-- The residue character fixes scalars. -/
theorem residueChar_algebraMap
    (hbij : Function.Bijective (residueClosure C₂ Af P)) (c : F) :
    residueChar C₂ Af hX hY hbij (algebraMap F C₁.CoordinateRing c) = c := by
  change (RingEquiv.ofBijective (residueClosure C₂ Af P) hbij).symm
    (Ideal.Quotient.mk P
      (coordRingToClosure C₂ Af hX hY (algebraMap F C₁.CoordinateRing c))) = c
  rw [coordRingToClosure_algebraMap C₂ Af hX hY c]
  exact (RingEquiv.ofBijective (residueClosure C₂ Af P) hbij).symm_apply_apply c

variable [C₁.toAffine.IsElliptic]

omit [C₁.toAffine.IsElliptic] in
/-- The kernel of the residue character is maximal (the character is surjective onto the
field `F`). -/
theorem ker_residueChar_isMaximal (hbij : Function.Bijective (residueClosure C₂ Af P)) :
    (RingHom.ker (residueChar C₂ Af hX hY hbij)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦
    ⟨algebraMap F C₁.CoordinateRing c, residueChar_algebraMap C₂ Af hX hY hbij c⟩

/-- **The smooth point of a maximal ideal of `D`** (over `K̄`): the point of `C₁` whose
maximal ideal is the kernel of the residue character of `P`. -/
noncomputable def pointAt [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P)) :
    C₁.SmoothPoint :=
  (C₁.exists_smoothPoint_of_isMaximal
    (ker_residueChar_isMaximal C₂ Af hX hY hbij)).choose

theorem maximalIdealAt_pointAt [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P)) :
    C₁.maximalIdealAt (pointAt C₂ Af hX hY hbij) =
      RingHom.ker (residueChar C₂ Af hX hY hbij) :=
  (C₁.exists_smoothPoint_of_isMaximal
    (ker_residueChar_isMaximal C₂ Af hX hY hbij)).choose_spec

/-- The residue character is evaluation at `pointAt P`. -/
theorem residueChar_eq_evalAt [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P)) (r : C₁.CoordinateRing) :
    residueChar C₂ Af hX hY hbij r = C₁.evalAt (pointAt C₂ Af hX hY hbij) r := by
  have hker : r - algebraMap F C₁.CoordinateRing
      (C₁.evalAt (pointAt C₂ Af hX hY hbij) r) ∈
      RingHom.ker (residueChar C₂ Af hX hY hbij) := by
    rw [← maximalIdealAt_pointAt C₂ Af hX hY hbij, ← C₁.ker_evalAt, RingHom.mem_ker,
      map_sub, C₁.evalAt_algebraMap, sub_self]
  rw [RingHom.mem_ker, map_sub, residueChar_algebraMap C₂ Af hX hY hbij, sub_eq_zero]
    at hker
  exact hker

/-! ### The place of `P` is the place of `pointAt P` -/

variable (P) in
/-- The subring of `K(C₁)` of fractions `d/s` with `d, s ∈ D`, `s ∉ P`. -/
noncomputable def fractionsAway (hPp : P.IsPrime) : Subring C₁.FunctionField where
  carrier := {z | ∃ d s : integralClosure Af C₁.FunctionField, s ∉ P ∧
    z * (s : C₁.FunctionField) = (d : C₁.FunctionField)}
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one P).mp hPp.ne_top, by simp⟩
  mul_mem' := by
    rintro z₁ z₂ ⟨d₁, s₁, hs₁, h₁⟩ ⟨d₂, s₂, hs₂, h₂⟩
    refine ⟨d₁ * d₂, s₁ * s₂, fun hmem ↦ ?_, ?_⟩
    · rcases hPp.mem_or_mem hmem with h | h
      exacts [hs₁ h, hs₂ h]
    · simp only [MulMemClass.coe_mul]
      calc z₁ * z₂ * ((s₁ : C₁.FunctionField) * (s₂ : C₁.FunctionField))
          = z₁ * (s₁ : C₁.FunctionField) * (z₂ * (s₂ : C₁.FunctionField)) := by ring
        _ = (d₁ : C₁.FunctionField) * (d₂ : C₁.FunctionField) := by rw [h₁, h₂]
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one P).mp hPp.ne_top, by simp⟩
  add_mem' := by
    rintro z₁ z₂ ⟨d₁, s₁, hs₁, h₁⟩ ⟨d₂, s₂, hs₂, h₂⟩
    refine ⟨d₁ * s₂ + d₂ * s₁, s₁ * s₂, fun hmem ↦ ?_, ?_⟩
    · rcases hPp.mem_or_mem hmem with h | h
      exacts [hs₁ h, hs₂ h]
    · push_cast
      linear_combination (s₂ : C₁.FunctionField) * h₁ + (s₁ : C₁.FunctionField) * h₂
  neg_mem' := by
    rintro z ⟨d, s, hs, h⟩
    refine ⟨-d, s, hs, ?_⟩
    push_cast
    rw [neg_mul, h]

omit [C₁.toAffine.IsElliptic] in
/-- The inverse of a nonzero element of `P` is not a fraction away from `P`. -/
theorem inv_notMem_fractionsAway (hPp : P.IsPrime)
    {u : integralClosure Af C₁.FunctionField} (huP : u ∈ P) (hu0 : u ≠ 0) :
    ((u : C₁.FunctionField))⁻¹ ∉ fractionsAway Af P hPp := by
  rintro ⟨d', s', hs', heq⟩
  have hu0' : (u : C₁.FunctionField) ≠ 0 := by simpa using hu0
  have hs : s' = u * d' := by
    apply Subtype.coe_injective
    push_cast
    field_simp at heq
    linear_combination heq
  apply hs'
  rw [hs]
  exact Ideal.mul_mem_right d' P huP

/-- **Contraction step** of the place identification: a coordinate-ring element of `C₁`
whose image in `D` lies in `P` lies in the maximal ideal `m_{pointAt P}`.  Indeed
`m_{pointAt P}` is the kernel of the residue character, and the residue character factors
the residue map of `P` through the residue field isomorphism, so vanishing in `D ⧸ P`
gives vanishing of the residue. -/
private theorem coordRingToClosure_mem_maximalIdealAt [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P))
    {r : C₁.CoordinateRing} (hr : coordRingToClosure C₂ Af hX hY r ∈ P) :
    r ∈ C₁.maximalIdealAt (pointAt C₂ Af hX hY hbij) := by
  rw [maximalIdealAt_pointAt C₂ Af hX hY hbij, RingHom.mem_ker]
  change (RingEquiv.ofBijective (residueClosure C₂ Af P) hbij).symm
    (Ideal.Quotient.mk P (coordRingToClosure C₂ Af hX hY r)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- **Valuation-ring containment** for the place identification: the valuation ring of
`pointAt P` (the elements of value `≤ 1`) is contained in the fraction subring
`fractionsAway P` (fractions `d/s` with `d, s ∈ D`, `s ∉ P`).  An element of value `≤ 1`
is the image of a localized fraction `r/s` with `s ∉ m_{pointAt P}`; pushing `r, s` into
`D`, the contraction step keeps the denominator out of `P`. -/
private theorem mem_fractionsAway_of_pointValuation_le_one [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P)) (hPp : P.IsPrime)
    {x : C₁.FunctionField}
    (hx : C₁.pointValuation (pointAt C₂ Af hX hY hbij) x ≤ 1) :
    x ∈ fractionsAway Af P hPp := by
  obtain ⟨w, hw⟩ :=
    SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one x hx
  obtain ⟨⟨r, s⟩, hmk⟩ :=
    IsLocalization.surj (C₁.maximalIdealAt (pointAt C₂ Af hX hY hbij)).primeCompl w
  have hxs : x * algebraMap C₁.CoordinateRing C₁.FunctionField (s : C₁.CoordinateRing) =
      algebraMap C₁.CoordinateRing C₁.FunctionField r := by
    have hmap := congrArg
      (algebraMap (C₁.localRingAt (pointAt C₂ Af hX hY hbij)) C₁.FunctionField) hmk
    rw [map_mul, hw, ← IsScalarTower.algebraMap_apply C₁.CoordinateRing
        (C₁.localRingAt (pointAt C₂ Af hX hY hbij)) C₁.FunctionField,
      ← IsScalarTower.algebraMap_apply C₁.CoordinateRing
        (C₁.localRingAt (pointAt C₂ Af hX hY hbij)) C₁.FunctionField] at hmap
    exact hmap
  refine ⟨coordRingToClosure C₂ Af hX hY r, coordRingToClosure C₂ Af hX hY
    (s : C₁.CoordinateRing), fun hsP ↦ s.2 (coordRingToClosure_mem_maximalIdealAt
      C₂ Af hX hY hbij hsP), hxs⟩

/-- **Strictness step** of the place identification: once the valuation ring of `pointAt P`
is contained in `fractionsAway P` (`hO`), every element of `P` has point valuation `< 1`.
The containment plus properness of `fractionsAway P` (`1/u ∉` for `0 ≠ u ∈ P`) forces
`≤ 1` on all of `fractionsAway P` by DVR maximality; an element of `P` lying there has
`≤ 1`, and value `1` would put its inverse in `fractionsAway P`, contradicting membership
in `P`. -/
private theorem pointValuation_lt_one_of_subset_fractionsAway [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P)) (hPp : P.IsPrime) (hP0 : P ≠ ⊥)
    (hO : ∀ x : C₁.FunctionField,
      C₁.pointValuation (pointAt C₂ Af hX hY hbij) x ≤ 1 → x ∈ fractionsAway Af P hPp)
    {d : integralClosure Af C₁.FunctionField} (hd : d ∈ P) :
    C₁.pointValuation (pointAt C₂ Af hX hY hbij) (d : C₁.FunctionField) < 1 := by
  -- `fractionsAway P` is a proper subring: `1/u ∉` for `0 ≠ u ∈ P`
  have hRne : fractionsAway Af P hPp ≠ ⊤ := by
    intro htop
    obtain ⟨u, huP, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    exact inv_notMem_fractionsAway Af hPp huP hu0 (htop ▸ Subring.mem_top _)
  -- `≤ 1` on all of `fractionsAway P` by the intermediate-ring lemma
  have hle : ∀ z ∈ fractionsAway Af P hPp,
      C₁.pointValuation (pointAt C₂ Af hX hY hbij) z ≤ 1 :=
    le_one_of_forall_le_one_mem_of_ne_top _ hO hRne
  have hdmem : (d : C₁.FunctionField) ∈ fractionsAway Af P hPp :=
    ⟨d, 1, (Ideal.ne_top_iff_one P).mp hPp.ne_top, by simp⟩
  rcases lt_or_eq_of_le (hle _ hdmem) with h | h
  · exact h
  -- strictness: `v(d) = 1` would put `d⁻¹` in `fractionsAway P`, contradicting `d ∈ P`
  · exfalso
    have hd0 : (d : C₁.FunctionField) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    have hinv : C₁.pointValuation (pointAt C₂ Af hX hY hbij)
        ((d : C₁.FunctionField))⁻¹ ≤ 1 := by
      rw [map_inv₀, h, inv_one]
    have hd0' : d ≠ 0 := fun h0 ↦ hd0 (by rw [h0]; rfl)
    exact inv_notMem_fractionsAway Af hPp hd hd0' (hO _ hinv)

/-- **The place identification** (the W-3b crux): for a maximal ideal `P` of `D` with
trivial residue field, the point valuation at `pointAt P` is `< 1` on every element
of `P`.  The local ring of `D` at `P` contains the (DVR) local ring of `C₁` at
`pointAt P` — membership of `P ∩ F[C₁]` in `m_{pointAt P}` is residue-character
vanishing — and is proper (`1/u ∉` for `0 ≠ u ∈ P`), so by DVR maximality the two
local rings have the same valuation. -/
theorem pointValuation_lt_one_of_mem_prime [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P))
    (hPp : P.IsPrime) (hP0 : P ≠ ⊥)
    {d : integralClosure Af C₁.FunctionField} (hd : d ∈ P) :
    C₁.pointValuation (pointAt C₂ Af hX hY hbij) (d : C₁.FunctionField) < 1 :=
  pointValuation_lt_one_of_subset_fractionsAway C₂ Af hX hY hbij hPp hP0
    (fun _ hx ↦ mem_fractionsAway_of_pointValuation_le_one C₂ Af hX hY hbij hPp hx) hd

/-- **Evaluation form of the place identification**: every `d ∈ D` evaluates at
`pointAt P` to its residue value: `v_{pointAt P}(d − residueValue d) < 1`. -/
theorem pointValuation_sub_residueValue_lt_one [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P))
    (hPp : P.IsPrime) (hP0 : P ≠ ⊥)
    (d : integralClosure Af C₁.FunctionField) :
    C₁.pointValuation (pointAt C₂ Af hX hY hbij)
      ((d : C₁.FunctionField) -
        algebraMap F C₁.FunctionField (residueValue C₂ Af hbij d)) < 1 := by
  have h := pointValuation_lt_one_of_mem_prime C₂ Af hX hY hbij hPp hP0
    (sub_residueValue_mem C₂ Af hbij d)
  have hcoe : ((d - scalarsToClosure C₂ Af (residueValue C₂ Af hbij d) :
      integralClosure Af C₁.FunctionField) : C₁.FunctionField) =
      (d : C₁.FunctionField) -
        algebraMap F C₁.FunctionField (residueValue C₂ Af hbij d) := by
    push_cast
    rfl
  rwa [hcoe] at h

omit [C₁.toAffine.IsElliptic] in
/-- The closure element of a pulled-back coordinate function is the `Af`-algebra image. -/
theorem closureElt_eq_algebraMap (a : Af) :
    (⟨algebraMap Af C₁.FunctionField a,
        (integralClosure Af C₁.FunctionField).algebraMap_mem _⟩ :
          integralClosure Af C₁.FunctionField) =
      algebraMap Af (integralClosure Af C₁.FunctionField) a :=
  Subtype.ext (IsScalarTower.algebraMap_apply Af
    (integralClosure Af C₁.FunctionField) C₁.FunctionField a)

omit [C₁.toAffine.IsElliptic] in
/-- **The residue value of a pulled-back coordinate function of `C₂` is its value at
`Q`**: for `P` over `q = awayIdealAt f Q` and `g ∈ F[C₂]`, the residue of the image of
`g` in `D` is `evalAt Q g`.  (Both `g ↦ residueValue (g-image)` and `evalAt Q` are ring
maps `F[C₂] → F` with kernel containing the maximal ideal `m_Q`, fixing scalars.) -/
theorem residueValue_algebraMap [IsAlgClosed F]
    (hbij : Function.Bijective (residueClosure C₂ Af P))
    (hPq : P.under Af = awayIdealAt Af Q) (g : C₂.CoordinateRing) :
    residueValue C₂ Af hbij
      (⟨algebraMap Af C₁.FunctionField (algebraMap C₂.CoordinateRing Af g),
        (integralClosure Af C₁.FunctionField).algebraMap_mem _⟩ :
          integralClosure Af C₁.FunctionField) = C₂.evalAt Q g := by
  apply hbij.1
  rw [residueClosure_residueValue]
  have h1 : residueClosure C₂ Af P (C₂.evalAt Q g) =
      Ideal.Quotient.mk P (scalarsToClosure C₂ Af (C₂.evalAt Q g)) := rfl
  rw [h1, closureElt_eq_algebraMap, scalarsToClosure_eq_algebraMap C₂ Af,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub, ← map_sub]
  -- the difference vanishes at `Q`, lands in `q`, hence in `P`
  have hgm : g - algebraMap F C₂.CoordinateRing (C₂.evalAt Q g) ∈ C₂.maximalIdealAt Q := by
    rw [← C₂.ker_evalAt, RingHom.mem_ker, map_sub, C₂.evalAt_algebraMap, sub_self]
  have hq : algebraMap C₂.CoordinateRing Af
      (g - algebraMap F C₂.CoordinateRing (C₂.evalAt Q g)) ∈ awayIdealAt Af Q :=
    Ideal.mem_map_of_mem _ hgm
  rw [← hPq] at hq
  exact hq

/-- **Distinct maximal ideals of `D` give distinct points**: if `P₁ ≠ P₂` are maximal
with trivial residue fields and `pointAt P₁ = pointAt P₂`, comaximality gives
`u₁ + u₂ = 1` with `uᵢ ∈ Pᵢ`, and the place identification makes both summands have
valuation `< 1` at the common point — contradicting `v(1) = 1`. -/
theorem pointAt_injective [IsAlgClosed F]
    {P₁ P₂ : Ideal (integralClosure Af C₁.FunctionField)}
    (hbij₁ : Function.Bijective (residueClosure C₂ Af P₁))
    (hbij₂ : Function.Bijective (residueClosure C₂ Af P₂))
    (hP₁ : P₁.IsMaximal) (hP₂ : P₂.IsMaximal) (hP₁0 : P₁ ≠ ⊥) (hP₂0 : P₂ ≠ ⊥)
    (hne : P₁ ≠ P₂) :
    pointAt C₂ Af hX hY hbij₁ ≠ pointAt C₂ Af hX hY hbij₂ := by
  intro hpteq
  obtain ⟨u₁, hu₁, u₂, hu₂, hsum⟩ :=
    Ideal.isCoprime_iff_exists.mp
      (Ideal.isCoprime_iff_sup_eq.mpr (hP₁.coprime_of_ne hP₂ hne))
  have hv₁ := pointValuation_lt_one_of_mem_prime C₂ Af hX hY hbij₁ hP₁.isPrime hP₁0 hu₁
  have hv₂ := pointValuation_lt_one_of_mem_prime C₂ Af hX hY hbij₂ hP₂.isPrime hP₂0 hu₂
  rw [← hpteq] at hv₂
  have hlt : C₁.pointValuation (pointAt C₂ Af hX hY hbij₁)
      ((u₁ : C₁.FunctionField) + (u₂ : C₁.FunctionField)) < 1 :=
    lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hv₁ hv₂)
  have hone : (u₁ : C₁.FunctionField) + (u₂ : C₁.FunctionField) = 1 := by
    have := congrArg (fun t : integralClosure Af C₁.FunctionField ↦
      (t : C₁.FunctionField)) hsum
    push_cast at this
    simpa using this
  rw [hone, map_one] at hlt
  exact lt_irrefl 1 hlt

end Prime

/-! ### The headline: the good fibre via the localized dictionary -/

section Headline

variable [ellC₁ : C₁.toAffine.IsElliptic] [ellC₂ : C₂.toAffine.IsElliptic]
variable [sepKL : Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]

/-- **The good target point** (avoidance + genericity step of the headline).  Given the
finite ramification locus `Sram` of `(Af, D)`, off any prescribed finite set `avoid` there
is a smooth point `Q` of `C₂` that also avoids the zeros of `f` and the pullback of `Sram`.
The argument is that all three loci are finite — `avoid` by hypothesis, the zeros of `f` by
unique factorization of `F[C₂]`, and the `Sram`-pullback by injectivity of `awayIdealAt` on
that locus — so their union has nonempty complement in the infinitely many smooth points. -/
private theorem exists_good_target_point [IsAlgClosed F]
    [IsIntegrallyClosed C₂.CoordinateRing] (hf : f ≠ 0)
    {avoid : Set C₂.SmoothPoint} (havoid : avoid.Finite)
    (Sram : Set (Ideal Af)) (hSfin : Sram.Finite) :
    ∃ Q : C₂.SmoothPoint, Q ∉ avoid ∧ f ∉ C₂.maximalIdealAt Q ∧
      awayIdealAt Af Q ∉ Sram := by
  classical
  have hfin1 : {Q' : C₂.SmoothPoint | f ∈ C₂.maximalIdealAt Q'}.Finite := by
    haveI : Fintype {I : Ideal C₂.CoordinateRing // I ∣ Ideal.span {f}} :=
      UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by simpa using hf)
    rw [← Set.finite_coe_iff]
    refine Finite.of_injective (fun Q' ↦
      (⟨C₂.maximalIdealAt Q'.1, Ideal.dvd_span_singleton.mpr Q'.2⟩ :
        {I : Ideal C₂.CoordinateRing // I ∣ Ideal.span {f}})) ?_
    intro Q₁ Q₂ h
    exact Subtype.ext (C₂.maximalIdealAt_injective (congrArg Subtype.val h))
  have hfin2 : {Q' : C₂.SmoothPoint |
      f ∉ C₂.maximalIdealAt Q' ∧ awayIdealAt Af Q' ∈ Sram}.Finite := by
    refine Set.Finite.of_finite_image (f := fun Q' ↦ awayIdealAt Af Q')
      (hSfin.subset ?_) ?_
    · rintro _ ⟨Q', ⟨_, hmem⟩, rfl⟩
      exact hmem
    · rintro Q₁ ⟨hf₁, _⟩ Q₂ ⟨hf₂, _⟩ heq
      apply C₂.maximalIdealAt_injective
      rw [← awayIdealAt_under f Af Q₁ hf₁, ← awayIdealAt_under f Af Q₂ hf₂]
      exact congrArg (Ideal.under C₂.CoordinateRing) heq
  have hbig : (avoid ∪ {Q' : C₂.SmoothPoint | f ∈ C₂.maximalIdealAt Q'} ∪
      {Q' : C₂.SmoothPoint | f ∉ C₂.maximalIdealAt Q' ∧ awayIdealAt Af Q' ∈ Sram}).Finite :=
    (havoid.union hfin1).union hfin2
  haveI : Infinite C₂.SmoothPoint := C₂.smoothPoint_infinite
  obtain ⟨Q, hQ⟩ := hbig.infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, Set.mem_union, not_or, not_or] at hQ
  obtain ⟨⟨hQavoid, hQf⟩, hQram⟩ := hQ
  exact ⟨Q, hQavoid, hQf, fun hmem ↦ hQram ⟨hQf, hmem⟩⟩

/-- **The fibre count** (`Σ e·f = [K(C₁):K(C₂)]` step of the headline).  For a good target
point `Q` — off the zeros of `f` (`hfQ`) and off the ramification locus `Sram` (`hQS`) — the
number of primes of `D = integralClosure Af K(C₁)` over `q = awayIdealAt Af Q` equals
`[K(C₁):K(C₂)]`.  This is mathlib's `Ideal.sum_ramification_inertia`, with ramification
index `1` off `Sram` (`hSram`) and inertia degree `1` over an algebraically closed base
(`inertiaDeg_eq_one_of_under_eq`), so the sum degenerates to the cardinality. -/
private theorem card_primesOver_eq_finrank [IsAlgClosed F]
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsDedekindDomain (integralClosure Af C₁.FunctionField)]
    (hf : f ≠ 0) {Q : C₂.SmoothPoint}
    (hfQ : f ∉ C₂.maximalIdealAt Q)
    (Sram : Set (Ideal Af))
    (hSram : ∀ q : Ideal Af, q ∉ Sram →
      ∀ P : Ideal (integralClosure Af C₁.FunctionField), P.IsPrime → P.under Af = q →
        Ideal.ramificationIdx q P = 1)
    (hQS : awayIdealAt Af Q ∉ Sram) :
    (IsDedekindDomain.primesOverFinset (awayIdealAt Af Q)
        (integralClosure Af C₁.FunctionField)).card =
      Module.finrank C₂.FunctionField C₁.FunctionField := by
  classical
  haveI := GoodAffineLocus.isDedekindDomain_away C₂ f Af hf
  haveI := GoodAffineLocus.isFractionRing_away C₂ f Af
  haveI hDFR : IsFractionRing (integralClosure Af C₁.FunctionField) C₁.FunctionField :=
    GoodAffineLocus.isFractionRing_integralClosure C₂ f Af hf
  haveI hDMF : Module.Finite Af (integralClosure Af C₁.FunctionField) :=
    GoodAffineLocus.module_finite_integralClosure C₂ f Af hf
  haveI hqmax : (awayIdealAt Af Q).IsMaximal := awayIdealAt_isMaximal f Af Q hf hfQ
  have hq0 : awayIdealAt Af Q ≠ ⊥ := awayIdealAt_ne_bot f Af Q hf
  haveI htf : Module.IsTorsionFree Af (integralClosure Af C₁.FunctionField) :=
    Curves.RamificationFinite.isTorsionFree Af C₂.FunctionField C₁.FunctionField _
  have hPdata : ∀ P ∈ IsDedekindDomain.primesOverFinset (awayIdealAt Af Q)
      (integralClosure Af C₁.FunctionField), P.IsPrime ∧ P.under Af = awayIdealAt Af Q := by
    intro P hP
    have hmem : P ∈ (awayIdealAt Af Q).primesOver (integralClosure Af C₁.FunctionField) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hq0 _).mp hP
    exact ⟨hmem.1, hmem.2.over.symm⟩
  have hsum := Ideal.sum_ramification_inertia
    (S := integralClosure Af C₁.FunctionField) C₂.FunctionField C₁.FunctionField hq0
  have hsum' : ∑ _P ∈ IsDedekindDomain.primesOverFinset (awayIdealAt Af Q)
      (integralClosure Af C₁.FunctionField), (1 : ℕ) =
      Module.finrank C₂.FunctionField C₁.FunctionField := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [hSram _ hQS P (hPdata P hP).1 (hPdata P hP).2,
      inertiaDeg_eq_one_of_under_eq C₂ f Af hf hfQ (hPdata P hP).1 (hPdata P hP).2]
  rwa [Finset.sum_const, Nat.smul_one_eq_cast, Nat.cast_id] at hsum'

omit finKL ellC₂ sepKL in
/-- **Coordinate evaluation at a produced point** (the local-place step of the headline).
For a prime `P` of `D` over `q = awayIdealAt Af Q` with trivial residue field, the
pulled-back image of any coordinate-ring element `g : F[C₂]` evaluates at the smooth point
`pointAt P` to its value `evalAt Q g`: the point valuation of the difference is `< 1`.  This
is the evaluation form of the place identification (`pointValuation_sub_residueValue_lt_one`)
together with the residue value of a pulled-back coordinate function being `evalAt Q g`
(`residueValue_algebraMap`); it discharges both the `x`- and `y`-generator obligations. -/
private theorem pointValuation_coordGen_sub_evalAt_lt_one [IsAlgClosed F]
    (hX : coordXFun C₁ ∈ integralClosure Af C₁.FunctionField)
    (hY : coordYFun C₁ ∈ integralClosure Af C₁.FunctionField)
    {P : Ideal (integralClosure Af C₁.FunctionField)} {Q : C₂.SmoothPoint}
    (hbij : Function.Bijective (residueClosure C₂ Af P))
    (hPp : P.IsPrime) (hP0 : P ≠ ⊥) (hPq : P.under Af = awayIdealAt Af Q)
    (g : C₂.CoordinateRing) :
    C₁.pointValuation (pointAt C₂ Af hX hY hbij)
        (algebraMap C₂.FunctionField C₁.FunctionField
            (algebraMap C₂.CoordinateRing C₂.FunctionField g) -
          algebraMap F C₁.FunctionField (C₂.evalAt Q g)) < 1 := by
  have h := pointValuation_sub_residueValue_lt_one C₂ Af hX hY hbij hPp hP0
    (⟨algebraMap Af C₁.FunctionField (algebraMap C₂.CoordinateRing Af g),
      (integralClosure Af C₁.FunctionField).algebraMap_mem _⟩)
  rw [residueValue_algebraMap C₂ Af hbij hPq] at h
  have hcoe : algebraMap Af C₁.FunctionField (algebraMap C₂.CoordinateRing Af g) =
      algebraMap C₂.FunctionField C₁.FunctionField
        (algebraMap C₂.CoordinateRing C₂.FunctionField g) := by
    rw [IsScalarTower.algebraMap_apply Af C₂.FunctionField C₁.FunctionField,
      ← IsScalarTower.algebraMap_apply C₂.CoordinateRing Af C₂.FunctionField]
  rwa [show ((⟨algebraMap Af C₁.FunctionField (algebraMap C₂.CoordinateRing Af g),
      (integralClosure Af C₁.FunctionField).algebraMap_mem _⟩ :
        integralClosure Af C₁.FunctionField) : C₁.FunctionField) =
      algebraMap Af C₁.FunctionField (algebraMap C₂.CoordinateRing Af g) from rfl,
    hcoe] at h

include Af in
/-- **The localized good fibre (W-3b headline)**.  Assume the denominator `f` swallows
the minimal-polynomial coefficients of the coordinate functions of `C₁` over `K(C₂)`
(`hdenX`, `hdenY`).  Then off any prescribed finite set of smooth points of `C₂` there
is a point `Q` together with `[K(C₁) : K(C₂)]` *distinct* smooth points of `C₁` at which
the pulled-back coordinate generators of `C₂` evaluate to the coordinates of `Q`.

The localization `Af` (any realization of `F[C₂][1/f]` mapping compatibly to the two
function fields) is auxiliary data for the proof; the statement does not mention it. -/
theorem exists_good_fiber_points [IsAlgClosed F] [IsIntegrallyClosed C₂.CoordinateRing]
    (hf : f ≠ 0)
    (hdenX : ∀ i, ∃ a : C₂.CoordinateRing,
      (minpoly C₂.FunctionField (coordXFun C₁)).coeff i *
          algebraMap C₂.CoordinateRing C₂.FunctionField f
        = algebraMap C₂.CoordinateRing C₂.FunctionField a)
    (hdenY : ∀ i, ∃ a : C₂.CoordinateRing,
      (minpoly C₂.FunctionField (coordYFun C₁)).coeff i *
          algebraMap C₂.CoordinateRing C₂.FunctionField f
        = algebraMap C₂.CoordinateRing C₂.FunctionField a)
    {avoid : Set C₂.SmoothPoint} (havoid : avoid.Finite) :
    ∃ Q : C₂.SmoothPoint, Q ∉ avoid ∧ ∃ S : Finset C₁.SmoothPoint,
      S.card = Module.finrank C₂.FunctionField C₁.FunctionField ∧
      ∀ pt ∈ S,
        C₁.pointValuation pt
          (algebraMap C₂.FunctionField C₁.FunctionField
              (algebraMap C₂.CoordinateRing C₂.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
                  (Polynomial.C Polynomial.X))) -
            algebraMap F C₁.FunctionField Q.x) < 1 ∧
        C₁.pointValuation pt
          (algebraMap C₂.FunctionField C₁.FunctionField
              (algebraMap C₂.CoordinateRing C₂.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine Polynomial.X)) -
            algebraMap F C₁.FunctionField Q.y) < 1 := by
  classical
  have hX : coordXFun C₁ ∈ integralClosure Af C₁.FunctionField :=
    show IsIntegral Af (coordXFun C₁) from
      isIntegral_of_denominator (C₁ := C₁) C₂ f Af hf (coordXFun C₁) hdenX
  have hY : coordYFun C₁ ∈ integralClosure Af C₁.FunctionField :=
    show IsIntegral Af (coordYFun C₁) from
      isIntegral_of_denominator (C₁ := C₁) C₂ f Af hf (coordYFun C₁) hdenY
  -- the W-2 finite ramification bound at `(Af, D)`
  obtain ⟨Sram, hSfin, hSram⟩ :=
    GoodAffineLocus.exists_finite_ramification_locus (C₁ := C₁) C₂ f Af hf
  -- a target point avoiding `avoid`, the zeros of `f`, and the ramified locus
  obtain ⟨Q, hQavoid, hfQ, hQS⟩ :=
    exists_good_target_point C₂ f Af hf havoid Sram hSfin
  -- instances to form the prime finset over `q` and read off prime data
  haveI := GoodAffineLocus.isDedekindDomain_away C₂ f Af hf
  haveI := GoodAffineLocus.isFractionRing_away C₂ f Af
  haveI hDDed : IsDedekindDomain (integralClosure Af C₁.FunctionField) :=
    GoodAffineLocus.isDedekindDomain_integralClosure C₂ f Af hf
  haveI hDFR : IsFractionRing (integralClosure Af C₁.FunctionField) C₁.FunctionField :=
    GoodAffineLocus.isFractionRing_integralClosure C₂ f Af hf
  haveI hDMF : Module.Finite Af (integralClosure Af C₁.FunctionField) :=
    GoodAffineLocus.module_finite_integralClosure C₂ f Af hf
  haveI hqmax : (awayIdealAt Af Q).IsMaximal := awayIdealAt_isMaximal f Af Q hf hfQ
  have hq0 : awayIdealAt Af Q ≠ ⊥ := awayIdealAt_ne_bot f Af Q hf
  haveI htf : Module.IsTorsionFree Af (integralClosure Af C₁.FunctionField) :=
    Curves.RamificationFinite.isTorsionFree Af C₂.FunctionField C₁.FunctionField _
  -- the count `#{P over q} = [K(C₁):K(C₂)]`
  have hcard := card_primesOver_eq_finrank C₂ f Af hf hfQ Sram hSram hQS
  have hPdata : ∀ P ∈ IsDedekindDomain.primesOverFinset (awayIdealAt Af Q)
      (integralClosure Af C₁.FunctionField), P.IsPrime ∧ P.under Af = awayIdealAt Af Q := by
    intro P hP
    have hmem : P ∈ (awayIdealAt Af Q).primesOver (integralClosure Af C₁.FunctionField) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hq0 _).mp hP
    exact ⟨hmem.1, hmem.2.over.symm⟩
  have hPbot : ∀ P ∈ IsDedekindDomain.primesOverFinset (awayIdealAt Af Q)
      (integralClosure Af C₁.FunctionField), P ≠ ⊥ := by
    intro P hP hbot
    exact hq0 (by rw [← (hPdata P hP).2, hbot, Ideal.under_bot])
  -- the point set: images of the primes over `q`
  refine ⟨Q, hQavoid, (IsDedekindDomain.primesOverFinset (awayIdealAt Af Q)
      (integralClosure Af C₁.FunctionField)).attach.image fun P ↦
        pointAt C₂ Af hX hY
          (residue_closure_bijective C₂ f Af hf hfQ (hPdata P.1 P.2).1 (hPdata P.1 P.2).2),
    ?_, ?_⟩
  · -- cardinality: the assignment is injective
    rw [Finset.card_image_of_injOn, Finset.card_attach]
    · exact hcard
    intro P₁ h₁ P₂ h₂ heq
    by_contra hne
    have hne' : P₁.1 ≠ P₂.1 := fun h ↦ hne (Subtype.ext h)
    have hd₁ := hPdata P₁.1 P₁.2
    have hd₂ := hPdata P₂.1 P₂.2
    have h₁0 : P₁.1 ≠ ⊥ := hPbot P₁.1 P₁.2
    have h₂0 : P₂.1 ≠ ⊥ := hPbot P₂.1 P₂.2
    exact pointAt_injective C₂ Af hX hY
      (residue_closure_bijective C₂ f Af hf hfQ hd₁.1 hd₁.2)
      (residue_closure_bijective C₂ f Af hf hfQ hd₂.1 hd₂.2)
      (hd₁.1.isMaximal h₁0) (hd₂.1.isMaximal h₂0) h₁0 h₂0 hne' heq
  · -- the evaluation facts at each produced point, via the coordinate-evaluation helper
    intro pt hpt
    rw [Finset.mem_image] at hpt
    obtain ⟨⟨P, hP⟩, -, rfl⟩ := hpt
    have hd := hPdata P hP
    have hP0 : P ≠ ⊥ := hPbot P hP
    refine ⟨?_, ?_⟩
    · have h := pointValuation_coordGen_sub_evalAt_lt_one C₂ Af hX hY
        (residue_closure_bijective C₂ f Af hf hfQ hd.1 hd.2) hd.1 hP0 hd.2
        (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine (Polynomial.C Polynomial.X))
      rwa [SmoothPlaneCurve.evalAt_x] at h
    · have h := pointValuation_coordGen_sub_evalAt_lt_one C₂ Af hX hY
        (residue_closure_bijective C₂ f Af hf hfQ hd.1 hd.2) hd.1 hP0 hd.2
        (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine Polynomial.X)
      rwa [SmoothPlaneCurve.evalAt_y] at h

end Headline

end Extension

/-! ### Existence of the denominator -/

section Denominator

variable {C₂}
variable {C₁ : SmoothPlaneCurve F}
variable [Algebra C₂.FunctionField C₁.FunctionField]
  [FiniteDimensional C₂.FunctionField C₁.FunctionField]

include C₂ in
omit [FiniteDimensional C₂.FunctionField C₁.FunctionField] in
/-- **Choice of the denominator** (instance-free): there is a single nonzero
`f ∈ F[C₂]` clearing the denominators of all coefficients of the minimal polynomials of
the two coordinate functions of `C₁` over `K(C₂)` (common denominator in the fraction
field of `F[C₂]`). -/
theorem exists_denominator :
    ∃ f : C₂.CoordinateRing, f ≠ 0 ∧
      (∀ i, ∃ a : C₂.CoordinateRing,
        (minpoly C₂.FunctionField (coordXFun C₁)).coeff i *
            algebraMap C₂.CoordinateRing C₂.FunctionField f
          = algebraMap C₂.CoordinateRing C₂.FunctionField a) ∧
      (∀ i, ∃ a : C₂.CoordinateRing,
        (minpoly C₂.FunctionField (coordYFun C₁)).coeff i *
            algebraMap C₂.CoordinateRing C₂.FunctionField f
          = algebraMap C₂.CoordinateRing C₂.FunctionField a) := by
  classical
  set px := minpoly C₂.FunctionField (coordXFun C₁) with hpx
  set py := minpoly C₂.FunctionField (coordYFun C₁) with hpy
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (C₂.CoordinateRing)⁰
    ((Finset.range (px.natDegree + 1)).image px.coeff ∪
      (Finset.range (py.natDegree + 1)).image py.coeff)
  have key : ∀ p : Polynomial C₂.FunctionField,
      (∀ j, j ≤ p.natDegree → IsLocalization.IsInteger C₂.CoordinateRing
        ((b : C₂.CoordinateRing) • p.coeff j)) →
      ∀ i, ∃ a : C₂.CoordinateRing,
        p.coeff i * algebraMap C₂.CoordinateRing C₂.FunctionField (b : C₂.CoordinateRing)
          = algebraMap C₂.CoordinateRing C₂.FunctionField a := by
    intro p hp i
    by_cases hi : i ≤ p.natDegree
    · obtain ⟨a, ha⟩ := hp i hi
      exact ⟨a, by rw [ha, Algebra.smul_def]; ring⟩
    · exact ⟨0, by
        rw [p.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi), zero_mul, map_zero]⟩
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_, ?_⟩
  · exact key px fun j hj ↦ hb _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))
  · exact key py fun j hj ↦ hb _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))

end Denominator

end HasseWeil.Curves.LocalizedDictionary
