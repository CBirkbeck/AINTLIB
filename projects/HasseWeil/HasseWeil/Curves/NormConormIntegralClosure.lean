/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.RamificationFinite

/-!
# The norm–conorm count over the integral closure `B` (CoordHom-free, Silverman II.3.6)

For a finite separable extension `K(C₁) / K(C₂)` of smooth-curve function fields that has *no*
global affine `CoordHom` (e.g. the pullback of a genuine isogeny, whose pullback of the
coordinate generators has poles at the affine kernel), the affine norm–conorm template of
`HasseWeil/Curves/PushforwardDivisor.lean` (`relNorm_maximalIdealAt_eq`,
`count_relNorm_eq_sum_fiber`) does not apply: it routes through the affine coordinate-ring
extension `F[C₂] → F[C₁]`.  Instead we work over the **integral closure**

  `B := integralClosure C₂.CoordinateRing C₁.FunctionField`,

whose maximal ideals are in bijection with *all* the places of `C₁` over the affine places of
`C₂` (supplied by `HasseWeil/Curves/LocalizedDictionary.lean`, instantiated at the trivial
localization `Af := C₂.CoordinateRing`, `f := 1`, valid at *every* affine place).

This file ports the affine template over `B`:
* the `s = 1` core `relNorm_{C₂.CoordinateRing}(P) = m_{below}` for a maximal `P` of `B`;
* the per-place count `count_{m_Q}(relNorm(span{w})) = Σ_{P over m_Q} count_P(span{w})`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6, II.3.6, III.4.10(c).
-/

open WeierstrassCurve
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace HasseWeil.Curves.NormConormIntegralClosure

open HasseWeil.Curves HasseWeil.Curves.LocalizedDictionary

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {C₁ C₂ : SmoothPlaneCurve F} [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
variable [IsIntegrallyClosed C₂.CoordinateRing]
variable [PerfectField (FractionRing C₂.CoordinateRing)]
variable [algKL : Algebra C₂.FunctionField C₁.FunctionField]
  [finKL : FiniteDimensional C₂.FunctionField C₁.FunctionField]
  [sepKL : Algebra.IsSeparable C₂.FunctionField C₁.FunctionField]
  [algCR1 : Algebra C₂.CoordinateRing C₁.FunctionField]
  [tw1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField C₁.FunctionField]
  [twF : IsScalarTower F C₂.FunctionField C₁.FunctionField]

/-- The integral closure `B` of `C₂.CoordinateRing` inside `C₁.FunctionField` (as a subalgebra;
its coercion to a type carries the Dedekind/finite/fraction-ring structure of the AKLB setup). -/
noncomputable abbrev B : Subalgebra C₂.CoordinateRing C₁.FunctionField :=
  integralClosure C₂.CoordinateRing C₁.FunctionField

/-! ### The trivial localization `Af := C₂.CoordinateRing`, `f := 1` -/

noncomputable instance instAway1 :
    IsLocalization.Away (1 : C₂.CoordinateRing) C₂.CoordinateRing :=
  IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id

noncomputable instance instTowTrivial :
    IsScalarTower C₂.CoordinateRing C₂.CoordinateRing C₂.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `1 ∉ m_Q` for every smooth point `Q` (a maximal ideal is proper). -/
theorem one_notMem_maximalIdealAt (Q : C₂.SmoothPoint) :
    (1 : C₂.CoordinateRing) ∉ C₂.maximalIdealAt Q := by
  rw [← Ideal.eq_top_iff_one]
  exact (C₂.maximalIdealAt_isMaximal Q).ne_top

/-- `awayIdealAt C₂.CoordinateRing Q = m_Q` (the localization at `f := 1` is trivial, so the
extended ideal is the original maximal ideal). -/
theorem awayIdealAt_eq_maximalIdealAt (Q : C₂.SmoothPoint) :
    awayIdealAt (C₂ := C₂) C₂.CoordinateRing Q = C₂.maximalIdealAt Q := by
  rw [awayIdealAt, Algebra.algebraMap_self, Ideal.map_id]

/-! ### The Dedekind/finite/torsion-free/fraction-ring instances for `B` (T-A1) -/

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a Dedekind domain (Krull–Akizuki, separable case). -/
instance instDedekindB : IsDedekindDomain (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.isDedekindDomain C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` is module-finite over `C₂.CoordinateRing`. -/
instance instModuleFiniteB :
    Module.Finite C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.module_finite C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` has fraction field `C₁.FunctionField`. -/
instance instFractionRingB :
    IsFractionRing (B (C₁ := C₁) (C₂ := C₂)) C₁.FunctionField :=
  RamificationFinite.isFractionRing C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a torsion-free `C₂.CoordinateRing`-module. -/
instance instTorsionFreeB :
    Module.IsTorsionFree C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)) :=
  RamificationFinite.isTorsionFree C₂.CoordinateRing C₂.FunctionField C₁.FunctionField _

/-! ### The coordinate ring of `C₁` lands in `B` (T-A2, integrality sub-wall)

The coordinate generators `x₁ = coordXFun C₁`, `y₁ = coordYFun C₁` of `C₁`, regarded inside
`K(C₁)`, are integral over `C₂.CoordinateRing`: each is regular at every place of `C₁` lying
over an *affine* place of `C₂` (their only poles — at `∞` of `C₁` and at the affine kernel —
all lie over `∞` of `C₂`).  Hence the entire coordinate ring `F[C₁] = F[x₁, y₁]` lands in `B`.

This is the integral-closure analogue of the affine `coordRing_mem_integralClosure`
(`LocalizedDictionary.lean`) at the *global* base (`Af := C₂.CoordinateRing`, `f := 1`).  Its
content is the genuine geometric input (regularity of the coordinate functions at all places
over the affine part of `C₂`); everything downstream is structural. -/

/-- **The `x`-generator of `C₁` is integral over `C₂.CoordinateRing`** (regular at every place
of `C₁` over an affine place of `C₂`). -/
theorem coordXFun_mem_B :
    coordXFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) := by
  sorry

/-- **The `y`-generator of `C₁` is integral over `C₂.CoordinateRing`.** -/
theorem coordYFun_mem_B :
    coordYFun C₁ ∈ (B (C₁ := C₁) (C₂ := C₂)) := by
  sorry

/-- **The coordinate ring of `C₁` lands in `B`** (Silverman II.2.6, the integral-closure form):
for every `r ∈ F[C₁]`, the image `algebraMap r ∈ K(C₁)` is integral over `C₂.CoordinateRing`.
Built from the two generator integralities via `LocalizedDictionary.coordRing_mem_integralClosure`
(at the trivial localization `Af := C₂.CoordinateRing`). -/
theorem coordRing_mem_B (r : C₁.CoordinateRing) :
    algebraMap C₁.CoordinateRing C₁.FunctionField r ∈ (B (C₁ := C₁) (C₂ := C₂)) :=
  coordRing_mem_integralClosure C₂ C₂.CoordinateRing coordXFun_mem_B coordYFun_mem_B r

/-! ### Inertia degree `1` and the `s = 1` core over `B` (T-A2 core) -/

/-- **Inertia degree `1`** for a prime `P` of `B` lying over the maximal ideal `m_Q` of
`C₂.CoordinateRing`: over an algebraically closed base the residue fields are trivial.  This is
`LocalizedDictionary.inertiaDeg_eq_one_of_under_eq` instantiated at the trivial localization
`Af := C₂.CoordinateRing`, `f := 1` (valid at *every* affine place since `1 ∉ m_Q`). -/
theorem inertiaDeg_eq_one (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (Q : C₂.SmoothPoint) (hPp : P.IsPrime)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.inertiaDeg (C₂.maximalIdealAt Q) P = 1 := by
  have hfQ : (1 : C₂.CoordinateRing) ∉ C₂.maximalIdealAt Q := one_notMem_maximalIdealAt Q
  have hPq' : P.under C₂.CoordinateRing = awayIdealAt (C₂ := C₂) C₂.CoordinateRing Q := by
    rw [hPq, awayIdealAt_eq_maximalIdealAt]
  have := inertiaDeg_eq_one_of_under_eq C₂ (1 : C₂.CoordinateRing) C₂.CoordinateRing
    one_ne_zero hfQ hPp hPq'
  rwa [awayIdealAt_eq_maximalIdealAt] at this

/-- **The `s = 1` core — Silverman II.3.6**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m_Q` of `C₂.CoordinateRing`, `relNorm_{C₂.CoordinateRing}(P) = m_Q`.  Over char-0
this is mathlib's `relNorm_eq_pow_of_isMaximal` (`relNorm P = m_Q ^ inertiaDeg`) with the inertia
degree `1` over an algebraically closed base. -/
theorem relNorm_eq_of_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (Q : C₂.SmoothPoint)
    (hPq : P.under C₂.CoordinateRing = C₂.maximalIdealAt Q) :
    Ideal.relNorm C₂.CoordinateRing P = C₂.maximalIdealAt Q := by
  haveI : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI hLies : P.LiesOver (C₂.maximalIdealAt Q) := ⟨hPq.symm⟩
  rw [Ideal.relNorm_eq_pow_of_isMaximal P (C₂.maximalIdealAt Q),
    inertiaDeg_eq_one P Q hP.isPrime hPq, pow_one]

/-- **The `s = 1` core, smooth-point-free form**: for a maximal ideal `P` of `B` lying over the
maximal ideal `m` of `C₂.CoordinateRing` corresponding (via `exists_smoothPoint_of_isMaximal`) to
*some* smooth point of `C₂`, `relNorm(P) = m`.  Wraps `relNorm_eq_of_under` so the count lemma can
use it for a general `B`-prime without first naming the target smooth point. -/
theorem relNorm_eq_under (P : Ideal (B (C₁ := C₁) (C₂ := C₂)))
    (hP : P.IsMaximal) (hm : (P.under C₂.CoordinateRing).IsMaximal) :
    Ideal.relNorm C₂.CoordinateRing P = P.under C₂.CoordinateRing := by
  obtain ⟨Q, hQ⟩ := C₂.exists_smoothPoint_of_isMaximal hm
  rw [relNorm_eq_of_under P hP Q hQ.symm, hQ]

/-! ### The per-place norm–divisor count over `B` (T-A2, the core)

The `B`-analogue of `CurveMap.count_relNorm_eq_sum_fiber` (`PushforwardDivisor.lean`): the
multiplicity of `m_Q` in `relNorm_{C₂.CoordinateRing}(span{w})` for `w ∈ B` is the fibre sum of the
multiplicities of the `B`-primes over `m_Q`.  Built on the `s = 1` core `relNorm_eq_under`
(`relNorm(P) = P.under` for a maximal `P` of `B`) — the genuine arithmetic of Silverman II.3.6 —
together with `relNorm` multiplicativity and `relNorm_singleton`. -/

set_option maxHeartbeats 1600000 in
/-- **The per-place norm–divisor count over `B`** (T-A2): for `w ∈ B` nonzero and a smooth point
`Q` of `C₂`, the `m_Q`-adic multiplicity of `relNorm(span{w})` equals the sum over the `B`-primes
`P` above `m_Q` of the `P`-adic multiplicity of `span{w}`.  All inertia degrees are `1`
(`inertiaDeg_eq_one`), so `relNorm(P^k) = m_Q^k` for `P` over `m_Q` and `relNorm(P'^k)` is prime to
`m_Q` for `P'` over a different maximal ideal. -/
theorem count_relNorm_eq_sum_fiber_B {w : B (C₁ := C₁) (C₂ := C₂)} (hw : w ≠ 0)
    (Q : C₂.SmoothPoint) :
    (Associates.mk (C₂.maximalIdealAt Q)).count
        (Associates.mk (Ideal.relNorm C₂.CoordinateRing (Ideal.span {w}))).factors =
      ∑ P ∈ IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q)
          (B (C₁ := C₁) (C₂ := C₂)),
        (Associates.mk P).count (Associates.mk (Ideal.span ({w} : Set _))).factors := by
  classical
  set p : Ideal C₂.CoordinateRing := C₂.maximalIdealAt Q with hp_def
  haveI hpMax : p.IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hp_ne : p ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  let vp : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing :=
    ⟨p, hpMax.isPrime, hp_ne⟩
  have h_vp_irr : Irreducible (Associates.mk vp.asIdeal) := vp.associates_irreducible
  have hI_ne : Ideal.span ({w} : Set (B (C₁ := C₁) (C₂ := C₂))) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hw
  have h_supp := Ideal.hasFiniteMulSupport (R := B (C₁ := C₁) (C₂ := C₂)) hI_ne
  have h_prime_ne_bot : ∀ P ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)),
      P ≠ ⊥ := by
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne] at hP
    intro h_eq
    apply hp_ne
    have h_over : p = P.under C₂.CoordinateRing := hP.2.over
    rw [h_eq, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective C₂.CoordinateRing (B (C₁ := C₁) (C₂ := C₂)))] at h_over
    exact h_over
  let toHOS : ∀ P ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)),
      IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)) := fun P hP =>
    ⟨P, ((IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne).mp hP).1,
      h_prime_ne_bot P hP⟩
  let sH : Finset (IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :=
    (IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))).attach.image
      (fun ⟨P, hP⟩ => toHOS P hP)
  set S : Finset (IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) :=
    h_supp.toFinset ∪ sH with hS_def
  have hS_supp : Function.mulSupport
      (fun P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)) =>
        P.maxPowDividing (Ideal.span ({w} : Set _))) ⊆ ↑S := by
    intro P hP
    simp only [hS_def, Finset.coe_union, Set.mem_union]
    left
    exact h_supp.mem_toFinset.mpr hP
  have h_finprod_eq_prod :
      (∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂)),
        P.maxPowDividing (Ideal.span ({w} : Set _))) =
      ∏ P ∈ S, P.maxPowDividing (Ideal.span ({w} : Set _)) :=
    finprod_eq_prod_of_mulSupport_subset _ hS_supp
  conv_lhs =>
    rw [← Ideal.finprod_heightOneSpectrum_factorization hI_ne, h_finprod_eq_prod,
      map_prod (Ideal.relNorm C₂.CoordinateRing)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]
  have h_term_ne : ∀ P ∈ S,
      Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^
        ((Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors)) ≠ 0 := by
    intro P _
    rw [Associates.mk_ne_zero]
    apply pow_ne_zero
    rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff]
    exact P.ne_bot
  rw [show Associates.mk (∏ P ∈ S, (Ideal.relNorm C₂.CoordinateRing) P.asIdeal ^
        (Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) =
      ∏ P ∈ S, Associates.mk ((Ideal.relNorm C₂.CoordinateRing) P.asIdeal ^
        (Associates.mk P.asIdeal).count
          (Associates.mk (Ideal.span ({w} : Set _))).factors) from
      map_prod (Associates.mkMonoidHom (M := Ideal C₂.CoordinateRing)) _ _]
  rw [count_finset_prod_factors h_term_ne h_vp_irr]
  have h_S_split : ∀ P ∈ S,
      (Associates.mk vp.asIdeal).count
        (Associates.mk ((Ideal.relNorm C₂.CoordinateRing P.asIdeal) ^
          ((Associates.mk P.asIdeal).count
            (Associates.mk (Ideal.span ({w} : Set _))).factors))).factors =
      if P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂)) then
        (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span ({w} : Set _))).factors
      else 0 := by
    intro P _
    haveI hPmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime P.ne_bot
    haveI hPunder_max : (P.asIdeal.under C₂.CoordinateRing).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
    have hrelP : Ideal.relNorm C₂.CoordinateRing P.asIdeal = P.asIdeal.under C₂.CoordinateRing :=
      relNorm_eq_under P.asIdeal hPmax hPunder_max
    by_cases h_over : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (B (C₁ := C₁) (C₂ := C₂))
    · rw [if_pos h_over]
      haveI hPlies : P.asIdeal.LiesOver p :=
        ((IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne).mp
          h_over).2
      have hunder_eq : P.asIdeal.under C₂.CoordinateRing = p := hPlies.over.symm
      rw [hrelP, hunder_eq, Associates.mk_pow]
      change (Associates.mk vp.asIdeal).count (Associates.mk vp.asIdeal ^ _).factors = _
      rw [Associates.count_pow (by rw [Associates.mk_ne_zero]; exact hp_ne) h_vp_irr,
        Associates.count_self h_vp_irr, mul_one]
    · rw [if_neg h_over]
      have hPne : P.asIdeal.under C₂.CoordinateRing ≠ p := by
        intro hpe
        apply h_over
        rw [IsDedekindDomain.mem_primesOverFinset_iff (B := B (C₁ := C₁) (C₂ := C₂)) hp_ne]
        exact ⟨P.isPrime, ⟨hpe.symm⟩⟩
      rw [hrelP, Associates.mk_pow]
      obtain ⟨Q', hQ'⟩ := C₂.exists_smoothPoint_of_isMaximal hPunder_max
      have hP'_ne_bot2 : P.asIdeal.under C₂.CoordinateRing ≠ ⊥ := by
        rw [← hQ']; exact C₂.maximalIdealAt_ne_bot Q'
      let vP' : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing :=
        ⟨_, hPunder_max.isPrime, hP'_ne_bot2⟩
      have h_vP'_irr : Irreducible (Associates.mk vP'.asIdeal) := vP'.associates_irreducible
      have h_vp_ne_vP' : (Associates.mk vp.asIdeal) ≠ (Associates.mk vP'.asIdeal) := by
        intro h_eq
        apply hPne
        rw [Associates.mk_eq_mk_iff_associated] at h_eq
        exact (associated_iff_eq.mp h_eq).symm
      change (Associates.mk vp.asIdeal).count (Associates.mk vP'.asIdeal ^ _).factors = 0
      rw [Associates.count_pow (by rw [Associates.mk_ne_zero]; exact hP'_ne_bot2) h_vp_irr,
        Associates.count_eq_zero_of_ne h_vp_irr h_vP'_irr h_vp_ne_vP', Nat.mul_zero]
  rw [Finset.sum_congr rfl h_S_split, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij'
    (i := fun (P : IsDedekindDomain.HeightOneSpectrum (B (C₁ := C₁) (C₂ := C₂))) _ => P.asIdeal)
    (j := fun (P'' : Ideal (B (C₁ := C₁) (C₂ := C₂))) hP'' => toHOS P'' hP'') ?_ ?_ ?_ ?_ ?_
  · intro P hP
    exact (Finset.mem_filter.mp hP).2
  · intro P'' hP''
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [hS_def, Finset.mem_union]
      right
      simp only [sH, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨P'', hP'', rfl⟩
    · exact hP''
  · intro P hP
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rfl
  · intro P'' hP''
    rfl
  · intro P hP
    rfl

end HasseWeil.Curves.NormConormIntegralClosure
