import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrderCoeff

set_option linter.style.longLine false

/-!
# The third-order (mod `p³`) Dwork-coordinate coefficient machinery

This file builds the **third-order** Dwork power-basis coordinate coefficient
`valuedLambdaQuotientDworkCoeffModCube`, the mod-`p³` analog of the proven second-order
`valuedLambdaQuotientDworkCoeffModSq` (`CaseIICor823SecondOrderCoeff.lean`).  It is needed to recover
the **second `37`-adic digit** `c₆₈` of the degree-`68` Dwork slice's `varpi^{32}` coordinate, which
the mod-`p²` coordinate cannot see (the `−37` ramification fold annihilates the source's second digit
at mod-`p²`).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The third order

`valuedLambdaQuotientDworkCoeffModCube i` takes an element of
`ValuedIntegerRing p K ⧸ (lambdaIdeal p K)^(3*(p-1))` (`= mod (p³)`, since `(p³) = (λ)^{3(p-1)}`),
maps it into the completed Dwork ring, reads the `i`-th Dwork power-basis coordinate (an element of
`RationalPadicIntegerRing p ≅ ℤ_[p]`), and reduces it modulo `p³` via `rationalPadicIntegerToZModCube`
(`= PadicInt.toZModPow 3` through the ring equiv).  It is well-defined modulo `(λ)^{3(p-1)} = (p³)`
because changing the representative by `(p³)` changes each Dwork coordinate by `p³·(coord)`, which
dies mod `p³`.  This is the **exact mod-`p³` analog** of the second-order construction, built in
parallel here, reusing the `p`-generic Dwork local-algebra API
(`span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred`,
`dworkParameterPowerLinearMap_injective`).

## What is built

* **§0** — `rationalPadicIntegerToZModCube : RationalPadicIntegerRing p →+* ZMod (p^3)`, the mod-`p³`
  residue map, and `rationalPadicIntegerToZModCube_eq_zero_iff_mem_primeIdeal_pow`: its kernel is
  `(rationalPadicPrimeIdeal p)^3 = (p³)`.  Also the compatibility
  `rationalPadicIntegerToZModSq_comp_castHom`: reducing mod-`p³` then casting to `ZMod p²` is the
  mod-`p²` residue.

* **§1** — the mod-`p³` coordinate congruence:
  `x - y ∈ (dworkParameterIdeal p K)^(3(p-1))` (`= (p³)`) forces every Dwork power-basis coordinate to
  agree mod `p³` (`dworkParameterPowerBasis_coeff_zmodCube_eq_of_sub_mem_parameterIdeal_pow_three_pred`).

* **§2** — the third-order coefficient `valuedLambdaQuotientDworkCoeffModCube` and its evaluation API
  (`_mk`, `_evalₐ`) plus `_natCast_mul`, `_intCast_mul`, the parallel of the second-order API used by
  the deg-`68` factorial extraction.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter
open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 0. The mod-`p³` residue map on the rational completed integer ring -/

/-- **The mod-`p³` residue map** on the rational completed integer coefficient ring, transported from
mathlib's `PadicInt.toZModPow 3`.  Third-order analog of `rationalPadicIntegerToZModSq`. -/
noncomputable def rationalPadicIntegerToZModCube :
    RationalPadicIntegerRing p →+* ZMod (p ^ 3) :=
  (PadicInt.toZModPow (p := lambdaPadicPrime p) 3).comp
    (padicIntToRationalPadicIntegerRingEquiv (p := p)).symm.toRingHom

@[simp]
theorem rationalPadicIntegerToZModCube_natCast (n : ℕ) :
    rationalPadicIntegerToZModCube p (n : RationalPadicIntegerRing p) =
      (n : ZMod (p ^ 3)) := by
  change PadicInt.toZModPow (p := lambdaPadicPrime p) 3
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm
        (n : RationalPadicIntegerRing p)) = (n : ZMod (p ^ 3))
  have hmap :
      (padicIntToRationalPadicIntegerRingEquiv (p := p))
          (n : ℤ_[lambdaPadicPrime p]) =
        (n : RationalPadicIntegerRing p) := by
    simp [padicIntToRationalPadicIntegerRingEquiv]
  rw [← hmap, RingEquiv.symm_apply_apply, map_natCast]

theorem rationalPadicIntegerToZModCube_eq_zero_iff_mem_primeIdeal_pow
    (x : RationalPadicIntegerRing p) :
    rationalPadicIntegerToZModCube p x = 0 ↔ x ∈ (rationalPadicPrimeIdeal p) ^ 3 := by
  let e := padicIntToRationalPadicIntegerRingEquiv (p := p)
  change PadicInt.toZModPow (p := lambdaPadicPrime p) 3 (e.symm x) = 0 ↔
    x ∈ (rationalPadicPrimeIdeal p) ^ 3
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
  have hpe : e ((lambdaPadicPrime p : ℕ) : ℤ_[lambdaPadicPrime p]) =
      (p : RationalPadicIntegerRing p) := by
    have hpn : ((lambdaPadicPrime p : ℕ) : ℤ_[lambdaPadicPrime p]) =
        ((p : ℕ) : ℤ_[lambdaPadicPrime p]) := by norm_cast
    rw [hpn]
    simp [e, padicIntToRationalPadicIntegerRingEquiv]
  rw [show ((rationalPadicPrimeIdeal p) ^ 3 :
      Ideal (RationalPadicIntegerRing p)) =
        Ideal.span {(p : RationalPadicIntegerRing p) ^ 3} from by
      rw [rationalPadicPrimeIdeal, Ideal.span_singleton_pow]]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e c, ?_⟩
    have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hx, hc, map_mul, map_pow, hpe]
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    have hpe' : e.symm (p : RationalPadicIntegerRing p) =
        ((lambdaPadicPrime p : ℕ) : ℤ_[lambdaPadicPrime p]) := by
      rw [← hpe, RingEquiv.symm_apply_apply]
    rw [hc, map_mul, map_pow, hpe']

/-- **Mod-`p³` then cast to `ZMod p²` is the mod-`p²` residue** (proven): `castHom (p²∣p³) ∘
rationalPadicIntegerToZModCube = rationalPadicIntegerToZModSq`.  Both sides are `PadicInt.toZModPow`
through the same equiv, and `toZModPow 3` followed by the `ZMod p³ → ZMod p²` cast is `toZModPow 2`
(`PadicInt.zmod_cast_comp_toZModPow`).  Lets the mod-`p³` coordinate recover the mod-`p²` coordinate. -/
theorem castHom_rationalPadicIntegerToZModCube (x : RationalPadicIntegerRing p) :
    (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2)))
        (rationalPadicIntegerToZModCube p x) =
      rationalPadicIntegerToZModSq p x := by
  change (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2)))
      (PadicInt.toZModPow (p := lambdaPadicPrime p) 3
        ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x)) =
    PadicInt.toZModPow (p := lambdaPadicPrime p) 2
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x)
  rw [show (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2)))
        (PadicInt.toZModPow (p := lambdaPadicPrime p) 3
          ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x)) =
      (ZMod.castHom (pow_dvd_pow (lambdaPadicPrime p : ℕ) (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2)))
        (PadicInt.toZModPow (p := lambdaPadicPrime p) 3
          ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x)) from by
      congr 1]
  have := PadicInt.zmod_cast_comp_toZModPow (p := lambdaPadicPrime p)
    2 3 (by norm_num)
  exact congrArg (fun f => f ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x)) this

/-! ## 1. The mod-`p³` Dwork power-basis coordinate congruence

If `x - y ∈ (dworkParameterIdeal p K)^(3(p-1)) = (p³)`, then every Dwork power-basis coordinate agrees
mod `p³`.  Third-order analog of `dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_…`; the proof
is the exact parallel with `p³` in place of `p²`. -/

set_option maxHeartbeats 800000 in
-- The proof compares two full Dwork power-basis expansions through the completed ramification
-- identity `(p³) = (varpi)^(3(p-1))`; elaborating the basis and scalar-action coercions is slower
-- than the default budget (as in the second-order analog).
omit [NumberField.IsCMField K] in
/-- **The mod-`p³` Dwork-coordinate congruence (ideal form)** (proven): `x - y ∈
(dworkParameterIdeal p K)^(3(p-1))` forces each Dwork power-basis coordinate difference into
`(rationalPadicPrimeIdeal p)^3`.  Third-order parallel of
`dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_pow_two_pred`. -/
theorem dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_cube_of_mem_parameterIdeal_pow_three_pred
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (3 * (p - 1)))
    (i : Fin (p - 1)) :
    (dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i ∈
      (rationalPadicPrimeIdeal p) ^ 3 := by
  classical
  let R₀ : Type := RationalPadicIntegerRing p
  let S : Type _ := DworkCompleteIntegerRing p K
  have hspan : x - y ∈ Ideal.span ({(p : S) ^ 3} : Set S) := by
    rw [← Ideal.span_singleton_pow,
      span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred (p := p) (K := K),
      ← pow_mul, Nat.mul_comm]
    exact hxy
  rcases Ideal.mem_span_singleton'.mp hspan with ⟨z, hz⟩
  let a : Fin (p - 1) → R₀ :=
    (dworkParameterPowerBasis p K).repr x -
      (dworkParameterPowerBasis p K).repr y
  let b : Fin (p - 1) → R₀ :=
    (dworkParameterPowerBasis p K).repr z
  have hmap_a :
      dworkParameterPowerLinearMap p K a = x - y := by
    calc
      dworkParameterPowerLinearMap p K a =
          dworkParameterPowerLinearMap p K
            ((dworkParameterPowerBasis p K).repr x -
              (dworkParameterPowerBasis p K).repr y) := rfl
      _ =
          dworkParameterPowerLinearMap p K ((dworkParameterPowerBasis p K).repr x) -
            dworkParameterPowerLinearMap p K ((dworkParameterPowerBasis p K).repr y) :=
            (dworkParameterPowerLinearMap p K).map_sub
              ((dworkParameterPowerBasis p K).repr x)
              ((dworkParameterPowerBasis p K).repr y)
      _ = x - y := by
            rw [KummerLogTrace.dworkParameterPowerLinearMap_repr
                (p := p) (K := K) x,
              KummerLogTrace.dworkParameterPowerLinearMap_repr
                (p := p) (K := K) y]
  have hmap_b :
      dworkParameterPowerLinearMap p K (((p : R₀) ^ 3) • b) = x - y := by
    have hbmap : dworkParameterPowerLinearMap p K b = z := by
      change dworkParameterPowerLinearMap p K
        ((dworkParameterPowerBasis p K).repr z) = z
      exact KummerLogTrace.dworkParameterPowerLinearMap_repr
        (p := p) (K := K) z
    calc
      dworkParameterPowerLinearMap p K (((p : R₀) ^ 3) • b)
          = ((p : R₀) ^ 3) • dworkParameterPowerLinearMap p K b :=
            (dworkParameterPowerLinearMap p K).map_smul ((p : R₀) ^ 3) b
      _ = ((p : R₀) ^ 3) • z := by rw [hbmap]
      _ = (p : S) ^ 3 * z := by
            change algebraMap R₀ S ((p : R₀) ^ 3) * z = (p : S) ^ 3 * z
            simp [R₀, S]
      _ = x - y := by simpa [S, mul_comm] using hz
  have hcoeff : a = ((p : R₀) ^ 3) • b :=
    dworkParameterPowerLinearMap_injective (p := p) (K := K)
      (hmap_a.trans hmap_b.symm)
  have hi := congrFun hcoeff i
  change a i ∈ (rationalPadicPrimeIdeal p) ^ 3
  rw [hi]
  have hp3_mem : (p : R₀) ^ 3 ∈ (rationalPadicPrimeIdeal p) ^ 3 := by
    rw [rationalPadicPrimeIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self ((p : R₀) ^ 3)
  have hmul_mem : (p : R₀) ^ 3 * b i ∈ (rationalPadicPrimeIdeal p) ^ 3 :=
    ((rationalPadicPrimeIdeal p) ^ 3).mul_mem_right (b i) hp3_mem
  have hi' : (((p : R₀) ^ 3) • b) i = (p : R₀) ^ 3 * b i := by
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hi']
  exact hmul_mem

omit [NumberField.IsCMField K] in
/-- **The mod-`p³` Dwork-coordinate congruence (residue form)** (proven): `x - y ∈
(dworkParameterIdeal p K)^(3(p-1))` forces each Dwork power-basis coordinate to agree under
`rationalPadicIntegerToZModCube`.  Third-order parallel of
`dworkParameterPowerBasis_coeff_zmodSq_eq_of_sub_mem_parameterIdeal_pow_two_pred`. -/
theorem dworkParameterPowerBasis_coeff_zmodCube_eq_of_sub_mem_parameterIdeal_pow_three_pred
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (3 * (p - 1)))
    (i : Fin (p - 1)) :
    rationalPadicIntegerToZModCube p ((dworkParameterPowerBasis p K).repr x i) =
      rationalPadicIntegerToZModCube p ((dworkParameterPowerBasis p K).repr y i) := by
  have hmem :=
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_cube_of_mem_parameterIdeal_pow_three_pred
      (p := p) (K := K) hxy i
  have hzero :
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr x i -
          (dworkParameterPowerBasis p K).repr y i) = 0 :=
    (rationalPadicIntegerToZModCube_eq_zero_iff_mem_primeIdeal_pow
      (p := p)
      ((dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i)).mpr hmem
  exact sub_eq_zero.mp (by simpa [map_sub] using hzero)

/-! ## 2. The third-order Dwork-coordinate coefficient

`valuedLambdaQuotientDworkCoeffModCube i` reads the `varpi^i` Dwork coordinate modulo `p³` of a valued
`λ`-quotient at precision `3*(p-1)` (`= mod (p³)`), through the completed Dwork ring.  Full mod-`p³`
analog of `valuedLambdaQuotientDworkCoeffModSq`. -/

omit [NumberField.IsCMField K] in
/-- The `varpi^i` coefficient modulo `p³` of a completed Dwork quotient modulo `(varpi)^(3(p-1))`.
Well-defined by the third-order coordinate congruence (§1). -/
noncomputable def dworkParameterQuotientCoeffModCube
    (i : Fin (p - 1)) :
    DworkCompleteIntegerRing p K ⧸ (dworkParameterIdeal p K) ^ (3 * (p - 1)) →
      ZMod (p ^ 3) :=
  fun q =>
    Quotient.liftOn' q
      (fun x : DworkCompleteIntegerRing p K =>
        rationalPadicIntegerToZModCube p
          ((dworkParameterPowerBasis p K).repr x i))
      (by
        intro x y hxy
        have hmem : x - y ∈ (dworkParameterIdeal p K) ^ (3 * (p - 1)) := by
          simpa using ((Submodule.quotientRel_def
            (p := (dworkParameterIdeal p K) ^ (3 * (p - 1)))).mp hxy)
        exact dworkParameterPowerBasis_coeff_zmodCube_eq_of_sub_mem_parameterIdeal_pow_three_pred
          (p := p) (K := K) hmem i)

omit [NumberField.IsCMField K] in
@[simp]
theorem dworkParameterQuotientCoeffModCube_mk
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1))) x) =
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr x i) :=
  rfl

omit [NumberField.IsCMField K] in
theorem lambdaIdeal_pow_three_pred_le_comap_dworkParameterIdeal_pow_three_pred :
    (lambdaIdeal p K) ^ (3 * (p - 1)) ≤
      ((dworkParameterIdeal p K) ^ (3 * (p - 1))).comap
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)) := by
  intro x hx
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  have hmap :
      algebraMap R S x ∈
        Ideal.map (algebraMap R S) ((lambdaIdeal p K) ^ (3 * (p - 1))) :=
    Ideal.mem_map_of_mem (algebraMap R S) hx
  simpa [R, S, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K), dworkCompleteLambdaIdeal, Ideal.map_pow] using hmap

omit [NumberField.IsCMField K] in
/-- The `varpi^i` coefficient modulo `p³` of a valued `lambda`-quotient at precision `3*(p-1)`, read
after mapping the representative into the completed Dwork ring.  Third-order analog of
`valuedLambdaQuotientDworkCoeffModSq`. -/
noncomputable def valuedLambdaQuotientDworkCoeffModCube
    (i : Fin (p - 1)) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1)) → ZMod (p ^ 3) :=
  fun q =>
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
      (Ideal.quotientMap ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))
        (lambdaIdeal_pow_three_pred_le_comap_dworkParameterIdeal_pow_three_pred
          (p := p) (K := K)) q)

omit [NumberField.IsCMField K] in
@[simp]
theorem valuedLambdaQuotientDworkCoeffModCube_mk
    (i : Fin (p - 1)) (x : ValuedIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (3 * (p - 1))) x) =
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x) i) := by
  change
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x)) =
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x) i)
  rw [dworkParameterQuotientCoeffModCube_mk]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModCube_evalₐ
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (3 * (p - 1)) x) =
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr x i) := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (3 * (p - 1)) x)
  have hzero :
      AdicCompletion.evalₐ I (3 * (p - 1))
        (x - algebraMap R S r) = 0 := by
    rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact sub_eq_zero.mpr hr.symm
  have hmemLam :
      x - algebraMap R S r ∈ (dworkCompleteLambdaIdeal p K) ^ (3 * (p - 1)) :=
    dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
      (p := p) (K := K) hzero
  have hmem :
      x - algebraMap R S r ∈ (dworkParameterIdeal p K) ^ (3 * (p - 1)) := by
    simpa [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K)] using hmemLam
  calc
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (3 * (p - 1)) x)
        =
      valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (3 * (p - 1))) r) := by
          simpa [I] using congrArg
            (valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i) hr.symm
    _ =
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr (algebraMap R S r) i) := by
          rw [valuedLambdaQuotientDworkCoeffModCube_mk]
    _ =
      rationalPadicIntegerToZModCube p
        ((dworkParameterPowerBasis p K).repr x i) :=
          (dworkParameterPowerBasis_coeff_zmodCube_eq_of_sub_mem_parameterIdeal_pow_three_pred
            (p := p) (K := K) hmem i).symm

/-! ### Additive and scalar linearity of the third-order coefficient -/

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModCube_mk_add
    (i : Fin (p - 1)) (x y : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1))) (x + y)) =
      dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1))) x) +
      dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1))) y) := by
  change rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr (x + y) i) =
    rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr x i) +
    rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr y i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (x + y) i =
        ((dworkParameterPowerBasis p K).repr x +
          (dworkParameterPowerBasis p K).repr y) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_add x y)
  rw [hrepr]
  change rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr x i +
        (dworkParameterPowerBasis p K).repr y i) =
    rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr x i) +
    rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr y i)
  rw [map_add]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModCube_mk_neg
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1))) (-x)) =
      -dworkParameterQuotientCoeffModCube (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1))) x) := by
  change rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr (-x) i) =
    -rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr x i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (-x) i =
        (-(dworkParameterPowerBasis p K).repr x) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_neg x)
  rw [hrepr]
  change rationalPadicIntegerToZModCube p
      (-(dworkParameterPowerBasis p K).repr x i) =
    -rationalPadicIntegerToZModCube p
      ((dworkParameterPowerBasis p K).repr x i)
  rw [map_neg]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModCube_add
    (i : Fin (p - 1))
    (x y : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i (x + y) =
      valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i x +
        valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  change dworkParameterQuotientCoeffModCube (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (x + y))) =
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x)) +
    dworkParameterQuotientCoeffModCube (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) y))
  rw [map_add, dworkParameterQuotientCoeffModCube_mk_add]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModCube_neg
    (i : Fin (p - 1))
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i (-x) =
      -valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i x := by
  refine Quotient.inductionOn' x ?_
  intro x
  change dworkParameterQuotientCoeffModCube (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (-x))) =
    -dworkParameterQuotientCoeffModCube (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (3 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x))
  rw [map_neg, dworkParameterQuotientCoeffModCube_mk_neg]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModCube_natCast_mul
    (i : Fin (p - 1)) (n : ℕ)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i
        ((n : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) * x) =
      (n : ZMod (p ^ 3)) *
        valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i x := by
  induction n with
  | zero =>
      have hzero := valuedLambdaQuotientDworkCoeffModCube_add
        (p := p) (K := K) i
        (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) 0
      simpa using hzero
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, valuedLambdaQuotientDworkCoeffModCube_add, ih]
      simp
      ring

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModCube_intCast_mul
    (i : Fin (p - 1)) (z : ℤ)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i
        ((z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) * x) =
      (z : ZMod (p ^ 3)) *
        valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i x := by
  cases z with
  | ofNat n =>
      simpa using
        valuedLambdaQuotientDworkCoeffModCube_natCast_mul
          (p := p) (K := K) i n x
  | negSucc n =>
      have h :=
        valuedLambdaQuotientDworkCoeffModCube_natCast_mul
          (p := p) (K := K) i (n + 1) x
      rw [Int.cast_negSucc, Int.cast_negSucc]
      rw [neg_mul]
      rw [valuedLambdaQuotientDworkCoeffModCube_neg, h]
      ring

end CyclotomicUnits
end BernoulliRegular

end
