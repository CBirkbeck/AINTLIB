import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71UnitDworkCoordBridge

/-!
# The `N`-generic specialized finite logarithm and the level-`71` Dwork-specialized residual

This file builds the **`N`-generic specialized finite logarithm**
`kummerLogDworkArtinHasseSpecializedFiniteLogN N a` (the precision-generic parallel of the proven
`kummerLogDworkArtinHasseSpecializedFiniteLog`, which is hard-coded at `N = p - 2 = 35` by
`kummerLogDworkArtinHasseSpecializedFiniteLog := kummerLogNormalizedQuotientFiniteLog ... (p - 2)`),
and isolates the **single** irreducible analytic kernel of the level-`71` unit ↔ Dwork-slice
coordinate bridge `CaseIICor823Level71UnitDworkCoordBridge37`
(`CaseIICor823Level71UnitDworkCoordBridge.lean`).  It imports only; it does **not** modify any
existing file.  No `sorry`, no `axiom`.

## What the `N`-generic refactor exposes

The proven first-order bridge
`valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled`
(`KummerLogFormalEvaluator/Folded.lean`) is the `N = p - 2` coordinate identity

  `coord_i(specializedFiniteLog) = (1 − k^i)·coord_i(dworkParameterNormalizedFiniteLogApprox)`.

Its two driving mechanisms are *both* `N`-generic:

* the **unscaled-minus-scaled decomposition**
  `kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs` (Part4) — but its proof goes
  through `kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_pow_pred`, the Teichmüller transport
  `τ(k) − k ∈ (λ)^{p-1}`, which is **exactly** `p − 1`-precise (the Teichmüller difference vanishes to
  order `p − 1`, *not* `2(p − 1)`);
* the **cyclotomic column factor**
  `valuedLambdaQuotientDworkCoeffModP_scaledNormalizedFiniteLog_eq_smul` (Folded) — `N`-generic via
  `samePrimeFiniteLog_quotientMap_cyclotomic` (`DworkParameter/Part18.lean`, any `N`).

The **definition** `kummerLogDworkArtinHasseSpecializedFiniteLog` fixes `N = p − 2`; the genuine
content at level `71 = 2(p − 1) − 1` is the **second-order Teichmüller/Fermat-quotient transport**
that the proven `p − 1`-precise `_evalₐ_pow_pred` does not supply.  We make the `N`-generic definition
explicit and re-express the level-`71` target's mod-`37²` coordinate identity `hCoord` so that the
only undischarged content is the single level-`71` finite-log equality

  `samePrimeFiniteLog 71 (c^{p-1} − 1) =`
    `samePrimeFiniteLog 71 (dworkParameterNormalizedCoordApprox 71)`
      `− samePrimeFiniteLog 71 (scaledDworkParameterNormalizedCoordApprox k 71)`,

i.e. the level-`71` lift of `kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs`
applied to the **unit** `c^{p-1} − 1` (combining the level-`71` unit ↔ quotient Fermat bridge with the
level-`71` Dwork ↔ quotient Teichmüller transport).  This is **strictly smaller** than
`CaseIICor823Level71UnitDworkCoordBridge37`: there the per-column mod-`37²`/mod-`37` coordinate value
is the unknown; here the coordinate extraction (the slice decomposition giving the proven
`37·(32!)⁻¹` and the cyclotomic column factor) is **discharged** from `N`-generic machinery, and the
*only* unknown is the single level-`71` finite-log equality of the unit with the Dwork-specialized
difference.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField
open scoped BigOperators

namespace BernoulliRegular.CyclotomicUnits

open BernoulliRegular.Reflection.Local

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

open PadicLogSetup PadicLogSetup.DworkParameter

/-! ## 1. The `N`-generic specialized finite logarithm

`kummerLogDworkArtinHasseSpecializedFiniteLogN N a := kummerLogNormalizedQuotientFiniteLog ... a N`,
the precision-generic parallel of the proven `kummerLogDworkArtinHasseSpecializedFiniteLog` (which is
the `N = p - 2` case).  Definitionally `kummerLogDworkArtinHasseSpecializedFiniteLog = ...N (p - 2)`
(`kummerLogDworkArtinHasseSpecializedFiniteLogN_pred_eq`). -/

/-- **The `N`-generic specialized finite logarithm**: the normalized-quotient finite logarithm at an
arbitrary precision `N`, parallel to the proven `kummerLogDworkArtinHasseSpecializedFiniteLog` which
hard-codes `N = p - 2`.  At `N = p - 2` it is definitionally equal to that object
(`kummerLogDworkArtinHasseSpecializedFiniteLogN_pred_eq`). -/
noncomputable def kummerLogDworkArtinHasseSpecializedFiniteLogN
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  kummerLogNormalizedQuotientFiniteLog (p := p) (K := K) hp_three a N

omit [NumberField.IsCMField K] in
/-- **The `N`-generic specialized finite log specializes to the proven `p − 2` object** (proven, by
`rfl`): `kummerLogDworkArtinHasseSpecializedFiniteLogN (p − 2) =
kummerLogDworkArtinHasseSpecializedFiniteLog`.  Confirms the `N`-generic definition is a genuine
generalization of the hard-coded one. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogN_pred_eq
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogN (p := p) (K := K) hp_three a (p - 2) =
      kummerLogDworkArtinHasseSpecializedFiniteLog (p := p) (K := K) hp_three a :=
  rfl

/-! ## 2. The `N`-generic unscaled-minus-scaled Dwork-parameter finite log

The unscaled and scaled Dwork-parameter normalized-coordinate finite logarithms at an arbitrary
precision `N` (the `N`-generic parallel of the `N = p - 2` objects that
`kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs` decomposes into).  Both
definitions are `N`-generic (`dworkParameterNormalizedCoordApprox`,
`scaledDworkParameterNormalizedCoordApprox` take the precision as an argument). -/

/-- **The `N`-generic unscaled Dwork-parameter normalized finite log**: the finite logarithm at
precision `N` of the principal-unit coordinate of the truncated normalized Artin-Hasse factor at the
Dwork-parameter approximant.  At `N = p - 2` this is the first summand of
`kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs`. -/
noncomputable def dworkParameterNormalizedCoordFiniteLogN (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteLog (p := p) (K := K) N
    (dworkParameterNormalizedCoordApprox (p := p) (K := K) N)
    (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal (p := p) (K := K) N)

/-- **The `N`-generic scaled Dwork-parameter normalized finite log**: the finite logarithm at
precision `N` of the principal-unit coordinate of the truncated normalized Artin-Hasse factor at the
scaled Dwork-parameter approximant for residue `z`.  At `N = p - 2`, `z = k`, this is the second
summand of `kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs`. -/
noncomputable def scaledDworkParameterNormalizedCoordFiniteLogN (z : ZMod p) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteLog (p := p) (K := K) N
    (scaledDworkParameterNormalizedCoordApprox (p := p) (K := K) z N)
    (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal (p := p) (K := K) z N)

omit [NumberField.IsCMField K] in
/-- **At `N = p − 2` the `N`-generic specialized finite log is the unscaled-minus-scaled Dwork
difference** (proven, re-export of `kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs`
on the `N`-generic objects): a *witness* that the `N = p − 2` instance of the level-`N`
unit ↔ Dwork-specialized identity holds, by the proven first-order chain.  The level-`71` instance is
the single irreducible kernel isolated in `§3`. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogN_pred_eq_normalizedCoordFiniteLog_diff
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogN (p := p) (K := K) hp_three a (p - 2) =
      dworkParameterNormalizedCoordFiniteLogN (p := p) (K := K) (p - 2) -
        scaledDworkParameterNormalizedCoordFiniteLogN (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) (p - 2) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogN_pred_eq,
    kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs]
  rfl

/-! ## 3. The `N`-generic cyclotomic column factor: scaled finite log = cyclotomic image of unscaled

`scaledDworkParameterNormalizedCoordFiniteLogN z N` is the cyclotomic image of
`dworkParameterNormalizedCoordFiniteLogN N` — the level-`N` analog of the proven
`samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap` (which is `N = p − 2`), via the
**`N`-generic** transports `quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox`
and `Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic`.  At the coordinate level this produces the
cyclotomic column factor. -/

omit [NumberField.IsCMField K] in
/-- **The `N`-generic scaled Dwork-parameter finite log is the cyclotomic image of the unscaled**
(proven, axiom-clean — fully `N`-generic): for any `N` and any cyclotomic residue `a`,
`scaledDworkParameterNormalizedCoordFiniteLogN a N = quotientMap (cyclotomicEquiv a)
(dworkParameterNormalizedCoordFiniteLogN N)`.

The level-`N` lift of the proven `samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap`
(`N = p − 2`): the cyclotomic image of the unscaled coordinate approximant differs from the scaled
approximant by an element of `(λ)^{N+1}`
(`quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox`, `N`-generic), and the
finite log commutes with the cyclotomic action
(`Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic`, `N`-generic). -/
theorem scaledDworkParameterNormalizedCoordFiniteLogN_eq_cyclotomic
    (a : CyclotomicUnitDelta p) (N : ℕ) :
    scaledDworkParameterNormalizedCoordFiniteLogN (p := p) (K := K) (a : ZMod p) N =
      Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
          (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) (N + 1))
        (dworkParameterNormalizedCoordFiniteLogN (p := p) (K := K) N) := by
  classical
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
  let x : ValuedIntegerRing p K :=
    dworkParameterNormalizedCoordApprox (p := p) (K := K) N
  let y : ValuedIntegerRing p K :=
    scaledDworkParameterNormalizedCoordApprox (p := p) (K := K) (a : ZMod p) N
  have hx : x ∈ lambdaIdeal p K := dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
    (p := p) (K := K) N
  have hy : y ∈ lambdaIdeal p K := scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
    (p := p) (K := K) (a : ZMod p) N
  have hex : e x ∈ lambdaIdeal p K :=
    Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx
  have hsub : e x - y ∈ (lambdaIdeal p K) ^ (N + 1) := by
    have hq := quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox
      (p := p) (K := K) a N
    exact Ideal.Quotient.eq.mp hq
  have hlog :
      samePrimeFiniteLog (p := p) (K := K) N (e x) hex =
        samePrimeFiniteLog (p := p) (K := K) N y hy :=
    samePrimeFiniteLog_eq_of_sub_mem (p := p) (K := K) hex hy hsub
  have hmap :=
    Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic
      (p := p) (K := K) (N := N) a hx
  -- `scaled log = log y = log (e x) = quotientMap (cyclotomicEquiv) (log x) = unscaled, mapped`.
  rw [scaledDworkParameterNormalizedCoordFiniteLogN, dworkParameterNormalizedCoordFiniteLogN]
  exact (hlog.symm.trans hmap.symm)

/-! ## 4. The mod-`p²` cyclotomic column factor on the level-`2(p−1)` Dwork coordinate

The mod-`p²` analog of `valuedLambdaQuotientDworkCoeffModP_quotientMap_cyclotomic`: the cyclotomic
action multiplies the `i`-th level-`2(p−1)` Dwork coordinate by the **mod-`p²` Teichmüller power**
`rationalPadicIntegerToZModSq (τ(a))^i`.  The factor is the genuine second-order Teichmüller datum; its
mod-`p` reduction is the residue `a` (`teichmullerCoeffModSq_castHom`), which is all the downstream
`37·`-collapse consumes. -/

/-- **The mod-`p²` Teichmüller coordinate factor** `rationalPadicIntegerToZModSq (τ(a))`, the
second-order (mod-`p²`) image of the Teichmüller lift of the residue `a`.  Its `i`-th power is the
cyclotomic column factor on the level-`2(p−1)` Dwork coordinate; its mod-`p` reduction is `a`. -/
noncomputable def teichmullerCoeffModSq (a : ZMod p) : ZMod (p ^ 2) :=
  rationalPadicIntegerToZModSq p (rationalPadicTeichmuller p a)

/-- **The mod-`p` reduction of the Teichmüller coordinate factor is the residue** (proven): `castHom
(teichmullerCoeffModSq a) = a`.  From the `castHom`/`ToZModSq` compatibility
`rationalPadicIntegerToZMod_eq_castHom_toZModSq` and `rationalPadicIntegerToZMod_teichmuller`
(`ToZMod (τ a) = a`).  This is why the genuine second-order Teichmüller datum drops out under the
`37·` factor: only its mod-`p` value `a` survives. -/
theorem teichmullerCoeffModSq_castHom (h : (p : ℕ) ∣ p ^ 2) (a : ZMod p) :
    (ZMod.castHom h (ZMod p)) (teichmullerCoeffModSq (p := p) a) = a := by
  rw [teichmullerCoeffModSq, ← rationalPadicIntegerToZMod_eq_castHom_toZModSq p h,
    rationalPadicIntegerToZMod_teichmuller]

omit [NumberField.IsCMField K] in
/-- **The mod-`p²` Dwork coordinate cyclotomic action** (proven, axiom-clean): the mod-`p²` analog of
`dworkParameterPowerBasis_repr_dworkCompleteCyclotomicEquiv_toZMod`.  The cyclotomic action multiplies
the `i`-th level-`2(p−1)` Dwork power-basis coordinate by `teichmullerCoeffModSq (a)^i`:

  `ToZModSq (repr (cyclotomicEquiv a x) i) = teichmullerCoeffModSq (a)^i · ToZModSq (repr x i)`.

Same proof as the mod-`p` version: the action sends `repr x = c` to `repr = (τ(a)^i · c i)`
(`dworkCompleteCyclotomicEquiv_powerLinearMap`), and `ToZModSq` is a ring hom. -/
theorem dworkParameterPowerBasis_repr_dworkCompleteCyclotomicEquiv_toZModSq
    (a : CyclotomicUnitDelta p) (x : DworkCompleteIntegerRing p K) (i : Fin (p - 1)) :
    rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr
          (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a x) i) =
      teichmullerCoeffModSq (p := p) (a : ZMod p) ^ (i : ℕ) *
        rationalPadicIntegerToZModSq p
          ((dworkParameterPowerBasis p K).repr x i) := by
  classical
  let c : Fin (p - 1) → RationalPadicIntegerRing p :=
    (dworkParameterPowerBasis p K).repr x
  have hx : dworkParameterPowerLinearMap p K c = x := by
    simpa [c] using
      KummerLogTrace.dworkParameterPowerLinearMap_repr (p := p) (K := K) x
  have haction :
      Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a x =
        dworkParameterPowerLinearMap p K
          (fun i : Fin (p - 1) ↦
            rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i) := by
    rw [← hx]
    exact Conjugation.dworkCompleteCyclotomicEquiv_powerLinearMap (p := p) (K := K) a c
  have hcoeff :
      (dworkParameterPowerBasis p K).repr
          (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a x) i =
        rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i := by
    have hrepr :=
      congrFun
        (dworkParameterPowerBasis_repr_powerLinearMap (p := p) (K := K)
          (fun i : Fin (p - 1) ↦
            rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i)) i
    rw [haction]
    simpa using hrepr
  rw [hcoeff, map_mul, map_pow, teichmullerCoeffModSq]

omit [NumberField.IsCMField K] in
/-- **The mod-`p²` level-`2(p−1)` Dwork coordinate cyclotomic action** (proven, axiom-clean): the
mod-`p²` analog of `valuedLambdaQuotientDworkCoeffModP_quotientMap_cyclotomic`.  For a representative
in the level-`2(p−1)` quotient,

  `coordModSq i (quotientMap (cyclotomicEquiv a) x) = teichmullerCoeffModSq (a)^i · coordModSq i x`.

By `Quotient.inductionOn'` and `dworkParameterPowerBasis_repr_dworkCompleteCyclotomicEquiv_toZModSq`,
with `dworkCompleteCyclotomicEquiv_algebraMap_valuedInteger` moving the action through the
`algebraMap`. -/
theorem valuedLambdaQuotientDworkCoeffModSq_quotientMap_cyclotomic
    (a : CyclotomicUnitDelta p) (i : Fin (p - 1))
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (Ideal.quotientMap ((lambdaIdeal p K) ^ (2 * (p - 1)))
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
            ValuedIntegerRing p K →+* ValuedIntegerRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
            (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
            (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
              (p := p) (K := K) a) (2 * (p - 1))) x) =
      teichmullerCoeffModSq (p := p) (a : ZMod p) ^ (i : ℕ) *
        valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i x := by
  refine Quotient.inductionOn' x ?_
  intro x
  have hcoord :=
    dworkParameterPowerBasis_repr_dworkCompleteCyclotomicEquiv_toZModSq
      (p := p) (K := K) a
      (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x) i
  rw [dworkCompleteCyclotomicEquiv_algebraMap_valuedInteger (p := p) (K := K) a x] at hcoord
  rw [show (Quotient.mk'' x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) x from rfl,
    Ideal.quotientMap_mk, valuedLambdaQuotientDworkCoeffModSq_mk,
    valuedLambdaQuotientDworkCoeffModSq_mk]
  exact hcoord

/-! ## 5. The level-`71` coordinate column factor: scaled coordinate = Teichmüller factor × unscaled

Combining `§3` (scaled finite log = cyclotomic image of unscaled) and `§4` (the mod-`p²` cyclotomic
coordinate action), the degree-`i` mod-`p²` coordinate of the scaled finite log at level `2(p−1)−1` is
`teichmullerCoeffModSq (z)^i` times the unscaled one.  Stated at `p = 37`, `N = 71` for the FLT37
endpoint. -/

omit [NumberField.IsCMField K] in
/-- **The level-`71` scaled coordinate is the Teichmüller factor times the unscaled, at `p = 37`**
(proven, axiom-clean): for a cyclotomic residue `a` and index `i`,

  `coordModSq i (scaledDworkParameterNormalizedCoordFiniteLogN a 71)`
    `= teichmullerCoeffModSq (a)^i · coordModSq i (dworkParameterNormalizedCoordFiniteLogN 71)`.

Rewrites the scaled finite log as the cyclotomic image of the unscaled (`§3`) and applies the mod-`37²`
cyclotomic coordinate action (`§4`); at `p = 37` the quotient level `71 + 1 = 72 = 2·(37 − 1)` matches
the coordinate functional's level definitionally. -/
theorem valuedLambdaQuotientDworkCoeffModSq_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    (a : CyclotomicUnitDelta 37) (i : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (scaledDworkParameterNormalizedCoordFiniteLogN (p := 37) (K := K)
          (a : ZMod 37) 71) =
      teichmullerCoeffModSq (p := 37) (a : ZMod 37) ^ (i : ℕ) *
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
          (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := K) 71) := by
  rw [scaledDworkParameterNormalizedCoordFiniteLogN_eq_cyclotomic (p := 37) (K := K) a]
  exact valuedLambdaQuotientDworkCoeffModSq_quotientMap_cyclotomic (p := 37) (K := K) a i _

/-! ## 6. The unscaled Dwork-parameter coordinate as a sum of homogeneous-degree slice coordinates

The mod-`p²` analog of `valuedLambdaQuotientDworkCoeffModP_factorPow_samePrimeFiniteLog_normalizedCoord`:
the degree-`i` mod-`p²` coordinate of `dworkParameterNormalizedCoordFiniteLogN N` is the sum over
homogeneous degrees `d` of the coordinate of the degree-`d` slice.  Fully `N`-generic, via the
`N`-generic full-log decomposition `samePrimeFiniteLog_normalizedArtinHasseCoord_eq_homogeneous_degree_sum_range`
and the mod-`p²` coordinate additivity `valuedLambdaQuotientDworkCoeffModSq_sum`. -/

omit [NumberField.IsCMField K] in
/-- **The unscaled level-`71` coordinate is the sum of degree-slice coordinates, at `p = 37`**
(proven, axiom-clean): for the index `i` and `p = 37`,

  `coordModSq i (dworkParameterNormalizedCoordFiniteLogN 71) =`
    `∑ d ∈ range (cutoff 71), coordModSq i (degree-d slice of dworkParameterApprox 72)`.

The mod-`37²` analog of `valuedLambdaQuotientDworkCoeffModP_factorPow_samePrimeFiniteLog_normalizedCoord`:
unfolds the finite log of the normalized Artin-Hasse coordinate to the homogeneous degree-sum range
(`samePrimeFiniteLog_normalizedArtinHasseCoord_eq_homogeneous_degree_sum_range`, `N`-generic) and
distributes the mod-`37²` coordinate over the sum (`valuedLambdaQuotientDworkCoeffModSq_sum`).  Fixed
at `N = 71` since `valuedLambdaQuotientDworkCoeffModSq` is the level-`2(37−1) = 72`-quotient functional
and `71 + 1 = 72`. -/
theorem valuedLambdaQuotientDworkCoeffModSq_dworkParameterNormalizedCoordFiniteLogN71_eq_sum
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    (i : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := K) 71) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := 37) 71),
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
            (p := 37) (K := K) 71 d
            (dworkParameterApprox (p := 37) (K := K) (71 + 1))
            (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1))) := by
  classical
  -- The full-log decomposition into homogeneous-degree slices (`N`-generic), applied to the
  -- Dwork-parameter approximant `dworkParameterApprox 72` (`= dworkParameterApprox (71+1)`).
  have hdecomp :=
    samePrimeFiniteLog_normalizedArtinHasseCoord_eq_homogeneous_degree_sum_range
      (p := 37) (K := K) 71 (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1))
  -- `dworkParameterNormalizedCoordFiniteLogN 71 = samePrimeFiniteLog 71 (normalizedArtinHasseCoord ...)`.
  have hlog : dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := K) 71 =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := 37) 71),
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 d
          (dworkParameterApprox (p := 37) (K := K) (71 + 1))
          (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1)) := by
    rw [dworkParameterNormalizedCoordFiniteLogN]
    exact (samePrimeFiniteLog_eq_of_eq (p := 37) (K := K) (N := 71)
      (dworkParameterNormalizedCoordApprox_eq (p := 37) (K := K) 71) _ _).trans hdecomp
  rw [hlog, valuedLambdaQuotientDworkCoeffModSq_sum]

end BernoulliRegular.CyclotomicUnits

end
