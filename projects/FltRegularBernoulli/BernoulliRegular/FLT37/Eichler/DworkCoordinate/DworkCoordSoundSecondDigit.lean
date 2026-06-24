import BernoulliRegular.FLT37.Eichler.DworkCoordinate.UnscaledCoordDeg32SliceDecomposition

/-!
# The SOUND level-`71` unit ↔ Dwork-slice coordinate bridge: the genuine `ρ₀ = (32!)⁻¹ + c₆₈` value,
# threaded correctly through both unscaled and scaled coordinates

This file builds the **sound** discharge of `CaseIICor823Level71SecondOrderPartValue37` (hence R4 and
the FLT37 endpoint) from the two genuine `p`-adic-`L` pieces, *avoiding* the over-stated piece-2 value
`37·(32!)⁻¹` that `CaseIICor823Level71DworkSpecializedReduction.lean` /
`CaseIICor823Level71UnitDworkCoordBridge.lean` carry.  It imports only; it does **not** modify any
existing file.  No `sorry`, no `axiom`.

## The soundness correction (the omitted degree-`68` second digit `c₆₈`)

`CaseIICor823Level71DworkSpecializedReduction.lean`'s `coordIdentity` (and the residual it discharges,
`CaseIICor823Level71UnitDworkCoordBridge37`, pinning `ρ = −(32!)⁻¹`) use the **over-stated** unscaled
degree-`32` coordinate value `coordModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71) = 37·(32!)⁻¹`.
But `CaseIICor823Level71DworkSpecializedSound.lean` proves that the genuine unscaled coordinate is

  `coordModSq 32 (unscaled) = 37·((32!)⁻¹ + c₆₈)`,

where `c₆₈ ∈ ZMod 37` is the degree-`68` homogeneous slice's second digit (the Kellner `α₁` content):
the `deg-`32`` slice contributes `37·(32!)⁻¹` (`deg32SliceCoordModSq37_eq`, proven) **and** the `deg-`68``
slice contributes `37·c₆₈` (`unscaled32SliceCoord_sixtyeight_castHom_eq_zero`, proven mod-`37` value `0`
but generally nonzero second digit).  So the pinned `ρ = −(32!)⁻¹` is **wrong**; the genuine
`ρ = −((32!)⁻¹ + c₆₈) = −ρ₀`.

Crucially, the FLT37 endpoint (`CaseIICor823Level71SecondOrderPartValue37`, the `M ≤ 1`
non-degeneracy) needs **only** `ρ ≠ 0`, *not* a numeral.  So this file targets that **sound**
existential, supplying the genuine `ρ = −ρ₀` (with `ρ₀ = (32!)⁻¹ + c₆₈` the genuine second digit of
the unscaled coordinate), proven nonzero from the sound non-degeneracy residual
`CaseIICor823Level71Unscaled32Coord37` (`ρ₀ ≠ 0`, `CaseIICor823Level71DworkSpecializedSound.lean`).

## The genuine remaining content, split into TWO honest pieces

After this file, `CaseIICor823Level71SecondOrderPartValue37` rests on exactly:

1. **`CaseIICor823Level71UnitFiniteLogIdentity37`** (defined here): the level-`71` unit ↔
   Dwork-specialized finite-log identity — `samePrimeFiniteLog 71 (c^{p-1} − 1) = unscaled − scaled`
   — the level-`71` lift of the proven `p − 2`-precise
   `kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs` applied to the **unit**
   `c^{p-1} − 1`.  This is the genuine **second-order Fermat-quotient** content (the first-order Fermat
   congruence `c^p ≡ c (mod p)` is valid only at precision `p − 1`).  It is *exactly* piece 1 of the
   existing `CaseIICor823Level71DworkSpecializedFiniteLog37`, stated alone.

2. **`CaseIICor823Level71Unscaled32Coord37`** (from `CaseIICor823Level71DworkSpecializedSound.lean`):
   the **sound** non-degeneracy `∃ ρ₀ ≠ 0, coordModSq 32 (unscaled) = 37·ρ₀.val`, where
   `ρ₀ = (32!)⁻¹ + c₆₈`.  This is the genuine `v_p(L₃₇(1, ω³²)) = 1` / Washington Proposition 8.12
   content: that the second `37`-adic digit of the unscaled Dwork coordinate of the cyclotomic-unit
   log is nonzero.

**Honest soundness note on the bridge `v_p(L) = 1 ⟹ ρ₀ ≠ 0`.**  The proven `v₃₇(L₃₇(1, ω³²)) = 1`
(`bernoulliGenOmegaValuationTwo37_proved`, `caseII_cor823_valuation_input_proven`) gives the **sharp
Bernoulli valuation** `v₃₇(B₃₂/32) = 1` — the *analytic* `L`-value is a first-order zero.  Piece 2's
`ρ₀ = (32!)⁻¹ + c₆₈` is the **second digit of the Dwork coordinate of the cyclotomic-unit logarithm**,
a *different normalization* (related to `B₃₂/32` and `B₆₈/68` through Washington Proposition 8.12's
single-unit `p`-adic-log valuation `v_p(log_p E_i^{(N)}) = i/(p−1) + v_p(L_p(1, ω^i))`).  The `37·`
structure (the first digit `= 0`) is proven *unconditionally* (`genericColumnCoordLHS37_castHom_eq_zero`),
**not** via `v_p(L)`; the non-degeneracy `ρ₀ ≠ 0` (the `unit` factor) is the genuine Proposition 8.12
content that the repo's first-order Kummer-determinant infrastructure does *not* supply
(cf. `CaseIICor823SecondOrder.lean`).  So `v_p(L) = 1` is the *motivation and analytic certificate* for
`ρ₀ ≠ 0`, but the formal bridge from the analytic valuation to the Dwork-coordinate second digit is
itself Proposition 8.12 — left as the explicit hypothesis `CaseIICor823Level71Unscaled32Coord37`.

## What this file fixes vs the existing chain

The existing `caseIICor823Level71DworkSpecializedFiniteLog37_coordIdentity` threads the over-stated
`37·(32!)⁻¹` into *both* the unscaled and (via the Teichmüller factor) the scaled coordinate — but
because it pins the unscaled value to `37·(32!)⁻¹` rather than the genuine `37·ρ₀.val`, it omits the
`c₆₈` digit.  Here we keep the unscaled coordinate **abstract** (`= 37·ρ₀.val` from the sound residual)
and let the *same* `ρ₀` flow into the scaled coordinate through the proven Teichmüller column factor,
so the difference is `(1 − τ(k)³²)·37·ρ₀.val` with the genuine `ρ₀` preserved — the sound value
`ρ = −ρ₀`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The level-`71` unit ↔ Dwork-specialized finite-log identity (piece 1, stated alone)

This is *exactly* piece 1 of the existing `CaseIICor823Level71DworkSpecializedFiniteLog37`, isolated
as its own `def … : Prop`.  Unlike the bundled residual, it carries **no** numeric coordinate value
(it is purely the finite-log substitution identity), so it cannot over-state the unscaled coordinate;
the coordinate value comes *only* from the sound `CaseIICor823Level71Unscaled32Coord37`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` unit ↔ Dwork-specialized finite-log identity** (a `def … : Prop`, **not** an
axiom — the genuine second-order Fermat-quotient `p`-adic-`L` kernel).

For every cyclotomic column `a`, the level-`71` finite logarithm of the normalized real cyclotomic
unit `c^{p-1} − 1` (where `c = kummerLogValuedCyclotomicQuotientDenUnit a`) equals the
unscaled-minus-scaled Dwork-parameter difference:

  `samePrimeFiniteLog 71 (c^{p-1} − 1) = dworkParameterNormalizedCoordFiniteLogN 71 −`
    `scaledDworkParameterNormalizedCoordFiniteLogN (kummerLogColumnDelta a) 71`.

This is **piece 1** of `CaseIICor823Level71DworkSpecializedFiniteLog37`
(`CaseIICor823Level71DworkSpecializedReduction.lean`), stated *alone* (without the over-stated piece-2
value `37·(32!)⁻¹`).  It is the level-`71` lift of the proven `p − 2`-precise
`kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs` applied to the **unit**
`c^{p-1} − 1`, combining the level-`71` unit ↔ quotient Fermat bridge with the level-`71` Dwork ↔
quotient Teichmüller transport (the Teichmüller difference `τ(k) − k` vanishes only to order `p − 1`,
so the proven `p − 2`-precise `_evalₐ_pow_pred` does not lift — this is the genuine `v_p(L₃₇(1, ω³²)) =
1` second-order Fermat-quotient content). -/
def CaseIICor823Level71UnitFiniteLogIdentity37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ a : Fin (kummerLogRank 37),
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) 71
        ((kummerLogValuedCyclotomicQuotientDenUnit
          (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a :
            ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ (37 - 1) - 1)
        (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
          (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a) =
      dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71 -
        scaledDworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ)
          ((kummerLogColumnDelta (p := 37) (by norm_num) a : CyclotomicUnitDelta 37) : ZMod 37) 71

open BernoulliRegular (CPlusGenerator) in
/-- **Piece 1 of the bundled residual is exactly `CaseIICor823Level71UnitFiniteLogIdentity37`**
(proven, by definitional projection): if the bundled
`CaseIICor823Level71DworkSpecializedFiniteLog37` holds, then so does its piece-1 finite-log identity
in isolation.  Records that the sound finite-log kernel isolated here is genuinely the analytic half
of the existing residual (not a different statement). -/
theorem caseIICor823Level71UnitFiniteLogIdentity37_of_dworkSpecialized
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hRes : CaseIICor823Level71DworkSpecializedFiniteLog37) :
    CaseIICor823Level71UnitFiniteLogIdentity37 :=
  hRes.1

/-! ## 2. The sound coordinate identity: `W(a) = (1 − τ(k)³²)·(37·ρ₀.val)` with the genuine `ρ₀`

The level-`71` finite-log coordinate `W(a) = normalizedUnitCoeff37 a` of the unit `c^{p-1} − 1`,
computed from the finite-log identity (piece 1) and the sound unscaled coordinate value `37·ρ₀.val`
(`CaseIICor823Level71Unscaled32Coord37`, the genuine `ρ₀ = (32!)⁻¹ + c₆₈`), threading the **same**
`ρ₀` into the scaled coordinate through the proven Teichmüller column factor.  This is the sound
replacement for `caseIICor823Level71DworkSpecializedFiniteLog37_coordIdentity` (which over-states the
unscaled value as `37·(32!)⁻¹`, dropping `c₆₈`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The sound mod-`37²` coordinate identity** (proven, axiom-clean given the finite-log identity and
the sound unscaled coordinate value): if piece 1 (`CaseIICor823Level71UnitFiniteLogIdentity37`) holds
and the unscaled `varpi^{32}` coordinate is `37·ρ₀.val` (the sound non-degeneracy datum), then for
every column `a`

  `normalizedUnitCoeff37 a = (1 − ((a+2 : ZMod 37²))³²)·(37·ρ₀.val)`.

The coordinate structure is **discharged** from the proven `N`-generic machinery: `W(a)` is the
finite-log coordinate of `c^{p-1} − 1` (`normalizedUnitCoeff37_eq_finiteLog_denUnit`), piece 1
rewrites the finite log as the unscaled-minus-scaled Dwork difference, the mod-`37²` coordinate
distributes (`valuedLambdaQuotientDworkCoeffModSq_sub`), the scaled coordinate is the Teichmüller
factor times the **same** unscaled coordinate
(`…_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul`), the unscaled coordinate is the sound
`37·ρ₀.val`, and the Teichmüller factor `τ(k)³²` collapses mod-`37` to the rational `k³² = (a+2)³²`
under the `37·` factor (`teichmullerCoeffModSq_castHom`, `thirtyseven_mul_eq_of_castHom_eq`).  Unlike
the existing `coordIdentity`, the unscaled value is kept abstract as `37·ρ₀.val`, so `ρ₀` (with `c₆₈`
folded in) flows correctly into both coordinates — the sound value. -/
theorem caseIICor823Level71SoundCoordIdentity
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLog : CaseIICor823Level71UnitFiniteLogIdentity37)
    {ρ₀ : ZMod 37}
    (hUnscaled :
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
          (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71) =
        (37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2)))
    (a : Fin (kummerLogRank 37)) :
    normalizedUnitCoeff37 a =
      (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
        ((37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2))) := by
  set i : Fin (37 - 1) :=
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 with hi_def
  have hi32 : (i : ℕ) = 32 := rfl
  set δ : CyclotomicUnitDelta 37 := kummerLogColumnDelta (p := 37) (by norm_num) a with hδ_def
  -- `W(a)` is the coordinate of the finite log of the unit `c^{p-1} − 1`.
  rw [normalizedUnitCoeff37_eq_finiteLog_denUnit a]
  -- Rewrite the finite log as the unscaled-minus-scaled Dwork difference (piece 1).
  rw [hLog a]
  -- Distribute the mod-`37²` coordinate over the difference.
  rw [valuedLambdaQuotientDworkCoeffModSq_sub]
  -- The scaled coordinate is the Teichmüller factor times the unscaled (proven column factor).
  rw [show ((kummerLogColumnDelta (p := 37) (by norm_num) a : CyclotomicUnitDelta 37) : ZMod 37) =
      (δ : ZMod 37) from rfl,
    valuedLambdaQuotientDworkCoeffModSq_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul
      (K := CyclotomicField 37 ℚ) δ i]
  -- The unscaled degree-`32` coordinate is the sound `37·ρ₀.val`.
  rw [hUnscaled]
  -- Now: `37·ρ₀.val − τ(k)³²·(37·ρ₀.val) = (1 − τ(k)³²)·(37·ρ₀.val) = 37·((1 − τ(k)³²)·ρ₀.val)`.
  rw [show (37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2)) -
        teichmullerCoeffModSq (p := 37) (δ : ZMod 37) ^ (i : ℕ) *
          ((37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2))) =
      (37 : ZMod (37 ^ 2)) *
        ((1 - teichmullerCoeffModSq (p := 37) (δ : ZMod 37) ^ (i : ℕ)) *
          ((ρ₀.val : ℕ) : ZMod (37 ^ 2))) by ring]
  rw [show (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
        ((37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2))) =
      (37 : ZMod (37 ^ 2)) *
        ((1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
          ((ρ₀.val : ℕ) : ZMod (37 ^ 2))) by ring]
  apply thirtyseven_mul_eq_of_castHom_eq
  -- mod-`37`: reduce both factors; only `castHom (τ(k)³²) = castHom ((a+2)³²)` is nontrivial.
  have hδval : (δ : ZMod 37) = (((a : ℕ) + 2 : ℕ) : ZMod 37) := by
    rw [hδ_def, kummerLogColumnDelta_val,
      kummerLogColumnIndex_eq_CPlusGeneratorIndex (p := 37) (by norm_num) a]
  have hTf : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
      (teichmullerCoeffModSq (p := 37) (δ : ZMod 37) ^ (i : ℕ)) =
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32) := by
    rw [map_pow, map_pow, hi32,
      teichmullerCoeffModSq_castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (δ : ZMod 37), hδval,
      map_natCast]
  simp only [map_mul, map_sub, map_one, hTf]

/-! ## 3. The sound second-order part value: `secondOrderPart37 a = (−ρ₀)·V̄(a)`, `−ρ₀ ≠ 0`

From the sound coordinate identity (`W(a) = 37·((1 − k³²)·ρ₀.val)`) and the proven `37·` structure,
`secondOrderPart37 a = castHom((1 − k³²)·ρ₀.val) = (1 − k³²)·ρ₀ = (−V̄(a))·ρ₀ = (−ρ₀)·V̄(a)`.  The sound
leading coefficient is `ρ = −ρ₀`, **nonzero** because the non-degeneracy residual gives `ρ₀ ≠ 0`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The sound second-order-part value identity** (proven, axiom-clean given the finite-log identity
and the sound non-degeneracy): if piece 1 holds and `coordModSq 32 (unscaled) = 37·ρ₀.val`, then for
every column `a`

  `secondOrderPart37 a = (−ρ₀) · vandermondeFactorModP37 a`  (in `ZMod 37`).

By `caseIICor823Level71SoundCoordIdentity`, `W(a) = 37·((1 − k³²)·ρ₀.val)`, so the proven `37·`
structure (`secondOrderPart37_eq_castHom_of_eq_thirtyseven_mul`) gives `secondOrderPart37 a =
castHom((1 − k³²)·ρ₀.val) = castHom(1 − k³²)·ρ₀`.  Evaluating `castHom(1 − k³²_modSq) = −V̄(a)`
(`column_pow_thirtytwo_castHom`) and `castHom(ρ₀.val_modSq) = ρ₀` (`ZMod.natCast_val`,
`ZMod.cast_id`) yields `(−V̄(a))·ρ₀ = (−ρ₀)·V̄(a)`.  This is the genuine value with `c₆₈` folded into
`ρ₀` — **not** the over-pinned `−(32!)⁻¹`. -/
theorem caseIICor823Level71SoundSecondOrderPartValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLog : CaseIICor823Level71UnitFiniteLogIdentity37)
    {ρ₀ : ZMod 37}
    (hUnscaled :
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
          (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71) =
        (37 : ZMod (37 ^ 2)) * ((ρ₀.val : ℕ) : ZMod (37 ^ 2)))
    (a : Fin (kummerLogRank 37)) :
    secondOrderPart37 a = (-ρ₀) * vandermondeFactorModP37 a := by
  -- `W(a) = 37·X` with `X = (1 − k³²)·ρ₀.val`.
  have hW : normalizedUnitCoeff37 a =
      (37 : ZMod (37 ^ 2)) *
        ((1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
          ((ρ₀.val : ℕ) : ZMod (37 ^ 2))) := by
    rw [caseIICor823Level71SoundCoordIdentity hLog hUnscaled a]; ring
  rw [secondOrderPart37_eq_castHom_of_eq_thirtyseven_mul a hW]
  -- `castHom X = castHom(1 − k³²)·castHom(ρ₀.val) = (−V̄(a))·ρ₀`.
  rw [map_mul]
  have hcol : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
      (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) = -vandermondeFactorModP37 a := by
    have h := column_pow_thirtytwo_castHom a
    rw [map_sub, map_one] at h ⊢
    rw [show (1 : ZMod 37) - (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) =
        -((ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) - 1) by ring]
    rw [h]
  have hρ₀ : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
      (((ρ₀.val : ℕ) : ZMod (37 ^ 2))) = ρ₀ := by
    rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  rw [hcol, hρ₀]
  ring

/-! ## 4. The sound discharge of `CaseIICor823Level71SecondOrderPartValue37`

Combining the finite-log identity (piece 1) with the sound non-degeneracy residual
`CaseIICor823Level71Unscaled32Coord37` (`∃ ρ₀ ≠ 0`, `CaseIICor823Level71DworkSpecializedSound.lean`),
the sound second-order-part value identity gives `CaseIICor823Level71SecondOrderPartValue37` with the
genuine nonzero `ρ = −ρ₀`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level71SecondOrderPartValue37` from the sound pieces** (proven, axiom-clean given
the level-`71` unit↔Dwork finite-log identity and the sound non-degeneracy
`CaseIICor823Level71Unscaled32Coord37`).

Destructure the sound non-degeneracy residual for the genuine nonzero `ρ₀` (`ρ₀ = (32!)⁻¹ + c₆₈ ≠ 0`)
and its unscaled coordinate value `37·ρ₀.val`; supply `ρ = −ρ₀` (nonzero since `ρ₀ ≠ 0`) and the
per-column identity `caseIICor823Level71SoundSecondOrderPartValue`.  This is the **sound** discharge —
it threads `ρ₀` (with `c₆₈`) correctly, avoiding the over-stated `37·(32!)⁻¹` of
`caseIICor823Level71DworkSpecializedFiniteLog37_coordIdentity`. -/
theorem caseIICor823Level71SecondOrderPartValue37_of_soundPieces
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLog : CaseIICor823Level71UnitFiniteLogIdentity37)
    (hNonDeg : CaseIICor823Level71Unscaled32Coord37) :
    CaseIICor823Level71SecondOrderPartValue37 := by
  obtain ⟨ρ₀, hρ₀_ne, hUnscaled⟩ := hNonDeg
  exact ⟨-ρ₀, neg_ne_zero.mpr hρ₀_ne,
    fun a ↦ caseIICor823Level71SoundSecondOrderPartValue hLog hUnscaled a⟩

/-! ## 5. R4 and the FLT37 endpoint, from the two sound pieces -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the two sound pieces** (proven,
axiom-clean given the level-`71` unit↔Dwork finite-log identity and the sound non-degeneracy).

Composes `caseIICor823Level71SecondOrderPartValue37_of_soundPieces` with the proven
`cor823PthPowerOfRationalModSq37_of_level71LeadingCoeff`-chain through
`caseIICor823Level71NormalizedUnitCoeff37_of_secondOrderPartValue`. -/
theorem cor823PthPowerOfRationalModSq37_of_soundPieces
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLog : CaseIICor823Level71UnitFiniteLogIdentity37)
    (hNonDeg : CaseIICor823Level71Unscaled32Coord37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_omega32Collapse
    (cor823Omega32SecondOrderCollapse37_of_genericColumnCoord
      (caseIICor823GenericColumnCoord37_of_level72LeadingCoeff
        (caseIICor823Level72LeadingCoeff37_of_normalizedUnitCoeff
          (caseIICor823Level71NormalizedUnitCoeff37_of_secondOrderPartValue
            (caseIICor823Level71SecondOrderPartValue37_of_soundPieces hLog hNonDeg)))))

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the TWO SOUND pieces** (proven, axiom-clean
given the genuine residuals + the carried Kellner Prop).

`R4` (Washington Proposition 8.12 at `i = 32`) reduced to exactly:

* `CaseIICor823Level71UnitFiniteLogIdentity37` — the level-`71` unit↔Dwork-specialized finite-log
  identity (the genuine second-order Fermat-quotient content, piece 1 of the existing
  `CaseIICor823Level71DworkSpecializedFiniteLog37`, stated alone);
* `CaseIICor823Level71Unscaled32Coord37` — the **sound** non-degeneracy `∃ ρ₀ ≠ 0,
  coordModSq 32 (unscaled) = 37·ρ₀.val` (`ρ₀ = (32!)⁻¹ + c₆₈`, the genuine second digit of the
  Dwork coordinate of the cyclotomic-unit log — the Washington Proposition 8.12 content).

The entire coordinate structure — the `37·(...)` first-digit vanishing (proven *unconditionally*,
not via `v_p(L)`), the cyclotomic Teichmüller column factor, the slice-sum decomposition, the
deg-`32` slice value, the deg-`68` slice mod-`37` vanishing — is **proven** from the `N`-generic
machinery; the genuine `c₆₈` second digit is folded into `ρ₀` (so this is the *sound* discharge, not
the over-stated `37·(32!)⁻¹`).  Discharging these two leaves FLT37 on R2 (the descent) + Kellner
alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_soundPieces
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_nonDeg : CaseIICor823Level71Unscaled32Coord37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71SecondOrderPartValue37_of_soundPieces caseII_finiteLogIdentity caseII_nonDeg)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
