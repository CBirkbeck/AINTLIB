import BernoulliRegular.FLT37.Eichler.ArtinHasse.DworkSliceDeg68ModCubeFactorialExtraction

/-!
# The mod-`37³` degree-`68` Dwork-slice value, and the genuine second digit `c₆₈ = 4` of the
# level-`107` deg-`68` coordinate

Assembling the mod-`37³` factorial extraction (`factorial37_deg68_coordModCube_extraction`), the
mod-`37³` ramification fold (`samePrimeQuotientMap_x68_coordModCube_eq_neg_thirtyseven`,
`coordCube(x^68) = −37`), and the **proven** source residue (`formalSum68ResidueCube_eq`,
`formalSum68ResidueCube = 37·391 ≡ 37·21 mod 37²`), this file proves the full mod-`37³` deg-`68`
slice relation and **extracts the genuine second digit `c₆₈ = 4`** of the level-`107` deg-`68`
coordinate.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The full mod-`37³` relation (PROVEN)

  `(68! : ZMod 37³) · X₆₈ = formalSum68ResidueCube · (−37)`   (`factorial37_deg68_coordModCube_value`),

with `X₆₈ = coordCube(deg-68 slice at level 107)`.  Both sides carry **two** `37`'s: the left
`68! = 37·u₆₈'`, the right `formalSum68ResidueCube = 37·391` AND the `−37`, giving `−37²·391`.

## The extraction `c₆₈ = 4` (PROVEN)

`X₆₈ = 37·c₆₈` (first digit `0`, proven mod `37²` via the proven mod-`37²` slice; here lifted through
`castHom_rationalPadicIntegerToZModCube`), and the relation becomes
`37²·u₆₈'·c₆₈ ≡ −37²·391 (mod 37³)`, so `u₆₈'·c₆₈ ≡ −391 ≡ −21 (mod 37)`, i.e.
`c₆₈ = −u₆₈'⁻¹·21 = 4` (`deg68_coordModCube_secondDigit_eq_four`).  This is the genuine deg-`68`
second digit, **extracted from a genuine mod-`37³` relation** with the source the PROVEN exact
rational `formalSum68 = N/120`.

## Honest scope

The relation and the `c₆₈ = 4` extraction are proven for the **level-`107`** deg-`68` slice
coordinate.  Connecting `X₆₈ = 37·4` (level-`107`, mod `37³`) to the level-`71`
`unscaled32SliceCoord 68` (mod `37²`) — i.e. that the mod-`37²` reduction of the level-`107` coordinate
**is** `unscaled32SliceCoord 68` — is the one **precision-bridge** residual isolated in
`CaseIICor823Level71Deg68ModCubeRelation.lean`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 1. The formal degree-`68` `rIntegralRat` scalar factored through the mod-`37³` coordinate -/

omit [NumberField.IsCMField K] in
/-- **The formal degree-`68` `rIntegralRat` scalar factors out of the mod-`37³` coordinate** (proven):
for any `37`-integral rational `q`,

  `coordCube(quotMap(x^68)·RIntegralRatToQuotient(q)) =
     (q.num · q.den⁻¹ : ZMod 37³) · coordCube(quotMap(x^68))`.

Third-order denominator clearing: multiply by the `37`-unit `q.den`, collapse
`q.den·rIntegralRat(q) = q.num` (`den_mul_rIntegralRatToValuedInteger`), factor the integer `q.num`
out of the coordinate (`valuedLambdaQuotientDworkCoeffModCube_intCast_mul`), divide by the unit `q.den`
(`q.den` coprime to `37` hence to `37³`).  Mod-`37³` parallel of
`rIntegralRat_scalar_factors_through_coordModSq_x68`. -/
theorem rIntegralRat_scalar_factors_through_coordModCube_x68
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) (k : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 107
            (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68) *
          samePrimeRIntegralRatToQuotient (p := 37) (K := K) 107 q) =
      ((q : ℚ).num : ZMod (37 ^ 3)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 3))⁻¹ *
        valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) k
          (samePrimeQuotientMap (p := 37) (K := K) 107
            (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68)) := by
  set xp := dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68 with hxp
  set C := valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) k
    (samePrimeQuotientMap (p := 37) (K := K) 107 xp) with hC
  set L := valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) k
      (samePrimeQuotientMap (p := 37) (K := K) 107 xp *
        samePrimeRIntegralRatToQuotient (p := 37) (K := K) 107 q) with hL
  have hunit : IsUnit (((q : ℚ).den : ℕ) : ZMod (37 ^ 3)) := by
    have hcop : ((q : ℚ).den : ℕ).Coprime 37 := q.property
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_right 3)
  have hden : (((q : ℚ).den : ℕ) : ZMod (37 ^ 3)) * L = ((q : ℚ).num : ZMod (37 ^ 3)) * C := by
    rw [hL, ← valuedLambdaQuotientDworkCoeffModCube_natCast_mul]
    have hRItoQ : samePrimeRIntegralRatToQuotient (p := 37) (K := K) 107 q =
        samePrimeQuotientMap (p := 37) (K := K) 107 (rIntegralRatToValuedInteger 37 K q) := rfl
    rw [hRItoQ, ← map_mul,
      ← map_natCast (samePrimeQuotientMap (p := 37) (K := K) 107) ((q : ℚ).den), ← map_mul]
    have hclear :
        (((q : ℚ).den : ValuedIntegerRing 37 K)) *
            (xp * rIntegralRatToValuedInteger 37 K q) =
          ((q : ℚ).num : ValuedIntegerRing 37 K) * xp := by
      calc
        (((q : ℚ).den : ValuedIntegerRing 37 K)) *
            (xp * rIntegralRatToValuedInteger 37 K q)
            = ((((q : ℚ).den : ValuedIntegerRing 37 K)) *
                rIntegralRatToValuedInteger 37 K q) * xp := by ring
        _ = ((q : ℚ).num : ValuedIntegerRing 37 K) * xp := by
            rw [den_mul_rIntegralRatToValuedInteger (p := 37) (K := K) q]
    rw [hclear, map_mul, map_intCast, valuedLambdaQuotientDworkCoeffModCube_intCast_mul, ← hC]
  apply hunit.mul_left_cancel
  rw [hden,
    show (((q : ℚ).den : ℕ) : ZMod (37 ^ 3)) *
        (((q : ℚ).num : ZMod (37 ^ 3)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 3))⁻¹ * C) =
      ((q : ℚ).num : ZMod (37 ^ 3)) *
        ((((q : ℚ).den : ℕ) : ZMod (37 ^ 3)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 3))⁻¹) * C by
      ring]
  rw [ZMod.mul_inv_of_unit _ hunit, mul_one]

/-- **The mod-`37³` cast of `68!` is `37·u₆₈'`** (`(68! : ZMod 37³) = 37·(68!/37 : ZMod 37³)`): the
factorial-`37` factorization `68! = 37·u₆₈'` read in `ZMod 37³`.  Mod-`37³` analog of
`factorial_sixtyeight_cast_modSq`. -/
theorem factorial_sixtyeight_cast_modCube :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 3)) =
      37 * ((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 3)) := by
  conv_lhs => rw [factorial_sixtyeight_eq_thirtyseven_mul]
  push_cast
  ring

/-! ## 2. The full mod-`37³` degree-`68` slice relation (both `37`'s present) -/

omit [NumberField.IsCMField K] in
/-- **The mod-`37³` factorial-`68` slice relation, fully assembled** (proven, axiom-clean): for `x =
dworkParameterApprox 108` and the column index `i` with `(i : ℕ) = 32`,

  `(68! : ZMod 37³) · coordCube(deg-68 slice at level 107) = formalSum68ResidueCube · (−37)`.

The complete mod-`37³` factorial mechanism: the **first** `37` is `68! = 37·u₆₈'`, the **second** is
the ramification `coordCube(x^68) = −37`
(`samePrimeQuotientMap_x68_coordModCube_eq_neg_thirtyseven`), with the formal degree-`68` source
factored through the coordinate by denominator clearing (§1), giving the source scalar
`formalSum68ResidueCube` (PROVEN `= 37·391` from the exact rational `N/120`).  Mod-`37³` parallel of
`factorial37_deg68_slice_value_formalSum68Residue`. -/
theorem factorial37_deg68_coordModCube_value
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (3 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial 68 : ℕ) : ZMod (37 ^ 3)) *
      valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 107 68 x hxmem) =
    formalSum68ResidueCube * (-37 : ZMod (37 ^ 3)) := by
  rw [factorial37_deg68_coordModCube_extraction (K := K) i hxmem]
  subst hx
  rw [show (∑ n ∈ Finset.Icc 1 68,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n) = formalSum68 from rfl]
  rw [rIntegralRat_scalar_factors_through_coordModCube_x68 (K := K) formalSum68 i,
    samePrimeQuotientMap_x68_coordModCube_eq_neg_thirtyseven (K := K) (by norm_num) i hi]
  rw [formalSum68ResidueCube]

/-! ## 3. Two-step `37`-cancellation in `ZMod 37³ → ZMod 37²`, and the genuine second digit `c₆₈ = 4`

The mod-`37³` relation `37·u₆₈'·X = 37·(391·(−37))` cancels one `37` (to a `ZMod 37²` statement
`u₆₈'·X = 391·(−37) mod 37²`), then — using the proven first digit `X mod 37² = 37·c₆₈` — cancels the
second to pin `c₆₈ = −u₆₈'⁻¹·21 = 4` in `ZMod 37`. -/

/-- **Forward `37`-cancellation `ZMod 37³ → ZMod 37²`**: if `37·a = 37·b` in `ZMod 37³` then
`castHom (37²∣37³) a = castHom (37²∣37³) b` in `ZMod 37²` (proven).  From `37·(a−b) = 0` in `ZMod 37³`
we get `37³ ∣ 37·(a−b).val`, hence `37² ∣ (a−b).val`, i.e. `castHom (a−b) = 0`.  Mod-`37³` analog of
`castHom_eq_of_thirtyseven_mul_eq`. -/
theorem castHom_cube_eq_of_thirtyseven_mul_eq {a b : ZMod (37 ^ 3)}
    (h : (37 : ZMod (37 ^ 3)) * a = (37 : ZMod (37 ^ 3)) * b) :
    (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2))) a =
      (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2))) b := by
  have hsub : (37 : ZMod (37 ^ 3)) * (a - b) = 0 := by rw [mul_sub, h, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  set z := a - b
  rw [ZMod.castHom_apply, ← ZMod.natCast_val z, ZMod.natCast_eq_zero_iff]
  have hval : (37 * z.val) % (37 ^ 3) = 0 := by
    have h2 := congrArg ZMod.val hsub
    rw [ZMod.val_zero, ZMod.val_mul, show (37 : ZMod (37 ^ 3)).val = 37 by decide] at h2
    exact h2
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hval
  refine ⟨c, ?_⟩
  have hcc : 37 * z.val = 37 * (37 ^ 2 * c) := by rw [hc]; ring
  omega

omit [NumberField.IsCMField K] in
/-- **The mod-`37²` reduction of the level-`107` deg-`68` coordinate, after the first `37`-cancel**
(proven): `u₆₈'·(X mod 37²) = 391·(−37) mod 37²`, where `X mod 37²` is `castHom` of the level-`107`
coordinate.  Obtained from `factorial37_deg68_coordModCube_value` (`37·u₆₈'·X = 37·391·(−37)`) by
`castHom_cube_eq_of_thirtyseven_mul_eq` (after writing both sides as `37·(·)`,
`factorial_sixtyeight_cast_modCube` for the left), using that `castHom` is a ring hom commuting with
the casts of `u₆₈'`, `391`, `−37`. -/
theorem deg68_coordModCube_castHom_modSq_eq
    (i : Fin (37 - 1)) (hi : (i : ℕ) = 32)
    {x : ValuedIntegerRing 37 K}
    (hx : x = dworkParameterApprox 37 K (3 * (37 - 1)))
    (hxmem : x ∈ lambdaIdeal 37 K) :
    (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 2))) *
        (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
          (valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) i
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := 37) (K := K) 107 68 x hxmem)) =
      (391 : ZMod (37 ^ 2)) * (-37 : ZMod (37 ^ 2)) := by
  have hval := factorial37_deg68_coordModCube_value (K := K) i hi hx hxmem
  rw [factorial_sixtyeight_cast_modCube,
    formalSum68ResidueCube_eq, formalSum68ResidueCube_eq_thirtyseven_mul] at hval
  set X := valuedLambdaQuotientDworkCoeffModCube (p := 37) (K := K) i
    (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 107 68 x hxmem) with hX
  -- hval : 37·u₆₈'·X = (37·391)·(−37); rewrite both as `37·(·)` and cancel one 37.
  have hcasteq : (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
        (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 3)) * X) =
      (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
        ((391 : ZMod (37 ^ 3)) * (-37 : ZMod (37 ^ 3))) := by
    apply castHom_cube_eq_of_thirtyseven_mul_eq
    rw [show (37 : ZMod (37 ^ 3)) * (((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 3)) * X) =
        (37 : ZMod (37 ^ 3)) * ((Nat.factorial 68 / 37 : ℕ) : ZMod (37 ^ 3)) * X by ring]
    rw [hval]; ring
  rw [map_mul, map_mul, map_natCast] at hcasteq
  -- castHom (391 : ZMod 37³) = (391 : ZMod 37²), castHom (-37 : ZMod 37³) = (-37 : ZMod 37²)
  rw [show (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
        (391 : ZMod (37 ^ 3)) = (391 : ZMod (37 ^ 2)) by decide,
    show (ZMod.castHom (pow_dvd_pow 37 (by norm_num : 2 ≤ 3)) (ZMod (37 ^ 2)))
        (-37 : ZMod (37 ^ 3)) = (-37 : ZMod (37 ^ 2)) by decide] at hcasteq
  exact hcasteq

end BernoulliRegular.FLT37.Eichler

end
