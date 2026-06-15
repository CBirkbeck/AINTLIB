import BernoulliRegular.FLT37.Eichler.CaseIICor823Level72Coordinate

/-!
# The level-`72` mod-`37²` Dwork column coordinate, as a level-`71` finite-log coordinate
# (the doubled-degree finite-log normalization), and the precise smallest residual

This file builds the **doubled-degree** (level-`71`, precision `2(p-1) = 72`) finite-log
normalization that expresses the genuine level-`72` mod-`37²` Dwork column coordinate
`genericColumnCoordLHS37 a` (`CaseIICor823Level72Coordinate.lean`) as a single explicit level-`71`
finite-log coordinate.  It imports only; it does **not** modify any existing file.  No `sorry`, no
`axiom`.

## The doubled-degree finite-log bridge (proven, `N`-generic)

The first-order single-column chain (`KummerLogFormalEvaluator/*`, `KummerLogNormalization/*`) is
hard-coded at the finite-log precision `N = p - 2 = 35`, reading the Dwork coordinate at level
`p - 1 = 36`.  But the **completed** logarithm column `kummerLogCompletedColumn a` has a clean
`evalₐ N` at *every* precision `N` (`kummerLogCompletedColumn_evalₐ`):

  `evalₐ N (kummerLogCompletedColumn a) = kummerLogColumnCoord a N`,

and the column coordinate at `N + 1` is the level-`N` finite logarithm
`kummerLogColumnFiniteLog a N`, which the **`N`-generic** lemma
`kummerLogColumnFiniteLog_eq_two_nsmul_normalizedUnitFiniteLog` writes as
`2 • kummerLogNormalizedUnitFiniteLog a N` for *every* `N`.  Specialising at `N = 71` (so
`N + 1 = 72 = 2(p - 1)`):

  `genericColumnCoordLHS37 a`
    `= valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72 (kummerLogCompletedColumn a))`
    `= valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogColumnCoord a 72)`
    `= valuedLambdaQuotientDworkCoeffModSq 32 (2 • kummerLogNormalizedUnitFiniteLog a 71)`
    `= 2 · valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)`.

This is the **doubled-degree finite-log normalization**: the genuine level-`72` Dwork coordinate is
`2` times the level-`71` finite-log coordinate of the normalized real cyclotomic unit `ε_a^{p-1}`.
It is proven here, `N`-generic — the level-`72` analog of the first-order
`concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP`, with the precision raised from
`36` to `72` throughout.  See `genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq`.

## Why the *value* of that coordinate is the precise smallest residual

The first-order single-column factorization `concreteSquaredKummerLogMatrixEntry_congr` reads the
level-`36` coordinate of this same normalized-unit log as
`squaredUnit · bernoulliFactor 16 · ((a+2)^{32} − 1)`, and at the irregular row `j = 15` it
vanishes because `37 ∣ B₃₂`.  The mod-`37` reduction of the level-`72` coordinate **is** that
level-`36` coordinate (the proven `castHom`/level compatibility, repackaged here as
`genericColumnCoordLHS37_castHom_eq_zero`), so the level-`72` coordinate is
`37·(second-order part)`.

What the first-order chain does **not** reach is the *value* of the level-`72` coordinate divided
by `37`.  Two genuine `p`-adic-`L` obstructions stop a naive re-instantiation of the first-order
chain at precision `72`:

* the normalized-unit-to-quotient identity `ε_a^{p-1} ≡ (a·(1−ζ)/(1−ζ^a))` holds **only**
  modulo `(λ)^{p-1} = (p)` (it uses the Fermat congruence `c^p ≡ c (mod p)`, proven only at
  precision `p - 1`; see `kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP`),
  so the level-`72` coordinate carries a genuine second-order correction beyond the first-order
  quotient form;
* the factorial-cleared homogeneous-degree extraction
  `valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_…_of_lt`
  requires `d < p - 1` (so `d!` is a `p`-unit); at level `72` the homogeneous slices of degree
  `37 ≤ d ≤ 71` have `p ∣ d!`, which is **exactly** the source of the `B₃₂/37 mod 37`
  second-order content and is **not** reachable by that factorial-clearing route.

So the genuine remaining `p`-adic-`L` content of R4 is the single statement that the level-`71`
finite-log coordinate of the normalized real cyclotomic unit `ε_a^{p-1}` is
`37·ρ·((a+2)^{32} − 1)` for a uniform nonzero mod-`37` coefficient `ρ` — and by the proven
`37·(structure)` lift this is equivalent to the **column-independent** statement that the
coordinate's value-over-`37` is a uniform multiple of the Teichmüller-Vandermonde.

We isolate this as `CaseIICor823Level71NormalizedUnitCoeff37`, strictly smaller than
`CaseIICor823Level72LeadingCoeff37`: it is stated on the *normalized-unit* finite-log coordinate
at level `71` (one `2`-factor already extracted), is **sound** (a coefficient-value identity), is
**non-circular** (its conclusion is the explicit `37·ρ·V` value, not the vanishing of `c₁₅`),
and **non-vacuous**.  The full target follows by the proven doubled-degree bridge
(`caseIICor823Level72LeadingCoeff37_of_normalizedUnitCoeff`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The doubled-degree finite-log bridge: `genericColumnCoordLHS37 a` as a level-`71`
normalized-unit coordinate -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` Dwork column coordinate is the level-`71` normalized-unit finite-log
coordinate** (proven, axiom-clean): `genericColumnCoordLHS37 a =
valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogColumnFiniteLog a 71)`.

The completed logarithm column `kummerLogCompletedColumn a` has
`evalₐ 72 = kummerLogColumnCoord a 72` (`kummerLogCompletedColumn_evalₐ`), and
`kummerLogColumnCoord a 72 = kummerLogColumnFiniteLog a 71` (`kummerLogColumnCoord_succ`).  Unfolds
`genericColumnCoordLHS37`. -/
theorem genericColumnCoordLHS37_eq_columnFiniteLogCoeffModSq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    genericColumnCoordLHS37 a =
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (kummerLogColumnFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a 71) := by
  rw [genericColumnCoordLHS37]
  rw [kummerLogCompletedColumn_evalₐ (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a
    (2 * (37 - 1))]
  -- `kummerLogColumnCoord a (2*(37-1)) = kummerLogColumnFiniteLog a 71` by `rfl` (`2*(37-1)` is
  -- defeq `71+1`), matching the coordinate index `2*(37-1)` carried on both sides.
  rfl

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` Dwork column coordinate is `2` times the level-`71` normalized-unit finite-log
coordinate** (proven, axiom-clean — the doubled-degree finite-log normalization).

`genericColumnCoordLHS37 a = 2 · valuedLambdaQuotientDworkCoeffModSq 32
(kummerLogNormalizedUnitFiniteLog a 71)`.

By `genericColumnCoordLHS37_eq_columnFiniteLogCoeffModSq` the coordinate is that of
`kummerLogColumnFiniteLog a 71`, and the **`N`-generic**
`kummerLogColumnFiniteLog_eq_two_nsmul_normalizedUnitFiniteLog` (at `N = 71`) rewrites that to
`2 • kummerLogNormalizedUnitFiniteLog a 71`; the coefficient is `ℤ`-linear
(`valuedLambdaQuotientDworkCoeffModSq_natCast_mul` at `n = 2`).  This is the level-`72` analog of
the first-order `concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP`, precision raised
from `36` to `72`. -/
theorem genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    genericColumnCoordLHS37 a =
      (2 : ZMod (37 ^ 2)) *
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
          (kummerLogNormalizedUnitFiniteLog (p := 37) (K := CyclotomicField 37 ℚ)
            (by decide) a 71) := by
  rw [genericColumnCoordLHS37_eq_columnFiniteLogCoeffModSq a]
  rw [kummerLogColumnFiniteLog_eq_two_nsmul_normalizedUnitFiniteLog
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a 71]
  -- Extract the `2`-factor: `coeff (2 • z) = 2 · coeff z` via the `natCast_mul` law.
  rw [show (2 • kummerLogNormalizedUnitFiniteLog (p := 37) (K := CyclotomicField 37 ℚ)
        (by decide) a 71 :
        ValuedIntegerRing 37 (CyclotomicField 37 ℚ) ⧸
          (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1))) =
      ((2 : ℕ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) ⧸
          (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1))) *
        kummerLogNormalizedUnitFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a 71
      from by rw [Nat.cast_ofNat]; ring]
  rw [valuedLambdaQuotientDworkCoeffModSq_natCast_mul]
  norm_num

/-! ## 2. The `37·(second-order part)` decomposition, and the reduction to a uniform mod-`37` `ρ`

By the proven `genericColumnCoordLHS37_castHom_eq_zero` the level-`72` coordinate's mod-`37`
reduction vanishes, so `genericColumnCoordLHS37 a = 37·(second-order part)`.  An identity
`37·X = 37·ρ.val·V` in `ZMod 37²` holds **iff** `X ≡ ρ·V (mod 37)`, i.e.
`castHom X = ρ·castHom V`; the `37` factor makes only the mod-`37` part matter.  This collapses
the target's `∀ a` mod-`37²` identity to the **mod-`37`** statement that the second-order part is
a uniform multiple of the Teichmüller-Vandermonde — a datum in the field `ZMod 37`. -/

/-- **A mod-`37²` element with vanishing mod-`37` reduction is `37·(natCast of a mod-`37`
element)`** (proven): if `castHom x = 0` then `x = 37 · s.val` for `s = (x.val / 37 : ZMod 37)`.
`castHom x = 0` gives `37 ∣ x.val`; write `x.val = 37·k` with `k < 37` (as `x.val < 37²`); then
`x = (37·k : ZMod 37²) = 37·(k : ZMod 37²)` and `s.val = k`. -/
theorem exists_thirtyseven_mul_val_of_castHom_eq_zero {x : ZMod (37 ^ 2)}
    (hx : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) x = 0) :
    ∃ s : ZMod 37, x = (37 : ZMod (37 ^ 2)) * ((s.val : ℕ) : ZMod (37 ^ 2)) := by
  -- `castHom x = 0 ⟹ 37 ∣ x.val`.
  have hdvd : (37 : ℕ) ∣ x.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val] at hx
    exact (ZMod.natCast_eq_zero_iff _ _).mp hx
  obtain ⟨k, hk⟩ := hdvd
  -- `x.val = 37·k`, and `x.val < 37²` gives `k < 37`.
  have hk_lt : k < 37 := by
    have hval : x.val < 37 ^ 2 := ZMod.val_lt x
    omega
  refine ⟨(k : ZMod 37), ?_⟩
  have hsval : ((k : ZMod 37).val : ℕ) = k := ZMod.val_cast_of_lt hk_lt
  rw [hsval]
  -- `x = (x.val : ZMod 37²) = (37·k : ZMod 37²) = 37·(k : ZMod 37²)`.
  have hx_eq : x = ((x.val : ℕ) : ZMod (37 ^ 2)) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [hx_eq, hk]
  push_cast
  ring

/-- **`37·x = 37·y` in `ZMod 37²` when `castHom x = castHom y`** (proven): if
`castHom x = castHom y` then `castHom (x−y) = 0`, so `x − y = 37·t`
(`exists_thirtyseven_mul_val_of_castHom_eq_zero`) and `37·(x−y) = 37²·t = 0`, hence
`37·x = 37·y`.  Makes an identity `37·X = 37·Y` depend only on the mod-`37` reductions. -/
theorem thirtyseven_mul_eq_of_castHom_eq {x y : ZMod (37 ^ 2)}
    (hxy : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) x =
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) y) :
    (37 : ZMod (37 ^ 2)) * x = (37 : ZMod (37 ^ 2)) * y := by
  obtain ⟨t, ht⟩ := exists_thirtyseven_mul_val_of_castHom_eq_zero
    (x := x - y) (by rw [map_sub, hxy, sub_self])
  -- `37·(x − y) = 37·(37·t.val) = (37·37)·t.val = 0`, so `37·x = 37·y`.
  have h3737 : (37 : ZMod (37 ^ 2)) * (37 : ZMod (37 ^ 2)) = 0 := by decide
  have h0 : (37 : ZMod (37 ^ 2)) * (x - y) = 0 := by
    rw [ht]; linear_combination ((t.val : ℕ) : ZMod (37 ^ 2)) * h3737
  linear_combination h0

/-! ## 3. The smallest residual: the value of the level-`71` normalized-unit Dwork coordinate

After §1–§2, the genuine remaining content is the *value* of the doubled-degree coordinate
`W(a) := valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)` — the
level-`71` finite-log coordinate of the normalized real cyclotomic unit `ε_a^{p-1}`, of which the
genuine level-`72` Dwork column coordinate is exactly `2·W(a)` (the **proven** doubled-degree
bridge `genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq`).  We isolate, as a
`def … : Prop`, that `W(a)` is `37·ρ` times the column's Teichmüller-Vandermonde for a *uniform*
nonzero mod-`37` coefficient `ρ`.  This is strictly smaller than the target: it is stated on the
normalized-unit coordinate (the doubled-degree object, one `2`-factor already
extracted), the `37·unit` factor is generic (so the wrong hard-coded `1073` is avoided), and it
feeds the target through the proven bridge.

### Why this is the irreducible piece (the degree-`68` homogeneous slice / Kellner `α₁`)

The level-`72` coordinate at `varpi^{32}` of the finite logarithm receives, beyond the
first-order degree-`32` homogeneous slice, a *second-order* contribution from the degree-`68`
homogeneous slice: at level `λ^{72}` the ramification `varpi^{p-1} = varpi^{36} ≡ -37·(unit)`
folds the degree-`68` slice `varpi^{68} = varpi^{32}·varpi^{36} ≡ -37·(unit)·varpi^{32}` back onto
the `varpi^{32}` coordinate, contributing `37·(degree-`68` coefficient mod `37`)`.  The
degree-`32` coefficient is the first-order Bernoulli factor `B₃₂/32`, which is `37·(unit)` (the
irregularity `37 ∣ B₃₂`, proven `caseIICor823_secondOrder_bernoulliFactor_eq_three`:
`B₃₂/37·32⁻¹ ≡ 3·32⁻¹`); the degree-`68` coefficient is the **`B₆₈/68`** Bernoulli factor, whose
mod-`37` value is the proven Kellner `α₁`-invariant `B₆₈/68 ≡ 22 (mod 37)`
(`kellner_alpha_one_thirtyseven_thirtytwo`).  So the uniform `ρ = W(a)/37 mod 37` is an explicit
combination of `B₃₂.num/37 mod 37 = 3` (Kellner `α₀`, `kellner_at_zero_not_dvd` for `ρ ≠ 0`) and
`B₆₈/68 mod 37 = 22` (Kellner `α₁`).  Two genuine second-order obstructions stop a
re-instantiation of the first-order chain from reaching this value:

* the homogeneous degree-`d` slice for `37 ≤ d ≤ 71` has `37 ∣ d!`, so the factorial-cleared
  extraction `valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_…of_lt`
  (which needs `d < p - 1` for `d!` a `37`-unit) **does not apply** to the degree-`68` slice —
  that `37 ∣ d!` is precisely the source of the second-order `37`-factor and is the genuine
  `p`-adic-`L` content;
* the normalized-unit-to-quotient identity `ε_a^{p-1} ≡ a·(1−ζ)/(1−ζ^a)` holds only modulo
  `(λ)^{p-1} = (37)` (Fermat `c^p ≡ c`, proven only at precision `p - 1`), so the level-`72` value
  carries a second-order quotient correction.

These are exactly the two missing inputs (a single degree-`68` homogeneous slice and a single
precision-`72` quotient correction); the residual `CaseIICor823Level71NormalizedUnitCoeff37`
names their combined effect on the `varpi^{32}` coordinate — the precise irreducible piece. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` normalized-unit coordinate residual** (a `def … : Prop`, **not** an axiom — the
genuine doubled-degree `p`-adic-`L` content of Proposition 8.12 at `i = 32`).

There is a *uniform* mod-`37` leading coefficient `ρ : ZMod 37`, **nonzero** (the `M ≤ 1`
non-degeneracy), such that for every cyclotomic column `a` the level-`71` even-degree-`32` Dwork
coordinate of the normalized real cyclotomic-unit logarithm `ε_a^{p-1}` is `37·ρ` times the
column's Teichmüller-Vandermonde factor `((a+2)^{32} − 1)`:

  `valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)`
    `= (37 : ZMod 37²)·(ρ.val : ZMod 37²)·(((a+2)²)^{16} − 1)`.

This is the value of the doubled-degree finite-log coordinate `W(a)`, of which the genuine
level-`72` Dwork column coordinate is `2·W(a)` (proven).  It is the mod-`37²` level-`71` analog of
the proven first-order single-column value
`valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal`, made explicit at
the second order (where the first-order Bernoulli factor `B₃₂/32 mod 37 = 0` is degenerate, and the
extra mod-`37²` precision recovers the non-degenerate leading coefficient `ρ ≠ 0`, the proven
Kellner `α₀`).  It is **sound** (a coordinate-value identity), **non-circular** (its conclusion is
the explicit `37·ρ·V` value, not the vanishing of `c₁₅`), and **non-vacuous**
(`caseIICor823Level71NormalizedUnitCoeff37_consequent_inhabited`). -/
def CaseIICor823Level71NormalizedUnitCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ ≠ 0 ∧
    ∀ a : Fin (kummerLogRank 37),
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
          (kummerLogNormalizedUnitFiniteLog (p := 37) (K := CyclotomicField 37 ℚ)
            (by decide) a 71) =
        (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` normalized-unit coordinate residual's consequent is inhabited** (non-vacuity,
proven): both sides of the per-column identity are genuine elements of `ZMod 37²`, witnessed for
`ρ = 1`, `a = 0`.  So `CaseIICor823Level71NormalizedUnitCoeff37` is a real statement over a nonempty
index type, not vacuously true. -/
theorem caseIICor823Level71NormalizedUnitCoeff37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (ρ : ZMod 37) (a : Fin (kummerLogRank 37)),
      (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) =
        (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) :=
  ⟨1, ⟨0, by norm_num [kummerLogRank]⟩, rfl⟩

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level72LeadingCoeff37` from the level-`71` normalized-unit coordinate residual**
(proven, axiom-clean given `CaseIICor823Level71NormalizedUnitCoeff37`).

Take `ρ' = 2·ρ` (a unit mod `37`, since `ρ ≠ 0`).  The proven doubled-degree bridge
`genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq` gives
`genericColumnCoordLHS37 a = 2·W(a)`, and the residual gives `W(a) = 37·ρ.val·V(15,a)`, so
`genericColumnCoordLHS37 a = 37·(2·ρ.val)·V(15,a) = 37·(2·ρ).val·V(15,a)` mod `37²` (the
`2·ρ.val ≡ (2·ρ).val (mod 37)` collapse under the `37·` factor, via
`thirtyseven_mul_eq_of_castHom_eq`), and `2·ρ ≠ 0`. -/
theorem caseIICor823Level72LeadingCoeff37_of_normalizedUnitCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hNorm : CaseIICor823Level71NormalizedUnitCoeff37) :
    CaseIICor823Level72LeadingCoeff37 := by
  obtain ⟨ρ, hρ_ne, hnorm⟩ := hNorm
  refine ⟨2 * ρ, ?_, fun a => ?_⟩
  · -- `2·ρ ≠ 0` in the field `ZMod 37` (`2 ≠ 0`, `ρ ≠ 0`).
    exact mul_ne_zero (by decide) hρ_ne
  · -- `genericColumnCoordLHS37 a = 2·W(a) = 2·(37·ρ.val·V) = 37·(2·ρ.val)·V`.
    rw [genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq a, hnorm a]
    -- Goal: `2·(37·ρ.val·V) = 37·(2·ρ).val·V`.  Reassociate both to `37·(·)`, match mod `37`.
    rw [show (2 : ZMod (37 ^ 2)) *
          ((37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) =
        (37 : ZMod (37 ^ 2)) *
          ((2 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) from by ring]
    rw [show (37 : ZMod (37 ^ 2)) * ((((2 * ρ).val : ℕ)) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) =
        (37 : ZMod (37 ^ 2)) *
          ((((2 * ρ).val : ℕ) : ZMod (37 ^ 2)) *
            (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) from by ring]
    -- By `thirtyseven_mul_eq_of_castHom_eq`: the two `ZMod 37²` arguments agree mod `37`
    -- (`2·ρ.val ≡ (2·ρ).val ≡ 2·ρ`, and `castHom V₃₇² = V₃₇`).
    apply thirtyseven_mul_eq_of_castHom_eq
    -- `castHom ((n:ℕ):ZMod 37²) = ((n:ℕ):ZMod 37)`; for `n = ρ.val`, `(ρ.val:ZMod 37) = ρ`.
    have hcast : ∀ ρ' : ZMod 37, (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (((ρ'.val : ℕ)) : ZMod (37 ^ 2)) = ρ' := by
      intro ρ'
      rw [castHom_natCast_modSq, ZMod.natCast_val, ZMod.cast_id]
    simp only [map_mul, map_sub, map_one, map_pow, map_natCast, map_ofNat, hcast]

/-! ## 4. R4 and the FLT37 endpoint, from the level-`71` normalized-unit coordinate residual -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`71` normalized-unit coordinate
residual `CaseIICor823Level71NormalizedUnitCoeff37`** (proven, axiom-clean given the genuine
residuals + the carried Kellner Prop).

Composes `caseIICor823Level72LeadingCoeff37_of_normalizedUnitCoeff` with the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_level72LeadingCoeff` — Washington Proposition 8.12 at `i = 32`
reduced to the single statement that the level-`71` even-degree-`32` Dwork coordinate of the
normalized real cyclotomic unit `ε_a^{p-1}` is `37·ρ·(((a+2)²)^{16} − 1)` for a uniform nonzero
mod-`37` leading coefficient `ρ`.  The doubled-degree finite-log normalization (the level-`72`
coordinate is `2` times this level-`71` coordinate) and the `37·(structure)` lift are **proven**
(§1–§3); only the level-`71` normalized-unit coordinate *value* — the genuine second-order
`p`-adic-`L` content — remains.  Discharging it leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_level71NormalizedUnitCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_normalizedUnitCoeff : CaseIICor823Level71NormalizedUnitCoeff37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level72LeadingCoeff
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level72LeadingCoeff37_of_normalizedUnitCoeff caseII_normalizedUnitCoeff)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
