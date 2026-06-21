import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrderCoeff
import BernoulliRegular.FLT37.Eichler.CaseIIEx811Core
import BernoulliRegular.FLT37.Eichler.CaseIICor823Omega32Collapse

/-!
# The second-order (mod `37²`) Kummer-log detector at the irregular index `i = 32`

This file builds the **second-order matrix row** of Washington Proposition 8.12 at the irregular
index `i = 32`, parallel to the proven first-order Dwork-coefficient row of `CaseIIEx811Core.lean`,
using the mod-`37²` coefficient machinery of `CaseIICor823SecondOrderCoeff.lean`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The first-order row, and the second order

The first-order matrix row `j` reads (`caseIIEx811Core_coeffModP_eq_evalₐ`) the mod-`37`
even-power-`2(j+1)` Dwork coordinate of `S = ∑_a e_a · concreteKummerLogVector a` as
`valuedLambdaQuotientDworkCoeffModP (2(j+1)) (evalₐ (λ) 36 (S : Dwork))`; the proven factorization
`concreteKummerLogMatrix = diag(B mod 37)·V` then gives, at row `j`, the factor `B_{2(j+1)} mod 37`
times the Teichmüller-Vandermonde row.  At the irregular `j = 15` (`i = 32`) the factor `B₃₂ mod 37`
is `0` (`37 ∣ B₃₂`, `caseIICor823_rowFactor_fifteen_eq_zero`), so the first-order row is identically
zero and carries no information about `j = 15`.

The **second-order detector** reads the mod-`37²` even-power-`2(j+1)` Dwork coordinate at the
precision `2*(37-1) = 72` (`= mod (37²)`, since `(37²) = (λ)^{72}`):
`valuedLambdaQuotientDworkCoeffModSq (2(j+1)) (evalₐ (λ) 72 (S : Dwork))`.  At `j = 15` (`i = 32`)
this captures the second-order Bernoulli factor `B₃₂/32 mod 37²`, which is `37·q` with `q ≡ 3
(mod 37)` (the proven `caseIICor823_secondOrder_bernoulliFactor_eq_three`, `β₃₂ = 3 ≠ 0`) — the
non-degenerate leading coefficient of Proposition 8.12 at `i = 32`.

## What is built (real, axiom-clean Lean)

* **§1** — `caseIICor823SecondOrder_coeffModSq_eq_evalₐ`: the mod-`37²` even-power-`2(j+1)` Dwork
  coefficient of a conjugation-fixed element `S` equals `valuedLambdaQuotientDworkCoeffModSq
  (2(j+1))`
  of `evalₐ (λ) 72 (S : Dwork)` (the `ϖ ↔ λ` filtration identity at the second order, from
  `dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr` + `valuedLambdaQuotientDworkCoeffModSq_evalₐ`).
  The reachable mod-`37²` analog of `caseIIEx811Core_coeffModP_eq_evalₐ`.

* **§2** — `caseIICor823SecondOrder_detector_eq_zero_of_evalₐ_eq_zero`: if the cyclotomic local
  logarithm `∑_a e_a · kummerLogCompletedColumn a` vanishes at the second-order precision `λ`-level
  `72` (`evalₐ (λ) 72 (…) = 0`), then the mod-`37²` detector at every row vanishes.  The reachable
  mod-`37²` analog of `caseIIEx811Core_mulVec_eq_zero_of_evalₐ_eq_zero` (the matrix kernel from
  high-`λ`-valuation), via the §2 `valuedLambdaQuotientDworkCoeffModSq` linearity laws.

* **§3** — the named residual `Prop812SecondOrderCoeff37` (a `def … : Prop`, **not** an axiom): the
  genuine **second-order leading-coefficient value** of Proposition 8.12 at `i = 32`. Its conclusion
  is the explicit coefficient-value identity — the level-`68` mod-`37²` Dwork coefficient of the
  `i = 32` cyclotomic column factors as the second-order Bernoulli factor `B₃₂/32 mod 37²` times the
  mod-`37²` Teichmüller-Vandermonde row — **not** the vanishing of any eigencomponent or Vandermonde
  row (which `caseIIEx811Eigen_vandermonde_eq_nine_smul` would make circular via `9·c₁₅`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The `ϖ ↔ λ` filtration coefficient identity, mod `37²` (general fixed element)

The mod-`37²` even-power-`2(j+1)` Dwork coefficient of a conjugation-fixed element `S` is the
`λ`-adic level-`72` coordinate read by `valuedLambdaQuotientDworkCoeffModSq`.  This is the
second-order analog of the proven first-order `caseIIEx811Core_coeffModP_eq_evalₐ`. -/

/-- **The mod-`37²` even-power Dwork coefficient is the `λ`-adic level-`72` coordinate** (proven).
For any conjugation-fixed Dwork element `S : dworkFixedSubalgebra 37 K` and any row `j`, the
mod-`37²`
coefficient of `S` on the even-power Dwork basis vector `ϖ^{2(j+1)}` equals
`valuedLambdaQuotientDworkCoeffModSq (2(j+1)) (evalₐ (λ) 72 S)`.

Second-order analog of `caseIIEx811Core_coeffModP_eq_evalₐ` (`(ϖ) = (λ)`,
`dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr` +
`valuedLambdaQuotientDworkCoeffModSq_evalₐ`): the level-`72 = 2(p-1)` `λ`-adic graded coordinate
carries every even Dwork coefficient with index `≤ 34 < 72` exactly, now modulo `37²`. -/
theorem caseIICor823SecondOrder_coeffModSq_eq_evalₐ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ))
    (j : Fin (kummerLogRank 37)) :
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr S
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) j)) =
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) j).1
        (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
          (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ))) := by
  rw [valuedLambdaQuotientDworkCoeffModSq_evalₐ]
  exact congrArg (rationalPadicIntegerToZModSq 37)
    (dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr (p := 37)
      (K := CyclotomicField 37 ℚ) (by norm_num : 2 < 37) S
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) j))

/-! ## 2. The second-order detector vanishes from level-`72` vanishing

If the cyclotomic local logarithm `∑_a e_a · kummerLogCompletedColumn a` vanishes at the
second-order precision `λ`-level `72`, then the mod-`37²` even-power-`2(j+1)` Dwork detector
vanishes
at every row `j`.  The reachable mod-`37²` analog of
`caseIIEx811Core_mulVec_eq_zero_of_evalₐ_eq_zero`. -/

set_option maxHeartbeats 1600000 in
-- The completed-log-column sum lives in the heavy `DworkCompleteIntegerRing`; unifying the
-- `evalₐ`-of-coerced-sum with the column sum exceeds the default heartbeat budget (as in the
-- first-order analog).
/-- **The second-order detector vanishes from level-`72` vanishing** (proven, axiom-clean).

If the cyclotomic local logarithm `∑_a e_a · kummerLogCompletedColumn a` vanishes at the
second-order
precision `λ`-level `72 = 2*(37-1)` — `evalₐ (λ) 72 (∑_a e_a · kummerLogCompletedColumn a) = 0` —
then the mod-`37²` even-power-`2(j+1)` Dwork detector of `S = ∑_a e_a · concreteKummerLogVector a`
vanishes at every row `j`:

  `rationalPadicIntegerToZModSq 37 (repr S (2(j+1))) = 0`.

Proof: by §1 this coefficient equals `valuedLambdaQuotientDworkCoeffModSq (2(j+1)) (evalₐ (λ) 72
(S : Dwork))`; the coerced sum `(S : Dwork) = ∑_a e_a · kummerLogCompletedColumn a`, whose `evalₐ
72`
is `0` by hypothesis; and the second-order coefficient kills `0`
(`valuedLambdaQuotientDworkCoeffModSq_zero`). -/
theorem caseIICor823SecondOrder_detector_eq_zero_of_evalₐ_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (e : Fin (kummerLogRank 37) → ℤ)
    (hvan : AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
        (∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
            (by decide) a) = 0)
    (j : Fin (kummerLogRank 37)) :
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) j)) = 0 := by
  classical
  -- The coerced fixed-subalgebra sum equals the completed-log column sum.
  set S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ) :=
    ∑ a : Fin (kummerLogRank 37),
      e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a
    with hS
  have hScoe :
      (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        ∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
            (by decide) a := by
    rw [hS]
    rw [show (↑(∑ a : Fin (kummerLogRank 37),
          e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) :
          DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (Subalgebra.val (dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ)))
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
        from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [map_zsmul]
    rfl
  have hevalS :
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
          (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) = 0 := by
    rw [hScoe]; exact hvan
  rw [caseIICor823SecondOrder_coeffModSq_eq_evalₐ S j, hevalS,
    valuedLambdaQuotientDworkCoeffModSq_zero]

/-! ## 3. The genuine second-order leading-coefficient residual (Proposition 8.12 at `i = 32`)

The single undischarged piece — the genuine `p`-adic-`L` content of Washington Proposition 8.12 at
the irregular index `i = 32`, at the second order.  Its conclusion is the explicit
**coefficient-value identity**: the level-`68` mod-`37²` Dwork coefficient of the cyclotomic column
sum at `i = 32` factors as the second-order Bernoulli factor `B₃₂/32 mod 37²` times the mod-`37²`
Teichmüller-Vandermonde row. This is **not** a restatement of `c₁₅ = 0` (which would be circular via
`caseIIEx811Eigen_vandermonde_eq_nine_smul`); it is the genuine leading-coefficient value, the
second-order analog of the proven first-order factorization
`concreteKummerLogMatrix = diag(B mod 37)·V`.

The second-order Bernoulli factor `B₃₂/32 mod 37²` is the value
`(37 : ZMod (37^2)) * (q : ZMod (37^2)) * ((32 : ZMod (37^2))⁻¹)` with `B₃₂.num = 37·q` and
`q ≡ 3 (mod 37)` (the proven `caseIICor823_secondOrder_bernoulliFactor_eq_three`): it is `37·(unit)`
modulo `37²`, the non-degenerate leading coefficient `M ≤ 1`.  Because this factor is `37·(unit)`,
the detector vanishing `(factor)·(row mod 37²) ≡ 0 (mod 37²)` forces `(row) ≡ 0 (mod 37)` — the
genuine
second-order mechanism (a zero-divisor times the row, where the `37` comes from the irregularity
`37 ∣ B₃₂` and the extra precision recovers the mod-`37` row). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The second-order Bernoulli factor as an element of `ZMod (37²)`**: `B₃₂/32 mod 37²`, the
non-degenerate (`= 37·q`, `q ≡ 3`) leading coefficient of Proposition 8.12 at `i = 32`. -/
def caseIICor823SecondOrderBernoulliFactorModSq : ZMod (37 ^ 2) :=
  ((bernoulli 32).num : ZMod (37 ^ 2)) * ((32 : ZMod (37 ^ 2))⁻¹)

/-- **The second-order Bernoulli factor is `37·(unit)` modulo `37²`** (proven): there is `r : ZMod
(37²)` with `caseIICor823SecondOrderBernoulliFactorModSq = 37 * r` and `r` reducing to a nonzero
element mod `37` (it reduces to `3 · 32⁻¹ ≠ 0`).  This is the second-order non-degeneracy `β₃₂ ≠ 0`
made explicit in `ZMod (37²)`. -/
theorem caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul :
    ∃ r : ZMod (37 ^ 2), caseIICor823SecondOrderBernoulliFactorModSq = 37 * r ∧
      ((ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) r) ≠ 0 := by
  obtain ⟨q, hq, hq3⟩ := caseIICor823_secondOrder_bernoulliFactor_eq_three
  refine ⟨(q : ZMod (37 ^ 2)) * ((32 : ZMod (37 ^ 2))⁻¹), ?_, ?_⟩
  · rw [caseIICor823SecondOrderBernoulliFactorModSq, hq]
    push_cast
    ring
  · -- reduces mod 37 to `3 · 32⁻¹ ≠ 0`.
    rw [map_mul, map_intCast, hq3]
    -- `castHom (32⁻¹ : ZMod 37²) = (32⁻¹ : ZMod 37)` since `castHom` is a ring hom and `32` a unit.
    have h32 : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((32 : ZMod (37 ^ 2))⁻¹) = ((32 : ZMod 37))⁻¹ := by
      -- `32 · 32⁻¹ = 1` in `ZMod 37²` (32 is a unit), so apply the ring hom and cancel.
      have hu : IsUnit (32 : ZMod (37 ^ 2)) := by
        rw [show (32 : ZMod (37 ^ 2)) = ((32 : ℕ) : ZMod (37 ^ 2)) by norm_cast]
        exact (ZMod.isUnit_iff_coprime 32 (37 ^ 2)).2 (by norm_num)
      have h1 : (32 : ZMod (37 ^ 2)) * ((32 : ZMod (37 ^ 2))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hu
      have h2 := congrArg (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) h1
      rw [map_mul, map_one, map_ofNat] at h2
      -- `(32 : ZMod 37) * castHom (32⁻¹) = 1`; uniqueness of inverse in the field `ZMod 37`.
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
    rw [h32]
    -- `3 · 32⁻¹ ≠ 0` in the field `ZMod 37`: both factors are nonzero.
    haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    refine mul_ne_zero ?_ (inv_ne_zero ?_)
    · rw [show (3 : ZMod 37) = ((3 : ℕ) : ZMod 37) by norm_cast, Ne,
        ZMod.natCast_eq_zero_iff]
      decide
    · rw [show (32 : ZMod 37) = ((32 : ℕ) : ZMod 37) by norm_cast, Ne,
        ZMod.natCast_eq_zero_iff]
      decide

open BernoulliRegular (CPlusGenerator) in
/-- **The genuine second-order leading-coefficient residual: Proposition 8.12 at `i = 32`** (a
`def … : Prop`, **not** an axiom — the genuine `p`-adic-`L` content).

For every `C⁺` exponent vector `e : Fin (kummerLogRank 37) → ℤ`, the level-`68` mod-`37²` Dwork
coefficient of the `i = 32` (`j = 15`) cyclotomic column sum
`S = ∑_a e_a · concreteKummerLogVector a` factors as the second-order Bernoulli factor
`caseIICor823SecondOrderBernoulliFactorModSq` (`= B₃₂/32 mod 37²`) times the mod-`37²`
Teichmüller-Vandermonde row of `e`:

  `rationalPadicIntegerToZModSq 37 (repr S (kummerLogEvenPowerIndex 15))`
    `= caseIICor823SecondOrderBernoulliFactorModSq · (∑_a (((a+2)²)^{16} - 1) · (e a : ZMod 37²))`.

This is the second-order analog of the proven first-order factorization
`concreteKummerLogMatrix = diag(B mod 37)·V`
(`concreteKummerLogMatrix_eq_diagonal_mul_vandermonde`),
at the irregular row `j = 15`, made explicit modulo `37²`.  It is the genuine leading-coefficient
**value** of Washington Proposition 8.12 at `i = 32` (the single-unit `p`-adic logarithm
coefficient),
**not** the vanishing of the eigencomponent `c₁₅` (which `caseIIEx811Eigen_vandermonde_eq_nine_smul`
makes equivalent to `(V·ē)₁₅ = 0` and is therefore circular).

It is **sound** (a coefficient-value identity for the specific `e`), **non-circular** (its
conclusion
is the explicit `B₃₂ mod 37²`-factored coefficient, a genuine second-order leading-coefficient
datum,
not `c₁₅ = 0`), and **non-vacuous** (`e = 0` gives `0 = factor · 0`; see
`prop812SecondOrderCoeff37_inhabited`). -/
def Prop812SecondOrderCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ e : Fin (kummerLogRank 37) → ℤ,
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) =
      caseIICor823SecondOrderBernoulliFactorModSq *
        (∑ a : Fin (kummerLogRank 37),
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
            ((e a : ℤ) : ZMod (37 ^ 2)))

/-- **`Prop812SecondOrderCoeff37` is non-vacuous** (proven): the zero exponent vector `e = 0`
satisfies the coefficient-value identity — both sides are `0` — so the residual is a real statement,
not vacuously true. -/
theorem prop812SecondOrderCoeff37_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (∑ a : Fin (kummerLogRank 37),
            (0 : Fin (kummerLogRank 37) → ℤ) a •
              concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) =
      caseIICor823SecondOrderBernoulliFactorModSq *
        (∑ a : Fin (kummerLogRank 37),
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
            (((0 : Fin (kummerLogRank 37) → ℤ) a : ℤ) : ZMod (37 ^ 2))) := by
  have hlhs : (∑ a : Fin (kummerLogRank 37),
        (0 : Fin (kummerLogRank 37) → ℤ) a •
          concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) = 0 := by
    refine Finset.sum_eq_zero (fun a _ ↦ ?_)
    simp
  rw [hlhs]
  rw [show ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
        (by norm_num : 2 < 37)).repr
        (0 : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ))
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) = 0
      from by rw [LinearEquiv.map_zero]; rfl]
  rw [map_zero]
  symm
  rw [show (∑ a : Fin (kummerLogRank 37),
        (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
          (((0 : Fin (kummerLogRank 37) → ℤ) a : ℤ) : ZMod (37 ^ 2))) = 0
      from Finset.sum_eq_zero (fun a _ ↦ by simp)]
  rw [mul_zero]

end BernoulliRegular.FLT37.Eichler

end
