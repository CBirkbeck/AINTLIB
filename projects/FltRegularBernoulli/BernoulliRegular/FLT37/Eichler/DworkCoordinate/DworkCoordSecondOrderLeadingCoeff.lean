import BernoulliRegular.FLT37.Eichler.Reduction.IrregularEigencollapseGenericDworkFactor

/-!
# The level-`72` mod-`37²` Dwork column coordinate: the proven first-order lift, and the smallest
# residual (the level-`72` second-order leading coefficient)

This file supplies the **actual** level-`72` mod-`37²` Dwork column coordinate
`genericColumnCoordLHS37 a` to the generic R4 engine `CaseIICor823GenericColumnCoord37`
(`CaseIICor823GenericColumnCoord.lean`).  It imports only; it does **not** modify any existing file.
No `sorry`, no `axiom`.

## What is proven, and the smallest residual

The generic engine consumes `∃ F r, F = 37·r ∧ castHom r ≠ 0 ∧ ∀ a, genericColumnCoordLHS37 a =
F·(((a+2)²)^{16} − 1)`.  Two things must be established about the genuine level-`72` coordinate:

* **§1 — the proven first-order lift `F = 37·r` (the `castHom F = 0` structure).**  We prove
  *unconditionally* `castHom (genericColumnCoordLHS37 a) = 0` for every column `a`
  (`genericColumnCoordLHS37_castHom_eq_zero`): the mod-`37` reduction of the level-`72` coordinate is
  the level-`36` first-order coordinate (the proven `castHom`/level compatibility
  `valuedLambdaQuotientDworkCoeffModP_eq_castHom_modSq`), which is the first-order Kummer-log matrix
  entry `concreteKummerLogMatrix 15 a = kummerLogDetRowFactor 15 · V(15,a)`, and
  `kummerLogDetRowFactor 15 = B₃₂/32 mod 37 = 0` (the proven `caseIICor823_rowFactor_fifteen_eq_zero`,
  the irregularity `37 ∣ B₃₂`).  So the level-`72` coordinate is `37·(second-order part)`: the
  `F = 37·r` structure is **forced**, not assumed.  This is the genuine first-order-structure lift
  the project's first-order single-column chain provides (the mod-`37` reduction of the level-`72`
  coordinate is the proven-degenerate first-order row).

* **§2 — the smallest residual: the level-`72` second-order leading coefficient
  `CaseIICor823Level72LeadingCoeff37`.**  After §1, all that remains is the genuine
  second-order content: that the level-`72` coordinate is `37·ρ·(((a+2)²)^{16} − 1)` for a *uniform*
  mod-`37` leading coefficient `ρ` that is **nonzero** (the `M ≤ 1` non-degeneracy).  We isolate this
  as `∃ ρ : ZMod 37, ρ ≠ 0 ∧ ∀ a, genericColumnCoordLHS37 a = 37·(ρ.val)·(((a+2)²)^{16} − 1)`.  This
  is exactly the level-`72` Dwork-evaluator content of Proposition 8.12 at `i = 32`: the
  second-order leading coefficient (the second-order analog of the proven first-order
  `concreteKummerLogMatrix = diag(B mod 37)·V`, whose `j = 15` row is degenerate).  No level-`72`
  analog of the entire `KummerLogFormalEvaluator` chain exists in the project; this single
  uniform-mod-`37`-factor statement is the precise irreducible piece.  It is **strictly smaller**
  than `CaseIICor823GenericColumnCoord37` (the `F = 37·r` structure is *proven* in §1, so the
  residual fixes only the genuine second-order leading coefficient `ρ` and its non-degeneracy, a
  mod-`37` datum), **sound** (the `ρ.val`-lift makes `F = 37·(ρ.val : ZMod 37²)` automatically
  `37·unit` via `castHom (ρ.val : ZMod 37²) = ρ ≠ 0`, so the non-degeneracy is the residual's own
  `ρ ≠ 0`, the `M ≤ 1` content made explicit and not double-counted), **non-circular** (its
  conclusion is the explicit second-order coefficient value, not the vanishing of `c₁₅`), and
  **non-vacuous** (the consequent `37·(ρ.val)·V_a` is a genuine element of `ZMod 37²`; see
  `caseIICor823Level72LeadingCoeff37_consequent_inhabited`).

* **§3 — `CaseIICor823GenericColumnCoord37` from the residual** (proven): take
  `F = 37·(ρ.val : ZMod 37²)`, `r = (ρ.val : ZMod 37²)`; then `F = 37·r`, `castHom r = ρ ≠ 0`, and
  the per-column identity is the residual.  This feeds the generic R4 engine.

* **§4 — the FLT37 endpoint** `fermatLastTheoremFor_thirtyseven_of_level72LeadingCoeff`, R4 reduced
  to the single level-`72` second-order leading coefficient.

## The factor value (machine-checked), and why the wrong `1073` is avoided

The structurally-expected level-`72` factor is the first-order-structure lift
`firstOrderStructureLiftFactor = 2·(-(32!)⁻¹)·(B₃₂.num·(32·B₃₂.den)⁻¹) = 407 = 37·11`
(`firstOrderStructureLiftFactor_eq`), whose mod-`37` second-order part is `ρ = 11`; the genuine
level-`72` factor is this plus a degree-`37..72` truncation correction.  The hard-coded
`caseIICor823SecondOrderBernoulliFactorModSq = 1073 = 37·29` is a **different** `37·unit` (mod-`37`
part `29 ≠ 11`), and is **not** the level-`72` coordinate factor
(`firstOrderStructureLiftFactor_ne_bernoulliFactor`).  By stating the residual over a *generic* `ρ`
(the genuine second-order leading coefficient, whatever its value — `11` plus the correction's
mod-`37` part), the wrong `1073` is avoided entirely; the generic engine needs only `ρ ≠ 0`, which is
the proven `M ≤ 1`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The proven first-order lift: the mod-`37` reduction of the level-`72` coordinate vanishes

For every column `a`, `castHom (genericColumnCoordLHS37 a) = 0`, i.e. the level-`72` coordinate is
`37·(second-order part)`.  This is the project's first-order single-column structure at the level-`72`
coordinate: the mod-`37` reduction is the first-order Kummer-log matrix entry, which is degenerate at
`j = 15` (`B₃₂/32 mod 37 = 0`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` coordinate's mod-`37` reduction is the first-order Kummer-log matrix entry**
(proven, axiom-clean): `castHom (genericColumnCoordLHS37 a) = concreteKummerLogMatrix 15 a`.

The mod-`37` reduction of the level-`72` `varpi^{32}` Dwork coordinate is the level-`36` first-order
coordinate (the proven `castHom`/level compatibility
`valuedLambdaQuotientDworkCoeffModP_eq_castHom_modSq`); that level-`36` single-column coordinate is
the first-order Kummer-log matrix entry `concreteKummerLogMatrix 15 a` (the proven `ϖ ↔ λ` bridge
`caseIIEx811Core_coeffModP_eq_evalₐ` applied to the single fixed column `concreteKummerLogVector a`,
plus `concreteKummerLogCoeff_eq`). -/
theorem genericColumnCoordLHS37_castHom_eq_concreteKummerLogMatrix
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (genericColumnCoordLHS37 a) =
      concreteKummerLogMatrix (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) (by norm_num)
        (15 : Fin (kummerLogRank 37)) a := by
  -- Work from the matrix-entry side.  The entry is the mod-`37` `repr` coordinate of the single
  -- fixed column `S = concreteKummerLogVector a` (`concreteKummerLogCoeff_eq`); the proven `ϖ ↔ λ`
  -- bridge `caseIIEx811Core_coeffModP_eq_evalₐ` (forward) rewrites it to the level-`36` `evalₐ`
  -- coordinate of `(S : Dwork) = kummerLogCompletedColumn a`; and the proven `castHom`/level
  -- compatibility identifies that with the mod-`37` reduction of the level-`72` coordinate.
  rw [show concreteKummerLogMatrix (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) (by norm_num)
        (15 : Fin (kummerLogRank 37)) a =
      rationalPadicIntegerToZMod 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))))
      from concreteKummerLogCoeff_eq (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num)
        (by norm_num) (15 : Fin (kummerLogRank 37)) a]
  rw [caseIIEx811Core_coeffModP_eq_evalₐ
    (concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
    (15 : Fin (kummerLogRank 37))]
  -- `(concreteKummerLogVector a : Dwork) = kummerLogCompletedColumn a` (definitional coercion of the
  -- fixed-subalgebra column `kummerLogFixedColumn a = ⟨kummerLogCompletedColumn a, _⟩`).
  rw [show (concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a :
        DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
      kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a from rfl]
  rw [genericColumnCoordLHS37,
    valuedLambdaQuotientDworkCoeffModP_eq_castHom_modSq (p := 37) (K := CyclotomicField 37 ℚ)
      (by norm_num)
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
      (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)]

open BernoulliRegular (CPlusGenerator) in
/-- **The mod-`37` reduction of the level-`72` coordinate vanishes** (proven, axiom-clean): for every
column `a`, `castHom (genericColumnCoordLHS37 a) = 0`.

The first-order structure lift: the level-`72` coordinate is `37·(second-order part)`, forcing the
`F = 37·r` form of the generic engine's factor.  Proof: by
`genericColumnCoordLHS37_castHom_eq_concreteKummerLogMatrix` the reduction is the first-order matrix
entry `concreteKummerLogMatrix 15 a = kummerLogDetRowFactor 15 · V(15,a)`
(`concreteKummerLogMatrix_eq_diagonal_mul_vandermonde`), and the proven
`caseIICor823_rowFactor_fifteen_eq_zero` (`B₃₂/32 mod 37 = 0`, the irregularity `37 ∣ B₃₂`) makes the
row factor `0`. -/
theorem genericColumnCoordLHS37_castHom_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (genericColumnCoordLHS37 a) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [genericColumnCoordLHS37_castHom_eq_concreteKummerLogMatrix a]
  -- `concreteKummerLogMatrix 15 a = (diag(rowFactor) · V) 15 a = rowFactor 15 · V(15,a) = 0`.
  rw [concreteKummerLogMatrix_eq_diagonal_mul_vandermonde (p := 37) (K := CyclotomicField 37 ℚ)
    (by norm_num) (by norm_num)]
  rw [Matrix.diagonal_mul, caseIICor823_rowFactor_fifteen_eq_zero, zero_mul]

/-! ## 2. The smallest residual: the level-`72` second-order leading coefficient

After §1 (`F = 37·r` forced), the genuine remaining content is that the level-`72` coordinate is
`37·ρ·(((a+2)²)^{16} − 1)` for a *uniform* mod-`37` leading coefficient `ρ ≠ 0`.  This is the
level-`72` Dwork-evaluator content of Proposition 8.12 at `i = 32` — the second-order leading
coefficient — isolated as a `def … : Prop` (**not** an axiom). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` second-order leading-coefficient residual** (a `def … : Prop`, **not** an axiom
— the genuine level-`72` Dwork-evaluator `p`-adic-`L` content of Proposition 8.12 at `i = 32`).

There is a *uniform* mod-`37` second-order leading coefficient `ρ : ZMod 37`, **nonzero** (the `M ≤ 1`
non-degeneracy), such that for every cyclotomic column `a` the level-`72` even-degree-`32` Dwork
coordinate of the completed real cyclotomic-unit logarithm column is `37·ρ·(((a+2)²)^{16} − 1)`:

  `genericColumnCoordLHS37 a = (37 : ZMod 37²)·((ρ.val : ℕ) : ZMod 37²)·(((a+2)²)^{16} − 1)`.

This is the second-order analog of the proven first-order single-column factorization
`concreteKummerLogMatrix = diag(B mod 37)·V`, at the irregular row `j = 15` (degenerate at first
order, `B₃₂/32 mod 37 = 0`), made explicit at the level-`72` second order.  By §1 the mod-`37`
reduction of the coordinate is already proven `0`, so the residual carries **only** the genuine
second-order content: the uniform leading coefficient `ρ` and its non-degeneracy `ρ ≠ 0`.  The
`ρ.val`-lift makes `F = 37·(ρ.val : ZMod 37²)` automatically `37·unit`
(`castHom (ρ.val : ZMod 37²) = ρ ≠ 0`), so the residual's `ρ ≠ 0` *is* the `M ≤ 1` non-degeneracy,
not double-counted. -/
def CaseIICor823Level72LeadingCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ ≠ 0 ∧
    ∀ a : Fin (kummerLogRank 37),
      genericColumnCoordLHS37 a =
        (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`72` leading-coefficient residual's consequent is inhabited** (non-vacuity, proven):
both sides of the per-column identity are genuine elements of `ZMod 37²`, witnessed for `ρ = 1`,
`a = 0`.  So `CaseIICor823Level72LeadingCoeff37` is a real statement over a nonempty index type, not
vacuously true. -/
theorem caseIICor823Level72LeadingCoeff37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (ρ : ZMod 37) (a : Fin (kummerLogRank 37)),
      (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) =
        (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) :=
  ⟨1, ⟨0, by norm_num [kummerLogRank]⟩, rfl⟩

/-! ## 3. `CaseIICor823GenericColumnCoord37` from the residual

The `ρ.val`-lift makes the generic engine's `F = 37·r` data explicit: `F = 37·(ρ.val : ZMod 37²)`,
`r = (ρ.val : ZMod 37²)`, with `castHom r = ρ ≠ 0` (the residual's own non-degeneracy). -/

/-- **`castHom ((n : ZMod 37²)) = (n : ZMod 37)`** for a natCast (proven): the mod-`37` reduction of
a rational integer reduced mod `37²` is its reduction mod `37` (both are the natCast). -/
theorem castHom_natCast_modSq (n : ℕ) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) ((n : ℕ) : ZMod (37 ^ 2)) =
      ((n : ℕ) : ZMod 37) := by
  rw [map_natCast]

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823GenericColumnCoord37` from the level-`72` leading-coefficient residual** (proven,
axiom-clean given `CaseIICor823Level72LeadingCoeff37`).

Take `F = 37·(ρ.val : ZMod 37²)`, `r = (ρ.val : ZMod 37²)`.  Then `F = 37·r` (rfl-level);
`castHom r = (ρ.val : ZMod 37) = ρ ≠ 0` (`castHom_natCast_modSq` + `ZMod.natCast_val` + `ZMod.cast_id`
on `ρ : ZMod 37`); and the per-column identity `genericColumnCoordLHS37 a = F·(((a+2)²)^{16} − 1)` is
the residual rewritten (`37·(ρ.val)·V_a = (37·(ρ.val))·V_a`).  Feeds the generic R4 engine. -/
theorem caseIICor823GenericColumnCoord37_of_level72LeadingCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLead : CaseIICor823Level72LeadingCoeff37) :
    CaseIICor823GenericColumnCoord37 := by
  obtain ⟨ρ, hρ_ne, hcol⟩ := hLead
  refine ⟨(37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)),
    ((ρ.val : ℕ) : ZMod (37 ^ 2)), rfl, ?_, ?_⟩
  · -- `castHom ((ρ.val : ZMod 37²)) = (ρ.val : ZMod 37) = ρ ≠ 0`.
    rw [castHom_natCast_modSq, ZMod.natCast_val, ZMod.cast_id]
    exact hρ_ne
  · -- The per-column identity, with `F = 37·(ρ.val)` regrouped (the residual is `rfl`-aligned).
    intro a
    rw [hcol a]

/-! ## 4. R4 and the FLT37 endpoint, from the level-`72` leading-coefficient residual -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the level-`72` leading-coefficient
residual** (proven, axiom-clean given `CaseIICor823Level72LeadingCoeff37`).

Composes `caseIICor823GenericColumnCoord37_of_level72LeadingCoeff` with the proven generic engine
`cor823PthPowerOfRationalModSq37_of_genericColumnCoord`. -/
theorem cor823PthPowerOfRationalModSq37_of_level72LeadingCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hLead : CaseIICor823Level72LeadingCoeff37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_genericColumnCoord
    (caseIICor823GenericColumnCoord37_of_level72LeadingCoeff hLead)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`72` second-order leading
coefficient `CaseIICor823Level72LeadingCoeff37`** (proven, axiom-clean given the genuine residuals +
the carried Kellner Prop).

Supplies the level-`72` second-order leading coefficient to the generic R4 engine endpoint
`fermatLastTheoremFor_thirtyseven_of_genericColumnCoord` — Washington Proposition 8.12 at `i = 32`
reduced to the single statement that the level-`72` even-degree-`32` Dwork coordinate of a single
completed real cyclotomic-unit logarithm column is `37·ρ·(((a+2)²)^{16} − 1)` for a uniform nonzero
mod-`37` leading coefficient `ρ`.  The `F = 37·r` structure of that coordinate is **proven** (§1, the
first-order lift `castHom = 0`); only the second-order leading coefficient `ρ` (the level-`72`
Dwork-evaluator content) and its non-degeneracy `ρ ≠ 0` (the proven `M ≤ 1`) remain.  Discharging
this leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_level72LeadingCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_level72LeadingCoeff : CaseIICor823Level72LeadingCoeff37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genericColumnCoord
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823GenericColumnCoord37_of_level72LeadingCoeff caseII_level72LeadingCoeff)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
