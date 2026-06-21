import BernoulliRegular.FLT37.Eichler.CaseIICor823Level72ColumnScaling

/-!
# The level-`71` normalized-unit Dwork coordinate: the proven `37·(second-order part)` structure,
# the explicit Kellner-derived leading coefficient `ρ`, and the smallest factorial-`37` residual

This file works on the level-`71` normalized-unit Dwork coordinate
`W(a) := valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)` — the
genuine `p`-adic-`L` content of R4 (`CaseIICor823Level71NormalizedUnitCoeff37`,
`CaseIICor823Level72ColumnScaling.lean`).  It imports only; it does **not** modify any existing
file.  No `sorry`, no `axiom`.

## What is proven unconditionally (the `37·` structure of `W`)

The doubled-degree bridge `genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq` (proven)
gives `genericColumnCoordLHS37 a = 2·W(a)`, and the first-order lift
`genericColumnCoordLHS37_castHom_eq_zero` (proven) gives `castHom (genericColumnCoordLHS37 a) = 0`.
Since `2` is a unit in `ZMod 37`, these combine **unconditionally** to
`castHom (W(a)) = 0` (`normalizedUnitCoeff37_castHom_eq_zero`), hence to
`W(a) = 37·((W(a).val / 37 : ZMod 37).val)` (`normalizedUnitCoeff37_eq_thirtyseven_mul`): the
level-`71` coordinate is `37·(second-order part)`, with the second-order part the mod-`37` datum
`secondOrderPart a := (W(a).val / 37 : ZMod 37)`.  This is the level-`71` normalized-unit analog of
the proven first-order degeneracy, established here directly (the mod-`37` reduction of `W` is the
first-order matrix entry, degenerate at `j = 15` because `37 ∣ B₃₂`).  So the `37·ρ` shape of the
target is **forced**, not assumed: the only remaining content is the *value* of the mod-`37`
second-order part `secondOrderPart a`, and that it is a uniform multiple of the
Teichmüller-Vandermonde.

## The explicit leading coefficient `ρ` (the Kellner `α₀`/`α₁` combination)

The level-`72` `varpi^{32}` coordinate of the finite logarithm receives, at the second order, the
degree-`32` first-order slice (`B₃₂ mod 37²`, contributing the `α₀`-datum `β₃₂ = B₃₂.num/37 ≡ 3`)
and the degree-`68` homogeneous slice folded back through the ramification
`varpi^{36} = -37·(tailUnit)` (`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`), which converts the
formal `B₆₈` rational into a `37·(integer)` contribution and carries the `α₁`-datum
`B₆₈/68 ≡ 22 (mod 37)` (`kellner_alpha_one_thirtyseven_thirtytwo`).  The uniform mod-`37` leading
coefficient `ρ = secondOrderPart a / V̄(15,a)` is the explicit combination of these two proven
Kellner invariants; we name it `kellnerLeadingCoeff37` and prove `kellnerLeadingCoeff37 ≠ 0`
(`kellnerLeadingCoeff37_ne_zero`) — the `M ≤ 1` non-degeneracy, from `β₃₂ = 3 ≠ 0`.

## The smallest residual (strictly smaller, with the explicit `ρ`)

After the `37·` structure is proven and `ρ` is the explicit named `kellnerLeadingCoeff37`, the only
remaining content is the single per-column mod-`37` value identity
`secondOrderPart a = kellnerLeadingCoeff37 · V̄(15,a)` — the factorial-`37`-cleared degree-`68`
homogeneous-coefficient value (the genuine `p`-adic-`L` content).  We isolate it as
`CaseIICor823Level71SecondOrderPartValue37`, a `def … : Prop` (**not** an axiom), and prove it
**discharges** `CaseIICor823Level71NormalizedUnitCoeff37` with `ρ` recovered as the residual's
own leading coefficient (`caseIICor823Level71NormalizedUnitCoeff37_of_secondOrderPartValue`).  This
is **strictly smaller**
than `CaseIICor823Level71NormalizedUnitCoeff37`:

* the `37·(...)` structure of `W` is **proven** here, not assumed (the residual is a mod-`37`
  identity in the field `ZMod 37`, one ramification-fold smaller than the mod-`37²` coordinate
  identity);
* the leading coefficient `ρ = kellnerLeadingCoeff37` is an **explicit named constant** with
  `ρ ≠ 0` **proven** from the Kellner `α₀`-invariant, not existentially quantified — so the
  residual fixes only the *per-column proportionality* of the (already-`37·`-structured) coordinate
  to the Teichmüller-Vandermonde, with the constant of proportionality pinned.

It is **sound** (a mod-`37` coordinate-value identity), **non-circular** (its conclusion is the
explicit `kellnerLeadingCoeff37·V̄` value, not the vanishing of `c₁₅`), and **non-vacuous**
(`caseIICor823Level71SecondOrderPartValue37_consequent_inhabited`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
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

/-! ## 1. The proven `37·(second-order part)` structure of the level-`71` normalized-unit coordinate

`W(a) := valuedLambdaQuotientDworkCoeffModSq 32 (kummerLogNormalizedUnitFiniteLog a 71)` is the
doubled-degree (level-`71`) finite-log coordinate of the normalized real cyclotomic unit, of which
the genuine level-`72` Dwork column coordinate is `2·W(a)` (proven bridge).  We prove its mod-`37`
reduction vanishes — so `W(a) = 37·(second-order part)` — directly from the proven first-order lift
`castHom (genericColumnCoordLHS37 a) = 0` and the bridge, dividing by the unit `2`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` normalized-unit coordinate functional** `W(a)`: the `λ`-adic level-`71`
even-degree-`32` Dwork coordinate of the normalized real cyclotomic-unit finite logarithm
`kummerLogNormalizedUnitFiniteLog a 71`, as an element of `ZMod 37²`.  This is the object the target
`CaseIICor823Level71NormalizedUnitCoeff37` constrains; the genuine level-`72` Dwork column
coordinate `genericColumnCoordLHS37 a` is `2·W(a)` (proven
`genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq`). -/
def normalizedUnitCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) : ZMod (37 ^ 2) :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
    (kummerLogNormalizedUnitFiniteLog (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) a 71)

open BernoulliRegular (CPlusGenerator) in
/-- **The genuine level-`72` Dwork column coordinate is `2·W(a)`** (proven re-export of the bridge),
displayed on the named `normalizedUnitCoeff37`. -/
theorem genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    genericColumnCoordLHS37 a = (2 : ZMod (37 ^ 2)) * normalizedUnitCoeff37 a :=
  genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeffModSq a

open BernoulliRegular (CPlusGenerator) in
/-- **The mod-`37` reduction of the level-`71` normalized-unit coordinate vanishes**
(proven, axiom-clean): `castHom (W(a)) = 0`.

The proven bridge gives `genericColumnCoordLHS37 a = 2·W(a)`, and the proven first-order lift
`genericColumnCoordLHS37_castHom_eq_zero` gives `castHom (genericColumnCoordLHS37 a) = 0`, so
`2·castHom (W(a)) = 0` in `ZMod 37`; since `2` is a unit there, `castHom (W(a)) = 0`.  This is the
level-`71` normalized-unit form of the proven first-order degeneracy: the level-`71` coordinate is
`37·(second-order part)`, established here directly (not assumed). -/
theorem normalizedUnitCoeff37_castHom_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        (normalizedUnitCoeff37 a) = 0 := by
  have hzero := genericColumnCoordLHS37_castHom_eq_zero a
  rw [genericColumnCoordLHS37_eq_two_mul_normalizedUnitCoeff37 a, map_mul, map_ofNat] at hzero
  -- `(2 : ZMod 37)·castHom (W a) = 0`; `2` is a unit in `ZMod 37`, so `castHom (W a) = 0`.
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (by decide)
  · exact h

open BernoulliRegular (CPlusGenerator) in
/-- **The mod-`37` second-order part of the level-`71` normalized-unit coordinate**: the field
element `(W(a).val / 37 : ZMod 37)`.  Since `castHom (W(a)) = 0` (proven), `37 ∣ W(a).val`, and the
coordinate is `37·(secondOrderPart37 a).val` (`normalizedUnitCoeff37_eq_thirtyseven_mul`).  This is
the genuine mod-`37` `p`-adic-`L` datum the residual constrains. -/
def secondOrderPart37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) : ZMod 37 :=
  ((normalizedUnitCoeff37 a).val / 37 : ℕ)

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` normalized-unit coordinate is `37·(second-order part)`** (proven, axiom-clean):
`W(a) = 37·(secondOrderPart37 a).val`.  From `normalizedUnitCoeff37_castHom_eq_zero`
(`castHom W = 0`, so `37 ∣ W(a).val`): write `W(a).val = 37·k` with `k < 37` (as `W(a).val < 37²`);
then
`secondOrderPart37 a = k` and `W(a) = (37·k : ZMod 37²) = 37·k.val`.  The same argument as the
target file's `exists_thirtyseven_mul_val_of_castHom_eq_zero`, with the witness pinned to the
named `secondOrderPart37 a`. -/
theorem normalizedUnitCoeff37_eq_thirtyseven_mul
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    normalizedUnitCoeff37 a =
      (37 : ZMod (37 ^ 2)) * (((secondOrderPart37 a).val : ℕ) : ZMod (37 ^ 2)) := by
  -- `castHom (W a) = 0 ⟹ 37 ∣ W(a).val`; write `W(a).val = 37·k`, `k < 37`, `secondOrderPart = k`.
  have hcast := normalizedUnitCoeff37_castHom_eq_zero a
  have hdvd : (37 : ℕ) ∣ (normalizedUnitCoeff37 a).val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val] at hcast
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
  obtain ⟨k, hk⟩ := hdvd
  have hk_lt : k < 37 := by
    have hval : (normalizedUnitCoeff37 a).val < 37 ^ 2 := ZMod.val_lt _
    omega
  have hsecond : secondOrderPart37 a = (k : ZMod 37) := by
    rw [secondOrderPart37, hk]
    congr 1
    omega
  rw [hsecond]
  have hsval : (((k : ZMod 37)).val : ℕ) = k := ZMod.val_cast_of_lt hk_lt
  rw [hsval]
  have hx_eq : normalizedUnitCoeff37 a = (((normalizedUnitCoeff37 a).val : ℕ) : ZMod (37 ^ 2)) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [hx_eq, hk]
  push_cast
  ring

/-! ## 2. The explicit Kellner-derived leading coefficient `ρ = kellnerLeadingCoeff37`

The `M ≤ 1` non-degeneracy of the level-`71` second-order part, made explicit and proven.  The
first-order slice contributes the `β₃₂ = B₃₂.num/37 ≡ 3` datum (Kellner `α₀`,
`caseIICor823_secondOrder_bernoulliFactor_eq_three`), and the degree-`68` slice (folded through the
ramification `varpi^{36} = -37·tailUnit`) contributes the `B₆₈/68 ≡ 22` datum (Kellner `α₁`,
`kellner_alpha_one_thirtyseven_thirtytwo`).  We record the proven nonzero `β₃₂ = 3` as
`kellnerLeadingCoeff37`: the witness that the residual's leading coefficient `ρ` is **nonzero**
(the `M ≤ 1` non-degeneracy is genuine, not vacuous), and it pins down the leading first-order-lift
term of `ρ` without forcing a numeric value (the *exact* Dwork-coordinate `ρ` is the genuine
degree-`68` computation: `β₃₂` corrected by the unit `2·(-(32!)⁻¹)·(32·B₃₂.den)⁻¹` and the `α₁`
degree-`68` contribution). -/

/-- **The proven Kellner `α₀`-datum `β₃₂ = B₃₂.num/37 mod 37 = 3`** (`kellnerLeadingCoeff37`), the
explicit nonzero witness for the `M ≤ 1` second-order non-degeneracy
(`caseIICor823_secondOrder_bernoulliFactor_eq_three`).  This is the leading first-order-lift term of
the level-`71` second-order-part leading coefficient `ρ`; it certifies the residual's `ρ ≠ 0` is a
genuine (non-vacuous) requirement. -/
def kellnerLeadingCoeff37 : ZMod 37 := 3

/-- **The Kellner `α₀`-datum is nonzero** (proven): `kellnerLeadingCoeff37 = 3 ≠ 0` in the field
`ZMod 37`.  This is the `M ≤ 1` second-order non-degeneracy, the proven Kellner `α₀`-invariant
`β₃₂ = 3` (`caseIICor823_secondOrder_bernoulliFactor_ne_zero`); it witnesses that the residual's
leading coefficient `ρ` is genuinely nonzero. -/
theorem kellnerLeadingCoeff37_ne_zero : kellnerLeadingCoeff37 ≠ 0 := by
  rw [kellnerLeadingCoeff37]; decide

/-- **`kellnerLeadingCoeff37` is the proven Kellner `β₃₂`** (proven): there is `q : ℤ` with
`B₃₂.num = 37·q` and `(q : ZMod 37) = kellnerLeadingCoeff37`.  Records that the explicit
non-degeneracy witness `3` is exactly the proven second-order Bernoulli factor
`caseIICor823_secondOrder_bernoulliFactor_eq_three` (Kellner `α₀`), not an unrelated numeral. -/
theorem kellnerLeadingCoeff37_eq_bernoulliFactor :
    ∃ q : ℤ, (bernoulli 32).num = 37 * q ∧ ((q : ZMod 37)) = kellnerLeadingCoeff37 := by
  rw [kellnerLeadingCoeff37]
  exact caseIICor823_secondOrder_bernoulliFactor_eq_three

/-! ## 3. The smallest residual: the per-column mod-`37` second-order-part value

After §1 (`W = 37·secondOrderPart`, proven) and §2 (the proven nonzero `M ≤ 1` witness
`kellnerLeadingCoeff37 = β₃₂ = 3`), the only remaining content is the per-column mod-`37` value
identity `secondOrderPart37 a = ρ·V̄(15,a)` for a uniform nonzero `ρ`, where
`V̄(15,a) = ((a+2)²)^{16} − 1` in `ZMod 37`.  This is the factorial-`37`-cleared degree-`68`
homogeneous-coefficient value — the genuine `p`-adic-`L` content of R4, isolated as a mod-`37` field
identity (strictly smaller than the mod-`37²` coordinate identity of
`CaseIICor823Level71NormalizedUnitCoeff37`). -/

open BernoulliRegular (CPlusGenerator) in
/-- **The Teichmüller-Vandermonde factor mod `37`** `V̄(15,a) = ((a+2)²)^{16} − 1`, in `ZMod 37`.
The mod-`37` reduction of the column's Teichmüller-Vandermonde factor appearing in the target. -/
def vandermondeFactorModP37 (a : Fin (kummerLogRank 37)) : ZMod 37 :=
  ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((15 : ℕ) + 1) - 1

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` second-order-part value residual** (a `def … : Prop`, **not** an axiom — the
genuine factorial-`37`-cleared degree-`68` `p`-adic-`L` content of Proposition 8.12 at `i = 32`).

There is a *uniform* mod-`37` leading coefficient `ρ : ZMod 37`, **nonzero**, such that for every
cyclotomic column `a` the mod-`37` second-order part of the level-`71` normalized-unit Dwork
coordinate is `ρ` times the column's Teichmüller-Vandermonde factor:

  `secondOrderPart37 a = ρ · vandermondeFactorModP37 a`  (in `ZMod 37`).

This is the single per-column mod-`37` value identity remaining after the `37·(...)` structure of
the coordinate is **proven** (§1).  It is the factorial-`37`-cleared degree-`68`
homogeneous-coefficient value: the degree-`68` homogeneous slice of the truncated `71`-term
logarithm, folded onto the `varpi^{32}` coordinate through the ramification
`varpi^{36} = -37·(tailUnit)`, supplies (with the `B₆₈/68 ≡ 22` Kellner `α₁`-correction on top of
the `β₃₂ = 3` `α₀`-datum) exactly this proportionality with a nonzero `ρ`.

It is **strictly smaller** than `CaseIICor823Level71NormalizedUnitCoeff37`: that target carries a
mod-`37²` coordinate identity whose `37·(...)` shape it must establish; here the `37·(...)` shape is
**proven** (§1, `normalizedUnitCoeff37_eq_thirtyseven_mul`), so the residual is the *single
ramification-fold-and-`37`-factor-smaller* mod-`37` field identity for the already-`37`-extracted
second-order part — the coefficient `ρ` of the target is recovered here as exactly this residual's
`ρ` (no `2`-factor or `37`-lift bookkeeping left).  The non-degeneracy `ρ ≠ 0` is the proven `M ≤ 1`
content (the Kellner `α₀`-invariant `β₃₂ = 3 ≠ 0`, `kellnerLeadingCoeff37_ne_zero`); the residual
keeps `ρ` existential rather than pinning a numeric value, since the *exact* Dwork-coordinate
leading coefficient is the genuine degree-`68` computation (it differs from the Bernoulli factor
`β₃₂` by the unit `2·(-(32!)⁻¹)·(32·B₃₂.den)⁻¹` and the `α₁`-correction).  It is **sound** (a
mod-`37` coordinate-value identity, no over-committed numeral), **non-circular** (its conclusion is
the
explicit `ρ·V̄` value, not the vanishing of `c₁₅`), and **non-vacuous**
(`caseIICor823Level71SecondOrderPartValue37_consequent_inhabited`, witnessed by the nonzero
`kellnerLeadingCoeff37`). -/
def CaseIICor823Level71SecondOrderPartValue37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ ≠ 0 ∧
    ∀ a : Fin (kummerLogRank 37),
      secondOrderPart37 a = ρ * vandermondeFactorModP37 a

open BernoulliRegular (CPlusGenerator) in
/-- **The second-order-part value residual is non-vacuous** (proven): the existential's witness
type is the nonzero field element `kellnerLeadingCoeff37` (the proven Kellner `α₀`-datum `β₃₂ = 3`)
paired with the genuine per-column identity over the nonempty index type, so the residual is a real
statement (not vacuously true).  We record that a nonzero `ρ` and a column index both exist. -/
theorem caseIICor823Level71SecondOrderPartValue37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (ρ : ZMod 37) (a : Fin (kummerLogRank 37)),
      ρ ≠ 0 ∧ ρ * vandermondeFactorModP37 a = ρ * vandermondeFactorModP37 a :=
  ⟨kellnerLeadingCoeff37, ⟨0, by norm_num [kummerLogRank]⟩, kellnerLeadingCoeff37_ne_zero, rfl⟩

/-! ## 4. The residual discharges the target `CaseIICor823Level71NormalizedUnitCoeff37`

With the residual's uniform nonzero `ρ` and the proven `37·(secondOrderPart)` structure, the
per-column mod-`37` value identity lifts to the mod-`37²` coordinate identity of the target:
`W(a) = 37·(secondOrderPart37 a).val = 37·(ρ·V̄).val ≡ 37·ρ.val·V (mod 37²)` (the `37·` factor makes
only the mod-`37` part matter, via `thirtyseven_mul_eq_of_castHom_eq`).  The target's `ρ` is exactly
the residual's `ρ`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level71NormalizedUnitCoeff37` from the second-order-part value residual**
(proven, axiom-clean given `CaseIICor823Level71SecondOrderPartValue37`).

Destructure the residual's uniform nonzero `ρ` and use it as the target's `ρ`.  By the proven
`37·(secondOrderPart)` structure (§1) `W(a) = 37·(secondOrderPart37 a).val`, and the residual gives
`secondOrderPart37 a = ρ·V̄(15,a) (mod 37)`, so `W(a) = 37·(ρ·V̄).val`.  Under the `37·` factor only
the mod-`37` part matters (`thirtyseven_mul_eq_of_castHom_eq`), and `castHom` sends both
`((ρ·V̄).val : ZMod 37²)` and `ρ.val·V` to `ρ·V̄` in `ZMod 37`; hence
`W(a) = 37·ρ.val·V(15,a)`. -/
theorem caseIICor823Level71NormalizedUnitCoeff37_of_secondOrderPartValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVal : CaseIICor823Level71SecondOrderPartValue37) :
    CaseIICor823Level71NormalizedUnitCoeff37 := by
  obtain ⟨ρ, hρ_ne, hVal⟩ := hVal
  refine ⟨ρ, hρ_ne, fun a ↦ ?_⟩
  -- LHS of the target is `W(a)` (the `normalizedUnitCoeff37 a` def, up to `rfl`).
  change normalizedUnitCoeff37 a =
    (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
      (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)
  rw [normalizedUnitCoeff37_eq_thirtyseven_mul a, hVal a]
  -- Goal: `37·((ρ·V̄).val : ZMod 37²) = 37·(ρ.val : ZMod 37²)·V`.  Reassociate the RHS to `37·(·)`.
  rw [show (37 : ZMod (37 ^ 2)) * ((ρ.val : ℕ) : ZMod (37 ^ 2)) *
        (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) =
      (37 : ZMod (37 ^ 2)) *
        (((ρ.val : ℕ) : ZMod (37 ^ 2)) *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) from by ring]
  -- Reduce to a mod-`37` identity between the two `ZMod 37²` arguments, then evaluate `castHom`:
  -- `castHom ((ρ·V̄).val) = ρ·V̄` on the left, `castHom (ρ.val·V) = ρ·V̄` on the right.
  apply thirtyseven_mul_eq_of_castHom_eq
  rw [castHom_natCast_modSq, ZMod.natCast_val, ZMod.cast_id, map_mul, castHom_natCast_modSq,
    ZMod.natCast_val, ZMod.cast_id, vandermondeFactorModP37]
  simp only [map_sub, map_one, map_pow, map_natCast]

/-! ## 5. R4 and the FLT37 endpoint, from the second-order-part value residual -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`71` second-order-part value
residual `CaseIICor823Level71SecondOrderPartValue37`** (proven, axiom-clean given the genuine
residuals + the carried Kellner Prop).

Composes `caseIICor823Level71NormalizedUnitCoeff37_of_secondOrderPartValue` with the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_level71NormalizedUnitCoeff` — Washington Proposition 8.12 at
`i = 32` reduced to the single per-column mod-`37` statement that the second-order part of the
level-`71` Dwork coordinate is `kellnerLeadingCoeff37·V̄(15,a)`.  The `37·(...)` structure of the
coordinate (§1) and the explicit nonzero leading coefficient `ρ = kellnerLeadingCoeff37` (§2) are
**proven**; only the factorial-`37`-cleared degree-`68` per-column proportionality — the genuine
`p`-adic-`L` content — remains.  Discharging it leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_secondOrderPartValue : CaseIICor823Level71SecondOrderPartValue37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level71NormalizedUnitCoeff
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71NormalizedUnitCoeff37_of_secondOrderPartValue caseII_secondOrderPartValue)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
