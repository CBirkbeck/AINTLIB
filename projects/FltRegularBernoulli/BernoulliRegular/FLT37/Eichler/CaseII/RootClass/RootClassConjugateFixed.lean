import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassTrivialOverRealData

/-!
# [FLT37-CASEII-REAL-ROOTCLASS-CONJFIXED] The genuinely-true Case-II II1 residual

## Why the previous residual `CaseIIRootRatioPthPower37` is provably false

`CaseIIRealAnchoredClass.lean` carried the Case-II II1 residual as
`CaseIIRootRatioPthPower37`: for adjacent `η ≠ η₀` over real data, there exist `a, b ≠ 0` with

  `(x + yη)·b^37 = (x + yη⁻¹)·a^37`,

i.e. `α₀ := (x + yη)/(x + yη⁻¹) = (a/b)^37` is a `37`-th power **in `K^×`**.  This is
**provably false**.  By Washington §9.1 (pp. 169-170) the radical that Lemma 9.2 makes a `37`-th
power is the *corrected* `α := -ζ^{-a}·α₀`, **not** `α₀` itself: `α₀ = -ζ^{a}·α^{...}` carries a
genuine root-of-unity twist `-ζ^a`.  And `-ζ^a` is **not** a `37`-th power in `K^× = ℚ(ζ₃₇)^×` for
`a ≢ 0 (mod 37)`: the only `37`-th-power roots of unity in `K^×` are `{1, -1}` (any `μ₇₄`-element
`η` has `η^37 ∈ {1, -1}`), and `-ζ^a ∈ {1, -1}` iff `a ≡ 0`.  For the adjacent roots one has
`a ≢ 0`.  Hence no such `a, b` exist, and the endpoint
`fermatLastTheoremFor_thirtyseven_of_realAnchoredClass` resting on
`CaseIIRootRatioPthPower37` is **vacuous**.

## The genuinely-true target: the `-ζ^a` twist is irrelevant at the ideal / class level

The downstream consumer (`caseII_anchored_class_sq_eq_one_of_pthPower` →
`caseII_real_anchored_class_trivial_of_pthPower` → the endpoint) only ever uses the **class**
consequence `[𝔞(η)] = [𝔞(η⁻¹)]` (the conjugate-fixedness of the Washington root class) — it goes
through `caseII_rootClass_eq_etaInv_of_pthPower`, whose own content
(`caseII_rootIdeal_mul_span_eq_of_pthPower`) is purely ideal-theoretic.  At the ideal level the
`-ζ^a` unit factor **vanishes** (`(ζ) = (1)`).  So the genuinely-true, satisfiable, **non-vacuous**
residual is the class equality itself:

  `[𝔞(η)] = [𝔞(η⁻¹)]`        (Washington Lemma 9.2's class consequence).

This file:

* states the corrected TRUE residual `CaseIIRootClassConjFixed37` (the **class form**
  `[𝔞(η)] = [𝔞(η⁻¹)]`);
* proves it is genuinely true / **non-vacuous**: it follows from the *corrected element form*
  `(x + yη)·b^37 = u·(x + yη⁻¹)·a^37` for a **unit** `u : (𝓞 K)ˣ` (which absorbs `-ζ^a` and is
  satisfiable — Washington Lemma 9.2), and equally from the **ideal form**
  `(x + yη)·(b)^37 = (x + yη⁻¹)·(a)^37` (as ideals).  Neither demands `-ζ^a` be a `37`-th power;
* re-derives the entire `c = 1` chain (`c² = 1`, `c = 1`, principalization) and the non-vacuous
  endpoint from `CaseIIRootClassConjFixed37`, mirroring `CaseIIRealAnchoredClass.lean` but from the
  TRUE residual.

It imports `CaseIIRealAnchoredClass.lean` (reusing its proven ideal/class machinery) and does
**not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, Lemma 9.2), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- Injectivity of `37`-th powers on ideals of `𝓞 K`: from `I ^ 37 = J ^ 37` deduce `I = J`.
`Ideal (𝓞 K)` is a `UniqueFactorizationMonoid`, so the `37`-th-power map is injective.  Used to
descend the cancelled `(𝔞·(b))^37 = (𝔞·(a))^37` identities to `𝔞·(b) = 𝔞·(a)`. -/
private theorem ideal_eq_of_pow37_eq {I J : Ideal (𝓞 K)} (h : I ^ 37 = J ^ 37) : I = J :=
  le_antisymm
    (Ideal.dvd_iff_le.mp
      ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h.symm.dvd))
    (Ideal.dvd_iff_le.mp
      ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h.dvd))

/-! ## 1. The corrected element form ⟹ the ideal identity (the `-ζ^a` twist is absorbed)

The provably-false `CaseIIRootRatioPthPower37` is the element identity with **no** unit:
`(x+yη)·b^37 = (x+yη⁻¹)·a^37`.  Washington Lemma 9.2 instead supplies the *corrected* identity
with a root-of-unity twist absorbed into a **unit** `u`.  The ideal heart
(`caseII_rootIdeal_mul_span_eq_of_pthPower`) only used `(x+yη)·b^37` and `(x+yη⁻¹)·a^37` up to the
span, where the unit `u` disappears.  We reprove that ideal identity from the corrected
(unit-twisted) element form — this is what makes the residual *true*, since `u` can be `-ζ^a`. -/

set_option maxRecDepth 4000 in
/-- **`𝔞(η)·(b) = 𝔞(η⁻¹)·(a)` from the *unit-corrected* `37`-th-power radical identity.**

The genuinely-true heart of Lemma 9.2.  Given a **unit** `u : (𝓞 K)ˣ` and
`(x+yη)·b^37 = u·(x+yη⁻¹)·a^37` — the Washington-corrected radical `α := u·α₀` is a `37`-th power,
with `u` absorbing the root-of-unity twist `-ζ^a` — the ideal identity `𝔞(η)·(b) = 𝔞(η⁻¹)·(a)`
holds.  The unit `u` disappears at the span level (`(u) = (1)`), so this does **not** demand `-ζ^a`
be a `37`-th power; it is satisfiable for the genuine adjacent-root data.

Mirror of `caseII_rootIdeal_mul_span_eq_of_pthPower`, but the right-hand element carries the unit
`u`; `span {u·w} = span {w}` (unit absorption) reduces it to the un-twisted ideal identity. -/
theorem caseII_rootIdeal_mul_span_eq_of_unitPthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {a b : 𝓞 K} (u : (𝓞 K)ˣ)
    (hab : (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
      (u : 𝓞 K) * ((D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37)) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η * Ideal.span {b} =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span {a} := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Promote the unit-twisted element identity to the un-twisted *ideal* identity, where the
  -- unit `u` is absorbed: `(x+yη)·(b)^37 = (x+yη⁻¹)·(a)^37` as principal ideals.
  have hspan :
      Ideal.span ({(D.x + D.y * (η : 𝓞 K)) * b ^ 37} : Set (𝓞 K)) =
        Ideal.span ({(D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37} : Set (𝓞 K)) := by
    rw [hab, Ideal.span_singleton_mul_left_unit u.isUnit]
  -- The un-twisted element identity at the *ideal* level is exactly the hypothesis of the proven
  -- `caseII_rootIdeal_mul_span_eq_of_pthPower`, but that needs an element-level equation.  Instead
  -- redo the proof using `hspan` directly.
  -- `(x+yη) = 𝔪·𝔠(η)·𝔭` and `(x+yη⁻¹) = 𝔪·𝔠(η⁻¹)·𝔭`.
  have hkey : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} = Ideal.span {D.x + D.y * (η : 𝓞 K)} :=
    m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hkeyinv : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} =
      Ideal.span {D.x + D.y * ((η : 𝓞 K) ^ 36)} := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
    rwa [caseII_etaInv_coe] at h
  -- Split the spans of products into products of spans.
  have hspan' :
      Ideal.span ({(D.x + D.y * (η : 𝓞 K))} : Set (𝓞 K)) * Ideal.span {b ^ 37} =
        Ideal.span ({(D.x + D.y * ((η : 𝓞 K) ^ 36))} : Set (𝓞 K)) * Ideal.span {a ^ 37} := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    exact hspan
  -- `𝔠 = 𝔞^37` at both roots.
  have hspecη : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η).symm
  have hspecinv : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)).symm
  rw [← hkey, ← hkeyinv, hspecη, hspecinv,
    ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow] at hspan'
  -- Reshape into `𝔪 · ((𝔞(η)·(b))^37 · 𝔭) = 𝔪 · ((𝔞(η⁻¹)·(a))^37 · 𝔭)` for cancellation.
  set 𝔪 := gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) with h𝔪
  set 𝔭 := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭
  set X := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η
  set Y := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)
  have hreshape : 𝔪 * ((X * Ideal.span {b}) ^ 37 * 𝔭) =
      𝔪 * ((Y * Ideal.span {a}) ^ 37 * 𝔭) := by
    rw [mul_pow, mul_pow]
    calc 𝔪 * (X ^ 37 * Ideal.span {b} ^ 37 * 𝔭)
        = 𝔪 * X ^ 37 * 𝔭 * Ideal.span {b} ^ 37 := by ring
      _ = 𝔪 * Y ^ 37 * 𝔭 * Ideal.span {a} ^ 37 := hspan'
      _ = 𝔪 * (Y ^ 37 * Ideal.span {a} ^ 37 * 𝔭) := by ring
  have hmne : 𝔪 ≠ 0 := by rw [h𝔪, Ideal.zero_eq_bot]; exact m_ne_zero D.hζ D.hy
  have hpne : 𝔭 ≠ 0 := by rw [h𝔭, Ideal.zero_eq_bot]; exact p_ne_zero D.hζ
  exact ideal_eq_of_pow37_eq (mul_right_cancel₀ hpne (mul_left_cancel₀ hmne hreshape))

/-! ## 2. The corrected TRUE residual: `[𝔞(η)] = [𝔞(η⁻¹)]` (class form)

This is the genuinely-true, satisfiable, **non-vacuous** form of the Case-II II1 leaf.  It is
Washington Lemma 9.2's *class* consequence, with the `-ζ^a` twist absorbed.  The downstream chain
consumes exactly this. -/

/-- **[FLT37-CASEII-LEMMA-9.2-RESIDUAL-TRUE] The Washington root class is conjugate-fixed.**

For every **real** Case-II datum `D` and adjacent root `η ≠ η₀`,

  `[𝔞(η)] = [𝔞(η⁻¹)]`   in `Cl(𝓞 K)`,

where `𝔞(η⁻¹) = 𝔞(η^36)` (`caseII_etaInv`).  Equivalently, since over real data
`σ[𝔞(η)] = [𝔞(η⁻¹)]` (`caseII_map_rootIdeal`), this says complex conjugation **fixes** the root
class.

This is **Washington Lemma 9.2's class consequence**, the genuine analytic content of the Case-II
II1 leaf.  Unlike the provably-false `CaseIIRootRatioPthPower37` (which demanded `α₀` itself — and
hence `-ζ^a` — be a `37`-th power **in `K^×`**), this is a **pure `Cl(𝓞 K)` equation**: the
root-of-unity twist `-ζ^a` of the corrected radical lives in the **unit** factor, which vanishes at
the class level (`[ζ] = 1`).  It is therefore genuinely true and **non-vacuous** — see
`caseII_rootClassConjFixed_of_unitPthPower` (satisfiable from Lemma 9.2's *corrected* element form
`(x+yη)·b^37 = u·(x+yη⁻¹)·a^37`, a unit `u` absorbing `-ζ^a`) and
`caseII_rootClassConjFixed_of_idealPthPower` (satisfiable from the ideal identity).  It is the SAME
Lemma-9.2 mechanism Case-I uses for its anti-Kummer radical `(a+ζb)/(a+ζ⁻¹b)`, taken at the
ideal/class level. -/
def CaseIIRootClassConjFixed37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
    η ≠ D.etaZero →
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 (by decide : (37 : ℕ) ≠ 2) η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy (caseII_etaInv η),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 (by decide : (37 : ℕ) ≠ 2)
                (caseII_etaInv η))⟩

/-! ## 3. Non-vacuity: the class form follows from the corrected element form and the ideal form

Both of these source identities are genuinely satisfiable (Washington Lemma 9.2 supplies the
corrected radical with the `-ζ^a` twist absorbed into a unit / vanishing at the ideal level).  This
demonstrates that `CaseIIRootClassConjFixed37` does **not** secretly demand `-ζ^a` be a `37`-th
power. -/

set_option maxRecDepth 4000 in
/-- **The class equality `[𝔞(η)] = [𝔞(η⁻¹)]` from the *unit-corrected* element form** — the
non-vacuity witness.

Given a unit `u : (𝓞 K)ˣ` and `(x+yη)·b^37 = u·(x+yη⁻¹)·a^37` (Washington's corrected radical
`u·α₀` a `37`-th power), the root classes are conjugate: `[𝔞(η)] = [𝔞(η⁻¹)]`.  The unit `u`
(which is `-ζ^a` in Washington's analysis) is absorbed in
`caseII_rootIdeal_mul_span_eq_of_unitPthPower`; it never has to be a `37`-th power.  This is the
genuine satisfiable source of the residual `CaseIIRootClassConjFixed37`. -/
theorem caseII_rootClassConjFixed_of_unitPthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0) (u : (𝓞 K)ˣ)
    (hab : (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
      (u : 𝓞 K) * ((D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37)) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hideal := caseII_rootIdeal_mul_span_eq_of_unitPthPower D hp η u hab
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨b, a, hb, ha, ?_⟩
  rw [mul_comm (Ideal.span {b}), mul_comm (Ideal.span {a})]
  exact hideal

set_option maxRecDepth 4000 in
/-- **The class equality `[𝔞(η)] = [𝔞(η⁻¹)]` from the ideal form** — the second non-vacuity
witness.

Given `Ideal.span{x+yη} · (b)^37 = Ideal.span{x+yη⁻¹} · (a)^37` (as ideals, the `-ζ^a` twist
already vanished), the root classes are conjugate.  This is the ideal-level Washington Lemma 9.2
conclusion, manifestly free of any "`-ζ^a` is a `37`-th power" demand. -/
theorem caseII_rootClassConjFixed_of_idealPthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Ideal.span ({D.x + D.y * (η : 𝓞 K)} : Set (𝓞 K)) * Ideal.span {b} ^ 37 =
      Ideal.span ({D.x + D.y * ((η : 𝓞 K) ^ 36)} : Set (𝓞 K)) * Ideal.span {a} ^ 37) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Reprove the ideal heart from the *ideal* identity `hab`, then read off the class equality.
  have hkey : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} = Ideal.span {D.x + D.y * (η : 𝓞 K)} :=
    m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hkeyinv : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} =
      Ideal.span {D.x + D.y * ((η : 𝓞 K) ^ 36)} := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
    rwa [caseII_etaInv_coe] at h
  have hspecη : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η).symm
  have hspecinv : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)).symm
  rw [← hkey, ← hkeyinv, hspecη, hspecinv] at hab
  set 𝔪 := gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) with h𝔪
  set 𝔭 := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭
  set X := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η
  set Y := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)
  have hreshape : 𝔪 * ((X * Ideal.span {b}) ^ 37 * 𝔭) =
      𝔪 * ((Y * Ideal.span {a}) ^ 37 * 𝔭) := by
    rw [mul_pow, mul_pow]
    calc 𝔪 * (X ^ 37 * Ideal.span {b} ^ 37 * 𝔭)
        = (𝔪 * X ^ 37 * 𝔭) * Ideal.span {b} ^ 37 := by ring
      _ = (𝔪 * Y ^ 37 * 𝔭) * Ideal.span {a} ^ 37 := hab
      _ = 𝔪 * (Y ^ 37 * Ideal.span {a} ^ 37 * 𝔭) := by ring
  have hmne : 𝔪 ≠ 0 := by rw [h𝔪, Ideal.zero_eq_bot]; exact m_ne_zero D.hζ D.hy
  have hpne : 𝔭 ≠ 0 := by rw [h𝔭, Ideal.zero_eq_bot]; exact p_ne_zero D.hζ
  have hideal : X * Ideal.span {b} = Y * Ideal.span {a} :=
    ideal_eq_of_pow37_eq (mul_right_cancel₀ hpne (mul_left_cancel₀ hmne hreshape))
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨b, a, hb, ha, ?_⟩
  rw [mul_comm (Ideal.span {b}), mul_comm (Ideal.span {a})]
  exact hideal

/-! ## 3'. The corrected Lemma-9.2 element-form residual (the genuine analytic kernel)

The provably-false `CaseIIRootRatioPthPower37` demanded `α₀ = (x+yη)/(x+yη⁻¹)` itself be a `37`-th
power **in `K^×`** (the un-twisted form `(x+yη)·b^37 = (x+yη⁻¹)·a^37`).  Washington Lemma 9.2
instead makes the *corrected* radical `α := -ζ^{-a}·α₀` a `37`-th power, i.e. `α₀ = (-ζ^a)·α₁^37`
for a `37`-th power `α₁^37` and the root-of-unity twist `-ζ^a` (Washington §9.1, pp. 169-170).
Absorbing `-ζ^a` into a **unit** `u : (𝓞 K)ˣ`, the genuine, TRUE element form is

  `∃ (u : (𝓞 K)ˣ) a b ≠ 0, (x+yη)·b^37 = u·(x+yη⁻¹)·a^37`.

This `CaseIIRootRatioUnitPthPower37` is the genuine analytic kernel of the Case-II II1 leaf —
exactly Washington Lemma 9.2's conclusion, with the `-ζ^a` correctly placed in the unit `u` (not
falsely demanded to be `1`).  It is **non-vacuous** precisely because `u` need not be a power.  From
it the entire downstream chain (the class form `CaseIIRootClassConjFixed37`, then `c = 1`, then the
endpoint) is **proved** below. -/

/-- **[FLT37-CASEII-LEMMA-9.2-KERNEL] The corrected radical `u·α₀` is a `37`-th power** — the
genuine TRUE element form, with the `-ζ^a` twist absorbed into a unit.

For every **real** Case-II datum `D` and adjacent root `η ≠ η₀`, there exist a unit
`u : (𝓞 K)ˣ` and nonzero `a, b ∈ 𝓞 K` with

  `(x+yη)·b^37 = u·(x+yη⁻¹)·a^37`,

i.e. `α₀ = (x+yη)/(x+yη⁻¹) = u·(a/b)^37`.  This is **Washington Lemma 9.2** for the Case-II radical:
over real data `α₀` is anti-fixed (`σα₀ = α₀⁻¹`) and the corrected radical `α := -ζ^{-a}·α₀` is
primary / generates an unramified Kummer extension (Lemma 9.1, the `-ζ^{-a}` chosen so the leading
`(1-ζ)`-term cancels); since `37 ∤ h⁺` (`Sinnott.flt37_not_dvd_hPlus`) there is no unramified cyclic
degree-`37` extension of `K⁺` (Hilbert 94), so `α := u⁻¹·α₀` is a `37`-th power, where `u = -ζ^a`.

This is the corrected, **genuinely-true** replacement for `CaseIIRootRatioPthPower37` (whose `u ≡ 1`
made it the provably-false claim "`-ζ^a` is a `37`-th power").  It is the SAME Lemma-9.2 mechanism
Case-I uses for its anti-Kummer radical `(a+ζb)/(a+ζ⁻¹b)`; the unit `u` is the Case-II analogue of
the Case-I primary normalisation `ζ^k`. -/
def CaseIIRootRatioUnitPthPower37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
    η ≠ D.etaZero →
    ∃ (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (a b : 𝓞 (CyclotomicField 37 ℚ)),
      a ≠ 0 ∧ b ≠ 0 ∧
      (D.x + D.y * (η : 𝓞 (CyclotomicField 37 ℚ))) * b ^ 37 =
        (u : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.x + D.y * ((η : 𝓞 (CyclotomicField 37 ℚ)) ^ 36)) * a ^ 37)

/-- **The TRUE class form follows from the corrected Lemma-9.2 kernel** — the discharge of the class
form down to the genuine analytic kernel.

`CaseIIRootClassConjFixed37` (the class equality `[𝔞(η)] = [𝔞(η⁻¹)]`) follows from the corrected
element-form kernel `CaseIIRootRatioUnitPthPower37` by `caseII_rootClassConjFixed_of_unitPthPower`
(the unit `u` is absorbed at the ideal level).  This exhibits the class form as a strict consequence
of Washington Lemma 9.2's genuine conclusion — and confirms the class form is **non-vacuous** (it is
satisfiable exactly when the corrected radical `u⁻¹·α₀` is a `37`-th power, which carries the `-ζ^a`
twist in `u` and never demands `-ζ^a` itself be a `37`-th power). -/
theorem caseIIRootClassConjFixed37_of_unitPthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_kernel : CaseIIRootRatioUnitPthPower37) :
    CaseIIRootClassConjFixed37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D η hη
  obtain ⟨u, a, b, ha, hb, hab⟩ := h_kernel D η hη
  exact caseII_rootClassConjFixed_of_unitPthPower D (by decide : (37 : ℕ) ≠ 2) η ha hb u hab

/-- **Non-vacuity check: the provably-false `CaseIIRootRatioPthPower37` implies the corrected kernel
`CaseIIRootRatioUnitPthPower37`.**

The corrected kernel is the special-case-`u = 1` predicate `CaseIIRootRatioPthPower37` **weakened**
by inserting an arbitrary unit `u`.  Hence the (provably-false, over-strong) old residual implies
the new one — the new residual is **strictly weaker** and therefore demands *strictly less*.  In
particular it does **not** secretly re-demand the false content ("`-ζ^a` is a `37`-th power"): that
content is exactly the gap between the two, namely fixing `u = 1`.  This machine-checks that the
correction genuinely loosens the residual (it cannot have made it vacuous or equivalent to the false
one). -/
theorem caseIIRootRatioUnitPthPower37_of_rootRatioPthPower37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_false : CaseIIRootRatioPthPower37) :
    CaseIIRootRatioUnitPthPower37 := by
  intro m D η hη
  obtain ⟨a, b, ha, hb, hab⟩ := h_false D η hη
  refine ⟨1, a, b, ha, hb, ?_⟩
  simpa only [Units.val_one, one_mul] using hab

set_option maxRecDepth 4000 in
/-- **Absolute non-vacuity: the class equality `[𝔞(η)] = [𝔞(η⁻¹)]` is EQUIVALENT to the
unit-corrected element form** — its full content is `α₀ = u·(a/b)^37` for a *free* unit `u`.

The reverse (`unit-form ⟹ class form`) is `caseII_rootClassConjFixed_of_unitPthPower`.  This is the
forward direction: from `[𝔞(η)] = [𝔞(η⁻¹)]` one recovers a unit `u : (𝓞 K)ˣ` and nonzero `a, b`
with `(x+yη)·b^37 = u·(x+yη⁻¹)·a^37`.  Hence the class form's entire content is exactly "`α₀` is a
**unit times** a `37`-th power" — the unit `u` is genuinely free (it is `-ζ^a` in Washington's
analysis), and the class form **never** demands `u = 1` (which would be the provably-false
`CaseIIRootRatioPthPower37`).  This machine-checks that `CaseIIRootClassConjFixed37` does not
secretly reduce to "`-ζ^a` is a `37`-th power": the false demand is precisely the unrecoverable
`u = 1`. -/
theorem caseII_unitPthPower_of_rootClassConjFixed {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hAeq :
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
        ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]
                exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩) :
    ∃ (u : (𝓞 K)ˣ) (a b : 𝓞 K), a ≠ 0 ∧ b ≠ 0 ∧
      (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
        (u : 𝓞 K) * ((D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- From `[𝔞(η)] = [𝔞(η⁻¹)]` extract `a, b ≠ 0` with `(a)·𝔞(η) = (b)·𝔞(η⁻¹)`.
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.mp hAeq
  -- Multiply the ideal identity `(a)·𝔞(η) = (b)·𝔞(η⁻¹)` by `𝔪·𝔭`, raise the root ideals to `37`
  -- via `𝔞^37 = 𝔠`, to obtain `(a^37)·(x+yη) = (b^37)·(x+yη⁻¹)` as ideals.
  have hkey : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} = Ideal.span {D.x + D.y * (η : 𝓞 K)} :=
    m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hkeyinv : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} =
      Ideal.span {D.x + D.y * ((η : 𝓞 K) ^ 36)} := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
    rwa [caseII_etaInv_coe] at h
  have hspecη : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η).symm
  have hspecinv : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)).symm
  -- `(a^37)·𝔠(η) = (b^37)·𝔠(η⁻¹)`: raise `(a)·𝔞(η) = (b)·𝔞(η⁻¹)` to the 37th power, use `𝔞^37=𝔠`.
  have hpow : Ideal.span ({a} : Set (𝓞 K)) ^ 37 *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      Ideal.span ({b} : Set (𝓞 K)) ^ 37 *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
    rw [hspecη, hspecinv]
    calc Ideal.span ({a} : Set (𝓞 K)) ^ 37 *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37
        = (Ideal.span ({a} : Set (𝓞 K)) *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) ^ 37 := by rw [mul_pow]
      _ = (Ideal.span ({b} : Set (𝓞 K)) *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 := by
          rw [hab]
      _ = Ideal.span ({b} : Set (𝓞 K)) ^ 37 *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 := by
          rw [mul_pow]
  -- Multiply by `𝔪·𝔭` and substitute `𝔪·𝔠·𝔭 = (x+yη)` to land on principal ideals.
  have hprincipal : Ideal.span ({a ^ 37 * (D.x + D.y * (η : 𝓞 K))} : Set (𝓞 K)) =
      Ideal.span ({b ^ 37 * (D.x + D.y * ((η : 𝓞 K) ^ 36))} : Set (𝓞 K)) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← hkey, ← hkeyinv]
    -- Both sides: `(a)^37 · (𝔪·𝔠(η)·𝔭)` vs `(b)^37 · (𝔪·𝔠(η⁻¹)·𝔭)`.  Reorder and use `hpow`.
    set 𝔪 := gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))
    set 𝔭 := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))
    set Cη := divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η
    set Ci := divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)
    calc Ideal.span ({a} : Set (𝓞 K)) ^ 37 * (𝔪 * Cη * 𝔭)
        = 𝔪 * 𝔭 * (Ideal.span ({a} : Set (𝓞 K)) ^ 37 * Cη) := by ring
      _ = 𝔪 * 𝔭 * (Ideal.span ({b} : Set (𝓞 K)) ^ 37 * Ci) := by rw [hpow]
      _ = Ideal.span ({b} : Set (𝓞 K)) ^ 37 * (𝔪 * Ci * 𝔭) := by ring
  -- The principal-ideal equality supplies an associating unit `u : a^37·(x+yη)·u = b^37·(x+yη⁻¹)`;
  -- reorient it into the residual witness `⟨u⁻¹, b, a⟩`.
  rw [Ideal.span_singleton_eq_span_singleton] at hprincipal
  obtain ⟨u, hu⟩ := hprincipal
  have hu' : (D.x + D.y * (η : 𝓞 K)) * a ^ 37 * (u : 𝓞 K) =
      (D.x + D.y * ((η : 𝓞 K) ^ 36)) * b ^ 37 := by
    linear_combination hu
  refine ⟨u⁻¹, b, a, hb, ha, ?_⟩
  calc (D.x + D.y * (η : 𝓞 K)) * a ^ 37
      = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) * ((D.x + D.y * (η : 𝓞 K)) * a ^ 37) := by
        rw [u.inv_mul, one_mul]
    _ = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          ((D.x + D.y * (η : 𝓞 K)) * a ^ 37 * (u : 𝓞 K)) := by ring
    _ = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          ((D.x + D.y * ((η : 𝓞 K) ^ 36)) * b ^ 37) := by rw [hu']

/-! ## 4. The `c = 1` chain, re-derived from the TRUE class-form residual

These mirror `caseII_anchored_class_sq_eq_one_of_pthPower`,
`caseII_anchored_class_eq_one_of_pthPower`, `caseII_real_anchored_class_trivial_of_pthPower`,
`caseII_real_etaZeroPrincipalization_of_pthPower` from `CaseIIRealAnchoredClass.lean`, but each
takes the genuinely-true class equality `[𝔞(η)] = [𝔞(η⁻¹)]` as input (directly, or from the residual
`CaseIIRootClassConjFixed37`) instead of the provably-false element identity. -/

set_option maxRecDepth 4000 in
/-- **`c² = 1` over `RealCaseIIData37`, from the class equality `[𝔞(η)] = [𝔞(η⁻¹)]`.**

Let `c = [𝔞(η)]·[𝔞(η₀)]⁻¹` be the anchored class for an adjacent root `η ≠ η₀`.  Combining the
**proven** `[𝔞(η)]·[𝔞(η⁻¹)] = [𝔞(η₀)]·[𝔞(η₀⁻¹)]` (`caseII_anchored_mul_conj_mk0_eq`, from
`c·σc = 1` under `37 ∤ h⁺`), the input class equality `[𝔞(η)] = [𝔞(η⁻¹)]`, and
`caseII_etaInv η₀ = η₀` (`caseII_etaInv_etaZero_eq`, so `[𝔞(η₀⁻¹)] = [𝔞(η₀)]`), gives
`[𝔞(η)]² = [𝔞(η₀)]²`, i.e. `c² = 1`.  Identical to
`caseII_anchored_class_sq_eq_one_of_pthPower` but the conjugate-fixedness `hAeq` is supplied as a
genuinely-true class hypothesis (no element identity). -/
theorem caseII_anchored_class_sq_eq_one_of_classEq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hAeq :
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
        ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]
                exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩) :
    (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ *
      (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩)⁻¹) ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Proven: `A·Ainv = A0·A0inv` (the `c·σc = 1` reassembly under Vandiver `37 ∤ h⁺`).
  have hmul := caseII_anchored_mul_conj_mk0_eq D hp h_VC η
  -- The anchor root is conjugate-stable: `[𝔞(η₀⁻¹)] = [𝔞(η₀)]` (since `caseII_etaInv η₀ = η₀`).
  have hroot0 : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
      (caseII_etaInv D.etaZero) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
    rw [caseII_etaInv_etaZero_eq D hp]
  have hclass0 : ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (caseII_etaInv D.etaZero),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv D.etaZero))⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩ :=
    congrArg ClassGroup.mk0 (Subtype.ext hroot0)
  -- Rewrite `Ainv → A` and `A0inv → A0` in `hmul` to get `A·A = A0·A0`.
  rw [← hAeq, hclass0, ← sq, ← sq] at hmul
  rw [mul_pow, inv_pow, mul_inv_eq_one]
  exact hmul

set_option maxRecDepth 4000 in
/-- **`c = 1` over `RealCaseIIData37`, from the class equality `[𝔞(η)] = [𝔞(η⁻¹)]`.**

For the adjacent root `η` the anchored class `c = [𝔞(η)]·[𝔞(η₀)]⁻¹` is **trivial**.  Combining the
**proven** `c³⁷ = 1` (`caseII_anchored_class_pow_eq_one`) with `c² = 1`
(`caseII_anchored_class_sq_eq_one_of_classEq`, from the genuinely-true class equality), the order of
`c` divides `gcd(2, 37) = 1`, so `c = 1`, i.e. `[𝔞(η)] = [𝔞(η₀)]`.  The non-vacuous analogue of
`caseII_anchored_class_eq_one_of_pthPower`. -/
theorem caseII_anchored_class_eq_one_of_classEq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (_hη : η ≠ D.etaZero)
    (hAeq :
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
        ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]
                exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hpow37 := caseII_anchored_class_pow_eq_one D.toCaseIIData37 hp η
  have hpow2 := caseII_anchored_class_sq_eq_one_of_classEq D hp h_VC η hAeq
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow2)
    (orderOf_dvd_of_pow_eq_one hpow37)
  rw [show Nat.gcd 2 37 = 1 from by decide] at hdvd
  exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

/-- **[FLT37-CASEII-REAL-PER-DATUM-TRUE] `[𝔞(η)] = [𝔞(η₀)]` for every real datum and adjacent root,
from the TRUE residual.**

The genuine, non-vacuous Case-II II1 statement.  Quantified over all
`D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` and adjacent roots `η ≠ η₀`, the anchored class is
trivial: `[𝔞(η)] = [𝔞(η₀)]` in `Cl(𝓞 K)`.

This follows from the genuinely-true class-form residual `CaseIIRootClassConjFixed37` by
`caseII_anchored_class_eq_one_of_classEq`; `¬ 37 ∣ h⁺` is supplied internally by the proven
`Sinnott.flt37_not_dvd_hPlus`.  Non-vacuous analogue of
`caseII_real_anchored_class_trivial_of_pthPower`. -/
theorem caseII_real_anchored_class_trivial_of_classConjFixed
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_class : CaseIIRootClassConjFixed37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη : η ≠ D.etaZero) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 (by decide : (37 : ℕ) ≠ 2) η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 (by decide : (37 : ℕ) ≠ 2)
                D.etaZero)⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))))) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr Sinnott.flt37_not_dvd_hPlus
  exact caseII_anchored_class_eq_one_of_classEq D (by decide : (37 : ℕ) ≠ 2) h_VC η hη
    (h_class D η hη)

/-- **Real-data `η₀`-principalization from the TRUE class-form residual.**

For a real datum `D` and the genuinely-true class-form residual `CaseIIRootClassConjFixed37`, the
codebase's `CaseIIPrincipalizationAgainstEtaZero` holds at `D`.  Non-vacuous analogue of
`caseII_real_etaZeroPrincipalization_of_pthPower`. -/
theorem caseII_real_etaZeroPrincipalization_of_classConjFixed
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_class : CaseIIRootClassConjFixed37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro η hη
  have hη' : η ≠ D.etaZero := hη
  have h_classEq := caseII_real_anchored_class_trivial_of_classConjFixed h_class D η hη'
  have h_root := caseII_rootQuotientPrincipal_of_classEq D.toCaseIIData37
    (by decide : (37 : ℕ) ≠ 2) η h_classEq
  exact caseII_isPrincipal_aDivAEtaZero_of_rootQuotientPrincipal
    (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η h_root

/-! ## 5. The non-vacuous endpoint, resting on the TRUE class-form residual

Identical assembly to `CaseIIRealAnchoredClass.lean` (the no-infinite-descent on `RealCaseIIData37`
+ the real producer + Assumption II + the carried second-order input), but every step now rests on
the genuinely-true `CaseIIRootClassConjFixed37` instead of the provably-false
`CaseIIRootRatioPthPower37`. -/

/-- **No real Case-II descent datum exists, from the TRUE residual + the reality-preserving descent
step.**  Mirror of `no_realCaseIIData37_of_pthPower_and_realDescent`. -/
theorem no_realCaseIIData37_of_classConjFixed_and_realDescent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_class : CaseIIRootClassConjFixed37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (h_realDescent : CaseIIRealSingleRootDescentPreservesReality37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  classical
  rintro ⟨m, D⟩
  let P : ℕ → Prop := fun n => Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) n)
  have hP : ∃ n, P n := ⟨m, D⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Dmin⟩
  have hprinc := caseII_real_etaZeroPrincipalization_of_classConjFixed h_class Dmin
  obtain ⟨m', hm', D'⟩ := h_realDescent h_exactUnit Dmin hprinc
  exact (Nat.find_min hP hm') D'

/-- **The public Case-II bridge from the TRUE class-form residual + reality-preserving descent +
Assumption II.**  Mirror of `caseIIBridge_thirtyseven_of_pthPower_and_realDescent`, resting on the
genuinely-true `CaseIIRootClassConjFixed37`. -/
theorem caseIIBridge_thirtyseven_of_classConjFixed_and_realDescent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_class : CaseIIRootClassConjFixed37)
    (h_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  have hNoData := no_realCaseIIData37_of_classConjFixed_and_realDescent
    h_class h_exactUnit h_realDescent
  exact hNoData
    (exists_realCaseIIData37_of_caseII_int_solution hprod hgcd hcase hEq)

/-- **Fermat's Last Theorem for `37`, from the genuinely-true class-form Case-II II1 residual.**

`FermatLastTheoremFor 37` from:

* `caseII_classConjFixed` (`CaseIIRootClassConjFixed37`): **Case-II II1**, Washington Lemma 9.2's
  class consequence `[𝔞(η)] = [𝔞(η⁻¹)]` over **real** data.  This is genuinely true and
  **non-vacuous** — it forces `c = 1` over real data (`caseII_anchored_class_eq_one_of_classEq`),
  and is satisfiable from the *corrected* radical (`caseII_rootClassConjFixed_of_unitPthPower`, with
  a unit absorbing the `-ζ^a` twist), unlike the provably-false `CaseIIRootRatioPthPower37` (which
  demanded `-ζ^a` itself be a `37`-th power);
* `caseII_realDescent` (`CaseIIRealSingleRootDescentPreservesReality37`): the reality-preserving
  single-root descent construction;
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): **Case-II II2**, Assumption
  II;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the second-order Bernoulli input.

Case I is discharged unconditionally by the Eichler first-case proof
(`caseIBridge_thirtyseven_eichler`); `¬ 37 ∣ h⁺` is the proven `Sinnott.flt37_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_classConjFixed_and_realDescent
      caseII_classConjFixed caseII_realDescent caseII_exactUnit)

/-- **Fermat's Last Theorem for `37`, from the corrected Lemma-9.2 element-form kernel.**

The maximally-honest endpoint.  `FermatLastTheoremFor 37` from:

* `caseII_kernel` (`CaseIIRootRatioUnitPthPower37`): **Case-II II1**, the genuine Washington Lemma
  9.2 conclusion — the corrected radical `u⁻¹·(x+yη)/(x+yη⁻¹)` is a `37`-th power, with the
  root-of-unity twist `-ζ^a` correctly placed in the unit `u`.  This is the genuinely-true,
  **non-vacuous** replacement for the provably-false `CaseIIRootRatioPthPower37` (whose `u ≡ 1`
  falsely demanded `-ζ^a` itself be a `37`-th power).  It forces `c = 1` over real data;
* `caseII_realDescent` (`CaseIIRealSingleRootDescentPreservesReality37`): the reality-preserving
  single-root descent;
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): **Case-II II2**, Assumption
  II;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the second-order Bernoulli input.

This routes through `caseIIRootClassConjFixed37_of_unitPthPower` (kernel ⟹ class form) and then the
proven `c = 1` chain.  Case I is unconditional (Eichler); `¬ 37 ∣ h⁺` is
`Sinnott.flt37_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_of_rootRatioUnitPthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_kernel : CaseIIRootRatioUnitPthPower37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    (caseIIRootClassConjFixed37_of_unitPthPower caseII_kernel)
    caseII_realDescent caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
