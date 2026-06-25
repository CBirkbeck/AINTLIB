import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificChain

/-!
# [II1-TARGET-AUDIT] Complex conjugation on the Case-II Washington ideals

This file audits the literal target of the Case-II II1 step, following the
2026-05-27-3 expert review. The point is to confirm that, **even for a datum with real
`x, y`** (`σ x = x`, `σ y = y`), complex conjugation `σ` sends the anchored quotient
`𝔞(η)/𝔞₀` to `𝔞(η⁻¹)/𝔞(η₀⁻¹)`, which is **not** `𝔞(η)/𝔞₀`. Consequently a *real*
generator of the raw anchored quotient cannot exist (a real generator forces ideal-level
`σ`-stability), so the structures `CaseIIWashingtonFixedIntegralGenerator37` and
`CaseIIWashingtonRootGenerator37` — both demanding a `σ`-fixed generator of the raw quotient
— are unsatisfiable as stated.

The chain is:
1. `caseII_complexConj_x_add_y_mul`: `σ(x + y·w) = x + y·σ(w)` for real `x, y` (this file).
2. `σ(η) = η⁻¹` for `η` a `37`-th root of unity (this file).
3. `σ(𝔦(η)) = 𝔦(η⁻¹)`, `σ(𝔪) = 𝔪`, `σ(𝔭) = 𝔭` ⟹ `σ(𝔠(η)) = 𝔠(η⁻¹)` ⟹ (p-th-root
   uniqueness) `σ(𝔞(η)) = 𝔞(η⁻¹)`  [to come].

## References
* Washington GTM 83 §9.1 ("`B₋ₐ` is the complex conjugate of `Bₐ`").
* Expert review 2026-05-27-3, "check the literal II1 target".
-/

@[expose] public section

open NumberField IsCyclotomicExtension NumberField.IsCMField Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Reality pushes through `x + y·w`.** If `x` and `y` are fixed by complex conjugation,
then `σ(x + y·w) = x + y·σ(w)` for any `w ∈ 𝓞 K`. This isolates the content of the
conjugation action to the action on the root-of-unity factor `w = η`. -/
theorem caseII_ringOfIntegersComplexConj_x_add_y_mul
    {x y : 𝓞 K} (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y) (w : 𝓞 K) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (x + y * w) =
      x + y * NumberField.IsCMField.ringOfIntegersComplexConj K w := by
  rw [map_add, map_mul, hx, hy]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Complex conjugation inverts a `37`-th root of unity.** If `η^37 = 1` then
`σ(η) = η^36 = η⁻¹`. This is the content isolated by
`caseII_ringOfIntegersComplexConj_x_add_y_mul`: combined with reality of `x, y` it gives
`σ(x + y·η) = x + y·η⁻¹`, Washington's `B₋ₐ = conj Bₐ`. -/
theorem caseII_ringOfIntegersComplexConj_root_of_unity
    {η : 𝓞 K} (hη : η ^ 37 = 1) :
    NumberField.IsCMField.ringOfIntegersComplexConj K η = η ^ 36 := by
  have h36 : η * η ^ 36 = 1 := by linear_combination hη
  set u : (𝓞 K)ˣ := ⟨η, η ^ 36, h36, by rw [mul_comm]; exact h36⟩
  have htor : u ∈ NumberField.Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨37, by norm_num, ?_⟩)
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hη
  have hconj_unit : NumberField.IsCMField.unitsComplexConj K u = u⁻¹ := by
    simpa using NumberField.IsCMField.unitsComplexConj_torsion K ⟨u, htor⟩
  exact Units.ext_iff.1 hconj_unit

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`σ(𝔦(η)) = 𝔦(η⁻¹)` at the principal-ideal level.** For real `x, y`, complex
conjugation sends the principal ideal `(x + y·η)` to `(x + y·η³⁶) = (x + y·η⁻¹)`. -/
theorem caseII_map_span_x_add_y_eta
    {x y : 𝓞 K} (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y)
    {η : 𝓞 K} (hη : η ^ 37 = 1) :
    (Ideal.span ({x + y * η} : Set (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({x + y * η ^ 36} : Set (𝓞 K)) := by
  have hfe : (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
      (x + y * η) = x + y * η ^ 36 := by
    have h := caseII_ringOfIntegersComplexConj_x_add_y_mul (K := K) hx hy η
    rwa [caseII_ringOfIntegersComplexConj_root_of_unity hη] at h
  rw [Ideal.map_span, Set.image_singleton, hfe]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- `σ` fixes the principal ideal of a real element. -/
theorem caseII_map_span_singleton_real {w : 𝓞 K}
    (hw : NumberField.IsCMField.ringOfIntegersComplexConj K w = w) :
    (Ideal.span ({w} : Set (𝓞 K))).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({w} : Set (𝓞 K)) := by
  rw [Ideal.map_span, Set.image_singleton,
    show (ringOfIntegersComplexConj K).toRingEquiv.toRingHom w = w from hw]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`σ(𝔪) = 𝔪`.** For real `x, y`, complex conjugation fixes `𝔪 = gcd((x),(y))`. -/
theorem caseII_map_gcd_span_real {x y : 𝓞 K}
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y) :
    (gcd (Ideal.span ({x} : Set (𝓞 K))) (Ideal.span ({y} : Set (𝓞 K)))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      gcd (Ideal.span ({x} : Set (𝓞 K))) (Ideal.span ({y} : Set (𝓞 K))) := by
  rw [Ideal.gcd_eq_sup, Ideal.map_sup, caseII_map_span_singleton_real hx,
    caseII_map_span_singleton_real hy, ← Ideal.gcd_eq_sup]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`σ(𝔭) = 𝔭`.** Complex conjugation fixes `𝔭 = (ζ - 1)`: `σ(ζ-1) = ζ³⁶-1 = -ζ³⁶·(ζ-1)`,
an associate of `ζ-1`. -/
theorem caseII_map_zetaSubOne_span {ζ : 𝓞 K} (hζ37 : ζ ^ 37 = 1) :
    (Ideal.span ({ζ - 1} : Set (𝓞 K))).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({ζ - 1} : Set (𝓞 K)) := by
  have hfe : (ringOfIntegersComplexConj K).toRingEquiv.toRingHom (ζ - 1) = ζ ^ 36 - 1 :=
    show NumberField.IsCMField.ringOfIntegersComplexConj K (ζ - 1) = ζ ^ 36 - 1 by
      rw [map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity hζ37]
  rw [Ideal.map_span, Set.image_singleton, hfe, Ideal.span_singleton_eq_span_singleton]
  -- Associated (ζ^36 - 1) (ζ - 1): the unit u = -ζ gives (ζ^36-1)·(-ζ) = ζ - ζ^37 = ζ - 1.
  exact ⟨⟨-ζ, -(ζ ^ 36), by linear_combination hζ37, by linear_combination hζ37⟩,
    by linear_combination -hζ37⟩

/-- The inverse root `η ↦ η⁻¹ = η³⁶` as a member of `nthRootsFinset 37 1`. Complex
conjugation maps the index-`η` Washington data to the index-`η⁻¹` data. -/
noncomputable def caseII_etaInv (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    nthRootsFinset 37 (1 : 𝓞 K) := by
  refine ⟨(η : 𝓞 K) ^ 36, ?_⟩
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  rw [mem_nthRootsFinset (by norm_num), ← pow_mul,
    show 36 * 37 = 37 * 36 from by norm_num, pow_mul, h37, one_pow]

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
@[simp] theorem caseII_etaInv_coe (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_etaInv η : 𝓞 K) = (η : 𝓞 K) ^ 36 := rfl

/-- **`σ(𝔠(η)) = 𝔠(η⁻¹)`.** For a Case-II datum with real `x, y`, complex conjugation sends the
Washington ideal `𝔠(η)` to `𝔠(η⁻¹)`. Proof: apply `σ` to `𝔪·𝔠(η)·𝔭 = (x+yη)`, use `σ𝔪 = 𝔪`,
`σ𝔭 = 𝔭`, `σ(x+yη) = (x+yη⁻¹) = 𝔪·𝔠(η⁻¹)·𝔭`, and cancel `𝔪`, `𝔭` (nonzero, Dedekind domain). -/
theorem caseII_map_c {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K D.x = D.x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K D.y = D.y)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37z : (D.hζ.toInteger) ^ 37 = 1 :=
    D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have h37e : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have hkey := m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hkeyinv := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
  rw [caseII_etaInv_coe] at hkeyinv
  have hmap := congrArg
    (Ideal.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) hkey
  rw [Ideal.map_mul, Ideal.map_mul, caseII_map_gcd_span_real hx hy,
    caseII_map_zetaSubOne_span h37z, caseII_map_span_x_add_y_eta hx hy h37e,
    ← hkeyinv] at hmap
  have hpne : Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} ≠ 0 := p_ne_zero D.hζ
  have hmne : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) ≠ 0 := m_ne_zero D.hζ D.hy
  exact mul_left_cancel₀ hmne (mul_right_cancel₀ hpne hmap)

set_option maxRecDepth 1000 in
/-- **`σ(𝔞(η)) = 𝔞(η⁻¹)`** — the audit's central conjugation identity. For a Case-II datum with
real `x, y`, complex conjugation sends the Washington root ideal `𝔞(η)` to `𝔞(η⁻¹)`. Since for the
adjacent roots `η ∈ {η₀ζ, η₀ζ²}` one has `η⁻¹ ≠ η`, the anchored quotient `𝔞(η)/𝔞₀` is **not**
fixed by `σ` as an ideal — so it admits no real (σ-fixed) generator, confirming that
`CaseIIWashingtonFixedIntegralGenerator37` / `CaseIIWashingtonRootGenerator37` are unsatisfiable as
stated (the reviewer's 2026-05-27-3 sharpening). Proof: `σ` of `(𝔞 η)^37 = 𝔠(η)` gives
`(σ𝔞(η))^37 = 𝔠(η⁻¹) = (𝔞(η⁻¹))^37`, then p-th-root uniqueness in the Dedekind ideal monoid. -/
theorem caseII_map_rootIdeal {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K D.x = D.x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K D.y = D.y)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hspec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η
  have hspecinv :=
    root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)
  have h1 : ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ 37 =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 := by
    rw [← Ideal.map_pow, hspec, caseII_map_c D hp hx hy η]
    exact hspecinv.symm
  have hAB := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h1.dvd
  have hBA := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h1.symm.dvd
  exact le_antisymm (Ideal.dvd_iff_le.mp hBA) (Ideal.dvd_iff_le.mp hAB)

/-- **[REAL-CASEII-DATUM] Reality-restricted Case-II descent datum.** Washington's second-case
descent (GTM 83 §9.1 / Thm 9.4) runs only on data whose two main variables `x, y` are **real**
(`σx = x`, `σy = y`): rational at the base of the descent, and real (norm-like `ρ_aρ̄_a`,
`ρ_bρ̄_b`) after each step. The general `CaseIIData37` forgets this invariant, which is exactly why
the II1 real-generator target is unsatisfiable over it (`caseII_map_rootIdeal`: `σ(𝔞(η)) = 𝔞(η⁻¹)`,
so `𝔞(η)/𝔞₀` is not `σ`-stable). This wrapper records the invariant. (Reviewer 2026-05-27-3,
recommended option B.) -/
structure RealCaseIIData37 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] (m : ℕ)
    extends CaseIIData37 K m where
  x_real : NumberField.IsCMField.ringOfIntegersComplexConj K x = x
  y_real : NumberField.IsCMField.ringOfIntegersComplexConj K y = y

/-- For a real Case-II datum, complex conjugation sends `𝔞(η)` to `𝔞(η⁻¹)` (specialisation of
`caseII_map_rootIdeal` to `RealCaseIIData37`, where reality is part of the datum). -/
theorem RealCaseIIData37.map_rootIdeal {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) :=
  caseII_map_rootIdeal D.toCaseIIData37 hp D.x_real D.y_real η

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- The inverse-root map is an involution: `(η⁻¹)⁻¹ = η` (since `(η³⁶)³⁶ = η^{1296} = η`). -/
theorem caseII_etaInv_etaInv (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_etaInv (caseII_etaInv η) = η := by
  apply Subtype.ext
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  simp only [caseII_etaInv_coe, ← pow_mul]
  rw [show (36 * 36 : ℕ) = 37 * 35 + 1 from by norm_num, pow_add, pow_mul, h37, one_pow,
    pow_one, one_mul]

/-- **[II1-RESTATE] The σ-stable Washington object.** The product `𝔞(η)·𝔞(η⁻¹)` IS fixed by complex
conjugation (σ swaps the two factors, using `(η⁻¹)⁻¹ = η`). This is the correct σ-stable target for
the real-generator step — unlike the raw anchored quotient `𝔞(η)/𝔞₀`, which is sent to
`𝔞(η⁻¹)/𝔞(η₀⁻¹)`. The conjugate-paired generators of Washington §9.1 generate (a twist of) this
object, not the raw quotient. -/
theorem RealCaseIIData37.map_rootIdeal_mul_conj {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  rw [Ideal.map_mul, D.map_rootIdeal hp η, D.map_rootIdeal hp (caseII_etaInv η),
    caseII_etaInv_etaInv, mul_comm]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- The fraction-field conjugation `ringEquivOfRingEquiv σ` sends the coe of an ideal `𝔞` to the coe
of the conjugated ideal `𝔞.map σ`. (Gap lemma for the ClassGroup-σ naturality.) -/
theorem caseII_ringEquivOfRingEquiv_coeIdeal (𝔞 : Ideal (𝓞 K)) :
    FractionalIdeal.ringEquivOfRingEquiv (FractionRing (𝓞 K)) (FractionRing (𝓞 K))
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv
        (𝔞 : FractionalIdeal (𝓞 K)⁰ (FractionRing (𝓞 K))) =
      (𝔞.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ (FractionRing (𝓞 K))) := by
  ext z
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply, ← FractionalIdeal.mem_coe,
    FractionalIdeal.coe_mk, Submodule.mem_map]
  simp only [FractionalIdeal.mem_coeIdeal, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(NumberField.IsCMField.ringOfIntegersComplexConj K) a,
      Ideal.mem_map_of_mem _ ha,
      by simp only [Algebra.linearMap_apply,
        IsFractionRing.semilinearEquivOfRingEquiv_algebraMap, AlgEquiv.coe_ringEquiv]⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.surjective).mp hb
    exact ⟨algebraMap (𝓞 K) (FractionRing (𝓞 K)) a, ⟨a, ha, rfl⟩,
      by simp only [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]⟩

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Naturality of `ClassGroup.mk0` under complex conjugation.** `ClassGroup.mulEquiv σ` sends the
class `[𝔞]` to `[σ𝔞]`. Lets the integral `classGroup_mul_complexConj_eq_one_of_pow_of_VC` act on the
class `[𝔞(η)/𝔞₀]` via any integral representative — the bridge for the σ-stable real-generator
step. -/
theorem caseII_classGroup_conj_mk0 {𝔞 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) :
    ClassGroup.mulEquiv (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv
        (ClassGroup.mk0 ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞⟩) =
      ClassGroup.mk0 ⟨𝔞.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
        mem_nonZeroDivisors_iff_ne_zero.mpr ((map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞)⟩ := by
  have hmid : (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv (FractionRing (𝓞 K))
        (FractionRing (𝓞 K))
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv).toMulEquiv)
        (FractionalIdeal.mk0 (FractionRing (𝓞 K))
          ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞⟩) =
      FractionalIdeal.mk0 (FractionRing (𝓞 K))
        ⟨𝔞.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr ((map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞)⟩ := by
    apply Units.ext
    simp only [Units.coe_mapEquiv, FractionalIdeal.coe_mk0]
    exact caseII_ringEquivOfRingEquiv_coeIdeal 𝔞
  rw [RingEquiv.toMulEquiv_eq_coe] at hmid
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply, ClassGroup.equiv_mk0,
    QuotientGroup.congr_mk', hmid]
  rw [← ClassGroup.equiv_mk0, MulEquiv.symm_apply_apply]

set_option maxRecDepth 4000 in
omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`c · σc = 1` for any `p`-torsion class under Vandiver.** If `c ∈ ClassGroup (𝓞 K)` is
`37`-torsion and `37 ∤ h⁺` (`h_VC`), then `c · σc = 1` (`σ` = `ClassGroup.mulEquiv` of complex
conjugation). Proof: pick an integral representative `𝔞` of `c` (`ClassGroup.mk0_surjective`); then
`𝔞³⁷` is principal (`c³⁷ = 1`), so the repo's `classGroup_mul_complexConj_eq_one_of_pow_of_VC` gives
`[𝔞·σ𝔞] = 1`; by `mk0` multiplicativity and the naturality `caseII_classGroup_conj_mk0`,
`[𝔞·σ𝔞] = c · σc`. -/
theorem caseII_classGroup_mul_conj_eq_one
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (c : ClassGroup (𝓞 K)) (hc : c ^ 37 = 1) :
    c * ClassGroup.mulEquiv
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv c = 1 := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have h𝔞_nz : (I : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hpow_one : ClassGroup.mk0 (I ^ 37) = 1 := by rw [map_pow]; exact hc
  have hmem : ((I : Ideal (𝓞 K)) ^ 37) ∈ (Ideal (𝓞 K))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 37 h𝔞_nz)
  have hprinc : ((I : Ideal (𝓞 K)) ^ 37).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hmem,
      show (⟨(I : Ideal (𝓞 K)) ^ 37, hmem⟩ : (Ideal (𝓞 K))⁰) = I ^ 37 from
        Subtype.ext (SubmonoidClass.coe_pow I 37)]
    exact hpow_one
  obtain ⟨α, hα⟩ := hprinc.principal
  have hα_ne : α ≠ 0 := by
    rintro rfl
    rw [Set.singleton_zero, Submodule.span_zero] at hα
    exact (pow_ne_zero 37 h𝔞_nz) hα
  have hkey := classGroup_mul_complexConj_eq_one_of_pow_of_VC (p := 37) (K := K) h_VC
    (α := α) hα_ne h𝔞_nz hα.symm
  have hmnz : (I : Ideal (𝓞 K)).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
      ∈ (Ideal (𝓞 K))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr ((map_ne_bot_iff_complexConj K _).mpr h𝔞_nz)
  have hnat : ClassGroup.mulEquiv (ringOfIntegersComplexConj K).toRingEquiv (ClassGroup.mk0 I)
      = ClassGroup.mk0 ⟨(I : Ideal (𝓞 K)).map
          (ringOfIntegersComplexConj K).toRingEquiv.toRingHom, hmnz⟩ :=
    caseII_classGroup_conj_mk0 h𝔞_nz
  rw [hnat, ← map_mul]
  exact hkey

/-- The Washington ideal `𝔠(η)` is nonzero (from `𝔪·𝔠(η)·𝔭 = (x+yη) ≠ 0`). -/
theorem caseII_c_ne_bot {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ≠ ⊥ := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hc
  have hmcp := m_mul_c_mul_p hp D.hζ D.equation D.hy η
  simp only [hc, Ideal.mul_bot, Ideal.bot_mul] at hmcp
  exact x_plus_y_mul_ne_zero hp D.hζ D.equation D.hz η
    (Ideal.span_singleton_eq_bot.mp hmcp.symm)

/-- The Washington root ideal `𝔞(η)` is nonzero (from `𝔞(η)³⁷ = 𝔠(η) ≠ ⊥`). Needed to view
`[𝔞(η)]` as a `ClassGroup` element. -/
theorem caseII_rootIdeal_ne_bot {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ≠ ⊥ := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hbot
  refine caseII_c_ne_bot D hp η ?_
  have hspec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η
  rw [hbot] at hspec
  simpa using hspec.symm

set_option maxRecDepth 4000 in
/-- **`[𝔠(η₁)] = [𝔠(η₂)]` in the class group.** From `𝔪·𝔠(η)·𝔭 = (x+yη)` (principal) for each `η`,
`[𝔪]·[𝔠(η)]·[𝔭] = 1`, so `[𝔠(η)]` is independent of `η`. -/
theorem caseII_mk0_c_eq {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    ClassGroup.mk0 ⟨divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_c_ne_bot D hp η₁)⟩ =
      ClassGroup.mk0 ⟨divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_c_ne_bot D hp η₂)⟩ := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  have key : ∀ η : nthRootsFinset 37 (1 : 𝓞 K),
      ClassGroup.mk0 ⟨gcd (Ideal.span {D.x}) (Ideal.span {D.y}),
          mem_nonZeroDivisors_iff_ne_zero.mpr (m_ne_zero D.hζ D.hy)⟩ *
        ClassGroup.mk0 ⟨divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]; exact caseII_c_ne_bot D hp η)⟩ *
        ClassGroup.mk0 ⟨Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)},
          mem_nonZeroDivisors_iff_ne_zero.mpr (p_ne_zero D.hζ)⟩ = 1 := by
    intro η
    rw [← map_mul, ← map_mul]
    exact (ClassGroup.mk0_eq_one_iff _).mpr
      ⟨⟨_, m_mul_c_mul_p hp D.hζ D.equation D.hy η⟩⟩
  exact mul_left_cancel (mul_right_cancel ((key η₁).trans (key η₂).symm))

set_option maxRecDepth 4000 in
/-- **The anchored-quotient class `[𝔞(η)]·[𝔞(η₀)]⁻¹` is `37`-torsion.** (`c³⁷ = [𝔞(η)³⁷]·[𝔞(η₀)³⁷]⁻¹
= [𝔠(η)]·[𝔠(η₀)]⁻¹ = 1` by `caseII_mk0_c_eq`.) This is the `p`-torsion hypothesis feeding
`caseII_classGroup_mul_conj_eq_one`. -/
theorem caseII_anchored_class_pow_eq_one {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp η)⟩ *
      (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp D.etaZero)⟩)⁻¹) ^ 37
      = 1 := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  have ha : ∀ η : nthRootsFinset 37 (1 : 𝓞 K),
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp η)⟩ ^ 37 =
      ClassGroup.mk0 ⟨divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_c_ne_bot D hp η)⟩ := by
    intro η
    rw [← map_pow]
    congr 1
    exact Subtype.ext (by
      rw [SubmonoidClass.coe_pow]
      exact root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η)
  rw [mul_pow, ha, inv_pow, ha, caseII_mk0_c_eq D hp η D.etaZero, mul_inv_cancel]

set_option maxRecDepth 4000 in
/-- **The anchored quotient class is fixed under `c ↦ c·σc`.** Combining the `37`-torsion of the
anchored class (`caseII_anchored_class_pow_eq_one`) with `caseII_classGroup_mul_conj_eq_one`
(Vandiver): for the anchored quotient class `c = [𝔞(η)]·[𝔞(η₀)]⁻¹`, `c · σc = 1`. Since
`σc = [𝔞(η⁻¹)]·[𝔞(η₀⁻¹)]⁻¹` (naturality + `map_rootIdeal`), this is the σ-stability of the class —
the input to `isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC` for the real generator. -/
theorem caseII_anchored_classGroup_mul_conj_eq_one {m : ℕ} (D : CaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp η)⟩ *
      (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp D.etaZero)⟩)⁻¹) *
      ClassGroup.mulEquiv (ringOfIntegersComplexConj K).toRingEquiv
        (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp η)⟩ *
          (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D hp D.etaZero)⟩)⁻¹) = 1 :=
  caseII_classGroup_mul_conj_eq_one h_VC _ (caseII_anchored_class_pow_eq_one D hp η)

omit [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- Abelian-group rearrangement: `a·b⁻¹·(a'·b'⁻¹) = 1 ⟹ a·a' = b·b'`. Stated abstractly so the
`group` normalization runs on opaque atoms (cheap), letting the caller close the proof-irrelevant
`ClassGroup.mk0 ⟨_,_⟩` atom mismatch by `exact` (definitional, proof-irrelevant). -/
theorem caseII_commGroup_rearrange {G : Type*} [CommGroup G] {a b a' b' : G}
    (h : a * b⁻¹ * (a' * b'⁻¹) = 1) : a * a' = b * b' := by
  refine mul_inv_eq_one.mp ?_
  rw [mul_inv, ← h]
  ac_rfl

set_option maxRecDepth 4000 in
/-- **`[𝔞(η)]·[𝔞(η⁻¹)] = [𝔞(η₀)]·[𝔞(η₀⁻¹)]` (mk0-product form).** Rearranging `c·σc=1` with `σc`
expanded by naturality + `map_rootIdeal`. The σ-stable anchored ratio is principal — INTEGRAL,
no fractional-ideal conjugation. -/
theorem caseII_anchored_mul_conj_mk0_eq {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ *
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩ =
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩ *
      ClassGroup.mk0
        ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv D.etaZero))⟩ := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hcc := caseII_anchored_classGroup_mul_conj_eq_one D.toCaseIIData37 hp h_VC η
  rw [map_mul, map_inv, caseII_classGroup_conj_mk0, caseII_classGroup_conj_mk0] at hcc
  · simp only [RealCaseIIData37.map_rootIdeal D hp η,
      RealCaseIIData37.map_rootIdeal D hp D.etaZero] at hcc
    exact caseII_commGroup_rearrange hcc
  · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero
  · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η

end BernoulliRegular.FLT37.LehmerVandiver.CaseII

end
