import BernoulliRegular.Thaine.UnitsComplexConjBridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.CharacterIdentification
import BernoulliRegular.UnitQuotient.ModPReduction
import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ModPRepresentation
import BernoulliRegular.UnitQuotient.FreeLatticeComparison.Eigenspaces
import BernoulliRegular.UnitQuotient.GlobalUnitDimension
import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.FLT37Closure
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.PthPowerLift
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.CertificateAudit

/-!
# T-EIG-B1: Structural decomposition of σ_a • pollaczekUnitPlus

For the σ-symmetric `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`,
the Galois action by `σ_a := cyclotomicSigmaOfUnit p K a` decomposes:

   `σ_a • pollaczekUnitPlus = (σ_a • pollaczekUnit) · (σ_{-a} • pollaczekUnit)`

Combined with the existing `cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue`
(in `KummerLift/CharacterIdentification.lean`), this provides the σ_a-eigenvalue
chain for pollaczekUnitPlus needed for the rank-one Pollaczek specialisation.

## Sources

* T-EIG-B0 bridge `unitsComplexConj_val_eq_cyclotomicSigmaOfUnit_neg_one_smul`.
* Project's `cyclotomicSigmaOfUnit_mul` (composition law).
* Project's `pollaczekUnitPlus` definition.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **Structural decomposition of `σ_a • pollaczekUnitPlus`**.

Distributes the Galois action over the σ-symmetric product structure:

  `σ_a • (P · σ_{-1} • P) = (σ_a • P) · (σ_a · σ_{-1}) • P = (σ_a • P) · σ_{-a} • P`

via `MulSemiringAction.smul_mul` (multiplicativity of σ_a),
`unitsComplexConj_val_eq_cyclotomicSigmaOfUnit_neg_one_smul` (T-EIG-B0
bridge), and `cyclotomicSigmaOfUnit_mul` (composition law). -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnitPlus_decomp
    (hp_two : 2 < p) (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      (cyclotomicSigmaOfUnit (p := p) K a •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K)) *
      (cyclotomicSigmaOfUnit (p := p) K (-a) •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K)) := by
  -- Unfold pollaczekUnitPlus = pollaczekUnit * unitsComplexConj K (pollaczekUnit).
  have h_def : ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
      ((NumberField.IsCMField.unitsComplexConj K (pollaczekUnit p K i) :
        (𝓞 K)ˣ) : 𝓞 K) := by
    unfold pollaczekUnitPlus
    rw [Units.val_mul]
  rw [h_def, smul_mul']
  -- Bridge unitsComplexConj K (pollaczekUnit) val = σ_{-1} • pollaczekUnit val (T-EIG-B0).
  rw [unitsComplexConj_val_eq_cyclotomicSigmaOfUnit_neg_one_smul (p := p)
        (K := K) hp_two (pollaczekUnit p K i)]
  -- Compose smul: σ_a • (σ_{-1} • x) = (σ_a · σ_{-1}) • x = σ_{-a} • x.
  rw [smul_smul, ← cyclotomicSigmaOfUnit_mul]
  congr 2
  rw [mul_neg_one]

/-- **σ_a-eigenvalue identity for `pollaczekUnitPlus` (substitution form)**.

Combines the structural decomposition `σ_a • pollaczekUnitPlus =
(σ_a • pollaczekUnit) · (σ_{-a} • pollaczekUnit)` (T-EIG-B1 above) with
two applications of the existing
`cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue` (one at
`a`, one at `-a`). Uses `i` even (i.e., `Even (p-1-i)` with `p` odd)
so that `(-a)^i = a^i`, giving `pollaczekUnit^{a^i + (-a)^i} =
pollaczekUnit^{2 a^i}`.

The equation has the substitution form (cyclotomicUnit factors at
`a.val` and `(-a).val` on the LHS, matching the existing
`almost_eigenvalue` signature). -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnitPlus_almost_eigenvalue
    (hp_odd : p ≠ 2) (hp_two : 2 < p) (a : (ZMod p)ˣ) (i : ℕ)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i)) :
    ∃ γ_pair : (𝓞 K)ˣ,
      cyclotomicSigmaOfUnit (p := p) K a •
          ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) *
        (cyclotomicUnit p K ((a : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
        (cyclotomicUnit p K (((-a : (ZMod p)ˣ) : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) =
      ((∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                (1 : 𝓞 K)
              else
                -((zeta_spec p ℚ K).toInteger) ^
                  (((a : ZMod p) * (b : ZMod p)).val))) ^ (b ^ (p - 1 - i))) *
       (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((if (((-a : (ZMod p)ˣ) : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                (1 : 𝓞 K)
              else
                -((zeta_spec p ℚ K).toInteger) ^
                  ((((-a : (ZMod p)ˣ) : ZMod p) * (b : ZMod p)).val))) ^
            (b ^ (p - 1 - i)))) *
      (((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^
        (((a^i : (ZMod p)ˣ) : ZMod p).val)) *
      (((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^
        ((((-a : (ZMod p)ˣ)^i : (ZMod p)ˣ) : ZMod p).val)) *
      ((γ_pair : 𝓞 K)) ^ p := by
  obtain ⟨γ_a, hγ_a⟩ :=
    cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue p K a i hp_odd hi hi_even
  obtain ⟨γ_neg_a, hγ_neg_a⟩ :=
    cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue p K (-a) i hp_odd hi hi_even
  refine ⟨γ_a * γ_neg_a, ?_⟩
  rw [cyclotomicSigmaOfUnit_smul_pollaczekUnitPlus_decomp p K hp_two a i]
  -- LHS = (σ_a • PU) · (σ_{-a} • PU) · cycU(a.val)^S · cycU((-a).val)^S
  --     = [σ_a • PU · cycU(a.val)^S] · [σ_{-a} • PU · cycU((-a).val)^S]
  -- which equals (RHS_a) · (RHS_{-a}) by the two almost-eigenvalue equations.
  have h_combined :
      ((cyclotomicSigmaOfUnit (p := p) K a •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K)) *
        (cyclotomicSigmaOfUnit (p := p) K (-a) •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K)) *
        cyclotomicUnit p K ((a : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      cyclotomicUnit p K (((-a : (ZMod p)ˣ) : ZMod p).val) ^
        (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) =
      (cyclotomicSigmaOfUnit (p := p) K a •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        cyclotomicUnit p K ((a : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) *
      (cyclotomicSigmaOfUnit (p := p) K (-a) •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        cyclotomicUnit p K (((-a : (ZMod p)ˣ) : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))) := by
    ring
  rw [h_combined, hγ_a, hγ_neg_a]
  push_cast
  ring

/-- **FLT37-specialised pollaczekUnitPlus eigenvalue identity**: applies
the FLT37 power-sum-divisibility (`pow_powerSum_eq_pow_pow_thirtyseven`)
to express both LHS cycU corrections in
`cyclotomicSigmaOfUnit_smul_pollaczekUnitPlus_almost_eigenvalue`
as 37-th powers, giving the form where ALL correction factors are
explicit 37-th powers — suitable for unit-level cancellation in the
clean eigenvalue identity. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnitPlus_almost_eigenvalue_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K']
    (a : (ZMod 37)ˣ) :
    ∃ γ_pair : (𝓞 K')ˣ,
      cyclotomicSigmaOfUnit (p := 37) K' a •
          ((pollaczekUnitPlus 37 K' 32 : (𝓞 K')ˣ) : 𝓞 K') *
        (cyclotomicUnit 37 K' ((a : ZMod 37).val) ^ 11685) ^ 37 *
        (cyclotomicUnit 37 K' (((-a : (ZMod 37)ˣ) : ZMod 37).val) ^ 11685) ^ 37 =
      (∏ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
          ((if ((a : ZMod 37) * (b : ZMod 37)).val ≤ ((37 : ℕ) - 1) / 2 then
                (1 : 𝓞 K')
              else
                -((zeta_spec 37 ℚ K').toInteger) ^
                  (((a : ZMod 37) * (b : ZMod 37)).val))) ^
            (b ^ ((37 : ℕ) - 1 - 32))) *
        (∏ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
          ((if (((-a : (ZMod 37)ˣ) : ZMod 37) * (b : ZMod 37)).val ≤ ((37 : ℕ) - 1) / 2 then
                (1 : 𝓞 K')
              else
                -((zeta_spec 37 ℚ K').toInteger) ^
                  ((((-a : (ZMod 37)ˣ) : ZMod 37) * (b : ZMod 37)).val))) ^
            (b ^ ((37 : ℕ) - 1 - 32))) *
      (((pollaczekUnit 37 K' 32 : (𝓞 K')ˣ) : 𝓞 K') ^
        (((a^32 : (ZMod 37)ˣ) : ZMod 37).val)) *
      (((pollaczekUnit 37 K' 32 : (𝓞 K')ˣ) : 𝓞 K') ^
        ((((-a : (ZMod 37)ˣ)^32 : (ZMod 37)ˣ) : ZMod 37).val)) *
      ((γ_pair : 𝓞 K')) ^ 37 := by
  obtain ⟨γ_pair, hγ⟩ :=
    cyclotomicSigmaOfUnit_smul_pollaczekUnitPlus_almost_eigenvalue
      37 K' (by decide : (37 : ℕ) ≠ 2) (by decide : 2 < 37) a 32
      (by decide : (32 : ℕ) ≤ 37 - 1)
      (by decide : Even (37 - 1 - 32))
  refine ⟨γ_pair, ?_⟩
  rw [← pow_powerSum_eq_pow_pow_thirtyseven
        (cyclotomicUnit 37 K' ((a : ZMod 37).val))]
  rw [← pow_powerSum_eq_pow_pow_thirtyseven
        (cyclotomicUnit 37 K' (((-a : (ZMod 37)ˣ) : ZMod 37).val))]
  exact hγ

/-- **FLT37 cyclotomic-unit power-sum vanishes mod p-th powers**: for any
unit `u : (𝓞 K)ˣ`, the FLT37 power-sum exponent `S = 432345 = 37·11685`
gives `u^S = (u^11685)^37`, hence `u^S ≡ 1` modulo `((𝓞 K)ˣ)^37`.

Concretely: the image of `u^S` in `Multiplicative (CyclotomicUnitFreePartModP K)`
under `cyclotomicUnitToFreePartModPMul` is the trivial element. -/
theorem cyclotomicUnitFreePartModPMul_pow_powerSum_eq_one_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    (u : CyclotomicUnitGroup K') :
    cyclotomicUnitToFreePartModPMul (p := 37) K'
        (u ^ (∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
          b ^ ((37 : ℕ) - 1 - 32))) = 1 := by
  rw [pow_powerSum_eq_pow_pow_thirtyseven u]
  -- (u^11685)^37 maps to 1 (37-th power vanishes mod 37-th powers).
  exact cyclotomicUnitToFreePartModPMul_pow_eq_one (p := 37) (K := K')
    (u ^ 11685)

omit [NumberField.IsCMField K] in
/-- **Structural connector**: the value of the unit-level Δ-action equals
the ring-level Δ-smul on the value. Direct from the definition of
`cyclotomicUnitEquiv` as `Units.mapEquiv (cyclotomicRingOfIntegersEquiv ...)`. -/
theorem cyclotomicUnitEquiv_val_eq_cyclotomicSigmaOfUnit_smul
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    ((cyclotomicUnitEquiv (p := p) K a u : (𝓞 K)ˣ) : 𝓞 K) =
      cyclotomicSigmaOfUnit (p := p) K a • ((u : (𝓞 K)ˣ) : 𝓞 K) :=
  rfl

/-- **FLT37 cyclotomic-unit additive power-sum scalar vanishes**: for any
class `x : CyclotomicUnitFreePartModP K`, `S • x = 0` where
`S = ∑_{b=1}^{18} b^4 = 432345 = 37·11685`.

Direct from `S` being divisible by 37, hence `(S : ZMod 37) = 0`, and
`CyclotomicUnitFreePartModP K` being a ZMod 37-module. -/
theorem cyclotomicUnitFreePartModP_powerSum_smul_eq_zero_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    (x : CyclotomicUnitFreePartModP (p := 37) K') :
    (∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
        b ^ ((37 : ℕ) - 1 - 32)) • x = 0 := by
  -- The ZMod 37-module structure: (n : ℕ) • x factors through (n : ZMod 37) • x.
  -- For S divisible by 37, (S : ZMod 37) = 0, so S • x = 0.
  have hp : Fact (Nat.Prime 37) := hp37
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  -- S = 37·11685, so 37 ∣ S, so (S : ZMod 37) = 0.
  have h_S_dvd : (37 : ℕ) ∣ ∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
      b ^ ((37 : ℕ) - 1 - 32) := by decide
  -- Cast to ZMod 37: (S : ZMod 37) = 0.
  have h_S_zmod : ((∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
      b ^ ((37 : ℕ) - 1 - 32) : ℕ) : ZMod 37) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 37).mpr h_S_dvd
  -- ℕ-smul on ModN: (n : ℕ) • x = (n : ZMod 37) • x (via the ZMod 37-module instance).
  rw [show ((∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
      b ^ ((37 : ℕ) - 1 - 32)) • x
      : CyclotomicUnitFreePartModP (p := 37) K') =
      ((∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
        b ^ ((37 : ℕ) - 1 - 32) : ℕ) : ZMod 37) • x from
    (Nat.cast_smul_eq_nsmul (R := ZMod 37) _ x).symm]
  rw [h_S_zmod, zero_smul]

/-- **FLT37 cyclotomic-unit's S-th power class is trivial in mod-p free part**.
For any unit `u : (𝓞 K)ˣ`, the class of `u^S` in
`CyclotomicUnitFreePartModP K` (additive form) is `0`. -/
theorem cyclotomicUnitToFreePartModPAdd_pow_powerSum_eq_zero_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    (u : CyclotomicUnitGroup K') :
    cyclotomicUnitToFreePartModPAdd (p := 37) K'
        (Additive.ofMul (u ^ (∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
          b ^ ((37 : ℕ) - 1 - 32)))) = 0 := by
  -- Multiplicative form: ofMul (u^S) maps to 1 (= 0 additively) by the shipped
  -- `cyclotomicUnitFreePartModPMul_pow_powerSum_eq_one_FLT37`.
  have h_mul : cyclotomicUnitToFreePartModPMul (p := 37) K'
      (u ^ (∑ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
        b ^ ((37 : ℕ) - 1 - 32))) = 1 :=
    cyclotomicUnitFreePartModPMul_pow_powerSum_eq_one_FLT37 (K' := K') u
  -- The additive class equals toAdd of the multiplicative class.
  exact Multiplicative.ext <| h_mul

/-- **Torsion units have trivial class in mod-p free part**.
For `u : (𝓞 K)ˣ` in the torsion subgroup, the additive class
`cyclotomicUnitToFreePartModPAdd K (Additive.ofMul u) = 0`. -/
theorem cyclotomicUnitToFreePartModPAdd_torsion_eq_zero
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {u : CyclotomicUnitGroup K} (hu : u ∈ NumberField.Units.torsion K) :
    cyclotomicUnitToFreePartModPAdd (p := p) K (Additive.ofMul u) = 0 := by
  -- u in torsion ⟹ cyclotomicUnitFreeClass K u = 1.
  have hu_free : cyclotomicUnitFreeClass K u = 1 := by
    rw [← MonoidHom.mem_ker, cyclotomicUnitFreeClass_ker]
    exact hu
  rw [cyclotomicUnitToFreePartModPAdd_apply, hu_free]
  rfl

omit [NumberField.IsCMField K] in
/-- **Unit-form of the sign+ζ if-branch factor** in the eigenvalue identity.
For each `b`, the factor `if cond then (1 : 𝓞 K) else -ζ^k` (a ring element)
is the value of the unit `if cond then (1 : (𝓞 K)ˣ) else -((zeta_spec p ℚ K).unit')^k`.

This is the unit-level companion of the if-branch in
`cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue`. -/
theorem signZeta_factor_unit_val (cond : Prop) [Decidable cond] (k : ℕ) :
    ((if cond then (1 : (𝓞 K)ˣ) else
        -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ k)) : 𝓞 K) =
      (if cond then (1 : 𝓞 K) else
        -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit : 𝓞 K) ^ k) := by
  by_cases h : cond
  · simp [h]
  · simp [h]

omit [NumberField.IsCMField K] in
/-- **Unit-form of each `(if-branch)^(b^E)` factor (torsion class is zero)**:
the unit `if cond then (1 : (𝓞 K)ˣ) else -((zeta_spec p ℚ K).unit')^k` is
torsion (a root of unity), since each branch is in `⟨-1, ζ⟩` (the
roots of unity in `(𝓞 K)ˣ`). -/
theorem signZeta_factor_isTorsion (cond : Prop) [Decidable cond] (k : ℕ) :
    (if cond then (1 : (𝓞 K)ˣ) else
        -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ k)) ∈
      NumberField.Units.torsion K := by
  by_cases h : cond
  · simp [h, NumberField.Units.torsion]
  · simp only [h, if_false]
    -- -ζ^k is torsion: ζ has order p, so ζ^k has order dividing p.
    -- -1 has order 2. Their product has order dividing 2p, hence finite.
    apply (CommGroup.mem_torsion _).2
    -- (-ζ^k)^(2p) = ζ^(2kp) = 1.
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 * p, by simp [(Fact.out : p.Prime).pos], ?_⟩
    have hζp : ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ p = 1 :=
      ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit hp.1.ne_zero).pow_eq_one
    rw [show (-(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ k)) ^ (2 * p) =
        ((-1 : (𝓞 K)ˣ) ^ (2 * p)) * (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ k) ^ (2 * p) from by
      rw [neg_eq_neg_one_mul, mul_pow]]
    rw [show ((-1 : (𝓞 K)ˣ) ^ (2 * p)) = 1 from by
      rw [pow_mul, neg_one_sq, one_pow]]
    rw [one_mul]
    rw [show (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ k) ^ (2 * p) =
        ((((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ p) ^ (2 * k)) from by
      rw [← pow_mul, ← pow_mul]; congr 1; ring]
    rw [hζp, one_pow]

omit [NumberField.IsCMField K] in
/-- **Unit-level half-range product form of the (sign+ζ)-prefactor**:
the unit-form product matches the ring-level (sign+ζ)-prefactor in the
eigenvalue identity. -/
theorem signZeta_prefactor_unit_val (a : (ZMod p)ˣ) (i : ℕ) :
    (((∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
              (1 : (𝓞 K)ˣ)
            else
              -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^
                (((a : ZMod p) * (b : ZMod p)).val))) ^ (b ^ (p - 1 - i)))
      : (𝓞 K)ˣ) : 𝓞 K) =
    ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
              (1 : 𝓞 K)
            else
              -((zeta_spec p ℚ K).toInteger) ^
                (((a : ZMod p) * (b : ZMod p)).val)) ^ (b ^ (p - 1 - i)) := by
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Units.val_pow_eq_pow_val]
  congr 1
  rw [apply_ite (·.val : (𝓞 K)ˣ → 𝓞 K)]
  simp only [Units.val_one, Units.val_neg, Units.val_pow_eq_pow_val, IsUnit.unit_spec]

omit [NumberField.IsCMField K] in
/-- **Unit-level half-range product is torsion**: products and powers of
torsion units are torsion. Apply `signZeta_factor_isTorsion` to each
factor + `Subgroup.prod_mem` + `Subgroup.pow_mem`. -/
theorem signZeta_prefactor_isTorsion (a : (ZMod p)ˣ) (i : ℕ) :
    (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
              (1 : (𝓞 K)ˣ)
            else
              -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^
                (((a : ZMod p) * (b : ZMod p)).val))) ^ (b ^ (p - 1 - i))) ∈
    NumberField.Units.torsion K := by
  apply Subgroup.prod_mem
  intro b _
  exact Subgroup.pow_mem _ (signZeta_factor_isTorsion (p := p) (K := K) _ _) _

omit [NumberField.IsCMField K] in
/-- **(sign+ζ)-prefactor's mod-p free part class is 0**: composition of
unit-form torsion claim with `cyclotomicUnitToFreePartModPAdd_torsion_eq_zero`. -/
theorem signZeta_prefactor_class_eq_zero (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicUnitToFreePartModPAdd (p := p) K
        (Additive.ofMul
          (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
              (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                    (1 : (𝓞 K)ˣ)
                  else
                    -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^
                      (((a : ZMod p) * (b : ZMod p)).val))) ^
                (b ^ (p - 1 - i)))) = 0 :=
  cyclotomicUnitToFreePartModPAdd_torsion_eq_zero
    (signZeta_prefactor_isTorsion (p := p) (K := K) a i)

omit [NumberField.IsCMField K] in
/-- **Unit-level form of the eigenvalue identity** (with prefactor at
unit level, value-matching shipped via `signZeta_prefactor_unit_val`).
Lifts the ring-level `cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue`
to `(𝓞 K)ˣ` via `Units.ext`. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue_units
    (a : (ZMod p)ˣ) (i : ℕ) (hp_odd : p ≠ 2) (hp_two : 2 ≤ p)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i))
    (ha_coprime : ((a : ZMod p).val).Coprime p) :
    ∃ γ : (𝓞 K)ˣ,
      cyclotomicUnitEquiv (p := p) K a (pollaczekUnit p K i) *
        (cyclotomicUnitUnit p K ((a : ZMod p).val) ha_coprime hp_two) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) =
        (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                (1 : (𝓞 K)ˣ)
              else
                -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^
                  (((a : ZMod p) * (b : ZMod p)).val))) ^
            (b ^ (p - 1 - i))) *
        (pollaczekUnit p K i) ^ (((a^i : (ZMod p)ˣ) : ZMod p).val) *
        γ ^ p := by
  obtain ⟨γ, hγ⟩ := cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue
    p K a i hp_odd hi hi_even
  refine ⟨γ, ?_⟩
  apply Units.ext
  -- LHS_val = σ_a • PU * cycU(a.val)^S.  RHS_val = (prefactor_val) * PU^... * γ^p.
  -- LHS: explicit unit-product cast to 𝓞 K, then equal to ring-level LHS.
  have h_lhs : ((cyclotomicUnitEquiv (p := p) K a (pollaczekUnit p K i) *
        (cyclotomicUnitUnit p K ((a : ZMod p).val) ha_coprime hp_two) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))
      : (𝓞 K)ˣ) : 𝓞 K) =
      cyclotomicSigmaOfUnit (p := p) K a •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        cyclotomicUnit p K ((a : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val,
        cyclotomicUnitUnit_val,
        cyclotomicUnitEquiv_val_eq_cyclotomicSigmaOfUnit_smul]
  -- RHS: explicit unit-product cast to 𝓞 K, then equal to ring-level RHS.
  have h_rhs : (((∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                (1 : (𝓞 K)ˣ)
              else
                -(((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^
                  (((a : ZMod p) * (b : ZMod p)).val))) ^
            (b ^ (p - 1 - i))) *
        (pollaczekUnit p K i) ^ (((a^i : (ZMod p)ˣ) : ZMod p).val) *
        γ ^ p : (𝓞 K)ˣ) : 𝓞 K) =
      (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                (1 : 𝓞 K)
              else
                -((zeta_spec p ℚ K).toInteger) ^
                  (((a : ZMod p) * (b : ZMod p)).val))) ^ (b ^ (p - 1 - i))) *
        ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^
          (((a^i : (ZMod p)ˣ) : ZMod p).val) *
        ((γ : 𝓞 K)) ^ p := by
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val,
        signZeta_prefactor_unit_val]
    rfl
  rw [h_lhs, h_rhs]
  exact hγ

/-- **Eigenspace claim — pollaczekUnit's class in mod-p free part satisfies the
ω^32-eigenvalue equation** (FLT37). For any `a : (ZMod 37)ˣ`,
the additive class `[cyclotomicUnitEquiv K a (pollaczekUnit 37 K 32)]` equals
`((a^32).val : ℕ) • [pollaczekUnit 37 K 32]` in `CyclotomicUnitFreePartModP K`.

Direct construction using the session-shipped building blocks:
* Unit-level eigenvalue identity (this file).
* (sign+ζ) prefactor's class is 0 (this file).
* cyclotomicUnitFreePartModP_powerSum_smul_eq_zero_FLT37 (this file).
* cyclotomicUnitToFreePartModPMul_pow_eq_one (project — γ^p vanishing).
-/
theorem pollaczekUnit_image_eigenvalue_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K']
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitToFreePartModPAdd (p := 37) K'
        (Additive.ofMul (cyclotomicUnitEquiv (p := 37) K' a (pollaczekUnit 37 K' 32))) =
      (((a^32 : (ZMod 37)ˣ) : ZMod 37).val : ℕ) •
        cyclotomicUnitToFreePartModPAdd (p := 37) K'
          (Additive.ofMul (pollaczekUnit 37 K' 32)) := by
  obtain ⟨γ, hγ⟩ :=
    cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue_units
      (p := 37) (K := K') a 32 (by decide : (37 : ℕ) ≠ 2) (by decide : 2 ≤ 37)
      (by decide : (32 : ℕ) ≤ 37 - 1)
      (by decide : Even (37 - 1 - 32))
      ha_coprime
  -- Apply additive group hom to both sides.
  have h_class := congrArg
    (fun u => cyclotomicUnitToFreePartModPAdd (p := 37) K' (Additive.ofMul u)) hγ
  simp only [ofMul_mul, map_add, ofMul_pow, map_nsmul] at h_class
  -- Vanish each correction.
  rw [show ((∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) •
        cyclotomicUnitToFreePartModPAdd (p := 37) K'
          (Additive.ofMul (cyclotomicUnitUnit 37 K' ((a : ZMod 37).val) ha_coprime
            (by decide : 2 ≤ 37) : CyclotomicUnitGroup K'))
        : CyclotomicUnitFreePartModP (p := 37) K') = 0 from
      cyclotomicUnitFreePartModP_powerSum_smul_eq_zero_FLT37 _,
    add_zero] at h_class
  rw [signZeta_prefactor_class_eq_zero (p := 37) (K := K') a 32, zero_add] at h_class
  -- γ^37 vanishes (37 • _ = 0 in ZMod 37-module).
  have h_gamma_vanish : ((37 : ℕ) •
      cyclotomicUnitToFreePartModPAdd (p := 37) K'
        (Additive.ofMul (γ : CyclotomicUnitGroup K'))
      : CyclotomicUnitFreePartModP (p := 37) K') = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 37) 37 _]
    rw [ZMod.natCast_self]
    exact zero_smul _ _
  rw [h_gamma_vanish, add_zero] at h_class
  exact h_class

/-- **Pollaczek unit's image satisfies the eigenvalue equation under the
mod-p Δ-action** (FLT37). For any `a : (ZMod 37)ˣ`,
`cyclotomicUnitFreePartLinearEquiv K a` (the additive Δ-action) applied
to PU's class equals `(a^32).val` times PU's class. -/
theorem pollaczekUnit_image_action_eq_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K']
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitFreePartModPClass (p := 37) K'
        (cyclotomicUnitFreePartLinearEquiv (p := 37) K' a
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32)))) =
      (((a^32 : (ZMod 37)ˣ) : ZMod 37).val : ℕ) •
        cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32))) := by
  -- LHS = class of (cyclotomicUnitEquiv K a PU)
  -- (via cyclotomicUnitFreePartLinearEquiv_apply_class).
  rw [cyclotomicUnitFreePartLinearEquiv_apply_class]
  -- Now use the eigenspace claim shipped above.
  exact pollaczekUnit_image_eigenvalue_FLT37 a ha_coprime

/-- **Pollaczek unit's image satisfies the eigenvalue equation under the
mod-p Δ-action ZMod-form** (FLT37). For any `a : (ZMod 37)ˣ` (with the
.val coprime hypothesis),
`cyclotomicUnitFreePartModPDeltaActionZMod K a (PU's class)
   = ((a^32).val : ℕ) • PU's class`. -/
theorem pollaczekUnit_image_DeltaActionZMod_eq_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K']
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K' a
        (cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32)))) =
      (((a^32 : (ZMod 37)ˣ) : ZMod 37).val : ℕ) •
        cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32))) := by
  rw [cyclotomicUnitFreePartModPDeltaActionZMod_apply,
      cyclotomicUnitFreePartModPLinearEquiv_apply_class]
  exact pollaczekUnit_image_action_eq_FLT37 a ha_coprime

/-- **Pollaczek unit's image satisfies the eigenvalue equation in ZMod 37
form** (FLT37). This is the form `action a x = (ZMod 37 scalar) • x`
matching the eigenspace condition `χ(a) • x` for character ω^32. -/
theorem pollaczekUnit_image_eigenvalue_zmod_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K']
    (a : (ZMod 37)ˣ) (ha_coprime : ((a : ZMod 37).val).Coprime 37) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K' a
        (cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32)))) =
      (((a^32 : (ZMod 37)ˣ) : ZMod 37)) •
        cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32))) := by
  rw [pollaczekUnit_image_DeltaActionZMod_eq_FLT37 a ha_coprime]
  -- Need: ((a^32).val : ℕ) • PU's class = ((a^32 : ZMod 37)) • PU's class.
  -- For ZMod p-modules, n • x = (n : ZMod p) • x.
  set y : CyclotomicUnitFreePartModP (p := 37) K' :=
    cyclotomicUnitFreePartModPClass (p := 37) K'
      (Additive.ofMul (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32)))
  have h_smul : (((a^32 : (ZMod 37)ˣ) : ZMod 37).val : ℕ) • y =
      (((a^32 : (ZMod 37)ˣ) : ZMod 37)) • y := by
    haveI : NeZero (37 : ℕ) := ⟨by decide⟩
    rw [show ((((a^32 : (ZMod 37)ˣ) : ZMod 37)) • y : CyclotomicUnitFreePartModP (p := 37) K') =
        (((((a^32 : (ZMod 37)ˣ) : ZMod 37).val : ℕ) : ZMod 37)) • y from by
      rw [ZMod.natCast_val, ZMod.cast_id]]
    exact (Nat.cast_smul_eq_nsmul (R := ZMod 37)
      (((a^32 : (ZMod 37)ˣ) : ZMod 37).val) y).symm
  exact h_smul

/-- **Pollaczek unit's image satisfies the eigenvalue equation for all units**
(FLT37). Removes the coprimality hypothesis (automatic from `a : (ZMod 37)ˣ`). -/
theorem pollaczekUnit_image_eigenvalue_zmod_FLT37_forall
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K']
    (a : (ZMod 37)ˣ) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K' a
        (cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32)))) =
      (((a^32 : (ZMod 37)ˣ) : ZMod 37)) •
        cyclotomicUnitFreePartModPClass (p := 37) K'
          (Additive.ofMul
            (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32))) :=
  pollaczekUnit_image_eigenvalue_zmod_FLT37 a (ZMod.val_coe_unit_coprime a)

/-- **The character ω^k** — `MulChar (CyclotomicUnitDelta p) (ZMod p)`
sending `a` to `(a : ZMod p)^k`. Used to formulate the eigenspace
membership condition for character ω^k. -/
noncomputable def cyclotomicOmegaChar (k : ℕ) :
    MulChar (CyclotomicUnitDelta p) (ZMod p) where
  toFun a := ((a : ZMod p))^k
  map_one' := by simp
  map_mul' a b := by simp [mul_pow]
  map_nonunit' a ha := absurd (Group.isUnit a) ha

@[simp]
theorem cyclotomicOmegaChar_apply (k : ℕ) (a : CyclotomicUnitDelta p) :
    cyclotomicOmegaChar (p := p) k a = ((a : ZMod p))^k := rfl

/-- **Pollaczek unit's image lies in the ω^32-eigenspace** (FLT37).
The substantive eigenspace membership claim — direct construction
via the eigenvalue equation. -/
theorem pollaczekUnit_image_in_omegaChar32_eigenspace_FLT37
    {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {37} ℚ K']
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K'] :
    cyclotomicUnitFreePartModPClass (p := 37) K'
        (Additive.ofMul
          (cyclotomicUnitFreeClass K' (pollaczekUnit 37 K' 32))) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37) K'
        (cyclotomicOmegaChar (p := 37) 32) := by
  intro a
  rw [cyclotomicOmegaChar_apply]
  -- ((a : ZMod 37))^32 = ((a^32 : (ZMod 37)ˣ) : ZMod 37).
  rw [show ((a : ZMod 37))^32 = ((a^32 : (ZMod 37)ˣ) : ZMod 37) from by
    push_cast
    rfl]
  exact pollaczekUnit_image_eigenvalue_zmod_FLT37_forall a

/-- **Global K-side certificate for pollaczekUnit at FLT37**: lift the
local mod-𝔩 certificate to the global form. -/
theorem flt37_pollaczekUnit_global_cert
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      ((pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
          𝓞 (CyclotomicField 37 ℚ))) ≠
        ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
  -- Use the existing pollaczekUnit cert + isUnit_cyclotomicUnit form.
  intro α hα
  -- The local cert (from FLT37Closure) says ¬ IsPthPowerModPrime 37 𝔩 (pollaczekUnit).
  have h_local := LehmerVandiver.flt37_not_isPthPowerModPrime_pollaczekUnit_concrete
  -- The cert lifts via not_isPthPower_unit_of_not_isPthPowerModPrime — but the
  -- pollaczekUnit's underlying value is a unit (it's in (𝓞 K)ˣ).
  -- We need to express pollaczekUnit's value as a unit value to apply the lift.
  -- pollaczekUnit p K i : (𝓞 K)ˣ, and
  -- (pollaczekUnit p K i : 𝓞 K) = ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K).
  exact not_isPthPower_unit_of_not_isPthPowerModPrime h_local α hα

/-- **PU's class in `E/E^37` is non-zero** (FLT37). Direct from the
global K-side certificate: PU is not a 37-th power in (𝓞 K)ˣ, so its
image in `E/E^37` (the unit power quotient) is non-trivial. -/
theorem flt37_pollaczekUnit_class_in_powerQuotient_ne_one
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
        (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32) ≠ 1 := by
  intro h_eq
  -- h_eq says PU's class is 1 in E/E^37, i.e., PU ∈ E^37.
  rw [cyclotomicUnitPowerClass, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h_eq
  -- h_eq : pollaczekUnit ∈ CyclotomicUnitPowerSubgroup (= range of pow 37).
  unfold CyclotomicUnitPowerSubgroup at h_eq
  rw [MonoidHom.mem_range] at h_eq
  obtain ⟨α, hα⟩ := h_eq
  -- hα : α^37 = pollaczekUnit (as units).
  -- Apply the cert at unit level (then descend to value level).
  apply flt37_pollaczekUnit_global_cert α
  -- Need: (pollaczekUnit : 𝓞 K) = (α : 𝓞 K)^37.
  rw [show (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
        𝓞 (CyclotomicField 37 ℚ)) =
      ((pollaczekUnit 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) from rfl]
  rw [← hα]
  push_cast
  rfl

/-- **Cert lift to unit-level for pollaczekUnitPlus**: lifts the value-level
cert `flt37_realLocalCert_global` to the unit-level form. -/
theorem flt37_pollaczekUnitPlus_unit_ne_pow_37
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 ≠ α ^ 37 := by
  intro α heq
  apply flt37_realLocalCert_global α
  rw [show ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
      ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) from rfl]
  rw [heq]
  push_cast
  rfl

/-- **PUP class non-zero in E/E^37 (multiplicative)**. Direct from the
unit-level cert. -/
theorem flt37_pollaczekUnitPlus_class_in_powerQuotient_ne_one
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
        (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32) ≠ 1 := by
  intro h_eq
  rw [cyclotomicUnitPowerClass, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h_eq
  unfold CyclotomicUnitPowerSubgroup at h_eq
  rw [MonoidHom.mem_range] at h_eq
  obtain ⟨α, hα⟩ := h_eq
  exact flt37_pollaczekUnitPlus_unit_ne_pow_37 α hα.symm

/-- **PUP class non-zero in E/E^37 (additive)**. -/
theorem flt37_pollaczekUnitPlus_class_in_powerQuotient_additive_ne_zero
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    Additive.ofMul
        (cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
          (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)) ≠ 0 := fun h_eq =>
  flt37_pollaczekUnitPlus_class_in_powerQuotient_ne_one <| Additive.ofMul.injective h_eq

/-- **PUP class is fixed by `σ_{-1} = complex conjugation` at the E/E^37 level**.
Directly from PUP being σ-fixed at the unit level: the action `σ_{-1} • [u]`
descends to `[unitsComplexConj K u]`, and PUP is σ-fixed. -/
theorem flt37_pollaczekUnitPlus_class_neg_one_fixed
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitPowerQuotientDeltaActionZMod (p := 37) (CyclotomicField 37 ℚ)
        (-1 : CyclotomicUnitDelta 37)
        (Additive.ofMul
          (cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
            (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32))) =
      Additive.ofMul
        (cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
          (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)) := by
  change cyclotomicUnitPowerQuotientLinearEquivZMod (p := 37) (CyclotomicField 37 ℚ)
      (-1 : CyclotomicUnitDelta 37) (Additive.ofMul _) = _
  rw [cyclotomicUnitPowerQuotientLinearEquivZMod_apply]
  -- Goal: ofMul ((cyclotomicUnitModPDeltaAction K).act (-1) [PUP]) = ofMul [PUP].
  congr 1
  -- Goal: (cyclotomicUnitModPDeltaAction K).act (-1) [PUP] = [PUP].
  change (cyclotomicUnitPowerQuotientDeltaAction (p := 37) (N := 1) (CyclotomicField 37 ℚ)).act
      (-1 : CyclotomicUnitDelta 37)
      (cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
        (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)) = _
  rw [cyclotomicUnitPowerQuotientDeltaAction_act_mk]
  -- Goal: cyclotomicUnitPowerClass K (cyclotomicUnitEquiv K (-1) PUP) =
  --       cyclotomicUnitPowerClass K PUP.
  have hp_two : (2 : ℕ) < 37 := by omega
  rw [cyclotomicUnitEquiv_neg_one_apply (p := 37) (K := CyclotomicField 37 ℚ) hp_two]
  -- Goal: cyclotomicUnitPowerClass K (cyclotomicUnitsComplexConj K hp_two PUP) =
  --       cyclotomicUnitPowerClass K PUP.
  congr 1
  -- Goal: cyclotomicUnitsComplexConj K hp_two PUP = PUP.
  -- This is `unitsComplexConj K PUP = PUP` modulo the IsCMField instance bridge.
  exact pollaczekUnitPlus_complexConj 37 (CyclotomicField 37 ℚ) 32

/-- **PUP class is not in the torsion-image of E/E^37**: combination of
σ_{-1}-fixedness + non-zero, applied to the contrapositive of
`cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed`. -/
theorem flt37_pollaczekUnitPlus_class_not_mem_torsion_powerClassSubgroup
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
        (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32) ∉
      cyclotomicTorsionPowerClassSubgroup (p := 37) (CyclotomicField 37 ℚ) := fun hmem =>
  flt37_pollaczekUnitPlus_class_in_powerQuotient_additive_ne_zero <|
    cyclotomicUnitPowerQuotient_eq_zero_of_mem_torsion_of_neg_one_fixed
      (p := 37) (K := CyclotomicField 37 ℚ) (by omega) hmem
      flt37_pollaczekUnitPlus_class_neg_one_fixed

end FLT37

end BernoulliRegular

end
