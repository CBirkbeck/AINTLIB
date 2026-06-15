module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part3

/-!
# Cross-ring bridge: 𝓞 K / P' inside 𝓞 R' / 𝔭

For a prime ideal `P'` of `𝓞 K` and a prime `𝔭` of `𝓞 R'` lying over `P'`
(in a finite extension `R' / K`), the residue field `𝓞 R' / 𝔭` extends
the residue field `𝓞 K / P'`. This file builds the bridge:

* Existence of `𝔭` over a maximal `P'` (via going-up).
* Canonical injection `𝓞 K / P' → 𝓞 R' / 𝔭`.
* Compatible CharP transfer.

This is the first cross-ring atomic step toward K2-2 path (a):
applying the K2-1 atom in `𝓞 R' / 𝔭` (where `gaussSumInt` lives via
`algebraMap 𝓞 K 𝓞 R'`) and pulling back to `𝓞 K / P'`.

Per AI reviewer 2026-05-05 K2-2 plan: the descent atom requires this
bridge to apply K2-1 in the right ambient ring. Multi-week scope per
the plan; this file is the first chunk.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Existence of a prime above `P'` in an integral extension -/

/-- **h_χ_eval_pow at unit_a from character identification**: when the
character identification holds and `unit_a` represents some `α : 𝓞 K`
with `α ∉ P` via `(unit_a : 𝓞 K / P) = Quotient.mk P α`, the K2-2c form
holds at `unit_a`. -/
theorem chi_pow_apply_unit_eq_pow_pthSymbol
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'')
    {a : ℕ} (ha : a ≠ 0)
    (χ : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      MulChar (𝓞 K ⧸ P) R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      χ = residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
        hdiv zeta_R hzeta_R)
    {α : 𝓞 K} (hα : α ∉ P)
    (unit_a :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (𝓞 K ⧸ P)ˣ)
    (h_unit_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (unit_a : 𝓞 K ⧸ P) = (Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((χ ^ a).ringHomComp σ) ((unit_a : 𝓞 K ⧸ P)) =
      σ (zeta_R : R') ^
        (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [h_unit_eq]
  exact chi_pow_apply_quotient_eq_pow_pthSymbol hP_bot hp_in_P hdiv zeta_R hzeta_R σ ha hα
    χ h_residue_char_eq

/-- **Natural-number cast through Ideal.Quotient.mk**: for `n : ℕ`, the
ring cast `(n : 𝓞 K ⧸ P)` equals `Ideal.Quotient.mk P (n : 𝓞 K)`. This
is `map_natCast` for the quotient ring hom. -/
theorem natCast_quotient_eq_mk
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (n : ℕ) :
    ((n : 𝓞 K ⧸ P) : 𝓞 K ⧸ P) = (Ideal.Quotient.mk P) ((n : 𝓞 K)) :=
  (map_natCast (Ideal.Quotient.mk P) n).symm

/-- **Integer cast through Ideal.Quotient.mk**: similar to natCast version. -/
theorem intCast_quotient_eq_mk
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (n : ℤ) :
    ((n : 𝓞 K ⧸ P) : 𝓞 K ⧸ P) = (Ideal.Quotient.mk P) ((n : 𝓞 K)) :=
  (map_intCast (Ideal.Quotient.mk P) n).symm

/-! ### Constructing unit_a from natCast non-membership

When a natural number `n` is not in `P` (in `𝓞 K`), its image in `𝓞 K / P`
is a unit. We package this as a constructor. -/

/-- **unit_a from natCast**: given `(n : 𝓞 K) ∉ P`, the residue
`(n : 𝓞 K / P)` is a unit. -/
noncomputable def unitOfNatCast_notMem
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) : (𝓞 K ⧸ P)ˣ :=
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem P
    (((n : ℕ) : 𝓞 K)) hn

/-- **`unitOfNatCast_notMem` value coercion**. -/
@[simp] theorem unitOfNatCast_notMem_val
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((unitOfNatCast_notMem n hn) : 𝓞 K ⧸ P) =
      Ideal.Quotient.mk P (((n : ℕ) : 𝓞 K)) := rfl

/-- **`unitOfNatCast_notMem` natCast form**: equals the natCast
`(n : 𝓞 K / P)` directly. -/
theorem unitOfNatCast_notMem_eq_natCast
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((unitOfNatCast_notMem n hn) : 𝓞 K ⧸ P) =
      ((n : ℕ) : 𝓞 K ⧸ P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [unitOfNatCast_notMem_val, ← natCast_quotient_eq_mk]

/-! ### Specialized K-chain at index a = 1

For index `a = 1` (the "primary" descent index), the K-chain conclusion
simplifies to `pthSymbol (phiPrimeGenDescent S 1) P' = -pthSymbol NP' P`,
matching the form of `K2_2_of_descent_pow_eq` from PhiPrimeSymbol.lean. -/

/-- **K2-2 at index 1**: specialization of `K2_2_path_a_pthSymbol_of_K2_2c_pow`
to `a = 1`, giving the direct symbol identity
`pthSymbol (phiPrimeGenDescent S 1) P' = -pthSymbol NP' P`.

The factor `(1 : ZMod p) * s = s` simplifies the conclusion, removing the
per-index `^a` weight. This is the clean primary form. -/
theorem K2_2_path_a_pthSymbol_at_index_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_one_le_p_minus_one : 1 ≤ p - 1)
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S
      (le_refl 1) h_one_le_p_minus_one h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ 1).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ 1).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_zeta_pow_p :
      ((Ideal.Quotient.mk 𝔭
        (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ p = 1)
    (s : ZMod p)
    (_hs_def : s = BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P)
    (h_χ_eval_pow :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ 1).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ (1 * s.val)) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S
          (le_refl 1) h_one_le_p_minus_one h_ne_zero) P' = -s := by
  have h_apex := K2_2_path_a_pthSymbol_of_K2_2c_pow
    (a := 1) S (le_refl 1) h_one_le_p_minus_one h_ne_zero hP'_bot hp_in_P' hdiv_P'
    h_phi_notin_P' h_over h_compat hp h_χp_eq_one hf hN_eq hN_mod_p unit_a h_unit hg_ne
    h_zeta_pow_p
    (s := s)
    (h_χ_eval_pow := h_χ_eval_pow)
  -- h_apex: pthSymbol = -((1 : ZMod p) * s); want -s.
  rw [h_apex]
  push_cast
  ring

/-! ### Convenience: `1 ≤ p - 1` from `p.Prime`

For prime `p ≥ 2`, we have `p - 1 ≥ 1`. This packages the calculation. -/

/-- **`1 ≤ p - 1` from prime**. -/
theorem one_le_p_sub_one_of_prime {p : ℕ} [Fact p.Prime] : 1 ≤ p - 1 := by
  have hp := (Fact.out : p.Prime)
  exact Nat.le_sub_one_of_lt hp.one_lt

/-! ### K-chain output transferred under unit factor

If two elements `γ₁ γ₂ ∈ 𝓞 K` differ by a unit `u : (𝓞 K)ˣ` (i.e., γ₁ = u · γ₂),
and the unit's pthSymbol at `P'` is `0`, then their pthSymbols at `P'`
agree. -/

/-- **pthSymbol transfers under unit factor**: if `γ₁ = u * γ₂` for a
unit `u` with `pthSymbol u P' = 0`, then `pthSymbol γ₁ P' = pthSymbol γ₂ P'`.
Requires P' maximal, u ∉ P', γ₂ ∉ P'. -/
theorem pthSymbolAtPrime_canonical_eq_of_eq_mul_unit
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P' : Ideal (𝓞 K)} (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (γ₁ γ₂ : 𝓞 K) (u : 𝓞 K)
    (hu_notin : u ∉ P') (hγ₂_notin : γ₂ ∉ P')
    (h_eq : γ₁ = u * γ₂)
    (h_u_symbol_zero :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) u P' = 0) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) γ₁ P' =
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) γ₂ P' := by
  rw [h_eq, BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical_mul
      hP'_bot hP'_max hu_notin hγ₂_notin, h_u_symbol_zero, zero_add]

/-! ### Span equality implies unit factor

In an integral domain, two elements with equal principal ideals
differ by a unit. -/

/-- **Same-span implies unit factor**: if `Ideal.span {γ₁} = Ideal.span {γ₂}`
in `𝓞 K` (with γ₂ ≠ 0), then `γ₁ = u * γ₂` for some unit `u`. -/
theorem exists_unit_eq_of_span_eq
    {K : Type*} [Field K] [NumberField K]
    {γ₁ γ₂ : 𝓞 K} (_hγ₂_ne : γ₂ ≠ 0)
    (h_span : Ideal.span ({γ₁} : Set (𝓞 K)) = Ideal.span ({γ₂} : Set (𝓞 K))) :
    ∃ u : (𝓞 K)ˣ, γ₁ = (u : 𝓞 K) * γ₂ := by
  -- Span equality in an integral domain (𝓞 K is a domain) implies associated.
  have h_assoc : Associated γ₁ γ₂ :=
    Ideal.span_singleton_eq_span_singleton.mp h_span
  -- Associated means ∃ u : (𝓞 K)ˣ, γ₁ * u = γ₂, equivalently γ₁ = u⁻¹ * γ₂.
  obtain ⟨u, hu⟩ := h_assoc
  -- hu : γ₁ * u = γ₂
  refine ⟨u⁻¹, ?_⟩
  have h_inv_mul : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * γ₂ = γ₁ := by
    rw [← hu]
    rw [show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (γ₁ * (u : 𝓞 K)) =
      γ₁ * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) by ring]
    rw [h_inv_mul, mul_one]
  exact this.symm

/-! ### Bridging phiPrimeGenDescent and h_stick.gen via unit correction

When phiPrimeGenDescent generates the same span as h_stick.gen (both
generate stickelbergerIdeal P), they differ by a unit. The pthSymbol
of h_stick.gen at P' equals the pthSymbol of phiPrimeGenDescent at P'
plus the symbol of the unit correction. Under U-chain assumptions
(unit symbol = 0), they coincide. -/

/-- **Symbol equality for two generators of the same span**: under
the unit-correction symbol vanishing hypothesis, two generators of
the same principal ideal have equal pthSymbols at any P'. -/
theorem pthSymbolAtPrime_canonical_eq_of_span_eq_of_unit_symbol_zero
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P' : Ideal (𝓞 K)} (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (γ₁ γ₂ : 𝓞 K) (hγ₁_notin : γ₁ ∉ P') (hγ₂_notin : γ₂ ∉ P')
    (hγ₂_ne : γ₂ ≠ 0)
    (h_span : Ideal.span ({γ₁} : Set (𝓞 K)) = Ideal.span ({γ₂} : Set (𝓞 K)))
    (h_unit_symbol :
      ∀ (u : 𝓞 K), IsUnit u → u ∉ P' →
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) u P' = 0) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) γ₁ P' =
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) γ₂ P' := by
  obtain ⟨u, h_eq⟩ := exists_unit_eq_of_span_eq hγ₂_ne h_span
  -- h_eq : γ₁ = (u : 𝓞 K) * γ₂
  -- u is a unit, so u ∉ P' (since P' ≠ top).
  have hu_isUnit : IsUnit ((u : 𝓞 K)) := u.isUnit
  have hu_notin : (u : 𝓞 K) ∉ P' := by
    intro h_mem
    rw [h_eq] at hγ₁_notin
    exact hγ₁_notin (Ideal.mul_mem_right γ₂ P' h_mem)
  exact pthSymbolAtPrime_canonical_eq_of_eq_mul_unit hP'_bot hP'_max γ₁ γ₂ (u : 𝓞 K)
    hu_notin hγ₂_notin h_eq (h_unit_symbol (u : 𝓞 K) hu_isUnit hu_notin)

/-! ### Full apex: K-chain output for h_stick.gen via specific-unit correction

The K-chain output for phiPrimeGenDescent transfers to h_stick.gen of
the StickelbergerIdealEquality constructed from phiPrimeGenDescent,
under the U-chain content for the SPECIFIC unit factor (h_stick.gen and
phiPrimeGenDescent generate the same span, hence differ by a single unit). -/

/-- **K-chain transferred to h_stick.gen via specific unit correction**:
the canonical pthSymbol of h_stick.gen at P' equals the K-chain target
`-((a : ZMod p) * pthSymbol NP' P)` provided we exhibit a specific unit
`u : (𝓞 K)ˣ` with `h_stick.gen = u * phiPrimeGenDescent` and
`pthSymbol (u : 𝓞 K) P' = 0`. -/
theorem pthSymbolAtPrime_canonical_h_stick_gen_eq_K_chain_target
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (h_K_chain :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P))
    (u : (𝓞 K)ˣ)
    (hu_eq :
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span).gen =
        (u : 𝓞 K) * phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)
    (hu_notin : (u : 𝓞 K) ∉ P')
    (hu_symbol :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) ((u : 𝓞 K)) P' = 0) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen
          (StickelbergerIdealEquality.of_phiPrimeGenDescent
            S ha₁ ha₂ h_ne_zero h_span)) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  rw [phiPrimeGen_eq_gen]
  rw [pthSymbolAtPrime_canonical_eq_of_eq_mul_unit hP'_bot hP'_max _ _ (u : 𝓞 K)
    hu_notin h_phi_notin_P' hu_eq hu_symbol]
  exact h_K_chain

/-! ### Discharging h_χp_eq_one

The K2-1 hypothesis `(residueCharInt^a).ringHomComp σ ^ p = 1` follows
from `residueMulChar^p = 1` (via `residueMulChar_pow_eq_one_mulChar`)
plus MulChar pow algebra: `(χ^a)^p = (χ^p)^a = 1^a = 1`, and ringHomComp
preserves 1. -/

/-- **`(χ^a).ringHomComp σ ^ p = 1` from `χ^p = 1`**: power algebra +
ringHomComp_one. -/
theorem mulChar_pow_ringHomComp_pow_p_eq_one
    {k : Type*} [CommMonoidWithZero k]
    {R' R'' : Type*} [CommRing R'] [CommRing R'']
    {p : ℕ}
    (χ : MulChar k R') (hχ : χ ^ p = 1) (a : ℕ) (σ : R' →+* R'') :
    (χ ^ a).ringHomComp σ ^ p = 1 := by
  rw [MulChar.ringHomComp_pow]
  rw [show (χ ^ a) ^ p = (χ ^ p) ^ a from by rw [← pow_mul, ← pow_mul, mul_comm]]
  rw [hχ, one_pow, MulChar.ringHomComp_one]

/-! ### Concrete residue-character specialization

The preceding K2-2 path only needs the character-value input
`h_χ_eval_pow`; two of its other hypotheses are automatic from the
`FullTeichDworkSetup`.  The next lemmas discharge these setup-internal
root-of-unity facts so later callers can focus on the actual
residue-character compatibility.
-/

/-- **Integral residue character has order dividing `p`**. -/
theorem ConcreteStickelbergerSetup.residueCharInt_pow_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    S.residueCharInt ^ p = 1 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  unfold ConcreteStickelbergerSetup.residueCharInt
  exact residueMulChar_pow_eq_one_mulChar
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- **K2-1 character-order input from the setup**. -/
theorem FullTeichDworkSetup.residueCharInt_ringHomComp_pow_p_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ) (𝔭 : Ideal (𝓞 R')) :
    (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1 :=
  mulChar_pow_ringHomComp_pow_p_eq_one
    S.residueCharInt
    (ConcreteStickelbergerSetup.residueCharInt_pow_eq_one
      S.toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup)
    a (Ideal.Quotient.mk 𝔭)

/-- **K2-2 path (a) with setup-internal root facts discharged**: compared
with `K2_2_path_a_pthSymbol_of_K2_2c_pow`, this theorem no longer asks the
caller to prove `(residueCharInt^a).ringHomComp _ ^ p = 1` or
`(zeta_p_int mod 𝔭)^p = 1`.  The remaining character-value hypothesis is the
actual K2-2c/residue-character compatibility input. -/
theorem K2_2_path_a_pthSymbol_of_residueCharInt_K2_2c_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0)
    (s : ZMod p)
    (h_χ_eval_pow :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^ (a * s.val)) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) * s) :=
  K2_2_path_a_pthSymbol_of_K2_2c_pow
    S ha₁ ha₂ h_ne_zero hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp
    (FullTeichDworkSetup.residueCharInt_ringHomComp_pow_p_eq_one S a 𝔭)
    hf hN_eq hN_mod_p unit_a h_unit hg_ne
    (ideal_quotient_mk_zeta_p_int_pow_p_eq_one (𝔭 := 𝔭) S)
    s h_χ_eval_pow

/-- **Reduced Gauss-sum nonvanishing from descended generator nonmembership**:
if `phiPrimeGenDescent S a` is nonzero modulo `P'`, then `gaussSumInt a`
is nonzero modulo any prime `𝔭` lying over `P'`, hence the reduced Gauss sum
is nonzero. -/
theorem gaussSum_ringHomComp_ne_zero_of_phiPrimeGenDescent_notMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    gaussSum
      ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
      ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0 := by
  let x : 𝓞 K ⧸ P' := Ideal.Quotient.mk P'
    (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)
  have hx_ne : x ≠ 0 := fun hx =>
    h_phi_notin_P' (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have h_image_ne : residueFieldEmbedding h_over x ≠ 0 := by
    intro hx0
    have hx_eq : residueFieldEmbedding h_over x = residueFieldEmbedding h_over 0 := by
      simpa using hx0
    exact hx_ne ((residueFieldEmbedding_injective h_over) hx_eq)
  have h_embed := residueFieldEmbedding_phiPrimeGenDescent
    S ha₁ ha₂ h_ne_zero h_over
  have h_embed_x :
      residueFieldEmbedding h_over x =
        (Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p) : 𝓞 R' ⧸ 𝔭) := by
    simpa [x] using h_embed
  have h_pow_ne :
      (Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p) : 𝓞 R' ⧸ 𝔭) ≠ 0 := fun hzero =>
    h_image_ne (by rw [h_embed_x]; exact hzero)
  intro hg
  have h_mk_zero : Ideal.Quotient.mk 𝔭 (S.gaussSumInt a) = 0 := by
    rw [ideal_quotient_mk_gaussSumInt]
    exact hg
  have h_pow_zero :
      (Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p) : 𝓞 R' ⧸ 𝔭) = 0 := by
    rw [map_pow, h_mk_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  exact h_pow_ne h_pow_zero

/-- **K2-2c from canonical residue-character compatibility**: if the setup
finite field is the canonical residue field `𝓞 K / P` and its integral
residue character is identified with the canonical `residueMulChar` at `P`,
then the remaining character-value input for the K2-2 path is automatic at
the unit represented by a natural number `n ∉ P`. -/
theorem residueCharInt_pow_apply_unitOfNatCast_eq_pow_pthSymbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {𝔭 : Ideal (𝓞 R')}
    {a n : ℕ} (ha₁ : 1 ≤ a)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        (unitOfNatCast_notMem (K := K) (P := P) n hn) =
      ((Ideal.Quotient.mk 𝔭
          S.zeta_p_int) :
        𝓞 R' ⧸ 𝔭) ^
        (a * (pthSymbolAtPrime_canonical (p := p) (K := K)
          (((n : ℕ) : 𝓞 K)) P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha₁
  have h_eval := chi_pow_apply_unit_eq_pow_pthSymbol
    (p := p) (K := K) (R' := 𝓞 R') (R'' := 𝓞 R' ⧸ 𝔭)
    hP_bot hp_in_P hdiv_P
    S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot
    (Ideal.Quotient.mk 𝔭) ha_ne
    S.residueCharInt
    h_residue_char_eq hn
    (unitOfNatCast_notMem (K := K) (P := P) n hn)
    (unitOfNatCast_notMem_val (K := K) (P := P) n hn)
  simpa [ConcreteStickelbergerSetup.zeta_p_int_unit_coe] using h_eval

/-- **Positive norm powers**: a power of a rational prime is at least `1`. -/
theorem one_le_pow_of_natPrime {ℓ' f : ℕ} [Fact ℓ'.Prime] :
    1 ≤ ℓ' ^ f :=
  Nat.succ_le_of_lt (Nat.pow_pos (Fact.out : ℓ'.Prime).pos)

/-- **Norm congruence from divisibility by `p`**: if `p ∣ N - 1` and `N > 0`,
then `N ≡ 1 (mod p)`.  This is the arithmetic side condition needed in the
K2-1 Frobenius cancellation step. -/
theorem Nat.mod_eq_one_of_dvd_sub_one
    {p N : ℕ} (hp : 1 < p) (hN_pos : 0 < N)
    (hdiv : p ∣ N - 1) :
    N % p = 1 := by
  rcases hdiv with ⟨m, hm⟩
  have hN_eq : N = p * m + 1 := by
    omega
  rw [hN_eq, Nat.add_mod, Nat.mul_mod_right]
  simp [Nat.mod_eq_of_lt hp]

/-- **Prime-ideal non-membership survives natural powers**: if the natural
integer `n` is nonzero modulo a prime ideal `P`, then so is `n^f`. -/
theorem natCast_pow_notMem_of_natCast_notMem
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsPrime]
    {n f : ℕ} (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    (((n ^ f : ℕ) : 𝓞 K)) ∉ P := by
  rw [Nat.cast_pow]
  intro hpow
  exact hn (Ideal.IsPrime.mem_of_pow_mem (hI := inferInstance) _ hpow)

/-- **Different rational primes stay nonzero in a residue field**: if
`𝓞 K / P` has characteristic `ℓ`, then a different rational prime `ℓ'` is not
in `P`. -/
theorem natPrime_notMem_of_charP_quotient_ne
    {K : Type*} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    {ℓ ℓ' : ℕ} [CharP (𝓞 K ⧸ P) ℓ]
    (hℓ'_prime : ℓ'.Prime) (h_ne : ℓ ≠ ℓ') :
    (((ℓ' : ℕ) : 𝓞 K)) ∉ P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  intro hmem
  have hzero : (ℓ' : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P) ℓ']
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (CharP.cast_ne_zero_of_ne_of_prime (𝓞 K ⧸ P) hℓ'_prime h_ne) hzero

/-- **Residue characteristic descends across the residue-field embedding**:
if `𝔭` lies over `P'` and `𝓞 R' / 𝔭` has characteristic `ℓ'`, then so does
`𝓞 K / P'`. -/
theorem charP_baseResidue_of_liesOver
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [CharP (𝓞 R' ⧸ 𝔭) ℓ'] :
    CharP (𝓞 K ⧸ P') ℓ' :=
  (residueFieldEmbedding h_over).charP (residueFieldEmbedding_injective h_over) ℓ'

/-- **Residue-field divisibility from the canonical root**: if `q` is a
maximal ideal of `𝓞 K` away from `p`, then the canonical residue primitive
`p`-th root forces `p ∣ #(𝓞 K/q)-1`. -/
theorem canonicalResidueZetaP_card_sub_one_dvd
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {q : Ideal (𝓞 K)} (hq_ne_bot : q ≠ ⊥) [hq_max : q.IsMaximal]
    (hp_not_in_q : (p : 𝓞 K) ∉ q) :
    p ∣ Fintype.card (𝓞 K ⧸ q) - 1 := by
  classical
  letI : Field (𝓞 K ⧸ q) := Ideal.Quotient.field q
  haveI : q.IsPrime := hq_max.isPrime
  have horder :
      orderOf (canonicalResidueZetaP (p := p) (K := K) q) = p :=
    canonicalResidueZetaP_orderOf_eq (p := p) (K := K) hq_ne_bot hp_not_in_q
  rw [← horder]
  simpa [Fintype.card_units] using
    (orderOf_dvd_card (x := canonicalResidueZetaP (p := p) (K := K) q))

/-- **Caller-facing K2-1 Frobenius congruence for the canonical source
residue field**. If `𝔭` lies over `P'`, the residue characteristic of
`𝓞 R' / 𝔭` is `ℓ'`, and the rational primes under `P` and `P'` are
different, then there is a unit in `𝓞 K / P` represented by
`#(𝓞 K / P')`, and the reduced Gauss sum satisfies

```
χ(#(𝓞 K / P')) * g^(#(𝓞 K / P')) = g
```

inside `𝓞 R' / 𝔭`. This is exactly the raw K2-1 congruence, before the
later cancellation/descent step that turns it into a residue-symbol
identity. -/
theorem K2_1_gaussSumInt_pow_card_apply_smul_eq_self_of_liesOver_ne_char
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (a : ℕ)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ∃ unit_N : (𝓞 K ⧸ P)ˣ,
      (unit_N : 𝓞 K ⧸ P) =
          ((Fintype.card (𝓞 K ⧸ P') : ℕ) : 𝓞 K ⧸ P) ∧
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭)) unit_N *
            ((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^
              Fintype.card (𝓞 K ⧸ P') =
          (Ideal.Quotient.mk 𝔭) (S.gaussSumInt a) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  haveI : CharP (𝓞 K ⧸ P') ℓ' := charP_baseResidue_of_liesOver h_over
  obtain ⟨f, _hℓ'_prime, hcard⟩ := FiniteField.card (𝓞 K ⧸ P') ℓ'
  have hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1 :=
    canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P') hP'_bot hp_in_P'
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hN_mod_p : (ℓ' ^ (f : ℕ)) % p = 1 :=
    Nat.mod_eq_one_of_dvd_sub_one hp
      (Nat.pow_pos (Fact.out : ℓ'.Prime).pos)
      (by
        rw [← hcard]
        exact hdiv_P')
  haveI : CharP (𝓞 K ⧸ P) ℓ :=
    charP_quotient_of_natPrime_mem P (Fact.out : ℓ.Prime) hℓ_in_P
  have hℓ'_notin_P : (((ℓ' : ℕ) : 𝓞 K)) ∉ P :=
    natPrime_notMem_of_charP_quotient_ne
      (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (Fact.out : ℓ'.Prime) hℓ_ne_ℓ'
  have hn_notin_P : ((((ℓ' ^ (f : ℕ) : ℕ) : 𝓞 K))) ∉ P := by
    haveI : P.IsPrime := hP_max.isPrime
    exact natCast_pow_notMem_of_natCast_notMem (K := K) (P := P) hℓ'_notin_P
  let unit_N : (𝓞 K ⧸ P)ˣ :=
    unitOfNatCast_notMem (K := K) (P := P) (ℓ' ^ (f : ℕ)) hn_notin_P
  have h_unit_N :
      (unit_N : 𝓞 K ⧸ P) = ((ℓ' ^ (f : ℕ) : ℕ) : 𝓞 K ⧸ P) :=
    unitOfNatCast_notMem_eq_natCast
      (K := K) (P := P) (ℓ' ^ (f : ℕ)) hn_notin_P
  refine ⟨unit_N, ?_, ?_⟩
  · rw [hcard]
    exact h_unit_N
  · have hK21 := ideal_quotient_mk_gaussSumInt_pow_apply_smul_eq_self
      (S := S) a hp
      (FullTeichDworkSetup.residueCharInt_ringHomComp_pow_p_eq_one S a 𝔭)
      hN_mod_p unit_N h_unit_N
    simpa [unit_N, hcard] using hK21

/-- **Proof-irrelevant residue-character transport**: changing the selected
source primitive root by equality changes neither the residue character nor
its proof arguments. -/
theorem residueMulChar_eq_of_zeta_eq
    {p : ℕ} [NeZero p]
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommMonoidWithZero R']
    {zeta_q zeta_q' : kˣ} (hζ : zeta_q = zeta_q')
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (hzeta_q' : IsPrimitiveRoot zeta_q' p)
    (hdiv' : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R =
      residueMulChar zeta_q' hzeta_q' hdiv' zeta_R hzeta_R := by
  cases hζ
  rfl

/-- **Residue-character identification from source-root compatibility**:
for a concrete setup over `𝓞 K/P`, the integral residue character is the
canonical residue character as soon as the setup's selected residue-field
root `S.zeta_k` is the canonical residue root at `P`. -/
theorem FullTeichDworkSetup.residueCharInt_eq_canonical_of_zeta_k_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.residueCharInt =
      residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
        (canonicalResidueZetaP_card_sub_one_dvd
          (p := p) (K := K) (q := P) hP_bot hp_in_P)
        S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [ConcreteStickelbergerSetup.residueCharInt]
  exact residueMulChar_eq_of_zeta_eq h_zeta_k_eq
    S.hzeta_k S.hdiv
    (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
    (canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P) hP_bot hp_in_P)
    S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot

end Furtwaengler

end BernoulliRegular

end
