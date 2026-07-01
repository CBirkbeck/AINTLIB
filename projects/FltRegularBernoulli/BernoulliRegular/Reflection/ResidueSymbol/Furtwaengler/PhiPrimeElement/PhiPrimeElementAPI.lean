module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge

/-!
# Data-carrying prime Φ-elements

The ideal-theoretic predicate `StickelbergerIdealEquality P` only says that
`stickelbergerIdeal P` is principal. Its extracted generator is therefore an
arbitrary generator, determined only up to a unit.

For K2-2 we need the actual Gauss-sum Φ element, not an arbitrary generator of
the same ideal. This file introduces a non-`Prop` object whose `gamma` field is
the element used in the residue-symbol theorem. The current constructor wires
in the existing `phiPrimeGenDescent S a` route from `CrossRingBridge.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-- **Data-carrying prime Φ element**.  The field `gamma` is the actual
element to use in residue-symbol statements. The span equality records that it
also generates the Stickelberger ideal, but the symbol theorem must use
`gamma`, not an arbitrary generator extracted later from the ideal equality. -/
structure PhiPrimeElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (P : Ideal (𝓞 K)) where
  /-- The actual Φ element. -/
  gamma : 𝓞 K
  /-- The actual Φ element is nonzero. -/
  gamma_ne_zero : gamma ≠ 0
  /-- The actual Φ element generates the Stickelberger ideal. -/
  span_gamma :
    Ideal.span ({gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P

namespace PhiPrimeElement

/-- A data-carrying Φ element still supplies the old ideal-theoretic
Stickelberger equality. This direction is safe; the reverse direction loses
the actual generator and introduces a unit ambiguity. -/
theorem toStickelbergerIdealEquality
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} (ΦP : PhiPrimeElement (p := p) (K := K) P) :
    StickelbergerIdealEquality (p := p) (K := K) P :=
  ⟨ΦP.gamma, ΦP.gamma_ne_zero, ΦP.span_gamma⟩

/-- Reverse direction: a (propositional) `StickelbergerIdealEquality` produces
a (data-carrying) `PhiPrimeElement` via classical choice.

This loses the specific normalization information — the resulting `gamma` is
the chosen generator from the existential, not necessarily the actual
descended Gauss-sum element `phiPrimeGenDescent S 1`. As a consequence,
constructions using this `PhiPrimeElement` for residue-symbol identities
inherit the unit-ambiguity tracked elsewhere in the chain (see
`unitToStickelbergerGen` and `phiPrimeGen_symbol_eq_unit_symbol_add`).

This is the correct constructor when the user produces a
`StickelbergerIdealEquality` via the abstract route — for example via
`stickelbergerIdealEquality_of_descentPrime_principal_of_split` or
`stickelbergerIdealEquality_of_orbitCoverage` — and does not separately
have access to the K2-2 source-data identification of `gamma` with
`phiPrimeGenDescent S 1`. -/
noncomputable def ofStickelbergerIdealEquality
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (h : StickelbergerIdealEquality (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma := h.gen
  gamma_ne_zero := h.gen_ne_zero
  span_gamma := h.span_gen

/-- Multiplying a prime Φ element by a unit preserves the ideal-theoretic
Stickelberger span.

This records the precise obstruction behind U4: any argument that only sees
`span_gamma` cannot distinguish the actual Gauss-sum normalization from a
unit-twist of it. Residue symbols do distinguish such twists. -/
def twistByUnit
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (u : (𝓞 K)ˣ) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma := (u : 𝓞 K) * ΦP.gamma
  gamma_ne_zero := mul_ne_zero (Units.ne_zero u) ΦP.gamma_ne_zero
  span_gamma := by
    rw [Ideal.span_singleton_mul_left_unit (Units.isUnit u) ΦP.gamma, ΦP.span_gamma]

@[simp]
theorem twistByUnit_gamma
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (u : (𝓞 K)ˣ) :
    (ΦP.twistByUnit (p := p) (K := K) u).gamma = (u : 𝓞 K) * ΦP.gamma :=
  rfl

/-- The actual Φ element is nonzero modulo `P'` as soon as its
Stickelberger ideal is not contained in `P'`. -/
theorem gamma_notMem_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P') :
    ΦP.gamma ∉ P' := fun h_mem =>
  h_not_le (ΦP.span_gamma ▸ (Ideal.span_singleton_le_iff_mem (I := P')).mpr h_mem)

/-- An arbitrary extracted Stickelberger generator is nonzero modulo `P'` as
soon as the Stickelberger ideal is not contained in `P'`. -/
theorem stickelbergerGen_notMem_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P') :
    h_stick.gen ∉ P' := fun h_mem =>
  h_not_le (h_stick.span_gen ▸ (Ideal.span_singleton_le_iff_mem (I := P')).mpr h_mem)

/-- If a nonzero prime `P'` contains `stickelbergerIdeal P`, then `P'` lies
over the same rational prime as `P`. -/
theorem under_eq_of_stickelbergerIdeal_le_prime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (h_le : stickelbergerIdeal (p := p) (K := K) P ≤ P') :
    P'.under ℤ = P.under ℤ := by
  classical
  have h_stick_ne : stickelbergerIdeal (p := p) (K := K) P ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    exact stickelbergerIdeal_ne_bot hP_ne
  have hP'_prime : Prime P' := (Ideal.prime_iff_isPrime hP'_ne).mpr inferInstance
  have h_dvd : P' ∣ stickelbergerIdeal (p := p) (K := K) P :=
    Ideal.dvd_iff_le.mpr h_le
  obtain ⟨Q, hQ_mem, hQ_assoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      h_stick_ne hP'_prime.irreducible h_dvd
  have hP'_factor :
      P' ∈ UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K) P) := by
    rwa [associated_iff_eq.mp hQ_assoc]
  have hP'_conj :
      P' ∈ cyclotomicConjugates (p := p) (K := K) P :=
    normalizedFactors_stickelbergerIdeal_subset hP_ne hP'_factor
  exact mem_cyclotomicConjugates_iff_under_eq.mp hP'_conj

/-- If `P` and `P'` lie over distinct rational primes, then `P'` cannot
contain `stickelbergerIdeal P`. -/
theorem stickelbergerIdeal_not_le_of_under_ne
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (h_under_ne : P'.under ℤ ≠ P.under ℤ) :
    ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P' := fun h_le =>
  h_under_ne (under_eq_of_stickelbergerIdeal_le_prime hP_ne hP'_ne h_le)

/-- Coprime rational norms force the ideal-support condition needed for the
prime Φ symbol: `P'` cannot contain `stickelbergerIdeal P`. -/
theorem stickelbergerIdeal_not_le_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P' := by
  intro h_le
  have h_under := under_eq_of_stickelbergerIdeal_le_prime hP_ne hP'_ne h_le
  haveI : NeZero P := ⟨by simpa [Ideal.zero_eq_bot] using hP_ne⟩
  have hq_prime : (Ideal.absNorm (P.under ℤ)).Prime :=
    Nat.absNorm_under_prime P
  have hdvd_left :
      Ideal.absNorm (P.under ℤ) ∣ Ideal.absNorm P :=
    Int.absNorm_under_dvd_absNorm P
  have hdvd_right' :
      Ideal.absNorm (P'.under ℤ) ∣ Ideal.absNorm P' :=
    Int.absNorm_under_dvd_absNorm P'
  have hdvd_right :
      Ideal.absNorm (P.under ℤ) ∣ Ideal.absNorm P' := by
    simpa [h_under] using hdvd_right'
  have hdvd_gcd :
      Ideal.absNorm (P.under ℤ) ∣ Nat.gcd (Ideal.absNorm P) (Ideal.absNorm P') :=
    Nat.dvd_gcd hdvd_left hdvd_right
  rw [hcop.gcd_eq_one] at hdvd_gcd
  exact hq_prime.not_dvd_one hdvd_gcd

/-- Coprime rational norms imply the actual Φ element is nonzero modulo `P'`. -/
theorem gamma_notMem_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    ΦP.gamma ∉ P' :=
  gamma_notMem_of_stickelbergerIdeal_not_le ΦP
    (stickelbergerIdeal_not_le_of_absNorm_coprime hP_ne hP'_ne hcop)

/-- Coprime rational norms imply an arbitrary extracted Stickelberger
generator is nonzero modulo `P'`. -/
theorem stickelbergerGen_notMem_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    h_stick.gen ∉ P' :=
  stickelbergerGen_notMem_of_stickelbergerIdeal_not_le h_stick
    (stickelbergerIdeal_not_le_of_absNorm_coprime hP_ne hP'_ne hcop)

/-! ### Unit correction for arbitrary Stickelberger generators -/

/-- The specific unit relating an arbitrary extracted Stickelberger generator
to the data-carrying actual Φ element. -/
noncomputable def unitToStickelbergerGen
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P) :
    (𝓞 K)ˣ :=
  unitFactorOfSpanEq (γ₁ := h_stick.gen) (γ₂ := ΦP.gamma) ΦP.gamma_ne_zero (by
    rw [h_stick.span_gen, ← ΦP.span_gamma])

/-- The unit `unitToStickelbergerGen ΦP h_stick` is the exact factor between
the arbitrary generator `h_stick.gen` and the actual Φ element `ΦP.gamma`. -/
theorem unitToStickelbergerGen_eq
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P) :
    h_stick.gen =
      ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) * ΦP.gamma :=
  unitFactorOfSpanEq_eq (γ₁ := h_stick.gen) (γ₂ := ΦP.gamma)
    ΦP.gamma_ne_zero (by
    rw [h_stick.span_gen, ← ΦP.span_gamma])

/-- If the arbitrary Stickelberger generator is nonzero modulo `P'`, then
the specific unit relating it to the actual Φ element is also nonzero modulo
`P'`. -/
theorem unitToStickelbergerGen_notMem
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P'.IsPrime]
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (h_stick_gen_notin : h_stick.gen ∉ P') :
    ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) ∉ P' :=
  unitFactorOfSpanEq_notMem (γ₁ := h_stick.gen) (γ₂ := ΦP.gamma)
    h_stick_gen_notin ΦP.gamma_ne_zero (by
    rw [h_stick.span_gen, ← ΦP.span_gamma])

/-- Ideal-support version of `unitToStickelbergerGen_notMem`. -/
theorem unitToStickelbergerGen_notMem_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P'.IsPrime]
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P') :
    ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) ∉ P' :=
  unitToStickelbergerGen_notMem ΦP h_stick
    (stickelbergerGen_notMem_of_stickelbergerIdeal_not_le h_stick h_not_le)

/-- Exact residue-symbol correction for replacing the actual Φ element by an
arbitrary generator of the same Stickelberger ideal.  This is the corrected
K2-2c shape: the arbitrary generator's symbol is the actual Φ symbol plus the
symbol of the specific unit relating the two generators. -/
theorem phiPrimeGen_symbol_eq_unit_symbol_add
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (h_gamma_notin : ΦP.gamma ∉ P')
    (h_stick_gen_notin : h_stick.gen ∉ P')
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' + T := by
  haveI : P'.IsPrime := hP'_max.isPrime
  rw [phiPrimeGen_eq_gen]
  conv_lhs =>
    rw [unitToStickelbergerGen_eq ΦP h_stick,
      pthSymbolAtPrime_canonical_mul hP'_bot hP'_max
        (unitToStickelbergerGen_notMem ΦP h_stick h_stick_gen_notin) h_gamma_notin]
  rw [h_gamma_symbol]

/-- Ideal-support version of `phiPrimeGen_symbol_eq_unit_symbol_add`. -/
theorem phiPrimeGen_symbol_eq_unit_symbol_add_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P')
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' + T :=
  phiPrimeGen_symbol_eq_unit_symbol_add ΦP h_stick hP'_bot hP'_max
    (gamma_notMem_of_stickelbergerIdeal_not_le ΦP h_not_le)
    (stickelbergerGen_notMem_of_stickelbergerIdeal_not_le h_stick h_not_le)
    h_gamma_symbol

/-- Coprime-rational-norm version of
`phiPrimeGen_symbol_eq_unit_symbol_add`. -/
theorem phiPrimeGen_symbol_eq_unit_symbol_add_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' + T :=
  phiPrimeGen_symbol_eq_unit_symbol_add_of_stickelbergerIdeal_not_le
    ΦP h_stick hP'_ne hP'_max
    (stickelbergerIdeal_not_le_of_absNorm_coprime hP_ne hP'_ne hcop)
    h_gamma_symbol

/-- The unit correction is exactly the obstruction to the uncorrected target
for an arbitrary extracted Stickelberger generator. -/
theorem phiPrimeGen_symbol_target_iff_unit_symbol_zero
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (h_gamma_notin : ΦP.gamma ∉ P')
    (h_stick_gen_notin : h_stick.gen ∉ P')
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T) :
    (pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' = T) ↔
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' = 0 := by
  let unitSymbol : ZMod p :=
    pthSymbolAtPrime_canonical (p := p) (K := K)
      ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P'
  have h_corr :
      pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' =
        unitSymbol + T :=
    phiPrimeGen_symbol_eq_unit_symbol_add
      ΦP h_stick hP'_bot hP'_max h_gamma_notin h_stick_gen_notin h_gamma_symbol
  constructor
  · intro h_target
    exact add_eq_right.mp (h_corr ▸ h_target)
  · intro h_unit
    change unitSymbol = 0 at h_unit
    rw [h_corr, h_unit, zero_add]

/-- Ideal-support version of
`phiPrimeGen_symbol_target_iff_unit_symbol_zero`. -/
theorem phiPrimeGen_symbol_target_iff_unit_symbol_zero_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P')
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T) :
    (pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' = T) ↔
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' = 0 :=
  phiPrimeGen_symbol_target_iff_unit_symbol_zero ΦP h_stick hP'_bot hP'_max
    (gamma_notMem_of_stickelbergerIdeal_not_le ΦP h_not_le)
    (stickelbergerGen_notMem_of_stickelbergerIdeal_not_le h_stick h_not_le)
    h_gamma_symbol

/-- If the unit correction vanishes, the arbitrary generator has the same
residue-symbol target as the actual Φ element. -/
theorem phiPrimeGen_symbol_eq_of_unit_symbol_zero
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (h_gamma_notin : ΦP.gamma ∉ P')
    (h_stick_gen_notin : h_stick.gen ∉ P')
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T)
    (h_unit_symbol_zero :
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' = 0) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' = T := by
  rw [phiPrimeGen_symbol_eq_unit_symbol_add
      ΦP h_stick hP'_bot hP'_max h_gamma_notin h_stick_gen_notin h_gamma_symbol,
    h_unit_symbol_zero, zero_add]

/-- Ideal-support version of `phiPrimeGen_symbol_eq_of_unit_symbol_zero`. -/
theorem phiPrimeGen_symbol_eq_of_unit_symbol_zero_of_stickelbergerIdeal_not_le
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P P' : Ideal (𝓞 K)}
    (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) P)
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    {T : ZMod p}
    (h_not_le : ¬ stickelbergerIdeal (p := p) (K := K) P ≤ P')
    (h_gamma_symbol :
      pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma P' = T)
    (h_unit_symbol_zero :
      pthSymbolAtPrime_canonical (p := p) (K := K)
        ((unitToStickelbergerGen ΦP h_stick : (𝓞 K)ˣ) : 𝓞 K) P' = 0) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (phiPrimeGen h_stick) P' = T :=
  phiPrimeGen_symbol_eq_of_unit_symbol_zero ΦP h_stick hP'_bot hP'_max
    (gamma_notMem_of_stickelbergerIdeal_not_le ΦP h_not_le)
    (stickelbergerGen_notMem_of_stickelbergerIdeal_not_le h_stick h_not_le)
    h_gamma_symbol h_unit_symbol_zero

/-- Construct the actual Φ-prime element from the existing descended
Gauss-sum element `phiPrimeGenDescent S a`. -/
noncomputable def ofDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma := phiPrimeGenDescent S ha₁ ha₂ h_ne_zero
  gamma_ne_zero := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
  span_gamma := h_span

@[simp] theorem ofDescent_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    (ofDescent S ha₁ ha₂ h_ne_zero h_span).gamma =
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero :=
  rfl

/-- Index-one constructor for the actual Φ-prime element. -/
noncomputable def ofDescentIndexOne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P :=
  ofDescent S (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero h_span

@[simp] theorem ofDescentIndexOne_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    (ofDescentIndexOne S h_ne_zero h_span).gamma =
      phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero :=
  rfl

/-- Reciprocal-index constructor for the actual Φ-prime element. -/
noncomputable def ofDescentSubOne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P :=
  ofDescent S (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
    h_ne_zero h_span

@[simp] theorem ofDescentSubOne_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    (ofDescentSubOne S h_ne_zero h_span).gamma =
      phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero :=
  rfl

/-- The actual reciprocal-index Φ candidate attached to a source construction.

This is the fixed candidate used by the REF-18' one-source route.  It is the
descended Gauss-sum Φ element at index `p - 1`; later nonzero, descent/span,
semi-primary, norm, and symbol facts must be proved for this element, not for an
arbitrary generator of the Stickelberger ideal. -/
noncomputable def reciprocalPhiCandidate
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    𝓞 K :=
  phiPrimeGenDescent S
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero

@[simp] theorem reciprocalPhiCandidate_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    reciprocalPhiCandidate (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R')
        S h_ne_zero =
      phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p))
        (le_refl (p - 1))
        h_ne_zero :=
  rfl

/-- The reciprocal Φ candidate is nonzero as an element of `𝓞 K`. -/
theorem reciprocalPhiCandidate_ne_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    reciprocalPhiCandidate (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R')
      S h_ne_zero ≠ 0 := by
  simpa [reciprocalPhiCandidate] using
    phiPrimeGenDescent_ne_zero S
      (one_le_p_sub_one_of_prime (p := p))
      (le_refl (p - 1))
      h_ne_zero

/-- The reciprocal Φ candidate descends the upstairs reciprocal Gauss-sum
pth power exactly. -/
theorem algebraMap_reciprocalPhiCandidate
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    algebraMap (𝓞 K) (𝓞 R')
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero) =
      S.gaussSumInt (p - 1) ^ p := by
  simpa [reciprocalPhiCandidate] using
    algebraMap_phiPrimeGenDescent S
      (one_le_p_sub_one_of_prime (p := p))
      (le_refl (p - 1))
      h_ne_zero

/-- Split atomic span normalization for the named reciprocal Φ candidate.

This is the REF-18' normalization theorem for the fixed candidate
`reciprocalPhiCandidate`: under the exact reciprocal Stickelberger exponent
predicate and split descent-prime hypotheses, the candidate generates the
Stickelberger ideal at the identified source prime. -/
theorem reciprocalPhiCandidate_span_of_atomic_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    {P : Ideal (𝓞 K)}
    (h_descentPrime : S.toConcreteStickelbergerSetup.descentPrime = P)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      S.StickelbergerExactConjugateExponents
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero))
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn
        (𝓞 K) = 1) :
    Ideal.span ({reciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P := by
  set γ : 𝓞 K :=
    reciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero
  have hγ_ne : γ ≠ 0 := by
    simpa [γ] using
      reciprocalPhiCandidate_ne_zero
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero
  have hγ_alg : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt (p - 1) ^ p := by
    simpa [γ] using
      algebraMap_reciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero
  have h_expγ : S.StickelbergerExactConjugateExponents γ := by
    simpa [γ] using h_exp
  have h_sup : S.StickelbergerSupportInOrbit γ :=
    S.stickelbergerSupportInOrbit_of_descentGaussSum
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) hγ_ne hγ_alg
  have h_faithful : S.StickelbergerOrbitFaithful :=
    S.stickelbergerOrbitFaithful_of_split he hf
  have h_stickMul : S.StickelbergerIdealConjugateMultiplicity :=
    S.stickelbergerIdealConjugateMultiplicity_of_orbitFaithful h_faithful
  have h_eq := S.span_eq_stickelbergerIdeal_of_atomic hγ_ne h_expγ h_sup h_stickMul
  rw [h_descentPrime] at h_eq
  simpa [γ] using h_eq

/-- Assemble the reciprocal candidate into a data-carrying Φ-prime element.

The `gamma` field is the fixed `reciprocalPhiCandidate`, not a classically chosen
Stickelberger generator. -/
noncomputable def ofReciprocalPhiCandidateAtomicSplit
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    {P : Ideal (𝓞 K)}
    (h_descentPrime : S.toConcreteStickelbergerSetup.descentPrime = P)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      S.StickelbergerExactConjugateExponents
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero))
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn
        (𝓞 K) = 1) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma :=
    reciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero
  gamma_ne_zero :=
    reciprocalPhiCandidate_ne_zero
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero
  span_gamma :=
    reciprocalPhiCandidate_span_of_atomic_split
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S
      h_descentPrime h_ne_zero h_exp he hf

@[simp] theorem ofReciprocalPhiCandidateAtomicSplit_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    {P : Ideal (𝓞 K)}
    (h_descentPrime : S.toConcreteStickelbergerSetup.descentPrime = P)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      S.StickelbergerExactConjugateExponents
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero))
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn
        (𝓞 K) = 1) :
    (ofReciprocalPhiCandidateAtomicSplit
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S
        h_descentPrime h_ne_zero h_exp he hf).gamma =
      reciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero :=
  rfl

@[simp] theorem ofDescentSubOne_gamma_eq_reciprocalPhiCandidate
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    (ofDescentSubOne S h_ne_zero h_span).gamma =
      reciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_ne_zero :=
  rfl

/-! ### K2-2 for the actual descended Φ element -/

/-- **K2-2 for the data-carrying actual Φ element from descent**.  This is
the corrected K2-2b target for the current path-a setup: the theorem is about
the `gamma` field of `PhiPrimeElement.ofDescent`, not about an arbitrary
generator extracted from `StickelbergerIdealEquality`. -/
theorem K2_2_of_canonical_zeta_choices_ofDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (ofDescent S ha₁ ha₂ h_ne_zero h_span).gamma P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  simpa [ofDescent] using
    K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zeta_choices
      hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
      ha₁ ha₂ h_ne_zero
      hP'_bot hp_in_P' h_phi_notin_P'
      h_over hℓ_ne_ℓ'

end PhiPrimeElement
end Furtwaengler

end BernoulliRegular

end
