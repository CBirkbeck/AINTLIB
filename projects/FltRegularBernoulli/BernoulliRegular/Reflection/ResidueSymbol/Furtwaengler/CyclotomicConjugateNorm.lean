module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Product of cyclotomic conjugates and the ideal norm

This file proves the REF-21.6 denominator computation:
the product of all cyclotomic Galois conjugates of an integral ideal, with
repeated conjugates counted, is the extension of its relative norm from
`ℤ` to `𝓞 K`.  Over `ℤ` that relative norm is the principal ideal generated
by the absolute ideal norm.

No split or residue-degree-one hypothesis appears.  The repeated factors are
accounted for by the stabilizer size, which is `e * f` in the Galois
fundamental identity.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Product of all cyclotomic conjugates of an ideal, counted with
multiplicity over `(ZMod p)ˣ`. -/
noncomputable def cyclotomicConjugateProductIdeal (B : Ideal (𝓞 K)) :
    Ideal (𝓞 K) :=
  ∏ a : CyclotomicUnitDelta p,
    cyclotomicGaloisConjugate (p := p) (K := K) a B

/-- The relative norm from `ℤ`, extended back to `𝓞 K`. -/
noncomputable def extendedRelNormIdeal (B : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ B)

@[simp] theorem cyclotomicConjugateProductIdeal_top :
    cyclotomicConjugateProductIdeal (p := p) (K := K) (⊤ : Ideal (𝓞 K)) = ⊤ := by
  simp [cyclotomicConjugateProductIdeal]

theorem cyclotomicConjugateProductIdeal_mul
    (I J : Ideal (𝓞 K)) :
    cyclotomicConjugateProductIdeal (p := p) (K := K) (I * J) =
      cyclotomicConjugateProductIdeal (p := p) (K := K) I *
        cyclotomicConjugateProductIdeal (p := p) (K := K) J := by
  simp [cyclotomicConjugateProductIdeal, cyclotomicGaloisConjugate_mul_ideal,
    Finset.prod_mul_distrib]

@[simp] theorem extendedRelNormIdeal_top :
    extendedRelNormIdeal (K := K) (⊤ : Ideal (𝓞 K)) = ⊤ := by
  rw [extendedRelNormIdeal, Ideal.relNorm_top, Ideal.map_top]

theorem extendedRelNormIdeal_mul (I J : Ideal (𝓞 K)) :
    extendedRelNormIdeal (K := K) (I * J) =
      extendedRelNormIdeal (K := K) I * extendedRelNormIdeal (K := K) J := by
  simp [extendedRelNormIdeal, Ideal.map_mul]

theorem coe_cyclotomicConjugates_eq_orbit (B : Ideal (𝓞 K)) :
    (cyclotomicConjugates (p := p) (K := K) B : Set (Ideal (𝓞 K))) =
      MulAction.orbit (CyclotomicUnitDelta p) B := by
  classical
  ext I
  rw [Finset.mem_coe, mem_cyclotomicConjugates_iff, MulAction.mem_orbit_iff]
  simp [cyclotomicMulAction_smul_def]

theorem cyclotomicStabilizer_card_eq_ramificationIdxIn_mul_inertiaDegIn
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥) :
    Fintype.card (MulAction.stabilizer (CyclotomicUnitDelta p) P) =
      (P.under ℤ).ramificationIdxIn (𝓞 K) *
        (P.under ℤ).inertiaDegIn (𝓞 K) := by
  classical
  letI : Fintype (MulAction.orbit (CyclotomicUnitDelta p) P) :=
    Set.fintypeRange (fun a : CyclotomicUnitDelta p ↦ a • P)
  have horbit_card :
      Fintype.card (MulAction.orbit (CyclotomicUnitDelta p) P) =
        (cyclotomicConjugates (p := p) (K := K) P).card := by
    have hn :
        (MulAction.orbit (CyclotomicUnitDelta p) P).ncard =
          (cyclotomicConjugates (p := p) (K := K) P).card := by
      rw [← coe_cyclotomicConjugates_eq_orbit (p := p) (K := K) P,
        Set.ncard_coe_finset]
    rw [← hn, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hgroup :
      (cyclotomicConjugates (p := p) (K := K) P).card *
          Fintype.card (MulAction.stabilizer (CyclotomicUnitDelta p) P) =
        p - 1 := by
    have h :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (CyclotomicUnitDelta p) P
    rw [horbit_card] at h
    have hcardΔ : Fintype.card (CyclotomicUnitDelta p) = p - 1 := by
      change Fintype.card ((ZMod p)ˣ) = p - 1
      rw [ZMod.card_units p]
    rwa [hcardΔ] at h
  have hfund :
      (cyclotomicConjugates (p := p) (K := K) P).card *
        ((P.under ℤ).ramificationIdxIn (𝓞 K) *
          (P.under ℤ).inertiaDegIn (𝓞 K)) = p - 1 :=
    cyclotomicConjugates_card_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p) (K := K) (q := P) hP_ne
  have hcard_pos :
      0 < (cyclotomicConjugates (p := p) (K := K) P).card :=
    Finset.card_pos.mpr
      ⟨P, self_mem_cyclotomicConjugates (p := p) (K := K) P⟩
  exact Nat.mul_left_cancel hcard_pos (hgroup.trans hfund.symm)

theorem cyclotomicConjugate_fiber_card_eq_ramificationIdxIn_mul_inertiaDegIn
    {P Q : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    (hQ : Q ∈ cyclotomicConjugates (p := p) (K := K) P) :
    ({a ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)) |
        cyclotomicGaloisConjugate (p := p) (K := K) a P = Q}.card) =
      (P.under ℤ).ramificationIdxIn (𝓞 K) *
        (P.under ℤ).inertiaDegIn (𝓞 K) := by
  classical
  obtain ⟨b, hb⟩ :=
    (mem_cyclotomicConjugates_iff (p := p) (K := K) P Q).mp hQ
  let e :
      {a : CyclotomicUnitDelta p //
        cyclotomicGaloisConjugate (p := p) (K := K) a P = Q} ≃
        MulAction.stabilizer (CyclotomicUnitDelta p) P := {
    toFun := fun a ↦
      ⟨b⁻¹ * a.1, by
        rw [MulAction.mem_stabilizer_iff]
        change cyclotomicGaloisConjugate (p := p) (K := K) (b⁻¹ * a.1) P = P
        rw [cyclotomicGaloisConjugate_mul, a.2, ← hb]
        rw [← cyclotomicGaloisConjugate_mul, inv_mul_cancel,
          cyclotomicGaloisConjugate_one]⟩
    invFun := fun c ↦
      ⟨b * c.1, by
        rw [← hb, cyclotomicGaloisConjugate_mul]
        have hc : cyclotomicGaloisConjugate (p := p) (K := K) c.1 P = P := by
          have hc_smul : c.1 • P = P := c.2
          simpa [cyclotomicMulAction_smul_def] using hc_smul
        rw [hc]⟩
    left_inv := by
      intro a
      apply Subtype.ext
      simp
    right_inv := by
      intro c
      apply Subtype.ext
      simp }
  have hfilter :
      ({a ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)) |
          cyclotomicGaloisConjugate (p := p) (K := K) a P = Q}.card) =
        Fintype.card {a : CyclotomicUnitDelta p //
          cyclotomicGaloisConjugate (p := p) (K := K) a P = Q} := by
    rw [Fintype.card_subtype]
  rw [hfilter, Fintype.card_congr e]
  exact cyclotomicStabilizer_card_eq_ramificationIdxIn_mul_inertiaDegIn
    (p := p) (K := K) hP_ne

theorem map_extendedRelNorm_prime_eq_cyclotomicConjugates_prod_pow
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥) :
    extendedRelNormIdeal (K := K) P =
      ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P,
        Q ^ ((P.under ℤ).ramificationIdxIn (𝓞 K) *
          (P.under ℤ).inertiaDegIn (𝓞 K)) := by
  classical
  let e := (P.under ℤ).ramificationIdxIn (𝓞 K)
  let f := (P.under ℤ).inertiaDegIn (𝓞 K)
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  have h_under_ne : P.under ℤ ≠ ⊥ :=
    under_ne_bot (K := K) (q := P) hP_ne
  haveI : (P.under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance h_under_ne
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP_ne
  haveI : PerfectField (FractionRing ℤ) := inferInstance
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ)) ℚ K
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ K
  have hrel :
      Ideal.relNorm ℤ P = (P.under ℤ) ^ f := by
    have h := Ideal.relNorm_eq_pow_of_isMaximal (R := ℤ) (S := 𝓞 K) P (P.under ℤ)
    dsimp [f]
    rw [Ideal.inertiaDegIn_eq_inertiaDeg (P.under ℤ) P Gal(K/ℚ),
      ← Ideal.inertiaDeg_eq_inertiaDeg' (p := P.under ℤ) (q := P)]
    exact h
  have hprimes :
      ((P.under ℤ).primesOver (𝓞 K)).toFinset =
        cyclotomicConjugates (p := p) (K := K) P := by
    rw [← Finset.coe_inj]
    rw [Set.coe_toFinset]
    exact (coe_cyclotomicConjugates (p := p) (K := K) (q := P)).symm
  have hmap_under :
      Ideal.map (algebraMap ℤ (𝓞 K)) (P.under ℤ) =
        ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P, Q ^ e := by
    have hmap :=
      Ideal.map_algebraMap_eq_finsetProd_pow
        (R := 𝓞 K) (S := ℤ) (p := P.under ℤ) h_under_ne
    rw [hprimes] at hmap
    trans ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P,
        Q ^ (P.under ℤ).ramificationIdx Q
    · exact hmap
    · refine Finset.prod_congr rfl ?_
      intro Q hQ
      haveI : Q.IsPrime :=
        isPrime_of_mem_cyclotomicConjugates (p := p) (K := K) hQ
      haveI : Q.LiesOver (P.under ℤ) :=
        ⟨(under_eq_of_mem_cyclotomicConjugates (p := p) (K := K) hQ).symm⟩
      dsimp [e]
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) Q Gal(K/ℚ),
        ← Ideal.ramificationIdx_eq_ramificationIdx' (q := Q) (hp := h_under_ne)]
  rw [extendedRelNormIdeal, hrel, Ideal.map_pow, hmap_under]
  dsimp [e, f]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro Q _hQ
  rw [pow_mul]

theorem cyclotomicConjugateProductIdeal_prime_eq_extendedRelNormIdeal
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥) :
    cyclotomicConjugateProductIdeal (p := p) (K := K) P =
      extendedRelNormIdeal (K := K) P := by
  classical
  let d :=
    (P.under ℤ).ramificationIdxIn (𝓞 K) *
      (P.under ℤ).inertiaDegIn (𝓞 K)
  have hprod :
      cyclotomicConjugateProductIdeal (p := p) (K := K) P =
        ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P, Q ^ d := by
    change
      (∏ a ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)),
        cyclotomicGaloisConjugate (p := p) (K := K) a P) =
        ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P, Q ^ d
    rw [Finset.prod_comp
      (s := (Finset.univ : Finset (CyclotomicUnitDelta p)))
      (f := fun Q : Ideal (𝓞 K) ↦ Q)
      (g := fun a : CyclotomicUnitDelta p ↦
        cyclotomicGaloisConjugate (p := p) (K := K) a P)]
    change
      ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P,
          Q ^
            ({a ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)) |
              cyclotomicGaloisConjugate (p := p) (K := K) a P = Q}.card) =
        ∏ Q ∈ cyclotomicConjugates (p := p) (K := K) P, Q ^ d
    refine Finset.prod_congr rfl ?_
    intro Q hQ
    have hfiber :
        ({a ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)) |
            cyclotomicGaloisConjugate (p := p) (K := K) a P = Q}.card) = d := by
      dsimp [d]
      exact cyclotomicConjugate_fiber_card_eq_ramificationIdxIn_mul_inertiaDegIn
        (p := p) (K := K) hP_ne hQ
    rw [hfiber]
  rw [hprod]
  exact (map_extendedRelNorm_prime_eq_cyclotomicConjugates_prod_pow
    (p := p) (K := K) hP_ne).symm

private theorem cyclotomicConjugateProductIdeal_multiset_prod_eq_extendedRelNormIdeal
    (m : Multiset (Ideal (𝓞 K)))
    (hm : ∀ P, P ∈ m → P.IsPrime ∧ P ≠ ⊥) :
    cyclotomicConjugateProductIdeal (p := p) (K := K) m.prod =
      extendedRelNormIdeal (K := K) m.prod := by
  classical
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons P m ih =>
      have hP : P.IsPrime ∧ P ≠ ⊥ := hm P (by simp)
      haveI : P.IsPrime := hP.1
      have hm' : ∀ Q, Q ∈ m → Q.IsPrime ∧ Q ≠ ⊥ := fun Q hQ ↦
        hm Q (by simp [hQ])
      rw [Multiset.prod_cons, cyclotomicConjugateProductIdeal_mul,
        extendedRelNormIdeal_mul,
        cyclotomicConjugateProductIdeal_prime_eq_extendedRelNormIdeal
          (p := p) (K := K) (P := P) hP.2,
        ih hm']

/-- The product of all cyclotomic conjugates of a nonzero ideal is the
extension of its relative norm from `ℤ`.  Repeated conjugates are counted
with the exact decomposition-group multiplicity. -/
theorem cyclotomicConjugateProductIdeal_eq_extendedRelNormIdeal
    {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    cyclotomicConjugateProductIdeal (p := p) (K := K) B =
      extendedRelNormIdeal (K := K) B := by
  rw [← Ideal.prod_normalizedFactors_eq_self hB]
  exact
    cyclotomicConjugateProductIdeal_multiset_prod_eq_extendedRelNormIdeal
      (p := p) (K := K)
      (UniqueFactorizationMonoid.normalizedFactors B)
      (fun P hP ↦ by
        obtain ⟨hP_prime, hP_ne, _hP_max⟩ := isPrime_of_mem_normalizedFactors hP
        exact ⟨hP_prime, hP_ne⟩)

/-- REF-21.6c3b denominator theorem: the product of all cyclotomic
conjugates is the principal ideal generated by the absolute ideal norm. -/
theorem cyclotomicConjugateProductIdeal_eq_absNorm_span
    {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    cyclotomicConjugateProductIdeal (p := p) (K := K) B =
      Ideal.span ({algebraMap ℤ (𝓞 K) (B.absNorm : ℤ)} : Set (𝓞 K)) := by
  rw [cyclotomicConjugateProductIdeal_eq_extendedRelNormIdeal (p := p) (K := K) hB]
  rw [extendedRelNormIdeal, Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]

/-- Norm-principal coprimality forces every conjugate of `α` to avoid every
prime factor of `B`.

This is the support bridge needed in REF-21.6c: it derives the denominator-side
Galois nonmembership from the actual norm ideal, not from a split-prime or
prime-by-prime vanishing assumption. -/
theorem cyclotomicRingOfIntegersEquiv_inv_notMem_of_absNorm_span_coprime
    {α : 𝓞 K} {B : Ideal (𝓞 K)} (hB : B ≠ ⊥)
    (hcop :
      IsCoprime
        (Ideal.span ({algebraMap ℤ (𝓞 K) (B.absNorm : ℤ)} : Set (𝓞 K)))
        (Ideal.span ({α} : Set (𝓞 K))))
    (a : CyclotomicUnitDelta p) {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors B) :
    cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P := by
  classical
  intro hmem
  obtain ⟨_, _hP_ne, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  haveI : P.IsMaximal := hP_max
  let σP := cyclotomicGaloisConjugate (p := p) (K := K) a P
  haveI : σP.IsMaximal := cyclotomicGaloisConjugate_isMaximal (p := p) (K := K) a P
  have hσP_ne_top : σP ≠ ⊤ := (inferInstance : σP.IsMaximal).ne_top
  have hα_mem_σP : α ∈ σP := by
    change α ∈ cyclotomicGaloisConjugate (p := p) (K := K) a P
    unfold cyclotomicGaloisConjugate
    rw [Ideal.mem_map_of_equiv]
    refine ⟨cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α, hmem, ?_⟩
    rw [← cyclotomicRingOfIntegersEquiv_mul_apply (p := p) (K := K) a a⁻¹ α,
      mul_inv_cancel, cyclotomicRingOfIntegersEquiv_one_apply]
  have hspan_le : Ideal.span ({α} : Set (𝓞 K)) ≤ σP := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hα_mem_σP
  have hB_le_P : B ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hσB_le_σP :
      cyclotomicGaloisConjugate (p := p) (K := K) a B ≤ σP := by
    change
      cyclotomicGaloisConjugate (p := p) (K := K) a B ≤
        cyclotomicGaloisConjugate (p := p) (K := K) a P
    rw [cyclotomicGaloisConjugate_le_iff]
    exact hB_le_P
  have hprod_le_σB :
      cyclotomicConjugateProductIdeal (p := p) (K := K) B ≤
        cyclotomicGaloisConjugate (p := p) (K := K) a B := by
    have hdvd :
        cyclotomicGaloisConjugate (p := p) (K := K) a B ∣
          cyclotomicConjugateProductIdeal (p := p) (K := K) B := by
      unfold cyclotomicConjugateProductIdeal
      exact Finset.dvd_prod_of_mem
        (fun b : CyclotomicUnitDelta p ↦
          cyclotomicGaloisConjugate (p := p) (K := K) b B)
        (Finset.mem_univ a)
    rwa [Ideal.dvd_iff_le] at hdvd
  have hnorm_le : Ideal.span ({algebraMap ℤ (𝓞 K) (B.absNorm : ℤ)} : Set (𝓞 K)) ≤ σP := by
    rw [← cyclotomicConjugateProductIdeal_eq_absNorm_span (p := p) (K := K) hB]
    exact hprod_le_σB.trans hσB_le_σP
  have htop_le : ⊤ ≤ σP := by
    rw [← hcop.sup_eq]
    exact sup_le hnorm_le hspan_le
  exact hσP_ne_top (top_le_iff.mp htop_le)

end Furtwaengler

end BernoulliRegular

end
