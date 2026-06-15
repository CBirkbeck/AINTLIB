import BernoulliRegular.FLT37.Eichler.HerbrandBoundAnalytic
import BernoulliRegular.FLT37.Eichler.ModuleStructure
import BernoulliRegular.FLT37.KummerUnits
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiRadicalNotPthPower
import FltRegular.MayAssume.Lemmas

/-!
# Eichler's first-case FLT argument for `p = 37` (`CaseIClose`)

This file formalises the *Eichler pigeonhole* descent that closes the first
case of Fermat's Last Theorem for the exponent `p = 37`, following Washington,
*Introduction to Cyclotomic Fields*, Theorem 6.23 (pp. 108–110).

The two inputs are already proved, axiom-clean, elsewhere in
`BernoulliRegular/FLT37/Eichler/`:

* **Herbrand bound** (`caseI_pRank_minus_bound_uncond`,
  `HerbrandBoundAnalytic.lean`): any `37`-torsion subgroup `C` of
  `ClassGroup (𝓞 (CyclotomicField 37 ℚ))` has `Nat.card C ≤ 37`.
* **`p`-torsion of the factor class** (`caseI_factor_class_pow_eq_one`,
  `ModuleStructure.lean`): the `p`-th-root ideal class `[I_ζ]` arising from
  `span {a + ζ b} = I_ζ ^ 37` is `37`-torsion.

## The argument

1. **`C` assembly + Herbrand bound** (`caseISubgroup_card_le`). For a putative
   Case-I solution `a^37 + b^37 = c^37` (coprime, `37 ∤ abc`), the classes
   `[I_{ζ^i}]` (`i = 1, …, 5`) of the `p`-th-root ideals are all `37`-torsion
   (`factorClass_pow_eq_one`). The subgroup `C` they generate
   (`caseISubgroup`) is therefore `37`-torsion (`caseISubgroup_pow_eq_one`), so
   the Herbrand bound gives `Nat.card C ≤ 37`.

2. **Pigeonhole (DM-A3)** (`caseI_exists_relation`). With `r = ⌊√37⌋ − 1 = 5`,
   the `37^5` products `∏_{i=1}^{5} [I_{ζ^i}]^{b_i}` (`0 ≤ b_i < 37`) all lie in
   `C`. Since `37^5 > 37 ≥ Nat.card C`, two distinct exponent tuples collide
   (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`), producing a nonzero
   integer tuple `(a_i)`, `−37 < a_i < 37`, with
   `∏_{i=1}^{5} [I_{ζ^i}]^{a_i} = 1` in the class group.

3. **Lift to an element relation** (`caseI_exists_element_relation`). Splitting
   the integer exponents into nonnegative parts gives a natural-exponent class
   equation `∏ [I_{ζ^{i+1}}]^{nPos i} = ∏ [I_{ζ^{i+1}}]^{nNeg i}`
   (`caseI_exists_nat_relation`). Via `ClassGroup.mk0_eq_mk0_iff` and the
   `p`-th-power identity `span {a + ζ^i b} = I_{ζ^i}^{37}`
   (`factorProdNZ_pow_val`), this becomes a genuine element equation in
   `𝓞 (CyclotomicField 37 ℚ)`:
   `x^{37} · ∏ (a + ζ^{i+1} b)^{nPos i} = (y^{37} · ∏ (a + ζ^{i+1} b)^{nNeg i}) · u`
   with `x, y ≠ 0` and `u` a unit. The factor elements are nonzero
   (`factorElt_ne_zero`).

## Analytic lemmas landed (the elementary half of the DM-A4 finish)

Two of the analytic inputs to the Washington pp. 109–110 finish are proved
here, axiom-clean, directly from mathlib's cyclotomic integral power basis:

* **Lemma 1.8** (`caseI_pow_sub_intCast_mem`): for `α ∈ 𝓞 K`, `α^37` is
  congruent modulo `37` to a rational integer. Proved via the freshman's dream
  in the characteristic-`37` quotient `𝓞 K ⧸ (37)`, using `ζ^37 = 1` and
  Fermat.
* **Lemma 1.9** (`caseI_dvd_of_sum_zeta_pow_mem`): an integer combination
  `∑_{k < 36} c_k ζ^k` lying in `(37)` forces `37 ∣ c_k` for all `k`. Proved
  from the `ℤ`-basis `1, ζ, …, ζ^{35}` of `𝓞 K`.

(The auxiliary `thirtyseven_mem_nonunits` — `(37 : 𝓞 K)` is not a unit — is the
input to the characteristic-`37` quotient.)

## Remaining work: the analytic Vandermonde finish (DM-A4)

The element relation of step 3 is the input consumed by the rest of the
Washington pp. 109–110 finish. Unlike the repo's classical Case-I finish (which
is Bernoulli/parity-routed via `MirimanoffBernoulliIdentity` and is unavailable
here because `37` is irregular), this finish is self-contained, and its
analytic inputs are now all in place:

* **Prop 1.5** (unit = root of unity × real) is available in the repo as
  `BernoulliRegular.FLT37.exists_zeta_pow_mul_real_eq_unit` (Kummer's units
  lemma, for any cyclotomic CM `ℚ(ζ_p)`): every unit `u : (𝓞 K)ˣ` is
  `ζ^m · algebraMap v⁺` with `v⁺ : (𝓞 K⁺)ˣ` real.
* **Lemma 1.8** (`caseI_pow_sub_intCast_mem`) and **Lemma 1.9**
  (`caseI_dvd_of_sum_zeta_pow_mem`) are proved here.

What remains is the polynomial bookkeeping that glues these together:

* Apply Prop 1.5 to the unit `u` of step 3 and Lemma 1.8 to clear `x^{37},
  y^{37}`, obtaining `∏ ((a + ζ^i b)/(b + ζ^i a))^{a_i} ≡ ζ^v (mod 37)`.
* Build `F, G ∈ ℤ[T]` with `F ≡ ζ^v G (mod 37)`, of degree `1 + r(r+1) = 31`;
  multiply by `∏ (x + ζ^i y)(y + ζ^i x)`, differentiate `(1 - T)`, and apply
  Lemma 1.9 to force `v ≡ 0` and (leading coefficient) `a² ≡ b²`, hence
  `a ≡ ±b (mod 37)`; the symmetric `a ≡ ±c (mod 37)` then makes
  `±a^{37} ± a^{37} ≡ a^{37} (mod 37)` impossible (`37 ∤ abc`, `37 ≠ 3`).

## References

* Washington, *Introduction to Cyclotomic Fields*, Theorem 6.23, pp. 108–110.
* `BernoulliRegular.FLT37.Eichler.caseI_pRank_minus_bound_uncond`.
* `BernoulliRegular.FLT37.Eichler.caseI_factor_class_pow_eq_one`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Ideal Polynomial

open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace Eichler

private instance : Fact (Nat.Prime 37) := ⟨by decide⟩

private def zetaPowBasis_aux : Module.Basis (Fin 36) ℤ (𝓞 (CyclotomicField 37 ℚ)) :=
  (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).integralPowerBasis.basis.reindex (finCongr (by
    rw [IsPrimitiveRoot.integralPowerBasis_dim]; decide))

private theorem zetaPowBasis_aux_apply (k : Fin 36) :
    zetaPowBasis_aux k = (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (k : ℕ) := by
  rw [zetaPowBasis_aux, Module.Basis.reindex_apply,
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).integralPowerBasis.basis_eq_pow,
    IsPrimitiveRoot.integralPowerBasis_gen]
  congr 1

/-- **Lemma 1.9 (`ℤ/(37)`-linear independence).** If an integer combination
`∑_{k < 36} c_k · ζ^k` of the powers `1, ζ, …, ζ^{35}` lies in the ideal `(37)`
of `𝓞 (CyclotomicField 37 ℚ)`, then `37 ∣ c_k` for every `k`. -/
theorem caseI_dvd_of_sum_zeta_pow_mem
    (c : Fin 36 → ℤ)
    (hmem : (∑ k : Fin 36, (c k : 𝓞 (CyclotomicField 37 ℚ)) *
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) ^ (k : ℕ)) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) :
    ∀ k, (37 : ℤ) ∣ c k := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζdef
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨z, hz⟩ := hmem
  set d : Fin 36 → ℤ := fun k ↦ zetaPowBasis_aux.repr z k with hd
  have hzsum : z = ∑ k : Fin 36, d k • ζ ^ (k : ℕ) := by
    conv_lhs => rw [← zetaPowBasis_aux.sum_repr z]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [hd, zetaPowBasis_aux_apply])
  intro k
  have h37 : ∑ k : Fin 36, ((37 * d k : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ) =
      ∑ k : Fin 36, (c k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ) := by
    rw [← hz, hzsum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    push_cast; rw [zsmul_eq_mul]; ring
  have hcomb : ∑ k : Fin 36, ((c k - 37 * d k : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ)
      = 0 := by
    have hexpand : ∑ k : Fin 36, ((c k - 37 * d k : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ)
        = (∑ k : Fin 36, (c k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ)) -
          ∑ k : Fin 36, ((37 * d k : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ ↦ ?_)
      push_cast; ring
    rw [hexpand, h37, sub_self]
  have hvanish := Fintype.linearIndependent_iff.mp zetaPowBasis_aux.linearIndependent
    (fun k ↦ ((c k - 37 * d k : ℤ))) (by
      simpa only [zsmul_eq_mul, zetaPowBasis_aux_apply] using hcomb) k
  exact ⟨d k, by omega⟩

/-- `(37 : 𝓞 (CyclotomicField 37 ℚ))` is not a unit: otherwise `1 ∈ (37)`, and
Lemma 1.9 (applied to the constant `1 = ζ^0`) would give `37 ∣ 1`. -/
theorem thirtyseven_mem_nonunits :
    (37 : 𝓞 (CyclotomicField 37 ℚ)) ∈ nonunits (𝓞 (CyclotomicField 37 ℚ)) := by
  rw [mem_nonunits_iff]
  intro hu
  have h1mem : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    rw [Ideal.mem_span_singleton]
    exact hu.dvd
  have hdvd := caseI_dvd_of_sum_zeta_pow_mem (Pi.single (0 : Fin 36) (1 : ℤ)) (by
    have hsum : (∑ k : Fin 36, (((Pi.single (0 : Fin 36) (1 : ℤ) : Fin 36 → ℤ) k) :
        𝓞 (CyclotomicField 37 ℚ)) *
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) ^ (k : ℕ)) = 1 := by
      rw [Finset.sum_eq_single (0 : Fin 36)]
      · simp
      · intro k _ hk; rw [Pi.single_eq_of_ne hk]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]; exact h1mem) 0
  rw [Pi.single_eq_same] at hdvd
  omega

private theorem thirtyseven_dvd_pow_sub_self (m : ℤ) : (37 : ℤ) ∣ m ^ 37 - m := by
  have : ((m ^ 37 - m : ℤ) : ZMod 37) = 0 := by
    push_cast
    rw [ZMod.pow_card (p := 37) (m : ZMod 37)]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 37).mp this

/-- **Lemma 1.8 (Washington).** For `α ∈ 𝓞 (CyclotomicField 37 ℚ)`, the `37`-th
power `α^37` is congruent modulo `37` to a rational integer: there is `a : ℤ`
with `α^37 − a ∈ (37)`.

Proof: expand `α = ∑_{k<36} b_k ζ^k` in the integral power basis. In the
quotient `Q = 𝓞 K ⧸ (37)` (characteristic `37`, via `thirtyseven_mem_nonunits`),
the freshman's dream gives `α^37 = ∑ (b_k ζ^k)^37 = ∑ b_k^37 (ζ^37)^k`, and
`ζ^37 = 1`, so `α^37 = ∑ b_k^37 ≡ ∑ b_k (mod 37)` by Fermat. Take `a = ∑ b_k`. -/
theorem caseI_pow_sub_intCast_mem
    (α : 𝓞 (CyclotomicField 37 ℚ)) :
    ∃ a : ℤ, α ^ 37 - (a : 𝓞 (CyclotomicField 37 ℚ)) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζdef
  set pb := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).integralPowerBasis with hpb
  have hdim : pb.dim = 36 := by
    rw [hpb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
  have hbgen : pb.gen = ζ := by rw [hpb, IsPrimitiveRoot.integralPowerBasis_gen]
  set b : Module.Basis (Fin 36) ℤ (𝓞 (CyclotomicField 37 ℚ)) :=
    pb.basis.reindex (finCongr hdim) with hb
  have hbk : ∀ k : Fin 36, b k = ζ ^ (k : ℕ) := by
    intro k
    rw [hb, Module.Basis.reindex_apply, pb.basis_eq_pow, hbgen]; congr 1
  set v : Fin 36 → ℤ := fun k ↦ b.repr α k with hv
  have hαsum : α = ∑ k : Fin 36, v k • ζ ^ (k : ℕ) := by
    conv_lhs => rw [← b.sum_repr α]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [hv, hbk])
  refine ⟨∑ k : Fin 36, v k, ?_⟩
  set I : Ideal (𝓞 (CyclotomicField 37 ℚ)) :=
    Ideal.span ({((37 : ℕ) : 𝓞 (CyclotomicField 37 ℚ))} : Set _) with hI
  have hnonunit : ((37 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) ∈
      nonunits (𝓞 (CyclotomicField 37 ℚ)) := by
    rw [Nat.cast_ofNat]; exact thirtyseven_mem_nonunits
  haveI hchar : CharP ((𝓞 (CyclotomicField 37 ℚ)) ⧸ I) 37 :=
    CharP.quotient (R := 𝓞 (CyclotomicField 37 ℚ)) 37 hnonunit
  have hmem_iff : ∀ z : 𝓞 (CyclotomicField 37 ℚ), z ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ↔ z ∈ I := by
    intro z; rw [hI, Nat.cast_ofNat]
  rw [hmem_iff, ← Ideal.Quotient.eq_zero_iff_mem]
  set mk := Ideal.Quotient.mk I with hmk
  have hζ37 : ζ ^ 37 = 1 := by
    rw [hζdef]
    exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
  have hmkζ37 : (mk ζ) ^ 37 = 1 := by rw [← map_pow, hζ37, map_one]
  have hfermat : ∀ k : Fin 36, (mk (v k : 𝓞 (CyclotomicField 37 ℚ))) ^ 37 =
      mk (v k : 𝓞 (CyclotomicField 37 ℚ)) := by
    intro k
    rw [← map_pow, ← sub_eq_zero, ← map_sub, hmk, Ideal.Quotient.eq_zero_iff_mem, hI,
      Ideal.mem_span_singleton]
    obtain ⟨t, ht⟩ := thirtyseven_dvd_pow_sub_self (v k)
    refine ⟨(t : 𝓞 (CyclotomicField 37 ℚ)), ?_⟩
    have : ((v k ^ 37 - v k : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) =
        ((37 * t : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) := by rw [ht]
    push_cast at this ⊢; linear_combination this
  rw [map_sub, map_pow]
  have hmkα : mk α = ∑ k : Fin 36,
      (mk (v k : 𝓞 (CyclotomicField 37 ℚ))) * (mk ζ) ^ (k : ℕ) := by
    rw [hmk, hαsum, map_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [zsmul_eq_mul, map_mul, map_pow])
  rw [hmkα, sum_pow_char]
  have hterm : ∀ k : Fin 36,
      (mk (v k : 𝓞 (CyclotomicField 37 ℚ)) * (mk ζ) ^ (k : ℕ)) ^ 37 =
        mk (v k : 𝓞 (CyclotomicField 37 ℚ)) := by
    intro k
    rw [mul_pow, ← pow_mul, mul_comm (k : ℕ) 37, pow_mul, hmkζ37, one_pow, mul_one,
      hfermat k]
  rw [Finset.sum_congr rfl (fun k _ ↦ hterm k), hmk, ← map_sum, sub_eq_zero]
  congr 1
  push_cast
  rfl

variable {a b c : ℤ}

private def factorRoot (i : ℕ) : 𝓞 (CyclotomicField 37 ℚ) :=
  ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) ^ i

private theorem factorRoot_mem (i : ℕ) :
    factorRoot i ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) := by
  have hμ : IsPrimitiveRoot
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) 37 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
  rw [Polynomial.mem_nthRootsFinset (by norm_num)]
  unfold factorRoot
  rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

private def factorIdealData
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    { I : Ideal (𝓞 (CyclotomicField 37 ℚ)) //
      ∃ hI : I ∈ (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰,
        Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) + factorRoot i *
          (b : 𝓞 (CyclotomicField 37 ℚ))} : Set _) = I ^ 37 ∧
        ClassGroup.mk0 ⟨I, hI⟩ ^ 37 = 1 } :=
  ⟨Classical.choose
      (caseI_factor_class_pow_eq_one (p := 37) (by norm_num) heq hgcd hcaseI
        (factorRoot_mem i)),
    Classical.choose_spec
      (caseI_factor_class_pow_eq_one (p := 37) (by norm_num) heq hgcd hcaseI
        (factorRoot_mem i))⟩

private def factorNZ
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰ :=
  ⟨(factorIdealData heq hgcd hcaseI i).1, (factorIdealData heq hgcd hcaseI i).2.choose⟩

private def factorClass
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    ClassGroup (𝓞 (CyclotomicField 37 ℚ)) :=
  ClassGroup.mk0 (factorNZ heq hgcd hcaseI i)

private theorem factorClass_eq_mk0
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    factorClass heq hgcd hcaseI i = ClassGroup.mk0 (factorNZ heq hgcd hcaseI i) :=
  rfl

private theorem factorClass_pow_eq_one
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    factorClass heq hgcd hcaseI i ^ 37 = 1 :=
  (factorIdealData heq hgcd hcaseI i).2.choose_spec.2

-- unifying `(factorNZ … : Ideal _)` with the `Classical.choose` of `factorIdealData` exceeds
-- the default recursion depth
set_option maxRecDepth 4000 in
private theorem factorNZ_span
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) + factorRoot i *
        (b : 𝓞 (CyclotomicField 37 ℚ))} : Set _) =
      (factorNZ heq hgcd hcaseI i : Ideal (𝓞 (CyclotomicField 37 ℚ))) ^ 37 :=
  (factorIdealData heq hgcd hcaseI i).2.choose_spec.1

private def caseISubgroup
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    Subgroup (ClassGroup (𝓞 (CyclotomicField 37 ℚ))) :=
  Subgroup.closure
    (Set.range fun i : Fin 5 ↦ factorClass heq hgcd hcaseI (i.1 + 1))

private theorem caseISubgroup_pow_eq_one
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
    (x : caseISubgroup heq hgcd hcaseI) :
    x ^ 37 = 1 := by
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  obtain ⟨x, hx⟩ := x
  refine Subgroup.closure_induction
    (p := fun g _ ↦ g ^ 37 = 1) ?_ ?_ ?_ ?_ hx
  · rintro g ⟨i, rfl⟩
    exact factorClass_pow_eq_one heq hgcd hcaseI (i.1 + 1)
  · exact one_pow 37
  · intro g₁ g₂ _ _ h₁ h₂
    rw [mul_pow, h₁, h₂, mul_one]
  · intro g _ h
    rw [inv_pow, h, inv_one]

private theorem caseISubgroup_card_le
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    haveI : IsCMField (CyclotomicField 37 ℚ) :=
      isCMField_of_cyclotomic (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num)
    Nat.card (caseISubgroup heq hgcd hcaseI) ≤ 37 := by
  haveI : IsCMField (CyclotomicField 37 ℚ) :=
    isCMField_of_cyclotomic (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num)
  exact caseI_pRank_minus_bound_uncond (caseISubgroup heq hgcd hcaseI)
    (caseISubgroup_pow_eq_one heq hgcd hcaseI)

private def caseIGen
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : Fin 5) :
    caseISubgroup heq hgcd hcaseI :=
  ⟨factorClass heq hgcd hcaseI (i.1 + 1),
    Subgroup.subset_closure ⟨i, rfl⟩⟩

private def caseIProd
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (t : Fin 5 → Fin 37) :
    caseISubgroup heq hgcd hcaseI :=
  ∏ i : Fin 5, caseIGen heq hgcd hcaseI i ^ (t i).1

private theorem caseI_exists_collision
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ t t' : Fin 5 → Fin 37, t ≠ t' ∧
      (∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (t i).1) =
        ∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (t' i).1 := by
  haveI : IsCMField (CyclotomicField 37 ℚ) :=
    isCMField_of_cyclotomic (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num)
  haveI : Fintype (caseISubgroup heq hgcd hcaseI) := Fintype.ofFinite _
  have hcard : Fintype.card (caseISubgroup heq hgcd hcaseI) <
      Fintype.card (Fin 5 → Fin 37) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hle : Nat.card (caseISubgroup heq hgcd hcaseI) ≤ 37 :=
      caseISubgroup_card_le heq hgcd hcaseI
    rw [Nat.card_eq_fintype_card] at hle
    calc Fintype.card (caseISubgroup heq hgcd hcaseI) ≤ 37 := hle
      _ < 37 ^ 5 := by norm_num
  obtain ⟨t, _, t', _, hne, hmap⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin 5 → Fin 37)))
      (t := (Finset.univ : Finset (caseISubgroup heq hgcd hcaseI)))
      (by rwa [Finset.card_univ, Finset.card_univ])
      (f := caseIProd heq hgcd hcaseI)
      (fun x _ ↦ Finset.mem_univ _)
  refine ⟨t, t', hne, ?_⟩
  have hval : ((caseIProd heq hgcd hcaseI t : caseISubgroup heq hgcd hcaseI) :
      ClassGroup (𝓞 (CyclotomicField 37 ℚ))) =
      ((caseIProd heq hgcd hcaseI t' : caseISubgroup heq hgcd hcaseI) :
      ClassGroup (𝓞 (CyclotomicField 37 ℚ))) := by rw [hmap]
  simpa only [caseIProd, caseIGen, SubmonoidClass.coe_finsetProd,
    SubmonoidClass.coe_pow] using hval

private theorem caseI_exists_relation
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ e : Fin 5 → ℤ, (∃ i, e i ≠ 0) ∧ (∀ i, -37 < e i ∧ e i < 37) ∧
      (∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (e i)) = 1 := by
  obtain ⟨t, t', hne, hmap⟩ := caseI_exists_collision heq hgcd hcaseI
  refine ⟨fun i ↦ ((t i).1 : ℤ) - ((t' i).1 : ℤ), ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hne
    funext i
    have hi : ((t i).1 : ℤ) = ((t' i).1 : ℤ) := by have := h i; omega
    exact Fin.ext (by exact_mod_cast hi)
  · intro i
    simp only
    have h1 : (t i).1 < 37 := (t i).2
    have h2 : (t' i).1 < 37 := (t' i).2
    omega
  · have hzpow : ∀ i : Fin 5,
        factorClass heq hgcd hcaseI (i.1 + 1) ^ (((t i).1 : ℤ) - ((t' i).1 : ℤ)) =
          (factorClass heq hgcd hcaseI (i.1 + 1) ^ (t i).1) *
          (factorClass heq hgcd hcaseI (i.1 + 1) ^ (t' i).1)⁻¹ := by
      intro i
      rw [zpow_sub, zpow_natCast, zpow_natCast]
    simp only [hzpow]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hmap,
      mul_inv_cancel]

private theorem zpow_eq_toNat_mul_inv
    (g : ClassGroup (𝓞 (CyclotomicField 37 ℚ))) (z : ℤ) :
    g ^ z = (g ^ z.toNat) * (g ^ (-z).toNat)⁻¹ := by
  rcases le_or_gt 0 z with h | h
  · rw [Int.toNat_of_nonpos (by omega : -z ≤ 0), pow_zero, inv_one, mul_one,
      ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [Int.toNat_of_nonpos h.le, pow_zero, one_mul, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega : 0 ≤ -z), ← zpow_neg, neg_neg]

private theorem caseI_exists_nat_relation
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ nPos nNeg : Fin 5 → ℕ, nPos ≠ nNeg ∧ (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      (∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (nPos i)) =
        ∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (nNeg i) := by
  obtain ⟨e, ⟨i₀, hi₀⟩, hbound, hrel⟩ := caseI_exists_relation heq hgcd hcaseI
  refine ⟨fun i ↦ (e i).toNat, fun i ↦ (-(e i)).toNat, ?_, ?_, ?_, ?_⟩
  · intro hcontra
    have hci := congrFun hcontra i₀
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · rw [Int.toNat_of_nonpos hneg.le] at hci
      rw [eq_comm, Int.toNat_eq_zero] at hci; omega
    · rw [Int.toNat_of_nonpos (by omega : -(e i₀) ≤ 0)] at hci
      rw [Int.toNat_eq_zero] at hci; omega
  · intro i; simp only; have h1 := (hbound i).1; have h2 := (hbound i).2; omega
  · intro i; simp only; have h1 := (hbound i).1; have h2 := (hbound i).2; omega
  · have hprod1 : (∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (e i).toNat) *
        (∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (-(e i)).toNat)⁻¹ = 1 := by
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← hrel]
      exact Finset.prod_congr rfl (fun i _ ↦ (zpow_eq_toNat_mul_inv _ _).symm)
    rwa [mul_inv_eq_one] at hprod1

private def factorProdNZ
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (n : Fin 5 → ℕ) :
    (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰ :=
  ∏ i : Fin 5, factorNZ heq hgcd hcaseI (i.1 + 1) ^ (n i)

private theorem mk0_factorProdNZ
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (n : Fin 5 → ℕ) :
    ClassGroup.mk0 (factorProdNZ heq hgcd hcaseI n) =
      ∏ i : Fin 5, factorClass heq hgcd hcaseI (i.1 + 1) ^ (n i) := by
  unfold factorProdNZ
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ ↦ by rw [map_pow, factorClass_eq_mk0])

private def factorElt (a b : ℤ) (i : ℕ) : 𝓞 (CyclotomicField 37 ℚ) :=
  (a : 𝓞 (CyclotomicField 37 ℚ)) + factorRoot i * (b : 𝓞 (CyclotomicField 37 ℚ))

private theorem factorElt_ne_zero
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : ℕ) :
    factorElt a b i ≠ 0 := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hcaseI (by simp)
  intro hfac0
  have hμ : IsPrimitiveRoot
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) 37 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
  have hprod := hμ.pow_add_pow_eq_prod_add_mul (a : 𝓞 (CyclotomicField 37 ℚ))
    (b : 𝓞 (CyclotomicField 37 ℚ)) (by norm_num)
  have hzero : (∏ η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)),
      ((a : 𝓞 (CyclotomicField 37 ℚ)) + η * (b : 𝓞 (CyclotomicField 37 ℚ)))) = 0 :=
    Finset.prod_eq_zero (factorRoot_mem i) hfac0
  have hcast : (a : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 + (b : 𝓞 (CyclotomicField 37 ℚ)) ^ 37
      = (c : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
    rw [← Int.cast_pow, ← Int.cast_pow, ← Int.cast_add, heq, Int.cast_pow]
  rw [hprod, hzero] at hcast
  have : (c : 𝓞 (CyclotomicField 37 ℚ)) = 0 := by
    simpa using pow_eq_zero_iff (by norm_num : 37 ≠ 0) |>.mp hcast.symm
  exact hc0 (by exact_mod_cast this)

private theorem factorProdNZ_pow_val
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (n : Fin 5 → ℕ) :
    ((factorProdNZ heq hgcd hcaseI n : Ideal (𝓞 (CyclotomicField 37 ℚ))) ^ 37) =
      ∏ i : Fin 5, Ideal.span ({factorElt a b (i.1 + 1)} : Set _) ^ (n i) := by
  unfold factorProdNZ factorElt
  rw [Submonoid.coe_finsetProd, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm, pow_mul, ← factorNZ_span]

private theorem caseI_exists_element_relation
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (x y : 𝓞 (CyclotomicField 37 ℚ))
      (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      nPos ≠ nNeg ∧ (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧ x ≠ 0 ∧ y ≠ 0 ∧
      x ^ 37 * ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nPos i) =
        (y ^ 37 * ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nNeg i)) *
          (u : 𝓞 (CyclotomicField 37 ℚ)) := by
  obtain ⟨nPos, nNeg, hne, hPosb, hNegb, hrel⟩ :=
    caseI_exists_nat_relation heq hgcd hcaseI
  have hmk0 : ClassGroup.mk0 (factorProdNZ heq hgcd hcaseI nPos) =
      ClassGroup.mk0 (factorProdNZ heq hgcd hcaseI nNeg) := by
    rw [mk0_factorProdNZ, mk0_factorProdNZ, hrel]
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hmk0
  have hpow : (Ideal.span ({x} : Set _)) ^ 37 *
        (factorProdNZ heq hgcd hcaseI nPos : Ideal (𝓞 (CyclotomicField 37 ℚ))) ^ 37 =
      (Ideal.span ({y} : Set _)) ^ 37 *
        (factorProdNZ heq hgcd hcaseI nNeg : Ideal (𝓞 (CyclotomicField 37 ℚ))) ^ 37 := by
    rw [← mul_pow, ← mul_pow, hxy]
  rw [factorProdNZ_pow_val, factorProdNZ_pow_val] at hpow
  have hspan : ∀ (z : 𝓞 (CyclotomicField 37 ℚ)) (n : Fin 5 → ℕ),
      (Ideal.span ({z} : Set _)) ^ 37 *
        ∏ i : Fin 5, Ideal.span ({factorElt a b (i.1 + 1)} : Set _) ^ (n i) =
      Ideal.span ({z ^ 37 * ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (n i)} : Set _) := by
    intro z n
    have hprod : (∏ i : Fin 5, Ideal.span ({factorElt a b (i.1 + 1)} : Set _) ^ (n i)) =
        Ideal.span ({∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (n i)} : Set _) := by
      rw [← Ideal.prod_span_singleton]
      exact Finset.prod_congr rfl (fun i _ ↦ Ideal.span_singleton_pow _ _)
    rw [Ideal.span_singleton_pow, hprod, Ideal.span_singleton_mul_span_singleton]
  rw [hspan, hspan] at hpow
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hpow
  refine ⟨nPos, nNeg, x, y, u⁻¹, hne, hPosb, hNegb, hx, hy, ?_⟩
  rw [← hu, mul_assoc, Units.mul_inv, mul_one]

private abbrev eichlerCM : IsCMField (CyclotomicField 37 ℚ) :=
  isCMField_of_cyclotomic (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num)

private theorem conj_zeta_eq :
    haveI := eichlerCM
    (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
        (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 := by
  haveI := eichlerCM
  have h := complexConj_apply_zeta (p := 37) (K := CyclotomicField 37 ℚ)
  apply RingOfIntegers.ext
  rw [h]

private theorem conj_factorRoot (k : ℕ) :
    haveI := eichlerCM
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (factorRoot k) =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (36 * k) := by
  haveI := eichlerCM
  unfold factorRoot
  rw [map_pow, conj_zeta_eq, ← pow_mul, mul_comm]

private theorem conj_factorElt (a b : ℤ) (k : ℕ) :
    haveI := eichlerCM
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (factorElt a b k) =
      (a : 𝓞 (CyclotomicField 37 ℚ)) +
        (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (36 * k) *
          (b : 𝓞 (CyclotomicField 37 ℚ)) := by
  haveI := eichlerCM
  unfold factorElt
  rw [map_add, map_mul, conj_factorRoot]
  congr 1 <;> [exact map_intCast _ a; rw [map_intCast]]

private theorem zetaSubOne_dvd_intCast_iff (n : ℤ) :
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ (n : 𝓞 (CyclotomicField 37 ℚ)))
      ↔ (37 : ℤ) ∣ n := by
  have hμ : IsPrimitiveRoot
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) 37 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
  exact LehmerVandiver.CaseI.zetaSubOne_dvd_Int_iff_p_dvd_OK (p := 37) (hζ := hμ)

private theorem zetaSubOne_not_dvd_factorElt
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (k : ℕ) :
    ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      factorElt a b k) := by
  have hμ : IsPrimitiveRoot
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) 37 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
  have hc : ¬ (37 : ℤ) ∣ c := fun h ↦ hcaseI (h.mul_left _)
  have hprod := hμ.pow_add_pow_eq_prod_add_mul (a : 𝓞 (CyclotomicField 37 ℚ))
    (b : 𝓞 (CyclotomicField 37 ℚ)) (by norm_num)
  have hcast : (a : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 + (b : 𝓞 (CyclotomicField 37 ℚ)) ^ 37
      = (c : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
    rw [← Int.cast_pow, ← Int.cast_pow, ← Int.cast_add, heq, Int.cast_pow]
  rw [hcast] at hprod
  have hcdvd : ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      (c : 𝓞 (CyclotomicField 37 ℚ)) ^ 37) := by
    intro h
    have hπ_prime : Prime ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) :=
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).zeta_sub_one_prime'
    have hcc : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
        (c : 𝓞 (CyclotomicField 37 ℚ)) := hπ_prime.dvd_of_dvd_pow h
    exact hc ((zetaSubOne_dvd_intCast_iff c).mp hcc)
  intro hk
  apply hcdvd
  rw [hprod]
  exact hk.trans (Finset.dvd_prod_of_mem _ (factorRoot_mem k))

private theorem conj_mem_span_iff (z : 𝓞 (CyclotomicField 37 ℚ)) :
    haveI := eichlerCM
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) z ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ↔
      z ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  haveI := eichlerCM
  have h37 : ∀ z : 𝓞 (CyclotomicField 37 ℚ), ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
      ((37 : 𝓞 (CyclotomicField 37 ℚ)) * z) =
      (37 : 𝓞 (CyclotomicField 37 ℚ)) *
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) z := by
    intro z
    rw [map_mul, show (37 : 𝓞 (CyclotomicField 37 ℚ)) =
      ((37 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) by push_cast; ring, map_intCast]
  have hinv : ∀ z : 𝓞 (CyclotomicField 37 ℚ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
        (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) z) = z := by
    intro z
    apply RingOfIntegers.ext
    rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj,
      complexConj_apply_apply]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · intro ⟨w, hw⟩
    refine ⟨ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w, ?_⟩
    have := congrArg (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)) hw
    rwa [hinv, h37] at this
  · intro ⟨w, hw⟩
    exact ⟨ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w, by rw [hw, h37]⟩

private theorem caseI_conj_pow_sub_intCast
    (α : 𝓞 (CyclotomicField 37 ℚ)) :
    haveI := eichlerCM
    ∃ n : ℤ, (α ^ 37 - (n : 𝓞 (CyclotomicField 37 ℚ)) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) ∧
      ((ringOfIntegersComplexConj (CyclotomicField 37 ℚ) α) ^ 37 -
        (n : 𝓞 (CyclotomicField 37 ℚ)) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) := by
  haveI := eichlerCM
  obtain ⟨n, hn⟩ := caseI_pow_sub_intCast_mem α
  refine ⟨n, hn, ?_⟩
  have hconj : ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
      (α ^ 37 - (n : 𝓞 (CyclotomicField 37 ℚ))) =
      (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) α) ^ 37 -
        (n : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [map_sub, map_pow, map_intCast]
  rw [← hconj]
  exact (conj_mem_span_iff _).mpr hn

private theorem coe_unitsComplexConj (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    haveI := eichlerCM
    ((unitsComplexConj (CyclotomicField 37 ℚ) u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
      𝓞 (CyclotomicField 37 ℚ)) =
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (u : 𝓞 (CyclotomicField 37 ℚ)) :=
  rfl

private theorem caseI_conj_pair_eq
    (A B : 𝓞 (CyclotomicField 37 ℚ)) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hAB : A = B * (u : 𝓞 (CyclotomicField 37 ℚ))) :
    haveI := eichlerCM
    ∃ m : ℕ, A * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) B =
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * B *
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) A := by
  haveI := eichlerCM
  set J := ringOfIntegersComplexConj (CyclotomicField 37 ℚ) with hJ
  set ζU := ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.isUnit
    (by norm_num)).unit with hζU
  obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) u (by norm_num)
  refine ⟨m, ?_⟩
  set Ju := unitsComplexConj (CyclotomicField 37 ℚ) u with hJu
  have hu_eq : (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) = (ζU ^ m) ^ 2 * Ju := by
    rw [← hm]; group
  have hJA : J A = J B * (Ju : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [hAB, map_mul, coe_unitsComplexConj]
  have huu : (u : 𝓞 (CyclotomicField 37 ℚ)) =
      ((ζU : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ^ m * (Ju : 𝓞 (CyclotomicField 37 ℚ)) := by
    have := congrArg (fun w : (𝓞 (CyclotomicField 37 ℚ))ˣ ↦ (w : 𝓞 (CyclotomicField 37 ℚ)))
      hu_eq
    push_cast at this
    rw [this]; ring
  have hζUval : (ζU : 𝓞 (CyclotomicField 37 ℚ)) =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger := IsUnit.unit_spec _
  rw [hζUval] at huu
  rw [hJA, hAB, huu]
  ring

private theorem zetaSubOne_prime :
    Prime ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) :=
  (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).zeta_sub_one_prime'

private theorem exists_zetaSubOne_pow_mul
    {x : 𝓞 (CyclotomicField 37 ℚ)} (hx : x ≠ 0) :
    ∃ (t : ℕ) (x' : 𝓞 (CyclotomicField 37 ℚ)),
      x = ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ t * x' ∧
      ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ x') := by
  have hfin : FiniteMultiplicity
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) x :=
    FiniteMultiplicity.of_prime_left zetaSubOne_prime hx
  obtain ⟨c, hc, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc, hndvd⟩

private theorem zetaSubOne_pow_mul_inj {a b : ℕ}
    {w w' : 𝓞 (CyclotomicField 37 ℚ)}
    (hw : ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ w))
    (hw' : ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ w'))
    (h : ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ a * w =
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ b * w') :
    a = b := by
  set π := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 with hπ
  have hπ0 : π ≠ 0 := zetaSubOne_prime.ne_zero
  rcases le_total a b with hab | hab
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rcases Nat.eq_zero_or_pos k with hk | hk
    · omega
    · exfalso
      apply hw
      have hcancel : w = π ^ k * w' := by
        have h' : π ^ a * w = π ^ a * (π ^ k * w') := by
          rw [h, pow_add]; ring
        exact mul_left_cancel₀ (pow_ne_zero a hπ0) h'
      rw [hcancel]
      exact dvd_mul_of_dvd_left (dvd_pow_self π hk.ne') w'
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rcases Nat.eq_zero_or_pos k with hk | hk
    · omega
    · exfalso
      apply hw'
      have hcancel : w' = π ^ k * w := by
        have h' : π ^ b * w' = π ^ b * (π ^ k * w) := by
          rw [← h, pow_add]; ring
        exact mul_left_cancel₀ (pow_ne_zero b hπ0) h'
      rw [hcancel]
      exact dvd_mul_of_dvd_left (dvd_pow_self π hk.ne') w

private theorem zetaSubOne_not_dvd_factorProd
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (n : Fin 5 → ℕ) :
    ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (n i)) := by
  rw [zetaSubOne_prime.dvd_finsetProd_iff]
  push Not
  intro i _
  rcases Nat.eq_zero_or_pos (n i) with hni | hni
  · rw [hni, pow_zero]
    exact zetaSubOne_prime.not_dvd_one
  · rw [zetaSubOne_prime.dvd_pow_iff_dvd hni.ne']
    exact zetaSubOne_not_dvd_factorElt heq hcaseI (i.1 + 1)

private theorem caseI_exists_coprime_element_relation
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (x y : 𝓞 (CyclotomicField 37 ℚ))
      (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      nPos ≠ nNeg ∧ (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ x) ∧
      ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ y) ∧
      x ^ 37 * ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nPos i) =
        (y ^ 37 * ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nNeg i)) *
          (u : 𝓞 (CyclotomicField 37 ℚ)) := by
  obtain ⟨nPos, nNeg, x, y, u, hne, hPosb, hNegb, hx0, hy0, hrel⟩ :=
    caseI_exists_element_relation heq hgcd hcaseI
  set π := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 with hπ
  obtain ⟨s, x', hx'eq, hx'⟩ := exists_zetaSubOne_pow_mul hx0
  obtain ⟨t, y', hy'eq, hy'⟩ := exists_zetaSubOne_pow_mul hy0
  set FP := ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nPos i) with hFP
  set FN := ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nNeg i) with hFN
  have hFP_ndvd : ¬ (π ∣ FP) := zetaSubOne_not_dvd_factorProd heq hcaseI nPos
  have hFN_ndvd : ¬ (π ∣ FN) := zetaSubOne_not_dvd_factorProd heq hcaseI nNeg
  have hx'37 : ¬ (π ∣ x' ^ 37) := fun h ↦ hx' (zetaSubOne_prime.dvd_of_dvd_pow h)
  have hy'37 : ¬ (π ∣ y' ^ 37) := fun h ↦ hy' (zetaSubOne_prime.dvd_of_dvd_pow h)
  have hw : ¬ (π ∣ x' ^ 37 * FP) :=
    fun h ↦ (zetaSubOne_prime.dvd_mul.mp h).elim hx'37 hFP_ndvd
  have hw' : ¬ (π ∣ y' ^ 37 * FN * (u : 𝓞 (CyclotomicField 37 ℚ))) := by
    intro h
    rcases zetaSubOne_prime.dvd_mul.mp h with h1 | h2
    · exact (zetaSubOne_prime.dvd_mul.mp h1).elim hy'37 hFN_ndvd
    · exact zetaSubOne_prime.not_dvd_one (isUnit_of_dvd_unit h2 u.isUnit).dvd
  have hrel' : π ^ (37 * s) * (x' ^ 37 * FP) =
      π ^ (37 * t) * (y' ^ 37 * FN * (u : 𝓞 (CyclotomicField 37 ℚ))) := by
    have hexp1 : (π ^ s) ^ 37 = π ^ (37 * s) := by rw [← pow_mul, mul_comm]
    have hexp2 : (π ^ t) ^ 37 = π ^ (37 * t) := by rw [← pow_mul, mul_comm]
    rw [hx'eq, hy'eq, mul_pow, mul_pow, hexp1, hexp2] at hrel
    linear_combination hrel
  have hst : 37 * s = 37 * t := zetaSubOne_pow_mul_inj hw hw' hrel'
  have hst' : s = t := by omega
  subst hst'
  have hcancel : x' ^ 37 * FP = y' ^ 37 * FN * (u : 𝓞 (CyclotomicField 37 ℚ)) :=
    mul_left_cancel₀ (pow_ne_zero _ zetaSubOne_prime.ne_zero) hrel'
  refine ⟨nPos, nNeg, x', y', u, hne, hPosb, hNegb, hx', hy', ?_⟩
  linear_combination hcancel

private theorem not_dvd_of_pow_sub_intCast
    {x' : 𝓞 (CyclotomicField 37 ℚ)} {X : ℤ}
    (hX : x' ^ 37 - (X : 𝓞 (CyclotomicField 37 ℚ)) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _))
    (hx' : ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ x')) :
    ¬ (37 : ℤ) ∣ X := by
  intro hXdvd
  apply hx'
  have h37dvd : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      (37 : 𝓞 (CyclotomicField 37 ℚ)) := by
    have hh : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
        ((37 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) :=
      (zetaSubOne_dvd_intCast_iff 37).mpr (dvd_refl 37)
    simpa using hh
  rw [Ideal.mem_span_singleton] at hX
  have hX' : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      (X : 𝓞 (CyclotomicField 37 ℚ)) := (zetaSubOne_dvd_intCast_iff X).mpr hXdvd
  have hpow : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ x' ^ 37 := by
    have : x' ^ 37 = (x' ^ 37 - (X : 𝓞 (CyclotomicField 37 ℚ))) +
        (X : 𝓞 (CyclotomicField 37 ℚ)) := by ring
    rw [this]
    exact dvd_add (h37dvd.trans hX) hX'
  exact zetaSubOne_prime.dvd_of_dvd_pow hpow

private theorem mem_span_of_intCast_mul_mem
    {m : ℤ} {z : 𝓞 (CyclotomicField 37 ℚ)} (hm : ¬ (37 : ℤ) ∣ m)
    (h : (m : 𝓞 (CyclotomicField 37 ℚ)) * z ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) :
    z ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  have hp37 : Prime (37 : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; norm_num
  have hcop : IsCoprime m (37 : ℤ) :=
    ((hp37.coprime_iff_not_dvd).mpr hm).symm
  obtain ⟨k, l, hkl⟩ := hcop
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨w, hw⟩ := h
  refine ⟨k * w + l * z, ?_⟩
  have hklcast : (k : 𝓞 (CyclotomicField 37 ℚ)) * (m : 𝓞 (CyclotomicField 37 ℚ)) +
      (l : 𝓞 (CyclotomicField 37 ℚ)) * (37 : 𝓞 (CyclotomicField 37 ℚ)) = 1 := by
    have := congrArg (fun n : ℤ ↦ (n : 𝓞 (CyclotomicField 37 ℚ))) hkl
    push_cast at this; linear_combination this
  linear_combination (k : 𝓞 (CyclotomicField 37 ℚ)) * hw - z * hklcast

private def factorEltConj (a b : ℤ) (k : ℕ) : 𝓞 (CyclotomicField 37 ℚ) :=
  (a : 𝓞 (CyclotomicField 37 ℚ)) +
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (36 * k) *
      (b : 𝓞 (CyclotomicField 37 ℚ))

private theorem conj_factorProd (a b : ℤ) (n : Fin 5 → ℕ) :
    haveI := eichlerCM
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
        (∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (n i)) =
      ∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (n i) := by
  haveI := eichlerCM
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [map_pow, conj_factorElt]
  rfl

private theorem sum_zeta_pow_eq_zero :
    ∑ k ∈ Finset.range 37, (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ k = 0 := by
  have hμ : IsPrimitiveRoot
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) 37 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
  exact hμ.geom_sum_eq_zero (by norm_num)

private theorem sum_zeta_pow_36_eq :
    ∑ j ∈ Finset.range 36, (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ j =
      -((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36) := by
  have h := sum_zeta_pow_eq_zero
  rw [Finset.sum_range_succ] at h
  linear_combination h

private theorem telescope_zeta :
    ∑ k ∈ Finset.range 37, (k : 𝓞 (CyclotomicField 37 ℚ)) *
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (k - 1) -
          (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ k) =
      -37 * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hA : ∑ k ∈ Finset.range 37, (k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k - 1) =
      ∑ j ∈ Finset.range 36, ((j : 𝓞 (CyclotomicField 37 ℚ)) + 1) * ζ ^ j := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul,
      add_zero]
  have hB : ∑ k ∈ Finset.range 37, (k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k =
      ∑ j ∈ Finset.range 36, ((j : 𝓞 (CyclotomicField 37 ℚ)) + 1) * ζ ^ (j + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
  have htel : (∑ j ∈ Finset.range 36, ((j : 𝓞 (CyclotomicField 37 ℚ)) + 1) * ζ ^ j) -
      (∑ j ∈ Finset.range 36, ((j : 𝓞 (CyclotomicField 37 ℚ)) + 1) * ζ ^ (j + 1)) =
      (∑ j ∈ Finset.range 36, ζ ^ j) - 36 * ζ ^ 36 := by
    have key : ∀ n : ℕ,
        (∑ j ∈ Finset.range n, ((j : 𝓞 (CyclotomicField 37 ℚ)) + 1) * ζ ^ j) -
          (∑ j ∈ Finset.range n, ((j : 𝓞 (CyclotomicField 37 ℚ)) + 1) * ζ ^ (j + 1)) =
        (∑ j ∈ Finset.range n, ζ ^ j) - (n : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        linear_combination ih
    simpa using key 36
  have hcomb : ∑ k ∈ Finset.range 37, (k : 𝓞 (CyclotomicField 37 ℚ)) *
      (ζ ^ (k - 1) - ζ ^ k) =
      (∑ j ∈ Finset.range 36, ζ ^ j) - 36 * ζ ^ 36 := by
    rw [Finset.sum_congr rfl (fun k _ ↦ mul_sub _ _ _), Finset.sum_sub_distrib, hA, hB, htel]
  rw [hcomb, sum_zeta_pow_36_eq]
  ring

private theorem caseI_bounded_deriv (c : ℕ → ℤ)
    (hmem : (∑ k ∈ Finset.range 37, (c k : 𝓞 (CyclotomicField 37 ℚ)) *
        (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ k) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) :
    (∑ k ∈ Finset.range 37, ((k : ℤ) * c k : 𝓞 (CyclotomicField 37 ℚ)) *
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (k - 1) -
          (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ k)) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hsum37 : ∑ k ∈ Finset.range 37, (c k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k =
      ∑ k ∈ Finset.range 36, ((c k - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k := by
    rw [Finset.sum_range_succ]
    have hsplit : ∑ k ∈ Finset.range 36, ((c k - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k =
        (∑ k ∈ Finset.range 36, (c k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k) -
          (c 36 : 𝓞 (CyclotomicField 37 ℚ)) * ∑ k ∈ Finset.range 36, ζ ^ k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ ↦ ?_)
      push_cast; ring
    rw [hsplit, sum_zeta_pow_36_eq]
    ring
  have hmem' : (∑ k : Fin 36, ((c k.1 - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) *
      ζ ^ (k : ℕ)) ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    have heq : (∑ k : Fin 36, ((c k.1 - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) *
        ζ ^ (k : ℕ)) =
        ∑ k ∈ Finset.range 36, ((c k - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k :=
      Fin.sum_univ_eq_sum_range
        (fun k ↦ ((c k - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k) 36
    rw [heq, ← hsum37]
    exact hmem
  have hdvd : ∀ k : Fin 36, (37 : ℤ) ∣ (c k.1 - c 36) :=
    caseI_dvd_of_sum_zeta_pow_mem (fun k ↦ c k.1 - c 36) hmem'
  have hsplit2 : ∑ k ∈ Finset.range 37, ((k : ℤ) * c k : 𝓞 (CyclotomicField 37 ℚ)) *
      (ζ ^ (k - 1) - ζ ^ k) =
      (∑ k ∈ Finset.range 37, ((k : ℤ) * (c k - c 36) : 𝓞 (CyclotomicField 37 ℚ)) *
        (ζ ^ (k - 1) - ζ ^ k)) +
      (c 36 : 𝓞 (CyclotomicField 37 ℚ)) * ∑ k ∈ Finset.range 37,
        (k : 𝓞 (CyclotomicField 37 ℚ)) * (ζ ^ (k - 1) - ζ ^ k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    push_cast; ring
  rw [hsplit2]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.sum_mem _ (fun k hk ↦ ?_)
    rw [Ideal.mem_span_singleton]
    rcases lt_or_ge k 36 with hk36 | hk36
    · obtain ⟨q, hq⟩ := hdvd ⟨k, hk36⟩
      refine ⟨(↑((k : ℤ) * q) : 𝓞 (CyclotomicField 37 ℚ)) * (ζ ^ (k - 1) - ζ ^ k), ?_⟩
      have hqcast : ((c k - c 36 : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) =
          (37 : 𝓞 (CyclotomicField 37 ℚ)) * (q : 𝓞 (CyclotomicField 37 ℚ)) := by
        have := congrArg (fun n : ℤ ↦ (n : 𝓞 (CyclotomicField 37 ℚ))) hq
        push_cast at this ⊢; linear_combination this
      push_cast
      push_cast at hqcast
      linear_combination (↑k * (ζ ^ (k - 1) - ζ ^ k) : 𝓞 (CyclotomicField 37 ℚ)) * hqcast
    · have hk37 : k = 36 := by
        have := Finset.mem_range.mp hk; omega
      subst hk37
      refine ⟨0, ?_⟩
      push_cast; ring
  · rw [telescope_zeta, Ideal.mem_span_singleton]
    exact ⟨-(c 36 : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ 36, by ring⟩

private noncomputable abbrev evZ : ℤ[X] →+* 𝓞 (CyclotomicField 37 ℚ) :=
  (Polynomial.aeval (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger).toRingHom

@[simp] private theorem evZ_X : evZ X = (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger :=
  Polynomial.aeval_X _

@[simp] private theorem evZ_C (n : ℤ) :
    evZ (Polynomial.C n) = (n : 𝓞 (CyclotomicField 37 ℚ)) := Polynomial.aeval_C _ _

private theorem one_sub_zeta_mul_evZ_derivative
    (S : ℤ[X]) (hS : S.natDegree < 37) :
    (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) * evZ (derivative S) =
      ∑ k ∈ Finset.range 37, ((k : ℤ) * S.coeff k : 𝓞 (CyclotomicField 37 ℚ)) *
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (k - 1) -
          (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ k) := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hdeg' : (derivative S).natDegree < 36 := by
    have := Polynomial.natDegree_derivative_le S
    omega
  have hev : evZ (derivative S) = ∑ j ∈ Finset.range 36,
      ((derivative S).coeff j : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ j := by
    rw [show evZ (derivative S) = Polynomial.aeval ζ (derivative S) from rfl,
      Polynomial.aeval_eq_sum_range' (by omega : (derivative S).natDegree < 36)]
    refine Finset.sum_congr rfl (fun j _ ↦ by rw [Algebra.smul_def]; rfl)
  rw [hev, Finset.mul_sum]
  have hcoeff : ∀ j, ((derivative S).coeff j : 𝓞 (CyclotomicField 37 ℚ)) =
      ((j + 1 : ℤ) * S.coeff (j + 1) : 𝓞 (CyclotomicField 37 ℚ)) := by
    intro j; rw [Polynomial.coeff_derivative]; push_cast; ring
  rw [Finset.sum_range_succ' (fun k ↦ ((k : ℤ) * S.coeff k : 𝓞 (CyclotomicField 37 ℚ)) *
      (ζ ^ (k - 1) - ζ ^ k)) 36]
  simp only [Nat.cast_zero, zero_mul, Int.cast_zero, add_zero]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [hcoeff]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

private theorem caseI_deriv_step (P : ℤ[X])
    (hP : evZ P ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) :
    (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) * evZ (derivative P) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hevX : evZ X = ζ := by rw [hζ]; exact Polynomial.aeval_X _
  set g : ℤ[X] := X ^ 37 - 1 with hg
  have hgmonic : g.Monic := by
    rw [hg]
    exact Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_one]; exact_mod_cast (by norm_num : (0 : ℕ∞) < 37))
  set S : ℤ[X] := P %ₘ g with hS
  set Q : ℤ[X] := P /ₘ g with hQ
  have hdecomp : P = S + g * Q := by rw [hS, hQ]; exact (Polynomial.modByMonic_add_div P g).symm
  have hgdeg : g.natDegree = 37 := by
    rw [hg, show (1 : ℤ[X]) = Polynomial.C 1 from (Polynomial.C_1).symm,
      Polynomial.natDegree_X_pow_sub_C]
  have hglt : g ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hgdeg; omega
  have hSdeg : S.natDegree < 37 := by
    rw [hS, ← hgdeg]
    exact Polynomial.natDegree_modByMonic_lt P hgmonic hglt
  have hevg : evZ g = 0 := by
    rw [hg, map_sub, map_pow, map_one, hevX]
    have : ζ ^ 37 = 1 := zeta_toInteger_pow_eq_one 37 (CyclotomicField 37 ℚ)
    rw [this, sub_self]
  have hevS : evZ S = evZ P := by
    rw [hdecomp, map_add, map_mul, hevg, zero_mul, add_zero]
  have hdg : derivative g = (37 : ℤ[X]) * X ^ 36 := by
    rw [hg, derivative_sub, derivative_one, sub_zero, derivative_X_pow]
    norm_num
  have hderiv : evZ (derivative P) =
      evZ (derivative S) + (37 : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ 36 * evZ Q := by
    have hdP : derivative P = derivative S + (derivative g * Q + g * derivative Q) := by
      rw [hdecomp, derivative_add, derivative_mul]
    rw [hdP, map_add, map_add, map_mul, map_mul, hevg, zero_mul, add_zero, hdg]
    rw [map_mul, map_pow, hevX, map_ofNat]
  rw [hderiv, mul_add]
  refine Ideal.add_mem _ ?_ ?_
  · rw [one_sub_zeta_mul_evZ_derivative S hSdeg]
    apply caseI_bounded_deriv (fun k ↦ S.coeff k)
    rw [← hevS] at hP
    have hevSsum : evZ S = ∑ k ∈ Finset.range 37,
        ((S.coeff k : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k := by
      rw [show evZ S = Polynomial.aeval ζ S from rfl,
        Polynomial.aeval_eq_sum_range' (by omega : S.natDegree < 37)]
      refine Finset.sum_congr rfl (fun k _ ↦ by rw [Algebra.smul_def]; rfl)
    rw [← hevSsum]; exact hP
  · rw [Ideal.mem_span_singleton]
    exact ⟨(1 - ζ) * ζ ^ 36 * evZ Q, by ring⟩

private theorem prod_mul_derivative_prod_pow {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℤ[X]) (e : ι → ℕ) :
    (∏ j ∈ s, f j) * derivative (∏ j ∈ s, f j ^ e j) =
      (∏ j ∈ s, f j ^ e j) *
        ∑ k ∈ s, (Polynomial.C (e k : ℤ)) * derivative (f k) * ∏ j ∈ s.erase k, f j := by
  classical
  rw [Polynomial.derivative_prod_finset, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk ↦ ?_)
  rw [Polynomial.derivative_pow]
  have hDl : (∏ j ∈ s, f j) = f k * ∏ j ∈ s.erase k, f j :=
    (Finset.mul_prod_erase s f hk).symm
  have hFl : (∏ j ∈ s, f j ^ e j) = f k ^ e k * ∏ j ∈ s.erase k, f j ^ e j :=
    (Finset.mul_prod_erase s (fun j ↦ f j ^ e j) hk).symm
  rw [hDl, hFl]
  rcases Nat.eq_zero_or_pos (e k) with he | he
  · simp [he]
  · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    rw [ht, Nat.succ_sub_one, pow_succ]
    ring

private theorem caseI_key_congruence
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (m : ℕ), nPos ≠ nNeg ∧
      (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      ((∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nPos i)) *
          (∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (nNeg i)) -
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m *
          (∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nNeg i)) *
          (∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (nPos i))) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  haveI := eichlerCM
  obtain ⟨nPos, nNeg, x', y', u, hne, hPosb, hNegb, hx', hy', hrel⟩ :=
    caseI_exists_coprime_element_relation heq hgcd hcaseI
  set J := ringOfIntegersComplexConj (CyclotomicField 37 ℚ) with hJ
  set FP := ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nPos i) with hFP
  set FN := ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (nNeg i) with hFN
  set A := x' ^ 37 * FP with hA
  set B := y' ^ 37 * FN with hB
  obtain ⟨m, hE2⟩ := caseI_conj_pair_eq A B u hrel
  refine ⟨nPos, nNeg, m, hne, hPosb, hNegb, ?_⟩
  obtain ⟨X, hX, hXc⟩ := caseI_conj_pow_sub_intCast x'
  obtain ⟨Y, hY, hYc⟩ := caseI_conj_pow_sub_intCast y'
  have hX37 : ¬ (37 : ℤ) ∣ X := not_dvd_of_pow_sub_intCast hX hx'
  have hY37 : ¬ (37 : ℤ) ∣ Y := not_dvd_of_pow_sub_intCast hY hy'
  have hJA : J A = (J x') ^ 37 * ∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (nPos i) := by
    rw [hA, hJ, map_mul, map_pow, ← hJ, hFP, conj_factorProd]
  have hJB : J B = (J y') ^ 37 * ∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (nNeg i) := by
    rw [hB, hJ, map_mul, map_pow, ← hJ, hFN, conj_factorProd]
  set GP := ∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (nPos i) with hGP
  set GN := ∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (nNeg i) with hGN
  have hgoal_mul : (X * Y : 𝓞 (CyclotomicField 37 ℚ)) *
      (FP * GN - ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * FN * GP) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    have e1 : A * J B - (X : 𝓞 (CyclotomicField 37 ℚ)) * (Y : 𝓞 (CyclotomicField 37 ℚ)) *
        (FP * GN) ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
      rw [hA, hJB]
      have hfac : (x' ^ 37 * FP) * ((J y') ^ 37 * GN) -
          (X : 𝓞 (CyclotomicField 37 ℚ)) * (Y : 𝓞 (CyclotomicField 37 ℚ)) * (FP * GN) =
          (x' ^ 37 - (X : 𝓞 (CyclotomicField 37 ℚ))) * ((J y') ^ 37 * (FP * GN)) +
          (X : 𝓞 (CyclotomicField 37 ℚ)) *
            (((J y') ^ 37 - (Y : 𝓞 (CyclotomicField 37 ℚ))) * (FP * GN)) := by ring
      rw [hfac]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hX) (Ideal.mul_mem_left _ _
        (Ideal.mul_mem_right _ _ hYc))
    have e2 : ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * B * J A -
        (X : 𝓞 (CyclotomicField 37 ℚ)) * (Y : 𝓞 (CyclotomicField 37 ℚ)) *
          (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * FN * GP) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
      rw [hB, hJA]
      have hfac : ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m *
            (y' ^ 37 * FN) * ((J x') ^ 37 * GP) -
          (X : 𝓞 (CyclotomicField 37 ℚ)) * (Y : 𝓞 (CyclotomicField 37 ℚ)) *
            (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * FN * GP) =
          ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m *
            ((y' ^ 37 - (Y : 𝓞 (CyclotomicField 37 ℚ))) * ((J x') ^ 37 * (FN * GP))) +
          ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m *
            ((Y : 𝓞 (CyclotomicField 37 ℚ)) *
              (((J x') ^ 37 - (X : 𝓞 (CyclotomicField 37 ℚ))) * (FN * GP))) := by ring
      rw [hfac]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
      · exact Ideal.mul_mem_right _ _ hY
      · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hXc)
    have hzero : A * J B - ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * B * J A
        = 0 := by rw [hE2]; ring
    have hcombine : (X * Y : 𝓞 (CyclotomicField 37 ℚ)) *
        (FP * GN - ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * FN * GP) =
        - (A * J B - (X : 𝓞 (CyclotomicField 37 ℚ)) * (Y : 𝓞 (CyclotomicField 37 ℚ)) *
            (FP * GN))
        + (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * B * J A -
            (X : 𝓞 (CyclotomicField 37 ℚ)) * (Y : 𝓞 (CyclotomicField 37 ℚ)) *
              (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * FN * GP))
        + (A * J B -
            ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * B * J A) := by ring
    rw [hcombine, hzero, add_zero]
    exact Ideal.add_mem _ (neg_mem e1) e2
  have hXYcop : ¬ (37 : ℤ) ∣ X * Y := by
    have hp37 : Prime (37 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; norm_num
    exact fun h ↦ (hp37.dvd_mul.mp h).elim hX37 hY37
  have : ((X * Y : ℤ) : 𝓞 (CyclotomicField 37 ℚ)) *
      (FP * GN - ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 2) ^ m * FN * GP) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    push_cast; exact hgoal_mul
  exact mem_span_of_intCast_mul_mem hXYcop this

private def Ppoly (a b : ℤ) (i : Fin 5) : ℤ[X] :=
  Polynomial.C a + Polynomial.C b * X ^ (i.1 + 1)

private def Gpoly (a b : ℤ) (i : Fin 5) : ℤ[X] :=
  Polynomial.C b + Polynomial.C a * X ^ (i.1 + 1)

private theorem evZ_Ppoly (a b : ℤ) (i : Fin 5) :
    evZ (Ppoly a b i) = factorElt a b (i.1 + 1) := by
  rw [Ppoly, map_add, map_mul, map_pow]
  have hevX : evZ X = (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger :=
    Polynomial.aeval_X _
  rw [hevX, show evZ (Polynomial.C a) = (a : 𝓞 (CyclotomicField 37 ℚ)) from
    Polynomial.aeval_C _ _, show evZ (Polynomial.C b) = (b : 𝓞 (CyclotomicField 37 ℚ)) from
    Polynomial.aeval_C _ _]
  rw [factorElt, factorRoot]
  ring

private theorem factorEltConj_eq_zeta_pow_mul (a b : ℤ) (i : Fin 5) :
    factorEltConj a b (i.1 + 1) =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ (36 * (i.1 + 1)) *
        evZ (Gpoly a b i) := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hevX : evZ X = ζ := Polynomial.aeval_X _
  rw [Gpoly, map_add, map_mul, map_pow, hevX,
    show evZ (Polynomial.C a) = (a : 𝓞 (CyclotomicField 37 ℚ)) from Polynomial.aeval_C _ _,
    show evZ (Polynomial.C b) = (b : 𝓞 (CyclotomicField 37 ℚ)) from Polynomial.aeval_C _ _]
  rw [factorEltConj]
  have hζ37 : ζ ^ 37 = 1 := zeta_toInteger_pow_eq_one 37 (CyclotomicField 37 ℚ)
  have hexp : ζ ^ (36 * (i.1 + 1)) * ζ ^ (i.1 + 1) = 1 := by
    rw [← pow_add, show 36 * (i.1 + 1) + (i.1 + 1) = 37 * (i.1 + 1) by ring, pow_mul, hζ37,
      one_pow]
  have hkey : ζ ^ (36 * (i.1 + 1)) * ((b : 𝓞 (CyclotomicField 37 ℚ)) +
      (a : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (i.1 + 1)) =
      (a : 𝓞 (CyclotomicField 37 ℚ)) + ζ ^ (36 * (i.1 + 1)) * (b : 𝓞 (CyclotomicField 37 ℚ)) := by
    linear_combination (a : 𝓞 (CyclotomicField 37 ℚ)) * hexp
  rw [hkey]

private theorem evZ_prod_Ppoly (a b : ℤ) (n : Fin 5 → ℕ) :
    evZ (∏ i : Fin 5, Ppoly a b i ^ (n i)) =
      ∏ i : Fin 5, factorElt a b (i.1 + 1) ^ (n i) := by
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ ↦ by rw [map_pow, evZ_Ppoly])

private theorem prod_factorEltConj_eq (a b : ℤ) (n : Fin 5 → ℕ) :
    (∏ i : Fin 5, factorEltConj a b (i.1 + 1) ^ (n i)) =
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^
          (∑ i : Fin 5, 36 * (i.1 + 1) * n i) *
        evZ (∏ i : Fin 5, Gpoly a b i ^ (n i)) := by
  rw [map_prod,
    ← Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ 36 * (i.1 + 1) * n i)
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [factorEltConj_eq_zeta_pow_mul, map_pow, mul_pow, ← pow_mul]

private def FpolyTot (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) : ℤ[X] :=
  (∏ i : Fin 5, Ppoly a b i ^ (nPos i)) * (∏ i : Fin 5, Gpoly a b i ^ (nNeg i))

private def GpolyTot (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) : ℤ[X] :=
  (∏ i : Fin 5, Ppoly a b i ^ (nNeg i)) * (∏ i : Fin 5, Gpoly a b i ^ (nPos i))

private theorem caseI_poly_congruence
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (v : ℕ), nPos ≠ nNeg ∧
      (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      (evZ (FpolyTot a b nPos nNeg) -
        (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ v *
          evZ (GpolyTot a b nPos nNeg)) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  obtain ⟨nPos, nNeg, m, hne, hPosb, hNegb, hKEY⟩ := caseI_key_congruence heq hgcd hcaseI
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  set Sneg := ∑ i : Fin 5, 36 * (i.1 + 1) * nNeg i with hSneg
  set Spos := ∑ i : Fin 5, 36 * (i.1 + 1) * nPos i with hSpos
  refine ⟨nPos, nNeg, 36 * Sneg + 2 * m + Spos, hne, hPosb, hNegb, ?_⟩
  rw [prod_factorEltConj_eq, prod_factorEltConj_eq] at hKEY
  rw [← evZ_prod_Ppoly a b nPos, ← evZ_prod_Ppoly a b nNeg] at hKEY
  rw [← hSneg, ← hSpos] at hKEY
  have hmul := Ideal.mul_mem_left
    (Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) (ζ ^ (36 * Sneg)) hKEY
  have hζ37 : ζ ^ 37 = 1 := zeta_toInteger_pow_eq_one 37 (CyclotomicField 37 ℚ)
  have hclear : ζ ^ (36 * Sneg) * ζ ^ Sneg = 1 := by
    rw [← pow_add, show 36 * Sneg + Sneg = 37 * Sneg by ring, pow_mul, hζ37, one_pow]
  have hexp_eq : ζ ^ (36 * Sneg + 2 * m + Spos) =
      ζ ^ (36 * Sneg) * ((ζ ^ 2) ^ m * ζ ^ Spos) := by
    rw [show (ζ ^ 2) ^ m = ζ ^ (2 * m) by rw [← pow_mul], ← pow_add, ← pow_add]
    congr 1; ring
  have hgoal_eq : ζ ^ (36 * Sneg) *
      (evZ (∏ i : Fin 5, Ppoly a b i ^ (nPos i)) * (ζ ^ Sneg *
          evZ (∏ i : Fin 5, Gpoly a b i ^ (nNeg i))) -
        (ζ ^ 2) ^ m * evZ (∏ i : Fin 5, Ppoly a b i ^ (nNeg i)) *
          (ζ ^ Spos * evZ (∏ i : Fin 5, Gpoly a b i ^ (nPos i)))) =
      evZ (FpolyTot a b nPos nNeg) -
        ζ ^ (36 * Sneg + 2 * m + Spos) * evZ (GpolyTot a b nPos nNeg) := by
    rw [FpolyTot, GpolyTot, map_mul, map_mul, hexp_eq]
    linear_combination (evZ (∏ i : Fin 5, Ppoly a b i ^ (nPos i)) *
        evZ (∏ i : Fin 5, Gpoly a b i ^ (nNeg i))) * hclear
  rwa [hgoal_eq] at hmul

private def Dpoly (a b : ℤ) : ℤ[X] :=
  (∏ i : Fin 5, Ppoly a b i) * (∏ i : Fin 5, Gpoly a b i)

private def NPoly (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) : ℤ[X] :=
  (∏ i : Fin 5, Gpoly a b i) *
      ∑ k : Fin 5, Polynomial.C (nPos k : ℤ) * derivative (Ppoly a b k) *
        ∏ j ∈ Finset.univ.erase k, Ppoly a b j +
  (∏ i : Fin 5, Ppoly a b i) *
      ∑ k : Fin 5, Polynomial.C (nNeg k : ℤ) * derivative (Gpoly a b k) *
        ∏ j ∈ Finset.univ.erase k, Gpoly a b j

private theorem Dpoly_mul_derivative_FpolyTot (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) :
    Dpoly a b * derivative (FpolyTot a b nPos nNeg) =
      FpolyTot a b nPos nNeg * NPoly a b nPos nNeg := by
  rw [FpolyTot, Dpoly, NPoly, derivative_mul]
  have hA := prod_mul_derivative_prod_pow (Finset.univ : Finset (Fin 5))
    (Ppoly a b) nPos
  have hB := prod_mul_derivative_prod_pow (Finset.univ : Finset (Fin 5))
    (Gpoly a b) nNeg
  linear_combination
    ((∏ i : Fin 5, Gpoly a b i) * (∏ i : Fin 5, Gpoly a b i ^ nNeg i)) * hA +
    ((∏ i : Fin 5, Ppoly a b i) * (∏ i : Fin 5, Ppoly a b i ^ nPos i)) * hB

private theorem associated_zetaSubOne_pow_thirtyseven :
    Associated (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 36)
      (37 : 𝓞 (CyclotomicField 37 ℚ)) := by
  have hμ : IsPrimitiveRoot
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) 37 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
  have h := associated_zeta_sub_one_pow_prime (p := 37)
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ))
  rw [show (37 : ℕ) - 1 = 36 from rfl, Nat.cast_ofNat] at h
  exact h

private theorem mem_span_of_coprime_mul_mem
    {w z : 𝓞 (CyclotomicField 37 ℚ)}
    (hw : ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ w))
    (h : w * z ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _)) :
    z ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  set π := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 with hπ
  obtain ⟨u, hu⟩ := associated_zetaSubOne_pow_thirtyseven
  rw [Ideal.mem_span_singleton] at h
  have h36 : π ^ 36 ∣ w * z := by
    rw [← hu] at h; exact (dvd_mul_right _ _).trans h
  have hz36 : π ^ 36 ∣ z := zetaSubOne_prime.pow_dvd_of_dvd_mul_left 36 hw h36
  rw [Ideal.mem_span_singleton, ← hu]
  obtain ⟨t, ht⟩ := hz36
  refine ⟨(↑u⁻¹ : 𝓞 (CyclotomicField 37 ℚ)) * t, ?_⟩
  rw [ht]
  have : (↑u : 𝓞 (CyclotomicField 37 ℚ)) * (↑u⁻¹ * t) = t := by
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [mul_assoc, this]

private theorem zetaSubOne_not_dvd_factorEltConj
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (i : Fin 5)
    (h : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      factorEltConj a b (i.1 + 1)) : False := by
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hdiff : factorEltConj a b (i.1 + 1) - factorElt a b (i.1 + 1) =
      (ζ ^ (36 * (i.1 + 1)) - ζ ^ (i.1 + 1)) * (b : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [factorEltConj, factorElt, factorRoot]; ring
  have hdvddiff : (ζ - 1) ∣ (factorEltConj a b (i.1 + 1) - factorElt a b (i.1 + 1)) := by
    rw [hdiff]
    refine Dvd.dvd.mul_right ?_ _
    have h1 : (ζ - 1) ∣ ζ ^ (36 * (i.1 + 1)) - 1 := by
      have := sub_dvd_pow_sub_pow ζ 1 (36 * (i.1 + 1)); simpa using this
    have h2 : (ζ - 1) ∣ ζ ^ (i.1 + 1) - 1 := by
      have := sub_dvd_pow_sub_pow ζ 1 (i.1 + 1); simpa using this
    have : ζ ^ (36 * (i.1 + 1)) - ζ ^ (i.1 + 1) =
        (ζ ^ (36 * (i.1 + 1)) - 1) - (ζ ^ (i.1 + 1) - 1) := by ring
    rw [this]; exact dvd_sub h1 h2
  exact zetaSubOne_not_dvd_factorElt heq hcaseI (i.1 + 1) (by
    have := dvd_sub h hdvddiff
    simpa using this)

private def Sigmapoly (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) : ℤ[X] :=
  NPoly a b nPos nNeg - NPoly a b nNeg nPos

private def Mtilpoly (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) (v : ℕ) : ℤ[X] :=
  X * Sigmapoly a b nPos nNeg - Polynomial.C (v : ℤ) * Dpoly a b

private def Ltilpoly (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) (v : ℕ) : ℤ[X] :=
  (1 - X) * Mtilpoly a b nPos nNeg v

private theorem zetaSubOne_not_dvd_evZ_FpolyTot
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) (nPos nNeg : Fin 5 → ℕ) :
    ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
      evZ (FpolyTot a b nPos nNeg)) := by
  haveI := eichlerCM
  rw [FpolyTot, map_mul, evZ_prod_Ppoly]
  intro hdvd
  rcases zetaSubOne_prime.dvd_mul.mp hdvd with h1 | h2
  · exact zetaSubOne_not_dvd_factorProd heq hcaseI nPos h1
  · rw [map_prod] at h2
    rw [zetaSubOne_prime.dvd_finsetProd_iff] at h2
    obtain ⟨i, _, hi⟩ := h2
    rcases Nat.eq_zero_or_pos (nNeg i) with hn | hn
    · rw [hn, pow_zero, map_one] at hi
      exact zetaSubOne_prime.not_dvd_one hi
    · rw [map_pow, zetaSubOne_prime.dvd_pow_iff_dvd hn.ne'] at hi
      have hconv := factorEltConj_eq_zeta_pow_mul a b i
      have hdvd_conj : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣
          factorEltConj a b (i.1 + 1) := by rw [hconv]; exact hi.mul_left _
      exact zetaSubOne_not_dvd_factorEltConj heq hcaseI i hdvd_conj

private theorem caseI_evZ_Ltil_mem
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (v : ℕ), nPos ≠ nNeg ∧
      (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      evZ (Ltilpoly a b nPos nNeg v) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
  obtain ⟨nPos, nNeg, v, hne, hPosb, hNegb, hKEY⟩ := caseI_poly_congruence heq hgcd hcaseI
  refine ⟨nPos, nNeg, v, hne, hPosb, hNegb, ?_⟩
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  set FT := evZ (FpolyTot a b nPos nNeg) with hFT
  set GT := evZ (GpolyTot a b nPos nNeg) with hGT
  set DT := evZ (Dpoly a b) with hDT
  set NF := evZ (NPoly a b nPos nNeg) with hNF
  set NG := evZ (NPoly a b nNeg nPos) with hNG
  set P : ℤ[X] := FpolyTot a b nPos nNeg - X ^ v * GpolyTot a b nPos nNeg with hP
  have hevP : evZ P = FT - ζ ^ v * GT := by
    rw [hP, map_sub, map_mul, map_pow, evZ_X]
  have hPmem : evZ P ∈ Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    rw [hevP]; exact hKEY
  have hDERIV := caseI_deriv_step P hPmem
  have hclF : DT * evZ (derivative (FpolyTot a b nPos nNeg)) = FT * NF := by
    rw [hDT, hFT, hNF, ← map_mul, ← map_mul, Dpoly_mul_derivative_FpolyTot]
  have hclG : DT * evZ (derivative (GpolyTot a b nPos nNeg)) = GT * NG := by
    rw [hDT, hGT, hNG, ← map_mul, ← map_mul]
    congr 1
    rw [show GpolyTot a b nPos nNeg = FpolyTot a b nNeg nPos from rfl,
      Dpoly_mul_derivative_FpolyTot]
  have hderivP : evZ (derivative P) =
      evZ (derivative (FpolyTot a b nPos nNeg)) -
        (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * GT -
        ζ ^ v * evZ (derivative (GpolyTot a b nPos nNeg)) := by
    rw [hP, derivative_sub, derivative_mul, derivative_X_pow]
    simp only [map_sub, map_add, map_mul, map_pow, map_natCast, evZ_X, ← hGT]
    ring
  have hevLtil : evZ (Ltilpoly a b nPos nNeg v) =
      (1 - ζ) * (ζ * (NF - NG) - (v : 𝓞 (CyclotomicField 37 ℚ)) * DT) := by
    rw [Ltilpoly, Mtilpoly, Sigmapoly]
    simp only [map_mul, map_sub, map_one, evZ_X, evZ_C, ← hNF, ← hNG, ← hDT]
    push_cast
    ring
  have hvζ : (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * ζ =
      (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ v := by
    rcases Nat.eq_zero_or_pos v with hv | hv
    · simp [hv]
    · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hv.ne'
      rw [ht, Nat.succ_sub_one, pow_succ]
      ring
  have hexact : FT * evZ (Ltilpoly a b nPos nNeg v) -
      ζ * (1 - ζ) * (DT * evZ (derivative P)) =
      (1 - ζ) * (FT - ζ ^ v * GT) * (-ζ * NG - (v : 𝓞 (CyclotomicField 37 ℚ)) * DT) := by
    rw [hevLtil, hderivP, mul_sub, mul_sub]
    rw [show DT * (evZ (derivative (FpolyTot a b nPos nNeg)) -
        (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * GT -
        ζ ^ v * evZ (derivative (GpolyTot a b nPos nNeg))) =
      DT * evZ (derivative (FpolyTot a b nPos nNeg)) -
        (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * (GT * DT) -
        ζ ^ v * (DT * evZ (derivative (GpolyTot a b nPos nNeg))) by ring]
    rw [hclF, hclG]
    have hvζ' : (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * (GT * DT) * (ζ * (1 - ζ)) =
        (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ v * (GT * DT) * (1 - ζ) := by
      rw [show (v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * (GT * DT) * (ζ * (1 - ζ)) =
        ((v : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (v - 1) * ζ) * (GT * DT) * (1 - ζ) by ring,
        hvζ]
    linear_combination hvζ'
  have hLHS : FT * evZ (Ltilpoly a b nPos nNeg v) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    have hterm1 : ζ * (1 - ζ) * (DT * evZ (derivative P)) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
      have : ζ * (1 - ζ) * (DT * evZ (derivative P)) =
          (ζ * DT) * ((1 - ζ) * evZ (derivative P)) := by ring
      rw [this]; exact Ideal.mul_mem_left _ _ hDERIV
    have hterm2 : (1 - ζ) * (FT - ζ ^ v * GT) *
        (-ζ * NG - (v : 𝓞 (CyclotomicField 37 ℚ)) * DT) ∈
        Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
      have hfac : (1 - ζ) * (FT - ζ ^ v * GT) *
          (-ζ * NG - (v : 𝓞 (CyclotomicField 37 ℚ)) * DT) =
          ((1 - ζ) * (-ζ * NG - (v : 𝓞 (CyclotomicField 37 ℚ)) * DT)) * (FT - ζ ^ v * GT) := by
        ring
      rw [hfac]
      exact Ideal.mul_mem_left _ _ (by rw [hFT, hGT]; exact hKEY)
    have : FT * evZ (Ltilpoly a b nPos nNeg v) =
        ζ * (1 - ζ) * (DT * evZ (derivative P)) +
        (1 - ζ) * (FT - ζ ^ v * GT) * (-ζ * NG - (v : 𝓞 (CyclotomicField 37 ℚ)) * DT) := by
      linear_combination hexact
    rw [this]
    exact Ideal.add_mem _ hterm1 hterm2
  exact mem_span_of_coprime_mul_mem
    (zetaSubOne_not_dvd_evZ_FpolyTot heq hcaseI nPos nNeg) hLHS

private theorem natDegree_Ppoly_le (a b : ℤ) (i : Fin 5) :
    (Ppoly a b i).natDegree ≤ i.1 + 1 := by
  rw [Ppoly]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [Polynomial.natDegree_C]
  refine max_le (by omega) ?_
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) (Polynomial.natDegree_X_pow_le _)

private theorem natDegree_Gpoly_le (a b : ℤ) (i : Fin 5) :
    (Gpoly a b i).natDegree ≤ i.1 + 1 := by
  rw [Gpoly]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [Polynomial.natDegree_C]
  refine max_le (by omega) ?_
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) (Polynomial.natDegree_X_pow_le _)

private theorem natDegree_prod_Ppoly_le (a b : ℤ) :
    (∏ i : Fin 5, Ppoly a b i).natDegree ≤ 15 := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ ↦ natDegree_Ppoly_le a b i)) ?_
  decide

private theorem natDegree_prod_Gpoly_le (a b : ℤ) :
    (∏ i : Fin 5, Gpoly a b i).natDegree ≤ 15 := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ ↦ natDegree_Gpoly_le a b i)) ?_
  decide

private theorem natDegree_Dpoly_le (a b : ℤ) : (Dpoly a b).natDegree ≤ 30 := by
  rw [Dpoly]
  exact Polynomial.natDegree_mul_le_of_le (natDegree_prod_Ppoly_le a b)
    (natDegree_prod_Gpoly_le a b)

private theorem sum_erase_succ_le (k : Fin 5) :
    ∑ j ∈ Finset.univ.erase k, (j.1 + 1) ≤ 14 - k.1 := by
  have h : (k.1 + 1) + ∑ j ∈ Finset.univ.erase k, (j.1 + 1) =
      ∑ j : Fin 5, (j.1 + 1) :=
    Finset.add_sum_erase (Finset.univ : Finset (Fin 5)) (fun j : Fin 5 ↦ j.1 + 1)
      (Finset.mem_univ k)
  have htot : ∑ j : Fin 5, (j.1 + 1) = 15 := by decide
  rw [htot] at h
  have hk : k.1 < 5 := k.2
  omega

private theorem natDegree_prod_erase_Ppoly_le (a b : ℤ) (k : Fin 5) :
    (∏ j ∈ Finset.univ.erase k, Ppoly a b j).natDegree ≤ 14 - k.1 :=
  le_trans (Polynomial.natDegree_prod_le _ _)
    (le_trans (Finset.sum_le_sum (fun j _ ↦ natDegree_Ppoly_le a b j)) (sum_erase_succ_le k))

private theorem natDegree_prod_erase_Gpoly_le (a b : ℤ) (k : Fin 5) :
    (∏ j ∈ Finset.univ.erase k, Gpoly a b j).natDegree ≤ 14 - k.1 :=
  le_trans (Polynomial.natDegree_prod_le _ _)
    (le_trans (Finset.sum_le_sum (fun j _ ↦ natDegree_Gpoly_le a b j)) (sum_erase_succ_le k))

private theorem natDegree_NPoly_le (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) :
    (NPoly a b nPos nNeg).natDegree ≤ 29 := by
  have hPk' : ∀ k : Fin 5, (derivative (Ppoly a b k)).natDegree ≤ k.1 := by
    intro k
    refine le_trans (Polynomial.natDegree_derivative_le _) ?_
    have := natDegree_Ppoly_le a b k; omega
  have hGk' : ∀ k : Fin 5, (derivative (Gpoly a b k)).natDegree ≤ k.1 := by
    intro k
    refine le_trans (Polynomial.natDegree_derivative_le _) ?_
    have := natDegree_Gpoly_le a b k; omega
  have hSA : (∑ k : Fin 5, Polynomial.C (nPos k : ℤ) * derivative (Ppoly a b k) *
      ∏ j ∈ Finset.univ.erase k, Ppoly a b j).natDegree ≤ 14 := by
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨by omega, fun k _ ↦ ?_⟩
    simp only [Function.comp_apply]
    rw [mul_assoc]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_mul_le_of_le (hPk' k)
      (natDegree_prod_erase_Ppoly_le a b k)) ?_
    have : k.1 < 5 := k.2; omega
  have hSB : (∑ k : Fin 5, Polynomial.C (nNeg k : ℤ) * derivative (Gpoly a b k) *
      ∏ j ∈ Finset.univ.erase k, Gpoly a b j).natDegree ≤ 14 := by
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨by omega, fun k _ ↦ ?_⟩
    simp only [Function.comp_apply]
    rw [mul_assoc]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_mul_le_of_le (hGk' k)
      (natDegree_prod_erase_Gpoly_le a b k)) ?_
    have : k.1 < 5 := k.2; omega
  rw [NPoly]
  exact Polynomial.natDegree_add_le_of_le
    (Polynomial.natDegree_mul_le_of_le (natDegree_prod_Gpoly_le a b) hSA)
    (Polynomial.natDegree_mul_le_of_le (natDegree_prod_Ppoly_le a b) hSB)

private theorem natDegree_Ltil_le (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) (v : ℕ) :
    (Ltilpoly a b nPos nNeg v).natDegree ≤ 31 := by
  rw [Ltilpoly, Mtilpoly, Sigmapoly]
  have h1X : ((1 : ℤ[X]) - X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [Polynomial.natDegree_one, Polynomial.natDegree_X]
    omega
  have hX : (X : ℤ[X]).natDegree ≤ 1 := by rw [Polynomial.natDegree_X]
  have hSig : (NPoly a b nPos nNeg - NPoly a b nNeg nPos).natDegree ≤ 29 :=
    Polynomial.natDegree_sub_le_of_le (natDegree_NPoly_le a b nPos nNeg)
      (natDegree_NPoly_le a b nNeg nPos)
  have hXSig : (X * (NPoly a b nPos nNeg - NPoly a b nNeg nPos)).natDegree ≤ 30 :=
    Polynomial.natDegree_mul_le_of_le hX hSig
  have hCD : (Polynomial.C (v : ℤ) * Dpoly a b).natDegree ≤ 30 :=
    le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_Dpoly_le a b)
  have hM : (X * (NPoly a b nPos nNeg - NPoly a b nNeg nPos) -
      Polynomial.C (v : ℤ) * Dpoly a b).natDegree ≤ 30 :=
    Polynomial.natDegree_sub_le_of_le hXSig hCD
  exact Polynomial.natDegree_mul_le_of_le h1X hM

private theorem caseI_dvd_Ltil_coeff
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (v : ℕ), nPos ≠ nNeg ∧
      (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      ∀ k, (37 : ℤ) ∣ (Ltilpoly a b nPos nNeg v).coeff k := by
  obtain ⟨nPos, nNeg, v, hne, hPosb, hNegb, hmem⟩ := caseI_evZ_Ltil_mem heq hgcd hcaseI
  refine ⟨nPos, nNeg, v, hne, hPosb, hNegb, ?_⟩
  set ζ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger with hζ
  have hdeg : (Ltilpoly a b nPos nNeg v).natDegree < 36 := by
    have := natDegree_Ltil_le a b nPos nNeg v; omega
  have hsum : evZ (Ltilpoly a b nPos nNeg v) = ∑ k ∈ Finset.range 36,
      ((Ltilpoly a b nPos nNeg v).coeff k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k := by
    rw [show evZ (Ltilpoly a b nPos nNeg v) =
      Polynomial.aeval ζ (Ltilpoly a b nPos nNeg v) from rfl,
      Polynomial.aeval_eq_sum_range' (by omega : (Ltilpoly a b nPos nNeg v).natDegree < 36)]
    refine Finset.sum_congr rfl (fun k _ ↦ by rw [Algebra.smul_def]; rfl)
  have hmem' : (∑ k : Fin 36,
      ((Ltilpoly a b nPos nNeg v).coeff k.1 : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ (k : ℕ)) ∈
      Ideal.span ({(37 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k ↦ ((Ltilpoly a b nPos nNeg v).coeff k : 𝓞 (CyclotomicField 37 ℚ)) * ζ ^ k) 36,
      ← hsum]
    exact hmem
  have hdvd36 : ∀ k : Fin 36, (37 : ℤ) ∣ (Ltilpoly a b nPos nNeg v).coeff k.1 :=
    caseI_dvd_of_sum_zeta_pow_mem (fun k ↦ (Ltilpoly a b nPos nNeg v).coeff k.1) hmem'
  intro k
  rcases lt_or_ge k 36 with hk | hk
  · exact hdvd36 ⟨k, hk⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by omega : (Ltilpoly a b nPos nNeg v).natDegree < k)]
    exact dvd_zero _

private theorem caseI_dvd_Mtil_coeff
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    ∃ (nPos nNeg : Fin 5 → ℕ) (v : ℕ), nPos ≠ nNeg ∧
      (∀ i, nPos i < 37) ∧ (∀ i, nNeg i < 37) ∧
      ∀ k, (37 : ℤ) ∣ (Mtilpoly a b nPos nNeg v).coeff k := by
  obtain ⟨nPos, nNeg, v, hne, hPosb, hNegb, hL⟩ := caseI_dvd_Ltil_coeff heq hgcd hcaseI
  refine ⟨nPos, nNeg, v, hne, hPosb, hNegb, ?_⟩
  have hLcoeff : ∀ k, (Ltilpoly a b nPos nNeg v).coeff (k + 1) =
      (Mtilpoly a b nPos nNeg v).coeff (k + 1) - (Mtilpoly a b nPos nNeg v).coeff k := by
    intro k
    rw [Ltilpoly, sub_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul]
  have hL0 : (Ltilpoly a b nPos nNeg v).coeff 0 = (Mtilpoly a b nPos nNeg v).coeff 0 := by
    rw [Ltilpoly, sub_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, sub_zero]
  have hM0 : (37 : ℤ) ∣ (Mtilpoly a b nPos nNeg v).coeff 0 := by rw [← hL0]; exact hL 0
  intro k
  induction k with
  | zero => exact hM0
  | succ n ih =>
    have hLn := hL (n + 1)
    rw [hLcoeff n] at hLn
    have : (Mtilpoly a b nPos nNeg v).coeff (n + 1) =
        ((Mtilpoly a b nPos nNeg v).coeff (n + 1) - (Mtilpoly a b nPos nNeg v).coeff n) +
          (Mtilpoly a b nPos nNeg v).coeff n := by ring
    rw [this]
    exact dvd_add hLn ih

private theorem eval_zero_Dpoly (a b : ℤ) :
    (Dpoly a b).eval 0 = a ^ 5 * b ^ 5 := by
  rw [Dpoly, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_prod]
  have hP : ∀ i : Fin 5, (Ppoly a b i).eval 0 = a := by
    intro i; rw [Ppoly]; simp
  have hG : ∀ i : Fin 5, (Gpoly a b i).eval 0 = b := by
    intro i; rw [Gpoly]; simp
  rw [Finset.prod_congr rfl (fun i _ ↦ hP i), Finset.prod_congr rfl (fun i _ ↦ hG i)]
  simp [Finset.prod_const]

private theorem coeff_zero_Mtil (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) (v : ℕ) :
    (Mtilpoly a b nPos nNeg v).coeff 0 = -(v : ℤ) * (a ^ 5 * b ^ 5) := by
  rw [Mtilpoly, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul,
    Polynomial.coeff_zero_eq_eval_zero, eval_zero_Dpoly]
  ring

private theorem derivative_Ppoly (a b : ℤ) (k : Fin 5) :
    derivative (Ppoly a b k) = Polynomial.C (b * (k.1 + 1)) * X ^ k.1 := by
  rw [Ppoly, derivative_add, Polynomial.derivative_C, zero_add, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_pow, Nat.add_sub_cancel, map_mul]
  push_cast; ring

private theorem derivative_Gpoly (a b : ℤ) (k : Fin 5) :
    derivative (Gpoly a b k) = Polynomial.C (a * (k.1 + 1)) * X ^ k.1 := by
  rw [Gpoly, derivative_add, Polynomial.derivative_C, zero_add, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_pow, Nat.add_sub_cancel, map_mul]
  push_cast; ring

private def termPoly (a b : ℤ) (k : Fin 5) : ℤ[X] :=
  derivative (Ppoly a b k) * ((∏ i : Fin 5, Gpoly a b i) * ∏ j ∈ Finset.univ.erase k, Ppoly a b j)
    - derivative (Gpoly a b k) *
      ((∏ i : Fin 5, Ppoly a b i) * ∏ j ∈ Finset.univ.erase k, Gpoly a b j)

private theorem Sigmapoly_eq_sum (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) :
    Sigmapoly a b nPos nNeg =
      ∑ k : Fin 5, Polynomial.C ((nPos k : ℤ) - (nNeg k : ℤ)) * termPoly a b k := by
  rw [Sigmapoly, NPoly, NPoly]
  simp only [termPoly]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  rw [map_sub]
  ring

private theorem eval_zero_gP (a b : ℤ) (k : Fin 5) :
    ((∏ i : Fin 5, Gpoly a b i) * ∏ j ∈ Finset.univ.erase k, Ppoly a b j).eval 0 =
      b ^ 5 * (a ^ 4) := by
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_prod]
  rw [Finset.prod_congr rfl (fun i _ ↦ by rw [Gpoly]; simp : ∀ i ∈ Finset.univ,
      (Gpoly a b i).eval 0 = b),
    Finset.prod_congr rfl (fun j _ ↦ by rw [Ppoly]; simp : ∀ j ∈ Finset.univ.erase k,
      (Ppoly a b j).eval 0 = a)]
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]

private theorem eval_zero_gG (a b : ℤ) (k : Fin 5) :
    ((∏ i : Fin 5, Ppoly a b i) * ∏ j ∈ Finset.univ.erase k, Gpoly a b j).eval 0 =
      a ^ 5 * (b ^ 4) := by
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_prod]
  rw [Finset.prod_congr rfl (fun i _ ↦ by rw [Ppoly]; simp : ∀ i ∈ Finset.univ,
      (Ppoly a b i).eval 0 = a),
    Finset.prod_congr rfl (fun j _ ↦ by rw [Gpoly]; simp : ∀ j ∈ Finset.univ.erase k,
      (Gpoly a b j).eval 0 = b)]
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]

private theorem coeff_termPoly_self (a b : ℤ) (k : Fin 5) :
    (termPoly a b k).coeff k.1 = (k.1 + 1) * a ^ 4 * b ^ 4 * (b ^ 2 - a ^ 2) := by
  rw [termPoly, derivative_Ppoly, derivative_Gpoly, Polynomial.coeff_sub]
  simp only [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', le_refl, if_true,
    Nat.sub_self]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero,
    eval_zero_gP, eval_zero_gG]
  ring

private theorem coeff_termPoly_lt (a b : ℤ) (k : Fin 5) {j : ℕ} (hj : j < k.1) :
    (termPoly a b k).coeff j = 0 := by
  rw [termPoly, derivative_Ppoly, derivative_Gpoly, Polynomial.coeff_sub]
  simp only [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  rw [if_neg (by omega), if_neg (by omega)]
  ring

private theorem coeff_Sigmapoly_at (a b : ℤ) (nPos nNeg : Fin 5 → ℕ) (i₀ : Fin 5)
    (hlt : ∀ k : Fin 5, k.1 < i₀.1 → (nPos k : ℤ) - (nNeg k : ℤ) = 0) :
    (Sigmapoly a b nPos nNeg).coeff i₀.1 =
      ((nPos i₀ : ℤ) - (nNeg i₀ : ℤ)) * ((i₀.1 + 1) * a ^ 4 * b ^ 4 * (b ^ 2 - a ^ 2)) := by
  rw [Sigmapoly_eq_sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i₀]
  · rw [Polynomial.coeff_C_mul, coeff_termPoly_self]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul]
    rcases lt_or_gt_of_ne (fun h ↦ hk (Fin.ext h) : k.1 ≠ i₀.1) with hlt' | hgt'
    · rw [hlt k hlt', zero_mul]
    · rw [coeff_termPoly_lt a b k hgt', mul_zero]
  · intro h; exact absurd (Finset.mem_univ i₀) h

private theorem caseI_a_sq_eq_b_sq
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    (37 : ℤ) ∣ b ^ 2 - a ^ 2 := by
  have hp37 : Prime (37 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; norm_num
  have hab : ¬ (37 : ℤ) ∣ a * b := fun h ↦ hcaseI (h.mul_right c)
  have ha : ¬ (37 : ℤ) ∣ a := fun h ↦ hab (h.mul_right b)
  have hb : ¬ (37 : ℤ) ∣ b := fun h ↦ hab (h.mul_left a)
  obtain ⟨nPos, nNeg, v, hne, hPosb, hNegb, hM⟩ := caseI_dvd_Mtil_coeff heq hgcd hcaseI
  have hv : (37 : ℤ) ∣ (v : ℤ) := by
    have h0 := hM 0
    rw [coeff_zero_Mtil] at h0
    have : (37 : ℤ) ∣ (v : ℤ) * (a ^ 5 * b ^ 5) := by
      have : -(v : ℤ) * (a ^ 5 * b ^ 5) = -((v : ℤ) * (a ^ 5 * b ^ 5)) := by ring
      rw [this] at h0; exact dvd_neg.mp h0
    rcases (hp37.dvd_mul.mp this) with h | h
    · exact h
    · exfalso; rcases hp37.dvd_mul.mp h with h' | h'
      · exact ha (hp37.dvd_of_dvd_pow h')
      · exact hb (hp37.dvd_of_dvd_pow h')
  have hexi : ∃ i : Fin 5, (nPos i : ℤ) - (nNeg i : ℤ) ≠ 0 := by
    by_contra! h
    exact hne (funext fun i ↦ by have := h i; omega)
  classical
  set i₀ := (Finset.univ.filter
    (fun i : Fin 5 ↦ (nPos i : ℤ) - (nNeg i : ℤ) ≠ 0)).min' (by
      rw [Finset.filter_nonempty_iff]; obtain ⟨i, hi⟩ := hexi; exact ⟨i, Finset.mem_univ i, hi⟩)
      with hi₀def
  have hi₀mem : i₀ ∈ Finset.univ.filter
      (fun i : Fin 5 ↦ (nPos i : ℤ) - (nNeg i : ℤ) ≠ 0) :=
    Finset.min'_mem _ _
  have hi₀ne : (nPos i₀ : ℤ) - (nNeg i₀ : ℤ) ≠ 0 := (Finset.mem_filter.mp hi₀mem).2
  have hi₀min : ∀ k : Fin 5, k.1 < i₀.1 → (nPos k : ℤ) - (nNeg k : ℤ) = 0 := by
    intro k hk
    by_contra hne'
    have : i₀ ≤ k := Finset.min'_le _ k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne'⟩)
    omega
  have hMcoeff : (Mtilpoly a b nPos nNeg v).coeff (i₀.1 + 1) =
      (Sigmapoly a b nPos nNeg).coeff i₀.1 - (v : ℤ) * (Dpoly a b).coeff (i₀.1 + 1) := by
    rw [Mtilpoly, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
  have hSig : (37 : ℤ) ∣ (Sigmapoly a b nPos nNeg).coeff i₀.1 := by
    have hMi := hM (i₀.1 + 1)
    rw [hMcoeff] at hMi
    have hvD : (37 : ℤ) ∣ (v : ℤ) * (Dpoly a b).coeff (i₀.1 + 1) :=
      hv.mul_right _
    have : (Sigmapoly a b nPos nNeg).coeff i₀.1 =
        ((Sigmapoly a b nPos nNeg).coeff i₀.1 - (v : ℤ) * (Dpoly a b).coeff (i₀.1 + 1)) +
          (v : ℤ) * (Dpoly a b).coeff (i₀.1 + 1) := by ring
    rw [this]; exact dvd_add hMi hvD
  rw [coeff_Sigmapoly_at a b nPos nNeg i₀ hi₀min] at hSig
  have hunit : ¬ (37 : ℤ) ∣
      ((nPos i₀ : ℤ) - (nNeg i₀ : ℤ)) * ((i₀.1 + 1) * a ^ 4 * b ^ 4) := by
    intro h
    rcases hp37.dvd_mul.mp h with h1 | h2
    · have hbnd1 : (nPos i₀ : ℤ) < 37 := by exact_mod_cast hPosb i₀
      have hbnd2 : (nNeg i₀ : ℤ) < 37 := by exact_mod_cast hNegb i₀
      have hbnd3 : (0 : ℤ) ≤ nPos i₀ := Int.natCast_nonneg _
      have hbnd4 : (0 : ℤ) ≤ nNeg i₀ := Int.natCast_nonneg _
      omega
    · rcases hp37.dvd_mul.mp h2 with h3 | h4
      · rcases hp37.dvd_mul.mp h3 with h5 | h6
        · have : (37 : ℤ) ≤ (i₀.1 + 1 : ℤ) := Int.le_of_dvd (by positivity) h5
          have : i₀.1 < 5 := i₀.2; omega
        · exact ha (hp37.dvd_of_dvd_pow h6)
      · exact hb (hp37.dvd_of_dvd_pow h4)
  rw [show ((nPos i₀ : ℤ) - (nNeg i₀ : ℤ)) * ((i₀.1 + 1) * a ^ 4 * b ^ 4 * (b ^ 2 - a ^ 2)) =
    (((nPos i₀ : ℤ) - (nNeg i₀ : ℤ)) * ((i₀.1 + 1) * a ^ 4 * b ^ 4)) * (b ^ 2 - a ^ 2) by ring]
    at hSig
  exact (hp37.dvd_mul.mp hSig).resolve_left hunit

private theorem gcd_triple_perm (a b c : ℤ) :
    ({c, -b, a} : Finset ℤ).gcd id = ({a, b, c} : Finset ℤ).gcd id := by
  have hdvd : ∀ x y z : ℤ, ({x, y, z} : Finset ℤ).gcd id ∣ x ∧
      ({x, y, z} : Finset ℤ).gcd id ∣ y ∧ ({x, y, z} : Finset ℤ).gcd id ∣ z := by
    intro x y z
    exact ⟨Finset.gcd_dvd (by simp), Finset.gcd_dvd (by simp), Finset.gcd_dvd (by simp)⟩
  have h1 := hdvd a b c
  have h2 := hdvd c (-b) a
  have hd1 : ({c, -b, a} : Finset ℤ).gcd id ∣ ({a, b, c} : Finset ℤ).gcd id := by
    refine Finset.dvd_gcd fun x hx ↦ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h2.2.2
    · exact dvd_neg.mp h2.2.1
    · exact h2.1
  have hd2 : ({a, b, c} : Finset ℤ).gcd id ∣ ({c, -b, a} : Finset ℤ).gcd id := by
    refine Finset.dvd_gcd fun x hx ↦ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1.2.2
    · exact dvd_neg.mpr h1.2.1
    · exact h1.1
  rw [← Finset.normalize_gcd (s := ({c, -b, a} : Finset ℤ)) (f := id),
    ← Finset.normalize_gcd (s := ({a, b, c} : Finset ℤ)) (f := id)]
  exact normalize_eq_normalize hd1 hd2

private theorem fltCaseI_primitive
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) : False := by
  have hab : (37 : ℤ) ∣ b ^ 2 - a ^ 2 := caseI_a_sq_eq_b_sq heq hgcd hcaseI
  have heq' : c ^ 37 + (-b) ^ 37 = a ^ 37 := by
    have hnb : (-b) ^ 37 = -(b ^ 37) := Odd.neg_pow (by norm_num) b
    rw [hnb]; linarith [heq]
  have hgcd' : ({c, -b, a} : Finset ℤ).gcd id = 1 := by rw [gcd_triple_perm]; exact hgcd
  have hcaseI' : ¬ (37 : ℤ) ∣ c * -b * a := by
    rw [show c * -b * a = -(a * b * c) by ring]; rwa [dvd_neg]
  have hbc0 : (37 : ℤ) ∣ (-b) ^ 2 - c ^ 2 := caseI_a_sq_eq_b_sq heq' hgcd' hcaseI'
  rw [neg_sq] at hbc0
  have hbc : (37 : ℤ) ∣ c ^ 2 - b ^ 2 := by rw [← neg_sub]; exact dvd_neg.mpr hbc0
  have ha0 : ¬ (37 : ℤ) ∣ a := fun h ↦ hcaseI ((h.mul_right b).mul_right c)
  have hb0 : ¬ (37 : ℤ) ∣ b := fun h ↦ hcaseI ((h.mul_left a).mul_right c)
  have hcong : ((a : ZMod 37) + b) = c := by
    have hdvd : (37 : ℤ) ∣ a + b - c := by
      obtain ⟨na, ha⟩ := thirtyseven_dvd_pow_sub_self a
      obtain ⟨nb, hb⟩ := thirtyseven_dvd_pow_sub_self b
      obtain ⟨nc, hc⟩ := thirtyseven_dvd_pow_sub_self c
      exact ⟨nc - na - nb, by linarith [heq]⟩
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b - c) 37).mpr hdvd
    push_cast at hh; linear_combination hh
  have hsqab : (a : ZMod 37) ^ 2 = (b : ZMod 37) ^ 2 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (b ^ 2 - a ^ 2) 37).mpr hab
    push_cast at hh
    exact (sub_eq_zero.mp hh).symm
  have hsqcb : (c : ZMod 37) ^ 2 = (b : ZMod 37) ^ 2 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (c ^ 2 - b ^ 2) 37).mpr hbc
    push_cast at hh
    exact sub_eq_zero.mp hh
  have ha0' : (a : ZMod 37) ≠ 0 := fun h ↦
    ha0 ((ZMod.intCast_zmod_eq_zero_iff_dvd a 37).mp (by exact_mod_cast h))
  have hb0' : (b : ZMod 37) ≠ 0 := fun h ↦
    hb0 ((ZMod.intCast_zmod_eq_zero_iff_dvd b 37).mp (by exact_mod_cast h))
  have hkey : (a : ZMod 37) * ((a : ZMod 37) + 2 * b) = 0 := by
    have h1 : ((a : ZMod 37) + b) ^ 2 = (b : ZMod 37) ^ 2 := by rw [hcong]; exact hsqcb
    linear_combination h1
  rcases mul_eq_zero.mp hkey with h | h
  · exact ha0' h
  · have ha2b : (a : ZMod 37) = -2 * b := by linear_combination h
    have h3 : (3 : ZMod 37) * (b : ZMod 37) ^ 2 = 0 := by
      have hh : (a : ZMod 37) ^ 2 = 4 * b ^ 2 := by rw [ha2b]; ring
      rw [hsqab] at hh; linear_combination -hh
    have h3ne : (3 : ZMod 37) ≠ 0 := by
      rw [show (3 : ZMod 37) = ((3 : ℕ) : ZMod 37) by norm_num, Ne,
        ZMod.natCast_eq_zero_iff]
      decide
    exact hb0' (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp
      ((mul_eq_zero.mp h3).resolve_left h3ne))

/-- **First case of Fermat's Last Theorem for the exponent `p = 37`.**
There are no integers `x, y, z`, all coprime to `37`, with `x^37 + y^37 = z^37`.

This is the Eichler argument (Washington, *Introduction to Cyclotomic Fields*,
Theorem 6.23, pp. 108–110): the Herbrand bound `p-rank C⁻ ≤ 1` for `p = 37`
combined with the pigeonhole descent and the analytic `(1-T)`-differentiation
finish, run symmetrically. -/
theorem fltCaseI_thirtyseven (x y z : ℤ)
    (hx : ¬ (37 : ℤ) ∣ x) (hy : ¬ (37 : ℤ) ∣ y) (hz : ¬ (37 : ℤ) ∣ z)
    (heq : x ^ 37 + y ^ 37 = z ^ 37) : False := by
  have hp37 : Prime (37 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; norm_num
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ dvd_zero _)
  have hy0 : y ≠ 0 := fun h ↦ hy (h ▸ dvd_zero _)
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ dvd_zero _)
  have hprod : x * y * z ≠ 0 := by
    simp only [mul_ne_zero_iff]; exact ⟨⟨hx0, hy0⟩, hz0⟩
  have hcaseI : ¬ (37 : ℤ) ∣ x * y * z := fun h ↦
    (hp37.dvd_mul.mp h).elim (fun h' ↦ (hp37.dvd_mul.mp h').elim hx hy) hz
  obtain ⟨heq', hgcd', hprod'⟩ := FltRegular.MayAssume.coprime heq hprod
  set d : ℤ := ({x, y, z} : Finset ℤ).gcd id with hd
  have hdx : d ∣ x := Finset.gcd_dvd (by simp)
  have hdy : d ∣ y := Finset.gcd_dvd (by simp)
  have hdz : d ∣ z := Finset.gcd_dvd (by simp)
  have hcaseI' : ¬ (37 : ℤ) ∣ (x / d) * (y / d) * (z / d) := by
    intro h
    apply hcaseI
    obtain ⟨nx, hnx⟩ := hdx; obtain ⟨ny, hny⟩ := hdy; obtain ⟨nz, hnz⟩ := hdz
    have hdne : d ≠ 0 := fun h0 ↦ hx0 (by
      have := Finset.gcd_eq_zero_iff.mp h0 x (by simp); simpa using this)
    refine h.trans ?_
    refine ⟨d ^ 3, ?_⟩
    rw [hnx, hny, hnz]
    rw [Int.mul_ediv_cancel_left _ hdne, Int.mul_ediv_cancel_left _ hdne,
      Int.mul_ediv_cancel_left _ hdne]
    ring
  exact fltCaseI_primitive heq' hgcd' hcaseI'

end Eichler

end FLT37

end BernoulliRegular

end
