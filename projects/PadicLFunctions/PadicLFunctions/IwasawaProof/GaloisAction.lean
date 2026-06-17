/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Map
import PadicLFunctions.Iwasawa.LocalUnits
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The Galois action on the cyclotomic tower (RJW §12.1, TeX 3182–3243) — E12.1

The linchpin of §12: an action of `𝒢 = ℤ_[p]ˣ` (via the cyclotomic character) on the
tower `𝒰_∞ = NormCompatUnits p`, by `σ_a(ξ_n) = ξ_n^{a mod p^n}`, and the
`𝒢`-equivariance of the Coleman map. mathlib supplies the ABSTRACT iso
`IsCyclotomicExtension.autEquivPow : (K_n ≃ₐ[ℚ_p] K_n) ≃* (ZMod (p^n))ˣ` (Tower.lean's
`isCyclotomicExtension_K` enables it over `ℚ_[p]`); the work here is realising the action
on the concrete fixed-`ξ` `ℂ_[p]`-tower, compatibly across levels and commuting with
`levelNorm`.

Skeleton (`/develop` §12): the constructions `galAut`/`galNCU`/`galSeries` are stated with
`sorry` bodies so the downstream equivariance statements elaborate; the E12.1 execution
ticket fills them (its first step: make Tower's `isCyclotomicExtension_K` public, then
`galAut p a n := (IsCyclotomicExtension.autEquivPow (K p n) (cyclotomic_irreducible_Qp …)).symm
(unitsToZModPow p n a)`).
-/

open PadicLFunctions PadicLFunctions.Coleman

open IsCyclotomicExtension

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- `NeZero (p ^ n)` (the cyclotomic-extension instances need it). -/
instance instNeZeroPpow (n : ℕ) : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩

/-- `σ_a` at level `n`: the automorphism of `K_n` sending `ξ_n ↦ ξ_n^{a mod p^n}`
(RJW TeX 3190). For `n ≥ 1` it is `(autEquivPow K_n …).symm` of the residue
`a mod p^n` (`IsCyclotomicExtension.autEquivPow`); for `n = 0` (`K_0 = ℚ_p`) the
action is trivial (`AlgEquiv.refl`). -/
def galAut (a : ℤ_[p]ˣ) (n : ℕ) : (K p n) ≃ₐ[ℚ_[p]] (K p n) :=
  if hn : 1 ≤ n then
    (IsCyclotomicExtension.autEquivPow (K p n)
      (cyclotomic_irreducible_Qp p hn)).symm (PadicMeasure.unitsToZModPow p n a)
  else AlgEquiv.refl

/-- `ξ_n^i = ξ_n^j` whenever `i ≡ j (mod p^n)` (the root has order `p^n`); the engine for
the tower-compatibility exponent reductions. -/
theorem zetaSys_pow_eq_pow_of_modEq {n i j : ℕ} (h : i ≡ j [MOD p ^ n]) :
    zetaSys p n ^ i = zetaSys p n ^ j := by
  set ζu : ℂ_[p]ˣ := (zetaSys_primitiveRoot p n).isUnit (NeZero.ne _) |>.unit with hζu
  have hζuval : (ζu : ℂ_[p]) = zetaSys p n := IsUnit.unit_spec _
  have hζuprim : IsPrimitiveRoot ζu (p ^ n) := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζuval]; exact zetaSys_primitiveRoot p n
  have hu : ζu ^ i = ζu ^ j := by
    rw [pow_eq_pow_iff_modEq, ← hζuprim.eq_orderOf]; exact h
  have := congrArg (Units.val) hu
  rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hζuval] at this

/-- The project's fixed root `ξ_n`, as a primitive `p^n`-th root of unity *inside* the
subtype `K_n` (transported from `ℂ_[p]` along the injective ring hom `K_n ↪ ℂ_[p]`). -/
theorem zetaSysK_primitiveRoot (n : ℕ) :
    IsPrimitiveRoot (⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n) (p ^ n) := by
  rw [← IsPrimitiveRoot.coe_submonoidClass_iff (M := ℂ_[p])]
  exact zetaSys_primitiveRoot p n

/-- **The autToPow root-independence bridge** (T1201a): for any `ℚ_p`-automorphism `f`
of `K_n`, the cyclotomic-character value `autToPow` computed via the project's fixed
root `ξ_n` agrees with the one computed via mathlib's chosen root `ζ = zeta (p^n) ℚ_p K_n`
(the one `autEquivPow` uses). Both `ξ_n` and `ζ` are primitive `p^n`-roots, so
`ζ = ξ_n^c` for a `c` coprime to `p^n`; the two `autToPow` values `m, m'` then satisfy
`ξ_n^{c·m.val} = f ζ = ξ_n^{c·m'.val}`, i.e. `c·m ≡ c·m' (mod p^n)`, and `c` invertible
forces `m = m'`. -/
theorem autToPow_zetaSys_eq {n : ℕ} (f : (K p n) ≃ₐ[ℚ_[p]] (K p n)) :
    (zetaSysK_primitiveRoot p n).autToPow ℚ_[p] f
      = (zeta_spec (p ^ n) ℚ_[p] (K p n)).autToPow ℚ_[p] f := by
  set ζξ : K p n := ⟨zetaSys p n, zetaSys_mem_K p n⟩ with hζξ
  set hξ := zetaSysK_primitiveRoot p n with hhξ
  set hζ := zeta_spec (p ^ n) ℚ_[p] (K p n) with hhζ
  set m := hξ.autToPow ℚ_[p] f with hm
  set m' := hζ.autToPow ℚ_[p] f with hm'
  obtain ⟨c, _, hc⟩ := hξ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hcop : Nat.Coprime c (p ^ n) := by
    rw [← hξ.pow_iff_coprime (pow_pos hp.out.pos n) c, hc]; exact hζ
  have hspecξ : ζξ ^ (m : ZMod (p ^ n)).val = f ζξ := hξ.autToPow_spec ℚ_[p] f
  have hspecζ : (zeta (p ^ n) ℚ_[p] (K p n)) ^ (m' : ZMod (p ^ n)).val = f (zeta _ _ _) :=
    hζ.autToPow_spec ℚ_[p] f
  have hfζ1 : f (zeta (p ^ n) ℚ_[p] (K p n)) = ζξ ^ (c * (m : ZMod (p ^ n)).val) := by
    rw [← hc, map_pow, ← hspecξ, ← pow_mul, mul_comm]
  have hfζ2 : f (zeta (p ^ n) ℚ_[p] (K p n)) = ζξ ^ (c * (m' : ZMod (p ^ n)).val) := by
    rw [← hspecζ, ← hc, ← pow_mul]
  have hpow : ζξ ^ (c * (m : ZMod (p ^ n)).val) = ζξ ^ (c * (m' : ZMod (p ^ n)).val) := by
    rw [← hfζ1, ← hfζ2]
  set ζu : ℂ_[p]ˣ := (zetaSys_primitiveRoot p n).isUnit (NeZero.ne _) |>.unit with hζu
  have hζuval : (ζu : ℂ_[p]) = zetaSys p n := IsUnit.unit_spec _
  have hζuprim : IsPrimitiveRoot ζu (p ^ n) := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζuval]; exact zetaSys_primitiveRoot p n
  have hpowU : ζu ^ (c * (m : ZMod (p ^ n)).val) = ζu ^ (c * (m' : ZMod (p ^ n)).val) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hζuval]
    have := congrArg (Subtype.val) hpow
    rwa [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, hζξ] at this
  rw [pow_eq_pow_iff_modEq, ← hζuprim.eq_orderOf, ← ZMod.natCast_eq_natCast_iff] at hpowU
  push_cast at hpowU
  have hcunit : IsUnit (c : ZMod (p ^ n)) := by
    rw [ZMod.isUnit_iff_coprime]; exact hcop
  have hvaleq : ((m : ZMod (p ^ n)).val : ZMod (p ^ n))
      = ((m' : ZMod (p ^ n)).val : ZMod (p ^ n)) :=
    hcunit.mul_left_cancel hpowU
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hvaleq
  exact Units.ext hvaleq

/-- `σ_a(ξ_n) = ξ_n^{(a mod p^n)}` (the defining cyclotomic-character property,
`IsPrimitiveRoot.autToPow_spec`). The cyclotomic-character value of `galAut p a n`,
computed via the project's root `ξ_n` (`autToPow_zetaSys_eq` bridge), is exactly
`a mod p^n`, because `galAut` is `autEquivPow.symm` of that residue. -/
theorem galAut_zetaSys (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) :
    (galAut p a n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p])
      = zetaSys p n ^ ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) :
        ZMod (p ^ n)).val := by
  set t : (ZMod (p ^ n))ˣ := PadicMeasure.unitsToZModPow p n a with ht
  set h := cyclotomic_irreducible_Qp p hn with hh
  have hgal : galAut p a n = (IsCyclotomicExtension.autEquivPow (K p n) h).symm t := by
    rw [galAut, dif_pos hn]
  have hae : IsCyclotomicExtension.autEquivPow (K p n) h (galAut p a n) = t := by
    rw [hgal, MulEquiv.apply_symm_apply]
  have hval : (zetaSysK_primitiveRoot p n).autToPow ℚ_[p] (galAut p a n) = t := by
    rw [autToPow_zetaSys_eq, ← hae, IsCyclotomicExtension.autEquivPow_apply]
    rfl
  have hspec := (zetaSysK_primitiveRoot p n).autToPow_spec ℚ_[p] (galAut p a n)
  rw [hval] at hspec
  have hcoe := congrArg (Subtype.val) hspec
  rw [SubmonoidClass.coe_pow] at hcoe
  exact hcoe.symm

/-- **Complex conjugation** `σ_{-1}` sends `ξ_{p^n} ↦ ξ_{p^n}⁻¹` (the cyclotomic-character
value `-1`, read through `unitsToZModPow (-1) = -1` and `ξ^{(-1).val} = ξ⁻¹`). RJW TeX 3185. -/
theorem galAut_neg_one_zetaSys {n : ℕ} (hn : 1 ≤ n) :
    (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]) = (zetaSys p n)⁻¹ := by
  rw [galAut_zetaSys p (-1) hn]
  have hneg : (PadicMeasure.unitsToZModPow p n (-1) : (ZMod (p ^ n))ˣ) = -1 := by
    apply Units.ext; rw [PadicMeasure.unitsToZModPow_coe]; push_cast; simp
  rw [hneg]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ]
  refine (zetaSys_pow_eq_pow_of_modEq p
    (i := (((-1 : (ZMod (p ^ n))ˣ) : ZMod (p ^ n))).val + 1) (j := 0) ?_).trans ?_
  · rw [← ZMod.natCast_eq_natCast_iff]; push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  · rw [pow_zero]

/-- `K_n/ℚ_p` is a Galois extension (it is a cyclotomic extension). -/
instance isGalois_K (n : ℕ) : IsGalois ℚ_[p] (K p n) := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  exact IsCyclotomicExtension.isGalois {p ^ n} ℚ_[p] (K p n)

/-- `K_n` is finite-dimensional over `ℚ_p` (degree `φ(p^n) > 0`). -/
instance finiteDimensional_K (n : ℕ) : FiniteDimensional ℚ_[p] (K p n) :=
  Module.finite_of_finrank_pos (R := ℚ_[p])
    (by rw [finrank_K]; exact Nat.totient_pos.2 (pow_pos hp.out.pos n))

/-- `ξ_{p^n} ≠ ξ_{p^n}⁻¹` for `p` odd and `n ≥ 1`: otherwise `ξ_n^2 = 1`, but `ξ_n` has
order `p^n ≥ 3` (RJW: this is where `p ≠ 2` enters the order-2 of conjugation). -/
theorem zetaSys_ne_inv (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    zetaSys p n ≠ (zetaSys p n)⁻¹ := by
  intro h
  have hξ0 : zetaSys p n ≠ 0 := (zetaSys_primitiveRoot p n).ne_zero (pow_pos hp.out.pos n).ne'
  have hsq : zetaSys p n ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel₀ hξ0
  have hdvd : p ^ n ∣ 2 := (zetaSys_primitiveRoot p n).dvd_of_pow_eq_one 2 hsq
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have : 3 ≤ p ^ n := le_trans hp3 (le_self_pow (by omega) (by omega))
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)

/-- `⟨ξ_n, _⟩` is integral over `ℚ_p` inside `K_n` (it is a root of unity). -/
private theorem isIntegral_zetaSysK (n : ℕ) :
    IsIntegral ℚ_[p] (⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n) :=
  ((zetaSysK_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).tower_top

/-- `K_n` is generated over `ℚ_p` by `⟨ξ_n, _⟩` as a subalgebra of itself: the adjoin of
the generator is `⊤`. (`K_n = ℚ_p(ξ_n)`, so `ξ_n` generates the whole field.) -/
private theorem adjoin_zetaSysK_eq_top (n : ℕ) :
    Algebra.adjoin ℚ_[p] {(⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (isIntegral_zetaSysK p n).isAlgebraic]
  rw [show (IntermediateField.adjoin ℚ_[p] {(⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)})
      = ⊤ from ?_]
  · rfl
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  have hmap : y ∈ (IntermediateField.adjoin ℚ_[p]
      {(⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)}).map (K p n).val := by
    rw [IntermediateField.adjoin_map]
    simp only [Set.image_singleton, IntermediateField.val_mk]
    change y ∈ K p n
    exact hy
  obtain ⟨z, hz, hzy⟩ := hmap
  have hzeq : (⟨y, hy⟩ : K p n) = z := Subtype.ext hzy.symm
  rw [hzeq]; exact hz

/-- **`σ_{-1}` has order `2`** (RJW §12, `p` odd, `n ≥ 1`): it is an involution
(`σ_{-1}^2 = id` since `(-1)·(-1) = 1`) and is non-trivial (`σ_{-1}(ξ) = ξ⁻¹ ≠ ξ`). -/
theorem orderOf_galAut_neg_one (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    orderOf (galAut p (-1) n) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · refine AlgEquiv.ext fun y => ?_
    have hξ : ((galAut p (-1) n ^ 2) ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p])
        = (⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n) := by
      rw [pow_two]
      change (galAut p (-1) n (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩) : ℂ_[p]) = _
      have h1 : galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩
          = ⟨(zetaSys p n)⁻¹, (K p n).inv_mem (zetaSys_mem_K p n)⟩ :=
        Subtype.ext (by rw [galAut_neg_one_zetaSys p hn])
      rw [h1]
      have h2 : (⟨(zetaSys p n)⁻¹, (K p n).inv_mem (zetaSys_mem_K p n)⟩ : K p n)
          = (⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)⁻¹ :=
        Subtype.ext (by rw [IntermediateField.coe_inv])
      rw [h2, map_inv₀, IntermediateField.coe_inv, galAut_neg_one_zetaSys p hn, inv_inv]
    have hcongr : (galAut p (-1) n ^ 2) ⟨zetaSys p n, zetaSys_mem_K p n⟩
        = (1 : (K p n) ≃ₐ[ℚ_[p]] (K p n)) ⟨zetaSys p n, zetaSys_mem_K p n⟩ :=
      Subtype.ext (by rw [hξ]; rfl)
    have heq : (galAut p (-1) n ^ 2) = (1 : (K p n) ≃ₐ[ℚ_[p]] (K p n)) := by
      apply AlgEquiv.coe_algHom_injective
      apply AlgHom.ext_of_adjoin_eq_top (adjoin_zetaSysK_eq_top p n)
      rintro z (rfl : z = ⟨zetaSys p n, zetaSys_mem_K p n⟩)
      exact hcongr
    exact AlgEquiv.ext_iff.1 heq y
  · intro hone
    have : (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]) = zetaSys p n := by
      rw [hone]; rfl
    rw [galAut_neg_one_zetaSys p hn] at this
    exact zetaSys_ne_inv p hp2 hn this.symm

/-- `K_n⁺` viewed as an intermediate field of `K_n / ℚ_p` (it sits inside `K_n` by
`KPlus_le_K`). Reducible so that the relative-algebra instances on `K_n` over it resolve. -/
noncomputable abbrev KPlusRestrict (n : ℕ) : IntermediateField ℚ_[p] (K p n) :=
  IntermediateField.restrict (KPlus_le_K p n)

/-- **Reality of `K_n⁺`**: complex conjugation `σ_{-1}` fixes every element of `K_n⁺`
pointwise. `K_n⁺ = ℚ_p(ξ+ξ⁻¹)` and `σ_{-1}` (a `ℚ_p`-automorphism of `K_n ⊇ K_n⁺`) fixes the
generator `ξ+ξ⁻¹` (`galAut_neg_one_zetaSys` + `add_comm`) and all of `ℚ_p`; closure under the
field operations is the `adjoin` induction. -/
theorem galAut_neg_one_fixes_KPlus {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]}
    (hx : x ∈ KPlus p n) (hxK : x ∈ K p n) :
    (galAut p (-1) n ⟨x, hxK⟩ : ℂ_[p]) = x := by
  have hgen : ∀ (hzK : zetaSys p n + (zetaSys p n)⁻¹ ∈ K p n),
      (galAut p (-1) n ⟨zetaSys p n + (zetaSys p n)⁻¹, hzK⟩ : ℂ_[p])
        = zetaSys p n + (zetaSys p n)⁻¹ := fun hzK => by
    rw [show (⟨zetaSys p n + (zetaSys p n)⁻¹, hzK⟩ : K p n)
        = ⟨zetaSys p n, zetaSys_mem_K p n⟩ + (⟨zetaSys p n, zetaSys_mem_K p n⟩)⁻¹ from
      Subtype.ext (by push_cast [Subtype.coe_mk]; rfl), map_add, map_inv₀,
      show ((galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩
          + (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩)⁻¹ : K p n) : ℂ_[p])
          = (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p])
            + ((galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]))⁻¹ from by
        push_cast; ring,
      galAut_neg_one_zetaSys p hn, inv_inv, add_comm]
  have key : ∀ y ∈ KPlus p n, ∀ (hyK : y ∈ K p n),
      (galAut p (-1) n ⟨y, hyK⟩ : ℂ_[p]) = y := by
    intro y hy
    rw [KPlus] at hy
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz => obtain rfl := hz; intro hzK; exact hgen hzK
    | algebraMap r =>
        intro hrK
        have hcoe : ((algebraMap ℚ_[p] (K p n) r : K p n) : ℂ_[p])
            = (algebraMap ℚ_[p] ℂ_[p]) r := by
          rw [← IntermediateField.algebraMap_apply]; rfl
        rw [show (⟨(algebraMap ℚ_[p] ℂ_[p]) r, hrK⟩ : K p n) = algebraMap ℚ_[p] (K p n) r from
          Subtype.ext hcoe, AlgEquiv.commutes, hcoe]
    | add a b ha hb iha ihb =>
        intro habK
        have haK : a ∈ K p n := KPlus_le_K p n ha
        have hbK : b ∈ K p n := KPlus_le_K p n hb
        rw [show (⟨a + b, habK⟩ : K p n) = ⟨a, haK⟩ + ⟨b, hbK⟩ from Subtype.ext rfl, map_add]
        rw [show ((galAut p (-1) n ⟨a, haK⟩ + galAut p (-1) n ⟨b, hbK⟩ : K p n) : ℂ_[p])
            = (galAut p (-1) n ⟨a, haK⟩ : ℂ_[p]) + (galAut p (-1) n ⟨b, hbK⟩ : ℂ_[p]) from rfl,
          iha haK, ihb hbK]
    | mul a b ha hb iha ihb =>
        intro habK
        have haK : a ∈ K p n := KPlus_le_K p n ha
        have hbK : b ∈ K p n := KPlus_le_K p n hb
        rw [show (⟨a * b, habK⟩ : K p n) = ⟨a, haK⟩ * ⟨b, hbK⟩ from Subtype.ext rfl, map_mul]
        rw [show ((galAut p (-1) n ⟨a, haK⟩ * galAut p (-1) n ⟨b, hbK⟩ : K p n) : ℂ_[p])
            = (galAut p (-1) n ⟨a, haK⟩ : ℂ_[p]) * (galAut p (-1) n ⟨b, hbK⟩ : ℂ_[p]) from rfl,
          iha haK, ihb hbK]
    | inv a ha iha =>
        intro haInvK
        have haK : a ∈ K p n := KPlus_le_K p n ha
        rw [show (⟨a⁻¹, haInvK⟩ : K p n) = (⟨a, haK⟩ : K p n)⁻¹ from
          Subtype.ext (by push_cast; rfl), map_inv₀]
        push_cast
        rw [iha haK]
  exact key x hx hxK

/-- `K_n⁺ ⊆ (K_n)^{⟨σ_{-1}⟩}`: every element of `K_n⁺` is fixed by complex conjugation, so
`K_n⁺` sits inside the fixed field. (The Galois reformulation of `galAut_neg_one_fixes_KPlus`,
via `K ≤ fixedField H ↔ H ≤ fixingSubgroup K` and `zpowers σ ≤ G ↔ σ ∈ G`.) -/
theorem KPlusRestrict_le_fixedField {n : ℕ} (hn : 1 ≤ n) :
    KPlusRestrict p n ≤ IntermediateField.fixedField
      (Subgroup.zpowers (galAut p (-1) n)) := by
  rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [KPlusRestrict, IntermediateField.mem_restrict] at hx
  exact Subtype.ext (galAut_neg_one_fixes_KPlus p hn hx x.2)

/-- `[K_n : (K_n)^{⟨σ_{-1}⟩}] = 2` (Galois correspondence: the fixed-field degree equals the
order of the subgroup, here `|⟨σ_{-1}⟩| = orderOf σ_{-1} = 2`). -/
theorem finrank_fixedField_galAut_neg_one (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank
      (IntermediateField.fixedField (Subgroup.zpowers (galAut p (-1) n))) (K p n) = 2 := by
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers,
    orderOf_galAut_neg_one p hp2 hn]

/-- `ℚ_p(ξ_n) = K_n` as an intermediate field of `K_n / ℚ_p` (the `IntermediateField`
recast of `adjoin_zetaSysK_eq_top`). -/
private theorem adjoinSimple_zetaSysK_eq_top (n : ℕ) :
    IntermediateField.adjoin ℚ_[p] {(⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)} = ⊤ := by
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (isIntegral_zetaSysK p n).isAlgebraic, IntermediateField.top_toSubalgebra,
    adjoin_zetaSysK_eq_top p n]

set_option maxHeartbeats 1600000 in
-- Field theory over the `restrict`-subtype `↥(KPlusRestrict p n)` (a `fieldRange` of an
-- inclusion) makes instance search and `compute_degree`/`minpoly.min` heavy; raised limits.
set_option synthInstance.maxHeartbeats 400000 in
/-- `[K_n : K_n⁺] ≤ 2`: `ξ_n` is a root of the monic degree-2 polynomial
`X² − (ξ+ξ⁻¹)X + 1` over `K_n⁺`, and `K_n = K_n⁺(ξ_n)` (since `ℚ_p(ξ_n) = K_n`), so the
relative degree is `(minpoly K_n⁺ ξ_n).natDegree ≤ 2`. -/
theorem finrank_K_over_KPlusRestrict_le {n : ℕ} (_hn : 1 ≤ n) :
    Module.finrank (KPlusRestrict p n) (K p n) ≤ 2 := by
  set ξK : K p n := ⟨zetaSys p n, zetaSys_mem_K p n⟩ with hξK
  have htop : IntermediateField.adjoin (KPlusRestrict p n) {ξK} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top (F := ℚ_[p])
      (adjoinSimple_zetaSysK_eq_top p n)
  have hξint : IsIntegral (KPlusRestrict p n) ξK := (isIntegral_zetaSysK p n).tower_top
  have hβmem : (zetaSys p n + (zetaSys p n)⁻¹) ∈ KPlus p n :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  set βK : K p n := ⟨zetaSys p n + (zetaSys p n)⁻¹, KPlus_le_K p n hβmem⟩ with hβK
  have hβrestrict : βK ∈ KPlusRestrict p n :=
    (IntermediateField.mem_restrict (KPlus_le_K p n) βK).2 hβmem
  set β : KPlusRestrict p n := ⟨βK, hβrestrict⟩ with hβdef
  set g : Polynomial (KPlusRestrict p n) := Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1
    with hg
  have hgmonic : g.Monic := by rw [hg]; monicity!
  have hgdeg : g.natDegree = 2 := by rw [hg]; compute_degree!
  have hroot : (Polynomial.aeval ξK) g = 0 := by
    have hξne : zetaSys p n ≠ 0 :=
      (zetaSys_primitiveRoot p n).ne_zero (pow_pos hp.out.pos n).ne'
    rw [hg, map_add, map_sub, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.aeval_one]
    apply Subtype.ext
    have hcoe : ((algebraMap (KPlusRestrict p n) (K p n) β : K p n) : ℂ_[p])
        = zetaSys p n + (zetaSys p n)⁻¹ := rfl
    push_cast [hξK]
    rw [hcoe]
    field_simp
    ring
  rw [show Module.finrank (KPlusRestrict p n) (K p n)
      = Module.finrank (KPlusRestrict p n) (IntermediateField.adjoin (KPlusRestrict p n) {ξK}) from
    by rw [htop]; exact (LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv).symm,
    IntermediateField.adjoin.finrank hξint]
  calc (minpoly (KPlusRestrict p n) ξK).natDegree
      ≤ g.natDegree := Polynomial.natDegree_le_natDegree (minpoly.min _ _ hgmonic hroot)
    _ = 2 := hgdeg

/-- **RJW §12, the Galois fixed-field characterisation of `K_n⁺`**: the maximal totally real
subfield `K_n⁺ = ℚ_p(ξ + ξ⁻¹)` is exactly the fixed field of complex conjugation
`σ_{-1} = galAut p (-1) n`. (Stated through `KPlusRestrict`, the realisation of `K_n⁺` as an
intermediate field of `K_n/ℚ_p`, so both sides have the same type.)

Proof: `K_n⁺ ⊆ (K_n)^{⟨σ_{-1}⟩}` (reality), and the two have the same `ℚ_p`-dimension —
`[K_n : (K_n)^{⟨σ_{-1}⟩}] = 2` (order of `σ_{-1}`) while `[K_n : K_n⁺] ≤ 2` (`ξ` quadratic over
`K_n⁺`), so via `[K_n:ℚ_p] = [F:ℚ_p]·[K_n:F]` both equal `φ(p^n)/2`. -/
theorem KPlus_eq_fixedField (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    KPlusRestrict p n
      = IntermediateField.fixedField (Subgroup.zpowers (galAut p (-1) n)) := by
  refine IntermediateField.eq_of_le_of_finrank_le' (KPlusRestrict_le_fixedField p hn) ?_
  rw [finrank_fixedField_galAut_neg_one p hp2 hn]
  exact finrank_K_over_KPlusRestrict_le p hn

/-- **Membership form of the fixed-field characterisation**: an element `x ∈ K_n` lies in
`K_n⁺` iff it is fixed by complex conjugation `σ_{-1}`. (`KPlus_eq_fixedField` applied through
`KPlusRestrict`/`fixedField` membership, with the `zpowers σ_{-1}` collapse to the single
generator `σ_{-1}`.) -/
theorem mem_KPlus_iff_galAut_neg_one_fixed (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]}
    (hxK : x ∈ K p n) :
    x ∈ KPlus p n ↔ (galAut p (-1) n ⟨x, hxK⟩ : ℂ_[p]) = x := by
  rw [show (x ∈ KPlus p n) ↔ (⟨x, hxK⟩ : K p n) ∈ KPlusRestrict p n from
    (IntermediateField.mem_restrict (KPlus_le_K p n) ⟨x, hxK⟩).symm,
    KPlus_eq_fixedField p hp2 hn, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    have := h (galAut p (-1) n) (Subgroup.mem_zpowers _)
    exact congrArg (Subtype.val) this
  · intro h f hf
    rw [Subgroup.mem_zpowers_iff] at hf
    obtain ⟨k, rfl⟩ := hf
    have hfix : galAut p (-1) n ⟨x, hxK⟩ = ⟨x, hxK⟩ := Subtype.ext h
    have hfixinv : (galAut p (-1) n)⁻¹ ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
      apply (galAut p (-1) n).injective
      rw [hfix, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    change (galAut p (-1) n ^ k) (⟨x, hxK⟩ : K p n) = ⟨x, hxK⟩
    induction k using Int.induction_on with
    | zero => simp
    | succ m ih => rw [zpow_add_one, AlgEquiv.mul_apply, hfix, ih]
    | pred m ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hfixinv, ih]

/-- **The unit-level fixed-field criterion** (RJW §12.5, the form fed to the milestone): a
principal unit `u ∈ 𝒰_{n,1}` lies in the totally real subgroup `𝒰⁺_{n,1}` iff its value is
fixed by complex conjugation `σ_{-1}`. This transports `mem_KPlus_iff_galAut_neg_one_fixed`
through `localUnitsOnePlus = localUnitsOne ⊓ localUnitsPlus` (`localUnitsPlus` membership is
`localUnits` + `(u : ℂ_[p]) ∈ K_n⁺`). -/
theorem mem_localUnitsOnePlus_iff_galAut_fixed (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n)
    {u : ℂ_[p]ˣ} (hu : u ∈ localUnitsOne p n) :
    u ∈ localUnitsOnePlus p n
      ↔ (galAut p (-1) n ⟨(u : ℂ_[p]), (Subring.mem_inf.1 hu.1.1).1⟩ : ℂ_[p]) = (u : ℂ_[p]) := by
  have hxK : (u : ℂ_[p]) ∈ K p n := (Subring.mem_inf.1 hu.1.1).1
  rw [localUnitsOnePlus, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hplus⟩
    have hmem : (u : ℂ_[p]) ∈ KPlus p n := hplus.2
    exact (mem_KPlus_iff_galAut_neg_one_fixed p hp2 hn hxK).1 hmem
  · intro hfix
    refine ⟨hu, hu.1, (mem_KPlus_iff_galAut_neg_one_fixed p hp2 hn hxK).2 hfix⟩

/-- Tower compatibility: `σ_a` at level `n+1` restricts to `σ_a` at level `n`
(uniqueness of the automorphism realising the character value). -/
theorem galAut_compat (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p n) :
    (galAut p a (n + 1) ⟨x, (K_le_succ p n) hx⟩ : ℂ_[p])
      = (galAut p a n ⟨x, hx⟩ : ℂ_[p]) := by
  set incl : (K p n) →ₐ[ℚ_[p]] (K p (n + 1)) := IntermediateField.inclusion (K_le_succ p n)
    with hincl
  set F1 : (K p n) →ₐ[ℚ_[p]] ℂ_[p] :=
    ((K p (n + 1)).val).comp ((galAut p a (n + 1)).toAlgHom.comp incl) with hF1
  set F2 : (K p n) →ₐ[ℚ_[p]] ℂ_[p] := ((K p n).val).comp (galAut p a n).toAlgHom with hF2
  set ζξ : K p n := ⟨zetaSys p n, zetaSys_mem_K p n⟩ with hζξ
  have hagree : F1 ζξ = F2 ζξ := by
    have hF2val : F2 ζξ = zetaSys p n ^
        ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val := by
      rw [hF2]; change (galAut p a n ζξ : ℂ_[p]) = _; rw [galAut_zetaSys p a hn]
    have hF1val : F1 ζξ = (zetaSys p (n + 1) ^
        ((PadicMeasure.unitsToZModPow p (n + 1) a : (ZMod (p ^ (n + 1)))ˣ) :
          ZMod (p ^ (n + 1))).val) ^ p := by
      rw [hF1]
      change ((galAut p a (n + 1)) (incl ζξ) : ℂ_[p]) = _
      have hinclζ : incl ζξ = ⟨zetaSys p (n + 1) ^ p,
          (K_le_succ p n) (by rw [zetaSys_pow_p]; exact zetaSys_mem_K p n)⟩ := by
        apply Subtype.ext
        rw [hincl]; change zetaSys p n = (zetaSys p (n + 1)) ^ p
        rw [zetaSys_pow_p]
      rw [hinclζ]
      rw [show (⟨zetaSys p (n + 1) ^ p, _⟩ : K p (n + 1))
          = (⟨zetaSys p (n + 1), zetaSys_mem_K p (n + 1)⟩ : K p (n + 1)) ^ p from by
            apply Subtype.ext; rfl, map_pow]
      rw [show ((galAut p a (n + 1)) (⟨zetaSys p (n + 1), zetaSys_mem_K p (n + 1)⟩) ^ p : K p (n+1))
          = ((galAut p a (n + 1)) (⟨zetaSys p (n + 1), zetaSys_mem_K p (n + 1)⟩)) ^ p from rfl]
      rw [SubmonoidClass.coe_pow]
      congr 1
      exact galAut_zetaSys p a (by omega)
    rw [hF1val, hF2val, ← pow_mul]
    rw [show (zetaSys p (n + 1) ^
        (((PadicMeasure.unitsToZModPow p (n + 1) a : (ZMod (p ^ (n + 1)))ˣ) :
          ZMod (p ^ (n + 1))).val * p))
        = (zetaSys p (n + 1) ^ p) ^
          ((PadicMeasure.unitsToZModPow p (n + 1) a : (ZMod (p ^ (n + 1)))ˣ) :
            ZMod (p ^ (n + 1))).val from by rw [← pow_mul, mul_comm], zetaSys_pow_p]
    have hred : (PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ)
        = ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n))
          (PadicMeasure.unitsToZModPow p (n + 1) a) :=
      PadicMeasure.unitsToZModPow_le p (Nat.le_succ n) a
    have hmod : ((PadicMeasure.unitsToZModPow p (n + 1) a : (ZMod (p ^ (n + 1)))ˣ) :
          ZMod (p ^ (n + 1))).val
        ≡ ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val
          [MOD p ^ n] := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, hred, ZMod.unitsMap_val,
        ZMod.natCast_val]
    exact zetaSys_pow_eq_pow_of_modEq p hmod
  have hFeq : F1 = F2 :=
    AlgHom.ext_of_adjoin_eq_top (adjoin_zetaSysK_eq_top p n)
      (by rintro y (rfl : y = ζξ); exact hagree)
  have hev := congrFun (congrArg (fun (F : (K p n) →ₐ[ℚ_[p]] ℂ_[p]) => (F : K p n → ℂ_[p]))
    hFeq) ⟨x, hx⟩
  rw [hF1, hF2] at hev
  exact hev

/-- `σ_a^{(n+1)}` as a ring automorphism of the `K_n`-algebra `extendScalars (K_n ≤ K_{n+1})`
(same carrier as `K_{n+1}`). This is `(galAut p a n)`-semilinear over `K_n`
(`galAut_compat`); packaged as a plain `RingEquiv` for the norm-conjugation. -/
private def galAutES (a : ℤ_[p]ˣ) {n : ℕ} (_hn : 1 ≤ n) :
    IntermediateField.extendScalars (K_le_succ p n)
      ≃+* IntermediateField.extendScalars (K_le_succ p n) :=
  (galAut p a (n + 1)).toRingEquiv

@[simp]
private theorem galAutES_apply (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n)
    (y : IntermediateField.extendScalars (K_le_succ p n)) :
    ((galAutES p a hn y : IntermediateField.extendScalars (K_le_succ p n)) : ℂ_[p])
      = (galAut p a (n + 1) ⟨(y : ℂ_[p]), y.2⟩ : ℂ_[p]) := rfl

/-- The relative norm is Galois-equivariant: `N_{n+1,n} ∘ σ_a = σ_a ∘ N_{n+1,n}`
(conjugation-invariance of `Algebra.norm`, RJW TeX 3199). Proof: `σ_a^{(n+1)}` is a
ring automorphism of `K_{n+1}` that restricts to `σ_a^{(n)}` on `K_n` (`galAut_compat`),
so it is `σ_a^{(n)}`-semilinear over `K_n`; `Algebra.norm_eq_of_ringEquiv` (with the base
twisted by `σ_a^{(n)}`) then gives `σ_a^{(n)}(N(x)) = N(σ_a^{(n+1)}(x))`. -/
theorem levelNorm_galAut (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]}
    (hx : x ∈ K p (n + 1)) :
    levelNorm p n (galAut p a (n + 1) ⟨x, hx⟩ : ℂ_[p])
      = (galAut p a n ⟨levelNorm p n x, levelNorm_mem p n hx⟩ : ℂ_[p]) := by
  set xes : IntermediateField.extendScalars (K_le_succ p n) :=
    ⟨x, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hx⟩ with hxes
  set e : (K p n) ≃+* (K p n) := (galAut p a n).toRingEquiv with he
  have hcompat : ∀ c : K p n,
      (galAutES p a hn) (algebraMap (K p n)
          (IntermediateField.extendScalars (K_le_succ p n)) c)
        = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) (e c) := by
    intro c
    apply Subtype.ext
    rw [galAutES_apply]
    change (galAut p a (n + 1) ⟨(c : ℂ_[p]), _⟩ : ℂ_[p]) = (e c : ℂ_[p])
    rw [he]
    change (galAut p a (n + 1) ⟨(c : ℂ_[p]), (K_le_succ p n) c.2⟩ : ℂ_[p])
      = (galAut p a n ⟨(c : ℂ_[p]), c.2⟩ : ℂ_[p])
    exact galAut_compat p a hn c.2
  have he' : (algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n))).comp
        (e : (K p n) →+* (K p n))
      = (galAutES p a hn : IntermediateField.extendScalars (K_le_succ p n) →+*
          IntermediateField.extendScalars (K_le_succ p n)).comp
        (algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n))) := by
    refine RingHom.ext fun c => ?_
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    exact (hcompat c).symm
  have hkey := Algebra.norm_eq_of_equiv_equiv e (galAutES p a hn) he' xes
  have hkey2 : e (Algebra.norm (K p n) xes)
      = Algebra.norm (K p n) (galAutES p a hn xes) := by
    rw [hkey, RingEquiv.apply_symm_apply]
  have hgalmem : (galAut p a (n + 1) ⟨x, hx⟩ : ℂ_[p]) ∈ K p (n + 1) :=
    (galAut p a (n + 1) ⟨x, hx⟩).2
  have hlhs : levelNorm p n (galAut p a (n + 1) ⟨x, hx⟩ : ℂ_[p])
      = (Algebra.norm (K p n) (galAutES p a hn xes) : K p n) := by
    rw [levelNorm_apply p n hgalmem]
    congr 1
  have hrhsK : (⟨levelNorm p n x, levelNorm_mem p n hx⟩ : K p n)
      = Algebra.norm (K p n) xes := by
    apply Subtype.ext; exact levelNorm_apply p n hx
  rw [hlhs, ← hkey2, he]
  -- both sides are `galAut p a n` applied to the same `K_n`-element `norm xes`
  change (galAut p a n (Algebra.norm (K p n) xes) : ℂ_[p])
    = (galAut p a n ⟨levelNorm p n x, levelNorm_mem p n hx⟩ : ℂ_[p])
  rw [hrhsK]

/-- The restriction of the `ℂ_p`-norm to `K_n`, as an `AbsoluteValue (K p n) ℝ`
(mirrors `Tower.restrictAbs`, which is private). -/
private noncomputable def restrictAbsK (n : ℕ) : AbsoluteValue (K p n) ℝ where
  toFun y := ‖(y : ℂ_[p])‖
  map_mul' x y := by push_cast; rw [norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    rw [norm_eq_zero]
    exact ⟨fun h => by exact_mod_cast h, fun h => by rw [h]; rfl⟩
  add_le' x y := by push_cast; exact norm_add_le _ _

/-- The `ℂ_p`-norm of `y ∈ K_n` is its `ℚ_p`-spectral norm. -/
private theorem norm_coe_eq_spectralNorm {n : ℕ} (y : K p n) :
    ‖(y : ℂ_[p])‖ = spectralNorm ℚ_[p] (K p n) y := by
  haveI : FiniteDimensional ℚ_[p] (K p n) := Module.finite_of_finrank_pos (R := ℚ_[p])
    (by rw [finrank_K]; exact Nat.totient_pos.2 (pow_pos hp.out.pos n))
  refine spectralNorm_unique_field_norm_ext (K := ℚ_[p]) (L := K p n)
    (f := restrictAbsK p n) (fun k => ?_) y
  change ‖((algebraMap ℚ_[p] (K p n) k : K p n) : ℂ_[p])‖ = ‖k‖
  rw [show ((algebraMap ℚ_[p] (K p n) k : K p n) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] k from by
    rw [← IntermediateField.algebraMap_apply]; rfl]
  simp

/-- **`σ_a` is an isometry on `K_n`** (RJW TeX 3199, used for `O_n`-preservation):
`‖σ_a y‖ = ‖y‖`. The `ℂ_p`-norm restricted to `K_n` is the spectral norm
(`norm_coe_eq_spectralNorm`), which depends only on the minimal polynomial, preserved
by the automorphism (`minpoly.algEquiv_eq`). -/
theorem norm_galAut (a : ℤ_[p]ˣ) {n : ℕ} (y : K p n) :
    ‖(galAut p a n y : ℂ_[p])‖ = ‖(y : ℂ_[p])‖ := by
  rw [norm_coe_eq_spectralNorm p (galAut p a n y), norm_coe_eq_spectralNorm p y,
    spectralNorm, spectralNorm, minpoly.algEquiv_eq (galAut p a n) y]

/-- `σ_a` preserves `O_n`: if `(y : ℂ_p) ∈ O_n` then so is `σ_a y` (norm preserved,
`K_n`-membership automatic). -/
theorem galAut_mem_O (a : ℤ_[p]ˣ) {n : ℕ} {y : ℂ_[p]} (hy : y ∈ O p n) :
    (galAut p a n ⟨y, (Subring.mem_inf.1 hy).1⟩ : ℂ_[p]) ∈ O p n := by
  rw [O, Subring.mem_inf]
  refine ⟨(galAut p a n ⟨y, (Subring.mem_inf.1 hy).1⟩).2, ?_⟩
  change ‖(galAut p a n ⟨y, (Subring.mem_inf.1 hy).1⟩ : ℂ_[p])‖ ≤ 1
  rw [norm_galAut p a ⟨y, (Subring.mem_inf.1 hy).1⟩]
  exact (Subring.mem_inf.1 hy).2

/-- The `K_n`-element `⟨v, hv⟩` of a unit `v` of `ℂ_p` lying in `K_n` is a unit of `K_n`. -/
private theorem isUnit_mkK {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) :
    IsUnit (⟨(v : ℂ_[p]), hv⟩ : K p n) :=
  isUnit_iff_ne_zero.2 (fun h => v.ne_zero (by simpa using congrArg (Subtype.val) h))

/-- The unit `σ_a u_n` of `K_n` from a unit `u_n` whose value lies in `K_n`:
`galAut` is a ring auto, so it maps the `K_n`-unit `⟨u_n, _⟩` to a unit, embedded back into
`ℂ_[p]ˣ` via `K_n ↪ ℂ_p`. -/
noncomputable def galAutUnit (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ)
    (hv : (v : ℂ_[p]) ∈ K p n) : ℂ_[p]ˣ :=
  Units.map ((K p n).val.toMonoidHom.comp (galAut p a n).toAlgHom.toMonoidHom)
    (isUnit_mkK p v hv).unit

@[simp]
theorem galAutUnit_val (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) :
    ((galAutUnit p a v hv : ℂ_[p]ˣ) : ℂ_[p]) = (galAut p a n ⟨(v : ℂ_[p]), hv⟩ : ℂ_[p]) := by
  rw [galAutUnit]
  change ((K p n).val ((galAut p a n) ((isUnit_mkK p v hv).unit : K p n)) : ℂ_[p]) = _
  rw [IsUnit.unit_spec]; rfl

@[simp]
theorem galAutUnit_inv_val (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ)
    (hv : (v : ℂ_[p]) ∈ K p n) :
    (((galAutUnit p a v hv)⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
      = (galAut p a n ⟨((v : ℂ_[p]))⁻¹, (K p n).inv_mem hv⟩ : ℂ_[p]) := by
  rw [Units.val_inv_eq_inv_val, galAutUnit_val]
  have hinvK : (⟨(v : ℂ_[p]), hv⟩ : K p n)⁻¹ = ⟨((v : ℂ_[p]))⁻¹, (K p n).inv_mem hv⟩ :=
    Subtype.ext (by rw [IntermediateField.coe_inv])
  rw [show (galAut p a n ⟨((v : ℂ_[p]))⁻¹, (K p n).inv_mem hv⟩ : ℂ_[p])
      = (galAut p a n (⟨(v : ℂ_[p]), hv⟩ : K p n)⁻¹ : ℂ_[p]) from by rw [hinvK]]
  rw [map_inv₀, IntermediateField.coe_inv]

@[simp]
theorem galAutUnit_inv_val' (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ)
    (hv : (v : ℂ_[p]) ∈ K p n) :
    (((galAutUnit p a v hv : ℂ_[p]ˣ) : ℂ_[p]))⁻¹
      = (galAut p a n ⟨((v : ℂ_[p]))⁻¹, (K p n).inv_mem hv⟩ : ℂ_[p]) := by
  rw [← Units.val_inv_eq_inv_val, galAutUnit_inv_val]

/-- The `𝒢`-action `σ_a` on the norm-compatible unit tower `𝒰_∞` (RJW TeX 3201–3204):
levelwise application of `galAut`, well-defined by `galAut_compat` + `levelNorm_galAut`.
Each level: `(σ_a u)_n` is `σ_a` applied to `u_n` (a ring auto preserving `O_n`, an isometry);
the inverse stays in `O_n` likewise, and norm-compatibility is `levelNorm_galAut` + `u.compat`. -/
def galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : NormCompatUnits p where
  elems n := galAutUnit p a (u.elems n) (Subring.mem_inf.1 (u.mem n)).1
  mem n := by
    rw [galAutUnit_val]
    exact galAut_mem_O p a (u.mem n)
  inv_mem n := by
    rw [galAutUnit_inv_val']
    have h := galAut_mem_O p a (u.inv_mem n)
    simpa only [Units.val_inv_eq_inv_val] using h
  compat n hn := by
    have hxK : (u.elems (n + 1) : ℂ_[p]) ∈ K p (n + 1) := (Subring.mem_inf.1 (u.mem _)).1
    change levelNorm p n ((galAutUnit p a (u.elems (n + 1)) hxK : ℂ_[p]ˣ) : ℂ_[p])
      = ((galAutUnit p a (u.elems n) (Subring.mem_inf.1 (u.mem n)).1 : ℂ_[p]ˣ) : ℂ_[p])
    rw [galAutUnit_val, galAutUnit_val, levelNorm_galAut p a hn hxK]
    congr 2
    exact Subtype.ext (u.compat n hn)

/-- The substituend `(1+T)^a − 1 ∈ ℤ_[p]⟦T⟧` for `a : ℤ_[p]ˣ`: mathlib's
`binomialSeries ℤ_[p] (a : ℤ_[p])` (the formal `(1+T)^a`) minus `1`. Its constant
coefficient is `0`, so it is a valid substituend (RJW TeX 3206). -/
noncomputable def galSubstend (a : ℤ_[p]ˣ) : PowerSeries ℤ_[p] :=
  PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p]) - 1

@[simp]
theorem constantCoeff_galSubstend (a : ℤ_[p]ˣ) :
    PowerSeries.constantCoeff (galSubstend p a) = 0 := by
  rw [galSubstend, map_sub, PowerSeries.binomialSeries_constantCoeff, map_one, sub_self]

theorem hasSubst_galSubstend (a : ℤ_[p]ˣ) : PowerSeries.HasSubst (galSubstend p a) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_galSubstend p a)

/-- `σ_a` on power series: `f ↦ f((1+T)^a − 1)` (RJW TeX 3206), realised as the
`PowerSeries.subst` of the binomial substituend `galSubstend a = (1+T)^a − 1`. -/
noncomputable def galSeries (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  f.subst (galSubstend p a)

/-- `‖coeff k (G^d)‖ ≤ 1` for an integral-coefficient series `G` (ultrametric Cauchy
product; re-derivation of `ResidueZeta.norm_coeff_pow_le_one`). -/
private theorem norm_coeff_pow_le_one' {G : PowerSeries ℂ_[p]}
    (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1) (d k : ℕ) :
    ‖PowerSeries.coeff k (G ^ d)‖ ≤ 1 := by
  induction d generalizing k with
  | zero => rw [pow_zero, PowerSeries.coeff_one]; split <;> simp [zero_le_one]
  | succ m ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_
    rw [norm_mul]; exact mul_le_one₀ (ih _) (norm_nonneg _) (hG _)

/-- `seriesEval (G ^ d) z = (seriesEval G z) ^ d` for integral `G`, `‖z‖ < 1`
(`seriesEval_mul` induction; re-derivation of the private `ResidueZeta.seriesEval_pow`). -/
private theorem seriesEval_pow_of_integral {G : PowerSeries ℂ_[p]}
    (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1) {z : ℂ_[p]} (hz : ‖z‖ < 1) (d : ℕ) :
    seriesEval (G ^ d) z = (seriesEval G z) ^ d := by
  induction d with
  | zero => rw [pow_zero, pow_zero, show (1 : PowerSeries ℂ_[p]) = PowerSeries.C 1 from
      (map_one _).symm, seriesEval_C]
  | succ e ih =>
    rw [pow_succ, pow_succ,
      seriesEval_mul (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_pow_le_one' p hG e) hz)
        (summable_seriesEval_of_norm_coeff_le_one hG hz), ih]

/-- `coeff k (G^n) = 0` for `k < n` when `constantCoeff G = 0` (so `X^n ∣ G^n`). -/
private theorem coeff_pow_eq_zero_of_lt {G : PowerSeries ℂ_[p]}
    (hG0 : PowerSeries.constantCoeff G = 0) {k n : ℕ} (hkn : k < n) :
    PowerSeries.coeff k (G ^ n) = 0 :=
  PowerSeries.X_pow_dvd_iff.1
    (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hG0) n) k hkn

/-- `‖seriesEval G z‖ ≤ ‖z‖ < 1` when `constantCoeff G = 0` and `G` is integral
(each term `‖coeff_k G · z^k‖ ≤ ‖z‖^k ≤ ‖z‖` for `k ≥ 1`, the `k = 0` term vanishes). -/
private theorem norm_seriesEval_lt {G : PowerSeries ℂ_[p]}
    (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1) (hG0 : PowerSeries.constantCoeff G = 0)
    {z : ℂ_[p]} (hz : ‖z‖ < 1) : ‖seriesEval G z‖ < 1 := by
  refine lt_of_le_of_lt ?_ hz
  rw [seriesEval]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
  cases k with
  | zero =>
    rw [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0, norm_zero]
    exact norm_nonneg _
  | succ m =>
    rw [norm_mul, norm_pow, pow_succ]
    calc ‖PowerSeries.coeff (m + 1) G‖ * (‖z‖ ^ m * ‖z‖)
        ≤ 1 * (1 * ‖z‖) :=
          mul_le_mul (hG _) (mul_le_mul (pow_le_one₀ (norm_nonneg _) hz.le) le_rfl
            (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
      _ = ‖z‖ := by ring

/-- **The subst-evaluation bridge** (RJW TeX 3206, generalising `evalPi_phi`): for an
integral-coefficient substituend `G` over `ℂ_[p]` with `constantCoeff G = 0`,
`seriesEval (f.subst G) z = seriesEval f (seriesEval G z)` at `‖z‖ < 1`. The inner-sum
identity uses `seriesEval_pow_of_integral` (no polynomiality needed, unlike the φ-case). -/
private theorem seriesEval_subst {f G : PowerSeries ℂ_[p]}
    (hf : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1)
    (hG0 : PowerSeries.constantCoeff G = 0) {z : ℂ_[p]} (hz : ‖z‖ < 1) :
    seriesEval (f.subst G) z = seriesEval f (seriesEval G z) := by
  have hS : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  have hw : ‖seriesEval G z‖ < 1 := norm_seriesEval_lt p hG hG0 hz
  let T : ℕ → ℕ → ℂ_[p] := fun n k =>
    PowerSeries.coeff n f * PowerSeries.coeff k (G ^ n) * z ^ k
  have hTbd : ∀ n k, ‖T n k‖ ≤ ‖z‖ ^ k := by
    intro n k
    rw [show T n k = PowerSeries.coeff n f * PowerSeries.coeff k (G ^ n) * z ^ k from rfl,
      norm_mul, norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n f‖ * ‖PowerSeries.coeff k (G ^ n)‖ * ‖z‖ ^ k
        ≤ 1 * 1 * ‖z‖ ^ k :=
          mul_le_mul (mul_le_mul (hf n) (norm_coeff_pow_le_one' p hG n k) (norm_nonneg _)
            zero_le_one) le_rfl (by positivity) (by positivity)
      _ = ‖z‖ ^ k := by ring
  have hprod : Summable (Function.uncurry T) := by
    rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
      NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    rw [Filter.eventually_cofinite]
    have htend0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz)
    obtain ⟨N, hN⟩ := (htend0.eventually_lt_const hε).exists_forall_of_atTop
    refine Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (N + 1)) (Set.finite_Iio (N + 1)))
      fun nk hnk => ?_
    simp only [Set.mem_setOf_eq, not_lt, Function.uncurry] at hnk
    by_cases hnk1 : nk.2 < nk.1
    · exfalso
      have hT0 : T nk.1 nk.2 = 0 := by
        rw [show T nk.1 nk.2 = PowerSeries.coeff nk.1 f * PowerSeries.coeff nk.2 (G ^ nk.1)
            * z ^ nk.2 from rfl, coeff_pow_eq_zero_of_lt p hG0 hnk1, mul_zero, zero_mul]
      rw [hT0, norm_zero] at hnk
      exact absurd (lt_of_lt_of_le hε hnk) (lt_irrefl _)
    rw [not_lt] at hnk1
    have hk : nk.2 < N + 1 := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd (lt_of_le_of_lt (le_trans hnk (hTbd nk.1 nk.2)) (hN nk.2 (by omega)))
        (lt_irrefl ε)
    exact Set.mem_prod.2 ⟨lt_of_le_of_lt hnk1 hk, hk⟩
  have hLHScoeff : ∀ k : ℕ,
      PowerSeries.coeff k (f.subst G) * z ^ k = ∑' n : ℕ, T n k := by
    intro k
    rw [PowerSeries.coeff_subst' hS,
      finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (k + 1)) (by
        intro n hn
        simp only [Function.mem_support] at hn
        by_contra hmem
        simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
        exact hn (by rw [coeff_pow_eq_zero_of_lt p hG0 (by omega), smul_zero]))]
    rw [Finset.sum_mul, tsum_eq_sum (s := Finset.range (k + 1)) fun n hn => by
      change PowerSeries.coeff n f * PowerSeries.coeff k (G ^ n) * z ^ k = 0
      rw [coeff_pow_eq_zero_of_lt p hG0
        (show k < n by simp only [Finset.mem_range, not_lt] at hn; omega), mul_zero, zero_mul]]
    refine Finset.sum_congr rfl fun n _ => ?_
    change PowerSeries.coeff n f • _ * z ^ k = _
    rw [smul_eq_mul]
  rw [seriesEval]
  simp_rw [hLHScoeff]
  rw [Summable.tsum_comm hprod, seriesEval]
  refine tsum_congr fun n => ?_
  rw [show (fun k : ℕ => T n k)
      = fun k : ℕ => PowerSeries.coeff n f * (PowerSeries.coeff k (G ^ n) * z ^ k) from by
    funext k; rw [show T n k = _ from rfl]; ring,
    (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_pow_le_one' p hG n) hz).tsum_mul_left,
    ← seriesEval, seriesEval_pow_of_integral p hG hz]

/-- The coefficient inclusion `toCp : ℤ_[p] → ℂ_[p]` is continuous (`ℤ_[p] ↪ ℚ_[p] ↪ ℂ_[p]`). -/
private theorem continuous_toCp : Continuous (toCp p) := by
  rw [toCp]
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

/-- `c ↦ zpPow p y c` is continuous in the exponent for a `1`-unit `y` (it is the
continuous additive character `addChar_of_value_at_one`). Re-derivation of the private
`LocalUnits.continuous_zpPow`. -/
private theorem continuous_zpPow_aux {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) :
    Continuous (zpPow p y) := by
  have h : zpPow p y = (PadicInt.addChar_of_value_at_one (y - 1)
      (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hy) : ℤ_[p] → ℂ_[p]) := by
    funext a
    rw [zpPow, dif_pos (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hy)]
  rw [h]
  exact PadicInt.continuous_addChar_of_value_at_one _

/-- The pushed-forward binomial coefficients are integral: `‖coeff k (map toCp (binomial c))‖
≤ 1` (`Ring.choose c k ∈ ℤ_[p]`, `toCp` isometric). -/
private theorem norm_coeff_map_binomialSeries_le_one (c : ℤ_[p]) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.map (toCp p) (PowerSeries.binomialSeries ℤ_[p] c))‖ ≤ 1 := by
  rw [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, norm_toCp]
  exact PadicInt.norm_le_one _

open scoped Topology in
/-- **`seriesEval` of the binomial series is `zpPow`** (the analytic `(1+z)^c = Σ (c k) z^k`):
for `‖z‖ < 1`, `(binomialSeries c)(z) = zpPow (1+z) c`. Both sides are continuous in `c : ℤ_[p]`
(uniform `‖·‖ ≤ ‖z‖^k` bound for LHS; `continuous_zpPow`-analogue for `zpPow`) and agree on
`c ∈ ℕ` (`binomialSeries_nat`/`seriesEval_one_add_X_pow` vs `zpPow_natCast`); ℕ is dense. -/
theorem seriesEval_map_binomialSeries (c : ℤ_[p]) {z : ℂ_[p]} (hz : ‖z‖ < 1) :
    seriesEval (PowerSeries.map (toCp p) (PowerSeries.binomialSeries ℤ_[p] c)) z
      = zpPow p (1 + z) c := by
  have hz1 : ‖(1 + z) - 1‖ < 1 := by rwa [add_sub_cancel_left]
  have hcontL : Continuous fun c : ℤ_[p] =>
      seriesEval (PowerSeries.map (toCp p) (PowerSeries.binomialSeries ℤ_[p] c)) z := by
    simp only [seriesEval, PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, smul_eq_mul,
      mul_one]
    refine continuous_tsum (u := fun k => ‖z‖ ^ k) (fun k => ?_) (summable_geometric_of_lt_one
      (norm_nonneg _) hz) (fun k c => ?_)
    · exact ((continuous_toCp p).comp (PadicInt.continuous_choose k)).mul continuous_const
    · rw [norm_mul, norm_pow, norm_toCp]
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one _)
  have hnat : ∀ k : ℕ,
      seriesEval (PowerSeries.map (toCp p) (PowerSeries.binomialSeries ℤ_[p] (k : ℤ_[p]))) z
        = zpPow p (1 + z) (k : ℤ_[p]) := by
    intro k
    rw [PowerSeries.binomialSeries_nat, zpPow_natCast p hz1,
      show PowerSeries.map (toCp p) ((1 + PowerSeries.X) ^ k : PowerSeries ℤ_[p])
        = ((1 + PowerSeries.X) ^ k : PowerSeries ℂ_[p]) from by
      simp only [map_pow, map_add, map_one, PowerSeries.map_X],
      seriesEval_one_add_X_pow]
  have heq := PadicInt.denseRange_natCast.equalizer hcontL (continuous_zpPow_aux p hz1)
    (funext hnat)
  exact congrFun heq c

open scoped Topology in
/-- **`zpPow` on a root of unity is the cyclotomic power** (the `p^n`-periodicity of
`ξ_n^·`): for `n ≥ 1` and `c : ℤ_[p]`, `zpPow ξ_n c = ξ_n^{(toZModPow n c).val}`. Both sides
are continuous in `c` and agree on `c ∈ ℕ` (`zpPow_natCast` vs `ξ_n^{k mod p^n} = ξ_n^k`). -/
private theorem zpPow_zetaSys {n : ℕ} (hn : 1 ≤ n) (c : ℤ_[p]) :
    zpPow p (zetaSys p n) c
      = zetaSys p n ^ ((PadicInt.toZModPow n c : ZMod (p ^ n)).val) := by
  have hz1 : ‖zetaSys p n - 1‖ < 1 := by
    have := norm_pi_lt_one p hn; rwa [pi] at this
  have hcontR : Continuous fun c : ℤ_[p] =>
      zetaSys p n ^ ((PadicInt.toZModPow n c : ZMod (p ^ n)).val) := by
    have hlcZ : IsLocallyConstant fun c : ℤ_[p] => (PadicInt.toZModPow n c : ZMod (p ^ n)) :=
      fun s => by
        rw [← Set.biUnion_preimage_singleton]
        exact isOpen_biUnion fun a _ => PadicMeasure.isOpen_toZModPow_fiber p n a
    exact ((hlcZ.comp ZMod.val).comp fun k => zetaSys p n ^ k).continuous
  have hnat : ∀ k : ℕ, zpPow p (zetaSys p n) (k : ℤ_[p])
      = zetaSys p n ^ ((PadicInt.toZModPow n (k : ℤ_[p]) : ZMod (p ^ n)).val) := by
    intro k
    rw [zpPow_natCast p hz1]
    refine zetaSys_pow_eq_pow_of_modEq p ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, map_natCast]
  have heq := PadicInt.denseRange_natCast.equalizer (continuous_zpPow_aux p hz1) hcontR
    (funext hnat)
  exact congrFun heq c

/-- The substituend evaluates to `σ_a(π_n)`: `(galSubstend a)(π_n) = ξ_n^{a mod p^n} − 1`,
which is `σ_a(ξ_n) − 1 = σ_a(π_n)` (`galAut_zetaSys`). Combines `seriesEval_map_binomialSeries`
+ `zpPow_zetaSys` + `unitsToZModPow_coe`. -/
private theorem seriesEval_map_galSubstend (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) :
    seriesEval (PowerSeries.map (toCp p) (galSubstend p a)) (pi p n)
      = zetaSys p n ^ ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) :
          ZMod (p ^ n)).val - 1 := by
  have hz : ‖pi p n‖ < 1 := norm_pi_lt_one p hn
  rw [galSubstend, map_sub, map_one]
  rw [seriesEval_sub (z := pi p n)
    (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_map_binomialSeries_le_one p _) hz)
    (summable_seriesEval_of_norm_coeff_le_one
      (fun k => by rw [show (1 : PowerSeries ℂ_[p]) = PowerSeries.C 1 from (map_one _).symm,
        PowerSeries.coeff_C]; split <;> simp [zero_le_one]) hz)]
  rw [show (1 : PowerSeries ℂ_[p]) = PowerSeries.C (1 : ℂ_[p]) from (map_one _).symm, seriesEval_C]
  congr 1
  rw [seriesEval_map_binomialSeries p (a : ℤ_[p]) hz,
    show (1 : ℂ_[p]) + pi p n = zetaSys p n from by rw [pi]; ring, zpPow_zetaSys p hn]
  rw [PadicMeasure.unitsToZModPow_coe]

/-- `σ_a` (continuous on `K_n`) commutes with the evaluation series of an integral
`ℂ_[p]`-coefficient series `H` at `π_n`: `σ_a(seriesEval H π_n) = seriesEval H (σ_a π_n)`,
where `H` has `ℚ_p`-coefficients (so `σ_a` fixes them) — here `H = map toCp f`. Realised
through the `K_n`-subtype continuity of `galAut` and `map of convergent series`. -/
private theorem galAut_evalPi (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    (galAut p a n ⟨evalPi p f n, (Subring.mem_inf.1 (evalPi_mem_O p f hn)).1⟩ : ℂ_[p])
      = seriesEval (PowerSeries.map (toCp p) f)
          (zetaSys p n ^ ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) :
            ZMod (p ^ n)).val - 1) := by
  haveI : FiniteDimensional ℚ_[p] (K p n) := Module.finite_of_finrank_pos (R := ℚ_[p])
    (by rw [finrank_K]; exact Nat.totient_pos.2 (pow_pos hp.out.pos n))
  set t : ℕ := ((PadicMeasure.unitsToZModPow p n a : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val with ht
  have hσπ : (galAut p a n ⟨pi p n, pi_mem_K p n⟩ : ℂ_[p]) = zetaSys p n ^ t - 1 := by
    have hζ := galAut_zetaSys p a hn
    have hsub : (⟨pi p n, pi_mem_K p n⟩ : K p n)
        = ⟨zetaSys p n, zetaSys_mem_K p n⟩ - 1 := by
      apply Subtype.ext; change pi p n = zetaSys p n - 1; rw [pi]
    rw [hsub, map_sub, map_one]
    change (galAut p a n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]) - 1 = _
    rw [hζ]
  set c : ℕ → ℂ_[p] := fun k => PowerSeries.coeff k (PowerSeries.map (toCp p) f) with hc
  have hcK : ∀ k, c k ∈ K p n := fun k => by
    change PowerSeries.coeff k (PowerSeries.map (toCp p) f) ∈ K p n
    rw [PowerSeries.coeff_map, toCp, RingHom.comp_apply]
    exact IntermediateField.algebraMap_mem (K p n) _
  have hgalc : ∀ k, (galAut p a n ⟨c k, hcK k⟩ : ℂ_[p]) = c k := by
    intro k
    obtain ⟨q, hq⟩ : ∃ q : ℚ_[p], algebraMap ℚ_[p] ℂ_[p] q = c k := by
      refine ⟨PadicInt.Coe.ringHom (PowerSeries.coeff k f), ?_⟩
      change algebraMap ℚ_[p] ℂ_[p] _ = PowerSeries.coeff k (PowerSeries.map (toCp p) f)
      rw [PowerSeries.coeff_map, toCp, RingHom.comp_apply]
    have hmk : (⟨c k, hcK k⟩ : K p n) = algebraMap ℚ_[p] (K p n) q := by
      apply Subtype.ext
      change c k = ((algebraMap ℚ_[p] (K p n) q : K p n) : ℂ_[p])
      rw [IntermediateField.coe_algebraMap_apply, hq]
    rw [hmk, AlgEquiv.commutes, IntermediateField.coe_algebraMap_apply, hq]
  set S : ℕ → K p n := fun m => ∑ k ∈ Finset.range m,
    ⟨c k, hcK k⟩ * ⟨pi p n, pi_mem_K p n⟩ ^ k with hS
  have hScoe : ∀ m, ((S m : K p n) : ℂ_[p]) = ∑ k ∈ Finset.range m, c k * pi p n ^ k := by
    intro m; rw [hS]; push_cast; rfl
  have hevalC : evalPi p f n = ∑' k, c k * pi p n ^ k := rfl
  have htendC : Filter.Tendsto (fun m => ∑ k ∈ Finset.range m, c k * pi p n ^ k)
      Filter.atTop (nhds (evalPi p f n)) := by
    rw [hevalC]
    exact (summable_evalPi p f hn).hasSum.tendsto_sum_nat
  have htendK : Filter.Tendsto S Filter.atTop
      (nhds (⟨evalPi p f n, (Subring.mem_inf.1 (evalPi_mem_O p f hn)).1⟩ : K p n)) := by
    rw [tendsto_subtype_rng]
    refine htendC.congr (fun m => (hScoe m).symm)
  have hcont : Continuous (galAut p a n) :=
    (galAut p a n).toLinearMap.continuous_of_finiteDimensional
  have htendGal : Filter.Tendsto (fun m => galAut p a n (S m)) Filter.atTop
      (nhds (galAut p a n ⟨evalPi p f n, (Subring.mem_inf.1 (evalPi_mem_O p f hn)).1⟩)) :=
    (hcont.tendsto _).comp htendK
  have htendGalC : Filter.Tendsto (fun m => (galAut p a n (S m) : ℂ_[p])) Filter.atTop
      (nhds (galAut p a n ⟨evalPi p f n, (Subring.mem_inf.1 (evalPi_mem_O p f hn)).1⟩ : ℂ_[p])) :=
    (continuous_subtype_val.tendsto _).comp htendGal
  have hgalS : ∀ m, (galAut p a n (S m) : ℂ_[p])
      = ∑ k ∈ Finset.range m, c k * (zetaSys p n ^ t - 1) ^ k := by
    intro m
    rw [hS, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, IntermediateField.coe_mul, IntermediateField.coe_pow, hgalc k,
      show (galAut p a n ⟨pi p n, pi_mem_K p n⟩ : ℂ_[p]) = zetaSys p n ^ t - 1 from hσπ]
  have hzt : ‖zetaSys p n ^ t - 1‖ < 1 := by
    have hξ1 : ‖zetaSys p n‖ = 1 := by
      have h1 : ‖zetaSys p n‖ ^ (p ^ n) = 1 := by
        rw [← norm_pow, (zetaSys_primitiveRoot p n).pow_eq_one, norm_one]
      have hne : p ^ n ≠ 0 := (pow_pos hp.out.pos n).ne'
      refine le_antisymm ?_ ?_
      · by_contra h; rw [not_le] at h; exact absurd h1 (one_lt_pow₀ h hne).ne'
      · by_contra h; rw [not_le] at h
        exact absurd h1 (pow_lt_one₀ (norm_nonneg _) h hne).ne
    have hle : ‖zetaSys p n ^ t - 1‖ ≤ ‖zetaSys p n - 1‖ := by
      rw [show zetaSys p n ^ t - 1
          = (∑ i ∈ Finset.range t, zetaSys p n ^ i) * (zetaSys p n - 1) from
        (geom_sum_mul (zetaSys p n) t).symm, norm_mul]
      have hgeom : ‖∑ i ∈ Finset.range t, zetaSys p n ^ i‖ ≤ 1 :=
        IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
          (fun i _ => by rw [norm_pow, hξ1, one_pow])
      nlinarith [norm_nonneg (zetaSys p n - 1), hgeom]
    have hπ : ‖zetaSys p n - 1‖ < 1 := by have := norm_pi_lt_one p hn; rwa [pi] at this
    exact lt_of_le_of_lt hle hπ
  have htendR : Filter.Tendsto (fun m => ∑ k ∈ Finset.range m, c k * (zetaSys p n ^ t - 1) ^ k)
      Filter.atTop (nhds (seriesEval (PowerSeries.map (toCp p) f) (zetaSys p n ^ t - 1))) := by
    rw [seriesEval]
    exact (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_map_le_one p f) hzt).hasSum
      |>.tendsto_sum_nat
  have hgalScongr : Filter.Tendsto (fun m => (galAut p a n (S m) : ℂ_[p])) Filter.atTop
      (nhds (seriesEval (PowerSeries.map (toCp p) f) (zetaSys p n ^ t - 1))) :=
    htendR.congr (fun m => (hgalS m).symm)
  exact tendsto_nhds_unique htendGalC hgalScongr

/-- **The evaluation bridge** `evalPi (galSeries a f) n = σ_a(f(π_n))`: subst-eval bridge
(`seriesEval_subst`) reduces `(galSeries a f)(π_n) = f((galSubstend a)(π_n))`; the inner value
is `σ_a(π_n)` (`seriesEval_map_galSubstend`), and `σ_a` commutes with the outer evaluation
(`galAut_evalPi`). -/
theorem evalPi_galSeries (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) :
    evalPi p (galSeries p a f) n
      = (galAut p a n ⟨evalPi p f n,
          (Subring.mem_inf.1 (evalPi_mem_O p f hn)).1⟩ : ℂ_[p]) := by
  have hz : ‖pi p n‖ < 1 := norm_pi_lt_one p hn
  have hmap : PowerSeries.map (toCp p) (galSeries p a f)
      = (PowerSeries.map (toCp p) f).subst (PowerSeries.map (toCp p) (galSubstend p a)) :=
    PowerSeries.map_subst (hasSubst_galSubstend p a) f
  have hG0 : PowerSeries.constantCoeff (PowerSeries.map (toCp p) (galSubstend p a)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_galSubstend, map_zero]
  rw [galAut_evalPi p a f hn, evalPi, hmap]
  rw [seriesEval_subst p (norm_coeff_map_le_one p f)
    (fun k => by rw [PowerSeries.coeff_map, norm_toCp]; exact PadicInt.norm_le_one _) hG0 hz]
  rw [seriesEval_map_galSubstend p a hn]

/-- The Coleman series intertwines the two actions: `f_{σ_a u} = σ_a f_u`
(RJW TeX 3210–3216): both sides are `ℤ_[p]`-power series with the same `evalPi` at every
`n ≥ 1` (`(galNCU a u).elems n = σ_a(u_n) = evalPi (galSeries a (colemanSeries u)) n` by
`evalPi_galSeries` + `evalPi_colemanSeries`), so they are equal by `evalPi_injective`. -/
theorem colemanSeries_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) :
    colemanSeries p (galNCU p a u) = galSeries p a (colemanSeries p u) := by
  refine evalPi_injective p (fun n hn => ?_)
  rw [evalPi_colemanSeries p (galNCU p a u) hn, evalPi_galSeries p a (colemanSeries p u) hn]
  change ((galAutUnit p a (u.elems n) (Subring.mem_inf.1 (u.mem n)).1 : ℂ_[p]ˣ) : ℂ_[p]) = _
  rw [galAutUnit_val]
  congr 2
  apply Subtype.ext
  exact (evalPi_colemanSeries p u hn).symm

/-- Multiplication by `a` on `ℤ_[p]ˣ`, as a continuous self-map: the σ_a action on
`Λ(ℤ_[p]ˣ)` is the pushforward along this map (RJW TeX 3217–3234). -/
def unitsMulLeftCM (a : ℤ_[p]ˣ) : C(ℤ_[p]ˣ, ℤ_[p]ˣ) :=
  ⟨fun v => a * v, continuous_const.mul continuous_id⟩

/-- The descending-Pochhammer recursion for `Ring.choose` over `ℤ_[p]`:
`(n+1)·binom(r, n+1) = (r − n)·binom(r, n)`. Engine for the binomial-series derivative
identity. -/
private theorem succ_mul_ringChoose (r : ℤ_[p]) (n : ℕ) :
    ((n : ℤ_[p]) + 1) * Ring.choose r (n + 1) = (r - (n : ℤ_[p])) * Ring.choose r n := by
  have h1 : (descPochhammer ℤ (n + 1)).smeval r
      = ((n + 1).factorial : ℤ_[p]) * Ring.choose r (n + 1) := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose r (n + 1), nsmul_eq_mul]
  have h2 : (descPochhammer ℤ n).smeval r = (n.factorial : ℤ_[p]) * Ring.choose r n := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose r n, nsmul_eq_mul]
  have hX : ((Polynomial.X : Polynomial ℤ) - (n : Polynomial ℤ)).smeval r
      = r - (n : ℤ_[p]) := by
    rw [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one,
      pow_zero, nsmul_eq_mul, mul_one]
  have hkey : ((n + 1).factorial : ℤ_[p]) * Ring.choose r (n + 1)
      = ((n.factorial : ℤ_[p]) * Ring.choose r n) * (r - (n : ℤ_[p])) := by
    rw [← h1, descPochhammer_succ_right, Polynomial.smeval_mul, h2, hX]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hkey
  have hfac : (n.factorial : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  refine mul_left_cancel₀ hfac ?_
  linear_combination hkey

/-- `coeff k (binomialSeries r) = binom(r, k)` over `ℤ_[p]` (the `• 1` smul is plain
multiplication on `ℤ_[p]`). -/
private theorem coeff_binomialSeries' (r : ℤ_[p]) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.binomialSeries ℤ_[p] r) = Ring.choose r k := by
  rw [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- **The binomial-series derivative identity** (RJW TeX 3223, the engine of `σ_a`):
`(1+T)·(binomialSeries r)′ = r·binomialSeries r`, i.e. `(1+T)·((1+T)^r)′ = r·(1+T)^r`
formally. Proved coefficientwise from the `Ring.choose` recursion `succ_mul_ringChoose`. -/
private theorem one_add_X_mul_derivative_binomialSeries (r : ℤ_[p]) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (PowerSeries.binomialSeries ℤ_[p] r)
      = r • PowerSeries.binomialSeries ℤ_[p] r := by
  set B : PowerSeries ℤ_[p] := PowerSeries.binomialSeries ℤ_[p] r with hB
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.smul_eq_C_mul, PowerSeries.coeff_C_mul,
    coeff_binomialSeries']
  rw [PowerSeries.coeff_derivativeFun, hB, coeff_binomialSeries']
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, add_zero, Ring.choose_one_right, Ring.choose_zero_right,
      mul_one]
    push_cast
    ring
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, coeff_binomialSeries']
    have h : ((m : ℤ_[p]) + 1 + 1) * Ring.choose r (m + 1 + 1)
        = (r - ((m : ℤ_[p]) + 1)) * Ring.choose r (m + 1) := by
      have := succ_mul_ringChoose p r (m + 1)
      rwa [Nat.cast_add, Nat.cast_one] at this
    push_cast
    linear_combination h

/-- `Ring.inverse` commutes with substitution of a valid substituend, for a *unit*
argument: `(Ring.inverse f).subst G = Ring.inverse (f.subst G)` (substitution is a ring
hom, so it sends the unit `f` and its inverse to inverse units). -/
private theorem subst_inverse_of_isUnit {f G : PowerSeries ℤ_[p]} (hf : IsUnit f)
    (hg : PowerSeries.HasSubst G) :
    (Ring.inverse f).subst G = Ring.inverse (f.subst G) := by
  obtain ⟨v, rfl⟩ := hf
  set φ : PowerSeries ℤ_[p] →* PowerSeries ℤ_[p] :=
    ((PowerSeries.substAlgHom hg : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] PowerSeries ℤ_[p]) :
      PowerSeries ℤ_[p] →+* PowerSeries ℤ_[p]).toMonoidHom with hφ
  have hval : ∀ w : PowerSeries ℤ_[p], (w.subst G) = φ w := fun w => by
    rw [hφ, ← PowerSeries.coe_substAlgHom hg]; rfl
  rw [Ring.inverse_unit, hval, hval, ← Units.coe_map φ v,
    show φ ((v⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])
        = ((Units.map φ v)⁻¹ : (PowerSeries ℤ_[p])ˣ) by rw [← Units.coe_map, ← map_inv],
    Ring.inverse_unit]

/-- **The `∂log` chain rule under `σ_a`** (RJW TeX 3223): for a unit `f`,
`∂log(σ_a f) = a·σ_a(∂log f)`, i.e. `∂log(f((1+T)^a−1)) = a·(∂log f)((1+T)^a−1)`.
The chain rule (`derivative_subst`) feeds the binomial-derivative identity
`(1+T)·((1+T)^a−1)′ = a·(1+T)^a`, and substitution being a ring hom moves the `1+T`,
the inverse, and the `(1+T)^a` factors through. -/
private theorem dlog_galSeries (a : ℤ_[p]ˣ) {f : PowerSeries ℤ_[p]} (hf : IsUnit f) :
    dlog p (galSeries p a f) = (a : ℤ_[p]) • galSeries p a (dlog p f) := by
  classical
  set G : PowerSeries ℤ_[p] := galSubstend p a with hG
  have hg : PowerSeries.HasSubst G := hasSubst_galSubstend p a
  have hBG : (1 : PowerSeries ℤ_[p]) + G = PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p]) := by
    rw [hG, galSubstend, add_sub_cancel]
  have hGderiv : (1 + PowerSeries.X) * PowerSeries.derivativeFun G
      = (a : ℤ_[p]) • PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p]) := by
    have hdG : PowerSeries.derivativeFun G
        = PowerSeries.derivativeFun (PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p])) := by
      rw [hG, galSubstend,
        show (PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p]) - 1)
            = PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p]) + (-1 : PowerSeries ℤ_[p]) by ring,
        PowerSeries.derivativeFun_add,
        show (-1 : PowerSeries ℤ_[p]) = PowerSeries.C (-1 : ℤ_[p]) by simp,
        PowerSeries.derivativeFun_C, add_zero]
    rw [hdG, one_add_X_mul_derivative_binomialSeries p (a : ℤ_[p])]
  have hchain : PowerSeries.derivativeFun (f.subst G)
      = (PowerSeries.derivativeFun f).subst G * PowerSeries.derivativeFun G :=
    PowerSeries.derivative_subst ℤ_[p] hg
  have hsubstX : (1 + PowerSeries.X : PowerSeries ℤ_[p]).subst G = 1 + G := by
    rw [PowerSeries.subst_add hg, PowerSeries.subst_X hg,
      ← PowerSeries.coe_substAlgHom hg, map_one]
  set D : PowerSeries ℤ_[p] := (PowerSeries.derivativeFun f).subst G with hD
  set I : PowerSeries ℤ_[p] := Ring.inverse (f.subst G) with hI
  have hLHS : dlog p (galSeries p a f)
      = ((a : ℤ_[p]) • PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p])) * D * I := by
    rw [dlog, galSeries, hchain]
    rw [show (1 + PowerSeries.X) * (D * PowerSeries.derivativeFun G) * I
        = ((1 + PowerSeries.X) * PowerSeries.derivativeFun G) * D * I by ring, hGderiv]
  have hRHS : (a : ℤ_[p]) • galSeries p a (dlog p f)
      = ((a : ℤ_[p]) • PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p])) * D * I := by
    rw [dlog, galSeries, PowerSeries.subst_mul hg, PowerSeries.subst_mul hg, hsubstX,
      subst_inverse_of_isUnit p hf hg, hBG, ← hD, ← hI, PowerSeries.smul_eq_C_mul,
      PowerSeries.smul_eq_C_mul]
    ring
  rw [hLHS, hRHS]

/-- **The inverse Mahler bridge** `𝒜⁻¹(σ_a g) = sigma a (𝒜⁻¹ g)` (RJW §3.5.5, TeX 1138,
transported to `𝒜⁻¹`): `galSeries a = subst((1+T)^a−1)` is exactly the `z`-twist of the
Mahler transform `mahlerTransform_sigma`, inverted via `mahlerLinearEquiv`. -/
private theorem mahlerSymm_galSeries (a : ℤ_[p]ˣ) (g : PowerSeries ℤ_[p]) :
    (PadicMeasure.mahlerLinearEquiv p).symm (galSeries p a g)
      = PadicMeasure.sigma p a ((PadicMeasure.mahlerLinearEquiv p).symm g) := by
  set μ : PadicMeasure p ℤ_[p] := (PadicMeasure.mahlerLinearEquiv p).symm g with hμ
  have hmt : PadicMeasure.mahlerTransform p (PadicMeasure.sigma p a μ)
      = galSeries p a g := by
    rw [PadicMeasure.mahlerTransform_sigma, galSeries, galSubstend]
    congr 1
    rw [hμ, ← PadicMeasure.mahlerLinearEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [← hmt, ← PadicMeasure.mahlerLinearEquiv_apply, LinearEquiv.symm_apply_apply]

/-- **The `a`/`a⁻¹` cancellation** at the level of test functions (RJW TeX 3223): for
`f : C(ℤ_[p]ˣ, ℤ_[p])`, the function `a • ((x⁻¹·f) ∘ extendByZero) ∘ (mult-a)` equals
`(x⁻¹·(f ∘ mult-a)) ∘ extendByZero` on `ℤ_[p]`. On units `w`: LHS `= a·(a·w)⁻¹·f(a·w)
= w⁻¹·f(a·w)` = RHS (the `x⁻¹` swallows the `a`); off the units both sides vanish
(`a·x` is a unit iff `x` is). -/
private theorem cancel_a_extendByZero (a : ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    (a : ℤ_[p]) • ((PadicMeasure.extendByZero p (PadicMeasure.invCM p * f)).comp
        (PadicMeasure.mulCM p (a : ℤ_[p])))
      = PadicMeasure.extendByZero p (PadicMeasure.invCM p * f.comp (unitsMulLeftCM p a)) := by
  classical
  ext x
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul]
  change (a : ℤ_[p]) * PadicMeasure.extendByZero p (PadicMeasure.invCM p * f) ((a : ℤ_[p]) * x)
      = PadicMeasure.extendByZero p (PadicMeasure.invCM p * f.comp (unitsMulLeftCM p a)) x
  by_cases hx : IsUnit x
  · obtain ⟨w, rfl⟩ := hx
    have hax : ((a : ℤ_[p]) * (w : ℤ_[p])) = ((a * w : ℤ_[p]ˣ) : ℤ_[p]) := by
      rw [Units.val_mul]
    rw [hax, PadicMeasure.extendByZero_coe_unit, PadicMeasure.extendByZero_coe_unit]
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply]
    have hfa : f (unitsMulLeftCM p a w) = f (a * w) := rfl
    have hinvaw : PadicMeasure.invCM p (a * w) = (((a * w)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := rfl
    have hinvw : PadicMeasure.invCM p w = (((w⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) := rfl
    have haa : (a : ℤ_[p]) * ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hfa, hinvaw, hinvw, mul_inv_rev, Units.val_mul]
    rw [show (a : ℤ_[p]) * ((((w⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
          * f (a * w))
        = (((w⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) * ((a : ℤ_[p]) * ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
          * f (a * w) by ring, haa, mul_one]
  · have hax : ¬ IsUnit ((a : ℤ_[p]) * x) := by
      intro h
      refine hx ?_
      have := (a⁻¹ : ℤ_[p]ˣ).isUnit.mul h
      rwa [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at this
    have hz0 : PadicMeasure.extendByZero p (PadicMeasure.invCM p * f) ((a : ℤ_[p]) * x) = 0 := by
      change (if h : IsUnit ((a : ℤ_[p]) * x) then _ else (0 : ℤ_[p])) = 0
      rw [dif_neg hax]
    have hz1 : PadicMeasure.extendByZero p
        (PadicMeasure.invCM p * f.comp (unitsMulLeftCM p a)) x = 0 := by
      change (if h : IsUnit x then _ else (0 : ℤ_[p])) = 0
      rw [dif_neg hx]
    rw [hz0, hz1, mul_zero]

/-- The μ-generic measure identity behind `Col_galNCU` (RJW TeX 3217–3234): after the
`∂log`/Mahler reductions, `Col(σ_a u)` and `σ_a·Col(u)` both reduce to
`x⁻¹·Res(a•σ_a μ)` resp. `pushforward (mult-a) (x⁻¹·Res μ)` with `μ = 𝒜⁻¹(∂log f_u)`;
they agree by the `a`/`a⁻¹` cancellation `cancel_a_extendByZero`. -/
private theorem unitsCmul_smul_sigma_eq_pushforward (a : ℤ_[p]ˣ)
    (μ : PadicMeasure p ℤ_[p]) :
    PadicMeasure.unitsCmul p (PadicMeasure.invCM p)
        (((a : ℤ_[p]) • PadicMeasure.sigma p a μ).comp (PadicMeasure.extendByZero p))
      = PadicMeasure.pushforward p (unitsMulLeftCM p a) (PadicMeasure.unitsCmul p
          (PadicMeasure.invCM p) (μ.comp (PadicMeasure.extendByZero p))) := by
  refine LinearMap.ext fun f => ?_
  rw [PadicMeasure.pushforward_apply, PadicMeasure.unitsCmul_apply, PadicMeasure.unitsCmul_apply]
  change ((a : ℤ_[p]) • PadicMeasure.sigma p a μ)
      (PadicMeasure.extendByZero p (PadicMeasure.invCM p * f))
    = μ (PadicMeasure.extendByZero p
        (PadicMeasure.invCM p * (f.comp (unitsMulLeftCM p a))))
  rw [LinearMap.smul_apply, PadicMeasure.sigma, PadicMeasure.pushforward_apply,
    ← cancel_a_extendByZero p a f, map_smul]

/-- **RJW §12.1 Proposition (TeX 3193–3236)**: the Coleman map is `𝒢`-equivariant.
Here `σ_a` acts on `Λ(ℤ_[p]ˣ)` by the pushforward along multiplication by `a`.

Statement note (T1201): the RHS is finalised to the genuine `σ_a` pushforward
`PadicMeasure.pushforward p (unitsMulLeftCM a)` (the skeleton carried the placeholder
`unitsCmul p 1`); this is the authorised statement-fix (RJW TeX 3217–3234: `∂log(σ_a f)
= a·σ_a ∂log f`, `∂⁻¹∘σ_a = a⁻¹σ_a∘∂⁻¹`, restriction equivariant, so the measure-side
action is pushforward along `v ↦ a·v`). -/
theorem Col_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) :
    Col p (galNCU p a u)
      = PadicMeasure.pushforward p (unitsMulLeftCM p a) (Col p u) := by
  rw [Col, Col, colemanSeries_galNCU p a u,
    dlog_galSeries p a (colemanSeries_isUnit p u), map_smul, mahlerSymm_galSeries p a]
  exact unitsCmul_smul_sigma_eq_pushforward p a
    ((PadicMeasure.mahlerLinearEquiv p).symm (dlog p (colemanSeries p u)))

end PadicLFunctions.Coleman
