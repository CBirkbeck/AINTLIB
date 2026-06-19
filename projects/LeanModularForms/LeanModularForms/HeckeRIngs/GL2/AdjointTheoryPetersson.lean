/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.ConcreteFamily
import LeanModularForms.HeckeRIngs.GL2.Unified.RingTransport

/-!
# Hecke adjoint theory: Petersson development and eigenform diagonalization

This file is the downstream continuation of
`LeanModularForms.HeckeRIngs.GL2.AdjointTheory`. It contains the bulk of the
adjoint theory of Hecke operators with respect to the Petersson inner product —
the long T090/T024/T128/T205 double-coset tile development — culminating in the
adjoint identity `heckeT_p_adjoint`, normality `heckeT_n_normal`, and the
existence of a simultaneous eigenform basis for cusp form spaces.

The core cusp/Hecke infrastructure (`heckeT_n_cusp`, `PreservesCusps`,
`adjointGamma0Rep`, `peterssonAdj`, `peterssonInner_slash_adjoint`, …) lives in
the imported `AdjointTheory.lean`; this file builds on top of it.

## Main results

* `heckeT_p_adjoint` — T_p* = ⟨p⟩⁻¹ T_p (Diamond–Shurman Thm 5.5.3)
* `diamondOp_petersson_unitary` — `⟨d⟩` is unitary for pet
* `heckeT_n_adjoint` — adjoint of the general `T_n`
* `heckeT_n_normal` — T_n is normal
* `exists_simultaneous_eigenform_basis` — spectral theorem for Hecke operators

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5
* [Miy] Miyake, *Modular Forms*, §4.5 (Thm 4.5.4–4.5.5)
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

private theorem heckeT_n_cusp_comm_diamondOp (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (diamondOp_cusp k d f) = diamondOp_cusp k d (heckeT_n_cusp k n f) :=
  CuspForm.ext fun τ ↦ congr_arg
    (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ)
    (DFunLike.congr_fun (heckeT_n_comm_diamondOp k n hn d) f.toModularForm').symm

private theorem heckeT_n_cusp_decomp (m : ℕ) [NeZero m] (hm : 1 < m)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    let p := m.minFac
    let hp := Nat.minFac_prime (by omega : m ≠ 1)
    let v := m.factorization p
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    haveI : NeZero (m / p ^ v) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p))
        (pow_pos hp.pos v)).ne'⟩
    heckeT_n_cusp k m f =
      heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) f) :=
  CuspForm.ext fun z ↦ heckeT_n_cusp_unfold m hm f z

private theorem heckeT_n_cusp_comm (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k m (heckeT_n_cusp k n f) = heckeT_n_cusp k n (heckeT_n_cusp k m f) :=
  CuspForm.ext fun τ ↦ congr_arg
    (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ)
    (DFunLike.congr_fun (heckeT_n_comm k m n hm hn) f.toModularForm')

private theorem diamondOp_cusp_comp (d₁ d₂ : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d₁ (diamondOp_cusp k d₂ f) = diamondOp_cusp k (d₁ * d₂) f := by
  change diamondOpCusp k d₁ (diamondOpCusp k d₂ f) = diamondOpCusp k (d₁ * d₂) f
  rw [show diamondOpCusp k d₁ (diamondOpCusp k d₂ f) =
    ((diamondOpCusp k d₁).comp (diamondOpCusp k d₂)) f from rfl, ← diamondOpCusp_mul]

private theorem diamondOp_cusp_one (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k (1 : (ZMod N)ˣ) f = f :=
  DFunLike.congr_fun (diamondOpCusp_one (N := N) (k := k)) f

private theorem heckeT_n_adjoint_coprime_case (m : ℕ) [NeZero m]
    (hcop : Nat.Coprime m N) (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (hn₁_cop : Nat.Coprime n₁ N) (hn₂_cop : Nat.Coprime n₂ N)
    (hpv_dvd : n₁ ∣ m) (hdiv_eq : n₂ = m / n₁)
    (hDecomp : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        heckeT_n_cusp k m h =
          heckeT_n_cusp k n₁ (heckeT_n_cusp k n₂ h))
    (ih_n₁ : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        petN (heckeT_n_cusp k n₁ f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹
            (heckeT_n_cusp k n₁ g₀)))
    (ih_n₂ : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        petN (heckeT_n_cusp k n₂ f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime n₂ hn₂_cop)⁻¹
            (heckeT_n_cusp k n₂ g₀)))
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_n_cusp k m f') g' =
      petN f' (diamondOp_cusp k (ZMod.unitOfCoprime m hcop)⁻¹
        (heckeT_n_cusp k m g')) := by
  rw [hDecomp f', ih_n₁ (heckeT_n_cusp k n₂ f') g',
    ih_n₂ f' (diamondOp_cusp k (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹
      (heckeT_n_cusp k n₁ g')),
    heckeT_n_cusp_comm_diamondOp n₂ hn₂_cop (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹
      (heckeT_n_cusp k n₁ g'), diamondOp_cusp_comp]
  have h_hecke : heckeT_n_cusp k n₂ (heckeT_n_cusp k n₁ g') = heckeT_n_cusp k m g' :=
    (heckeT_n_cusp_comm n₂ n₁ hn₂_cop hn₁_cop g').trans (hDecomp g').symm
  have h_unit : (ZMod.unitOfCoprime n₂ hn₂_cop)⁻¹ *
      (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹ = (ZMod.unitOfCoprime m hcop)⁻¹ := by
    rw [← mul_inv]
    congr 1
    ext
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime]
    rw [mul_comm]
    exact mod_cast congr_arg (Nat.cast (R := ZMod N))
      (show (n₁ : ℕ) * n₂ = m by rw [hdiv_eq]; exact Nat.mul_div_cancel' hpv_dvd)
  simp only [h_hecke, h_unit]

private theorem heckeT_n_cusp_ppow_recursion (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp k (p ^ (r + 2)) f =
      heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f) -
        (↑p : ℂ) ^ (k - 1) • diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
          (heckeT_n_cusp k (p ^ r) f) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  refine CuspForm.ext fun τ ↦ ?_
  show (heckeT_n k (p ^ (r + 2)) f.toModularForm').toFun τ =
    ((heckeT_n k p) ((heckeT_n k (p ^ (r + 1))) f.toModularForm')).toFun τ -
      (↑p : ℂ) ^ (k - 1) •
        ((diamondOp k (ZMod.unitOfCoprime p hpN))
          ((heckeT_n k (p ^ r)) f.toModularForm')).toFun τ
  rw [heckeT_n_prime_pow k hp (r + 2) (by omega), heckeT_n_prime_pow k hp (r + 1) (by omega),
      heckeT_n_prime_coprime k hp hpN, heckeT_ppow_succ_succ k p hp r,
      diamondOp_n_coprime k hpN, heckeT_p_all_coprime k hp hpN]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  conv_rhs =>
    rw [show heckeT_n k (p ^ r) = heckeT_ppow (N := N) k p hp r by
        rcases r with _ | r
        · simp [heckeT_n, heckeT_n_aux, heckeT_ppow]
        · exact heckeT_n_prime_pow k hp _ (by omega)]
  rfl

private theorem diamondOp_cusp_cancel (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (diamondOp_cusp k d⁻¹ f) = f := by
  rw [show diamondOp_cusp k d (diamondOp_cusp k d⁻¹ f) =
      ((diamondOpCusp k d).comp (diamondOpCusp k d⁻¹)) f from rfl,
    ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
  rfl

private theorem diamondOp_cusp_sub (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (f - g) = diamondOp_cusp k d f - diamondOp_cusp k d g :=
  (diamondOpCusp k d).map_sub f g

private theorem diamondOp_cusp_smul (d : (ZMod N)ˣ) (c : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (c • f) = c • diamondOp_cusp k d f :=
  (diamondOpCusp k d).map_smul c f

private theorem petN_diamondOp_adjoint (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k d f) g = petN f (diamondOp_cusp k d⁻¹ g) := by
  calc petN (diamondOp_cusp k d f) g
      = petN (diamondOp_cusp k d f) (diamondOp_cusp k d (diamondOp_cusp k d⁻¹ g)) := by
        rw [diamondOp_cusp_cancel]
    _ = petN f (diamondOp_cusp k d⁻¹ g) := diamondOp_petersson_unitary d f _

private theorem conj_natCast_zpow (p : ℕ) :
    starRingEnd ℂ ((↑p : ℂ) ^ (k - 1)) = (↑p : ℂ) ^ (k - 1) := by
  rw [map_zpow₀, Complex.conj_natCast]

omit [NeZero N] in
private theorem unitOfCoprime_inv_mul_pow_succ {a : ℕ} (p : ℕ) (h1 : Nat.Coprime (p ^ a) N)
    (h2 : Nat.Coprime p N) (h3 : Nat.Coprime (p ^ (a + 1)) N) :
    (ZMod.unitOfCoprime (p ^ a) h1)⁻¹ * (ZMod.unitOfCoprime p h2)⁻¹ =
      (ZMod.unitOfCoprime (p ^ (a + 1)) h3)⁻¹ := by
  rw [← mul_inv]
  congr 1
  ext
  simp only [Units.val_mul, ZMod.coe_unitOfCoprime]
  push_cast
  ring

private theorem heckeT_n_adjoint_ppow_case (p : ℕ) (hp : Nat.Prime p) (v : ℕ) (hv : 2 ≤ v)
    (hcop : Nat.Coprime (p ^ v) N)
    (ih : ∀ j : ℕ, j < p ^ v → (hj_pos : 0 < j) → (hj : Nat.Coprime j N) →
      ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        haveI : NeZero j := ⟨hj_pos.ne'⟩
        petN (heckeT_n_cusp k j f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime j hj)⁻¹ (heckeT_n_cusp k j g₀)))
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    petN (heckeT_n_cusp k (p ^ v) f') g' =
      petN f' (diamondOp_cusp k (ZMod.unitOfCoprime (p ^ v) hcop)⁻¹
        (heckeT_n_cusp k (p ^ v) g')) := by
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  obtain ⟨r, rfl⟩ : ∃ r, v = r + 2 := ⟨v - 2, by omega⟩
  have hp_cop : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left
    (dvd_pow_self p (by omega : r + 2 ≠ 0)) hcop
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  have hpv1_cop : Nat.Coprime (p ^ (r + 1)) N := Nat.Coprime.pow_left _ hp_cop
  have hpr_cop : Nat.Coprime (p ^ r) N := Nat.Coprime.pow_left _ hp_cop
  have hp_lt : p < p ^ (r + 2) := by
    simpa using Nat.pow_lt_pow_right hp.one_lt (by omega : 1 < r + 2)
  set up := ZMod.unitOfCoprime p hp_cop
  set c := (↑p : ℂ) ^ (k - 1)
  rw [heckeT_n_cusp_ppow_recursion p hp hp_cop r f', sub_eq_add_neg, petN_add_left,
    petN_neg_left, petN_conj_smul_left, conj_natCast_zpow,
    ih p hp_lt hp.pos hp_cop (heckeT_n_cusp k (p ^ (r + 1)) f') g',
    ih (p ^ (r + 1)) (Nat.pow_lt_pow_right hp.one_lt (by omega)) (pow_pos hp.pos _) hpv1_cop f'
      (diamondOp_cusp k up⁻¹ (heckeT_n_cusp k p g')),
    petN_diamondOp_adjoint up (heckeT_n_cusp k (p ^ r) f') g',
    ih (p ^ r) (Nat.pow_lt_pow_right hp.one_lt (by omega)) (pow_pos hp.pos _) hpr_cop f'
      (diamondOp_cusp k up⁻¹ g'),
    heckeT_n_cusp_comm_diamondOp (p ^ (r + 1)) hpv1_cop up⁻¹ (heckeT_n_cusp k p g'),
    heckeT_n_cusp_comm_diamondOp (p ^ r) hpr_cop up⁻¹ g', diamondOp_cusp_comp,
    diamondOp_cusp_comp, heckeT_n_cusp_comm (p ^ (r + 1)) p hpv1_cop hp_cop g',
    ← petN_smul_right c f',
    ← petN_neg_right, ← petN_add_right]
  congr 1
  have h_unit_prod_v : (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ * up⁻¹ =
      (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹ :=
    unitOfCoprime_inv_mul_pow_succ p hpv1_cop hp_cop hcop
  rw [h_unit_prod_v, unitOfCoprime_inv_mul_pow_succ p hpr_cop hp_cop hpv1_cop,
    heckeT_n_cusp_ppow_recursion p hp hp_cop r g',
    diamondOp_cusp_sub, diamondOp_cusp_smul, diamondOp_cusp_comp,
    (mul_inv_eq_iff_eq_mul.mp h_unit_prod_v).symm]
  abel

private theorem heckeT_n_adjoint_prime_power_case (p : ℕ) (hp : Nat.Prime p) (v : ℕ) (hv : 0 < v)
    (hcop : Nat.Coprime (p ^ v) N)
    (ih : ∀ j : ℕ, j < p ^ v → (hj_pos : 0 < j) → (hj : Nat.Coprime j N) →
      ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        haveI : NeZero j := ⟨hj_pos.ne'⟩
        petN (heckeT_n_cusp k j f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime j hj)⁻¹ (heckeT_n_cusp k j g₀)))
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    petN (heckeT_n_cusp k (p ^ v) f') g' =
      petN f' (diamondOp_cusp k (ZMod.unitOfCoprime (p ^ v) hcop)⁻¹
        (heckeT_n_cusp k (p ^ v) g')) := by
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  by_cases hv1 : v = 1
  · have hp_m : Nat.Prime (p ^ v) := by rw [hv1, pow_one]; exact hp
    have hTn_eq : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        heckeT_n_cusp k (p ^ v) h = heckeT_p_cusp k (p ^ v) hp_m hcop h :=
      fun h ↦ CuspForm.ext fun τ ↦ by
        show (heckeT_n k (p ^ v) h.toModularForm').toFun τ =
          (heckeT_p k (p ^ v) hp_m hcop h.toModularForm').toFun τ
        rw [heckeT_n_prime_coprime k hp_m hcop]
    rw [hTn_eq f', hTn_eq g']
    exact heckeT_p_adjoint (p ^ v) hp_m hcop f' g'
  · exact heckeT_n_adjoint_ppow_case p hp v (by omega) hcop ih f' g'

private theorem heckeT_n_adjoint_composite_step (m : ℕ) (hcop : Nat.Coprime m N) (hle : 1 < m)
    (ih : ∀ j : ℕ, j < m → (hj_pos : 0 < j) → (hj : Nat.Coprime j N) →
      ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        haveI : NeZero j := ⟨hj_pos.ne'⟩
        petN (heckeT_n_cusp k j f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime j hj)⁻¹ (heckeT_n_cusp k j g₀)))
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero m := ⟨(by omega : 0 < m).ne'⟩
    petN (heckeT_n_cusp k m f') g' =
      petN f' (diamondOp_cusp k (ZMod.unitOfCoprime m hcop)⁻¹
        (heckeT_n_cusp k m g')) := by
  haveI : NeZero m := ⟨(by omega : 0 < m).ne'⟩
  set p := m.minFac
  have hpp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
  set v := m.factorization p
  have hpv_pos : 0 < p ^ v := pow_pos hpp.pos v
  have hdiv_pos : 0 < m / p ^ v :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) hpv_pos
  haveI : NeZero (p ^ v) := ⟨hpv_pos.ne'⟩
  haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
  have hpv_cop : Nat.Coprime (p ^ v) N := Nat.Coprime.pow_left v
    (Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd m) hcop)
  have hdiv_cop : Nat.Coprime (m / p ^ v) N :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p)) hcop
  by_cases hpv_lt : p ^ v < m
  · exact heckeT_n_adjoint_coprime_case m hcop (p ^ v) (m / p ^ v)
      hpv_cop hdiv_cop (Nat.ordProj_dvd m p) rfl (heckeT_n_cusp_decomp m hle)
      (ih (p ^ v) hpv_lt hpv_pos hpv_cop)
      (ih (m / p ^ v) (heckeT_n_unfold_lt m hle) hdiv_pos hdiv_cop) f' g'
  · have hpv_eq : p ^ v = m := le_antisymm
      (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (not_lt.mp hpv_lt)
    have hTn_pv : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        heckeT_n_cusp k m h = heckeT_n_cusp k (p ^ v) h := fun h ↦ CuspForm.ext fun τ ↦ by
        show (heckeT_n k m h.toModularForm').toFun τ =
          (heckeT_n k (p ^ v) h.toModularForm').toFun τ
        simp only [heckeT_n, hpv_eq]
    have h_unit_eq : (ZMod.unitOfCoprime m hcop)⁻¹ = (ZMod.unitOfCoprime (p ^ v) hpv_cop)⁻¹ := by
      congr 1; ext; simp [ZMod.coe_unitOfCoprime, hpv_eq]
    rw [hTn_pv f', hTn_pv g', h_unit_eq]
    exact heckeT_n_adjoint_prime_power_case p hpp v
      (hpp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)) hpv_cop
      (fun j hj hj_pos hj_cop f₀ g₀ ↦ ih j (hpv_eq ▸ hj) hj_pos hj_cop f₀ g₀) f' g'

private theorem heckeT_n_cusp_one_eq (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp (N := N) k 1 f = f :=
  CuspForm.ext fun τ ↦ by
    change (heckeT_n k 1 f.toModularForm').toFun τ = f τ
    rw [heckeT_n_one]; rfl

/-- The Hecke adjoint for general T_n: `T_n* = ⟨n⟩⁻¹ T_n` on `S_k(Γ₁(N))`,
w.r.t. the level-N Petersson inner product `petN`. -/
theorem heckeT_n_adjoint (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_n_cusp k n f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeT_n_cusp k n g)) := by
  suffices key : ∀ m : ℕ, (hm : 0 < m) → (hcop : Nat.Coprime m N) →
      ∀ f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        haveI : NeZero m := ⟨hm.ne'⟩
        petN (heckeT_n_cusp k m f') g' =
          petN f' (diamondOp_cusp k (ZMod.unitOfCoprime m hcop)⁻¹
            (heckeT_n_cusp k m g')) from
    key n (NeZero.pos n) hn f g
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hcop f' g'
    haveI : NeZero m := ⟨hm.ne'⟩
    by_cases hle : m ≤ 1
    · obtain rfl : m = 1 := by omega
      have hunit : ZMod.unitOfCoprime 1 hcop = 1 := by ext; simp [ZMod.coe_unitOfCoprime]
      rw [heckeT_n_cusp_one_eq f', heckeT_n_cusp_one_eq g', hunit, inv_one, diamondOp_cusp_one]
    · exact heckeT_n_adjoint_composite_step m hcop (by omega) ih f' g'

/-- T_n is normal: `T_n T_n* = T_n* T_n` for `(n,N) = 1`.

Reference: [DS] Theorem 5.5.4, [Miy] Theorem 4.5.5. -/
theorem heckeT_n_normal (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeT_n_cusp k n f)) =
      diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹
        (heckeT_n_cusp k n (heckeT_n_cusp k n f)) :=
  heckeT_n_cusp_comm_diamondOp n hn (ZMod.unitOfCoprime n hn)⁻¹ (heckeT_n_cusp k n f)

/-- A cusp form is a common eigenfunction of all `T_n` (cusp form version). -/
abbrev IsCommonEigenfunctionCusp (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    ∃ a : ℂ, heckeT_n_cusp k n.val f = a • f

/-- `heckeT_n_cusp` preserves the cusp-form character space `S_k(Γ₁(N), χ)`.
Follows from `heckeT_n_preserves_charSpace` (the `ModularForm` version) via
the cusp-form coercion. -/
lemma heckeT_n_cusp_preserves_cuspFormCharSpace
    (k : ℤ) (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeT_n_cusp k n f ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff] at hf ⊢
  intro d
  change diamondOp_cusp k d (heckeT_n_cusp k n f) = (↑(χ d) : ℂ) • heckeT_n_cusp k n f
  rw [(heckeT_n_cusp_comm_diamondOp n hn d f).symm]
  have hfd : diamondOp_cusp k d f = (↑(χ d) : ℂ) • f := hf d
  rw [hfd]
  ext z
  change (heckeT_n k n ((↑(χ d) : ℂ) • f).toModularForm').toFun z =
    (↑(χ d) : ℂ) • (heckeT_n k n f.toModularForm').toFun z
  rw [show ((↑(χ d) : ℂ) • f).toModularForm' =
      (↑(χ d) : ℂ) • f.toModularForm' from rfl, map_smul]
  rfl

/-- `T_n` restricted to `cuspFormCharSpace` as a linear endomorphism. -/
noncomputable def heckeT_n_cusp_charRestrict (k : ℤ) (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (cuspFormCharSpace k χ) where
  toFun := fun ⟨f, hf⟩ ↦
    ⟨heckeT_n_cusp k n f, heckeT_n_cusp_preserves_cuspFormCharSpace k n hn χ hf⟩
  map_add' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ ↦ by
    ext z
    change (heckeT_n k n (f₁ + f₂).toModularForm').toFun z =
      ((heckeT_n k n f₁.toModularForm').toFun z + (heckeT_n k n f₂.toModularForm').toFun z)
    rw [show (f₁ + f₂).toModularForm' = f₁.toModularForm' + f₂.toModularForm' from rfl, map_add]
    rfl
  map_smul' := fun c ⟨f, _⟩ ↦ by
    ext z
    change (heckeT_n k n (c • f).toModularForm').toFun z =
      c • (heckeT_n k n f.toModularForm').toFun z
    rw [show (c • f).toModularForm' = c • f.toModularForm' from rfl, map_smul]
    rfl

private theorem petN_add_left' (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g := by
  have e := congr_arg (starRingEnd ℂ) (petN_add_right g f₁ f₂)
  rwa [petN_conj_symm, map_add, petN_conj_symm, petN_conj_symm] at e

private theorem petN_conj_smul_left' (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (c • f) g = starRingEnd ℂ c * petN f g := by
  simp only [petN, Finset.mul_sum]
  congr 1
  ext q
  have h1 : ⇑(c • f) ∣[k] (q.out : SL(2, ℤ))⁻¹ = c • (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹) :=
    ModularForm.SL_smul_slash k _ ⇑f c
  rw [h1]
  exact UpperHalfPlane.peterssonInner_conj_smul_left k ModularGroup.fd c _ _

/-- `petN f f` has non-negative real part. -/
lemma petN_self_re_nonneg (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    0 ≤ (petN f f).re := by
  simp only [petN, Complex.re_sum]
  exact Finset.sum_nonneg fun q _ ↦
    let ⟨r, hr_nonneg, hr_eq⟩ := petN_summand_nonneg f q
    hr_eq ▸ Complex.ofReal_re r ▸ hr_nonneg

/-- An `InnerProductSpace.Core` instance on `CuspForm` from `petN`.

This provides the algebraic inner product structure needed for the spectral theorem.
The inner product is `⟪f, g⟫ := petN f g` (conjugate-linear in first, linear in second). -/
noncomputable def petN_innerProductCore :
    @InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ _ _ where
  inner f g := petN f g
  conj_inner_symm f g := petN_conj_symm f g
  re_inner_nonneg f := petN_self_re_nonneg f
  add_left f g h := petN_add_left' f g h
  smul_left f g c := petN_conj_smul_left' c f g
  definite f hf := petN_definite f hf

private lemma heckeT_n_adjoint_on_charSpace (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (_hf : f ∈ cuspFormCharSpace k χ) (hg : g ∈ cuspFormCharSpace k χ) :
    petN (heckeT_n_cusp k n f) g =
      (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * petN f (heckeT_n_cusp k n g) := by
  rw [heckeT_n_adjoint n hn f g]
  have h_diamond : diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeT_n_cusp k n g) =
      (↑(χ (ZMod.unitOfCoprime n hn)⁻¹) : ℂ) • heckeT_n_cusp k n g :=
    ((mem_cuspFormCharSpace_iff k χ _).mp
      (heckeT_n_cusp_preserves_cuspFormCharSpace k n hn χ hg)) (ZMod.unitOfCoprime n hn)⁻¹
  rw [h_diamond]
  simp only [map_inv, Units.val_inv_eq_inv_val]
  exact petN_smul_right _ f (heckeT_n_cusp k n g)

private lemma heckeT_n_cusp_charRestrict_commute (χ : (ZMod N)ˣ →* ℂˣ) (m n : ℕ) [NeZero m]
    [NeZero n] (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    Commute (heckeT_n_cusp_charRestrict k m hm χ) (heckeT_n_cusp_charRestrict k n hn χ) := by
  change heckeT_n_cusp_charRestrict k m hm χ * heckeT_n_cusp_charRestrict k n hn χ =
    heckeT_n_cusp_charRestrict k n hn χ * heckeT_n_cusp_charRestrict k m hm χ
  refine LinearMap.ext fun ⟨f, _⟩ ↦ ?_
  simp only [Module.End.mul_apply]
  exact Subtype.ext (heckeT_n_cusp_comm m n hm hn f)

private abbrev CoprimeIndex (N : ℕ) := { n : ℕ+ // Nat.Coprime n.val N }

private noncomputable def heckeFamily (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ) :
    CoprimeIndex N → Module.End ℂ (cuspFormCharSpace k chi) :=
  fun ⟨n, hn⟩ ↦ haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp_charRestrict k n.val hn chi

private lemma heckeFamily_pairwise_commute (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ) :
    Pairwise fun i j ↦ Commute (heckeFamily k chi i) (heckeFamily k chi j) := by
  intro ⟨m, hm⟩ ⟨n, hn⟩ _hmn
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  exact heckeT_n_cusp_charRestrict_commute chi m.val n.val hm hn

private lemma heckeFamily_triangularizable (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)]
    (i : CoprimeIndex N) :
    ⨆ μ : ℂ, Module.End.maxGenEigenspace (heckeFamily k chi i) μ = ⊤ := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  exact Module.End.iSup_maxGenEigenspace_eq_top _

private lemma heckeFamily_joint_eigenspace_top (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)] :
    ⨆ ev : CoprimeIndex N → ℂ,
      ⨅ i, Module.End.maxGenEigenspace (heckeFamily k chi i) (ev i) = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (heckeFamily k chi) (heckeFamily_pairwise_commute k chi)
    (heckeFamily_triangularizable k chi)

private lemma heckeFamily_isFinitelySemisimple (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)] (i : CoprimeIndex N) :
    (heckeFamily k chi i).IsFinitelySemisimple := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  set T := heckeT_n_cusp_charRestrict k n hn chi
  letI ipCore : InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    petN_innerProductCore
  letI : NormedAddCommGroup (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ ipCore
  letI : InnerProductSpace ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    InnerProductSpace.ofCore (𝕜 := ℂ) (F := CuspForm ((Gamma1 N).map (mapGL ℝ)) k) inferInstance
  set χn_inv : ℂ := ↑(chi (ZMod.unitOfCoprime n hn))⁻¹
  obtain ⟨c, hc_sq⟩ := IsAlgClosed.exists_pow_nat_eq χn_inv (show 0 < 2 from two_pos)
  have hχn_inv_ne : χn_inv ≠ 0 := by
    simp only [χn_inv]
    exact mod_cast Units.ne_zero ((chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ)
  have hc_ne : c ≠ 0 := by
    intro hc
    rw [hc, zero_pow (by norm_num : 2 ≠ 0)] at hc_sq
    exact hχn_inv_ne hc_sq.symm
  have h_conj_mul_c : starRingEnd ℂ c * c = 1 := by
    have h_norm_c_sq : ‖c‖ ^ 2 = 1 := by
      rw [← norm_pow, hc_sq]
      exact ((Units.coeHom ℂ).isOfFinOrder (MonoidHom.isOfFinOrder chi
        (isOfFinOrder_of_finite (ZMod.unitOfCoprime n hn))).inv).norm_eq_one
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h_norm_c_sq,
      Complex.ofReal_one]
  have h_symm : LinearMap.IsSymmetric (c • T) := by
    intro x y
    change petN (c • heckeT_n_cusp k n x.val) y.val = petN x.val (c • heckeT_n_cusp k n y.val)
    rw [petN_conj_smul_left' c (heckeT_n_cusp k n x.val) y.val,
      heckeT_n_adjoint_on_charSpace chi n hn x.prop y.prop,
      petN_smul_right c x.val (heckeT_n_cusp k n y.val)]
    change starRingEnd ℂ c * (χn_inv * _) = c * _
    rw [← hc_sq, sq]
    have h_key : ∀ P : ℂ, starRingEnd ℂ c * (c * c * P) = c * P :=
      fun P ↦ by linear_combination (c * P) * h_conj_mul_c
    exact h_key _
  rw [Module.End.isFinitelySemisimple_iff_isSemisimple]
  have h_semi_cT : (c • T).IsSemisimple := by
    rw [← Module.End.isFinitelySemisimple_iff_isSemisimple]
    exact h_symm.isFinitelySemisimple
  exact (Module.End.IsSemisimple_smul_iff hc_ne).mp h_semi_cT

private lemma eigenforms_orthogonal_of_distinct_eigenvalues (chi : (ZMod N)ˣ →* ℂˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf_char : f ∈ cuspFormCharSpace k chi)
    (hg_char : g ∈ cuspFormCharSpace k chi) {n : ℕ} [NeZero n] (hn : Nat.Coprime n N) (a_f b_g : ℂ)
    (hf_eig : heckeT_n_cusp k n f = a_f • f) (hg_eig : heckeT_n_cusp k n g = b_g • g)
    (h_diff : starRingEnd ℂ a_f ≠ (↑(chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * b_g) :
    petN f g = 0 := by
  have h_adj := heckeT_n_adjoint_on_charSpace chi n hn hf_char hg_char
  rw [hf_eig, petN_conj_smul_left', hg_eig, petN_smul_right, ← mul_assoc] at h_adj
  have h_eq : (starRingEnd ℂ a_f - (↑(chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * b_g) *
      petN f g = 0 := by
    rw [sub_mul, h_adj, sub_self]
  exact (mul_eq_zero.mp h_eq).resolve_left (sub_ne_zero.mpr h_diff)

private lemma heckeFamily_commute_all (χ : (ZMod N)ˣ →* ℂˣ) (i j : CoprimeIndex N) :
    Commute (heckeFamily k χ i) (heckeFamily k χ j) := by
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  · exact heckeFamily_pairwise_commute k χ hij

private lemma heckeFamily_mapsTo_maxGenEigenspace (χ : (ZMod N)ˣ →* ℂˣ) :
    ∀ i j : CoprimeIndex N, ∀ φ : ℂ,
      Set.MapsTo (heckeFamily k χ i)
        ((heckeFamily k χ j).maxGenEigenspace φ)
        ((heckeFamily k χ j).maxGenEigenspace φ) :=
  fun i j φ ↦ Module.End.mapsTo_maxGenEigenspace_of_comm (heckeFamily_commute_all χ j i) φ

private lemma heckeFamily_iSupIndep_iInf_maxGenEigenspace
    (χ : (ZMod N)ˣ →* ℂˣ) :
    iSupIndep
      (fun ev : CoprimeIndex N → ℂ ↦ ⨅ i, (heckeFamily k χ i).maxGenEigenspace (ev i)) :=
  Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (heckeFamily k χ) (heckeFamily_mapsTo_maxGenEigenspace χ)

private lemma heckeFamily_iInf_eq (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    (ev : CoprimeIndex N → ℂ) :
    (⨅ i, (heckeFamily k χ i).maxGenEigenspace (ev i)) =
      ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i) := by
  refine iInf_congr (fun i ↦ ?_)
  exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (heckeFamily_isFinitelySemisimple k χ i) (ev i)

private lemma heckeFamily_iSupIndep_iInf_eigenspace
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    iSupIndep (fun ev : CoprimeIndex N → ℂ ↦
      ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)) := by
  refine (heckeFamily_iSupIndep_iInf_maxGenEigenspace (k := k) χ).mono fun ev ↦ ?_
  simp only [heckeFamily_iInf_eq, le_refl]

private lemma heckeFamily_iSup_iInf_eigenspace_eq_top
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    ⨆ ev : CoprimeIndex N → ℂ,
      ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i) = ⊤ := by
  rw [← heckeFamily_joint_eigenspace_top k χ]
  exact iSup_congr (fun ev ↦ (heckeFamily_iInf_eq χ ev).symm)

open Classical in
private lemma heckeFamily_directSum_isInternal
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    DirectSum.IsInternal (fun ev : CoprimeIndex N → ℂ ↦
      ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (heckeFamily_iSupIndep_iInf_eigenspace χ)
    (heckeFamily_iSup_iInf_eigenspace_eq_top χ)

private lemma heckeT_n_eigenvalue_chi_hecke (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) (hf_ne : f ≠ 0)
    {n : ℕ} [NeZero n] (hn : Nat.Coprime n N) {a : ℂ}
    (hf_eig : heckeT_n_cusp k n f = a • f) :
    starRingEnd ℂ a = (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * a := by
  have h_adj := heckeT_n_adjoint_on_charSpace χ n hn hf hf
  rw [hf_eig, petN_conj_smul_left', petN_smul_right, ← mul_assoc] at h_adj
  exact mul_right_cancel₀ (fun hpet ↦ hf_ne (petN_definite f hpet)) h_adj

lemma eigenforms_orthogonal_of_ne_eigenvalues (χ : (ZMod N)ˣ →* ℂˣ)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf_char : f ∈ cuspFormCharSpace k χ)
    (hg_char : g ∈ cuspFormCharSpace k χ) (hf_ne : f ≠ 0) (_hg_ne : g ≠ 0) {n : ℕ} [NeZero n]
    (hn : Nat.Coprime n N) {a b : ℂ} (hf_eig : heckeT_n_cusp k n f = a • f)
    (hg_eig : heckeT_n_cusp k n g = b • g) (h_diff_ab : a ≠ b) :
    petN f g = 0 := by
  refine eigenforms_orthogonal_of_distinct_eigenvalues χ f g hf_char hg_char hn a b hf_eig
    hg_eig ?_
  intro h_eq
  rw [heckeT_n_eigenvalue_chi_hecke χ hf_char hf_ne hn hf_eig] at h_eq
  have hχ_ne : (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) ≠ 0 :=
    mod_cast Units.ne_zero ((χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ)
  exact h_diff_ab (mul_left_cancel₀ hχ_ne h_eq)

private lemma joint_eigenspace_orthogonal (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] {ev₁ ev₂ : CoprimeIndex N → ℂ}
    (h_ne : ev₁ ≠ ev₂) {f g : cuspFormCharSpace k χ}
    (hf : f ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev₁ i))
    (hg : g ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev₂ i))
    (hf_ne : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0)
    (hg_ne : (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0) :
    petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
  obtain ⟨n_idx, hn_diff⟩ := Function.ne_iff.mp h_ne
  obtain ⟨n_pn, hn_cop⟩ := n_idx
  haveI : NeZero n_pn.val := ⟨n_pn.pos.ne'⟩
  exact eigenforms_orthogonal_of_ne_eigenvalues χ f.prop g.prop hf_ne hg_ne hn_cop
    (congr_arg Subtype.val
      (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hf ⟨n_pn, hn_cop⟩)))
    (congr_arg Subtype.val
      (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hg ⟨n_pn, hn_cop⟩)))
    hn_diff

private lemma joint_eigenspace_subset_isCommonEigenfunction (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] (ev : CoprimeIndex N → ℂ)
    {f : cuspFormCharSpace k χ}
    (hf : f ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)) :
    ∀ n : ℕ+, Nat.Coprime n.val N →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      ∃ a : ℂ, heckeT_n_cusp k n.val (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        a • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  intro n hn_cop
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  exact ⟨ev ⟨n, hn_cop⟩, congr_arg Subtype.val
    (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hf ⟨n, hn_cop⟩))⟩

private lemma jointEigenspace_petN_orthogonal (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] {ev₁ ev₂ : CoprimeIndex N → ℂ}
    (h_ne : ev₁ ≠ ev₂) {u v : cuspFormCharSpace k χ}
    (hu : u ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev₁ i))
    (hv : v ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev₂ i)) :
    petN (u : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
  by_cases hu0 : (u : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0
  · rw [hu0, petN_zero_left]
  by_cases hv0 : (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0
  · rw [hv0, petN_zero_right]
  exact joint_eigenspace_orthogonal χ h_ne hu hv hu0 hv0

theorem exists_simultaneous_eigenform_basis (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    ∃ (B : Finset (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      (∀ f ∈ B, f ∈ cuspFormCharSpace k χ) ∧
      (∀ f ∈ B, IsCommonEigenfunctionCusp k f) ∧
      (∀ f g, f ∈ B → g ∈ B → f ≠ g → petN f g = 0) := by
  classical
  letI ipCore : InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    petN_innerProductCore
  letI : NormedAddCommGroup (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ ipCore
  letI : InnerProductSpace ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    InnerProductSpace.ofCore (𝕜 := ℂ) (F := CuspForm ((Gamma1 N).map (mapGL ℝ)) k) inferInstance
  have h_internal := heckeFamily_directSum_isInternal (k := k) χ
  let W : (CoprimeIndex N → ℂ) → Submodule ℂ (cuspFormCharSpace k χ) :=
    fun ev ↦ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)
  let evToBasis : (CoprimeIndex N → ℂ) → Type := fun ev ↦ Fin (Module.finrank ℂ (W ev))
  let basisAtEv : ∀ ev, Module.Basis (evToBasis ev) ℂ (W ev) :=
    fun ev ↦ (stdOrthonormalBasis ℂ (W ev)).toBasis
  let bigBasis : Module.Basis (Σ ev, evToBasis ev) ℂ (cuspFormCharSpace k χ) :=
    h_internal.collectedBasis basisAtEv
  have h_orthFamily : OrthogonalFamily ℂ
      (fun ev ↦ (W ev : Submodule ℂ (cuspFormCharSpace k χ)))
      (fun ev ↦ (W ev).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise fun _ _ h_ne ↦ Submodule.isOrtho_iff_inner_eq.mpr
      fun _ hu _ hv ↦ jointEigenspace_petN_orthogonal χ h_ne hu hv
  have h_orthonormal : Orthonormal ℂ ⇑bigBasis :=
    DirectSum.IsInternal.collectedBasis_orthonormal h_orthFamily h_internal
      fun ev ↦ by
        simp only [basisAtEv, OrthonormalBasis.coe_toBasis]
        exact (stdOrthonormalBasis ℂ (W ev)).orthonormal
  haveI : Finite (Σ ev, evToBasis ev) := Module.Finite.finite_basis bigBasis
  haveI : Fintype (Σ ev, evToBasis ev) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (Σ ev, evToBasis ev)).image
    (fun x ↦ ((bigBasis x : cuspFormCharSpace k χ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k)), ?_, ?_, ?_⟩
  · intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨x, _, rfl⟩ := hf
    exact (bigBasis x).property
  · intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨x, _, rfl⟩ := hf
    intro n hn_cop
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    exact joint_eigenspace_subset_isCommonEigenfunction χ x.1
      (h_internal.collectedBasis_mem basisAtEv x) n hn_cop
  · intro f g hf hg hfg
    rw [Finset.mem_image] at hf hg
    obtain ⟨x, _, rfl⟩ := hf
    obtain ⟨y, _, rfl⟩ := hg
    exact h_orthonormal.inner_eq_zero (fun h ↦ hfg (by rw [h]))

/-- The Hecke family `heckeFamily k χ` maps a submodule `p ≤ S_k(Γ₁(N),χ)` into itself,
provided the underlying cusp-form submodule `W` (with `p = W.comap (subtype)`) is preserved
by every `heckeT_n_cusp`. -/
private lemma heckeFamily_mapsTo_comap (χ : (ZMod N)ˣ →* ℂˣ)
    (W : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hW : ∀ (n : ℕ), ∀ [NeZero n], Nat.Coprime n N → ∀ f ∈ W, heckeT_n_cusp k n f ∈ W)
    (i : CoprimeIndex N) :
    ∀ x ∈ W.comap (cuspFormCharSpace k χ).subtype,
      heckeFamily k χ i x ∈ W.comap (cuspFormCharSpace k χ).subtype := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  intro x hx
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx ⊢
  exact hW n hn x hx

/-- Restricting the commuting `heckeFamily` to a stable submodule keeps it pairwise
commuting (proof helper for `exists_eigenform_decomposition_of_invariant`). -/
private lemma heckeFamily_restrict_pairwise_commute
    (χ : (ZMod N)ˣ →* ℂˣ) {p : Submodule ℂ (cuspFormCharSpace k χ)}
    (hmaps : ∀ i, ∀ x ∈ p, heckeFamily k χ i x ∈ p) :
    Pairwise fun i j ↦ Commute
      ((heckeFamily k χ i).restrict (hmaps i) : Module.End ℂ p)
      ((heckeFamily k χ j).restrict (hmaps j) : Module.End ℂ p) := by
  intro i j _hij
  change ((heckeFamily k χ i).restrict (hmaps i) : Module.End ℂ p) *
      (heckeFamily k χ j).restrict (hmaps j) =
    ((heckeFamily k χ j).restrict (hmaps j) : Module.End ℂ p) *
      (heckeFamily k χ i).restrict (hmaps i)
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  have hcfun := DFunLike.congr_fun (heckeFamily_commute_all (k := k) χ i j)
    (x : cuspFormCharSpace k χ)
  simp only [Module.End.mul_apply] at hcfun ⊢
  simpa only [LinearMap.coe_restrict_apply] using hcfun

/-- The joint eigenspace decomposition for the restriction of `heckeFamily` to a stable
submodule fills the whole submodule (proof helper for
`exists_eigenform_decomposition_of_invariant`). -/
private lemma heckeFamily_restrict_iSup_iInf_eigenspace_eq_top
    (χ : (ZMod N)ˣ →* ℂˣ) [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    {p : Submodule ℂ (cuspFormCharSpace k χ)}
    (hmaps : ∀ i, ∀ x ∈ p, heckeFamily k χ i x ∈ p) :
    ⨆ ev : CoprimeIndex N → ℂ, ⨅ i, Module.End.eigenspace
      ((heckeFamily k χ i).restrict (hmaps i) : Module.End ℂ p) (ev i) = ⊤ := by
  set F : CoprimeIndex N → Module.End ℂ p :=
    fun i ↦ (heckeFamily k χ i).restrict (hmaps i) with hF_def
  have hF_tri : ∀ i, ⨆ μ : ℂ, (F i).maxGenEigenspace μ = ⊤ := fun i ↦
    Module.End.genEigenspace_restrict_eq_top (k := ⊤) (hmaps i)
      (heckeFamily_triangularizable k χ i)
  have hF_ss : ∀ i, (F i).IsFinitelySemisimple := fun i ↦
    (heckeFamily_isFinitelySemisimple k χ i).restrict (hmaps i)
  have h_max : ⨆ ev : CoprimeIndex N → ℂ,
      ⨅ i, (F i).maxGenEigenspace (ev i) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      F (heckeFamily_restrict_pairwise_commute χ hmaps) hF_tri
  rw [← h_max]
  refine iSup_congr (fun ev ↦ iInf_congr (fun i ↦ ?_))
  exact ((hF_ss i).maxGenEigenspace_eq_eigenspace (ev i)).symm

/-- An element of the joint eigenspace of the restricted `heckeFamily` is a common
Hecke eigenfunction at the underlying cusp-form level (proof helper for
`exists_eigenform_decomposition_of_invariant`). -/
private lemma isCommonEigenfunction_of_mem_iInf_eigenspace_restrict (χ : (ZMod N)ˣ →* ℂˣ)
    {p : Submodule ℂ (cuspFormCharSpace k χ)}
    (hmaps : ∀ i, ∀ x ∈ p, heckeFamily k χ i x ∈ p) (ev : CoprimeIndex N → ℂ) (v : p)
    (hv : v ∈ ⨅ i, Module.End.eigenspace
      ((heckeFamily k χ i).restrict (hmaps i) : Module.End ℂ p) (ev i)) :
    IsCommonEigenfunctionCusp k
      (((v : cuspFormCharSpace k χ)) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  intro n hn_cop
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  refine ⟨ev ⟨n, hn_cop⟩, ?_⟩
  have heq := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv ⟨n, hn_cop⟩)
  have heq_V : (heckeFamily k χ ⟨n, hn_cop⟩) (v : p).1 = ev ⟨n, hn_cop⟩ • (v : p).1 := by
    simpa only [LinearMap.coe_restrict_apply, SetLike.val_smul] using congr_arg Subtype.val heq
  have h := congr_arg (Subtype.val) heq_V
  simp only [SetLike.val_smul] at h
  exact h

/-- **Eigenform decomposition of an invariant submodule.**  Let `W` be a submodule of cusp
forms preserved by every Hecke operator `T_n` with `(n,N)=1`, and let `g ∈ W` lie in the
Nebentypus space `S_k(Γ₁(N),χ)`.  Then `g` is a finite sum of common Hecke eigenfunctions,
each of which lies in `W ∩ S_k(Γ₁(N),χ)`.

Applied with `W = S_k^♯(N)` (the new subspace, `heckeT_n_preserves_cuspFormsNew`) this is
the spectral input to Miyake 4.6.12's descent (ticket T008a). -/
theorem exists_eigenform_decomposition_of_invariant
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    (W : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hW : ∀ (n : ℕ), ∀ [NeZero n], Nat.Coprime n N →
      ∀ f ∈ W, heckeT_n_cusp k n f ∈ W)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ) (hg_W : g ∈ W) :
    ∃ (ι : Type) (_ : Fintype ι) (h : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (∀ i, h i ∈ W) ∧ (∀ i, h i ∈ cuspFormCharSpace k χ) ∧
      (∀ i, IsCommonEigenfunctionCusp k (h i)) ∧ g = ∑ i, h i := by
  classical
  set p : Submodule ℂ (cuspFormCharSpace k χ) :=
    W.comap (cuspFormCharSpace k χ).subtype with hp_def
  have hmaps : ∀ i, ∀ x ∈ p, heckeFamily k χ i x ∈ p :=
    fun i ↦ heckeFamily_mapsTo_comap χ W hW i
  have hg_p : (⟨g, hg_char⟩ : cuspFormCharSpace k χ) ∈ p := by
    simp only [hp_def, Submodule.mem_comap, Submodule.coe_subtype]; exact hg_W
  set gp : p := ⟨⟨g, hg_char⟩, hg_p⟩ with hgp_def
  have hg_mem : gp ∈ ⨆ ev : CoprimeIndex N → ℂ, ⨅ i, Module.End.eigenspace
      ((heckeFamily k χ i).restrict (hmaps i) : Module.End ℂ p) (ev i) := by
    rw [heckeFamily_restrict_iSup_iInf_eigenspace_eq_top χ hmaps]; trivial
  obtain ⟨fc, hfc_mem, hfc_sum⟩ := Submodule.mem_iSup_iff_exists_finsupp _ _ |>.mp hg_mem
  set hForm : (CoprimeIndex N → ℂ) → CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    fun ev ↦ (((fc ev : p) : cuspFormCharSpace k χ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) with hForm_def
  have h_in_W : ∀ ev, hForm ev ∈ W := fun ev ↦ Submodule.mem_comap.mp <| by
    rw [← hp_def]; exact (fc ev).2
  have h_in_char : ∀ ev, hForm ev ∈ cuspFormCharSpace k χ := fun ev ↦ (fc ev : p).1.2
  have h_eigen : ∀ ev, IsCommonEigenfunctionCusp k (hForm ev) := fun ev ↦
    isCommonEigenfunction_of_mem_iInf_eigenspace_restrict χ hmaps ev (fc ev) (hfc_mem ev)
  refine ⟨{ev // ev ∈ fc.support}, inferInstance, fun e ↦ hForm e.1,
    fun e ↦ h_in_W e.1, fun e ↦ h_in_char e.1, fun e ↦ h_eigen e.1, ?_⟩
  have hsum_form : g = ∑ ev ∈ fc.support, hForm ev := by
    have hsum_p : ∑ ev ∈ fc.support, (fc ev : p) = gp := hfc_sum
    have hval : (gp : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        ∑ ev ∈ fc.support, hForm ev := by
      rw [← hsum_p, hForm_def]
      simp only [AddSubmonoidClass.coe_finsetSum]
    exact hval
  rw [hsum_form, ← Finset.sum_coe_sort fc.support (fun ev ↦ hForm ev)]

end HeckeRing.GL2
