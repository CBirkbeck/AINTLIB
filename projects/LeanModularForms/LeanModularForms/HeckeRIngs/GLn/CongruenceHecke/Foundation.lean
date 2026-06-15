/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.Basic
import LeanModularForms.HeckeRIngs.GLn.SL2Surjection
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.StabConjugation
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.PolynomialRing
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.Ideal.Maps

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Foundation

Defines the Hecke pair `(Γ₀(N), Δ₀(N))` for congruence subgroups and the
foundational double-coset lemmas (Shimura §3.3, 3.28–3.29), including the
Chinese-remainder machinery `Gamma_gcd_eq_mul` and the coprime-determinant
double-coset comparison `doubleCoset_eq_of_Gamma0_coprimeDet`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

/-- `Δ₀(N)`: integer matrices with `c ≡ 0 (mod N)`, `(a, N) = 1`, positive determinant.
    Shimura (3.3.1). -/
noncomputable def Delta0_submonoid (N : ℕ) : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | HasIntEntries 2 g ∧ 0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      (N : ℤ) ∣ A 1 0 ∧ Int.gcd (A 0 0) N = 1}
  one_mem' := ⟨hasIntEntries_one 2, by simp, 1,
    by ext i j; simp [Matrix.map_apply, Matrix.one_apply], by simp, by simp⟩
  mul_mem' := by
    intro a b ⟨ha, hda, A, hA, hAN, hAco⟩ ⟨hb, hdb, B, hB, hBN, hBco⟩
    refine ⟨HasIntEntries.mul (n := 2) ha hb,
      by simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]; exact mul_pos hda hdb,
      A * B, ?_, ?_, ?_⟩
    · ext i j; simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      rw [Int.gcd_add_right_left_of_dvd _ (dvd_mul_of_dvd_right hBN _),
        Int.gcd_mul_right_left_of_gcd_eq_one hAco]
      exact hBco

/-- `Γ₀(N) ≤ Δ₀(N)`: the subgroup embeds into the submonoid. -/
lemma Gamma0_le_Delta0 (N : ℕ) [NeZero N] :
    ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)).toSubmonoid ≤ Delta0_submonoid N := by
  intro g hg
  rw [Subgroup.mem_toSubmonoid, Subgroup.mem_map] at hg
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [CongruenceSubgroup.Gamma0_mem] at hσ_mem
  have hc : (N : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσ_mem
  have hmem : mapGL ℚ σ ∈ SLnZ_subgroup 2 := MonoidHom.mem_range.mpr ⟨σ, rfl⟩
  simp only [Delta0_submonoid, Submonoid.mem_mk]
  refine ⟨SLnZ_subgroup_hasIntEntries 2 hmem, ?_,
    (σ : Matrix (Fin 2) (Fin 2) ℤ), rfl, hc, ?_⟩
  · have hdet := σ.prop; rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.det_fin_two, mapGL_coe_matrix, RingHom.mapMatrix_apply,
      map_apply_coe, algebraMap_int_eq, Int.coe_castRingHom, Matrix.map_apply]
    exact_mod_cast hdet ▸ one_pos
  · rw [← Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨k, hk⟩ := hc
    have hdet : (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; linarith
    exact ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1,
      -(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * k, by rw [hk] at hdet; linarith⟩

lemma Delta0_le_posDetInt (N : ℕ) :
    Delta0_submonoid N ≤ posDetInt_submonoid 2 :=
  fun _ ⟨hint, hdet, _⟩ ↦ ⟨hint, hdet⟩

private lemma Gamma0_map_commensurable_SLnZ (N : ℕ) [NeZero N] :
    Subgroup.Commensurable ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ))
      (Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤) := by
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₀(N) ≤ commensurator(Γ₀(N))`. Follows from Shimura Lemma 3.10. -/
lemma Delta0_le_commensurator (N : ℕ) [NeZero N] :
    Delta0_submonoid N ≤
    (commensurator ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ))).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (Gamma0_map_commensurable_SLnZ N),
      ← MonoidHom.range_eq_map]
  exact (Delta0_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke pair `(Γ₀(N), Δ₀(N))`** — Shimura §3.3. -/
noncomputable def Gamma0_pair (N : ℕ) [NeZero N] : HeckePair (GL (Fin 2) ℚ) where
  H := (CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)
  Δ := Delta0_submonoid N
  h₀ := Gamma0_le_Delta0 N
  h₁ := Delta0_le_commensurator N

section FoundationLemmas

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- `Γ₀(N) ≤ SL₂(ℤ)` (as subgroups of `GL₂(ℚ)`): every Gamma0 element is in SLnZ. -/
lemma Gamma0_le_SLnZ : (CongruenceSubgroup.Gamma0 N).map (mapGL ℚ) ≤ SLnZ_subgroup 2 := by
  rintro _ ⟨σ, _, rfl⟩
  exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩

omit [NeZero N] in
/-- `Γ(N) ≤ Γ₀(N)`: the principal congruence subgroup is contained in Gamma0. -/
lemma GammaN_le_Gamma0 : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N := fun _ hσ ↦ by
  rw [CongruenceSubgroup.Gamma_mem] at hσ
  exact CongruenceSubgroup.Gamma0_mem.mpr hσ.2.2.1

omit [NeZero N] in
private lemma gcd_A11_N_eq_one
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hAN : (N : ℤ) ∣ A 1 0)
    (hdet_coprime : Int.gcd A.det N = 1) :
    Int.gcd (A 1 1) N = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hdet_coprime ⊢
  have hdet : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  obtain ⟨k, hk⟩ := hAN
  have hdet_co' : IsCoprime (A 0 0 * A 1 1) (N : ℤ) := by
    have : A 0 0 * A 1 1 = A.det + (A 0 1 * k) * ↑N := by
      rw [hdet, hk]; ring
    rw [this]; exact hdet_coprime.add_mul_right_left _
  exact (IsCoprime.mul_left_iff.mp hdet_co').2

private lemma intCast_eq_zero_of_dvd {m n : ℕ} (h : m ∣ n) (x : ℤ)
    (hx : (x : ZMod n) = 0) : (x : ZMod m) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr
    ((Int.natCast_dvd_natCast.mpr h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hx))

private lemma intCast_eq_one_of_dvd {m n : ℕ} (h : m ∣ n) (x : ℤ)
    (hx : (x : ZMod n) = 1) : (x : ZMod m) = 1 := by
  have h2 := intCast_eq_zero_of_dvd h _ (by push_cast; simp [hx] : ((x - 1 : ℤ) : ZMod n) = 0)
  push_cast at h2; rwa [sub_eq_zero] at h2

open CongruenceSubgroup in
private lemma Gamma_le_of_dvd {m n : ℕ} (h : m ∣ n) : Gamma n ≤ Gamma m := by
  intro γ hγ
  rw [Gamma_mem] at hγ ⊢
  exact ⟨intCast_eq_one_of_dvd h _ hγ.1,
    intCast_eq_zero_of_dvd h _ hγ.2.1,
    intCast_eq_zero_of_dvd h _ hγ.2.2.1,
    intCast_eq_one_of_dvd h _ hγ.2.2.2⟩

private lemma int_crt {m n x y : ℤ} (h : x ≡ y [ZMOD ↑(Int.gcd m n)]) :
    ∃ z : ℤ, z ≡ x [ZMOD m] ∧ z ≡ y [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h; obtain ⟨k, hk⟩ := h
  have hbez := Int.gcd_eq_gcd_ab m n; set g := (↑(Int.gcd m n) : ℤ)
  refine ⟨x + m * (Int.gcdA m n * k), ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]; exact ⟨-(Int.gcdA m n * k), by ring⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨Int.gcdB m n * k,
      by rw [show y = x + g * k from by linarith, hbez]; ring⟩

private lemma intModEq_to_zmod {m : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD ↑m]) :
    (a : ZMod m) = (b : ZMod m) :=
  (ZMod.intCast_eq_intCast_iff _ _ _).mpr h

private lemma SL2_gamma_entry_modEq (N : ℕ) (γ : SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (i j : Fin 2) :
    ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ℤ) ≡ (γ i j : ℤ) [ZMOD ↑N] := by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ
  have h := congr_fun₂ (congr_arg Subtype.val hγ) i j
  simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, coe_one,
    Int.coe_castRingHom] at h
  rw [← ZMod.intCast_eq_intCast_iff]; simpa [one_apply] using h.symm

private lemma crt_lift_reduces_mod {a b : ℕ} [NeZero (Nat.lcm a b)]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (β : SpecialLinearGroup (Fin 2) ℤ)
    (hβ : (↑(SpecialLinearGroup.map (Int.castRingHom (ZMod (Nat.lcm a b))) β) :
        Matrix (Fin 2) (Fin 2) (ZMod (Nat.lcm a b))) =
      M.map (Int.castRingHom (ZMod (Nat.lcm a b))))
    {m : ℕ} (hm : m ∣ Nat.lcm a b) (i j : Fin 2) :
    (↑(SpecialLinearGroup.map (Int.castRingHom (ZMod m)) β) :
        Matrix (Fin 2) (Fin 2) (ZMod m)) i j = ((M i j : ℤ) : ZMod m) := by
  have hentry : (((β : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (Nat.lcm a b)) =
      ((M i j : ℤ) : ZMod (Nat.lcm a b)) := by
    have := congr_fun₂ hβ i j
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]
      using this
  have := congr_arg (ZMod.castHom hm (ZMod m)) hentry
  simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
    map_intCast] using this

private lemma exists_Gamma_factor_of_mem_Gamma_gcd (a b : ℕ) [NeZero a] [NeZero b]
    [NeZero (Nat.gcd a b)] [NeZero (Nat.lcm a b)]
    (γ : SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma (Nat.gcd a b)) :
    ∃ y ∈ CongruenceSubgroup.Gamma a, ∃ z ∈ CongruenceSubgroup.Gamma b, y * z = γ := by
  have hcompat : ∀ i j : Fin 2,
      ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ℤ) ≡
      (γ i j : ℤ) [ZMOD ↑(Int.gcd (↑a) (↑b))] := by
    rw [show (↑(Int.gcd (↑a : ℤ) (↑b : ℤ)) : ℤ) = ↑(Nat.gcd a b) from by simp [Int.gcd]]
    exact SL2_gamma_entry_modEq _ γ hγ
  obtain ⟨z00, hz00a, hz00b⟩ := int_crt (hcompat 0 0)
  obtain ⟨z01, hz01a, hz01b⟩ := int_crt (hcompat 0 1)
  obtain ⟨z10, hz10a, hz10b⟩ := int_crt (hcompat 1 0)
  obtain ⟨z11, hz11a, hz11b⟩ := int_crt (hcompat 1 1)
  have hdet_lcm : z00 * z11 - z01 * z10 ≡ 1 [ZMOD ↑(Nat.lcm a b)] := by
    rw [show (↑(Nat.lcm a b) : ℤ) = ↑(Int.lcm ↑a ↑b) from by simp [Int.lcm, Nat.lcm]]
    rw [← Int.modEq_and_modEq_iff_modEq_lcm]
    refine ⟨?_, ?_⟩
    · show z00 * z11 - z01 * z10 ≡ 1 * 1 - 0 * 0 [ZMOD ↑a]
      exact (hz00a.mul hz11a).sub (hz01a.mul hz10a)
    · have hdetγ : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := γ.prop; rw [det_fin_two] at h; exact_mod_cast h
      show z00 * z11 - z01 * z10 ≡ 1 [ZMOD ↑b]
      rw [← hdetγ]; exact (hz00b.mul hz11b).sub (hz01b.mul hz10b)
  set M : Matrix (Fin 2) (Fin 2) ℤ := !![z00, z01; z10, z11]
  have hM_det : (M.map (Int.castRingHom (ZMod (Nat.lcm a b)))).det = 1 := by
    simp only [det_fin_two, M, Matrix.map_apply, Int.coe_castRingHom]
    have h := intModEq_to_zmod hdet_lcm
    push_cast at h ⊢; exact_mod_cast h
  obtain ⟨β, hβ⟩ := SL2Reduction.SL2_reduction_surjective (Nat.lcm a b)
    ⟨M.map (Int.castRingHom (ZMod (Nat.lcm a b))), hM_det⟩
  have hβ_mat : (↑(SpecialLinearGroup.map (Int.castRingHom (ZMod (Nat.lcm a b))) β) :
      Matrix (Fin 2) (Fin 2) (ZMod (Nat.lcm a b))) =
      M.map (Int.castRingHom (ZMod (Nat.lcm a b))) := congr_arg Subtype.val hβ
  have hzM : ∀ i j : Fin 2, (M i j : ZMod a) = ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ZMod a) ∧
      (M i j : ZMod b) = (γ i j : ZMod b) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      exact ⟨intModEq_to_zmod ‹_›, intModEq_to_zmod ‹_›⟩
  have hβ_a : β ∈ CongruenceSubgroup.Gamma a := by
    rw [CongruenceSubgroup.Gamma_mem']; ext i j
    rw [crt_lift_reduces_mod M β hβ_mat (Nat.dvd_lcm_left a b) i j, (hzM i j).1]
    simp [Matrix.one_apply]
  have hβγ_b : β⁻¹ * γ ∈ CongruenceSubgroup.Gamma b := by
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv]
    have hβ_b : SpecialLinearGroup.map (Int.castRingHom (ZMod b)) β =
        SpecialLinearGroup.map (Int.castRingHom (ZMod b)) γ := by
      ext i j
      rw [crt_lift_reduces_mod M β hβ_mat (Nat.dvd_lcm_right a b) i j, (hzM i j).2]
      simp
    rw [hβ_b]; exact inv_mul_cancel _
  exact ⟨β, hβ_a, β⁻¹ * γ, hβγ_b, by group⟩

open CongruenceSubgroup in
/-- **Shimura Lemma 3.28**: `Γ(gcd(a,b)) = Γ(a) · Γ(b)` — the product of principal
    congruence subgroups is the congruence subgroup of the gcd. -/
theorem Gamma_gcd_eq_mul (a b : ℕ) [NeZero a] [NeZero b]
    [NeZero (Nat.gcd a b)] :
    (Gamma (Nat.gcd a b)).map (mapGL ℚ) =
    ((Gamma a).map (mapGL ℚ)) ⊔ ((Gamma b).map (mapGL ℚ)) := by
  rw [← Subgroup.map_sup]
  congr 1
  apply le_antisymm
  · haveI : (Gamma a).Normal := Gamma_normal a
    haveI : NeZero (Nat.lcm a b) :=
      ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    intro γ hγ
    rw [Subgroup.mem_sup_of_normal_left]
    exact exists_Gamma_factor_of_mem_Gamma_gcd a b γ hγ
  · exact sup_le (Gamma_le_of_dvd (Nat.gcd_dvd_left a b))
      (Gamma_le_of_dvd (Nat.gcd_dvd_right a b))

omit [NeZero N] in
private lemma dvd_apply_one_zero_of_dvd_mul (P Q : Matrix (Fin 2) (Fin 2) ℤ)
    (hPQ : (N : ℤ) ∣ (P * Q) 1 0) (hP10 : (N : ℤ) ∣ P 1 0)
    (hP11 : Int.gcd (P 1 1) N = 1) : (N : ℤ) ∣ Q 1 0 := by
  have key : (P * Q) 1 0 = P 1 0 * Q 0 0 + P 1 1 * Q 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [key] at hPQ
  have h2 : (N : ℤ) ∣ P 1 1 * Q 1 0 := by
    have := Int.dvd_sub hPQ (dvd_mul_of_dvd_left hP10 (Q 0 0))
    rwa [add_sub_cancel_left] at this
  rw [mul_comm] at h2
  exact (Int.isCoprime_iff_gcd_eq_one.mpr hP11).symm.dvd_of_dvd_mul_right h2

omit [NeZero N] in
private lemma Gamma0_mul_apply_one_zero_and_gcd (τ A : Matrix (Fin 2) (Fin 2) ℤ)
    (hτ10 : (N : ℤ) ∣ τ 1 0) (hτ11 : (N : ℤ) ∣ (τ 1 1 - 1))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco2 : Int.gcd (A 1 1) N = 1) :
    (N : ℤ) ∣ (τ * A) 1 0 ∧ Int.gcd ((τ * A) 1 1) N = 1 := by
  refine ⟨?_, ?_⟩
  · have : (τ * A) 1 0 = τ 1 0 * A 0 0 + τ 1 1 * A 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_right hAN _)
  · rw [← Int.isCoprime_iff_gcd_eq_one]
    have hmod : (N : ℤ) ∣ ((τ * A) 1 1 - A 1 1) := by
      have : (τ * A) 1 1 - A 1 1 = τ 1 0 * A 0 1 + (τ 1 1 - 1) * A 1 1 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_left hτ11 _)
    obtain ⟨k, hk⟩ := hmod
    rw [show (τ * A) 1 1 = A 1 1 + k * ↑N from by linarith]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hAco2).add_mul_right_left k

private lemma mapGL_mul_coe_eq_intMatrix (τ δ : SpecialLinearGroup (Fin 2) ℤ)
    (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    (↑(mapGL ℚ τ * g * mapGL ℚ δ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((τ : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ) := by
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hA]
  ext i j; simp [Matrix.mul_apply, Matrix.map_apply]

open CongruenceSubgroup in
private lemma mem_Gamma0_doubleCoset_of_mem_Delta0
    (α : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco2 : Int.gcd (A 1 1) N = 1)
    (hAdet_ne : A.det ≠ 0) (hdet_coprime : Int.gcd A.det N = 1)
    (σ₁ σ₂ : SpecialLinearGroup (Fin 2) ℤ)
    (hx_delta : mapGL ℚ σ₁ * α * mapGL ℚ σ₂ ∈ Delta0_submonoid N) :
    mapGL ℚ σ₁ * α * mapGL ℚ σ₂ ∈ DoubleCoset.doubleCoset α
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  haveI : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet_ne⟩
  haveI : NeZero (Nat.gcd A.det.natAbs N) :=
    ⟨by rw [show Nat.gcd A.det.natAbs N = Int.gcd A.det N from rfl, hdet_coprime]
        exact one_ne_zero⟩
  haveI : (Gamma N).Normal := Gamma_normal N
  have h_top : Gamma N ⊔ Gamma A.det.natAbs = ⊤ := by
    have h := Gamma_gcd_eq_mul A.det.natAbs N
    rw [← Subgroup.map_sup] at h
    have := Subgroup.map_injective mapGL_injective h
    rw [show Nat.gcd A.det.natAbs N = Int.gcd A.det N from rfl,
      hdet_coprime, Gamma_one_top] at this
    rw [sup_comm]; exact this.symm
  obtain ⟨τ_N, hτ_N, τ_a, hτ_a, hσ₁_eq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (h_top ▸ Subgroup.mem_top σ₁)
  have hτ_N_Gamma0 : τ_N ∈ Gamma0 N := GammaN_le_Gamma0 N hτ_N
  have hτ10 : (N : ℤ) ∣ (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rwa [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ_N_Gamma0
  have hτ11 : (N : ℤ) ∣ ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
    rw [Gamma_mem] at hτ_N
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; simp [hτ_N.2.2.2])
  have hτ_ker : τ_a ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker := by
    rw [MonoidHom.mem_ker]; rwa [Gamma_mem'] at hτ_a
  obtain ⟨h_sl, hh_sl⟩ := conj_ker_mem_SLnZ 2 α A hA hAdet_ne τ_a hτ_ker
  set γ₂' := h_sl * σ₂
  have hx_eq' : mapGL ℚ σ₁ * α * mapGL ℚ σ₂ = mapGL ℚ τ_N * α * mapGL ℚ γ₂' := by
    rw [hσ₁_eq.symm, map_mul, map_mul, mul_assoc, mul_assoc, mul_assoc]
    congr 1; rw [← mul_assoc, show mapGL ℚ τ_a * α = α * mapGL ℚ h_sl from by rw [hh_sl]; group,
      mul_assoc]
  obtain ⟨hCN, hCco2⟩ := Gamma0_mul_apply_one_zero_and_gcd N
    (τ_N : Matrix (Fin 2) (Fin 2) ℤ) A hτ10 hτ11 hAN hAco2
  have hγ₂'_mem : γ₂' ∈ Gamma0 N := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine dvd_apply_one_zero_of_dvd_mul N _ (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) ?_ hCN hCco2
    obtain ⟨_, _, B, hB, hBN, _⟩ := hx_delta
    have hB_eq : B = (τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) :=
      Matrix.map_injective (Int.cast_injective)
        (hB.symm.trans (hx_eq' ▸ mapGL_mul_coe_eq_intMatrix τ_N γ₂' α A hA))
    rw [← hB_eq]; exact hBN
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨mapGL ℚ τ_N, Subgroup.mem_map_of_mem _ hτ_N_Gamma0,
    mapGL ℚ γ₂', Subgroup.mem_map_of_mem _ hγ₂'_mem, hx_eq'⟩

open CongruenceSubgroup in
/-- **Shimura Lemma 3.29(3)**: For `α ∈ Δ₀(N)` with `gcd(det(α), N) = 1`,
    the intersection of the full double coset `ΓαΓ` with `Δ₀(N)` equals the
    `Γ₀(N)`-double coset: `ΓαΓ ∩ Δ₀(N) = Γ₀(N)αΓ₀(N)`. -/
theorem doubleCoset_eq_of_Gamma0_coprimeDet
    (α : GL (Fin 2) ℚ) (hα : α ∈ Delta0_submonoid N)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (hdet_coprime : Int.gcd A.det N = 1) :
    DoubleCoset.doubleCoset α (SLnZ_subgroup 2) (SLnZ_subgroup 2) ∩
      (Delta0_submonoid N : Set (GL (Fin 2) ℚ)) =
    DoubleCoset.doubleCoset α
      ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) := by
  have hdet_pos := hα.2.1
  have hAdet_pos : 0 < A.det := by
    exact Int.cast_pos.mp (by rw [(det_intMat_cast 2 A).symm, ← hA]; exact hdet_pos)
  have hAco2 : Int.gcd (A 1 1) N = 1 :=
    gcd_A11_N_eq_one N A hAN hdet_coprime
  ext x; constructor
  · intro ⟨hx_dc, hx_delta⟩
    rw [DoubleCoset.mem_doubleCoset] at hx_dc
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx_dc
    obtain ⟨σ₁, rfl⟩ := hγ₁; obtain ⟨σ₂, rfl⟩ := hγ₂
    rw [SetLike.mem_coe] at hx_delta
    rw [hx_eq] at hx_delta ⊢
    exact mem_Gamma0_doubleCoset_of_mem_Delta0 N α A hA hAN hAco2
      (ne_of_gt hAdet_pos) hdet_coprime σ₁ σ₂ hx_delta
  · intro hx
    rw [DoubleCoset.mem_doubleCoset] at hx
    obtain ⟨δ₁, hδ₁, δ₂, hδ₂, hx_eq⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [DoubleCoset.mem_doubleCoset]
      obtain ⟨τ₁, _, rfl⟩ := Subgroup.mem_map.mp hδ₁
      obtain ⟨τ₂, _, rfl⟩ := Subgroup.mem_map.mp hδ₂
      exact ⟨mapGL ℚ τ₁, ⟨τ₁, rfl⟩, mapGL ℚ τ₂, ⟨τ₂, rfl⟩, hx_eq⟩
    · rw [hx_eq, SetLike.mem_coe]
      exact (Delta0_submonoid N).mul_mem ((Delta0_submonoid N).mul_mem
        (Gamma0_le_Delta0 N ((Subgroup.mem_toSubmonoid _ _).mpr hδ₁)) hα)
        (Gamma0_le_Delta0 N ((Subgroup.mem_toSubmonoid _ _).mpr hδ₂))

open CongruenceSubgroup in
omit [NeZero N] in
/-- `Γ₀(N)αΓ₀(N) ⊆ ΓαΓ`: the `Γ₀(N)`-double coset is contained in
    the `Γ`-double coset. Immediate from `Γ₀(N) ≤ Γ = SL₂(ℤ)`. -/
theorem Gamma0_doubleCoset_subset_Gamma (α : GL (Fin 2) ℚ) :
    DoubleCoset.doubleCoset α
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ⊆
    DoubleCoset.doubleCoset α (SLnZ_subgroup 2) (SLnZ_subgroup 2) := fun x hx ↦ by
  rw [DoubleCoset.mem_doubleCoset] at hx ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx
  exact ⟨γ₁, Gamma0_le_SLnZ N hγ₁, γ₂, Gamma0_le_SLnZ N hγ₂, hx_eq⟩

end FoundationLemmas

end HeckeRing.GLn
