/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_GLpair
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0

/-!
# The Hecke double coset `D_p` in `𝕋(Γ₀(N))`

Defines the Γ₀(N)-level double coset `Γ₀(N) · diag(1,p) · Γ₀(N)` and related
infrastructure. This is the basis element in the Hecke algebra `𝕋(Gamma0_pair N) ℤ`
whose image under `heckeRingHom_Gamma0 N k` is the Hecke operator `T_p` at
level Γ₀(N).

## Main definitions

* `D_p_Gamma0 N p hp` — the double coset `Γ₀(N) · diag(1,p) · Γ₀(N)`.
* `diag_1p_delta_Gamma0 N p hp` — `diag(1,p)` as an element of `Δ₀(N)`.

## Main results

* `HeckeCoset_deg_D_p_Gamma0` — the double coset has exactly `p + 1` left cosets.
* `T_p_upper_mem_D_p_Gamma0` — `T_p_upper(b) ∈ D_p_Gamma0` for all `b`.
* `T_p_lower_mem_D_p_Gamma0` — `T_p_lower ∈ D_p_Gamma0` for `gcd(p, N) = 1`.

## References

* Shimura, §3.4, Theorem 3.35.
* Diamond–Shurman, §5.2, Proposition 5.2.1.
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

/-- `diag(1,p)` lies in `Δ₀(N)` for any `N` and `p > 0`. -/
lemma diag_1p_mem_Delta0 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    diagMat 2 ![1, p] ∈ Delta0_submonoid N :=
  diagMat_mem_Delta0_of_gcd N ![1, p] (fun i ↦ by fin_cases i <;> simp [hp]) (by simp)

/-- `diag(1,p)` as an element of `(Gamma0_pair N).Δ`. -/
noncomputable def diag_1p_delta_Gamma0 (N p : ℕ) [NeZero N] (hp : 0 < p) : (Gamma0_pair N).Δ :=
  ⟨diagMat 2 ![1, p], diag_1p_mem_Delta0 N p hp⟩

@[simp] lemma diag_1p_delta_Gamma0_val (N p : ℕ) [NeZero N] (hp : 0 < p) :
    (diag_1p_delta_Gamma0 N p hp : GL (Fin 2) ℚ) = diagMat 2 ![1, p] := rfl

/-- The double coset `Γ₀(N) · diag(1,p) · Γ₀(N)` in `Gamma0_pair N`.
This is the Hecke double coset representing the operator `T_p` at level `Γ₀(N)`. -/
noncomputable def D_p_Gamma0 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    HeckeRing.HeckeCoset (Gamma0_pair N) :=
  ⟦diag_1p_delta_Gamma0 N p hp⟧

/-- The Γ₀(N)-double coset degree of `diag(1,p)` is `p + 1` for `p` prime
coprime to `N`: the `decompQuot` has exactly `p + 1` elements. -/
lemma HeckeCoset_deg_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) : Nat.card (HeckeRing.decompQuot (Gamma0_pair N)
      (HeckeRing.HeckeCoset.rep (D_p_Gamma0 N p hp.pos))) = p + 1 := by
  have h_deg := HeckeCoset_deg_Gamma0_one_ppow N p hp hpN 1 one_pos
  simp only [pow_one, HeckeRing.HeckeCoset_deg, Nat.sub_self, pow_zero, one_mul] at h_deg
  have h_eq : D_p_Gamma0 N p hp.pos =
      T_diag_Gamma0 N ![1, p] (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp) := rfl
  rw [Nat.card_eq_fintype_card, h_eq]
  exact_mod_cast h_deg

/-- Any `g` factoring as `s · diag(1,p) · t` with `s, t ∈ Γ₀(N)` lies in `D_p_Gamma0`. -/
lemma mem_D_p_Gamma0_of_factor_through_diag (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p)
    (g s t : GL (Fin 2) ℚ) (hs : s ∈ (Gamma0_pair N).H) (ht : t ∈ (Gamma0_pair N).H)
    (hfact : g = s * (diag_1p_delta_Gamma0 N p hp : GL (Fin 2) ℚ) * t) :
    g ∈ HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp) :=
  DoubleCoset.mem_doubleCoset.mpr ⟨s, hs, t, ht, hfact⟩

private lemma T_p_lower_factor_through_diag_1p (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) : ∃ (s : GL (Fin 2) ℚ) (_ : s ∈ (Gamma0_pair N).H)
      (t : GL (Fin 2) ℚ) (_ : t ∈ (Gamma0_pair N).H), (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
        s * (diag_1p_delta_Gamma0 N p hp.pos : GL (Fin 2) ℚ) * t := by
  obtain ⟨u, v, h_bezout⟩ := hpN.isCoprime
  set σ : SL(2, ℤ) := ⟨!![(p : ℤ), -v; (N : ℤ), u], by grind [det_fin_two_of]⟩
  set τ : SL(2, ℤ) := ⟨!![u * p, v; -(N : ℤ), 1], by grind [det_fin_two_of]⟩
  refine ⟨mapGL ℚ σ, Subgroup.mem_map_of_mem _ (by simp [Gamma0_mem, σ]),
    mapGL ℚ τ, Subgroup.mem_map_of_mem _ (by simp [Gamma0_mem, τ]), ?_⟩
  have h_bezout_Q : (u : ℚ) * p + (v : ℚ) * N = 1 := by exact_mod_cast h_bezout
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ, τ, Matrix.mul_apply, Fin.sum_univ_two, Fin.forall_fin_two, hp.pos] <;> grind

/-- Membership of `T_p_upper(b)` in the Γ₀(N)-double coset `D_p_Gamma0`, via the
factorization `T_p_upper(b) = diag(1,p) · σ_b` with `σ_b = [[1,b],[0,1]] ∈ Γ₀(N)`. -/
lemma T_p_upper_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∈
      HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  set σ_b : SL(2, ℤ) := ⟨!![1, (b : ℤ); 0, 1], by simp [det_fin_two]⟩
  refine mem_D_p_Gamma0_of_factor_through_diag N p hp.pos _ 1 (mapGL ℚ σ_b) (one_mem _)
    (Subgroup.mem_map_of_mem _ (by simp [Gamma0_mem, σ_b])) ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ_b, Matrix.mul_apply, Fin.sum_univ_two, Fin.forall_fin_two, hp.pos]

/-- Membership of `T_p_lower` in the Γ₀(N)-double coset `D_p_Gamma0`, via the Bezout
factorization `T_p_lower = σ · diag(1,p) · τ` with `σ, τ ∈ Γ₀(N)`. -/
lemma T_p_lower_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) : (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∈
      HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  obtain ⟨s, hs, t, ht, hfact⟩ := T_p_lower_factor_through_diag_1p N p hp hpN
  exact mem_D_p_Gamma0_of_factor_through_diag N p hp.pos _ s t hs ht hfact

/-- Inclusion `(Gamma0_pair N).H ≤ (GL_pair 2).H = SLnZ_subgroup 2`. Γ₀(N) is the
image of the inclusion `Γ₀(N) ↪ SL₂(ℤ)` under `mapGL`. -/
lemma Gamma0_pair_H_le_GL_pair_H (N : ℕ) [NeZero N] : (Gamma0_pair N).H ≤ (GL_pair 2).H :=
  Subgroup.map_le_range _ _

end HeckeRing.GL2
