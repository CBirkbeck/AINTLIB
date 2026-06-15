/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke

/-!
# Generalized Hecke Action for Arbitrary Hecke Pairs

Ports the Hecke action from `GL_pair 2` (level-1) to arbitrary
`P : HeckePair (GL (Fin 2) ℚ)`, parameterized by a `HeckePairAction P` instance
that guarantees positive determinant for elements of `P.Δ`.

Uses the **adjugate anti-involution** instead of transpose, so that congruence
subgroups like `Γ₁(N)` also satisfy `HeckePairAction`. For 2×2 matrices,
`adj([[a,b],[c,d]]) = [[d,-b],[-c,a]]`, which preserves `Γ₁(N)` because
`a ≡ 1, c ≡ 0 (mod N)` implies `d ≡ 1, -c ≡ 0 (mod N)` when `det = 1`.

## Main definitions

* `GL_adjugate` -- the adjugate map `GL₂(ℚ) → GL₂(ℚ)`
* `HeckePairAction` -- typeclass requiring `∀ g : P.Δ, 0 < det(glMap g)`
    and `adjugate_mem_H : ∀ h ∈ P.H, GL_adjugate h ∈ P.H`
* `tRep_gen` -- adjugated right-coset representative, generalized
* `heckeSlash_gen` -- Hecke slash action of a double coset, generalized
* `heckeSlashExt_gen` -- Hecke slash extended by linearity to `𝕋 P ℤ`

## Main results

* `heckeSlash_gen_slash_invariant` -- the Hecke slash preserves P.H-invariance
* `heckeSlash_gen_comp` -- composition corresponds to Hecke algebra multiplication
* `heckeSlash_gen_comm` -- commutativity when `𝕋 P ℤ` is commutative

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §§3.4
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise CongruenceSubgroup
open HeckeRing DoubleCoset HeckeRing.GLn HeckeRing.GL2
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane

namespace HeckeRing.GL2

/-- The adjugate of a `GL₂(ℚ)` element, as a `GL₂(ℚ)` element.
For a 2×2 matrix `[[a,b],[c,d]]`, this is `[[d,-b],[-c,a]]`. -/
noncomputable def GL_adjugate (g : GL (Fin 2) ℚ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.adjugate g.val) (by
    rw [Matrix.det_adjugate, Fintype.card_fin]; simpa using g.det_ne_zero)

@[simp]
lemma GL_adjugate_val (g : GL (Fin 2) ℚ) :
    (GL_adjugate g).val = Matrix.adjugate g.val := rfl

/-- The adjugate is anti-multiplicative: `adj(g₁ g₂) = adj(g₂) adj(g₁)`. -/
lemma GL_adjugate_mul (g₁ g₂ : GL (Fin 2) ℚ) :
    GL_adjugate (g₁ * g₂) = GL_adjugate g₂ * GL_adjugate g₁ := by
  ext
  simp [Units.val_mul, adjugate_mul_distrib]

/-- The adjugate is involutive for 2×2 matrices: `adj(adj(g)) = g`. -/
lemma GL_adjugate_involutive (g : GL (Fin 2) ℚ) :
    GL_adjugate (GL_adjugate g) = g := by
  ext
  simp [adjugate_adjugate _ (by simp : Fintype.card (Fin 2) ≠ 1)]

/-- For a `GL₂` element with `det = 1`, the adjugate equals the inverse. -/
lemma GL_adjugate_eq_inv_of_det_one (g : GL (Fin 2) ℚ) (hdet : g.val.det = 1) :
    GL_adjugate g = g⁻¹ := by
  apply Units.ext
  simp [GL_adjugate_val, Matrix.inv_def, hdet, Ring.inverse_one]

private lemma SLnZ_det_one (g : GL (Fin 2) ℚ) (hg : g ∈ SLnZ_subgroup 2) :
    g.val.det = 1 := by
  rw [MonoidHom.mem_range] at hg
  obtain ⟨σ, rfl⟩ := hg
  simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom]
  exact_mod_cast σ.prop

/-- The adjugate preserves `SLnZ_subgroup 2`. -/
lemma GL_adjugate_mem_SLnZ {g : GL (Fin 2) ℚ} (hg : g ∈ SLnZ_subgroup 2) :
    GL_adjugate g ∈ SLnZ_subgroup 2 := by
  rw [GL_adjugate_eq_inv_of_det_one g (SLnZ_det_one g hg)]
  exact (SLnZ_subgroup 2).inv_mem hg

/-- For any subgroup `Γ` of `GL₂(ℚ)` contained in the image of `SL₂(ℤ)` under `mapGL ℚ`,
the adjugate restricts to `Γ` (since `Γ ⊆ SL₂(ℤ)` implies det = 1, so adj = inv ∈ Γ). -/
private lemma GL_adjugate_mem_of_le_SLnZ {Γ : Subgroup (GL (Fin 2) ℚ)}
    (hΓ : Γ ≤ SLnZ_subgroup 2) {h : GL (Fin 2) ℚ} (hh : h ∈ Γ) :
    GL_adjugate h ∈ Γ := by
  rw [GL_adjugate_eq_inv_of_det_one h (SLnZ_det_one h (hΓ hh))]
  exact Γ.inv_mem hh

/-- A Hecke pair `P` inside `GL₂(ℚ)` whose `Δ`-elements have positive real determinant
and whose `H` is closed under the adjugate anti-involution. -/
class HeckePairAction (P : HeckePair (GL (Fin 2) ℚ)) where
  det_pos : ∀ g : P.Δ, 0 < (glMap (g : GL _ ℚ)).det.val
  adjugate_mem_H : ∀ h, h ∈ P.H → GL_adjugate h ∈ P.H

private lemma glMap_det_val_aux (g : GL (Fin 2) ℚ) :
    (glMap g).det.val = algebraMap ℚ ℝ g.det.val :=
  congr_arg Units.val (GeneralLinearGroup.map_det _ g)

noncomputable instance : HeckePairAction (GL_pair 2) where
  det_pos g := by
    rw [glMap_det_val_aux, GeneralLinearGroup.val_det_apply]
    exact Rat.cast_pos.mpr g.prop.2
  adjugate_mem_H h hh := GL_adjugate_mem_SLnZ hh

/-- Det-positivity for `Gamma1_pair`. -/
theorem Gamma1_pair_det_pos (N : ℕ) [NeZero N] (g : (Gamma1_pair N).Δ) :
    0 < (glMap (g : GL _ ℚ)).det.val := by
  obtain ⟨_, hdet, _⟩ : (g : GL _ ℚ) ∈ Delta1_submonoid N := g.prop
  rw [glMap_det_val_aux, GeneralLinearGroup.val_det_apply]
  exact Rat.cast_pos.mpr hdet

/-- `Gamma1_pair N` satisfies `HeckePairAction`: the adjugate preserves `Γ₁(N)`
because for elements of determinant 1, the adjugate equals the inverse, and
`Γ₁(N)` is a subgroup (hence closed under inversion). -/
noncomputable instance (N : ℕ) [NeZero N] : HeckePairAction (Gamma1_pair N) where
  det_pos := Gamma1_pair_det_pos N
  adjugate_mem_H _ hh := GL_adjugate_mem_of_le_SLnZ
    (Subgroup.map_le_range (mapGL ℚ) (Gamma1 N)) hh

/-- Det-positivity for `Gamma0_pair N`. -/
theorem Gamma0_pair_det_pos (N : ℕ) [NeZero N] (g : (HeckeRing.GLn.Gamma0_pair N).Δ) :
    0 < (glMap (g : GL _ ℚ)).det.val := by
  obtain ⟨_, hdet, _⟩ := g.prop
  rw [glMap_det_val_aux, GeneralLinearGroup.val_det_apply]
  exact Rat.cast_pos.mpr hdet

/-- `Gamma0_pair N` satisfies `HeckePairAction`: `Γ₀(N) ⊆ SL₂(ℤ)` and `adj` on
`SL₂(ℤ)` equals inversion (since `det = 1`), so `adj(γ) ∈ Γ₀(N)` because `Γ₀(N)`
is a subgroup. -/
noncomputable instance (N : ℕ) [NeZero N] : HeckePairAction (HeckeRing.GLn.Gamma0_pair N) where
  det_pos := Gamma0_pair_det_pos N
  adjugate_mem_H _ hh := GL_adjugate_mem_of_le_SLnZ
    (Subgroup.map_le_range (mapGL ℚ) (Gamma0 N)) hh

section DetPositivity

variable {P : HeckePair (GL (Fin 2) ℚ)} [HeckePairAction P]

private lemma glMap_adjugate_det_val_gen (g : GL (Fin 2) ℚ) :
    (glMap (GL_adjugate g)).det.val = (glMap g).det.val := by
  rw [glMap_det_val_aux, glMap_det_val_aux]
  congr 1
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GL_adjugate_val, Matrix.det_adjugate, Fintype.card_fin, pow_one]

private lemma delta_det_pos_real_gen (g : P.Δ) :
    0 < (glMap (g : GL (Fin 2) ℚ)).det.val :=
  HeckePairAction.det_pos g

private lemma H_det_pos_gen (σ : P.H) :
    0 < (glMap (σ : GL (Fin 2) ℚ)).det.val :=
  delta_det_pos_real_gen ⟨σ, P.h₀ σ.prop⟩

private lemma cosetRep_delta_det_pos_gen (σ : P.H) (g : P.Δ) :
    0 < (glMap ((σ : GL (Fin 2) ℚ) * (g : GL (Fin 2) ℚ))).det.val := by
  rw [map_mul, map_mul, Units.val_mul]
  exact mul_pos (H_det_pos_gen σ) (delta_det_pos_real_gen g)

private lemma cosetRep_delta_adjugate_det_pos_gen (σ : P.H) (g : P.Δ) :
    0 < (glMap (GL_adjugate
      ((σ : GL (Fin 2) ℚ) * (g : GL (Fin 2) ℚ)))).det.val := by
  rw [glMap_adjugate_det_val_gen]; exact cosetRep_delta_det_pos_gen σ g

private lemma sigma_eq_id_of_pos_det_gen {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    UpperHalfPlane.σ g = ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ; simp only [hg, ↓reduceIte]

end DetPositivity

section Definitions

variable (P : HeckePair (GL (Fin 2) ℚ))

/-- The adjugated right-coset representative for an arbitrary Hecke pair:
`adj(σᵢ * δ)`. Since adjugate is anti-multiplicative, this equals `adj(δ) * adj(σᵢ)`,
converting right cosets to left cosets. -/
noncomputable abbrev tRep_gen
    (D : HeckeCoset P) (i : decompQuot P (HeckeCoset.rep D)) : GL (Fin 2) ℚ :=
  GL_adjugate
    ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ))

/-- The Hecke slash action of a double coset `D` on a function `f : ℍ → ℂ`, for an
arbitrary Hecke pair `P`, via left coset representatives `T_k(D)(f) = Σᵢ f ∣[k] adj(σᵢδ)`
(Shimura Prop 3.30). -/
noncomputable def heckeSlash_gen [HeckePairAction P] (k : ℤ)
    (D : HeckeCoset P) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot P (HeckeCoset.rep D), f ∣[k] tRep_gen P D i

/-- The extended Hecke slash action: extends `heckeSlash_gen` by ℤ-linearity from single
double cosets to formal sums `𝕋 P ℤ`. -/
noncomputable def heckeSlashExt_gen [HeckePairAction P] (k : ℤ)
    (T : 𝕋 P ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum (fun D c ↦ c • heckeSlash_gen P k D f)

end Definitions

section BasicLemmas

variable {P : HeckePair (GL (Fin 2) ℚ)} [HeckePairAction P]

/-- The generalized Hecke slash distributes over addition. -/
lemma heckeSlash_gen_add (k : ℤ) (D : HeckeCoset P) (f g : ℍ → ℂ) :
    heckeSlash_gen P k D (f + g) = heckeSlash_gen P k D f + heckeSlash_gen P k D g := by
  simp [heckeSlash_gen, SlashAction.add_slash, Finset.sum_add_distrib]

/-- The generalized Hecke slash sends zero to zero. -/
@[simp] lemma heckeSlash_gen_zero (k : ℤ) (D : HeckeCoset P) :
    heckeSlash_gen P k D 0 = 0 := by
  simp [heckeSlash_gen, SlashAction.zero_slash, Finset.sum_const_zero]

/-- The generalized Hecke slash commutes with scalar multiplication. -/
lemma heckeSlash_gen_smul (k : ℤ) (D : HeckeCoset P) (c : ℂ) (f : ℍ → ℂ) :
    heckeSlash_gen P k D (c • f) = c • heckeSlash_gen P k D f := by
  simp only [heckeSlash_gen, Finset.smul_sum]
  congr 1
  ext i
  change ((c • f) ∣[k] glMap _) _ = (c • (f ∣[k] glMap _)) _
  rw [ModularForm.smul_slash, sigma_eq_id_of_pos_det_gen
    (cosetRep_delta_adjugate_det_pos_gen ⟨i.out, SetLike.coe_mem _⟩ (HeckeCoset.rep D))]
  simp

end BasicLemmas

section SlashInvariance

variable {P : HeckePair (GL (Fin 2) ℚ)} [HeckePairAction P]

private noncomputable def leftMulQuot_gen (D : HeckeCoset P) (σ : P.H) :
    decompQuot P (HeckeCoset.rep D) →
    decompQuot P (HeckeCoset.rep D) :=
  fun i ↦ ⟦⟨σ * i.out, P.H.mul_mem σ.prop (SetLike.coe_mem _)⟩⟧

omit [HeckePairAction P] in
private lemma leftMulQuot_gen_injective (D : HeckeCoset P) (σ : P.H) :
    Function.Injective (leftMulQuot_gen D σ) := by
  intro i₁ i₂ h
  simp only [leftMulQuot_gen] at h
  by_contra hne
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at h_K
  simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
  have h_mem : (HeckeCoset.rep D : GL _ ℚ)⁻¹ *
      ((i₁.out : GL _ ℚ)⁻¹ * (i₂.out : GL _ ℚ)) *
      (HeckeCoset.rep D : GL _ ℚ) ∈ P.H := by
    convert h_K using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  refine decompQuot_coset_diff P (HeckeCoset.rep D) i₁ i₂ hne
    (leftCoset_eq_of_not_disjoint P.H _ _ ?_)
  rw [Set.not_disjoint_iff]
  refine ⟨(i₂.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ), ?_, ?_⟩
  · rw [smul_eq_singleton_mul]
    exact ⟨_, rfl, _, h_mem, by group⟩
  · rw [smul_eq_singleton_mul]
    exact ⟨_, rfl, 1, P.H.one_mem, by group⟩

private noncomputable def leftMulEquiv_gen (D : HeckeCoset P) (σ : P.H) :
    decompQuot P (HeckeCoset.rep D) ≃
    decompQuot P (HeckeCoset.rep D) :=
  Equiv.ofBijective _ ⟨leftMulQuot_gen_injective D σ,
    Finite.surjective_of_injective (leftMulQuot_gen_injective D σ)⟩

private lemma heckeSlash_gen_slash (k : ℤ) (D : HeckeCoset P) (f : ℍ → ℂ)
    (g : GL (Fin 2) ℚ) : (heckeSlash_gen P k D f) ∣[k] g =
    ∑ i : decompQuot P (HeckeCoset.rep D), (f ∣[k] tRep_gen P D i) ∣[k] g := by
  simp only [heckeSlash_gen]
  induction Finset.univ (α := decompQuot P (HeckeCoset.rep D))
      using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp [Finset.sum_cons, SlashAction.add_slash, ih]

private lemma slash_left_H_adjugate_mul_gen (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f) (h : GL (Fin 2) ℚ)
    (hh : h ∈ P.H) (g : GL (Fin 2) ℚ) :
    f ∣[k] (GL_adjugate h * g) = f ∣[k] g := by
  change f ∣[k] glMap (GL_adjugate h * g) = f ∣[k] glMap g
  rw [map_mul, SlashAction.slash_mul]
  congr 1
  exact hf _ (HeckePairAction.adjugate_mem_H h hh)

omit [HeckePairAction P] in
private lemma h_coset_mem_H_gen (D : HeckeCoset P)
    (q : decompQuot P (HeckeCoset.rep D)) (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ P.H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ P.H)
    (hq : (⟦q.out⟧ : decompQuot P (HeckeCoset.rep D)) = ⟦⟨h₁, hh₁⟩⟧) :
    ((HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
      (HeckeCoset.rep D : GL _ ℚ) * h₂) ∈ P.H := by
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at h_K
  simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
  exact P.H.mul_mem (by
    convert h_K using 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]) hh₂

omit [HeckePairAction P] in
private lemma adjugate_decomp_eq_gen (D : HeckeCoset P)
    (q : decompQuot P (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) :
    GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) =
    GL_adjugate ((HeckeCoset.rep D : GL _ ℚ)⁻¹ *
      ((q.out : GL _ ℚ)⁻¹ * h₁) *
      (HeckeCoset.rep D : GL _ ℚ) * h₂) * tRep_gen P D q := by
  simp only [tRep_gen]
  rw [← GL_adjugate_mul]
  congr 1
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Slashing by the adjugate of `h₁ * delta * h₂` with `h₁, h₂ ∈ P.H` equals slashing
by `tRep_gen D ⟦h₁⟧`, using P.H-invariance (generalized). -/
lemma slash_tRep_gen_of_mem (k : ℤ) (D : HeckeCoset P) (h₁ h₂ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ P.H) (hh₂ : h₂ ∈ P.H) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f) :
    f ∣[k] (GL_adjugate (h₁ * (HeckeCoset.rep D : GL (Fin 2) ℚ) * h₂)) =
    f ∣[k] tRep_gen P D ⟦⟨h₁, hh₁⟩⟧ := by
  set q : decompQuot P (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  rw [adjugate_decomp_eq_gen D q h₁ h₂]
  exact slash_left_H_adjugate_mul_gen k f hf _
    (h_coset_mem_H_gen D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq _)) _

omit [HeckePairAction P] in
/-- Anti-homomorphism: `tRep_gen D₂ j * tRep_gen D₁ i = adj(σᵢδ₁ · σⱼδ₂)`. -/
lemma tRep_gen_mul_anti (D₁ D₂ : HeckeCoset P) (i : decompQuot P (HeckeCoset.rep D₁))
    (j : decompQuot P (HeckeCoset.rep D₂)) :
    tRep_gen P D₂ j * tRep_gen P D₁ i =
    GL_adjugate ((i.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((j.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ))) := by
  rw [← GL_adjugate_mul]

private lemma slash_tRep_gen_mul_eq_perm (k : ℤ) (D : HeckeCoset P) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f) (σ_Q : GL (Fin 2) ℚ) (hσ : σ_Q ∈ P.H)
    (i : decompQuot P (HeckeCoset.rep D)) :
    (f ∣[k] tRep_gen P D i) ∣[k] σ_Q = f ∣[k] tRep_gen P D
      (leftMulEquiv_gen D ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩ i) := by
  set σ_QA : P.H := ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩
  rw [(SlashAction.slash_mul k (tRep_gen P D i) σ_Q f).symm]
  change f ∣[k] (tRep_gen P D i * σ_Q) = _
  conv_lhs =>
    rw [show tRep_gen P D i * σ_Q = GL_adjugate
      (GL_adjugate σ_Q * (i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)) from by
      change GL_adjugate _ * σ_Q = _
      conv_lhs =>
        rw [show σ_Q = GL_adjugate (GL_adjugate σ_Q) from
          (GL_adjugate_involutive σ_Q).symm, ← GL_adjugate_mul]
        rfl
      rw [show GL_adjugate σ_Q * (i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ) =
        GL_adjugate σ_Q * ((i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)) from by group]]
  rw [show σ_QA.val * ↑i.out * (HeckeCoset.rep D : GL _ ℚ) =
      σ_QA.val * ↑i.out * (HeckeCoset.rep D : GL _ ℚ) * 1 from (mul_one _).symm]
  exact slash_tRep_gen_of_mem k D _ 1
    (P.H.mul_mem σ_QA.prop (SetLike.coe_mem _)) P.H.one_mem f hf

/-- The Hecke slash action preserves P.H-invariance (Shimura Prop 3.30, generalized). -/
lemma heckeSlash_gen_slash_invariant (k : ℤ) (D : HeckeCoset P) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f) (σ_Q : GL (Fin 2) ℚ)
    (hσ : σ_Q ∈ P.H) :
    (heckeSlash_gen P k D f) ∣[k] σ_Q = heckeSlash_gen P k D f := by
  set σ_QA : P.H := ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩
  set π := leftMulEquiv_gen D σ_QA
  rw [heckeSlash_gen_slash,
    Finset.sum_congr rfl (fun i _ ↦ slash_tRep_gen_mul_eq_perm k D f hf σ_Q hσ i),
    Fintype.sum_equiv π _ (fun i ↦ f ∣[k] tRep_gen P D i) (fun _ ↦ rfl)]
  rfl

end SlashInvariance

section FiberSum

variable {P : HeckePair (GL (Fin 2) ℚ)} [HeckePairAction P]

private lemma slash_and_coset_of_mulMap_eq_gen (k : ℤ) (D₁ D₂ D : HeckeCoset P)
    (f : ℍ → ℂ) (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f)
    (p : decompQuot P (HeckeCoset.rep D₁) ×
         decompQuot P (HeckeCoset.rep D₂))
    (hp : mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D) :
    ∃ q : decompQuot P (HeckeCoset.rep D),
      (f ∣[k] (tRep_gen P D₂ p.2 * tRep_gen P D₁ p.1) =
        f ∣[k] tRep_gen P D q) ∧
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      (P.H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      (P.H : Set (GL (Fin 2) ℚ)) := by
  have hmem : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈ HeckeCoset.toSet D := by
    rw [← hp]
    change _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset P)
    simp only [HeckeCoset.toSet_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hmem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hmem
  set q : decompQuot P (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  refine ⟨q, ?_, ?_⟩
  · rw [tRep_gen_mul_anti D₁ D₂ p.1 p.2, heq]
    exact slash_tRep_gen_of_mem k D _ h₂ hh₁ hh₂ f hf
  · have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact (Quotient.out_eq q))
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at h_K
    simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
    set κ := (HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
        (HeckeCoset.rep D : GL _ ℚ)
    rw [Set.singleton_mul_singleton, heq]
    apply leftCoset_eq_of_not_disjoint
    rw [Set.not_disjoint_iff]
    exact ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
      ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩,
      ⟨κ * h₂, P.H.mul_mem h_K hh₂, by simp only [smul_eq_mul, κ]; group⟩⟩

omit [HeckePairAction P] in
private lemma prod_mem_D_of_rightCoset_gen (D : HeckeCoset P) (g : GL (Fin 2) ℚ)
    (q : decompQuot P (HeckeCoset.rep D)) (h : GL (Fin 2) ℚ)
    (hh : h ∈ (P.H : Set (GL (Fin 2) ℚ)))
    (hprod : g = (q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ) * h) :
    g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  exact ⟨(q.out : GL (Fin 2) ℚ), SetLike.coe_mem q.out, h, hh, hprod⟩

omit [HeckePairAction P] in
private lemma prod_mem_mulMap_gen (D₁ D₂ : HeckeCoset P)
    (p : decompQuot P (HeckeCoset.rep D₁) × decompQuot P (HeckeCoset.rep D₂)) :
    (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet (mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2)) := by
  change _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset P)
  simp only [HeckeCoset.toSet_mk]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

omit [HeckePairAction P] in
private lemma mulMap_eq_of_rightCoset_gen (D₁ D₂ D : HeckeCoset P)
    (p : decompQuot P (HeckeCoset.rep D₁) × decompQuot P (HeckeCoset.rep D₂))
    (q : decompQuot P (HeckeCoset.rep D))
    (hp_rc : ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      (P.H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} * (P.H : Set (GL (Fin 2) ℚ))) :
    mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D := by
  have h_in_rc : (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      ({(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
      (P.H : Set (GL (Fin 2) ℚ)) := by
    rw [← hp_rc, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, P.H.one_mem, by simp only [mul_one]⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in_rc
  rw [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  refine HeckeCoset_ext_toSet (P := P) ?_
  rw [HeckeCoset.toSet_eq_rep, HeckeCoset.toSet_eq_rep]
  refine DoubleCoset.eq_of_not_disjoint ?_
  rw [Set.not_disjoint_iff]
  have hm := prod_mem_mulMap_gen D₁ D₂ p
  rw [HeckeCoset.toSet_eq_rep] at hm
  have hd := prod_mem_D_of_rightCoset_gen D _ q h hh hprod.symm
  rw [HeckeCoset.toSet_eq_rep] at hd
  exact ⟨_, hm, hd⟩

open scoped Classical in
omit [HeckePairAction P] in
private lemma fiber_card_eq_gen (D₁ D₂ D : HeckeCoset P)
    (q_of : decompQuot P (HeckeCoset.rep D₁) ×
        decompQuot P (HeckeCoset.rep D₂) → decompQuot P (HeckeCoset.rep D))
    (S : Finset (decompQuot P (HeckeCoset.rep D₁) ×
        decompQuot P (HeckeCoset.rep D₂)))
    (hS : ∀ p, p ∈ S ↔
      mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D)
    (h_coset_eq : ∀ p,
      mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        (P.H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        (P.H : Set (GL (Fin 2) ℚ)))
    (h_unique : ∀ p (q : decompQuot P (HeckeCoset.rep D)),
      mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      (({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        (P.H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        (P.H : Set (GL (Fin 2) ℚ))) → q_of p = q)
    (q : decompQuot P (HeckeCoset.rep D)) :
    (S.filter (fun p ↦ q_of p = q)).card = Nat.card
      {p : decompQuot P (HeckeCoset.rep D₁) ×
           decompQuot P (HeckeCoset.rep D₂) |
        ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        (P.H : Set (GL (Fin 2) ℚ)) =
        {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        (P.H : Set (GL (Fin 2) ℚ))} := by
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact {
    toFun := fun ⟨p, hp⟩ ↦ ⟨p, by
      simp only [Finset.mem_filter] at hp
      rw [← hp.2]; exact h_coset_eq p ((hS p).mp hp.1)⟩
    invFun := fun ⟨p, hp_rc⟩ ↦ ⟨p, by
      have hmap := mulMap_eq_of_rightCoset_gen D₁ D₂ D p q hp_rc
      rw [Finset.mem_filter, hS]
      exact ⟨hmap, h_unique p q hmap hp_rc⟩⟩
    left_inv := fun ⟨_, _⟩ ↦ rfl
    right_inv := fun ⟨_, _⟩ ↦ rfl }

private lemma heckeSlash_gen_fiber_sum [DecidableEq (HeckeCoset P)] (k : ℤ)
    (D₁ D₂ D : HeckeCoset P)
    (_hD : D ∈ mulSupport P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
    (f : ℍ → ℂ) (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot P (HeckeCoset.rep D₁) ×
                 decompQuot P (HeckeCoset.rep D₂) ↦
          mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D),
      f ∣[k] (tRep_gen P D₂ p.2 * tRep_gen P D₁ p.1)) =
    (m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D •
      ∑ q : decompQuot P (HeckeCoset.rep D),
        f ∣[k] tRep_gen P D q := by
  classical
  have h_main := slash_and_coset_of_mulMap_eq_gen k D₁ D₂ D f hf
  set q_of : decompQuot P (HeckeCoset.rep D₁) ×
      decompQuot P (HeckeCoset.rep D₂) →
      decompQuot P (HeckeCoset.rep D) := fun p ↦
    if h : mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D
    then (h_main p h).choose else ⟦1⟧
  have h_slash_eq : ∀ p,
      mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      f ∣[k] (tRep_gen P D₂ p.2 * tRep_gen P D₁ p.1) =
        f ∣[k] tRep_gen P D (q_of p) := by
    intro p hp
    simp only [q_of, hp, dif_pos]
    exact (h_main p hp).choose_spec.1
  set S := Finset.univ.filter (fun p : decompQuot P (HeckeCoset.rep D₁) ×
      decompQuot P (HeckeCoset.rep D₂) ↦
      mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D)
  rw [Finset.sum_congr rfl (fun p hp ↦ by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact h_slash_eq p hp)]
  rw [← Finset.sum_fiberwise (s := S) (g := q_of)]
  conv_lhs =>
    arg 2
    ext q
    rw [Finset.sum_congr rfl (fun p hp ↦ by
      simp only [Finset.mem_filter] at hp
      rw [hp.2])]
    rw [Finset.sum_const]
  have h_fiber_eq := fiber_card_eq_gen D₁ D₂ D q_of S
    (fun p ↦ by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and])
    (fun p hp ↦ by
      simp only [q_of, hp, dif_pos]
      exact (h_main p hp).choose_spec.2)
    (fun p q hmap hp_rc ↦ by
      simp only [q_of, hmap, dif_pos]
      set q' := (h_main p hmap).choose
      by_contra hne
      exact decompQuot_coset_diff P (HeckeCoset.rep D) q' q hne
        ((h_main p hmap).choose_spec.2.symm.trans hp_rc))
  simp_rw [h_fiber_eq,
    heckeMultiplicity_uniform P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D]
  set n := Nat.card
    {p : decompQuot P (HeckeCoset.rep D₁) ×
         decompQuot P (HeckeCoset.rep D₂) |
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      (P.H : Set (GL (Fin 2) ℚ)) =
      {(HeckeCoset.rep D : GL _ ℚ)} * (P.H : Set (GL (Fin 2) ℚ))}
  rw [show ∑ x : decompQuot P (HeckeCoset.rep D), n • f ∣[k] tRep_gen P D x =
      n • ∑ x, f ∣[k] tRep_gen P D x from Finset.sum_nsmul _ _ _]
  simp only [m, Finsupp.coe_mk, heckeMultiplicity, n, Nat.cast_smul_eq_nsmul ℤ]

end FiberSum

section HeckeAlgebraAction

variable {P : HeckePair (GL (Fin 2) ℚ)} [HeckePairAction P]

omit [HeckePairAction P] in
private lemma sum_slash_eq_swap (k : ℤ) (D₁ D₂ : HeckeCoset P) (f : ℍ → ℂ) :
    (∑ i : decompQuot P (HeckeCoset.rep D₁),
        (∑ j : decompQuot P (HeckeCoset.rep D₂), f ∣[k] tRep_gen P D₂ j)
          ∣[k] tRep_gen P D₁ i) =
      ∑ i, ∑ j, (f ∣[k] tRep_gen P D₂ j) ∣[k] tRep_gen P D₁ i := by
  congr 1
  ext i
  induction Finset.univ (α := decompQuot P (HeckeCoset.rep D₂))
      using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp [Finset.sum_cons, SlashAction.add_slash]

omit [HeckePairAction P] in
private lemma slash_tRep_gen_mul (k : ℤ) (D₁ D₂ : HeckeCoset P) (f : ℍ → ℂ)
    (i : decompQuot P (HeckeCoset.rep D₁)) (j : decompQuot P (HeckeCoset.rep D₂)) :
    (f ∣[k] tRep_gen P D₂ j) ∣[k] tRep_gen P D₁ i =
      f ∣[k] (tRep_gen P D₂ j * tRep_gen P D₁ i) := by
  change (f ∣[k] glMap (tRep_gen P D₂ j)) ∣[k] glMap (tRep_gen P D₁ i) =
    f ∣[k] glMap (tRep_gen P D₂ j * tRep_gen P D₁ i)
  rw [map_mul, ← SlashAction.slash_mul]

private lemma heckeSlashExt_gen_mul_T_single (k : ℤ) (D₁ D₂ : HeckeCoset P)
    (f : ℍ → ℂ) :
    heckeSlashExt_gen P k (T_single P ℤ D₂ 1 * T_single P ℤ D₁ 1) f =
      (m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
        (fun D c ↦ c • heckeSlash_gen P k D f) := by
  unfold heckeSlashExt_gen
  rw [mul_singleton_𝕋]
  simp

private lemma heckeSlash_gen_comp_sum_eq (k : ℤ) (D₁ D₂ : HeckeCoset P) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f) :
    (∑ p : decompQuot P (HeckeCoset.rep D₁) × decompQuot P (HeckeCoset.rep D₂),
        f ∣[k] (tRep_gen P D₂ p.2 * tRep_gen P D₁ p.1)) =
      (m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).sum
        (fun D c ↦ c • heckeSlash_gen P k D f) := by
  letI : DecidableEq (HeckeCoset P) := Classical.decEq _
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p ↦ mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2))
    (fun p _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    show Finset.image (mulMap P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) Finset.univ =
      mulSupport P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl,
    Finsupp.sum,
    show (m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).support =
      mulSupport P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl]
  exact Finset.sum_congr rfl fun D hD ↦ heckeSlash_gen_fiber_sum k D₁ D₂ D hD f hf

/-- Multiplicativity of the generalized Hecke slash for P.H-invariant functions:
`T(D₁)(T(D₂)(f)) = (T(D₂) · T(D₁))(f)` (Shimura Proposition 3.30, generalized).
Requires commutativity of the Hecke ring multiplication to swap the order. -/
theorem heckeSlash_gen_comp (k : ℤ) (D₁ D₂ : HeckeCoset P) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ P.H → f ∣[k] (glMap h) = f)
    (hcomm : T_single P ℤ D₂ 1 * T_single P ℤ D₁ 1 =
      T_single P ℤ D₁ 1 * T_single P ℤ D₂ 1) :
    heckeSlash_gen P k D₁ (heckeSlash_gen P k D₂ f) =
    heckeSlashExt_gen P k (T_single P ℤ D₂ 1 * T_single P ℤ D₁ 1) f := by
  rw [heckeSlashExt_gen_mul_T_single, show m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) by
    simp only [T_single_one_mul_T_single_one] at hcomm; exact hcomm]
  simp_rw [heckeSlash_gen, sum_slash_eq_swap, slash_tRep_gen_mul]
  rw [← Fintype.sum_prod_type']
  exact heckeSlash_gen_comp_sum_eq k D₁ D₂ f hf

end HeckeAlgebraAction

section Commutativity

variable {P : HeckePair (GL (Fin 2) ℚ)} [HeckePairAction P]

end Commutativity

end HeckeRing.GL2
