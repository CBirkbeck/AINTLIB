/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Hecke Operators on Modular Forms

Defines the action of the Hecke algebra on functions `ℍ → ℂ` via the slash action,
and shows it preserves slash invariance.

## Main definitions

* `glMap` — embedding `GL₂(ℚ) →* GL₂(ℝ)`
* `heckeSlash` — action of a double coset on functions via left coset representatives:
    `T(D) f = Σᵢ f ∣[k] (σᵢδ)ᵀ` where `ΓδΓ = ⊔ Γ(δᵀσᵢᵀ)` (Shimura Prop 3.30)
* `heckeSlashInvariant` — the Hecke operator preserves slash invariance

## Implementation

The slash action on `GL₂(ℚ)` is induced from `GL₂(ℝ)` via `monoidHomSlashAction glMap`,
so `f ∣[k] g` works directly for `g : GL (Fin 2) ℚ` without explicit coercion.

Left coset representatives are obtained by transposing right coset representatives:
if `ΓδΓ = ⊔ᵢ (σᵢδ)Γ`, then `ΓδΓ = ⊔ᵢ Γ(δᵀσᵢᵀ)` since transpose is an
anti-involution preserving `Γ` and fixing every double coset (`GL_pair_onHeckeCoset_eq`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4, Prop 3.30
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise
open HeckeRing DoubleCoset HeckeRing.GLn
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane

namespace HeckeRing.GL2

/-- Embed `GL₂(ℚ)` into `GL₂(ℝ)` via `ℚ ↪ ℝ`. -/
noncomputable def glMap : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- Slash action on `GL₂(ℚ)` induced from `GL₂(ℝ)` via the embedding `ℚ ↪ ℝ`.
    Satisfies `f ∣[k] g = f ∣[k] glMap g` definitionally. -/
noncomputable scoped instance : SlashAction ℤ (GL (Fin 2) ℚ) (ℍ → ℂ) :=
  monoidHomSlashAction glMap

section DetPositivity

private lemma glMap_det (g : GL (Fin 2) ℚ) :
    GeneralLinearGroup.det (glMap g) =
    Units.map (algebraMap ℚ ℝ) (GeneralLinearGroup.det g) :=
  GeneralLinearGroup.map_det _ g

private lemma glMap_det_val (g : GL (Fin 2) ℚ) :
    (glMap g).det.val = algebraMap ℚ ℝ g.det.val :=
  congr_arg Units.val (glMap_det g)

private lemma delta_det_pos_real (g : (GL_pair 2).Δ) :
    0 < (glMap (g : GL (Fin 2) ℚ)).det.val := by
  rw [glMap_det_val, GeneralLinearGroup.val_det_apply]
  exact Rat.cast_pos.mpr g.prop.2

private lemma SLnZ_det_one_real (σ : (GL_pair 2).H) :
    (glMap (σ : GL (Fin 2) ℚ)).det.val = 1 := by
  obtain ⟨s, hs⟩ := σ.prop
  rw [← hs, glMap_det, det_mapGL s, map_one, Units.val_one]

private lemma cosetRep_delta_det_pos (σ : (GL_pair 2).H) (g : (GL_pair 2).Δ) :
    0 < (glMap ((σ : GL (Fin 2) ℚ) * (g : GL (Fin 2) ℚ))).det.val := by
  simpa only [map_mul, Units.val_mul, SLnZ_det_one_real, one_mul] using delta_det_pos_real g

/-- The complex automorphism `UpperHalfPlane.σ g` attached to `g : GL(2, ℝ)` is the identity
    when `g` has positive determinant. -/
lemma sigma_eq_id_of_pos_det {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    UpperHalfPlane.σ g = ContinuousAlgEquiv.refl ℝ ℂ :=
  if_pos hg

private lemma glMap_transpose_det_val (g : GL (Fin 2) ℚ) :
    (glMap (GL_transposeEquiv 2 g).unop).det.val = (glMap g).det.val := by
  rw [glMap_det_val, glMap_det_val, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_det_apply, GL_transposeEquiv_val, Matrix.det_transpose]

private lemma cosetRep_delta_transpose_det_pos (σ : (GL_pair 2).H) (g : (GL_pair 2).Δ) :
    0 < (glMap (GL_transposeEquiv 2
      ((σ : GL (Fin 2) ℚ) * (g : GL (Fin 2) ℚ))).unop).det.val :=
  glMap_transpose_det_val _ ▸ cosetRep_delta_det_pos σ g

end DetPositivity

/-- The transposed right-coset representative: `(σᵢ * δ)ᵀ = δᵀ * σᵢᵀ`. -/
noncomputable abbrev tRep (D : HeckeCoset (GL_pair 2))
    (i : decompQuot (GL_pair 2) (HeckeCoset.rep D)) : GL (Fin 2) ℚ :=
  (GL_transposeEquiv 2
    ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ))).unop

/-- The Hecke slash action of a double coset `D` on a function `f : ℍ → ℂ`.

    Uses left coset representatives via transpose (Shimura Prop 3.30):
    `T_k(D)(f) = Σᵢ f ∣[k] (σᵢδ)ᵀ`
    where `ΓδΓ = ⊔ᵢ (σᵢδ)Γ` is the right coset decomposition.
    Each `(σᵢδ)ᵀ = δᵀσᵢᵀ` is a left coset representative, giving
    genuinely distinct terms `f ∣[k] (δᵀσᵢᵀ)`. -/
noncomputable def heckeSlash (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot (GL_pair 2) (HeckeCoset.rep D), f ∣[k] tRep D i

/-- The Hecke slash action distributes over addition of functions. -/
lemma heckeSlash_add (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f g : ℍ → ℂ) :
    heckeSlash k D (f + g) = heckeSlash k D f + heckeSlash k D g := by
  simp [heckeSlash, Finset.sum_add_distrib]

/-- The Hecke slash action sends the zero function to zero. -/
@[simp] lemma heckeSlash_zero (k : ℤ) (D : HeckeCoset (GL_pair 2)) : heckeSlash k D 0 = 0 := by
  simp [heckeSlash]

/-- The Hecke slash action commutes with scalar multiplication. -/
lemma heckeSlash_smul (k : ℤ) (D : HeckeCoset (GL_pair 2)) (c : ℂ) (f : ℍ → ℂ) :
    heckeSlash k D (c • f) = c • heckeSlash k D f := by
  simp only [heckeSlash, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change (c • f) ∣[k] glMap (tRep D i) = c • (f ∣[k] glMap (tRep D i))
  rw [ModularForm.smul_slash,
    sigma_eq_id_of_pos_det (cosetRep_delta_transpose_det_pos ⟨i.out, SetLike.coe_mem _⟩
      (HeckeCoset.rep D)),
    ContinuousAlgEquiv.refl_apply]

section SlashInvariance

lemma glMap_mapGL_eq (s : SL(2, ℤ)) :
    glMap (mapGL ℚ s) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) s := by
  ext i j
  simp only [glMap, GeneralLinearGroup.map_apply, mapGL_coe_matrix]
  exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (s.1 i j)).symm

private lemma glMap_mem_SL (σ : (GL_pair 2).H) :
    glMap (σ : GL (Fin 2) ℚ) ∈ 𝒮ℒ :=
  let ⟨s, hs⟩ := σ.prop
  ⟨s, by rw [← glMap_mapGL_eq, hs]⟩

private lemma mem_SL_exists_H {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) :
    ∃ σ ∈ (GL_pair 2).H, glMap σ = γ :=
  let ⟨s, hs⟩ := hγ
  ⟨mapGL ℚ s, ⟨s, rfl⟩, hs ▸ glMap_mapGL_eq s⟩

private lemma heckeSlash_slash (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (g : GL (Fin 2) ℚ) : (heckeSlash k D f) ∣[k] g =
    ∑ i : decompQuot (GL_pair 2) (HeckeCoset.rep D), (f ∣[k] tRep D i) ∣[k] g := by
  simp [heckeSlash]

private lemma slash_left_H_transpose_mul (k : ℤ) (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (h : GL (Fin 2) ℚ) (hh : h ∈ (GL_pair 2).H) (g : GL (Fin 2) ℚ) :
    f ∣[k] ((GL_transposeEquiv 2 h).unop * g) = f ∣[k] g := by
  rw [SlashAction.slash_mul]
  congr 1
  exact hf _ (glMap_mem_SL ⟨_, GL_transpose_mem_SLnZ 2 hh⟩)

private lemma h_coset_mem_H (D : HeckeCoset (GL_pair 2))
    (q : decompQuot (GL_pair 2) (HeckeCoset.rep D)) (h₁ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (GL_pair 2).H) (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (GL_pair 2).H)
    (hq : (⟦q.out⟧ : decompQuot (GL_pair 2) (HeckeCoset.rep D)) = ⟦⟨h₁, hh₁⟩⟧) :
    ((HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
      (HeckeCoset.rep D : GL _ ℚ) * h₂) ∈ (GL_pair 2).H := by
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at h_K
  simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
  exact (GL_pair 2).H.mul_mem
    (by convert h_K using 1; simp only [Subgroup.coe_mul, Subgroup.coe_inv]) hh₂

private lemma transpose_decomp_eq (D : HeckeCoset (GL_pair 2))
    (q : decompQuot (GL_pair 2) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) :
    (GL_transposeEquiv 2 (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)).unop =
    (GL_transposeEquiv 2 ((HeckeCoset.rep D : GL _ ℚ)⁻¹ *
      ((q.out : GL _ ℚ)⁻¹ * h₁) *
      (HeckeCoset.rep D : GL _ ℚ) * h₂)).unop * tRep D q := by
  simp only [tRep, ← MulOpposite.unop_mul, ← (GL_transposeEquiv 2).map_mul,
    mul_assoc, mul_inv_cancel_left]

/-- Slashing by the transpose of `h₁ * δ * h₂` with `h₁, h₂ ∈ H` equals slashing
    by `tRep D ⟦h₁⟧`. -/
lemma slash_tRep_of_mem (k : ℤ) (D : HeckeCoset (GL_pair 2))
    (h₁ h₂ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (GL_pair 2).H)
    (hh₂ : h₂ ∈ (GL_pair 2).H) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    f ∣[k] (GL_transposeEquiv 2
      (h₁ * (HeckeCoset.rep D : GL (Fin 2) ℚ) * h₂)).unop =
    f ∣[k] tRep D ⟦⟨h₁, hh₁⟩⟧ := by
  set q : decompQuot (GL_pair 2) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  rw [transpose_decomp_eq D q h₁ h₂]
  exact slash_left_H_transpose_mul k f hf _
    (h_coset_mem_H D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq _)) _

private lemma tRep_mul_eq_transpose (D : HeckeCoset (GL_pair 2))
    (i : decompQuot (GL_pair 2) (HeckeCoset.rep D)) (σ_Q : GL (Fin 2) ℚ) :
    tRep D i * σ_Q = (GL_transposeEquiv 2
      ((GL_transposeEquiv 2 σ_Q).unop * (i.out : GL _ ℚ) *
        (HeckeCoset.rep D : GL _ ℚ))).unop := by
  simp [tRep, map_mul, MulOpposite.unop_mul, GL_transposeEquiv_involutive, mul_assoc]

/-- The Hecke slash action preserves slash-invariance under `SL₂(Z)` (Shimura Prop 3.30). -/
lemma heckeSlash_slash_invariant (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) :
    (heckeSlash k D f) ∣[k] γ = heckeSlash k D f := by
  obtain ⟨σ_Q, hσ_Q, rfl⟩ := mem_SL_exists_H hγ
  change (heckeSlash k D f) ∣[k] σ_Q = heckeSlash k D f
  set σ_QT : (GL_pair 2).H :=
    ⟨(GL_transposeEquiv 2 σ_Q).unop, GL_transpose_mem_SLnZ 2 hσ_Q⟩
  set π : Equiv.Perm (decompQuot (GL_pair 2) (HeckeCoset.rep D)) := MulAction.toPerm σ_QT
  have h_perm (i) : (f ∣[k] tRep D i) ∣[k] σ_Q = f ∣[k] tRep D (π i) := by
    rw [← SlashAction.slash_mul k (tRep D i) σ_Q f, tRep_mul_eq_transpose,
      ← mul_one ((σ_QT : GL (Fin 2) ℚ) * i.out * (HeckeCoset.rep D : GL (Fin 2) ℚ)),
      slash_tRep_of_mem k D _ 1 ((GL_pair 2).H.mul_mem σ_QT.prop (SetLike.coe_mem _))
        (GL_pair 2).H.one_mem f hf]
    exact congrArg (f ∣[k] tRep D ·) (MulAction.Quotient.mk_smul_out _ σ_QT i)
  rw [heckeSlash_slash, Finset.sum_congr rfl (fun i _ ↦ h_perm i),
    Fintype.sum_equiv π _ (fun i ↦ f ∣[k] tRep D i) (fun _ ↦ rfl)]
  rfl

/-- The `SlashInvariantForm` obtained by applying a Hecke operator. -/
noncomputable def heckeSlashInvariant (k : ℤ) (D : HeckeCoset (GL_pair 2))
    (f : SlashInvariantForm 𝒮ℒ k) : SlashInvariantForm 𝒮ℒ k where
  toFun := heckeSlash k D f
  slash_action_eq' := heckeSlash_slash_invariant k D f f.slash_action_eq'

/-- The transpose anti-homomorphism applied to the product of two coset reps:
    `tRep D₂ j * tRep D₁ i = (σᵢδ₁ · σⱼδ₂)ᵀ`. -/
lemma tRep_mul_anti (D₁ D₂ : HeckeCoset (GL_pair 2))
    (i : decompQuot (GL_pair 2) (HeckeCoset.rep D₁))
    (j : decompQuot (GL_pair 2) (HeckeCoset.rep D₂)) :
    tRep D₂ j * tRep D₁ i =
    (GL_transposeEquiv 2
      ((i.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
       ((j.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)))).unop := by
  simp only [tRep, ← MulOpposite.unop_mul, ← (GL_transposeEquiv 2).map_mul]

end SlashInvariance

end HeckeRing.GL2
