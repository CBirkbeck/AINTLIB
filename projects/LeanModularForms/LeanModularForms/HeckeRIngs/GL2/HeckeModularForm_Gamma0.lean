/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral

/-!
# Hecke algebra acting on `ModularForm ((Gamma0 N).map (mapGL ℝ)) k`

Packages the generalized Hecke action `heckeSlash_gen (Gamma0_pair N)` from
`HeckeActionGeneral.lean` into a ring homomorphism

  `heckeRingHom_Gamma0 N k : 𝕋 (Gamma0_pair N) ℤ →+*
     Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k)`.

This is the direct analogue of `heckeRingHom` from `HeckeModularForm.lean`,
but at level `Γ₀(N)` instead of `SL₂(ℤ)`. Multiplicativity uses the
commutativity of `𝕋 (Gamma0_pair N) ℤ` (Shimura Prop 3.8, via the
Atkin–Lehner anti-involution, exposed as
`Gamma0_pair_HeckeAlgebra_mul_comm` in `CongruenceHecke/AtkinLehner.lean`).

## Main definitions

* `heckeOperator_Gamma0 N k D` — `T(D) : ModularForm ((Gamma0 N).map (mapGL ℝ)) k
   → ModularForm ((Gamma0 N).map (mapGL ℝ)) k`
* `heckeOperatorLinear_Gamma0 N k D` — `T(D)` as a ℂ-linear map
* `heckeSum_Gamma0 N k T` — `T = ∑ c_D · [D] ↦ ∑ c_D · T(D)` as a linear map
* `heckeRingHom_Gamma0 N k` — the ring homomorphism `𝕋 (Gamma0_pair N) ℤ
   →+* Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise CongruenceSubgroup
open HeckeRing DoubleCoset HeckeRing.GLn HeckeRing.GL2
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- A `Γ₀(N)`-slash-invariance assumption `∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f`
converts to the `heckeSlash_gen`-style hypothesis
`∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f`. -/
lemma Gamma0_pair_H_invariant_of_invariant {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f)
    (h : GL (Fin 2) ℚ) (hh : h ∈ (Gamma0_pair N).H) :
    f ∣[k] glMap h = f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hh
  rw [glMap_mapGL_eq]
  exact hf _ (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)

/-- The Hecke slash action preserves holomorphicity. -/
lemma heckeSlash_gen_Gamma0_holomorphic (k : ℤ) (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlash_gen (Gamma0_pair N) k D f) :=
  MDifferentiable.sum fun _ _ ↦ hf.slash k _

/-- `GL₂(ℚ)` maps cusps of `(Gamma0 N).map (mapGL ℝ)` to cusps: the Möbius action
preserves `ℙ¹(ℚ)`, and all arithmetic subgroups share the same cusps. -/
lemma glMap_smul_isCusp_Gamma0 (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma0 N).map (mapGL ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact glMap_smul_isCusp A hc

/-- `GL₂(ℚ)` maps cusps of `(Gamma1 N).map (mapGL ℝ)` to cusps. -/
lemma glMap_smul_isCusp_Gamma1 (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact glMap_smul_isCusp A hc

/-- The Hecke slash action preserves boundedness at cusps. -/
lemma heckeSlash_gen_Gamma0_bdd_at_cusps (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma0 N).map (mapGL ℝ))) :
    c.IsBoundedAt (heckeSlash_gen (Gamma0_pair N) k D f) k := by
  simp only [heckeSlash_gen]
  exact Finset.sum_induction _ (fun g ↦ c.IsBoundedAt g k) (fun _ _ ha hb ↦ ha.add hb)
    ((0 : ModularForm ((Gamma0 N).map (mapGL ℝ)) k).bdd_at_cusps' hc) fun _ _ ↦
    OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp_Gamma0 N _ hc))

/-- The `SlashInvariantForm` obtained by applying a Hecke operator at level `Γ₀(N)`. -/
noncomputable def heckeSlashInvariant_Gamma0 (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : SlashInvariantForm ((Gamma0 N).map (mapGL ℝ)) k) :
    SlashInvariantForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := heckeSlash_gen (Gamma0_pair N) k D f
  slash_action_eq' γ hγ := by
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
    rw [← glMap_mapGL_eq]
    exact heckeSlash_gen_slash_invariant (P := Gamma0_pair N) k D (f : ℍ → ℂ)
      (Gamma0_pair_H_invariant_of_invariant N f.slash_action_eq')
      (mapGL ℚ σ) (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)

/-- The Hecke operator `T(D)` on `ModularForm ((Gamma0 N).map (mapGL ℝ)) k`,
preserving slash-invariance, holomorphicity, and boundedness at cusps. -/
noncomputable def heckeOperator_Gamma0 (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toSlashInvariantForm := heckeSlashInvariant_Gamma0 N k D f.toSlashInvariantForm
  holo' := heckeSlash_gen_Gamma0_holomorphic N k D f f.holo'
  bdd_at_cusps' hc := heckeSlash_gen_Gamma0_bdd_at_cusps N k D f hc

/-- The Hecke operator `T(D)` as a `ℂ`-linear map on modular forms at level `Γ₀(N)`. -/
noncomputable def heckeOperatorLinear_Gamma0 (k : ℤ) (D : HeckeCoset (Gamma0_pair N)) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := heckeOperator_Gamma0 N k D
  map_add' f g := ModularForm.ext fun z ↦ congrFun (heckeSlash_gen_add k D (f : ℍ → ℂ) g) z
  map_smul' c f := ModularForm.ext fun z ↦ congrFun (heckeSlash_gen_smul k D c (f : ℍ → ℂ)) z

/-- Composition of Hecke operators at level `Γ₀(N)` corresponds to Hecke algebra
multiplication (Shimura Proposition 3.30, generalized). Using commutativity of
`𝕋 (Gamma0_pair N) ℤ` there is no ordering ambiguity. -/
theorem heckeOperator_Gamma0_comp (k : ℤ) (D₁ D₂ : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (heckeOperator_Gamma0 N k D₁ (heckeOperator_Gamma0 N k D₂ f) : ℍ → ℂ) =
    heckeSlashExt_gen (Gamma0_pair N) k
      (T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1) f :=
  heckeSlash_gen_comp (P := Gamma0_pair N) k D₁ D₂ (f : ℍ → ℂ)
    (Gamma0_pair_H_invariant_of_invariant N (SlashInvariantFormClass.slash_action_eq f))
    (Gamma0_pair_HeckeAlgebra_mul_comm N _ _)

/-- The `ℂ`-linear endomorphism of `ModularForm ((Gamma0 N).map (mapGL ℝ)) k`
attached to a Hecke algebra element `T : 𝕋 (Gamma0_pair N) ℤ`, obtained by
extending `heckeOperatorLinear_Gamma0` by `ℤ`-linearity. -/
noncomputable def heckeSum_Gamma0 (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ) :
    Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  T.sum (fun D c ↦ c • heckeOperatorLinear_Gamma0 N k D)

@[simp] lemma heckeSum_Gamma0_zero (k : ℤ) : heckeSum_Gamma0 N k (0 : 𝕋 (Gamma0_pair N) ℤ) = 0 :=
  Finsupp.sum_zero_index

@[simp] lemma heckeSum_Gamma0_T_single (k : ℤ) (D : HeckeCoset (Gamma0_pair N)) (c : ℤ) :
    heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D c) = c • heckeOperatorLinear_Gamma0 N k D :=
  Finsupp.sum_single_index (zero_smul ..)

lemma heckeSum_Gamma0_add (k : ℤ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    heckeSum_Gamma0 N k (T₁ + T₂) = heckeSum_Gamma0 N k T₁ + heckeSum_Gamma0 N k T₂ :=
  Finsupp.sum_add_index' (fun _ ↦ zero_smul ..) fun _ _ _ ↦ add_zsmul ..

/-- Pointwise agreement of `heckeSum_Gamma0 N k T f` and the underlying
generalized slash sum `heckeSlashExt_gen (Gamma0_pair N) k T f`. -/
lemma heckeSum_Gamma0_apply_apply (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (z : ℍ) :
    (heckeSum_Gamma0 N k T f) z = heckeSlashExt_gen (Gamma0_pair N) k T (f : ℍ → ℂ) z := by
  classical
  simp only [heckeSlashExt_gen]
  induction T using Finsupp.induction_linear with
  | zero => simp [Finsupp.sum_zero_index, heckeSum_Gamma0]
  | add T₁ T₂ h₁ h₂ =>
    rw [Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [add_zsmul]),
      Pi.add_apply, ← h₁, ← h₂]
    exact congrArg (· z) (DFunLike.congr_fun (heckeSum_Gamma0_add N k T₁ T₂) f)
  | single D c =>
    rw [heckeSum_Gamma0_T_single,
      Finsupp.sum_single_index (by simp : (0 : ℤ) • heckeSlash_gen (Gamma0_pair N) k D _ = _)]
    rfl

private lemma heckeSlashExt_gen_Gamma0_zsmul (k : ℤ) (n : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ)
    (f : ℍ → ℂ) :
    heckeSlashExt_gen (Gamma0_pair N) k (n • T) f =
      n • heckeSlashExt_gen (Gamma0_pair N) k T f := by
  simp only [heckeSlashExt_gen]
  have hsmi := Finsupp.sum_smul_index (g := T) (b := n)
    (h := fun D c ↦ c • heckeSlash_gen (Gamma0_pair N) k D f) fun _ ↦ zero_smul ..
  rw [show ((n • T : 𝕋 (Gamma0_pair N) ℤ).sum
      fun D c ↦ c • heckeSlash_gen (Gamma0_pair N) k D f) =
    T.sum (fun D a ↦ (n * a) • heckeSlash_gen (Gamma0_pair N) k D f) from hsmi,
    Finsupp.smul_sum]
  exact Finsupp.sum_congr fun D _ ↦ mul_smul ..

private lemma heckeSum_Gamma0_mul_T_single (k : ℤ) (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (a b : ℤ) :
    heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₁ a * T_single (Gamma0_pair N) ℤ D₂ b) =
      heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₁ a) *
        heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ D₂ b) := by
  have hsm : T_single (Gamma0_pair N) ℤ D₂ b * T_single (Gamma0_pair N) ℤ D₁ a =
      (b * a) • (T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1) := by
    rw [HeckeRing.T_single_mul_T_single, T_single_one_mul_T_single_one, smul_smul]
    rfl
  rw [Gamma0_pair_HeckeAlgebra_mul_comm N
    (T_single (Gamma0_pair N) ℤ D₁ a) (T_single (Gamma0_pair N) ℤ D₂ b)]
  refine LinearMap.ext fun f ↦ ModularForm.ext fun z ↦ ?_
  rw [heckeSum_Gamma0_apply_apply, hsm, heckeSlashExt_gen_Gamma0_zsmul,
    ← heckeOperator_Gamma0_comp N k D₁ D₂ f, heckeSum_Gamma0_T_single, heckeSum_Gamma0_T_single]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    ModularForm.smul_apply, smul_smul, mul_comm b a]
  rfl

lemma heckeSum_Gamma0_mul (k : ℤ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    heckeSum_Gamma0 N k (T₁ * T₂) = heckeSum_Gamma0 N k T₁ * heckeSum_Gamma0 N k T₂ := by
  induction T₁ using HeckeRing.induction_linear_𝕋 with
  | h_zero => rw [zero_mul, heckeSum_Gamma0_zero, zero_mul]
  | h_single D₁ a =>
    induction T₂ using HeckeRing.induction_linear_𝕋 with
    | h_zero => rw [mul_zero, heckeSum_Gamma0_zero, mul_zero]
    | h_single D₂ b => exact heckeSum_Gamma0_mul_T_single N k D₁ D₂ a b
    | h_add T₂ T₂' h h' => rw [mul_add, heckeSum_Gamma0_add, heckeSum_Gamma0_add, h, h', mul_add]
  | h_add T₁ T₁' h h' => rw [add_mul, heckeSum_Gamma0_add, heckeSum_Gamma0_add, h, h', add_mul]

private lemma heckeSlash_gen_Gamma0_one (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (Gamma0_pair N).H → f ∣[k] glMap h = f) :
    heckeSlash_gen (Gamma0_pair N) k (HeckeCoset.one (Gamma0_pair N)) f = f := by
  have := subsingleton_decompQuot_T_one (Gamma0_pair N)
  simp only [heckeSlash_gen]
  rw [Fintype.sum_subsingleton _ (one_in_decompQuot_T_one (Gamma0_pair N)).some]
  exact hf _ <| HeckePairAction.adjugate_mem_H _ <|
    (Gamma0_pair N).H.mul_mem (SetLike.coe_mem _) (HeckeCoset.one_rep_mem_H _)

/-- `heckeOperator_Gamma0 N k (HeckeCoset.one _) = id`. -/
@[simp] lemma heckeOperator_Gamma0_one (k : ℤ) (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    heckeOperator_Gamma0 N k (HeckeCoset.one (Gamma0_pair N)) f = f :=
  ModularForm.ext fun _ ↦ congrFun (heckeSlash_gen_Gamma0_one N k (f : ℍ → ℂ) <|
    Gamma0_pair_H_invariant_of_invariant N (SlashInvariantFormClass.slash_action_eq f)) _

@[simp] lemma heckeOperatorLinear_Gamma0_one (k : ℤ) :
    heckeOperatorLinear_Gamma0 N k (HeckeCoset.one (Gamma0_pair N)) = 1 :=
  LinearMap.ext fun _ ↦ heckeOperator_Gamma0_one _ _ _

@[simp] lemma heckeSum_Gamma0_one (k : ℤ) : heckeSum_Gamma0 N k (1 : 𝕋 (Gamma0_pair N) ℤ) = 1 := by
  rw [HeckeRing.one_def, heckeSum_Gamma0_T_single, heckeOperatorLinear_Gamma0_one, one_smul]

/-- The Hecke algebra `𝕋 (Gamma0_pair N) ℤ` as endomorphisms of
`ModularForm ((Gamma0 N).map (mapGL ℝ)) k` (Shimura Prop 3.30, level `Γ₀(N)`). -/
noncomputable def heckeRingHom_Gamma0 (k : ℤ) :
    𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) where
  toFun := heckeSum_Gamma0 N k
  map_zero' := heckeSum_Gamma0_zero N k
  map_one' := heckeSum_Gamma0_one N k
  map_add' := heckeSum_Gamma0_add N k
  map_mul' := heckeSum_Gamma0_mul N k

@[simp] lemma heckeRingHom_Gamma0_apply (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ) :
    heckeRingHom_Gamma0 N k T = heckeSum_Gamma0 N k T := rfl

@[simp] lemma heckeRingHom_Gamma0_T_single (k : ℤ) (D : HeckeCoset (Gamma0_pair N)) (c : ℤ) :
    heckeRingHom_Gamma0 N k (T_single (Gamma0_pair N) ℤ D c) =
      c • heckeOperatorLinear_Gamma0 N k D :=
  heckeSum_Gamma0_T_single N k D c

end HeckeRing.GL2
