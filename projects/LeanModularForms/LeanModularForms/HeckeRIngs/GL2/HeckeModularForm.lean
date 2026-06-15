/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeAction

/-!
# Hecke Operators as Endomorphisms of Modular Forms

Constructs the Hecke operator `T(D)` as an endomorphism of `ModularForm 𝒮ℒ k`,
proving holomorphicity, linearity, and boundedness at cusps, and packages the full
Hecke algebra `𝕋 (GL_pair 2) ℤ` as a ring of endomorphisms.

## Main definitions

* `heckeOperator` — `T(D) : ModularForm 𝒮ℒ k → ModularForm 𝒮ℒ k`
* `heckeOperatorLinear` — `T(D)` as a `ℂ`-linear map
* `heckeRingHom` — the ring homomorphism `𝕋 (GL_pair 2) ℤ →+* Module.End ℂ (ModularForm 𝒮ℒ k)`

## Main results

* `heckeOperator_comp` — composition corresponds to Hecke algebra multiplication
  (Shimura Proposition 3.30): the double sum over coset pairs `(i, j)` is regrouped
  by the value of `mulMap (i, j)`, with fibers counted by `heckeMultiplicity_uniform`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise
open HeckeRing DoubleCoset HeckeRing.GLn HeckeRing.GL2
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane Manifold

namespace HeckeRing.GL2

/-- `𝒮ℒ` has determinant 1: all elements come from SL₂(ℤ). -/
instance : Subgroup.HasDetOne 𝒮ℒ where
  det_eq {γ} hγ := by
    obtain ⟨s, rfl⟩ := hγ
    exact det_mapGL s

/-- The Hecke slash action preserves holomorphicity. -/
lemma heckeSlash_holomorphic (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlash k D f) :=
  MDifferentiable.sum fun _ _ ↦ hf.slash k _

/-- `GL₂(ℚ)` maps cusps of `𝒮ℒ` to cusps: the Möbius action preserves `ℙ¹(ℚ)`. -/
lemma glMap_smul_isCusp (A : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (glMap A • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  exact ⟨A • q, OnePoint.map_smul (algebraMap ℚ ℝ) A q⟩

/-- The Hecke slash action preserves boundedness at cusps. -/
lemma heckeSlash_bdd_at_cusps (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ModularForm 𝒮ℒ k)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (heckeSlash k D f) k := by
  simp only [heckeSlash]
  exact Finset.sum_induction _ (fun g ↦ c.IsBoundedAt g k) (fun _ _ ha hb ↦ ha.add hb)
    ((0 : ModularForm 𝒮ℒ k).bdd_at_cusps' hc) fun _ _ ↦
    OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp _ hc))

/-- The Hecke operator `T(D)` on modular forms, preserving slash invariance and holomorphicity. -/
noncomputable def heckeOperator (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashInvariant k D f.toSlashInvariantForm
  holo' := heckeSlash_holomorphic k D f f.holo'
  bdd_at_cusps' hc := heckeSlash_bdd_at_cusps k D f hc

/-- The Hecke operator `T(D)` as a `ℂ`-linear map on modular forms. -/
noncomputable def heckeOperatorLinear (k : ℤ) (D : HeckeCoset (GL_pair 2)) :
    ModularForm 𝒮ℒ k →ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun := heckeOperator k D
  map_add' f g := ModularForm.ext fun z ↦ congrFun (heckeSlash_add k D (f : ℍ → ℂ) g) z
  map_smul' c f := ModularForm.ext fun z ↦ congrFun (heckeSlash_smul k D c (f : ℍ → ℂ)) z

private lemma prod_mem_mulMap (D₁ D₂ : HeckeCoset (GL_pair 2))
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) × decompQuot (GL_pair 2) (HeckeCoset.rep D₂)) :
    (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet (mulMap (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) := by
  change _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (GL_pair 2))
  simp only [HeckeCoset.toSet_mk]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

private lemma slash_and_coset_of_mulMap_eq (k : ℤ) (D₁ D₂ D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) × decompQuot (GL_pair 2) (HeckeCoset.rep D₂))
    (hp : mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D) :
    ∃ q : decompQuot (GL_pair 2) (HeckeCoset.rep D),
      (f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1) = f ∣[k] tRep D q) ∧
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) := by
  have hmem := hp ▸ prod_mem_mulMap D₁ D₂ p
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hmem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hmem
  set q : decompQuot (GL_pair 2) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  refine ⟨q, ?_, ?_⟩
  · rw [tRep_mul_anti D₁ D₂ p.1 p.2, heq]
    exact slash_tRep_of_mem k D _ h₂ hh₁ hh₂ f hf
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
      ⟨1, (GL_pair 2).H.one_mem, by simp [smul_eq_mul]⟩,
      ⟨κ * h₂, (GL_pair 2).H.mul_mem h_K hh₂, by
        simp only [smul_eq_mul, κ]
        group⟩⟩

private lemma mulMap_eq_of_rightCoset (D₁ D₂ D : HeckeCoset (GL_pair 2))
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) × decompQuot (GL_pair 2) (HeckeCoset.rep D₂))
    (q : decompQuot (GL_pair 2) (HeckeCoset.rep D))
    (hp_rc : ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ))) :
    mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D := by
  have h_in_rc : (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      ({(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) := by
    rw [← hp_rc, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, (GL_pair 2).H.one_mem, mul_one _⟩
  obtain ⟨_, rfl, h, hh, hprod⟩ := h_in_rc
  refine HeckeCoset_ext_toSet (GL_pair 2) ?_
  rw [HeckeCoset.toSet_eq_rep, HeckeCoset.toSet_eq_rep]
  have hm := prod_mem_mulMap D₁ D₂ p
  rw [HeckeCoset.toSet_eq_rep] at hm
  exact DoubleCoset.eq_of_not_disjoint (Set.not_disjoint_iff.mpr
    ⟨_, hm, DoubleCoset.mem_doubleCoset.mpr ⟨q.out, SetLike.coe_mem q.out, h, hh, hprod.symm⟩⟩)

private lemma exists_coset_choice_of_mulMap_eq [DecidableEq (HeckeCoset (GL_pair 2))] (k : ℤ)
    (D₁ D₂ D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∃ q_of : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
             decompQuot (GL_pair 2) (HeckeCoset.rep D₂) →
             decompQuot (GL_pair 2) (HeckeCoset.rep D),
      (∀ p, mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
        f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1) = f ∣[k] tRep D (q_of p)) ∧
      (∀ p, mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
        ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
        {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        ((GL_pair 2).H : Set (GL (Fin 2) ℚ))) := by
  have h_main := slash_and_coset_of_mulMap_eq k D₁ D₂ D f hf
  refine ⟨fun p ↦
    if h : mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D
    then (h_main p h).choose else ⟦1⟧,
    fun p hp ↦ by simpa only [hp, dif_pos] using (h_main p hp).choose_spec.1,
    fun p hp ↦ by simpa only [hp, dif_pos] using (h_main p hp).choose_spec.2⟩

private lemma fiber_card_eq_rightCoset_card (D₁ D₂ D : HeckeCoset (GL_pair 2))
    [DecidableEq (HeckeCoset (GL_pair 2))] [DecidableEq (decompQuot (GL_pair 2) (HeckeCoset.rep D))]
    (q_of : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
            decompQuot (GL_pair 2) (HeckeCoset.rep D₂) →
            decompQuot (GL_pair 2) (HeckeCoset.rep D))
    (hq_coset : ∀ p, mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)))
    (q : decompQuot (GL_pair 2) (HeckeCoset.rep D)) :
    ((Finset.univ.filter (fun p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
        decompQuot (GL_pair 2) (HeckeCoset.rep D₂) ↦
        mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D)).filter
      (fun p ↦ q_of p = q)).card = Nat.card
        {p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
             decompQuot (GL_pair 2) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((GL_pair 2).H : Set (GL (Fin 2) ℚ))} := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr {
    toFun := fun ⟨p, hp⟩ ↦ ⟨p, by
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_filter.mp hp
      exact hp₂ ▸ hq_coset p (Finset.mem_filter.mp hp₁).2⟩
    invFun := fun ⟨p, hp_rc⟩ ↦ ⟨p, by
      have hmap := mulMap_eq_of_rightCoset D₁ D₂ D p q hp_rc
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap⟩, ?_⟩
      by_contra hne
      exact decompQuot_coset_diff (GL_pair 2) (HeckeCoset.rep D) (q_of p) q hne
        ((hq_coset p hmap).symm.trans hp_rc)⟩
    left_inv := fun ⟨_, _⟩ ↦ rfl
    right_inv := fun ⟨_, _⟩ ↦ rfl }

private lemma heckeSlash_fiber_sum [DecidableEq (HeckeCoset (GL_pair 2))] (k : ℤ)
    (D₁ D₂ D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
                 decompQuot (GL_pair 2) (HeckeCoset.rep D₂) ↦
          mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D),
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1)) =
    (m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D •
      ∑ q : decompQuot (GL_pair 2) (HeckeCoset.rep D),
        f ∣[k] tRep D q := by
  classical
  obtain ⟨q_of, h_slash_eq, h_coset_eq⟩ := exists_coset_choice_of_mulMap_eq k D₁ D₂ D f hf
  rw [Finset.sum_congr rfl fun p hp ↦ h_slash_eq p (Finset.mem_filter.mp hp).2,
    ← Finset.sum_fiberwise (g := q_of)]
  conv_lhs =>
    enter [2, q]
    rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.mp hp).2],
      Finset.sum_const]
  simp_rw [fiber_card_eq_rightCoset_card D₁ D₂ D q_of h_coset_eq,
    heckeMultiplicity_uniform (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D,
    Finset.sum_nsmul]
  simp only [m, Finsupp.coe_mk, heckeMultiplicity, Nat.cast_smul_eq_nsmul ℤ]

/-- The Hecke slash action extended by `ℤ`-linearity from single double cosets to the
full Hecke algebra `𝕋 (GL_pair 2) ℤ`. -/
noncomputable def heckeSlashExt (k : ℤ) (T : HeckeAlgebra 2) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum fun D c ↦ c • heckeSlash k D f

private theorem heckeSlash_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) : heckeSlash k D₁ (heckeSlash k D₂ f) =
    heckeSlashExt k (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) f := by
  classical
  rw [T_single_one_mul_T_single_one,
    (GL_pair_antiInvolution 2).m_comm_of_onHeckeCoset_eq (GL_pair_onHeckeCoset_eq 2) D₂ D₁]
  simp_rw [heckeSlashExt, heckeSlash, SlashAction.sum_slash, ← SlashAction.slash_mul]
  rw [← Fintype.sum_prod_type', ← Finset.sum_fiberwise_of_maps_to
    (g := fun p ↦ mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2))
    (fun p _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)), Finsupp.sum]
  exact Finset.sum_congr rfl fun D _ ↦ heckeSlash_fiber_sum k D₁ D₂ D f hf

/-- Composing Hecke operators corresponds to Hecke algebra multiplication
    (Shimura Proposition 3.30): `T(D₁)(T(D₂)(f)) = (T(D₂) · T(D₁))(f)`. -/
theorem heckeOperator_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ModularForm 𝒮ℒ k) :
    (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) =
    heckeSlashExt k (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) f :=
  heckeSlash_comp k D₁ D₂ f (SlashInvariantFormClass.slash_action_eq f)

/-- The `ℂ`-linear endomorphism of modular forms attached to a Hecke algebra element
`T : 𝕋 (GL_pair 2) ℤ`, obtained by extending `heckeOperatorLinear` by `ℤ`-linearity. -/
noncomputable def heckeSum (k : ℤ) (T : HeckeAlgebra 2) : Module.End ℂ (ModularForm 𝒮ℒ k) :=
  T.sum fun D c ↦ c • heckeOperatorLinear k D

@[simp] lemma heckeSum_zero (k : ℤ) : heckeSum k (0 : HeckeAlgebra 2) = 0 :=
  Finsupp.sum_zero_index

@[simp] lemma heckeSum_T_single (k : ℤ) (D : HeckeCoset (GL_pair 2)) (c : ℤ) :
    heckeSum k (T_single (GL_pair 2) ℤ D c) = c • heckeOperatorLinear k D :=
  Finsupp.sum_single_index (zero_smul ..)

lemma heckeSum_add (k : ℤ) (T₁ T₂ : HeckeAlgebra 2) :
    heckeSum k (T₁ + T₂) = heckeSum k T₁ + heckeSum k T₂ :=
  Finsupp.sum_add_index' (fun _ ↦ zero_smul ..) fun _ _ _ ↦ add_zsmul ..

/-- Pointwise agreement of `heckeSum k T f` and `heckeSlashExt k T f` for each `z ∈ ℍ`. -/
lemma heckeSum_apply_apply (k : ℤ) (T : HeckeAlgebra 2) (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    (heckeSum k T f) z = heckeSlashExt k T (f : ℍ → ℂ) z := by
  classical
  simp only [heckeSlashExt]
  induction T using Finsupp.induction_linear with
  | zero => simp [Finsupp.sum_zero_index, heckeSum]
  | add T₁ T₂ h₁ h₂ =>
    rw [Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [add_zsmul]),
      Pi.add_apply, ← h₁, ← h₂]
    exact congrArg (· z) (DFunLike.congr_fun (heckeSum_add k T₁ T₂) f)
  | single D c =>
    rw [heckeSum_T_single,
      Finsupp.sum_single_index (zero_smul .. : (0 : ℤ) • heckeSlash k D _ = _)]
    rfl

private lemma heckeSlash_one (k : ℤ) (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    heckeSlash k (HeckeCoset.one (GL_pair 2)) f = f := by
  have := subsingleton_decompQuot_T_one (GL_pair 2)
  set q := (one_in_decompQuot_T_one (GL_pair 2)).some
  simp only [heckeSlash]
  rw [Fintype.sum_subsingleton _ q]
  obtain ⟨s, hs⟩ := GL_transpose_mem_SLnZ 2 <|
    (GL_pair 2).H.mul_mem (SetLike.coe_mem q.out) (HeckeCoset.one_rep_mem_H _)
  have hrep : (tRep (HeckeCoset.one (GL_pair 2)) q : GL (Fin 2) ℚ) = mapGL ℚ s := hs.symm
  change f ∣[k] glMap (tRep (HeckeCoset.one (GL_pair 2)) q) = f
  rw [hrep, glMap_mapGL_eq]
  exact hf _ ⟨s, rfl⟩

/-- `heckeOperator k (HeckeCoset.one _) = id` on modular forms. -/
@[simp] lemma heckeOperator_one (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    heckeOperator k (HeckeCoset.one (GL_pair 2)) f = f :=
  ModularForm.ext fun _ ↦ congrFun
    (heckeSlash_one k (f : ℍ → ℂ) (SlashInvariantFormClass.slash_action_eq f)) _

@[simp] lemma heckeOperatorLinear_one (k : ℤ) :
    heckeOperatorLinear k (HeckeCoset.one (GL_pair 2)) = 1 :=
  LinearMap.ext fun _ ↦ heckeOperator_one _ _

@[simp] lemma heckeSum_one (k : ℤ) : heckeSum k (1 : HeckeAlgebra 2) = 1 := by
  rw [HeckeRing.one_def, heckeSum_T_single, heckeOperatorLinear_one, one_smul]

private lemma heckeSlashExt_zsmul (k : ℤ) (n : ℤ) (T : HeckeAlgebra 2) (f : ℍ → ℂ) :
    heckeSlashExt k (n • T) f = n • heckeSlashExt k T f := by
  simp only [heckeSlashExt]
  rw [show ((n • T : HeckeAlgebra 2).sum fun D c ↦ c • heckeSlash k D f) =
      T.sum (fun D c ↦ (n * c) • heckeSlash k D f) from
    Finsupp.sum_smul_index fun _ ↦ zero_smul .., Finsupp.smul_sum]
  exact Finsupp.sum_congr fun D _ ↦ mul_smul ..

private lemma heckeSum_mul_T_single (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (a b : ℤ) :
    heckeSum k (T_single (GL_pair 2) ℤ D₁ a * T_single (GL_pair 2) ℤ D₂ b) =
      heckeSum k (T_single (GL_pair 2) ℤ D₁ a) * heckeSum k (T_single (GL_pair 2) ℤ D₂ b) := by
  have hsm : T_single (GL_pair 2) ℤ D₂ b * T_single (GL_pair 2) ℤ D₁ a =
      (b * a) • (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) := by
    rw [HeckeRing.T_single_mul_T_single, T_single_one_mul_T_single_one, smul_smul]
    rfl
  rw [(GL_pair_antiInvolution 2).mul_comm_of_antiInvolution (GL_pair_onHeckeCoset_eq 2)
    (T_single (GL_pair 2) ℤ D₁ a) (T_single (GL_pair 2) ℤ D₂ b)]
  refine LinearMap.ext fun f ↦ ModularForm.ext fun z ↦ ?_
  rw [heckeSum_apply_apply, hsm, heckeSlashExt_zsmul, ← heckeOperator_comp k D₁ D₂ f,
    heckeSum_T_single, heckeSum_T_single]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    ModularForm.smul_apply, smul_smul, mul_comm b a]
  rfl

lemma heckeSum_mul (k : ℤ) (T₁ T₂ : HeckeAlgebra 2) :
    heckeSum k (T₁ * T₂) = heckeSum k T₁ * heckeSum k T₂ := by
  induction T₁ using HeckeRing.induction_linear_𝕋 with
  | h_zero => rw [zero_mul, heckeSum_zero, zero_mul]
  | h_single D₁ a =>
    induction T₂ using HeckeRing.induction_linear_𝕋 with
    | h_zero => rw [mul_zero, heckeSum_zero, mul_zero]
    | h_single D₂ b => exact heckeSum_mul_T_single k D₁ D₂ a b
    | h_add T₂ T₂' h h' => rw [mul_add, heckeSum_add, heckeSum_add, h, h', mul_add]
  | h_add T₁ T₁' h h' => rw [add_mul, heckeSum_add, heckeSum_add, h, h', add_mul]

/-- The Hecke algebra as endomorphisms of modular forms (Shimura Prop 3.30). Maps a
formal sum `T = ∑ c_D · [D]` to `∑ c_D · T(D)`; multiplicativity comes from
`heckeOperator_comp` plus the commutativity of `𝕋 (GL_pair 2) ℤ`. -/
noncomputable def heckeRingHom (k : ℤ) : HeckeAlgebra 2 →+* Module.End ℂ (ModularForm 𝒮ℒ k) where
  toFun := heckeSum k
  map_zero' := heckeSum_zero k
  map_one' := heckeSum_one k
  map_add' := heckeSum_add k
  map_mul' := heckeSum_mul k

@[simp] lemma heckeRingHom_apply (k : ℤ) (T : HeckeAlgebra 2) :
    heckeRingHom k T = heckeSum k T := rfl

@[simp] lemma heckeRingHom_T_single (k : ℤ) (D : HeckeCoset (GL_pair 2)) (c : ℤ) :
    heckeRingHom k (T_single (GL_pair 2) ℤ D c) = c • heckeOperatorLinear k D :=
  heckeSum_T_single k D c

end HeckeRing.GL2
