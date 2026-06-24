/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke

/-!
# Twisted `Γ₀(N)` Hecke-ring action on Nebentypus spaces

This file constructs the `χ`-twisted action of the Hecke ring
`𝕋 (Gamma0_pair N) ℤ` on `Γ₀(N), χ`-invariant functions: a semigroup character
on `Δ₀(N)` from the upper-left entry modulo `N` (the classical Nebentypus
formalism), the character-weighted Hecke slash over the right-coset
decomposition of each double coset, and its multiplicativity over the ring.

## Main definitions

* `delta0NebentypusDeltaChar`: the semigroup character on `Δ₀(N)` attached to a
  Dirichlet character `χ`.
* `twistedHeckeSlashGen`: the `χ`-weighted Hecke slash of a double coset.
* `IsGamma0TwistedInvariant`: the `Γ₀(N), χ` function-level invariance condition.
* `twistedHeckeSumFunction`: the resulting `𝕋 (Gamma0_pair N) ℤ`-indexed family
  of endomorphisms of the invariant submodule.

## Main results

* `twistedHeckeSlashGen_comp`: composing two coset operators agrees with the
  Hecke-ring product.
* `twistedHeckeSumFunction_mul`: the endomorphism-valued action is
  multiplicative on `𝕋 (Gamma0_pair N) ℤ`.
-/

open Matrix HeckeRing.GLn

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- A concrete integer matrix witness for an element of `Δ₀(N)`. -/
noncomputable def delta0IntegralMatrix (g : (Gamma0_pair N).Δ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Classical.choose g.2.2.2

/-- The chosen integer matrix witness really represents `g`. -/
lemma delta0IntegralMatrix_spec (g : (Gamma0_pair N).Δ) :
    ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (delta0IntegralMatrix g).map (Int.cast : ℤ → ℚ) :=
  (Classical.choose_spec g.2.2.2).1

/-- The lower-left entry of the chosen witness is divisible by `N`. -/
lemma delta0IntegralMatrix_lower_left_dvd (g : (Gamma0_pair N).Δ) :
    (N : ℤ) ∣ delta0IntegralMatrix g 1 0 :=
  (Classical.choose_spec g.2.2.2).2.1

/-- The upper-left entry of the chosen witness is coprime to `N`. -/
lemma delta0IntegralMatrix_upper_left_coprime (g : (Gamma0_pair N).Δ) : Int.gcd
    (delta0IntegralMatrix g 0 0) N = 1 :=
  (Classical.choose_spec g.2.2.2).2.2

/-- Any two integer witnesses for the same element of `Δ₀(N)` agree entrywise. -/
lemma delta0IntegralMatrix_witness_unique (g : (Gamma0_pair N).Δ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    delta0IntegralMatrix g = A :=
  Matrix.map_injective Int.cast_injective ((delta0IntegralMatrix_spec g).symm.trans hA)

/-- The upper-left entry of a `Δ₀(N)` witness is a unit modulo `N`. -/
lemma isUnit_delta0UpperEntry (g : (Gamma0_pair N).Δ) :
    IsUnit ((delta0IntegralMatrix g 0 0 : ℤ) : ZMod N) :=
  (ZMod.coe_int_isUnit_iff_isCoprime _ N).mpr
    (isCoprime_comm.mpr (Int.isCoprime_iff_gcd_eq_one.mpr
      (delta0IntegralMatrix_upper_left_coprime g)))

/-- The unit in `(ZMod N)ˣ` attached to the upper-left entry of a `Δ₀(N)` matrix. -/
noncomputable def delta0UpperUnit (g : (Gamma0_pair N).Δ) : (ZMod N)ˣ :=
  (isUnit_delta0UpperEntry g).unit

/-- The value of `delta0UpperUnit` as a `ZMod N`. -/
@[simp]
lemma delta0UpperUnit_val (g : (Gamma0_pair N).Δ) :
    (delta0UpperUnit g : ZMod N) = (delta0IntegralMatrix g 0 0 : ZMod N) :=
  (isUnit_delta0UpperEntry g).unit_spec

/-- The chosen witness for a product in `Δ₀(N)` is the product of the chosen
integer witnesses. -/
lemma delta0IntegralMatrix_mul (g h : (Gamma0_pair N).Δ) : delta0IntegralMatrix (g * h) =
    delta0IntegralMatrix g * delta0IntegralMatrix h := by
  apply delta0IntegralMatrix_witness_unique (g := g * h)
  simp only [Submonoid.coe_mul, Units.val_mul, delta0IntegralMatrix_spec, ← map_mul_intCast]

/-- The upper-left units multiply on `Δ₀(N)`. -/
lemma delta0UpperUnit_mul (g h : (Gamma0_pair N).Δ) :
    delta0UpperUnit (g * h) = delta0UpperUnit g * delta0UpperUnit h := by
  ext
  rw [Units.val_mul, delta0UpperUnit_val, delta0UpperUnit_val, delta0UpperUnit_val,
    delta0IntegralMatrix_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hz : ((delta0IntegralMatrix g 0 1 * delta0IntegralMatrix h 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_of_dvd_right (delta0IntegralMatrix_lower_left_dvd h) _
  simp only [Fin.isValue, Int.cast_add, Int.cast_mul, hz, add_comm, zero_add]

/-- The chosen integer witness for the identity of `Δ₀(N)` is the identity matrix. -/
@[simp] lemma delta0IntegralMatrix_one :
    delta0IntegralMatrix (1 : (Gamma0_pair N).Δ) = 1 := by
  apply delta0IntegralMatrix_witness_unique (g := 1)
  simp only [OneMemClass.coe_one, Units.val_one, Int.cast_zero, Int.cast_one, Matrix.map_one]

/-- The upper-left unit of the identity of `Δ₀(N)` is `1`. -/
@[simp] lemma delta0UpperUnit_one : delta0UpperUnit (1 : (Gamma0_pair N).Δ) = 1 := by
  ext
  rw [delta0UpperUnit_val]
  simp only [Fin.isValue, delta0IntegralMatrix_one, one_apply_eq, Int.cast_one, Units.val_one]

/-- The semigroup character on `Δ₀(N)` obtained from the upper-left unit. -/
noncomputable def delta0NebentypusDeltaChar (χ : (ZMod N)ˣ →* ℂˣ) :
    (Gamma0_pair N).Δ →* ℂˣ where
  toFun g := χ (delta0UpperUnit g)
  map_one' := by simp only [delta0UpperUnit_one, map_one]
  map_mul' g h := by
    rw [delta0UpperUnit_mul g h, map_mul]

/-- The `Δ₀(N)` upper-left character restricted to `Γ₀(N) = H`, evaluated on `adj(h)` to
match adjugated coset representatives; for `h ∈ Γ₀(N)` this gives the classical
lower-right Nebentypus entry. -/
noncomputable def delta0NebentypusHChar (χ : (ZMod N)ˣ →* ℂˣ) (h : GL (Fin 2) ℚ)
    (hh : h ∈ (Gamma0_pair N).H) : ℂˣ :=
  delta0NebentypusDeltaChar χ ⟨h, (Gamma0_pair N).h₀ hh⟩

/-- The concrete `Δ₀(N)` representative `σᵢ · rep(D)` attached to an index in the
right-coset decomposition of a `Γ₀(N)` Hecke coset. -/
noncomputable def deltaRepGen (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) : (Gamma0_pair N).Δ :=
  ⟨(i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ),
    (Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).h₀ (SetLike.coe_mem _)) (SetLike.coe_mem _)⟩

/-- The nebentypus weight attached to a `Γ₀(N)` Hecke-coset summand. -/
noncomputable def delta0NebentypusWeight (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) : ℂˣ :=
  delta0NebentypusDeltaChar χ <| deltaRepGen D i

/-- The twisted Hecke slash action attached to the existing `Γ₀(N)` Hecke coset.
Since the slash uses the adjugated representatives `tRep_gen = adj(σᵢ · rep(D))`,
each summand carries the inverse of the upper-left Nebentypus character, matching
the twisted fixed-space law `f ∣ h = η(h)⁻¹ f` for `h ∈ Γ₀(N)`. -/
noncomputable def twistedHeckeSlashGen (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
    (↑(delta0NebentypusWeight χ D i) : ℂ)⁻¹ •
      (f ∣[k] tRep_gen (Gamma0_pair N) D i)

/-- Positivity of the real determinant of an adjugated `Γ₀(N)` Hecke
representative. -/
lemma tRep_gen_Gamma0_det_pos (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    0 < (glMap (tRep_gen (Gamma0_pair N) D i)).det.val := by
  have hRat : 0 < (tRep_gen (Gamma0_pair N) D i).det.val := by
    change 0 < (GL_adjugate
      ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ))).det.val
    rw [GeneralLinearGroup.val_det_apply, GL_adjugate_val, Matrix.det_adjugate,
      Fintype.card_fin]
    simpa [deltaRepGen] using (deltaRepGen D i).prop.2.1
  exact glMap_det_pos_of_rat_det_pos _ hRat

private lemma tRep_gen_sigma_eq_id (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    UpperHalfPlane.σ (glMap (tRep_gen (Gamma0_pair N) D i)) = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp only [UpperHalfPlane.σ, tRep_gen_Gamma0_det_pos D i, ↓reduceIte]

private lemma glMap_sigma_eq_id_of_mem_H (h : GL (Fin 2) ℚ) (hh : h ∈ (Gamma0_pair N).H) :
    UpperHalfPlane.σ (glMap h) = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp only [UpperHalfPlane.σ, Gamma0_pair_det_pos N ⟨h, (Gamma0_pair N).h₀ hh⟩,
    ↓reduceIte]

private lemma smul_slash_tRep_gen (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] tRep_gen (Gamma0_pair N) D i =
      c • (f ∣[k] tRep_gen (Gamma0_pair N) D i) := by
  change (c • f) ∣[k] glMap (tRep_gen (Gamma0_pair N) D i) =
    c • (f ∣[k] glMap (tRep_gen (Gamma0_pair N) D i))
  simp only [ModularForm.smul_slash, tRep_gen_sigma_eq_id D i, ContinuousAlgEquiv.refl_apply]

/-- The twisted Hecke slash of a coset distributes over pointwise addition of functions. -/
@[simp] lemma twistedHeckeSlashGen_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f g : ℍ → ℂ) : twistedHeckeSlashGen k χ D (f + g) =
      twistedHeckeSlashGen k χ D f + twistedHeckeSlashGen k χ D g := by
  simp only [twistedHeckeSlashGen, SlashAction.add_slash, smul_add, Finset.sum_add_distrib]

/-- The `χ`-twisted Hecke slash is linear in the input function. -/
@[simp] lemma twistedHeckeSlashGen_smul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (c : ℂ) (f : ℍ → ℂ) :
    twistedHeckeSlashGen k χ D (c • f) = c • twistedHeckeSlashGen k χ D f := by
  simp only [twistedHeckeSlashGen, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_slash_tRep_gen, smul_comm]

/-- The weighted Hecke slash action extended by `ℤ`-linearity to the
Hecke ring `𝕋 (Gamma0_pair N) ℤ`. -/
noncomputable def twistedHeckeSlashExtGen (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum (fun D c ↦ c • twistedHeckeSlashGen k χ D f)

/-- The `ℤ`-linear extension `twistedHeckeSlashExtGen` is additive in the Hecke-ring element. -/
@[simp]
lemma twistedHeckeSlashExtGen_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) (f : ℍ → ℂ) :
    twistedHeckeSlashExtGen k χ (T₁ + T₂) f =
      twistedHeckeSlashExtGen k χ T₁ f +
        twistedHeckeSlashExtGen k χ T₂ f :=
  Finsupp.sum_add_index' (fun _ ↦ by simp only [zero_smul])
    (fun _ _ _ ↦ funext fun z ↦ by
      simp only [Pi.smul_apply, add_smul, zsmul_eq_mul, Pi.add_apply, Pi.mul_apply,
        Pi.intCast_apply])

/-- The `Γ₀(N),χ` function-level invariance condition: `f ∣[k] h = χ(adj(h)) • f` for all
`h` in the Hecke-pair subgroup `Γ₀(N)`. -/
def IsGamma0TwistedInvariant (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : ℍ → ℂ) : Prop :=
  ∀ h : GL (Fin 2) ℚ, ∀ hh : h ∈ (Gamma0_pair N).H,
    f ∣[k] glMap h =
      (↑(delta0NebentypusHChar χ (GL_adjugate h)
        (HeckePairAction.adjugate_mem_H h hh)) : ℂ) • f

/-- The `Γ₀(N),χ` twisted-invariant submodule of functions `ℍ → ℂ`. -/
noncomputable def gamma0TwistedInvariantFunctionSubmodule (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ℍ → ℂ) where
  carrier := {f | IsGamma0TwistedInvariant k χ f}
  zero_mem' := by
    simp only [IsGamma0TwistedInvariant, Set.mem_setOf_eq, SlashAction.zero_slash, smul_zero,
      implies_true]
  add_mem' := by
    intro f g hf hg h hh
    simp only [SlashAction.add_slash, hf h hh, hg h hh, smul_add]
  smul_mem' := by
    intro c f hf h hh
    rw [ModularForm.smul_slash, glMap_sigma_eq_id_of_mem_H h hh, hf h hh]
    exact smul_comm c _ f

/-- The `H`-correction element attached to replacing `h₁` by its quotient
representative in a right-coset decomposition. -/
noncomputable def gamma0Correction (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h₁ h₂ : GL (Fin 2) ℚ) : GL (Fin 2) ℚ :=
  (HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
    (HeckeCoset.rep D : GL _ ℚ) * h₂

/-- The correction element lies in `Γ₀(N)`. -/
lemma gamma0Correction_mem_H (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h₁ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hq : (⟦q.out⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) = ⟦⟨h₁, hh₁⟩⟧) :
    gamma0Correction D q h₁ h₂ ∈ (Gamma0_pair N).H := by
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at h_K
  simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at h_K
  exact (Gamma0_pair N).H.mul_mem h_K hh₂

/-- The adjugate decomposition of a corrected representative. -/
lemma gamma0_adjugate_decomp_eq (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h₁ h₂ : GL (Fin 2) ℚ) :
    GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) =
    GL_adjugate (gamma0Correction D q h₁ h₂) * tRep_gen (Gamma0_pair N) D q := by
  simp only [mul_assoc, gamma0Correction, tRep_gen, ← GL_adjugate_mul, mul_inv_cancel_left]

/-- The `Δ₀(N)` element `h₁ · rep(D) · h₂`. -/
noncomputable def gamma0TripleDelta (D : HeckeCoset (Gamma0_pair N)) (h₁ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (Gamma0_pair N).H) (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    : (Gamma0_pair N).Δ :=
  ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
    (Gamma0_pair N).Δ.mul_mem
      ((Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).h₀ hh₁) (SetLike.coe_mem _))
      ((Gamma0_pair N).h₀ hh₂)⟩

/-- The correction term as a `Δ₀(N)` element via `H ⊆ Δ`. -/
noncomputable def gamma0CorrectionDelta (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h₁ h₂ : GL (Fin 2) ℚ)
    (hκ : gamma0Correction D q h₁ h₂ ∈ (Gamma0_pair N).H) : (Gamma0_pair N).Δ :=
  ⟨gamma0Correction D q h₁ h₂, (Gamma0_pair N).h₀ hκ⟩

/-- The corrected representative factorization inside `Δ₀(N)`. -/
lemma gamma0TripleDelta_eq_deltaRep_mul_correction (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hκ : gamma0Correction D q h₁ h₂ ∈ (Gamma0_pair N).H) :
    gamma0TripleDelta D h₁ hh₁ h₂ hh₂ =
      deltaRepGen D q * gamma0CorrectionDelta D q h₁ h₂ hκ := by
  simp only [gamma0TripleDelta, mul_assoc, deltaRepGen, gamma0CorrectionDelta, gamma0Correction,
    Submonoid.mk_mul_mk, mul_inv_cancel_left]

private lemma slash_GL_adjugate_triple_eq_correction_slash (k : ℤ)
    (D : HeckeCoset (Gamma0_pair N)) (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) (f : ℍ → ℂ) :
    f ∣[k] GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) =
      (f ∣[k] glMap (GL_adjugate (gamma0Correction D q h₁ h₂))) ∣[k]
        glMap (tRep_gen (Gamma0_pair N) D q) := by
  rw [gamma0_adjugate_decomp_eq D q h₁ h₂]
  change f ∣[k] glMap (GL_adjugate (gamma0Correction D q h₁ h₂) *
      tRep_gen (Gamma0_pair N) D q) = _
  rw [map_mul, SlashAction.slash_mul]

private lemma delta0NebentypusHChar_adjugate_adjugate_correction (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) (hκ : gamma0Correction D q h₁ h₂ ∈ (Gamma0_pair N).H)
    (hκadj : GL_adjugate (gamma0Correction D q h₁ h₂) ∈ (Gamma0_pair N).H) :
    delta0NebentypusHChar χ
        (GL_adjugate (GL_adjugate (gamma0Correction D q h₁ h₂)))
        (HeckePairAction.adjugate_mem_H
          (GL_adjugate (gamma0Correction D q h₁ h₂)) hκadj) =
      delta0NebentypusDeltaChar χ (gamma0CorrectionDelta D q h₁ h₂ hκ) :=
  congrArg (delta0NebentypusDeltaChar χ) (Subtype.ext (GL_adjugate_involutive _))

/-- Twisted replacement for `slash_tRep_gen_of_mem`: the `H` correction is
absorbed by the inverse character coefficient. -/
lemma twisted_weighted_slash_tRep_gen_of_mem (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant k χ f) :
    ((↑(delta0NebentypusDeltaChar χ
      (gamma0TripleDelta D h₁ hh₁ h₂ hh₂)) : ℂ)⁻¹) •
        (f ∣[k] GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)) =
      ((↑(delta0NebentypusDeltaChar χ (deltaRepGen D
        (⟦⟨h₁, hh₁⟩⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)))) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D
          (⟦⟨h₁, hh₁⟩⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))) := by
  set q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  have hκ : gamma0Correction D q h₁ h₂ ∈ (Gamma0_pair N).H :=
    gamma0Correction_mem_H D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq q)
  have hη :
      delta0NebentypusDeltaChar χ
          (gamma0TripleDelta D h₁ hh₁ h₂ hh₂) =
        delta0NebentypusDeltaChar χ (deltaRepGen D q) *
          delta0NebentypusDeltaChar χ
            (gamma0CorrectionDelta D q h₁ h₂ hκ) := by
    rw [gamma0TripleDelta_eq_deltaRep_mul_correction D q h₁ hh₁ h₂ hh₂ hκ]
    exact map_mul _ _ _
  rw [slash_GL_adjugate_triple_eq_correction_slash k D q h₁ h₂ f]
  have hκadj : GL_adjugate (gamma0Correction D q h₁ h₂) ∈
      (Gamma0_pair N).H :=
    HeckePairAction.adjugate_mem_H _ hκ
  rw [hf (GL_adjugate (gamma0Correction D q h₁ h₂)) hκadj,
    ModularForm.smul_slash]
  · rw [tRep_gen_sigma_eq_id D q,
      delta0NebentypusHChar_adjugate_adjugate_correction χ D q h₁ h₂ hκ hκadj, hη]
    ext z
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousAlgEquiv.refl_apply, Units.val_mul, mul_inv]
    rw [mul_assoc, inv_mul_cancel_left₀ (Units.ne_zero _)]
    rfl

private lemma units_coe_inv_right_smul_eq_mul_smul_inv_mul (a b : ℂˣ) (g : ℍ → ℂ) :
    (↑b : ℂ)⁻¹ • g = (↑a : ℂ) • ((↑(a * b) : ℂ)⁻¹ • g) := by
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul, _root_.mul_inv_rev, mul_assoc,
    mul_left_comm, ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]

private lemma units_inv_smul_inv_smul_eq_mul_inv_smul (a b : ℂˣ) (g : ℍ → ℂ) :
    (↑a : ℂ)⁻¹ • ((↑b : ℂ)⁻¹ • g) = (↑(a * b) : ℂ)⁻¹ • g := by
  grind [smul_smul, Units.val_mul, mul_comm]

private noncomputable def gamma0LeftMulQuot (D : HeckeCoset (Gamma0_pair N))
    (σ : (Gamma0_pair N).H) : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) →
    decompQuot (Gamma0_pair N) (HeckeCoset.rep D) :=
  fun i ↦ ⟦⟨σ * i.out, (Gamma0_pair N).H.mul_mem σ.prop (SetLike.coe_mem _)⟩⟧

private lemma gamma0LeftMulQuot_injective (D : HeckeCoset (Gamma0_pair N)) (σ : (Gamma0_pair N).H) :
    Function.Injective (gamma0LeftMulQuot D σ) := by
  intro i₁ i₂ h
  rw [← Quotient.out_eq i₁, ← Quotient.out_eq i₂, Quotient.eq'', QuotientGroup.leftRel_apply]
  convert QuotientGroup.leftRel_apply.mp (Quotient.exact h) using 1
  exact Subtype.ext (by simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group)

private noncomputable def gamma0LeftMulEquiv (D : HeckeCoset (Gamma0_pair N))
    (σ : (Gamma0_pair N).H) : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) ≃
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D) :=
  Equiv.ofBijective _ (gamma0LeftMulQuot_injective D σ).bijective_of_finite

private lemma gamma0TripleDelta_left_eq_h_mul_deltaRep (D : HeckeCoset (Gamma0_pair N))
    (σ : GL (Fin 2) ℚ) (hσ : σ ∈ (Gamma0_pair N).H)
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    gamma0TripleDelta D (σ * (i.out : GL (Fin 2) ℚ))
        ((Gamma0_pair N).H.mul_mem hσ (SetLike.coe_mem _)) 1 (Gamma0_pair N).H.one_mem =
      (⟨σ, (Gamma0_pair N).h₀ hσ⟩ : (Gamma0_pair N).Δ) *
        deltaRepGen D i := by
  simp only [gamma0TripleDelta, mul_assoc, mul_one, deltaRepGen, Submonoid.mk_mul_mk]

private lemma delta0Nebentypus_left_weight (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (σ : GL (Fin 2) ℚ) (hσ : σ ∈ (Gamma0_pair N).H)
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) : delta0NebentypusDeltaChar χ
      (gamma0TripleDelta D (σ * (i.out : GL (Fin 2) ℚ)) ((Gamma0_pair N).H.mul_mem hσ
        (SetLike.coe_mem _)) 1 (Gamma0_pair N).H.one_mem) = delta0NebentypusHChar χ σ hσ *
      delta0NebentypusWeight χ D i :=
  gamma0TripleDelta_left_eq_h_mul_deltaRep D σ hσ i ▸ map_mul _ _ _

private lemma twistedHeckeSlashGen_slash_distrib (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) (g : GL (Fin 2) ℚ) :
    (twistedHeckeSlashGen k χ D f) ∣[k] g =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (((↑(delta0NebentypusWeight χ D i) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] g := by
  simp only [twistedHeckeSlashGen, SlashAction.sum_slash]

private lemma tRep_gen_mul_eq_adjugate_leftMul (D : HeckeCoset (Gamma0_pair N))
    (σ_Q : GL (Fin 2) ℚ) (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    tRep_gen (Gamma0_pair N) D i * σ_Q = GL_adjugate (GL_adjugate σ_Q * (i.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep D : GL (Fin 2) ℚ)) := by
  simp only [GL_adjugate_mul, mul_assoc, GL_adjugate_involutive]

private lemma twistedHeckeSlashGen_perm_summand (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (σ_Q : GL (Fin 2) ℚ) (hσ : σ_Q ∈ (Gamma0_pair N).H)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant k χ f)
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    (((↑(delta0NebentypusWeight χ D i) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q =
      (↑(delta0NebentypusHChar χ (GL_adjugate σ_Q)
          (HeckePairAction.adjugate_mem_H σ_Q hσ)) : ℂ) •
        (((↑(delta0NebentypusWeight χ D
            (gamma0LeftMulEquiv D
              ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩ i)) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D
            (gamma0LeftMulEquiv D
              ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩ i))) := by
  set σA : (Gamma0_pair N).H :=
    ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩
  set π := gamma0LeftMulEquiv D σA
  rw [ModularForm.smul_slash, glMap_sigma_eq_id_of_mem_H σ_Q hσ]
  have hslash :
      (f ∣[k] tRep_gen (Gamma0_pair N) D i) ∣[k] glMap σ_Q =
        f ∣[k] (tRep_gen (Gamma0_pair N) D i * σ_Q) := by
    change (f ∣[k] glMap (tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q =
      f ∣[k] glMap (tRep_gen (Gamma0_pair N) D i * σ_Q)
    rw [map_mul, ← SlashAction.slash_mul]
  rw [hslash, tRep_gen_mul_eq_adjugate_leftMul D σ_Q i]
  have htw' :
      ((↑(delta0NebentypusDeltaChar χ
        (gamma0TripleDelta D (σA.val * (i.out : GL (Fin 2) ℚ))
          ((Gamma0_pair N).H.mul_mem σA.prop (SetLike.coe_mem _))
          1 (Gamma0_pair N).H.one_mem)) : ℂ)⁻¹) •
        (f ∣[k] GL_adjugate (σA.val * (i.out : GL (Fin 2) ℚ) *
          (HeckeCoset.rep D : GL (Fin 2) ℚ))) =
      ((↑(delta0NebentypusWeight χ D (π i)) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D (π i)) := by
    simpa [π, gamma0LeftMulEquiv, gamma0LeftMulQuot, delta0NebentypusWeight,
      Equiv.ofBijective_apply, mul_one]
      using twisted_weighted_slash_tRep_gen_of_mem k χ D
        (σA.val * (i.out : GL (Fin 2) ℚ))
        ((Gamma0_pair N).H.mul_mem σA.prop (SetLike.coe_mem _))
        1 (Gamma0_pair N).H.one_mem f hf
  rw [← htw', delta0Nebentypus_left_weight χ D σA.val σA.prop i]
  exact units_coe_inv_right_smul_eq_mul_smul_inv_mul _ _ _

/-- A single twisted Hecke-coset operator preserves the `Γ₀(N),χ` fixed space. -/
lemma twistedHeckeSlashGen_preserves_invariant (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : IsGamma0TwistedInvariant k χ f) :
    IsGamma0TwistedInvariant k χ
      (twistedHeckeSlashGen k χ D f) := by
  intro σ_Q hσ
  let σA : (Gamma0_pair N).H :=
    ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩
  let π := gamma0LeftMulEquiv D σA
  rw [show (twistedHeckeSlashGen k χ D f) ∣[k] glMap σ_Q =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (((↑(delta0NebentypusWeight χ D i) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q by
    exact twistedHeckeSlashGen_slash_distrib k χ D f σ_Q,
    Finset.sum_congr rfl
      (fun i _ ↦ twistedHeckeSlashGen_perm_summand k χ D σ_Q hσ f hf i),
    ← Finset.smul_sum, Fintype.sum_equiv π _ (fun i ↦
      ((↑(delta0NebentypusWeight χ D i) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D i)) (fun _ ↦ rfl)]
  rfl

private lemma delta0NebentypusWeight_mul_eq_tripleDelta (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (heq : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
        ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) =
      h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    delta0NebentypusWeight χ D₁ p.1 *
        delta0NebentypusWeight χ D₂ p.2 =
      delta0NebentypusDeltaChar χ
        (gamma0TripleDelta D h₁ hh₁ h₂ hh₂) := by
  simp only [delta0NebentypusWeight, ← map_mul]
  exact congrArg _ (Subtype.ext heq)

private lemma twisted_weighted_slash_product_eq (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant k χ f)
    (heq : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
        ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) =
      h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    ((↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) =
      ((↑(delta0NebentypusWeight χ D
          (⟦⟨h₁, hh₁⟩⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D
          (⟦⟨h₁, hh₁⟩⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))) := by
  set q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  calc
    ((↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1)
        = ((↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹) •
            (((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹) •
              ((f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
                tRep_gen (Gamma0_pair N) D₁ p.1)) := by
          rw [smul_slash_tRep_gen k D₁ p.1]
    _ = ((↑(delta0NebentypusWeight χ D₁ p.1 *
            delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹) •
          ((f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) :=
          units_inv_smul_inv_smul_eq_mul_inv_smul (delta0NebentypusWeight χ D₁ p.1)
            (delta0NebentypusWeight χ D₂ p.2)
            ((f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
              tRep_gen (Gamma0_pair N) D₁ p.1)
    _ = ((↑(delta0NebentypusDeltaChar χ
            (gamma0TripleDelta D h₁ hh₁ h₂ hh₂)) : ℂ)⁻¹) •
          (f ∣[k] GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)) := by
          rw [delta0NebentypusWeight_mul_eq_tripleDelta χ D₁ D₂ D p h₁ hh₁ h₂ hh₂ heq,
            ← SlashAction.slash_mul, tRep_gen_mul_anti D₁ D₂ p.1 p.2, heq]
    _ = ((↑(delta0NebentypusWeight χ D q) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D q) := by
          simpa [q, delta0NebentypusWeight] using
            twisted_weighted_slash_tRep_gen_of_mem k χ D h₁ hh₁ h₂ hh₂ f hf

private lemma twisted_slash_and_coset_of_mulMap_eq (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant k χ f)
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (hp : mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D) :
    ∃ q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
      (((↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) =
        ((↑(delta0NebentypusWeight χ D q) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D q)) ∧
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) := by
  have hmem : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet D := by
    have : HeckeCoset.toSet (mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) = HeckeCoset.toSet D := by
      rw [hp]
    rw [← this]
    show _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (Gamma0_pair N))
    simp only [HeckeCoset.toSet_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hmem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hmem
  let q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  refine ⟨q, ?_, ?_⟩
  · exact twisted_weighted_slash_product_eq k χ D₁ D₂ D p h₁ hh₁ h₂ hh₂ f hf heq
  · have hκ : gamma0Correction D q h₁ h₂ ∈ (Gamma0_pair N).H :=
      gamma0Correction_mem_H D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq q)
    rw [Set.singleton_mul_singleton, heq]
    refine leftCoset_eq_of_not_disjoint _ _ _ <| Set.not_disjoint_iff.mpr
      ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
        ⟨1, (Gamma0_pair N).H.one_mem, by simp only [smul_eq_mul, mul_one]⟩,
        ⟨gamma0Correction D q h₁ h₂, hκ, by
          simp only [smul_eq_mul, gamma0Correction]
          group⟩⟩

private lemma gamma0_prod_mem_D_of_rightCoset (D : HeckeCoset (Gamma0_pair N)) (g : GL (Fin 2) ℚ)
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h : GL (Fin 2) ℚ)
    (hh : h ∈ ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)))
    (hprod : g = (q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ) * h) :
    g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  exact ⟨q.out, SetLike.coe_mem q.out, h, hh, hprod⟩

private lemma gamma0_prod_mem_mulMap (D₁ D₂ : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂)) :
    (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet (mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) := by
  simpa only [mulMap, HeckeCoset.toSet_mk] using DoubleCoset.mem_doubleCoset_self _ _ _

private lemma gamma0_mulMap_eq_of_rightCoset (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (hp_rc : ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))) :
    mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D := by
  have h_in_rc : (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      ({(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) := by
    rw [← hp_rc, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, (Gamma0_pair N).H.one_mem, by simp only [mul_one]⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in_rc
  rw [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  refine HeckeCoset_ext_toSet (P := Gamma0_pair N) ?_
  rw [HeckeCoset.toSet_eq_rep, HeckeCoset.toSet_eq_rep]
  refine DoubleCoset.eq_of_not_disjoint (Set.not_disjoint_iff.mpr ?_)
  have hm := gamma0_prod_mem_mulMap D₁ D₂ p
  have hd := gamma0_prod_mem_D_of_rightCoset D _ q h hh hprod.symm
  rw [HeckeCoset.toSet_eq_rep] at hm hd
  exact ⟨_, hm, hd⟩

open Classical in
private lemma twisted_fiber_filter_card_eq (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (q_of : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h_coset_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    ((Finset.univ.filter
        (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
            decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) ↦
          mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
            (p.1, p.2) = D)).filter (fun p ↦ q_of p = q)).card =
      Nat.card
        {p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
             decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))} := by
  refine (Nat.subtype_card _ fun p ↦ ?_).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨hmap, hq⟩ ↦ hq ▸ h_coset_eq p hmap, fun hp_rc ↦ ?_⟩
  have hmap := gamma0_mulMap_eq_of_rightCoset D₁ D₂ D p q hp_rc
  refine ⟨hmap, byContradiction fun hne ↦ decompQuot_coset_diff (Gamma0_pair N)
    (HeckeCoset.rep D) (q_of p) q hne ((h_coset_eq p hmap).symm.trans hp_rc)⟩

private lemma twisted_filtered_sum_collapse_of_qOf {M : Type*} [AddCommGroup M]
    [DecidableEq (HeckeCoset (Gamma0_pair N))] (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (q_of : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (F : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) → M)
    (G : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) → M)
    (h_term_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2) = D → F p = G (q_of p))
    (h_coset_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
                 decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) =>
          mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
            (p.1, p.2) = D), F p) =
      (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D • ∑ q, G q := by
  classical
  set S := Finset.univ.filter
    (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) ↦
      mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D)
  rw [Finset.sum_congr rfl (fun p hp ↦ by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact h_term_eq p hp), ← Finset.sum_fiberwise' (s := S) (g := q_of)]
  simp_rw [Finset.sum_const]
  have h_fiber_eq : ∀ q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
      (S.filter (fun p ↦ q_of p = q)).card = Nat.card
        {p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
             decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))} := by
    intro q
    convert twisted_fiber_filter_card_eq D₁ D₂ D q_of h_coset_eq q using 4
  simp_rw [h_fiber_eq,
    heckeMultiplicity_uniform (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D]
  rw [Finset.sum_nsmul]
  simp only [m, Finsupp.coe_mk, heckeMultiplicity, Nat.cast_smul_eq_nsmul ℤ]

private lemma twistedHeckeSlashGen_fiber_sum [DecidableEq (HeckeCoset (Gamma0_pair N))]
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (_hD : D ∈ mulSupport (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant k χ f) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
                 decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) =>
          mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D),
      (↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹ •
        (((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹ •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1)) =
    (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D •
      ∑ q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (↑(delta0NebentypusWeight χ D q) : ℂ)⁻¹ •
          (f ∣[k] tRep_gen (Gamma0_pair N) D q) := by
  classical
  have h_main := twisted_slash_and_coset_of_mulMap_eq k χ D₁ D₂ D f hf
  set q_of : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := fun p ↦
    if h : mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D
    then (h_main p h).choose else ⟦1⟧
  have h_term_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D →
      (↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹ •
        (((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹ •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k] tRep_gen (Gamma0_pair N) D₁ p.1) =
      (↑(delta0NebentypusWeight χ D (q_of p)) : ℂ)⁻¹ •
        (f ∣[k] tRep_gen (Gamma0_pair N) D (q_of p)) := by
    intro p hp
    simp only [q_of, hp, dif_pos]
    exact (h_main p hp).choose_spec.1
  have h_coset_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) := by
    intro p hp
    simp only [q_of, hp, dif_pos]
    exact (h_main p hp).choose_spec.2
  exact twisted_filtered_sum_collapse_of_qOf D₁ D₂ D q_of
    (fun p ↦ (↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹ •
      (((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹ •
        (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k] tRep_gen (Gamma0_pair N) D₁ p.1))
    (fun q ↦ (↑(delta0NebentypusWeight χ D q) : ℂ)⁻¹ •
      (f ∣[k] tRep_gen (Gamma0_pair N) D q))
    h_term_eq h_coset_eq

private lemma twistedHeckeSlashGen_comp_eq_prod_sum (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) :
    twistedHeckeSlashGen k χ D₁
        (twistedHeckeSlashGen k χ D₂ f) =
      ∑ p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
          decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂),
        ((↑(delta0NebentypusWeight χ D₁ p.1) : ℂ)⁻¹) •
          ((((↑(delta0NebentypusWeight χ D₂ p.2) : ℂ)⁻¹) •
            (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
              tRep_gen (Gamma0_pair N) D₁ p.1) := by
  simp only [twistedHeckeSlashGen, SlashAction.sum_slash, Finset.smul_sum,
    ← Fintype.sum_prod_type']

private lemma twistedHeckeSlashExtGen_T_single_one_mul_eq_m_sum (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) :
    twistedHeckeSlashExtGen k χ
        (T_single (Gamma0_pair N) ℤ D₁ 1 * T_single (Gamma0_pair N) ℤ D₂ 1) f =
      (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).sum
        (fun D c ↦ c • twistedHeckeSlashGen k χ D f) := by
  simp only [twistedHeckeSlashExtGen, mul_singleton_𝕋, one_smul, zsmul_eq_mul]

private lemma twistedHeckeSlashGen_comp_eq_m_sum (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : IsGamma0TwistedInvariant k χ f) :
    twistedHeckeSlashGen k χ D₁
        (twistedHeckeSlashGen k χ D₂ f) =
      (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).sum
        (fun D c ↦ c • twistedHeckeSlashGen k χ D f) := by
  rw [twistedHeckeSlashGen_comp_eq_prod_sum k χ D₁ D₂ f]
  letI : DecidableEq (HeckeCoset (Gamma0_pair N)) := Classical.decEq _
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p ↦ mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
      (p.1, p.2))
    (fun p _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    Finsupp.sum, m_support, mulSupport]
  exact Finset.sum_congr rfl fun D hD ↦
    twistedHeckeSlashGen_fiber_sum k χ D₁ D₂ D hD f hf

/-- Multiplicativity of the twisted slash action on `Γ₀(N),χ`-invariant
functions, using the existing `Γ₀(N)` Hecke-ring multiplication. -/
theorem twistedHeckeSlashGen_comp (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : IsGamma0TwistedInvariant k χ f)
    (hcomm : T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1 =
      T_single (Gamma0_pair N) ℤ D₁ 1 * T_single (Gamma0_pair N) ℤ D₂ 1) :
    twistedHeckeSlashGen k χ D₁
        (twistedHeckeSlashGen k χ D₂ f) =
      twistedHeckeSlashExtGen k χ
        (T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1) f := by
  rw [twistedHeckeSlashExtGen_T_single_one_mul_eq_m_sum k χ D₂ D₁ f,
    show m (Gamma0_pair N) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) by
      simp only [T_single_one_mul_T_single_one] at hcomm; exact hcomm]
  exact twistedHeckeSlashGen_comp_eq_m_sum k χ D₁ D₂ f hf

private lemma twistedHeckeSlashExtGen_zsmul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : ℤ)
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : ℍ → ℂ) :
    twistedHeckeSlashExtGen k χ (n • T) f =
      n • twistedHeckeSlashExtGen k χ T f := by
  unfold twistedHeckeSlashExtGen
  have hsmi : (n • T).sum (fun D c ↦ c • twistedHeckeSlashGen k χ D f) =
      T.sum (fun D a ↦ (n * a) • twistedHeckeSlashGen k χ D f) :=
    Finsupp.sum_smul_index (fun _ ↦ zero_smul ℤ _)
  rw [hsmi, Finsupp.smul_sum]
  exact Finsupp.sum_congr fun D _ ↦ SemigroupAction.mul_smul _ _ _

/-- The endomorphism of the `Γ₀(N),χ`-invariant function submodule
attached to a single `Γ₀(N)` Hecke double coset. -/
noncomputable def twistedHeckeOperatorFunction (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) :
    Module.End ℂ (gamma0TwistedInvariantFunctionSubmodule k χ) where
  toFun f := ⟨twistedHeckeSlashGen k χ D f,
    twistedHeckeSlashGen_preserves_invariant k χ D f f.property⟩
  map_add' f g := by ext z; simp only [Submodule.coe_add, twistedHeckeSlashGen_add, Pi.add_apply]
  map_smul' c f := by
    ext z
    simp only [SetLike.val_smul, twistedHeckeSlashGen_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- The `ℤ`-linear extension of the twisted coset operators over the existing
Hecke ring source `𝕋 (Gamma0_pair N) ℤ`. -/
noncomputable def twistedHeckeSumFunction (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) : Module.End ℂ (gamma0TwistedInvariantFunctionSubmodule k χ) :=
  T.sum (fun D c ↦ (c : ℂ) • twistedHeckeOperatorFunction k χ D)

/-- `twistedHeckeSumFunction` at the zero element of `𝕋 (Gamma0_pair N) ℤ` is zero. -/
@[simp] lemma twistedHeckeSumFunction_zero (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    twistedHeckeSumFunction k χ (0 : 𝕋 (Gamma0_pair N) ℤ) = 0 :=
  Finsupp.sum_zero_index

/-- `twistedHeckeSumFunction` applied to a basis element `T_single D c` equals
`c • twistedHeckeOperatorFunction D`. -/
@[simp] lemma twistedHeckeSumFunction_T_single (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (c : ℤ) :
    twistedHeckeSumFunction k χ (T_single (Gamma0_pair N) ℤ D c) =
      (c : ℂ) • twistedHeckeOperatorFunction k χ D := by
  simp only [twistedHeckeSumFunction, T_single, Int.cast_zero, zero_smul, Finsupp.sum_single_index]

/-- `twistedHeckeSumFunction` is additive in the Hecke-ring element. -/
@[simp] lemma twistedHeckeSumFunction_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) : twistedHeckeSumFunction k χ (T₁ + T₂) =
      twistedHeckeSumFunction k χ T₁ + twistedHeckeSumFunction k χ T₂ := by
  unfold twistedHeckeSumFunction
  refine Finsupp.sum_add_index' (fun D ↦ ?_) (fun D c₁ c₂ ↦ ?_)
  · simp only [Int.cast_zero, zero_smul]
  · ext f z
    simp only [Int.cast_add, add_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      SetLike.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Applying the endomorphism-valued extension agrees with the function-valued
weighted extension. -/
lemma twistedHeckeSumFunction_apply_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : gamma0TwistedInvariantFunctionSubmodule k χ) :
    (twistedHeckeSumFunction k χ T f : ℍ → ℂ) = twistedHeckeSlashExtGen k χ T f := by
  induction T using HeckeRing.induction_linear_𝕋 with
  | h_zero => rfl
  | h_add T₁ T₂ h₁ h₂ =>
      rw [twistedHeckeSumFunction_add, twistedHeckeSlashExtGen_add]
      ext z
      simp only [LinearMap.add_apply, Submodule.coe_add, h₁, h₂, Pi.add_apply]
  | h_single D c =>
      simp only [twistedHeckeSumFunction_T_single, twistedHeckeOperatorFunction, Algebra.smul_def,
        map_intCast, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk,
        Module.End.intCast_apply, SetLike.val_smul_of_tower, eq_intCast, twistedHeckeSlashExtGen,
        Int.cast_zero, zero_mul, Finsupp.sum_single_index]

private lemma twistedHeckeSumFunction_mul_T_single (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (a b : ℤ) :
    twistedHeckeSumFunction k χ
        (T_single (Gamma0_pair N) ℤ D₁ a * T_single (Gamma0_pair N) ℤ D₂ b) =
      twistedHeckeSumFunction k χ (T_single (Gamma0_pair N) ℤ D₁ a) *
        twistedHeckeSumFunction k χ (T_single (Gamma0_pair N) ℤ D₂ b) := by
  rw [Gamma0_pair_HeckeAlgebra_mul_comm N
    (T_single (Gamma0_pair N) ℤ D₁ a) (T_single (Gamma0_pair N) ℤ D₂ b)]
  ext f z
  rw [twistedHeckeSumFunction_apply_coe]
  have h_prod : T_single (Gamma0_pair N) ℤ D₂ b *
      T_single (Gamma0_pair N) ℤ D₁ a =
      (b * a) • (T_single (Gamma0_pair N) ℤ D₂ 1 *
        T_single (Gamma0_pair N) ℤ D₁ 1) := by
    rw [HeckeRing.T_single_mul_T_single, HeckeRing.T_single_mul_T_single,
      one_smul, one_smul, ← SemigroupAction.mul_smul]
    rfl
  rw [h_prod, twistedHeckeSlashExtGen_zsmul]
  rw [← twistedHeckeSlashGen_comp k χ D₁ D₂ (f : ℍ → ℂ)
    f.property (Gamma0_pair_HeckeAlgebra_mul_comm N
      (T_single (Gamma0_pair N) ℤ D₂ 1) (T_single (Gamma0_pair N) ℤ D₁ 1))]
  simp only [Module.End.mul_apply]
  rw [twistedHeckeSumFunction_T_single, twistedHeckeSumFunction_T_single]
  simp only [LinearMap.smul_apply]
  rw [(twistedHeckeOperatorFunction k χ D₁).map_smul]
  simp only [mul_comm, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, mul_assoc,
    twistedHeckeOperatorFunction, LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul, smul_eq_mul]

/-- Multiplicativity of the endomorphism-valued twisted action for all elements
of the existing Hecke ring `𝕋 (Gamma0_pair N) ℤ`. -/
lemma twistedHeckeSumFunction_mul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    twistedHeckeSumFunction k χ (T₁ * T₂) = twistedHeckeSumFunction k χ T₁ *
      twistedHeckeSumFunction k χ T₂ := by
  induction T₁ using HeckeRing.induction_linear_𝕋 with
  | h_zero => rw [zero_mul, twistedHeckeSumFunction_zero, zero_mul]
  | h_single D₁ a =>
      induction T₂ using HeckeRing.induction_linear_𝕋 with
      | h_zero => rw [mul_zero, twistedHeckeSumFunction_zero, mul_zero]
      | h_single D₂ b =>
          exact twistedHeckeSumFunction_mul_T_single k χ D₁ D₂ a b
      | h_add T₂ T₂' h h' =>
          rw [mul_add, twistedHeckeSumFunction_add, twistedHeckeSumFunction_add,
            h, h', mul_add]
  | h_add T₁ T₁' h h' =>
      rw [add_mul, twistedHeckeSumFunction_add, twistedHeckeSumFunction_add,
        h, h', add_mul]

private lemma twistedHeckeSlashGen_identity_coset (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant k χ f) :
    twistedHeckeSlashGen k χ (HeckeCoset.one (Gamma0_pair N)) f = f := by
  haveI : Subsingleton (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) :=
    subsingleton_decompQuot_T_one (Gamma0_pair N)
  haveI : Nonempty (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) :=
    one_in_decompQuot_T_one (Gamma0_pair N)
  haveI : Unique (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) := uniqueOfSubsingleton default
  unfold twistedHeckeSlashGen
  rw [show (Finset.univ : Finset (decompQuot (Gamma0_pair N)
        (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N))))) = {default} from
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_univ _, fun i _ ↦ Subsingleton.elim _ _⟩, Finset.sum_singleton]
  set q : decompQuot (Gamma0_pair N)
    (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N))) := default
  have h_adj_mem : tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q ∈
      (Gamma0_pair N).H :=
    HeckePairAction.adjugate_mem_H _ <|
      (Gamma0_pair N).H.mul_mem (SetLike.coe_mem _) (HeckeCoset.one_rep_mem_H _)
  have hchar :
      delta0NebentypusHChar χ
        (GL_adjugate (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q))
        (HeckePairAction.adjugate_mem_H _ h_adj_mem) =
      delta0NebentypusWeight χ (HeckeCoset.one (Gamma0_pair N)) q :=
    congrArg (delta0NebentypusDeltaChar χ)
      (Subtype.ext (by simp only [tRep_gen, GL_adjugate_involutive, deltaRepGen]))
  change (↑(delta0NebentypusWeight χ (HeckeCoset.one (Gamma0_pair N)) q) : ℂ)⁻¹ •
      (f ∣[k] glMap (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q)) = f
  rw [hf _ h_adj_mem, hchar]
  ext z
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, Units.ne_zero, not_false_eq_true,
    inv_mul_cancel_left₀]

/-- The twisted Hecke operator at the identity coset is the identity endomorphism. -/
@[simp] lemma twistedHeckeOperatorFunction_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    twistedHeckeOperatorFunction k χ (HeckeCoset.one (Gamma0_pair N)) = 1 :=
  LinearMap.ext fun f ↦ Subtype.ext (twistedHeckeSlashGen_identity_coset k χ ↑f f.property)

/-- `twistedHeckeSumFunction` sends the unit of the Hecke ring to the identity operator. -/
@[simp] lemma twistedHeckeSumFunction_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    twistedHeckeSumFunction k χ (1 : 𝕋 (Gamma0_pair N) ℤ) = 1 := by
  simp only [one_def, twistedHeckeSumFunction_T_single, Int.cast_one,
    twistedHeckeOperatorFunction_one, one_smul]

end HeckeRing.GL2.Unified
