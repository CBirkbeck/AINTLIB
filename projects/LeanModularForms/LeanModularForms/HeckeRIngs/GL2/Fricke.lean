/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace

/-!
# The Fricke operator on `M_k(Γ₁(N))`

This file defines the Fricke involution `W_N` on modular forms for `Γ₁(N)`.

The Fricke matrix is `W = (0, -1; N, 0) ∈ GL₂(ℚ)` (determinant `N`).  It satisfies the
matrix identities (all verified below):

* `W⁻¹ = (0, 1/N; -1, 0)` and `W² = -N · I`;
* `W` *normalizes* `Γ₁(N)` (and `Γ₀(N)`): for `γ = (a, b; Nc, d) ∈ Γ₁(N)`,
  `W⁻¹ · γ · W = (d, -c; -Nb, a) ∈ Γ₁(N)` (and equals `W · γ · W⁻¹`, since `W²` is central);
* on a diamond representative `σ_d ∈ Γ₀(N)` with `Gamma0MapUnits σ_d = d`, the conjugate
  `W⁻¹ · σ_d · W` has `Gamma0MapUnits = d⁻¹`.

Consequently the slash-by-`W` operator `frickeOperator` is a `ℂ`-linear endomorphism of
`M_k(Γ₁(N))` (slash-invariance from normalization, boundedness at cusps from the
`Gamma1_isCusp`-style transport), it satisfies `frickeOperator ∘ ⟨d⟩ = ⟨d⁻¹⟩ ∘ frickeOperator`,
and `frickeOperator ∘ frickeOperator` is a scalar.  It therefore maps the Nebentypus space
`modFormCharSpace k χ` isomorphically onto `modFormCharSpace k (chiConj χ)` where
`chiConj χ = χ ∘ (·)⁻¹`.

This packages the algebraic input needed to define the Shimura-convention Hecke action `Ψ`
as the Fricke conjugate of the existing companion `Φ = heckeRingHomCharSpace`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.
* Atkin–Lehner, *Hecke operators on `Γ₀(m)`*.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The Fricke matrix `W = (0, -1; N, 0)` as an element of `GL₂(ℚ)` (determinant `N ≠ 0`). -/
noncomputable def frickeGL (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℚ), 0]
    (by rw [det_fin_two_of]; simpa using (NeZero.ne (N : ℚ)).symm ∘ Eq.symm)

@[simp] lemma frickeGL_coe :
    (↑(frickeGL N) : Matrix (Fin 2) (Fin 2) ℚ) = !![0, -1; (N : ℚ), 0] := rfl

lemma frickeGL_det : (↑(frickeGL N) : Matrix (Fin 2) (Fin 2) ℚ).det = N := by
  rw [frickeGL_coe, det_fin_two_of]; ring

@[simp] lemma frickeGL_det_val : (frickeGL N).det.val = N := by
  rw [GeneralLinearGroup.val_det_apply, frickeGL_det]

lemma frickeGL_det_pos : 0 < (frickeGL N).det.val := by
  rw [frickeGL_det_val]; exact_mod_cast NeZero.pos N

/-- The inverse Fricke matrix `W⁻¹ = (0, 1/N; -1, 0)`. -/
lemma frickeGL_inv_coe :
    (↑(frickeGL N)⁻¹ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1 / (N : ℚ); -1, 0] := by
  have hN : (N : ℚ) ≠ 0 := NeZero.ne _
  rw [GeneralLinearGroup.coe_inv, frickeGL_coe, Matrix.inv_def,
    show (!![0, -1; (N : ℚ), 0] : Matrix (Fin 2) (Fin 2) ℚ).det = N by
      rw [det_fin_two_of]; ring,
    Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

/-- `W² = (-N) • I` as matrices. -/
lemma frickeGL_sq_coe :
    (↑(frickeGL N * frickeGL N) : Matrix (Fin 2) (Fin 2) ℚ) =
      (-(N : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  rw [GeneralLinearGroup.coe_mul, frickeGL_coe]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The bad-prime representative `δ_r = [[1,0],[N·r,p]] ∈ GL₂(ℚ)` (det `p`). -/
noncomputable def lunipRep (p : ℕ) (hp : 0 < p) (r : ℕ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; (N : ℚ) * r, (p : ℚ)]
    (by rw [det_fin_two_of]; simpa using (Nat.cast_ne_zero (R := ℚ)).mpr hp.ne')

omit [NeZero N] in
@[simp] lemma lunipRep_coe (p : ℕ) (hp : 0 < p) (r : ℕ) :
    (↑(lunipRep (N := N) p hp r) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![1, 0; (N : ℚ) * r, (p : ℚ)] := rfl

/-- **Bad-prime `U_p`-matching matrix identity** (machine-verified): the `W`-conjugate of the
adjugate of the lower-unipotent bad representative `δ_r = [[1,0],[N·r,p]]` is exactly the `U_p`
representative `T_p_upper(r) = [[1,r],[0,p]]`:
`W · adj(δ_r) · W⁻¹ = T_p_upper(r)`.
(`adj(δ_r) = [[p,0],[−N·r,1]]`; this is the core of the `Ψ(D_p) = U_p` bridge at `p ∣ N`.) -/
lemma frickeGL_mul_adj_lunipRep_mul_frickeGL_inv (p : ℕ) (hp : 0 < p) (r : ℕ) :
    frickeGL N * GL_adjugate (lunipRep (N := N) p hp r) * (frickeGL N)⁻¹ = T_p_upper p hp r := by
  apply Units.ext
  have hNc : (N : ℚ) ≠ 0 := NeZero.ne _
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, GL_adjugate_val, lunipRep_coe,
    Matrix.adjugate_fin_two, frickeGL_coe, frickeGL_inv_coe, T_p_upper_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- The integer `c'` with `c = N · c'` for a `Γ₀(N)` matrix `σ` (lower-left entry over `N`). -/
private noncomputable def botLeftDiv (σ : ↥(Gamma0 N)) : ℤ :=
  ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ.property)).choose

omit [NeZero N] in
private lemma botLeftDiv_spec (σ : ↥(Gamma0 N)) :
    (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = N * botLeftDiv σ :=
  ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ.property)).choose_spec

/-- The conjugate `W · σ · W⁻¹` of a `Γ₀(N)` element `σ = (a, b; Nc', d)`, as an integer
`SL₂(ℤ)` matrix `(d, -c'; -Nb, a)`.  (Using `W² = -N·I` central, this equals `W⁻¹ · σ · W`.) -/
noncomputable def frickeConjSL (σ : ↥(Gamma0 N)) : SL(2, ℤ) :=
  ⟨!![(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -botLeftDiv σ;
      -(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0], by
    set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.1.prop; rwa [det_fin_two] at this
    rw [det_fin_two_of]
    have hc := botLeftDiv_spec σ
    rw [← hM] at hc
    linear_combination hdet + M 0 1 * hc⟩

omit [NeZero N] in
@[simp] lemma frickeConjSL_coe (σ : ↥(Gamma0 N)) :
    (frickeConjSL σ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -botLeftDiv σ;
         -(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
         (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0] := rfl

omit [NeZero N] in
/-- The conjugate stays in `Γ₀(N)`: its lower-left entry `-Nb` is divisible by `N`. -/
lemma frickeConjSL_mem_Gamma0 (σ : ↥(Gamma0 N)) : frickeConjSL σ ∈ Gamma0 N := by
  rw [Gamma0_mem, frickeConjSL_coe]
  show ((-(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod N) = 0
  push_cast; simp

omit [NeZero N] in
/-- The conjugate of a `Γ₁(N)` element stays in `Γ₁(N)`: the diagonal entries `(d, a)`
remain `≡ 1 (mod N)`. -/
lemma frickeConjSL_mem_Gamma1 (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) :
    frickeConjSL ⟨σ, Gamma1_in_Gamma0 N hσ⟩ ∈ Gamma1 N := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N σ).mp hσ
  rw [Gamma1_mem, frickeConjSL_coe]
  refine ⟨?_, ?_, ?_⟩
  · show ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = 1; exact hd
  · show ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) = 1; exact ha
  · show ((-(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod N) = 0
    push_cast; simp

omit [NeZero N] in
/-- The diamond image of the conjugate is the **inverse**: `Gamma0MapUnits (frickeConjSL σ) =
(Gamma0MapUnits σ)⁻¹`.  (The lower-right entry of `frickeConjSL σ` is `a ≡ d⁻¹ (mod N)`.) -/
lemma Gamma0MapUnits_frickeConjSL (σ : ↥(Gamma0 N)) :
    Gamma0MapUnits ⟨frickeConjSL σ, frickeConjSL_mem_Gamma0 σ⟩ = (Gamma0MapUnits σ)⁻¹ := by
  have hc : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 := Gamma0_mem.mp σ.property
  have hdet : (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := σ.1.prop
    rwa [det_fin_two] at this
  rw [eq_inv_iff_mul_eq_one]
  ext
  simp only [Units.val_mul, Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_one, frickeConjSL_coe, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.of_apply]
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] using
    congrArg (Int.cast : ℤ → ZMod N) hdet

/-- **`W` normalizes `Γ₀(N)`** (the core matrix identity): `W · σ = (frickeConjSL σ) · W`
in `GL₂(ℚ)`, for `σ ∈ Γ₀(N)`. -/
lemma frickeGL_mul_mapGL (σ : ↥(Gamma0 N)) :
    frickeGL N * mapGL ℚ (σ : SL(2, ℤ)) =
      mapGL ℚ (frickeConjSL σ) * frickeGL N := by
  apply Units.ext
  have hc : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) = (N : ℚ) * (botLeftDiv σ : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (botLeftDiv_spec σ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, frickeGL_coe,
      mapGL_coe_matrix, RingHom.mapMatrix_apply, Matrix.map_apply, frickeConjSL_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      algebraMap_int_eq, Int.coe_castRingHom, SpecialLinearGroup.map_apply_coe, Fin.isValue] <;>
    push_cast [hc] <;> ring

/-- The left-multiplication normalization identity: `σ · W = W · (frickeConjSL σ)` in
`GL₂(ℚ)`, for `σ ∈ Γ₀(N)` (equivalently `frickeConjSL σ = W⁻¹ · σ · W`, since `W²` is
central). -/
lemma mapGL_mul_frickeGL (σ : ↥(Gamma0 N)) :
    mapGL ℚ (σ : SL(2, ℤ)) * frickeGL N =
      frickeGL N * mapGL ℚ (frickeConjSL σ) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul]
  have hc : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) = (N : ℚ) * (botLeftDiv σ : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (botLeftDiv_spec σ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, frickeGL_coe,
      mapGL_coe_matrix, RingHom.mapMatrix_apply, Matrix.map_apply, frickeConjSL_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      algebraMap_int_eq, Int.coe_castRingHom, SpecialLinearGroup.map_apply_coe, Fin.isValue] <;>
    push_cast [hc] <;> ring

/-- Real form of the normalization identity: `glMap W · mapGL ℝ σ = mapGL ℝ (frickeConjSL σ) ·
glMap W` for `σ ∈ Γ₀(N)`. -/
lemma glMap_frickeGL_mul_mapGL (σ : ↥(Gamma0 N)) :
    glMap (frickeGL N) * mapGL ℝ (σ : SL(2, ℤ)) =
      mapGL ℝ (frickeConjSL σ) * glMap (frickeGL N) := by
  rw [← glMap_mapGL_eq, ← glMap_mapGL_eq, ← map_mul, ← map_mul, frickeGL_mul_mapGL]

/-- Real form of `mapGL_mul_frickeGL`: `mapGL ℝ σ · glMap W = glMap W · mapGL ℝ (frickeConjSL σ)`. -/
lemma mapGL_mul_glMap_frickeGL (σ : ↥(Gamma0 N)) :
    mapGL ℝ (σ : SL(2, ℤ)) * glMap (frickeGL N) =
      glMap (frickeGL N) * mapGL ℝ (frickeConjSL σ) := by
  rw [← glMap_mapGL_eq, ← glMap_mapGL_eq, ← map_mul, ← map_mul, mapGL_mul_frickeGL]

/-- Slash-invariance of `f ∣[k] W` under `Γ₁(N)`: for `f` invariant under
`(Γ₁(N)).map (mapGL ℝ)`, the slash `f ∣[k] W` is again invariant.  Uses that `W` conjugates
`Γ₁(N)` into itself (`frickeConjSL_mem_Gamma1`). -/
lemma frickeSlash_invariant {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (f ∣[k] (frickeGL N : GL (Fin 2) ℚ)) ∣[k] γ = f ∣[k] (frickeGL N : GL (Fin 2) ℚ) := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  change (f ∣[k] glMap (frickeGL N)) ∣[k] mapGL ℝ σ = f ∣[k] glMap (frickeGL N)
  rw [← SlashAction.slash_mul, glMap_frickeGL_mul_mapGL ⟨σ, Gamma1_in_Gamma0 N hσ⟩,
    SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, frickeConjSL_mem_Gamma1 σ hσ, rfl⟩)]

/-- Cusp transport for `W`: a cusp `c` for `Γ₁(N).map (mapGL ℝ)` is carried by `glMap W` to
another such cusp.  (Mirrors `Gamma1_isCusp_glMap_smul` for `T_p`.) -/
private lemma frickeGL_isCusp_smul {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap (frickeGL N) • c) ((Gamma1 N).map (mapGL ℝ)) := by
  have hc_SL : IsCusp c ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) :=
    hc.mono (Subgroup.map_mono le_top)
  rw [← MonoidHom.range_eq_map] at hc_SL
  have hsmul_SL : IsCusp (glMap (frickeGL N) • c) (mapGL ℝ : SL(2, ℤ) →* _).range := by
    rw [isCusp_SL2Z_iff] at hc_SL ⊢
    obtain ⟨q, rfl⟩ := hc_SL
    refine ⟨frickeGL N • q, ?_⟩
    show OnePoint.map (algebraMap ℚ ℝ) (frickeGL N • q) =
      glMap (frickeGL N) • OnePoint.map (algebraMap ℚ ℝ) q
    simp [OnePoint.map_smul, glMap]
  rw [MonoidHom.range_eq_map] at hsmul_SL
  haveI : ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) := ⟨by
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  exact hsmul_SL.of_isFiniteRelIndex

private lemma frickeGL_bdd_at_cusps (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (⇑f ∣[k] (frickeGL N : GL (Fin 2) ℚ)) k :=
  OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (frickeGL_isCusp_smul hc))

/-- **The Fricke operator `W_N`** on `M_k(Γ₁(N))`: `f ↦ f ∣[k] W`, where `W = (0, -1; N, 0)`.
A `ℂ`-linear endomorphism (slash-invariance from `W` normalizing `Γ₁(N)`, boundedness at the
cusps from `frickeGL_isCusp_smul`). -/
noncomputable def frickeOperator (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (frickeGL N : GL (Fin 2) ℚ)
        slash_action_eq' _ hγ :=
          frickeSlash_invariant
            (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (ModularFormClass.holo f).slash k _
      bdd_at_cusps' hc := frickeGL_bdd_at_cusps k f hc }
  map_add' f g := by
    ext z; show ((⇑(f + g)) ∣[k] glMap (frickeGL N)) z = _
    simp [SlashAction.add_slash, ModularForm.add_apply]; rfl
  map_smul' c f := by
    ext z; change ((c • ⇑f) ∣[k] (frickeGL N : GL (Fin 2) ℚ)) z = c • _
    rw [smul_slash_pos_det k c _ _ frickeGL_det_pos]; rfl

@[simp] lemma frickeOperator_coe (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(frickeOperator (N := N) k f) : ℍ → ℂ) = ⇑f ∣[k] (frickeGL N : GL (Fin 2) ℚ) := rfl

/-- **Diamond shift**: `W ∘ ⟨d⟩ = ⟨d⁻¹⟩ ∘ W`.  Concretely on functions
`(⟨d⟩ f) ∣ W = ⟨d⁻¹⟩ (f ∣ W)`, because `W · σ_d = σ_{d⁻¹}' · W` with
`Gamma0MapUnits σ_{d⁻¹}' = d⁻¹`. -/
theorem frickeOperator_diamondOp (k : ℤ) (d : (ZMod N)ˣ) :
    (frickeOperator (N := N) k).comp (diamondOp k d) =
      (diamondOp k d⁻¹).comp (frickeOperator (N := N) k) := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
  have hg' : Gamma0MapUnits ⟨frickeConjSL g, frickeConjSL_mem_Gamma0 g⟩ = d⁻¹ := by
    rw [Gamma0MapUnits_frickeConjSL, hg]
  ext f z
  show (frickeOperator k (diamondOp k d f)) z = (diamondOp k d⁻¹ (frickeOperator k f)) z
  rw [diamondOp_eq_diamondOpAux k d g hg, diamondOp_eq_diamondOpAux k d⁻¹ _ hg']
  show ((⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k] glMap (frickeGL N)) z =
    ((⇑f ∣[k] glMap (frickeGL N)) ∣[k] mapGL ℝ (frickeConjSL g : SL(2, ℤ))) z
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, mapGL_mul_glMap_frickeGL g]

/-- The scalar `c` with `frickeOperator ∘ frickeOperator = c • id`, namely
`c = N^{2(k-1)} · (-N)^{-k}` (from `W² = (-N)·I` and the weight-`k` slash normalization). -/
noncomputable def frickeScalar (N : ℕ) (k : ℤ) : ℂ :=
  (N : ℂ) ^ (2 * (k - 1)) * (-(N : ℂ)) ^ (-k)

lemma frickeScalar_ne_zero (k : ℤ) : frickeScalar N k ≠ 0 := by
  have hNc : (N : ℂ) ≠ 0 := NeZero.ne _
  refine mul_ne_zero (zpow_ne_zero _ hNc) (zpow_ne_zero _ ?_)
  simpa using hNc

/-- Slashing by `W² = (-N)·I` is multiplication by the scalar `frickeScalar N k`. -/
lemma frickeGL_sq_slash (k : ℤ) (f : UpperHalfPlane → ℂ) :
    f ∣[k] (frickeGL N * frickeGL N : GL (Fin 2) ℚ) = frickeScalar N k • f := by
  ext z
  show (f ∣[k] glMap (frickeGL N * frickeGL N)) z = _
  rw [ModularForm.slash_apply]
  have hNpos : (0 : ℚ) < N := by exact_mod_cast NeZero.pos N
  have hdetpos : 0 < (frickeGL N * frickeGL N : GL (Fin 2) ℚ).det.val := by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_mul, Matrix.det_mul, frickeGL_det]
    positivity
  have hσ : UpperHalfPlane.σ (glMap (frickeGL N * frickeGL N)) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos (glMap_det_pos_of_rat_det_pos _ hdetpos)]
  rw [hσ]
  have hentry : ∀ i j, (glMap (frickeGL N * frickeGL N)) i j =
      (((-(N : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) i j : ℝ) := by
    intro i j
    show (algebraMap ℚ ℝ) ((frickeGL N * frickeGL N : GL (Fin 2) ℚ).val i j) = _
    rw [frickeGL_sq_coe]
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have hsmul : (glMap (frickeGL N * frickeGL N)) • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (glMap_det_pos_of_rat_det_pos _ hdetpos)]
    show ((glMap (frickeGL N * frickeGL N)) 0 0 * (z : ℂ) +
        (glMap (frickeGL N * frickeGL N)) 0 1) /
        ((glMap (frickeGL N * frickeGL N)) 1 0 * (z : ℂ) +
          (glMap (frickeGL N * frickeGL N)) 1 1) = (z : ℂ)
    rw [hentry 0 0, hentry 0 1, hentry 1 0, hentry 1 1]
    have hNc : (N : ℂ) ≠ 0 := NeZero.ne _
    norm_num [Matrix.smul_apply, Matrix.one_apply]
    field_simp
  have hdenom : UpperHalfPlane.denom (glMap (frickeGL N * frickeGL N)) z = (-N : ℂ) := by
    show (glMap (frickeGL N * frickeGL N)) 1 0 * (z : ℂ) +
        (glMap (frickeGL N * frickeGL N)) 1 1 = _
    rw [hentry 1 0, hentry 1 1]
    norm_num [Matrix.smul_apply, Matrix.one_apply]
  have habsdet : (↑|(glMap (frickeGL N * frickeGL N)).det.val| : ℂ) = (N : ℂ) ^ 2 := by
    have hdet : (glMap (frickeGL N * frickeGL N)).det.val =
        algebraMap ℚ ℝ (frickeGL N * frickeGL N : GL (Fin 2) ℚ).det.val :=
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _)
    rw [hdet, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_mul, Matrix.det_mul,
      frickeGL_det, abs_of_nonneg (by positivity)]
    push_cast
    ring
  rw [hsmul, hdenom, habsdet]
  show f z * ((N : ℂ) ^ 2) ^ (k - 1) * (-(N : ℂ)) ^ (-k) = frickeScalar N k • f z
  rw [frickeScalar, smul_eq_mul,
    show ((N : ℂ) ^ 2) ^ (k - 1) = (N : ℂ) ^ (2 * (k - 1)) by
      rw [show ((N : ℂ) ^ 2) = (N : ℂ) ^ (2 : ℤ) by norm_cast, ← _root_.zpow_mul]]
  ring

/-- Per-term Fricke conjugation: slashing by `A · W` equals `c •` slashing by `A · W⁻¹`,
since `A · W = (A · W⁻¹) · W²` and `W²` slashes by `c = frickeScalar N k`.  This is the
identity that makes the two Fricke factors in `Ψ = E.symm ∘ Φ ∘ E` collapse to a `W`-conjugation
of the slash representatives. -/
lemma slash_mul_frickeGL (k : ℤ) (f : UpperHalfPlane → ℂ) (A : GL (Fin 2) ℚ) :
    f ∣[k] (A * frickeGL N) = frickeScalar N k • (f ∣[k] (A * (frickeGL N)⁻¹)) := by
  rw [show A * frickeGL N = (A * (frickeGL N)⁻¹) * (frickeGL N * frickeGL N) by group,
    SlashAction.slash_mul, frickeGL_sq_slash]

/-- **`W ∘ W = c • id`** for the explicit scalar `c = frickeScalar N k = N^{2(k-1)}·(-N)^{-k}`. -/
theorem frickeOperator_frickeOperator (k : ℤ) :
    (frickeOperator (N := N) k).comp (frickeOperator (N := N) k) =
      frickeScalar N k • LinearMap.id := by
  ext f z
  show (⇑(frickeOperator k f) ∣[k] (frickeGL N : GL (Fin 2) ℚ)) z = _
  rw [frickeOperator_coe, ← SlashAction.slash_mul, frickeGL_sq_slash]
  rfl

/-- The **inverse-conjugate character** `χ' = χ ∘ (·)⁻¹`.  The Fricke operator sends
`modFormCharSpace k χ` into `modFormCharSpace k (chiConj χ)`. -/
noncomputable def chiConj (χ : (ZMod N)ˣ →* ℂˣ) : (ZMod N)ˣ →* ℂˣ :=
  χ.comp invMonoidHom

omit [NeZero N] in
@[simp] lemma chiConj_apply (χ : (ZMod N)ˣ →* ℂˣ) (d : (ZMod N)ˣ) :
    chiConj χ d = χ d⁻¹ := rfl

/-- The Fricke operator carries the `χ`-Nebentypus space into the `χ⁻¹`-Nebentypus space:
`⟨d⟩ (W f) = χ(d⁻¹) • (W f)`. -/
theorem frickeOperator_mem_charSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    frickeOperator k f ∈ modFormCharSpace k (chiConj χ) := by
  rw [mem_modFormCharSpace_iff]
  intro d
  have hd : diamondOp k d⁻¹ f = (↑(χ d⁻¹) : ℂ) • f := (mem_modFormCharSpace_iff k χ f).mp hf d⁻¹
  have h := LinearMap.congr_fun (frickeOperator_diamondOp (N := N) k d⁻¹) f
  simpa only [diamondOpHom_apply, LinearMap.comp_apply, inv_inv, hd, map_smul, chiConj_apply]
    using h.symm

/-- The Fricke operator restricted to `modFormCharSpace k χ`, landing in
`modFormCharSpace k (chiConj χ)`. -/
noncomputable def frickeCharRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k (chiConj χ) where
  toFun f := ⟨frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
    frickeOperator_mem_charSpace k χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (frickeOperator k) _ _)
  map_smul' c _ := Subtype.ext (map_smul (frickeOperator k) c _)

@[simp] lemma frickeCharRestrict_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((frickeCharRestrict k χ f : modFormCharSpace k (chiConj χ)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- **The Fricke isomorphism** `modFormCharSpace k χ ≃ₗ[ℂ] modFormCharSpace k (chiConj χ)`.
Its forward map is `frickeCharRestrict`; the inverse is `c⁻¹ •` the other Fricke restriction
(using `W² = c • id` and `chiConj (chiConj χ) = χ`). -/
noncomputable def frickeCharEquiv (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ ≃ₗ[ℂ] modFormCharSpace k (chiConj χ) where
  toLinearMap := frickeCharRestrict k χ
  invFun := (frickeScalar N k)⁻¹ • frickeCharRestrict k (chiConj χ)
  left_inv f := by
    have hc := frickeScalar_ne_zero (N := N) k
    have hsq : frickeOperator k (frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
        frickeScalar N k • (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
      LinearMap.congr_fun (frickeOperator_frickeOperator (N := N) k) _
    apply Subtype.ext
    rw [LinearMap.smul_apply, SetLike.val_smul]
    show (frickeScalar N k)⁻¹ • frickeOperator k (frickeOperator k
        (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = (f : ModularForm _ k)
    rw [hsq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv f := by
    have hc := frickeScalar_ne_zero (N := N) k
    have hsq : frickeOperator k (frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
        frickeScalar N k • (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
      LinearMap.congr_fun (frickeOperator_frickeOperator (N := N) k) _
    apply Subtype.ext
    rw [LinearMap.smul_apply]
    show frickeOperator k ((frickeScalar N k)⁻¹ • frickeOperator k
        (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = (f : ModularForm _ k)
    rw [map_smul, hsq, smul_smul, inv_mul_cancel₀ hc, one_smul]

end HeckeRing.GL2
