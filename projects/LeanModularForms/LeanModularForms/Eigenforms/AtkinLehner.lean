/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.Eigenforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Atkin-Lehner same-level `p`-supported projection API

This file develops the Atkin-Lehner projection API for `Newforms.mainLemma`: any cusp
form `f ∈ S_k(Γ₁(N))` whose Fourier coefficients vanish at every index coprime to `N`
is an oldform.  The framework captures "support on multiples of `d`":

* `IsSupportedOnDvd d P` — the power-series support predicate, with its algebraic
  closure lemmas.
* `QExpansionSupportedOnDvd d f` and `qSupportedOnDvdSubmodule N k d` — the same
  condition on the canonical period-1 `q`-expansion of a cusp form, packaged as a
  submodule.
* `qExpansion_levelRaise_isSupportedOnDvd` / `levelRaise_mem_qSupportedOnDvdSubmodule` —
  the forward direction: level-raise images are supported on multiples of `d`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.7.
* Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970).
* Miyake, *Modular Forms*, §4.6.
-/

open scoped ModularForm
open ModularFormClass CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane

namespace HeckeRing.GL2.AtkinLehner

/-- A power series is **supported on multiples of `d`** if its
coefficient at every index not divisible by `d` is zero. -/
def IsSupportedOnDvd (d : ℕ) (P : PowerSeries ℂ) : Prop :=
  ∀ n : ℕ, ¬ d ∣ n → (PowerSeries.coeff n) P = 0

namespace IsSupportedOnDvd

@[simp] lemma zero (d : ℕ) : IsSupportedOnDvd d (0 : PowerSeries ℂ) := fun _ _ ↦ by simp

lemma add {d : ℕ} {P Q : PowerSeries ℂ}
    (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P + Q) := fun n hn ↦ by
  rw [map_add, hP n hn, hQ n hn, zero_add]

lemma smul {d : ℕ} (c : ℂ) {P : PowerSeries ℂ} (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (c • P) := fun n hn ↦ by simp [smul_eq_mul, hP n hn]

lemma neg {d : ℕ} {P : PowerSeries ℂ} (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (-P) := fun n hn ↦ by rw [map_neg, hP n hn, neg_zero]

lemma sub {d : ℕ} {P Q : PowerSeries ℂ}
    (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P - Q) := sub_eq_add_neg P Q ▸ hP.add hQ.neg

/-- The constant power series `1 : PowerSeries ℂ` is supported on multiples of any `d`. -/
lemma one (d : ℕ) : IsSupportedOnDvd d (1 : PowerSeries ℂ) := fun n hn ↦ by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (dvd_zero d) hn
  · rw [PowerSeries.coeff_one, if_neg hpos.ne']

end IsSupportedOnDvd

variable {N : ℕ} [NeZero N] {k : ℤ} {d : ℕ}

/-- A cusp form `f ∈ S_k(Γ₁(N))` is **q-supported on multiples of `d`**
if its canonical period-1 `q`-expansion is supported on multiples of
`d`. -/
def QExpansionSupportedOnDvd (d : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IsSupportedOnDvd d (qExpansion (1 : ℝ) f)


/-- The submodule of cusp forms `f ∈ S_k(Γ₁(N))` whose canonical
period-1 `q`-expansion is supported on multiples of `d`. -/
noncomputable def qSupportedOnDvdSubmodule (N : ℕ) [NeZero N] (k : ℤ) (d : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | QExpansionSupportedOnDvd d f}
  zero_mem' n _ := by simp [qExpansion_zero]
  add_mem' {f g} hf hg n hn := by
    have h_eq : qExpansion (1 : ℝ) (⇑(f + g) : UpperHalfPlane → ℂ) =
        qExpansion (1 : ℝ) ⇑f + qExpansion (1 : ℝ) ⇑g := by
      convert ModularForm.qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ))
        (h := 1) (a := k) (b := k)
        one_pos (one_mem_strictPeriods_Gamma1_map N) f g using 2 <;>
        exact CuspForm.coe_add f g
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(f + g)) = 0
    rw [h_eq, map_add, hf n hn, hg n hn, zero_add]
  smul_mem' c f hf n hn := by
    have h_eq : qExpansion (1 : ℝ) (⇑(c • f) : UpperHalfPlane → ℂ) =
        c • qExpansion (1 : ℝ) ⇑f := by
      convert ModularForm.qExpansion_smul (Γ := (Gamma1 N).map (mapGL ℝ))
        (k := k) (h := 1) one_pos
        (one_mem_strictPeriods_Gamma1_map N) c f using 2 <;>
        rfl
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(c • f)) = 0
    rw [h_eq, show (PowerSeries.coeff n) (c • qExpansion (1 : ℝ) ⇑f) =
      c * (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑f) by simp [smul_eq_mul],
      hf n hn, mul_zero]


/-- Level-raise q-expansion forward direction (modular form): for
`g : ModularForm Γ₁(M) k`, the image `modularFormLevelRaise M d k g`
has period-1 `q`-expansion supported on multiples of `d`. -/
lemma qExpansion_modularFormLevelRaise_isSupportedOnDvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d (qExpansion (1 : ℝ) (modularFormLevelRaise M d k g)) :=
  fun n hn ↦ by rw [qExpansion_one_modularFormLevelRaise_coeff g n, if_neg hn]

/-- Level-raise q-expansion forward direction (cusp form): for any cusp form
`g : CuspForm Γ₁(M) k`, the level-raise `levelRaise M d k g` has period-1
`q`-expansion supported on multiples of `d`. -/
lemma qExpansion_levelRaise_isSupportedOnDvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] {k : ℤ}
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d (qExpansion (1 : ℝ) (levelRaise M d k g)) := fun n hn ↦ by
  let g_mf : ModularForm ((Gamma1 M).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := g.toSlashInvariantForm
      holo' := g.holo'
      bdd_at_cusps' := fun {c} hc γ hγ ↦ (g.zero_at_cusps' hc γ hγ).isBoundedAtImInfty }
  rw [show (qExpansion (1 : ℝ) (levelRaise M d k g)) =
      qExpansion (1 : ℝ) (modularFormLevelRaise M d k g_mf) from
    qExpansion_ext2 _ _ (by rw [coe_modularFormLevelRaise]; rfl)]
  exact qExpansion_modularFormLevelRaise_isSupportedOnDvd _ n hn

/-- Forward Atkin–Lehner correspondence (submodule form): any cusp form obtained by
level-raising lies in the `qSupportedOnDvdSubmodule`. -/
theorem levelRaise_mem_qSupportedOnDvdSubmodule
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d]
    (heq : d * M = N) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (heq ▸ levelRaise M d k g) ∈ qSupportedOnDvdSubmodule N k d := by
  subst heq
  show QExpansionSupportedOnDvd d (levelRaise M d k g)
  exact qExpansion_levelRaise_isSupportedOnDvd g

private lemma cuspForm_coe_eq_of_cast {M N : ℕ} {k : ℤ} (h : M = N)
    (x : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(h ▸ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) =
      ⇑x := by
  cases h; rfl

private lemma isOldformGenerator_of_funeq
    {N d : ℕ} [NeZero d] (hd : 1 < d) (hdN : d ∣ N) [NeZero N] [NeZero (N / d)]
    {k : ℤ}
    (F : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_funeq : (⇑(levelRaise (N / d) d k F) : UpperHalfPlane → ℂ) = ⇑f) :
    IsOldformGenerator f := by
  have h_dvd_eq : d * (N / d) = N := Nat.mul_div_cancel' hdN
  refine ⟨N / d, d, ⟨NeZero.ne (N / d)⟩, ‹_›, hd, h_dvd_eq, F, ?_⟩
  apply DFunLike.coe_injective
  show (⇑(h_dvd_eq ▸ levelRaise (N / d) d k F :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) = ⇑f
  rwa [cuspForm_coe_eq_of_cast h_dvd_eq]

/-- Reverse Atkin-Lehner bridge (with Nebentypus character): a cusp form
`f ∈ S_k(Γ₁(N), χ)` whose period-1 `q`-expansion is supported on multiples of a
proper divisor `d` of `N` (`1 < d`, `d ∣ N`) is an oldform, `f ∈ cuspFormsOld N k`. -/
theorem qSupportedOnDvd_mem_cuspFormsOld_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (hfsupp : f ∈ qSupportedOnDvdSubmodule N k d) :
    f ∈ cuspFormsOld N k := by
  obtain ⟨φ, h_eq, h_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hd hdN f (fun n hn ↦ hfsupp n hn)
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      d N hdN k χ φ f hfχ h_eq h_period with
    ⟨_h_fac, F, _hF_char, hF_eq⟩ | h_zero
  · refine Submodule.subset_span (isOldformGenerator_of_funeq hd hdN F f ?_)
    show levelRaiseFun d k ⇑F = ⇑f
    rw [hF_eq, ← h_eq]
  · refine (?_ : f = 0) ▸ Submodule.zero_mem _
    apply DFunLike.coe_injective
    show (⇑f : UpperHalfPlane → ℂ) = 0
    rw [h_eq, h_zero]; simp [levelRaiseFun]

/-- Submodule-level forward bridge: the `heq`-cast of every level-raise image lies in
`qSupportedOnDvdSubmodule N k d`. -/
theorem cast_levelRaise_mem_qSupportedOnDvdSubmodule
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hdN : d ∣ N) {k : ℤ}
    (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k) :
    ((Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      qSupportedOnDvdSubmodule N k d :=
  levelRaise_mem_qSupportedOnDvdSubmodule (Nat.mul_div_cancel' hdN) g

/-- For `h : M = N` a type-level equality of levels, the identity cast `(h ▸ ·)` is a
`ℂ`-linear equivalence between the two CuspForm spaces. -/
def castCuspFormLinearEquiv {M N : ℕ} (h : M = N) (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k ≃ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun x := (h ▸ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  invFun x := (h.symm ▸ x : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
  map_add' x y := by subst h; rfl
  map_smul' c x := by subst h; rfl
  left_inv x := by subst h; rfl
  right_inv x := by subst h; rfl

/-- The Atkin-Lehner level-raise operator packaged at the same-level target `Γ₁(N)`:
the composition of `levelRaise (N/d) d k` with `castCuspFormLinearEquiv`. -/
noncomputable def castLevelRaise (N : ℕ) [NeZero N] (d : ℕ) [NeZero d]
    [NeZero (N / d)] (hdN : d ∣ N) (k : ℤ) :
    CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (castCuspFormLinearEquiv (Nat.mul_div_cancel' hdN) k).toLinearMap.comp
    (levelRaise (N / d) d k)

@[simp] lemma castLevelRaise_apply {N : ℕ} [NeZero N] {d : ℕ} [NeZero d]
    [NeZero (N / d)] (hdN : d ∣ N) (k : ℤ)
    (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k) :
    castLevelRaise N d hdN k g =
      ((Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- Every image of `castLevelRaise` at level `Γ₁(N)` lies in
`qSupportedOnDvdSubmodule N k d`. -/
theorem range_castLevelRaise_le_qSupportedOnDvdSubmodule
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] [NeZero (N / d)]
    (hdN : d ∣ N) (k : ℤ) :
    LinearMap.range (castLevelRaise N d hdN k) ≤
      qSupportedOnDvdSubmodule N k d := by
  rintro _ ⟨g, rfl⟩
  rw [castLevelRaise_apply]
  exact cast_levelRaise_mem_qSupportedOnDvdSubmodule hdN g

/-- **Higher-level `p`-supported projection.**  The composition
`V_p ∘ U_p` at modular-form level, mapping
`ModularForm Γ₁(N) k →ₗ[ℂ] ModularForm Γ₁(p · N) k`. -/
noncomputable def pSupportedRaise {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
  (HeckeRing.GL2.modularFormLevelRaise N p k).comp
    (HeckeRing.GL2.heckeT_p_divN k p hp hpN)

/-- `q`-expansion formula for `pSupportedRaise`: at period 1,
`a_n(pSupportedRaise f) = a_n(f)` if `p ∣ n`, else `0`. -/
theorem qExpansion_one_pSupportedRaise_coeff {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ) (pSupportedRaise k p hp hpN f)).coeff n =
      if p ∣ n then (qExpansion (1 : ℝ) f).coeff n else 0 := by
  show (qExpansion (1 : ℝ) (HeckeRing.GL2.modularFormLevelRaise N p k
    (HeckeRing.GL2.heckeT_p_divN k p hp hpN f))).coeff n = _
  rw [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff]
  split_ifs with h
  · rw [HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff hp hpN f (n / p),
      Nat.mul_div_cancel' h]
  · rfl

/-- **Same-level divisor decomposition consumer** (`mainLemma_charSpace`, the headline
output of this file): given a Dirichlet character `χ` mod `N`, a cusp form
`f : CuspForm Γ₁(N) k`, and a same-level divisor decomposition
`f = ∑ d ∈ N.divisors.filter (1 < ·), samePiece d` whose pieces simultaneously lie in
`qSupportedOnDvdSubmodule N k d` and `cuspFormCharSpace k χ.toUnitHom`, conclude
`f ∈ cuspFormsOld N k`.  Each piece is handled by
`qSupportedOnDvd_mem_cuspFormsOld_of_char`, and the conclusion follows by `sum_mem`. -/
theorem mainLemma_charSpace_of_sameLevelDivisorDecomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (samePiece : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sum : f = ∑ d ∈ N.divisors.filter (1 < ·), samePiece d)
    (h_pieces : ∀ d ∈ N.divisors.filter (1 < ·),
      samePiece d ∈ qSupportedOnDvdSubmodule N k d ∧
      samePiece d ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k := by
  rw [h_sum]
  refine Submodule.sum_mem _ fun d hd ↦ ?_
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdN, _⟩, hd_gt⟩ := hd
  have hd_pos : 0 < d := by omega
  haveI : NeZero d := ⟨hd_pos.ne'⟩
  haveI : NeZero (N / d) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hdN) hd_pos).ne'⟩
  have hd_mem : d ∈ N.divisors.filter (1 < ·) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdN, NeZero.ne N⟩, hd_gt⟩
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hd_gt hdN χ
    (samePiece d) (h_pieces d hd_mem).2 (h_pieces d hd_mem).1

end HeckeRing.GL2.AtkinLehner
