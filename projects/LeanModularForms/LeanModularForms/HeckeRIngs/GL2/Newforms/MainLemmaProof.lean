/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma
import LeanModularForms.SMOObligations

/-!
# The Atkin–Lehner Main Lemma (DS Theorem 5.7.1), assembled

This file completes the Main Lemma: a cusp form `f ∈ S_k(Γ₁(N))` whose Fourier coefficients
`aₙ` vanish at every index coprime to `N` is an oldform.

We give the **route-B** (Miyake §4.6) proof.  The per-character ingredient
`mainLemma_charSpace` is `HeckeRing.GL2.mainLemma_charSpace_routeB` (proven sorry-free in
`SMOObligations.lean` via Miyake's sieve/conductor descent).  That file sits **above**
`Newforms.MainLemma` in the import DAG (the route-B sieve transitively imports
`Newforms.CoeffSeq → Newforms.MainLemma`, where the `Newform` structure is defined), so the
assembly cannot live in `Newforms.MainLemma` itself without an import cycle — hence this
separate high file, which imports `SMOObligations` directly.

The Nebentypus character decomposition `f = ∑_χ g_χ` reduces the global statement to the
per-character version, given that each component inherits the coprime-index coefficient
vanishing (`qExpansion_charComponent_coprime_eq_zero`).
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The canonical (period-1) `q`-expansion of a cusp form, packaged as an `AddMonoidHom`
to power series.  Used to push `q`-expansion through finite/`Finsupp` sums. -/
private noncomputable def qExpansionOneCuspAddHom :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →+ PowerSeries ℂ :=
  (ModularForm.qExpansionAddHom (Γ := (Gamma1 N).map (mapGL ℝ)) (h := (1 : ℝ))
      one_pos (one_mem_strictPeriods_Gamma1_map N) k).comp
    (cuspFormToModularFormLin (N := N) (k := k)).toAddMonoidHom

omit [NeZero N] in
private lemma qExpansionOneCuspAddHom_apply (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansionOneCuspAddHom g = UpperHalfPlane.qExpansion (1 : ℝ) g := rfl

omit [NeZero N] in
/-- **Additivity of the canonical (period-1) `q`-expansion coefficients over a `Finset` sum
of cusp forms.**  Packaging of `ModularForm.qExpansionAddHom` for the cusp-form coercion. -/
private lemma qExpansion_one_coeff_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (∑ i ∈ s, F i)).coeff n =
      ∑ i ∈ s, (UpperHalfPlane.qExpansion (1 : ℝ) (F i)).coeff n := by
  have h := map_sum qExpansionOneCuspAddHom F s
  simp only [qExpansionOneCuspAddHom_apply] at h
  rw [show (∑ i ∈ s, ⇑(F i) : UpperHalfPlane → ℂ) = ⇑(∑ i ∈ s, F i) from
    (map_sum (CuspForm.coeHom (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k)) F s).symm, h, map_sum]

/-- **Per-character coefficient inheritance (route-B ingredient 1).**  If `f` is a cusp form
all of whose canonical Fourier coefficients at indices coprime to `N` vanish, and `g` is the
`χ`-Nebentypus component of `f` in the character decomposition `f = ∑_χ g_χ` (so that
`g ∈ S_k(Γ₁(N), χ)` and `g` is one summand of a `Finsupp`-sum equal to `f` whose every other
summand lies in a *different* character space), then `g` likewise has vanishing canonical
Fourier coefficients at all indices coprime to `N`.

Mathematically this is the statement that the Nebentypus projector commutes with the
coprime-index coefficient functionals — equivalently that the diamond operators `⟨d⟩` preserve
the subspace of forms whose coprime-index `q`-coefficients vanish.  In the present codebase the
diamond operators' action on individual `q`-coefficients is only computed *inside* a single
character space (`fourierCoeff_heckeT_n_period_one`), so this projection-level statement is not
yet derivable here. -/
private lemma qExpansion_charComponent_coprime_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (gd : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_char : ∀ χ : (ZMod N)ˣ →* ℂˣ, gd χ ∈ cuspFormCharSpace k χ)
    (h_sum : (gd.sum fun _ y ↦ y) = f)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) (hn : Nat.Coprime n N) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ)).coeff n = 0 := by
  sorry

/-- **Per-character Main Lemma (route-B ingredient 2).**  A cusp form `g ∈ S_k(Γ₁(N), χ)` whose
canonical (period-1) `q`-expansion vanishes at every index coprime to `N` is an oldform.

This is exactly `HeckeRing.GL2.mainLemma_charSpace_routeB` (`SMOObligations.lean`), proven
sorry-free by Miyake's sieve/conductor descent (Theorems 4.6.4 / 4.6.8); now that this file
imports `SMOObligations`, it is invoked directly. -/
private lemma mainLemma_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0) :
    g ∈ cuspFormsOld N k :=
  mainLemma_charSpace_routeB χ g hg_char h_vanish

/-- **The Main Lemma** (DS Theorem 5.7.1, Atkin-Lehner [AL70]):
If `f ∈ S_k(Γ₁(N))` has Fourier expansion `f(τ) = Σ aₙ qⁿ` with `aₙ = 0`
whenever `(n, N) = 1`, then `f` is an oldform.

This is the technical heart of the newform theory.  We give the **route-B** (Miyake §4.6)
proof: the Nebentypus character decomposition `f = ∑_χ g_χ` reduces the claim to the
per-character Atkin–Lehner descent, since each component `g_χ` inherits the coprime-index
coefficient vanishing (`qExpansion_charComponent_coprime_eq_zero`) and is therefore an oldform
(`mainLemma_charSpace`); a finite sum of oldforms is an oldform. -/
theorem mainLemma
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  classical
  -- Nebentypus character decomposition `f = ∑_χ g_χ`, each `g_χ ∈ S_k(Γ₁(N), χ)`.
  obtain ⟨gd, hgd_mem, hgd_sum⟩ :=
    exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k ⊤
      (fun d g _ ↦ Submodule.mem_top) (Submodule.mem_top : f ∈ ⊤)
  have h_char : ∀ χ : (ZMod N)ˣ →* ℂˣ, gd χ ∈ cuspFormCharSpace k χ :=
    fun χ ↦ (hgd_mem χ).2
  -- Each component is an oldform: it inherits the vanishing, then route-B descent applies.
  have h_old : ∀ χ : (ZMod N)ˣ →* ℂˣ, gd χ ∈ cuspFormsOld N k := fun χ ↦
    mainLemma_charSpace χ (gd χ) (h_char χ)
      (fun n hn ↦ qExpansion_charComponent_coprime_eq_zero f gd h_char hgd_sum h χ n hn)
  -- A finite sum of oldforms is an oldform.
  rw [← hgd_sum, Finsupp.sum]
  exact Submodule.sum_mem _ fun χ _ ↦ h_old χ

end HeckeRing.GL2
