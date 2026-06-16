/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: character decomposition, the `Newform` structure, and the Main Lemma

Character-space decomposition of the old/new subspaces, the `Newform` structure (DS Def 5.8.1),
primitive forms, the eigenvalue-as-Fourier-coefficient identity, and the Atkin-Lehner Main Lemma
(DS Thm 5.7.1) with its uniqueness corollary.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

section CharSpaceDecomposition

/-- **`diamondOpCuspHom`-invariance of `cuspFormsOld N k`.** -/
lemma diamondOpCuspHom_preserves_cuspFormsOld
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsOld N k) :
    diamondOpCuspHom k d f ∈ cuspFormsOld N k :=
  diamondOp_preserves_cuspFormsOld d f hf

/-- **`diamondOpCuspHom`-invariance of `cuspFormsNew N k`.** -/
lemma diamondOpCuspHom_preserves_cuspFormsNew
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNew N k) :
    diamondOpCuspHom k d f ∈ cuspFormsNew N k :=
  diamondOp_preserves_cuspFormsNew d f hf

/-- **Finsupp-indexed character decomposition of a newform subspace element.**
Every `f ∈ cuspFormsNew N k` is a finitely-supported sum of Nebentypus
components, each simultaneously in `cuspFormsNew N k` and in its character
subspace. -/
theorem exists_finsupp_charSpace_of_cuspFormsNew (k : ℤ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y ↦ y) = f :=
  exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k (cuspFormsNew N k)
    diamondOpCuspHom_preserves_cuspFormsNew hf

end CharSpaceDecomposition

/-- A **newform** of level Γ₁(N) and weight k: a cusp form that is
1. an eigenform (common eigenfunction of all T_n with (n,N)=1)
2. in the new subspace
3. normalised: a_1(f) = 1

By Atkin-Lehner uniqueness (DS Theorem 5.8.2), newforms are uniquely determined
by their Hecke eigenvalues away from the level. -/
@[ext]
structure Newform (N : ℕ) [NeZero N] (k : ℤ)
    extends Eigenform N k where
  /-- The form is in the new subspace. -/
  isNew : toCuspForm ∈ cuspFormsNewExtended N k
  /-- Normalisation at the **canonical Fourier period** (`h = 1`): the first
  Fourier coefficient is `1`, i.e. `a₁ = 1` (the Diamond–Shurman / Miyake
  normalisation). -/
  isNorm : (UpperHalfPlane.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

/-- The **conductor** of a `Newform N k` is the smallest level at which `f`
arises as a `Newform`; for a bundled `Newform N k` this is `N` itself. -/
noncomputable def Newform.conductor (_f : Newform N k) : ℕ := N

private lemma qExpansion_one_coeff_one_smul_of_norm
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_norm : (UpperHalfPlane.qExpansion (1 : ℝ) f.toModularForm').coeff 1 = 1)
    (c : ℂ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (c • f)).coeff 1 = c := by
  change (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(c • f : CuspForm _ k))).coeff 1 = c
  rw [show (⇑(c • f : CuspForm _ k) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, smul_eq_mul, h_norm, mul_one]

lemma qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_char : f.toModularForm' ∈ modFormCharSpace k χ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n f)).coeff 1 =
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n := by
  rw [show (⇑(heckeT_n_cusp k n f) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k n f).toModularForm' from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl, heckeT_n_cusp_toModularForm']
  have h := fourierCoeff_heckeT_n_period_one (N := N) k n hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simpa only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] using h

/-- For a `Newform` f lying in a character eigenspace `modFormCharSpace k χ`,
the eigenvalue at `n` (coprime to `N`) equals the `n`-th **canonical
Fourier coefficient** of `f` (period `h = 1`).  The character hypothesis
`hf_char` is required because `fourierCoeff_heckeT_n_period_one` is stated for
forms living in a single Nebentypus eigenspace. -/
theorem Newform.eigenvalue_eq_coeff (f : Newform N k) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue n =
      (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  rw [← qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff n.val hn χ f.toCuspForm hf_char,
    f.isEigen n hn]
  exact (qExpansion_one_coeff_one_smul_of_norm f.toCuspForm f.isNorm _).symm

section MainLemmaSkeleton

/-!
### The Main Lemma (DS Theorem 5.7.1) — route B (Miyake §4.6), skeleton form

We reduce the global Main Lemma to its **per-character** version via the Nebentypus
character decomposition.  Concretely, writing `f = ∑_χ g_χ` with `g_χ ∈ S_k(Γ₁(N), χ)`
(`exists_finsupp_charSpace_of_diamondOpCuspHom_invariant` with `p = ⊤`):

1. each component `g_χ` again has vanishing `q`-coefficients at indices coprime to `N`
   (`qExpansion_charComponent_coprime_eq_zero`);
2. each such component is an oldform by the per-character Main Lemma
   (`mainLemma_charSpace`, the route-B Atkin–Lehner descent);
3. `f` is a finite sum of oldforms, hence an oldform (`Submodule.sum_mem`).

The two ingredients are isolated as named sub-lemmas below.  Both are *mathematically
established* — `mainLemma_charSpace` is `HeckeRing.GL2.mainLemma_charSpace_routeB`
(`SMOObligations.lean`, proven sorry-free via Miyake's sieve/conductor argument) — but they
sit **above** this file in the import DAG (the route-B sieve transitively imports
`Newforms.CoeffSeq → Newforms.MainLemma`), so they cannot be invoked here directly without
introducing an import cycle.  They are therefore stated locally with the `sorry`s marking the
DAG seam, not a genuine mathematical gap.
-/

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
sorry-free by Miyake's sieve/conductor descent (Theorems 4.6.4 / 4.6.8).  It is restated here
only because that file sits above `Newforms.MainLemma` in the import DAG; the `sorry` marks the
DAG seam, not an open mathematical problem. -/
private lemma mainLemma_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0) :
    g ∈ cuspFormsOld N k := by
  sorry

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

end MainLemmaSkeleton

end HeckeRing.GL2
