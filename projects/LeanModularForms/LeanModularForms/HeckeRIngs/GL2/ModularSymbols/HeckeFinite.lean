/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Labels.HeckeFieldArithmetic
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.HeckeSymbol
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.ModuleMFinite

/-!
# The faithfulness endgame: `heckeAlgℤ` is module-finite, from a period map (ES-asm)

This file proves — **conditionally on the abstract period-map interface** — that the integral Hecke
algebra `HeckeRing.GL2.heckeAlgℤ N k` is a finite `ℤ`-module.  This is the *logic* of the
Eichler–Shimura faithfulness endgame, isolated from all analysis: the actual period map (with its
injectivity and Hecke/diamond equivariance) is supplied separately and consumed here purely as
hypotheses.

## The interface

Write `S_k := CuspForm ((Γ₁ N).map (mapGL ℝ)) k` for the cusp-form space, and `𝕄 := 𝕄 N k` for the
integral modular-symbol module (finite over `ℤ`).  We take a **period map**
`ι : S_k →ₗ[ℂ] (𝕄 →ₗ[ℤ] ℂ)` — equivalently a `ℂ`-linear map into `Hom_ℤ(𝕄, ℂ)` — together with:

* `hι : Function.Injective ι` (Eichler–Shimura: periods separate cusp forms);
* `hT : ∀ n f, ι (heckeEnd N k n f) = (heckeSymb N k n.val).dualPrecomp (ι f)` (Hecke equivariance);
* `hD : ∀ d f, ι (diamondOpCusp k d f) = (diamondSymb N k d).dualPrecomp (ι f)` (diamond
  equivariance);
* `hComm : Pairwise (Commute on genM N k)` — the integral modular-symbol Hecke algebra is
  commutative (the standard Hecke-commutativity input, on the symbol side where it is consumed);

where `T.dualPrecomp φ = φ ∘ₗ T` is the transpose of `T : 𝕄 →ₗ[ℤ] 𝕄`.

## The argument (free-algebra kernel-inclusion)

Indexing the generators by `Idx := ℕ+ ⊕ (ZMod N)ˣ`, we form two evaluation `ℤ`-algebra
homomorphisms out of the **free** `ℤ`-algebra `FreeAlgebra ℤ (Idx N)` (free, so its universal
property `FreeAlgebra.lift` applies even to the noncommutative endomorphism rings): `evalS` into
`End_ℂ(S_k)` (whose range is `heckeAlgℤ`) and `evalM` into `End_ℤ(𝕄)`.  Since `𝕄` is `ℤ`-finite and
`ℤ` is Noetherian, `End_ℤ(𝕄)` is `ℤ`-finite, hence so is `range evalM`.  The commutativity `hComm`
makes the image `range evalM` commutative, which (together with the generator equivariance
`hT`/`hD`)
lets the equivariance identity `ι ((evalS p) f) = (evalM p).dualPrecomp (ι f)` extend by
`FreeAlgebra.induction` to all `p` — the multiplicative step needs precisely that the two factors'
images commute, since `dualPrecomp` is an anti-homomorphism.  Injectivity of `ι` then gives
`ker evalM ≤ ker evalS`, a surjection `FreeAlgebra ⧸ ker evalM ↠ FreeAlgebra ⧸ ker evalS` transports
finiteness, and the first isomorphism theorem identifies the target with
`range evalS = heckeAlgℤ`.

## Main result

* `HeckeRing.GL2.ModularSymbols.heckeAlgℤ_finite_of_period` :
  `Module.Finite ℤ (heckeAlgℤ N k)`, given the period-map interface above.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups
open HeckeRing.GL2 CongruenceSubgroup Matrix.SpecialLinearGroup

universe u

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## `dualPrecomp` — the transpose `φ ↦ φ ∘ₗ T` -/

/-- The transpose / precomposition map: for a `ℤ`-linear endomorphism `T` of `𝕄 N k`, send a
functional `φ : 𝕄 N k →ₗ[ℤ] ℂ` to `φ ∘ₗ T`.  This is `ℤ`-linear in `φ`. -/
noncomputable def dualPrecomp (T : 𝕄 N k →ₗ[ℤ] 𝕄 N k) :
    (𝕄 N k →ₗ[ℤ] ℂ) →ₗ[ℤ] (𝕄 N k →ₗ[ℤ] ℂ) :=
  LinearMap.lcomp ℤ ℂ T

@[simp]
theorem dualPrecomp_apply (T : 𝕄 N k →ₗ[ℤ] 𝕄 N k) (φ : 𝕄 N k →ₗ[ℤ] ℂ) (x : 𝕄 N k) :
    dualPrecomp T φ x = φ (T x) :=
  rfl

/-- `dualPrecomp` is an *anti*-homomorphism for composition: `(A ∘ₗ B).dualPrecomp` precomposes by
`A ∘ B`, which equals precomposing by `B` then by `A`. -/
theorem dualPrecomp_comp (A B : 𝕄 N k →ₗ[ℤ] 𝕄 N k) :
    dualPrecomp (A ∘ₗ B) = dualPrecomp B ∘ₗ dualPrecomp A := by
  ext φ x
  simp

/-- `dualPrecomp` of a product (in `Module.End`) is the product in the opposite order. -/
theorem dualPrecomp_mul (A B : Module.End ℤ (𝕄 N k)) :
    dualPrecomp (A * B) = dualPrecomp B * dualPrecomp A :=
  dualPrecomp_comp A B

@[simp]
theorem dualPrecomp_one : dualPrecomp (1 : Module.End ℤ (𝕄 N k)) = 1 := by
  ext φ x
  simp

@[simp]
theorem dualPrecomp_zero : dualPrecomp (0 : 𝕄 N k →ₗ[ℤ] 𝕄 N k) = 0 := by
  ext φ x
  simp

theorem dualPrecomp_add (A B : 𝕄 N k →ₗ[ℤ] 𝕄 N k) :
    dualPrecomp (A + B) = dualPrecomp A + dualPrecomp B := by
  ext φ x
  simp

theorem dualPrecomp_zsmul (c : ℤ) (T : 𝕄 N k →ₗ[ℤ] 𝕄 N k) :
    dualPrecomp (c • T) = c • dualPrecomp T := by
  ext φ x
  simp

/-- `dualPrecomp` sends commuting operators to commuting transposes (in the opposite order, but
`Commute` is symmetric). -/
theorem dualPrecomp_commute {A B : Module.End ℤ (𝕄 N k)} (h : Commute A B) :
    Commute (dualPrecomp A) (dualPrecomp B) := by
  show dualPrecomp A * dualPrecomp B = dualPrecomp B * dualPrecomp A
  rw [← dualPrecomp_mul, ← dualPrecomp_mul, h.eq]

/-! ## Finiteness of `End_ℤ(𝕄 N k)` -/

/-- `End_ℤ(𝕄 N k)` is a finite `ℤ`-module: `𝕄 N k` is `ℤ`-finite and `ℤ` is Noetherian, so the
module of `ℤ`-linear endomorphisms is Noetherian, hence finite. -/
instance instModuleFiniteEndModularSymbols (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Finite ℤ (Module.End ℤ (𝕄 N k)) := by
  haveI : IsNoetherian ℤ (𝕄 N k →ₗ[ℤ] 𝕄 N k) := isNoetherian_linearMap ℤ (𝕄 N k) (𝕄 N k)
  exact Module.IsNoetherian.finite ℤ (Module.End ℤ (𝕄 N k))

/-! ## The two evaluation algebra homomorphisms -/

/-- The generator index set: positive integers `n` (Hecke operators `T_n`/`U_p`) together with
units `d` (diamond operators `⟨d⟩`). -/
abbrev Idx (N : ℕ) : Type := ℕ+ ⊕ (ZMod N)ˣ

/-- The generator family on the cusp-form side: `T_n` on the left summand, `⟨d⟩` on the right. -/
noncomputable def genS (N : ℕ) [NeZero N] (k : ℤ) :
    Idx N → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Sum.elim (fun n => heckeEnd N k n) (fun d => diamondOpCusp k d)

/-- The generator family on the modular-symbol side: `heckeSymb N k n` on the left, `diamondSymb`
on the right. -/
noncomputable def genM (N : ℕ) [NeZero N] (k : ℤ) :
    Idx N → Module.End ℤ (𝕄 N k) :=
  Sum.elim (fun n => heckeSymb N k n.val) (fun d => diamondSymb N k d)

/-- Evaluation `ℤ`-algebra hom into `End_ℂ(S_k)`, from the free `ℤ`-algebra on the generators. -/
noncomputable def evalS (N : ℕ) [NeZero N] (k : ℤ) :
    FreeAlgebra ℤ (Idx N) →ₐ[ℤ] Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  FreeAlgebra.lift ℤ (genS N k)

/-- Evaluation `ℤ`-algebra hom into `End_ℤ(𝕄)`, from the free `ℤ`-algebra on the generators. -/
noncomputable def evalM (N : ℕ) [NeZero N] (k : ℤ) :
    FreeAlgebra ℤ (Idx N) →ₐ[ℤ] Module.End ℤ (𝕄 N k) :=
  FreeAlgebra.lift ℤ (genM N k)

@[simp]
theorem evalS_ι (i : Idx N) : evalS N k (FreeAlgebra.ι ℤ i) = genS N k i :=
  FreeAlgebra.lift_ι_apply _ _

@[simp]
theorem evalM_ι (i : Idx N) : evalM N k (FreeAlgebra.ι ℤ i) = genM N k i :=
  FreeAlgebra.lift_ι_apply _ _

/-- The generator family `genS` has range the union of the two operator ranges. -/
theorem range_genS :
    Set.range (genS N k) =
      Set.range (heckeEnd N k) ∪ Set.range (diamondOpCusp (N := N) k) := by
  rw [genS, Set.Sum.elim_range]

/-- The range of `evalS` is exactly the integral Hecke algebra. -/
theorem evalS_range : (evalS N k).range = heckeAlgℤ N k := by
  rw [evalS, ← Algebra.adjoin_range_eq_range_freeAlgebra_lift, range_genS, heckeAlgℤ]

/-- The underlying-submodule form of `evalS_range`: the `ℤ`-linear range of `evalS` is the integral
Hecke algebra, as a `ℤ`-submodule of `End_ℂ(S_k)`. -/
theorem range_evalS_toLinearMap :
    LinearMap.range (evalS N k).toLinearMap = (heckeAlgℤ N k).toSubmodule := by
  rw [← evalS_range]; rfl

/-- `range evalM` is `ℤ`-finite: a `ℤ`-subalgebra of the finite `ℤ`-module `End_ℤ(𝕄)`. -/
instance instFiniteRangeEvalM : Module.Finite ℤ (evalM N k).range :=
  Module.Finite.of_injective (evalM N k).range.toSubmodule.subtype Subtype.val_injective

/-! ## Commutativity of the image of `evalM` -/

variable (hComm : Pairwise fun i j => Commute (genM N k i) (genM N k j))

include hComm

/-- A single generator commutes with the whole image of `evalM`, given pairwise commutativity of
the generators.  Proved by `FreeAlgebra.induction` on `b`. -/
theorem genM_commute_evalM (i : Idx N) (b : FreeAlgebra ℤ (Idx N)) :
    Commute (genM N k i) (evalM N k b) := by
  induction b using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right c _
  | grade1 j =>
    rw [evalM_ι]
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl _
    · exact hComm hij
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

/-- Every element of `range evalM` commutes with every other, given that the generators pairwise
commute (`hComm`).  Proved by `FreeAlgebra.induction` on `a`, using `genM_commute_evalM`. -/
theorem evalM_commute (a b : FreeAlgebra ℤ (Idx N)) :
    Commute (evalM N k a) (evalM N k b) := by
  induction a using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact (Algebra.commute_algebraMap_right c _).symm
  | grade1 i => rw [evalM_ι]; exact genM_commute_evalM hComm i b
  | mul a₁ a₂ ha₁ ha₂ => rw [map_mul]; exact ha₁.mul_left ha₂
  | add a₁ a₂ ha₁ ha₂ => rw [map_add]; exact ha₁.add_left ha₂

/-! ## The polynomial equivariance identity (the crux) -/

variable (ι : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ))

/-- **The crux.**  Given the generator-level Hecke/diamond equivariance and commutativity of the
symbol-side generators, the identity `ι ((evalS p) f) = (evalM p).dualPrecomp (ι f)` extends from
generators to *all* `p`, by `FreeAlgebra.induction`.  The multiplicative step uses that the image of
`evalM` is commutative (`evalM_commute`), so that the order-reversal forced by `dualPrecomp` being
an
anti-homomorphism is harmless. -/
theorem ι_evalS_eq_dualPrecomp
    (hT : ∀ (n : ℕ+) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      ι (heckeEnd N k n f) = dualPrecomp (heckeSymb N k n.val) (ι f))
    (hD : ∀ (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      ι (diamondOpCusp k d f) = dualPrecomp (diamondSymb N k d) (ι f))
    (p : FreeAlgebra ℤ (Idx N)) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ι ((evalS N k p) f) = dualPrecomp (evalM N k p) (ι f) := by
  induction p using FreeAlgebra.induction generalizing f with
  | grade0 c =>
    -- both sides are scalar (integer) multiples of `ι f`
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_zsmul,
      dualPrecomp_zsmul, dualPrecomp_one, LinearMap.smul_apply, Module.End.one_apply]
  | grade1 i =>
    rw [evalS_ι, evalM_ι]
    cases i with
    | inl n => exact hT n f
    | inr d => exact hD d f
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, dualPrecomp_mul, ha, Module.End.mul_apply, hb,
      ← Module.End.mul_apply, ← Module.End.mul_apply,
      (dualPrecomp_commute (evalM_commute hComm a b)).eq]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, dualPrecomp_add, LinearMap.add_apply,
      ha, hb]

/-! ## The kernel inclusion and the finiteness conclusion -/

/-- From the polynomial equivariance and injectivity of `ι`, the kernel of the `ℤ`-linear map
underlying `evalM` is contained in that of `evalS`. -/
theorem ker_evalM_le_ker_evalS
    (hι : Function.Injective ι)
    (hT : ∀ (n : ℕ+) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      ι (heckeEnd N k n f) = dualPrecomp (heckeSymb N k n.val) (ι f))
    (hD : ∀ (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      ι (diamondOpCusp k d f) = dualPrecomp (diamondSymb N k d) (ι f)) :
    LinearMap.ker (evalM N k).toLinearMap ≤ LinearMap.ker (evalS N k).toLinearMap := by
  intro p hp
  rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hp ⊢
  -- `evalS p` is `ℂ`-linear, so it suffices to show it kills every `f`
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  -- apply injectivity of `ι`
  apply hι
  rw [ι_evalS_eq_dualPrecomp hComm ι hT hD p f, show (evalM N k) p = 0 from hp,
    dualPrecomp_zero, LinearMap.zero_apply, map_zero]

/-- **ES-asm — the faithfulness endgame, abstract form.**  Given a period map `ι : S_k →ₗ[ℂ]
Hom_ℤ(𝕄 N k, ℂ)` that is injective and intertwines the Hecke operators (`hT`) and the diamond
operators (`hD`) with the integral modular-symbol operators — together with commutativity of the
symbol-side Hecke generators (`hComm`) — the integral Hecke algebra `heckeAlgℤ N k` is a finite
`ℤ`-module.

The hypotheses pin the interface that the real period map (`periodMap`/`periodMap_injective`/
`periodMap_hecke`, built separately by ES-3b/3c/4) and the Hecke-commutativity input must satisfy;
this theorem verifies the endgame logic is sound. -/
theorem heckeAlgℤ_finite_of_period
    (hι : Function.Injective ι)
    (hT : ∀ (n : ℕ+) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      ι (heckeEnd N k n f) = dualPrecomp (heckeSymb N k n.val) (ι f))
    (hD : ∀ (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      ι (diamondOpCusp k d f) = dualPrecomp (diamondSymb N k d) (ι f)) :
    Module.Finite ℤ (heckeAlgℤ N k) := by
  -- `ker evalM ≤ ker evalS`, from equivariance + injectivity of `ι`.
  have hker : LinearMap.ker (evalM N k).toLinearMap ≤ LinearMap.ker (evalS N k).toLinearMap :=
    ker_evalM_le_ker_evalS hComm ι hι hT hD
  have hker' : LinearMap.ker (evalM N k).toLinearMap ≤
      Submodule.comap LinearMap.id (LinearMap.ker (evalS N k).toLinearMap) := by
    rwa [Submodule.comap_id]
  -- `range evalM` is `ℤ`-finite (a submodule of the finite module `End_ℤ(𝕄)`).
  haveI : Module.Finite ℤ (LinearMap.range (evalM N k).toLinearMap) :=
    Module.Finite.of_injective (LinearMap.range (evalM N k).toLinearMap).subtype
      Subtype.val_injective
  -- Build a `ℤ`-linear surjection `range evalM ↠ range evalS` *between the ranges*, going
  -- `range evalM ≃ FreeAlgebra ⧸ ker evalM ↠ FreeAlgebra ⧸ ker evalS ≃ range evalS`.  Keeping the
  -- domain a `range` (not a quotient) sidesteps the `ℤ`-module instance diamond on quotients.
  set σ := (evalM N k).toLinearMap.quotKerEquivRange.symm with hσ
  set Q := Submodule.mapQ (LinearMap.ker (evalM N k).toLinearMap)
      (LinearMap.ker (evalS N k).toLinearMap) LinearMap.id hker' with hQ
  set τ := (evalS N k).toLinearMap.quotKerEquivRange with hτ
  have hQsurj : Function.Surjective Q := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (evalS N k).toLinearMap) y
    exact ⟨Submodule.Quotient.mk x, Submodule.mapQ_apply _ _ _ x⟩
  have hsurj : Function.Surjective (τ.toLinearMap ∘ₗ Q ∘ₗ σ.toLinearMap) := by
    simpa using τ.surjective.comp (hQsurj.comp σ.surjective)
  -- so `range evalS` is `ℤ`-finite (a surjective image of the finite module `range evalM`),
  haveI hfin : Module.Finite ℤ (LinearMap.range (evalS N k).toLinearMap) :=
    Module.Finite.of_surjective _ hsurj
  -- and `range evalS = heckeAlgℤ` as `ℤ`-submodules.
  rw [range_evalS_toLinearMap] at hfin
  exact hfin

end HeckeRing.GL2.ModularSymbols
