/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Topological Nakayama: finiteness from a finite adic quotient

([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaf 10.)  If `R` is
`I`-adically precomplete, `M` is `I`-adically Hausdorff, and `M/IM` is a
finite `R`-module, then `M` is a finite `R`-module: lift generators of the
quotient, and apply the adic surjectivity criterion
`surjective_of_mkQ_comp_surjective`.

The consumer instantiates `R = 𝒪_K` (`π`-adically complete), `M = B` a
noetherian-domain quotient of the integral Tate algebra (`π`-adically
Hausdorff by Krull intersection), with `B/πB` finite over the residue field.
-/

@[expose] public section

open scoped Classical

section AdicNakayama

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `I • ⊤` on `R` itself is `I`. -/
theorem ideal_smul_top_self {R : Type*} [CommRing R] (I : Ideal R) :
    (I • (⊤ : Submodule R R)) = (I : Submodule R R) := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · simpa [smul_eq_mul] using Ideal.mul_mem_right x _ ha
  · have h1 : x • (1 : R) ∈ I • (⊤ : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa using h1

/-- `I • ⊤` on a finite power of `R` is the coordinatewise ideal. -/
theorem ideal_smul_top_pi {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (I • (⊤ : Submodule R (ι → R))) =
      Submodule.pi Set.univ (fun _ => (I : Submodule R R)) := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · refine Submodule.mem_pi.mpr fun i _ => ?_
    simpa [smul_eq_mul] using Ideal.mul_mem_right (x i) _ ha
  · rw [Submodule.mem_pi] at hx
    have hxs : x = ∑ i : ι, Pi.single i (x i) :=
      (Finset.univ_sum_single x).symm
    rw [hxs]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : Pi.single i (x i) = (x i) • Pi.single i (1 : R) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    rw [h1]
    exact Submodule.smul_mem_smul (hx i trivial) Submodule.mem_top

/-- Precompleteness passes to finite powers, coordinatewise. -/
theorem isPrecomplete_pi {R : Type*} [CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (ι : Type*) [Finite ι] :
    IsPrecomplete I (ι → R) := by
  classical
  cases nonempty_fintype ι
  constructor
  intro f hf
  have hcomp : ∀ i : ι, ∃ L : R, ∀ n,
      f n i ≡ L [SMOD (I ^ n • (⊤ : Submodule R R))] := by
    intro i
    refine IsPrecomplete.prec ‹IsPrecomplete I R› (fun {m n} hmn => ?_)
    have h1 := hf hmn
    rw [SModEq.sub_mem] at h1 ⊢
    rw [ideal_smul_top_pi] at h1
    rw [ideal_smul_top_self]
    have h2 := Submodule.mem_pi.mp h1 i trivial
    simpa using h2
  choose L hL using hcomp
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, ideal_smul_top_pi]
  refine Submodule.mem_pi.mpr fun i _ => ?_
  have h3 := hL i n
  rw [SModEq.sub_mem, ideal_smul_top_self] at h3
  simpa using h3

/-- **Topological Nakayama**: over an `I`-precomplete base, an `I`-Hausdorff
module with finitely generated reduction mod `I` is finitely generated. -/
theorem Module.Finite.of_finite_quotient_smul_top_of_isPrecomplete
    (I : Ideal R) [IsPrecomplete I R] [IsHausdorff I M]
    (hfin : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose g hg using Submodule.mkQ_surjective (I • (⊤ : Submodule R M))
  set v : s → M := fun i => g i.1 with hv
  set F : (s → R) →ₗ[R] M := Fintype.linearCombination R v with hF
  have hcomp : Function.Surjective
      ((I • (⊤ : Submodule R M)).mkQ ∘ₗ F) := by
    intro y
    have hy : y ∈ Submodule.span R (↑s : Set (M ⧸ (I • (⊤ : Submodule R M)))) := by
      rw [hs]
      exact Submodule.mem_top
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hy
    refine ⟨fun i => c i.1, ?_⟩
    have h1 : ((I • (⊤ : Submodule R M)).mkQ ∘ₗ F) (fun i => c i.1) =
        ∑ i : s, c i.1 • (I • (⊤ : Submodule R M)).mkQ (v i) := by
      rw [LinearMap.comp_apply, hF, Fintype.linearCombination_apply,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    rw [h1]
    have h2 : ∀ i : s, (I • (⊤ : Submodule R M)).mkQ (v i) = i.1 := by
      intro i
      rw [hv]
      exact hg i.1
    calc ∑ i : s, c i.1 • (I • (⊤ : Submodule R M)).mkQ (v i)
        = ∑ i : s, c i.1 • i.1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [h2 i]
      _ = ∑ a ∈ s, c a • a := Finset.sum_coe_sort s (fun a => c a • a)
      _ = y := hc
  haveI : IsPrecomplete I (s → R) := isPrecomplete_pi I s
  exact Module.Finite.of_surjective F
    (surjective_of_mkQ_comp_surjective hcomp)

end AdicNakayama
