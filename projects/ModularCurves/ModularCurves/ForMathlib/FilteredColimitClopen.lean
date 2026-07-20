/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FinitePresentationDescent

/-!
# Clopen subsets over filtered colimits

A finite union of basic opens generated at one stage of a filtered colimit which becomes
clopen over the colimit is already clopen at a later stage.
-/

open TopologicalSpace

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
variable {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
variable {t : ∀ ⦃i j : ι⦄, i ≤ j → (S i →ₐ[R] S j)}
variable {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, S i →ₐ[R] A}

private lemma coe_iSup_basicOpen {B κ : Type*} [CommRing B] (f : κ → B) :
    ((↑(⨆ k, PrimeSpectrum.basicOpen (f k)) : Set (PrimeSpectrum B))) =
      (PrimeSpectrum.zeroLocus
        ((Ideal.span (Set.range f) : Ideal B) : Set B))ᶜ := by
  rw [PrimeSpectrum.zeroLocus_span]
  simp only [TopologicalSpace.Opens.coe_iSup,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  congr 2
  ext x
  simp

/-- A finite union of basic opens which is clopen over a filtered colimit is clopen at a
common later stage. -/
theorem IsFilteredAlgColimit.exists_isClopen_iSup_basicOpen
    (H : IsFilteredAlgColimit R S t A uA)
    {κ : Type*} [Finite κ] {i : ι} (f : κ → S i)
    (hclopen : IsClopen
      ((↑(⨆ k, PrimeSpectrum.basicOpen (uA i (f k))) : Set (PrimeSpectrum A)))) :
    ∃ (j : ι) (hij : i ≤ j), IsClopen
      ((↑(⨆ k, PrimeSpectrum.basicOpen (t hij (f k))) :
        Set (PrimeSpectrum (S j)))) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  obtain ⟨e, he, hUe⟩ :=
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen
  have hzero :
      PrimeSpectrum.zeroLocus
          (((Ideal.span (Set.range fun k ↦ uA i (f k))) : Ideal A) : Set A) =
        PrimeSpectrum.zeroLocus
          (((Ideal.span ({e} : Set A)) : Ideal A) : Set A) := by
    apply compl_injective
    rw [← coe_iSup_basicOpen]
    simpa only [PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl] using hUe
  have hradical :
      (Ideal.span (Set.range fun k ↦ uA i (f k))).radical =
        (Ideal.span ({e} : Set A)).radical :=
    PrimeSpectrum.zeroLocus_eq_iff.mp hzero
  have he_mem : e ∈ (Ideal.span (Set.range fun k ↦ uA i (f k))).radical := by
    rw [hradical]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self e)
  have hf_mem (k : κ) :
      uA i (f k) ∈ (Ideal.span ({e} : Set A)).radical := by
    rw [← hradical]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self k))
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp he_mem
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hn
  choose m hm using fun k ↦ Ideal.mem_radical_iff.mp (hf_mem k)
  choose d hd using fun k ↦ Ideal.mem_span_singleton'.mp (hm k)
  let value : Unit ⊕ κ ⊕ κ → A
    | Sum.inl _ => e
    | Sum.inr (Sum.inl k) => c k
    | Sum.inr (Sum.inr k) => d k
  obtain ⟨j₀, value₀, hvalue₀⟩ := H.exists_common_lift value
  letI := H.directed
  obtain ⟨j, hij, hj₀j⟩ := directed_of (· ≤ ·) i j₀
  let e₀ : S j := t hj₀j (value₀ (Sum.inl ()))
  let c₀ (k : κ) : S j := t hj₀j (value₀ (Sum.inr (Sum.inl k)))
  let d₀ (k : κ) : S j := t hj₀j (value₀ (Sum.inr (Sum.inr k)))
  let f₀ (k : κ) : S j := t hij (f k)
  have he₀ : uA j e₀ = e := by
    dsimp [e₀]
    rw [H.compat, hvalue₀]
  have hc₀ (k : κ) : uA j (c₀ k) = c k := by
    dsimp [c₀]
    rw [H.compat, hvalue₀]
  have hd₀ (k : κ) : uA j (d₀ k) = d k := by
    dsimp [d₀]
    rw [H.compat, hvalue₀]
  have hf₀ (k : κ) : uA j (f₀ k) = uA i (f k) := by
    exact H.compat hij (f k)
  let lhs : Unit ⊕ Unit ⊕ κ → S j
    | Sum.inl _ => e₀ * e₀
    | Sum.inr (Sum.inl _) => ∑ k, c₀ k * f₀ k
    | Sum.inr (Sum.inr k) => d₀ k * e₀
  let rhs : Unit ⊕ Unit ⊕ κ → S j
    | Sum.inl _ => e₀
    | Sum.inr (Sum.inl _) => e₀ ^ n
    | Sum.inr (Sum.inr k) => f₀ k ^ m k
  have hlr (q : Unit ⊕ Unit ⊕ κ) : uA j (lhs q) = uA j (rhs q) := by
    rcases q with _ | _ | k
    · simpa only [lhs, rhs, map_mul, he₀] using he.eq
    · simpa only [lhs, rhs, map_sum, map_mul, map_pow, hc₀, hf₀, he₀] using hc
    · simpa only [lhs, rhs, map_mul, map_pow, hd₀, he₀, hf₀] using hd k
  obtain ⟨k, hjk, heq⟩ := H.exists_common_eq lhs rhs hlr
  let e₁ : S k := t hjk e₀
  let c₁ (q : κ) : S k := t hjk (c₀ q)
  let d₁ (q : κ) : S k := t hjk (d₀ q)
  let f₁ (q : κ) : S k := t (hij.trans hjk) (f q)
  have he₁ : IsIdempotentElem e₁ := by
    have h := heq (Sum.inl ())
    unfold IsIdempotentElem
    simpa only [lhs, rhs, e₁, map_mul] using h
  have hf₁ (q : κ) : t hjk (f₀ q) = f₁ q := by
    dsimp [f₀, f₁]
    rw [← H.t_trans hij hjk]
  have hc₁ : ∑ q, c₁ q * f₁ q = e₁ ^ n := by
    have h := heq (Sum.inr (Sum.inl ()))
    simpa only [lhs, rhs, c₁, f₁, e₁, map_sum, map_mul, map_pow,
      hf₁] using h
  have hd₁ (q : κ) : d₁ q * e₁ = f₁ q ^ m q := by
    have h := heq (Sum.inr (Sum.inr q))
    simpa only [lhs, rhs, d₁, e₁, f₁, map_mul, map_pow,
      hf₁] using h
  have he₁_mem : e₁ ∈ (Ideal.span (Set.range f₁)).radical := by
    exact ⟨n, Ideal.mem_span_range_iff_exists_fun.mpr ⟨c₁, hc₁⟩⟩
  have hf₁_mem (q : κ) : f₁ q ∈ (Ideal.span ({e₁} : Set (S k))).radical := by
    exact ⟨m q, Ideal.mem_span_singleton'.mpr ⟨d₁ q, hd₁ q⟩⟩
  have hopen : ⨆ q, PrimeSpectrum.basicOpen (f₁ q) =
      PrimeSpectrum.basicOpen e₁ := by
    apply le_antisymm
    · exact iSup_le fun q ↦
        (PrimeSpectrum.basicOpen_le_basicOpen_iff (f₁ q) e₁).mpr (hf₁_mem q)
    · rw [← SetLike.coe_subset_coe, coe_iSup_basicOpen,
        PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
      apply Set.compl_subset_compl.mpr
      rw [← PrimeSpectrum.zeroLocus_span ({e₁} : Set (S k))]
      exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
        (Ideal.span (Set.range f₁)) (Ideal.span ({e₁} : Set (S k)))).mpr
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr he₁_mem))
  refine ⟨k, hij.trans hjk, ?_⟩
  rw [show (⨆ q, PrimeSpectrum.basicOpen (t (hij.trans hjk) (f q))) =
    PrimeSpectrum.basicOpen e₁ from hopen]
  exact PrimeSpectrum.isClopen_iff.mpr ⟨e₁, he₁, rfl⟩

/-- A finite union of basic opens on a spread-stage affine chart which becomes clopen on
the colimit chart is clopen at a common later spread stage. -/
theorem SpreadData.exists_isClopen_iSup_basicOpen
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData S uA B) (H : IsFilteredAlgColimit R S t A uA)
    {κ : Type*} [Finite κ] (P : {i : ι // D.i₀ ≤ i})
    (f : κ → D.spreadStage (t := t) P.2)
    (hclopen : IsClopen
      ((↑(⨆ k, PrimeSpectrum.basicOpen
        (D.stageToColimit H P (f k))) : Set (PrimeSpectrum B)))) :
    ∃ (Q : {i : ι // D.i₀ ≤ i}) (hPQ : P ≤ Q), IsClopen
      ((↑(⨆ k, PrimeSpectrum.basicOpen
        (D.stageTransition H hPQ (f k))) :
          Set (PrimeSpectrum (D.spreadStage (t := t) Q.2)))) := by
  letI : ∀ P : {j : ι // D.i₀ ≤ j},
      Algebra (S D.i₀) (D.spreadStage (t := t) P.2) :=
    fun P => ((algebraMap (S P.1) (D.spreadStage (t := t) P.2)).comp
      (t P.2).toRingHom).toAlgebra
  letI : Algebra (S D.i₀) B :=
    ((algebraMap A B).comp (uA D.i₀).toRingHom).toAlgebra
  exact (D.isFilteredAlgColimit H).exists_isClopen_iSup_basicOpen f hclopen

end Algebra
