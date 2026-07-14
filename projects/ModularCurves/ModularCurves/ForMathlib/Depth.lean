/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Module depth `≥ k` over a Noetherian local ring, and its API — [T-DEPTH]

PLANNING SKELETON (statements + `:= sorry`, no proofs) for the depth invariant that closes the
BACKWARD core of Buchsbaum–Eisenbud (Stacks 00N1 `(2)⟹(1)`) via the acyclicity lemma
(Stacks 00N0 = Lemma 10.102.8).  See
`projects/ModularCurves/.mathlib-quality/decomposition-depth.md` for the full ticket tree, the
verbatim Stacks quotes per leaf, and the route decision.

## The invariant

mathlib has NO packaged `depth` (only `RingTheory.Sequence.IsRegular`;
`RingTheory/Regular/Depth.lean`
is a deprecated stub, and `RegularSequence.lean`'s own TODO lists "depth" as unbuilt).  We package
the LEAN predicate `Module.HasDepthGE R M k := "𝔪 contains an M-regular sequence of length k"`
(Stacks 00LE/00LF depth, in `≥ k` predicate form).  This is the module analogue of the existing
`Ideal.gradeGE` (`ForMathlib.Grade`, the `M = R` case): the acyclicity lemma 00N0 states its
hypothesis `depth(Mᵢ) ≥ i` and conclusion `depth(H) ≥ 1` purely in `≥`-form, so the predicate is the
leanest faithful shape (no `ℕ∞` arithmetic).

## The decisive reuse — depth⟺Ext is ALREADY PROVEN

Stacks 00LW (Lemma 10.72.5): `depth(M) = min { i | Extⁱ(R/𝔪, M) ≠ 0 }`, equivalently
`depth(M) ≥ k ⟺ Extⁱ_R(R/𝔪, M) = 0 ∀ i < k`.  This is EXACTLY `ForMathlib.Grade.rees_core`
specialised to `I = 𝔪` (that lemma is proved there in full, for a GENERAL finite module `M`, by the
classical Rees induction — it is stated `∀ M`, not just `M = R`).  So
`hasDepthGE_iff_forall_subsingleton_ext` is discharged by exposing `rees_core`; the depth⟺Ext bridge
is NOT new work.

Consequently the depth-of-a-short-exact-sequence inequalities (Stacks 00LX = Lemma 10.72.6) — the
sole engine of the acyclicity lemma — follow from that Ext characterisation plus the covariant `Ext`
long exact sequence (`Ext.covariant_sequence_exact₁/₂/₃`), the SAME machinery `ForMathlib.Grade`
already drives.  This is why the depth layer is tractable, not a wall.

## NOT needed: Auslander–Buchsbaum

The Stacks proof of the FORWARD core (00N1 `(1)⟹(2)`) does **not** use Auslander–Buchsbaum: it runs
via associated primes (depth-0 localisations), rank stability, a prime-avoidance nonzerodivisor, and
quotient-by-a-nonzerodivisor (00MZ) + induction.  Neither direction of 00N1 invokes 090V/0AVJ.  So
this file contains NO Auslander–Buchsbaum leaf.
-/
import ModularCurves.ForMathlib.Grade

noncomputable section

open RingTheory.Sequence CategoryTheory Abelian

universe u

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **[T-DEPTH.def]** `HasDepthGE R M k`: the maximal ideal `𝔪` of the local ring `R` contains an
`M`-regular sequence of length `k` (Stacks 00LE/00LF, `depth_𝔪(M) ≥ k`, predicate form).  The module
analogue of `Ideal.gradeGE` (`ForMathlib.Grade`), which is the `M = R` special case.  A real `def`
(no `sorry`); everything below is API. -/
def HasDepthGE (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ) : Prop :=
  ∃ rs : List R, rs.length = k ∧ IsRegular M rs ∧ ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R

/-- `HasDepthGE R M 0 ↔ Nontrivial M` (the empty sequence is `M`-regular iff `M ≠ 0`); documents the
convention that `depth` of the zero module is not `≥ 0` in this predicate — callers carry
`Nontrivial` exactly where Stacks 00LX/00N0 say "nonzero finite module". -/
theorem hasDepthGE_zero_iff (M : Type u) [AddCommGroup M] [Module R M] :
    HasDepthGE R M 0 ↔ Nontrivial M := by
  constructor
  · rintro ⟨rs, hlen, hreg, -⟩
    have hnil : rs = [] := by
      cases rs with
      | nil => rfl
      | cons a t => simp at hlen
    subst hnil
    have h := hreg.top_ne_smul
    rw [Ideal.ofList_nil, Submodule.bot_smul] at h
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact h (by haveI := (Submodule.subsingleton_iff R).mpr hcon; exact Subsingleton.elim _ _)
  · intro h
    haveI := h
    exact ⟨[], rfl, IsRegular.nil R M, by simp⟩

/-- **[T-DEPTH.mono]** `depth` is monotone in `k`: a prefix of an `M`-regular sequence is
`M`-regular. -/
theorem hasDepthGE_mono {M : Type u} [AddCommGroup M] [Module R M] {j k : ℕ}
    (h : HasDepthGE R M k) (hjk : j ≤ k) : HasDepthGE R M j := by
  obtain ⟨rs, hlen, hreg, hmem⟩ := h
  refine ⟨rs.take j, ?_, ?_, ?_⟩
  · rw [List.length_take, hlen, min_eq_left hjk]
  · -- The prefix `rs.take j` is `M`-regular: it is weakly regular (prefix of a weakly regular
    -- sequence) and proper (its ideal is `≤` the proper ideal of the full sequence).
    have hwr : IsWeaklyRegular M (rs.take j) := by
      have happ : IsWeaklyRegular M (rs.take j ++ rs.drop j) := by
        rw [List.take_append_drop]; exact hreg.toIsWeaklyRegular
      exact ((isWeaklyRegular_append_iff M _ _).mp happ).1
    have hle : Ideal.ofList (rs.take j) ≤ Ideal.ofList rs := by
      conv_rhs => rw [← List.take_append_drop j rs, Ideal.ofList_append]
      exact le_sup_left
    have hsmul : Ideal.ofList (rs.take j) • (⊤ : Submodule R M) ≤ Ideal.ofList rs • ⊤ :=
      Submodule.smul_mono hle le_rfl
    exact ⟨hwr, fun heq => hreg.top_ne_smul (le_antisymm (heq.le.trans hsmul) le_top)⟩
  · intro x hx; exact hmem x (List.take_subset _ _ hx)

/-- **[T-DEPTH.ext] Stacks 00LW (Lemma 10.72.5).**  Over a Noetherian local ring, for a nonzero
finite module, `depth(M) ≥ k` iff `Extⁱ_R(R/𝔪, M) = 0` for every `i < k`.  This is
`ForMathlib.Grade.rees_core` at `I = 𝔪` (that lemma is proved in full there, for GENERAL `M`); the
discharge is to expose `rees_core` (currently `private`) or re-run its Rees induction. -/
theorem hasDepthGE_iff_forall_subsingleton_ext [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (k : ℕ) :
    HasDepthGE R M k ↔
      ∀ i : Fin k, Subsingleton
        (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) i) :=
  rees_core (R := R) (le_refl (IsLocalRing.maximalIdeal R)) k (ModuleCat.of R M)
    inferInstance inferInstance

/-! ### Stacks 00LX (Lemma 10.72.6): the three depth inequalities of a short exact sequence

For `0 → A →f→ B →g→ C → 0` of nonzero finite modules, Stacks 00LX asserts
(1) `depth B ≥ min(depth A, depth C)`,
(2) `depth C ≥ min(depth B, depth A − 1)`,
(3) `depth A ≥ min(depth B, depth C + 1)`.
Each follows from the `Ext`-characterisation above and the covariant long exact `Ext`-sequence
`⋯ → Extⁱ(κ,A) → Extⁱ(κ,B) → Extⁱ(κ,C) → Extⁱ⁺¹(κ,A) → ⋯`.  **(2) and (3) are the load-bearing
ones** for the acyclicity lemma; (1) is stated for completeness.  We give them in `≥ k` predicate
form (`min(x, y) ≥ k ⟺ x ≥ k ∧ y ≥ k`), which is what 00N0's syzygy induction consumes and avoids
`ℕ∞` truncated subtraction. -/

omit [IsLocalRing R] in
/-- The `ModuleCat`-valued short exact sequence attached to a short exact sequence of `R`-linear
maps `0 → A →f→ B →g→ C → 0`.  This packages `f`, `g` into a `ShortComplex.ShortExact`, ready
for the
covariant `Ext` long exact sequence. -/
private lemma shortExact_of_exact {A B C : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (hfg0 : g.comp f = 0) :
    (ShortComplex.moduleCatMk f g hfg0).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact (hfg x).mp hx
  mono_f := (ModuleCat.mono_iff_injective _).mpr hf
  epi_g := (ModuleCat.epi_iff_surjective _).mpr hg

/-- **[T-DEPTH.ses1] Stacks 00LX(1).**  `depth B ≥ min(depth A, depth C)`. -/
theorem hasDepthGE_mid_of_shortExact [IsNoetherianRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {k : ℕ} (hA : HasDepthGE R A k) (hC : HasDepthGE R C k) : HasDepthGE R B k := by
  set κ := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) with hκ
  have hfg0 : g.comp f = 0 := by ext a; exact (hfg (f a)).mpr ⟨a, rfl⟩
  set S := ShortComplex.moduleCatMk f g hfg0 with hSdef
  have hS : S.ShortExact := shortExact_of_exact R hf hfg hg hfg0
  rw [hasDepthGE_iff_forall_subsingleton_ext] at hA hC ⊢
  intro i
  refine subsingleton_of_forall_eq 0 (fun β => ?_)
  haveI : Subsingleton (Ext κ S.X₁ (i : ℕ)) := hA i
  haveI : Subsingleton (Ext κ S.X₃ (i : ℕ)) := hC i
  -- `g* β = 0` since `Extⁱ(κ,C)` vanishes; hence `β = f* α` with `α ∈ Extⁱ(κ,A) = 0`.
  have hg0 : β.comp (Ext.mk₀ S.g) (add_zero _) = 0 := Subsingleton.elim _ _
  obtain ⟨α, hα⟩ := Ext.covariant_sequence_exact₂ (X := κ) (hS := hS) (x₂ := β) (hx₂ := hg0)
  rw [← hα, Subsingleton.elim α 0]
  exact Ext.zero_comp _ _ (Ext.mk₀ S.f) _ (add_zero _)

/-- **[T-DEPTH.ses2] Stacks 00LX(2) — LOAD-BEARING.**  `depth C ≥ min(depth B, depth A − 1)`, i.e.
`depth B ≥ k` and `depth A ≥ k+1` force `depth C ≥ k`.  This is the inequality that drives the
acyclicity lemma (Stacks 00N0) down the syzygy tower. -/
theorem hasDepthGE_quotient_of_shortExact [IsNoetherianRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {k : ℕ} (hB : HasDepthGE R B k) (hA : HasDepthGE R A (k + 1)) : HasDepthGE R C k := by
  set κ := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) with hκ
  have hfg0 : g.comp f = 0 := by ext a; exact (hfg (f a)).mpr ⟨a, rfl⟩
  set S := ShortComplex.moduleCatMk f g hfg0 with hSdef
  have hS : S.ShortExact := shortExact_of_exact R hf hfg hg hfg0
  rw [hasDepthGE_iff_forall_subsingleton_ext] at hB hA ⊢
  intro i
  refine subsingleton_of_forall_eq 0 (fun α => ?_)
  haveI : Subsingleton (Ext κ S.X₂ (i : ℕ)) := hB i
  haveI : Subsingleton (Ext κ S.X₁ ((i : ℕ) + 1)) := hA ⟨(i : ℕ) + 1, by omega⟩
  -- `δ α = 0` since `Extⁱ⁺¹(κ,A)` vanishes; hence `α = g* β` with `β ∈ Extⁱ(κ,B) = 0`.
  have hδ : α.comp hS.extClass (rfl : (i : ℕ) + 1 = (i : ℕ) + 1) = 0 := Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₃ (X := κ) (hS := hS) (x₃ := α)
    (hn₁ := rfl) (hx₃ := hδ)
  rw [← hβ, Subsingleton.elim β 0]
  exact Ext.zero_comp _ _ (Ext.mk₀ S.g) _ (add_zero _)

/-- **[T-DEPTH.ses3] Stacks 00LX(3) — LOAD-BEARING.**  `depth A ≥ min(depth B, depth C + 1)`, i.e.
`depth B ≥ k+1` and `depth C ≥ k` force `depth A ≥ k+1`.  Used for the `0 → Kᵢ → Mᵢ → im → 0`
kernel-depth step of the acyclicity lemma (`depth Kᵢ ≥ 1` from `depth Mᵢ ≥ i ≥ 1`, taking
`k = 0`). -/
theorem hasDepthGE_sub_of_shortExact [IsNoetherianRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {k : ℕ} (hB : HasDepthGE R B (k + 1)) (hC : HasDepthGE R C k) : HasDepthGE R A (k + 1) := by
  set κ := ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) with hκ
  have hfg0 : g.comp f = 0 := by ext a; exact (hfg (f a)).mpr ⟨a, rfl⟩
  set S := ShortComplex.moduleCatMk f g hfg0 with hSdef
  have hS : S.ShortExact := shortExact_of_exact R hf hfg hg hfg0
  haveI : Mono S.f := hS.mono_f
  rw [hasDepthGE_iff_forall_subsingleton_ext] at hB hC ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · -- Degree `0`: `Ext⁰(κ,A) ↪ Ext⁰(κ,B) = 0` since `f` is mono, so `Ext⁰(κ,A) = 0`.
    simp only [Fin.val_zero]
    haveI : Subsingleton (Ext κ S.X₂ 0) := hB 0
    refine ⟨fun a b => ?_⟩
    have hinj := Ext.postcomp_mk₀_injective_of_mono κ S.f
    exact hinj (Subsingleton.elim _ _)
  · -- Degree `j+1`: `f* γ = 0` since `Extʲ⁺¹(κ,B)` vanishes; hence `γ = δ x₃`,
    -- `x₃ ∈ Extʲ(κ,C) = 0`.
    simp only [Fin.val_succ]
    haveI : Subsingleton (Ext κ S.X₃ (j : ℕ)) := hC j
    haveI : Subsingleton (Ext κ S.X₂ ((j : ℕ) + 1)) := hB ⟨(j : ℕ) + 1, by omega⟩
    refine subsingleton_of_forall_eq 0 (fun γ => ?_)
    have hf0 : γ.comp (Ext.mk₀ S.f) (add_zero _) = 0 := Subsingleton.elim _ _
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (X := κ) (hS := hS) (x₁ := γ)
      (hx₁ := hf0) (hn₀ := rfl)
    rw [← hx₃, Subsingleton.elim x₃ 0]
    exact Ext.zero_comp _ _ hS.extClass _ rfl

/-- **Regular element in a non-avoided ideal** (prime avoidance against the associated primes).
If `I` is contained in no associated prime of a finite module `M`, then `I` contains an
`M`-regular element.  (Re-derivation of the recipe in `ForMathlib.BuchsbaumEisenbud`, kept local so
this file does not depend on that `private` lemma.) -/
private theorem exists_isSMulRegular_of_forall_not_le_associatedPrimes {S : Type*} [CommRing S]
    [IsNoetherianRing S] {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (I : Ideal S) (h : ∀ p ∈ associatedPrimes S M, ¬ (I : Set S) ⊆ p) :
    ∃ x ∈ I, IsSMulRegular M x := by
  have hfin : (associatedPrimes S M).Finite := associatedPrimes.finite S M
  have hnot : ¬ ((I : Set S) ⊆ ⋃ p ∈ associatedPrimes S M, (p : Set S)) := by
    rw [Ideal.subset_union_prime_finite hfin ⊥ ⊥
      (fun p hp _ _ => (AssociatedPrimes.mem_iff.mp hp).isPrime)]
    rintro ⟨p, hp, hle⟩
    exact h p hp hle
  rw [Set.not_subset] at hnot
  obtain ⟨x, hxI, hxnot⟩ := hnot
  refine ⟨x, hxI, ?_⟩
  rw [biUnion_associatedPrimes_eq_compl_regular S M] at hxnot
  simpa using hxnot

/-- **[T-DEPTH.ass] Stacks 00LD / 00LW base case.**  `depth(M) ≥ 1 ⟺ 𝔪 ∉ Ass(M)`: the maximal
ideal carries an `M`-regular element iff it is not an associated prime.  This turns "the
homology `H`
is supported only at `𝔪` and `H ≠ 0`" into "`¬ HasDepthGE R H 1`" (since then `𝔪 ∈ Ass H`), the
contradiction that closes 00N1's backward induction. -/
theorem hasDepthGE_one_iff_notMem_associatedPrimes [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    HasDepthGE R M 1 ↔ IsLocalRing.maximalIdeal R ∉ associatedPrimes R M := by
  constructor
  · rintro ⟨rs, hlen, hreg, hmem⟩ hmax
    obtain ⟨x, rfl⟩ : ∃ x, rs = [x] := by
      cases rs with
      | nil => simp at hlen
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b u => simp at hlen
    have hx : x ∈ IsLocalRing.maximalIdeal R := hmem x List.mem_cons_self
    have hxreg : IsSMulRegular M x := ((isRegular_cons_iff M x []).mp hreg).1
    have hxin : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_biUnion hmax hx
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hxin
    exact hxin hxreg
  · intro hmax
    obtain ⟨x, hx, hxreg⟩ := exists_isSMulRegular_of_forall_not_le_associatedPrimes
      (M := M) (IsLocalRing.maximalIdeal R) (by
        intro p hp hle
        apply hmax
        have hprime : p.IsPrime := (AssociatedPrimes.mem_iff.mp hp).isPrime
        have hpmax : p ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hprime.ne_top
        have hpeq : p = IsLocalRing.maximalIdeal R := le_antisymm hpmax hle
        rwa [hpeq] at hp)
    refine ⟨[x], rfl, ?_, ?_⟩
    · rw [isRegular_cons_iff]
      refine ⟨hxreg, ?_⟩
      haveI := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
      exact IsRegular.nil R _
    · intro y hy
      simp only [List.mem_singleton] at hy
      rw [hy]; exact hx

/-- **[T-DEPTH.free]**  `depth(Rⁿ) = depth(R)` for `n ≥ 1`: an `R`-regular sequence acts diagonally,
so it is `Rⁿ`-regular.  Lets the acyclicity lemma (over abstract finite modules) be applied to the
free complex of Buchsbaum–Eisenbud, where `Mᵢ = R^{rk i}` and `depth Mᵢ = depth R`. -/
theorem hasDepthGE_pi_of_hasDepthGE {n : ℕ} (hn : 0 < n) (k : ℕ)
    (h : HasDepthGE R R k) : HasDepthGE R (Fin n → R) k := by
  obtain ⟨rs, hlen, hreg, hmem⟩ := h
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → R) := inferInstance
  haveI : Module.Flat R (Fin n → R) := Module.Flat.of_free
  refine ⟨rs, hlen, ?_, hmem⟩
  -- Over the local ring, with the sequence in `𝔪`, regularity reduces to weak regularity;
  -- weak regularity transfers from `R` to `Fin n → R` by flat base change along the diagonal.
  have hwr : IsWeaklyRegular (Fin n → R) rs :=
    (isWeaklyRegular_map_algebraMap_iff (S := Fin n → R) (M := Fin n → R) (rs := rs)).mp
      (IsWeaklyRegular.of_flat (S := Fin n → R) hreg.toIsWeaklyRegular)
  exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hwr

end Module

end
