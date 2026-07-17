/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetNoetherianVertices
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Strict graph–Koszul exactness in degrees ≤ 2 ([FJP] Lemma 4.2)

Source: [FJP] Lemma 4.2 (verbatim statement): "Let `D` be an affinoid k-algebra, possibly
nonreduced, and let `g, f₁, …, f_m ∈ D` generate the unit ideal. Put `P_D = D⟨T₁,…,T_m⟩`,
`r_i = gT_i − f_i`. For `m ≥ 1`, the Koszul complex `K_{P_D}(r₁,…,r_m)` is strictly exact in
positive degrees. Moreover, every differential has closed image and is strict onto that
image. In particular, `I_D = im(d₁) ⊂ P_D` is closed and `d₁ : P_D^m ↠ I_D` is strict."

Design (DD6, `plan.md`): mathlib has no Koszul complexes, and the downstream consumer
([FJP] Lemma 4.3) uses only exterior degrees ≤ 2 — (4.7) `d₁`-lifting with constant and
(4.8) `d₂`-lifting onto `ker d₁` with constant. We therefore state everything concretely:
`d₁ u = ∑ uᵢ rᵢ` on `m`-tuples and `d₂` on strictly-ordered pairs with the [FJP] p.10 sign
convention `d₂(e_i ∧ e_j) = r_i e_j − r_j e_i`.

Proof architecture (mirrors [FJP]'s proof exactly):
1. polynomial level over any commutative ring: coordinate-sequence syzygies are
   Koszul-generated (elementary induction); translation `T ↦ T + a` and unit scaling
   transport this to `(gT_i − f_i)` over `D[T]_g`; the two-case prime-local argument plus
   `Submodule.eq_top_of_localization_maximal` globalises ("the localization of every positive
   Koszul homology module at every prime … is zero; hence each such homology module is
   zero" — degrees ≤ 1 form);
2. `P_D ≅ (D₀[T])^∧_ϖ[1/ϖ]` for a noetherian ring of definition `D₀` ([FJP] (4.4)); the base
   change `D[T] → P_D` is **flat** (mathlib `AdicCompletion.flat_of_isNoetherian` = Stacks
   00MB + localisation), and only *positive-degree* exactness transfers ([FJP]: "Notice that
   `g, f_i` need not lie in `D₀`, because exactness was established before completion" —
   and `H₀` genuinely changes: `r` can become a unit in `D⟨T⟩`);
3. strictness/closedness over the noetherian `P_D` via the finite-module theory
   (`NoetherianTateModules.lean`, Wedhorn 6.18 = the Huber [4, Lemma 2.4(ii)] citation) and
   the Banach open mapping theorem with constants
   (`ContinuousLinearMap.exists_preimage_norm_le`).
-/

open Filter Topology

namespace FiniteJet

namespace GraphKoszul

/-! ### The concrete differentials -/

section Differentials

variable {S : Type*} [CommRing S] {m : ℕ}

/-- Index type for exterior degree 2: strictly ordered pairs. -/
abbrev Pairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

/-- `d₁ u = ∑ᵢ uᵢ rᵢ` — the first graph–Koszul differential. -/
def d1 (r : Fin m → S) (u : Fin m → S) : S := ∑ i, u i * r i

/-- `d₂` on ordered pairs, with the [FJP] p.10 sign convention
`d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`:
`(d₂ v)_j = ∑_{i<j} v_{ij} r_i − ∑_{k>j} v_{jk} r_k`. -/
def d2 (r : Fin m → S) (v : Pairs m → S) : Fin m → S := fun j =>
  (∑ i, if h : i < j then v ⟨(i, j), h⟩ * r i else 0) -
    ∑ k, if h : j < k then v ⟨(j, k), h⟩ * r k else 0

/-- `d₁ ∘ d₂ = 0` (the Koszul relations are syzygies). -/
theorem d1_d2 (r : Fin m → S) (v : Pairs m → S) : d1 r (d2 r v) = 0 := by
  unfold d1 d2
  simp only [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a < b
  · rw [dif_pos hab, dif_pos hab, mul_right_comm]
  · rw [dif_neg hab, dif_neg hab, zero_mul, zero_mul]

end Differentials

/-! ### Polynomial level: syzygies of the graph sequence are Koszul-generated

[FJP] Lemma 4.2, proof (verbatim): "First work over `D[T₁,…,T_m]`. At a prime not containing
every `r_i`, one generator is a unit and the localized Koszul complex is contractible. At a
prime containing all `r_i`, choose `1 = a₀g + ∑ a_i f_i`. … Thus `g` is a unit in that local
ring … Over `D_g`, translation by the tuple `(f_i/g)_i` identifies `(T_i − f_i/g)_i` with the
coordinate sequence `(T_i)_i`. The coordinate sequence is regular over an arbitrary
coefficient ring … The polynomial Koszul complex is therefore exact in positive degrees, even
when `D` is nonreduced. Indeed, the localization of every positive Koszul homology module at
every prime of `D[T₁,…,T_m]` is zero by the two cases above; hence each such homology module
is zero." -/

section Polynomial

variable {D : Type*} [CommRing D] {m : ℕ}

open MvPolynomial in
/-- Coordinate-sequence syzygies over an arbitrary base are Koszul-generated (the elementary
multidegree induction; [FJP]: "The coordinate sequence is regular over an arbitrary
coefficient ring"). -/
theorem syzygy_coordinate (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => (X i : MvPolynomial (Fin m) D)) u = 0) :
    ∃ v, d2 (fun i => (X i : MvPolynomial (Fin m) D)) v = u := by
  classical
  induction m with
  | zero => exact ⟨fun p => 0, funext fun i => i.elim0⟩
  | succ m ih =>
    set e := MvPolynomial.finSuccEquiv D m with he
    set U : Fin (m + 1) → Polynomial (MvPolynomial (Fin m) D) := fun i => e (u i) with hUdef
    -- the relation in `A[y]`, `y := X 0`
    have hrel : U 0 * Polynomial.X +
        ∑ i : Fin m, U i.succ * Polynomial.C (X i) = 0 := by
      have h0 := congrArg e h
      rw [map_zero] at h0
      rw [← h0]
      unfold d1
      rw [map_sum, Fin.sum_univ_succ]
      congr 1
      · rw [map_mul, MvPolynomial.finSuccEquiv_X_zero]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [map_mul, MvPolynomial.finSuccEquiv_X_succ]
    -- reduction mod `y`: the constant coefficients form a coordinate syzygy over `Fin m`
    set a : Fin m → MvPolynomial (Fin m) D := fun i => (U i.succ).coeff 0 with hadef
    have hared : d1 (fun i => (X i : MvPolynomial (Fin m) D)) a = 0 := by
      have hc := congrArg (fun p : Polynomial (MvPolynomial (Fin m) D) => p.coeff 0) hrel
      simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.mul_coeff_zero,
        Polynomial.coeff_X_zero, mul_zero, zero_add, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_zero] at hc
      unfold d1
      exact hc
    obtain ⟨w, hw⟩ := ih a hared
    -- the `divX` decomposition of the positive part
    set Q : Fin m → Polynomial (MvPolynomial (Fin m) D) := fun i => (U i.succ).divX with hQdef
    have hdecomp : ∀ i : Fin m, U i.succ = Polynomial.X * Q i + Polynomial.C (a i) :=
      fun i => (Polynomial.X_mul_divX_add (U i.succ)).symm
    -- cancel `y`: the top coefficient is Koszul-expressed
    have hU0 : U 0 = -∑ i : Fin m, Q i * Polynomial.C (X i) := by
      have hXmul : Polynomial.X *
          (U 0 + ∑ i : Fin m, Q i * Polynomial.C (X i)) = 0 := by
        have hsplit : ∑ i : Fin m, U i.succ * Polynomial.C (X i) =
            Polynomial.X * ∑ i : Fin m, Q i * Polynomial.C (X i) +
              Polynomial.C (d1 (fun i => (X i : MvPolynomial (Fin m) D)) a) := by
          unfold d1
          rw [Finset.mul_sum, map_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hdecomp i, add_mul, map_mul, mul_assoc]
        rw [mul_add, mul_comm Polynomial.X (U 0)]
        have h2 := hrel
        rw [hsplit, hared, map_zero, add_zero] at h2
        exact h2
      have hcancel : U 0 + ∑ i : Fin m, Q i * Polynomial.C (X i) = 0 := by
        refine Polynomial.ext fun n => ?_
        have hcn := congrArg (fun q : Polynomial (MvPolynomial (Fin m) D) =>
          q.coeff (n + 1)) hXmul
        simpa [Polynomial.coeff_X_mul] using hcn
      exact eq_neg_of_add_eq_zero_left hcancel
    -- assemble the wedge
    have hp2ne : ∀ p : Pairs (m + 1), p.1.2 ≠ 0 := fun p =>
      Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) p.2)
    refine ⟨fun p =>
      if h0 : p.1.1 = 0 then e.symm (Q (p.1.2.pred (hp2ne p)))
      else e.symm (Polynomial.C (w ⟨(p.1.1.pred h0, p.1.2.pred (hp2ne p)),
        (Fin.pred_lt_pred_iff (ha := h0) (hb := hp2ne p)).mpr p.2⟩)), ?_⟩
    funext j
    refine Fin.cases ?_ ?_ j
    · -- component 0: `-∑ₖ v₀ₖ Xₖ = u 0` is exactly the `y`-cofactor identity `hU0`
      unfold d2
      simp only [Fin.not_lt_zero, Fin.sum_univ_succ, lt_irrefl, Fin.succ_pos, dif_pos,
        Fin.pred_succ]
      simp only [dif_neg not_false, Finset.sum_const_zero, zero_add, zero_sub]
      have hU0' : e (u 0) = -∑ i : Fin m, Q i * Polynomial.C (X i) := hU0
      apply e.injective
      rw [map_neg, map_sum, hU0', neg_inj]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_mul, AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_succ]
    · -- component `j.succ`: the `divX` decomposition plus the IH wedge
      intro j
      unfold d2
      simp only [Fin.sum_univ_succ, Fin.succ_pos, dif_pos, Fin.not_lt_zero,
        Fin.succ_lt_succ_iff, Fin.succ_ne_zero, Fin.pred_succ]
      apply e.injective
      have hUj : e (u j.succ) = Polynomial.X * Q j +
          Polynomial.C (d2 (fun i => (X i : MvPolynomial (Fin m) D)) w j) := by
        rw [hw]
        exact hdecomp j
      rw [hUj]
      unfold d2
      have heX0 : e (X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
      have heXs : ∀ i : Fin m, e (X i.succ) = Polynomial.C (X i) := fun i =>
        MvPolynomial.finSuccEquiv_X_succ
      simp only [dif_neg not_false, zero_add, map_sub, map_add, map_sum, map_mul,
        AlgEquiv.apply_symm_apply, apply_dite e, apply_dite Polynomial.C, map_zero, heX0,
        heXs]
      ring

end Polynomial

/-! ### Coefficientwise maps of restricted rings (used here and in the localization layer) -/

section MapHom

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {n : ℕ}

/-- Coefficientwise application of a norm-nonincreasing ring homomorphism to restricted
multivariate power series ([FJP] Lemma 4.1's ambient maps). -/
noncomputable def mapRestricted (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (c : Fin n → ℝ) :
    MvPowerSeries.Restricted R c →+* MvPowerSeries.Restricted S c where
  toFun f := ⟨MvPowerSeries.map φ f.1, by sorry⟩
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

theorem norm_mapRestricted_le (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (c : Fin n → ℝ)
    [StrongPos c] (f : MvPowerSeries.Restricted R c) :
    ‖mapRestricted φ hφ c f‖ ≤ ‖f‖ := by sorry

end MapHom

/-! ### Restricted level over an affinoid vertex

Statements are parametrised over a normed vertex `E` with a noetherian unit ball and a
noetherian restricted extension; instantiated at `E ∈ {𝓑, 𝓒, 𝓓}` via
`FiniteJetNoetherianVertices.lean`. `P := E⟨T₁,…,T_m⟩` is the vendored radius-one restricted
ring. -/

/-- `P_E = E⟨T₁,…,T_m⟩`. -/
abbrev P (E : Type*) [NormedCommRing E] [IsUltrametricDist E] (m : ℕ) : Type _ :=
  MvPowerSeries.Restricted E (fun _ : Fin m => (1 : ℝ))

section Restricted

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}

/-- The scalar embedding `MvPolynomial → P_E` ([FJP] (4.4)'s dense polynomial subring). -/
noncomputable def polyToP : MvPolynomial (Fin m) E →+* P E m := by sorry

/-- The base change `E[T] → E⟨T⟩` is **flat** ([FJP] Lemma 4.2, proof: "Noetherian adic
completion is flat [8, Lemma 10.97.2, Tag 00MB], and localization preserves flatness";
via the (4.4) identification `P_E ≅ (E₀[T])^∧_ϖ[1/ϖ]` for the noetherian unit ball `E₀`). -/
theorem flat_polyToP (hE₀ : IsNoetherianRing (unitBall E)) :
    letI : Algebra (MvPolynomial (Fin m) E) (P E m) := (polyToP (E := E) (m := m)).toAlgebra
    Module.Flat (MvPolynomial (Fin m) E) (P E m) := by sorry

/-- Graph-sequence syzygies over `P_E = E⟨T⟩` are Koszul-generated **algebraically**
([FJP] Lemma 4.2: positive-degree exactness transfers along the flat base change; degree-1
form). -/
theorem syzygy_graph_restricted (hE₀ : IsNoetherianRing (unitBall E))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (u : Fin m → P E m) (h : d1 r u = 0) :
    ∃ v, d2 r v = u := by sorry

/-- The graph ideal `I_E = im(d₁) ⊂ P_E` is **closed** ([FJP] Lemma 4.2: "every
differential has closed image … In particular `I_D = im(d₁) ⊂ P_D` is closed"; via the
noetherian finite-module theory of `NoetherianTateModules.lean`). Requires `P_E`
noetherian (strong noetherianity of the vertex). -/
theorem isClosed_graphIdeal [IsNoetherianRing (P E m)]
    (r : Fin m → P E m) :
    IsClosed ((Ideal.span (Set.range r) : Set (P E m))) := by sorry

/-- Strictness of `d₁` with an explicit constant ([FJP] (4.7): "an element `x ∈ I_E` has a
representative `u ∈ P_E^m` with `d_{1,E}(u) = x`, `‖u‖ ≤ h_E ‖x‖`"; from closedness + the
Banach open mapping theorem with constants). -/
theorem exists_d1_lift [IsNoetherianRing (P E m)] (r : Fin m → P E m) :
    ∃ h : ℝ, 1 ≤ h ∧ ∀ x ∈ Ideal.span (Set.range r),
      ∃ u : Fin m → P E m, d1 r u = x ∧ ‖u‖ ≤ h * ‖x‖ := by sorry

/-- Strictness of `d₂` onto `ker d₁` with an explicit constant ([FJP] (4.8): "every
`s ∈ ker(d_{1,D})` has `v ∈ ⋀² P_D^m` satisfying `d_{2,D}(v) = s`, `‖v‖ ≤ z_D ‖s‖`").
For `m = 1` the conclusion forces `ker d₁ = 0` (`Pairs 1` is empty), which holds because
`gT − f` is a nonzerodivisor. -/
theorem exists_d2_lift [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) :
    ∃ z : ℝ, 1 ≤ z ∧ ∀ u : Fin m → P E m, d1 r u = 0 →
      ∃ v : Pairs m → P E m, d2 r v = u ∧ ‖v‖ ≤ z * ‖u‖ := by sorry

end Restricted

end GraphKoszul

end FiniteJet
