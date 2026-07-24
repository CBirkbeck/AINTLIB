/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.YSpace

/-!
# The adic Fargues--Fontaine curve 𝒳 = 𝒴/φ^ℤ

We define the adic Fargues--Fontaine curve (for `E = Q_p` and a perfectoid base field
`F` of characteristic `p`) as the quotient of `𝒴` by the `φ^ℤ`-action, and prove the
point-set theorems that make the quotient well-behaved:

* the action on `𝒴` is **free** (`smul_ne_of_ne_zero`) — a corollary of the window
  covering, translation, and disjointness;
* the action is **wandering** (`exists_nhd_smul_disjoint`): every point has an open
  neighbourhood moved off itself by every `φ^k`, `k ≠ 0` — this is the precise content
  of "properly discontinuous" used by the sources;
* the quotient map is an **open quotient map**, is **injective on each window**, and the
  images of `U_0` and `V_0` **cover** the curve;
* the curve is **T0** and (given window quasicompactness) **quasicompact**.

## The definition

`Curve p F ϖ := ↥(Y p F ϖ) / orbitRel (Multiplicative ℤ)`.

Source: [BFHHLWY][bfhhlwy2018], Definition 2.1.1: "The (mixed-characteristic) adic
Fargues-Fontaine curve 𝒳_{E,F} is 𝒳_{E,F} = 𝒴_{E,F}/φ^ℤ." (specialised to `E = Q_p`);
[Scholze–Weinstein][sw2020], Definition 13.5.1: "The adic Fargues-Fontaine curve is the
quotient 𝒳_FF = 𝒴_(0,∞)/φ^ℤ", justified by "As φ acts properly discontinuously on
𝒴_(0,∞) (as follows from κ∘φ = pκ), it makes sense to form the quotient";
[Kedlaya-AWS][kedlaya-aws], §3.1: "The action of φ on Y_S is properly discontinuous. The
quotient space X_S := Y_S/φ^ℤ ... is the adic (relative) Fargues–Fontaine curve", and
Remark 3.1.9: "The spaces U_0 and V_0 map isomorphically to their images in X_S and
cover the latter. In particular, X_S can be covered by two affinoid subspaces."
-/

open TopologicalRing ValuationSpectrum Pointwise

universe u

attribute [local instance] IsLinearTopology.nonarchimedeanAddGroup

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [IsLinearTopology F F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-! ### Freeness and wandering -/

variable {p F ϖ}

/-- **Freeness of the `φ^ℤ`-action on 𝒴**: no nontrivial power of Frobenius fixes a
point of `𝒴`.

Proof plan (corollary of the window machinery, no separate value-group argument): by the
covering, `v` lies in some `U_n` (or `V_n`); the translation lemma puts `φ^k·v` in
`U_{n-k}` (resp. `V_{n-k}`), and within-family disjointness for `k ≠ 0` forbids
`φ^k·v = v`.

Source: [Kedlaya-AWS, Rem. 3.1.9] ("The action of φ permutes the U_n ... hence is
properly discontinuous"); [SW, Def. 13.5.1] (the quotient is legitimate). -/
theorem smul_ne_of_ne_zero {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {k : ℤ}
    (hk : k ≠ 0) : (Multiplicative.ofAdd k) • v ≠ v := by sorry

/-- **The wandering property** ("properly discontinuous" in the sources): every point of
`𝒴` has an open neighbourhood `W ⊆ 𝒴` with `φ^k·W ∩ W = ∅` for all `k ≠ 0` — namely its
window.

Source: [Kedlaya-AWS, Rem. 3.1.9]; [SW, Def. 13.5.1]. -/
theorem exists_nhd_smul_disjoint {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) :
    ∃ W : Set (Spv (Ainf p F)),
      v ∈ W ∧ W ⊆ Y p F ϖ ∧
      IsOpen (Subtype.val ⁻¹' W : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) ∧
      ∀ k : ℤ, k ≠ 0 → Disjoint ((Multiplicative.ofAdd k) • W) W := by sorry

/-! ### The action on the subtype ↥𝒴 -/

variable (p F ϖ)

/-- The `φ^ℤ`-action restricted to the subtype `↥𝒴` (well-defined by `smul_mem_Y`). -/
instance instMulActionYSub : MulAction (Multiplicative ℤ) ↥(Y p F ϖ) where
  smul g v := ⟨g • v.1, smul_mem_Y p F ϖ g v.2⟩
  one_smul v := by sorry
  mul_smul g h v := by sorry

/-- The restricted action is by homeomorphisms of `↥𝒴` (subspace topology from
`Spv(A_inf)`). -/
instance instContinuousConstSMulYSub :
    ContinuousConstSMul (Multiplicative ℤ) ↥(Y p F ϖ) := by sorry

/-! ### The curve -/

/-- **The adic Fargues--Fontaine curve** `𝒳 = 𝒴/φ^ℤ` (as a topological space; the
structure presheaf is a follow-on development).

Source: [BFHHLWY, Def 2.1.1]: "𝒳_{E,F} = 𝒴_{E,F}/φ^ℤ" (`E = Q_p`);
[SW, Def 13.5.1]; [Kedlaya-AWS, §3.1]. -/
def Curve : Type u :=
  Quotient (MulAction.orbitRel (Multiplicative ℤ) ↥(Y p F ϖ))

instance instTopologicalSpaceCurve : TopologicalSpace (Curve p F ϖ) :=
  instTopologicalSpaceQuotient

/-- The quotient map `𝒴 → 𝒳`. -/
def toCurve : ↥(Y p F ϖ) → Curve p F ϖ :=
  Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) ↥(Y p F ϖ))

theorem toCurve_surjective : Function.Surjective (toCurve p F ϖ) := by sorry

/-- The quotient map `𝒴 → 𝒳` is an open quotient map (orbit maps of continuous group
actions are open quotient maps). -/
theorem isOpenQuotientMap_toCurve : IsOpenQuotientMap (toCurve p F ϖ) := by sorry

/-- The quotient map is injective on each window `U_n`: two points of a window in the
same `φ^ℤ`-orbit are equal (wandering + freeness).

Source: [Kedlaya-AWS, Rem. 3.1.9]: "The spaces U_0 and V_0 map isomorphically to their
images in X_S". -/
theorem injOn_toCurve_windowU (n : ℤ) :
    Set.InjOn (toCurve p F ϖ)
      {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ n} := by sorry

/-- The quotient map is injective on each window `V_n`. -/
theorem injOn_toCurve_windowV (n : ℤ) :
    Set.InjOn (toCurve p F ϖ)
      {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ n} := by sorry

/-- **Two charts cover the curve**: `𝒳 = im(U_0) ∪ im(V_0)`. Every `φ^ℤ`-orbit meets
`U_0 ∪ V_0`, by the covering and the translation lemmas.

Source: [Kedlaya-AWS, Rem. 3.1.9]: "The spaces U_0 and V_0 map isomorphically to their
images in X_S and cover the latter." -/
theorem curve_eq_image_window_zero :
    toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0} ∪
      toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0} =
      Set.univ := by sorry

/-- The curve is T0 (as the sources' adic spaces are; here proved directly from the
quotient structure and T0-ness of `Spa`). -/
instance instT0SpaceCurve : T0Space (Curve p F ϖ) := by sorry

/-- Quasicompactness of the closed-window hull: each window is contained in a
quasicompact subset of `Spa(A_inf, A_inf)` cut out by the two `vle`-inequalities and the
nonvanishing conditions (a rational-subset-shaped set, quasicompact by the Boolean
product-embedding machinery of `SpaCompact`/`ValuationSpectrumCompact`). -/
theorem isCompact_windowU_zero :
    IsCompact (Subtype.val ⁻¹' windowU p F ϖ 0 :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by sorry

/-- Quasicompactness for `V_0`, as for `U_0`. -/
theorem isCompact_windowV_zero :
    IsCompact (Subtype.val ⁻¹' windowV p F ϖ 0 :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by sorry

/-- **The curve is quasicompact**: it is the union of the images of the two
quasicompact charts `U_0`, `V_0`.

Source: [Kedlaya-AWS, Rem. 3.1.9]: "In particular, X_S can be covered by two affinoid
subspaces". -/
instance instCompactSpaceCurve : CompactSpace (Curve p F ϖ) := by sorry

/-- STRETCH GOAL — **the curve is nonempty** (equivalently `𝒴 ≠ ∅`). Planned route: the
ρ-Gauss norm `v(Σ p^n [a_n]) = max_n |a_n|·ρ^n` (for `|·|` the rank-1 valuation of `F`
and any `ρ ∈ (0,1)`) is a continuous multiplicative valuation on `A_inf` with
`v(p) = ρ ≠ 0` and `v([ϖ]) = |ϖ| ≠ 0`; multiplicativity is the real content
(Fargues–Fontaine, *Courbes et fibrés vectoriels*, §1.4). -/
theorem Y_nonempty : (Y p F ϖ).Nonempty := by sorry

end FarguesFontaine

end
