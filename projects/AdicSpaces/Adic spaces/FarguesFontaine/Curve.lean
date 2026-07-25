/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.GaussPoint
import «Adic spaces».FarguesFontaine.YSpace
import «Adic spaces».SpaQCviaSpvAI

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


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
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
    (hk : k ≠ 0) : (Multiplicative.ofAdd k) • v ≠ v := by
  intro heq
  have hv' := hv
  rw [Y_eq_iUnion_windows] at hv'
  rcases hv' with hU | hV
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hU
    have h2 : v ∈ windowU p F ϖ (n - k) := by
      rw [← zsmul_windowU p F ϖ k n]
      exact heq ▸ Set.smul_mem_smul_set hn
    exact Set.disjoint_left.mp (windowU_disjoint p F ϖ (by omega : n ≠ n - k)) hn h2
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hV
    have h2 : v ∈ windowV p F ϖ (n - k) := by
      rw [← zsmul_windowV p F ϖ k n]
      exact heq ▸ Set.smul_mem_smul_set hn
    exact Set.disjoint_left.mp (windowV_disjoint p F ϖ (by omega : n ≠ n - k)) hn h2

/-- **The wandering property** ("properly discontinuous" in the sources): every point of
`𝒴` has an open neighbourhood `W ⊆ 𝒴` with `φ^k·W ∩ W = ∅` for all `k ≠ 0` — namely its
window.

Source: [Kedlaya-AWS, Rem. 3.1.9]; [SW, Def. 13.5.1]. -/
theorem exists_nhd_smul_disjoint {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) :
    ∃ W : Set (Spv (Ainf p F)),
      v ∈ W ∧ W ⊆ Y p F ϖ ∧
      IsOpen (Subtype.val ⁻¹' W : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) ∧
      ∀ k : ℤ, k ≠ 0 → Disjoint ((Multiplicative.ofAdd k) • W) W := by
  have hv' := hv
  rw [Y_eq_iUnion_windows] at hv'
  rcases hv' with hU | hV
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hU
    refine ⟨windowU p F ϖ n, hn, fun w hw => hw.1, isOpen_windowU p F ϖ n,
      fun k hk => ?_⟩
    rw [zsmul_windowU]
    exact windowU_disjoint p F ϖ (by omega)
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hV
    refine ⟨windowV p F ϖ n, hn, fun w hw => hw.1, isOpen_windowV p F ϖ n,
      fun k hk => ?_⟩
    rw [zsmul_windowV]
    exact windowV_disjoint p F ϖ (by omega)

/-! ### The action on the subtype ↥𝒴 -/

variable (p F ϖ)

/-- The `φ^ℤ`-action on `Spv(A_inf)` is by homeomorphisms: `g • v = comap (φ^{-g}) v`
and `comap` of a ring homomorphism is continuous. -/
instance instContinuousConstSMulSpv :
    ContinuousConstSMul (Multiplicative ℤ) (Spv (Ainf p F)) := by
  refine ⟨fun g => ?_⟩
  show Continuous fun v : Spv (Ainf p F) =>
    comap (MulSemiringAction.toRingHom _ _ g⁻¹) v
  exact comap_continuous _

/-- The `φ^ℤ`-action restricted to the subtype `↥𝒴` (well-defined by `smul_mem_Y`). -/
instance instMulActionYSub : MulAction (Multiplicative ℤ) ↥(Y p F ϖ) where
  smul g v := ⟨g • v.1, smul_mem_Y p F ϖ g v.2⟩
  one_smul v := Subtype.ext (one_smul _ v.1)
  mul_smul g h v := Subtype.ext (mul_smul g h v.1)

/-- The restricted action is by homeomorphisms of `↥𝒴` (subspace topology from
`Spv(A_inf)`). -/
instance instContinuousConstSMulYSub :
    ContinuousConstSMul (Multiplicative ℤ) ↥(Y p F ϖ) :=
  ⟨fun g => Continuous.subtype_mk
    ((continuous_const_smul g).comp continuous_subtype_val) _⟩

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

theorem toCurve_surjective : Function.Surjective (toCurve p F ϖ) :=
  fun c => ⟨c.out, Quotient.out_eq c⟩

/-- The quotient map `𝒴 → 𝒳` is an open quotient map (orbit maps of continuous group
actions are open quotient maps). -/
theorem isOpenQuotientMap_toCurve : IsOpenQuotientMap (toCurve p F ϖ) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The quotient map is injective on each window `U_n`: two points of a window in the
same `φ^ℤ`-orbit are equal (wandering + freeness).

Source: [Kedlaya-AWS, Rem. 3.1.9]: "The spaces U_0 and V_0 map isomorphically to their
images in X_S". -/
theorem injOn_toCurve_windowU (n : ℤ) :
    Set.InjOn (toCurve p F ϖ)
      {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ n} := by
  intro y₁ h₁ y₂ h₂ heq
  have hrel : y₁ ∈ MulAction.orbit (Multiplicative ℤ) y₂ :=
    MulAction.orbitRel_apply.mp (Quotient.eq''.mp heq)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
  by_cases hk : Multiplicative.toAdd g = 0
  · have hg1 : g = 1 := by
      rw [← ofAdd_toAdd g, hk]
      rfl
    rw [hg1, one_smul] at hg
    exact hg.symm
  · exfalso
    have h3 : (y₁.1 : Spv (Ainf p F)) ∈ windowU p F ϖ (n - Multiplicative.toAdd g) := by
      rw [← zsmul_windowU p F ϖ (Multiplicative.toAdd g) n]
      exact ⟨y₂.1, h₂, by rw [ofAdd_toAdd]; exact congrArg Subtype.val hg⟩
    exact Set.disjoint_left.mp (windowU_disjoint p F ϖ (by omega)) h₁ h3

/-- The quotient map is injective on each window `V_n`. -/
theorem injOn_toCurve_windowV (n : ℤ) :
    Set.InjOn (toCurve p F ϖ)
      {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ n} := by
  intro y₁ h₁ y₂ h₂ heq
  have hrel : y₁ ∈ MulAction.orbit (Multiplicative ℤ) y₂ :=
    MulAction.orbitRel_apply.mp (Quotient.eq''.mp heq)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
  by_cases hk : Multiplicative.toAdd g = 0
  · have hg1 : g = 1 := by
      rw [← ofAdd_toAdd g, hk]
      rfl
    rw [hg1, one_smul] at hg
    exact hg.symm
  · exfalso
    have h3 : (y₁.1 : Spv (Ainf p F)) ∈ windowV p F ϖ (n - Multiplicative.toAdd g) := by
      rw [← zsmul_windowV p F ϖ (Multiplicative.toAdd g) n]
      exact ⟨y₂.1, h₂, by rw [ofAdd_toAdd]; exact congrArg Subtype.val hg⟩
    exact Set.disjoint_left.mp (windowV_disjoint p F ϖ (by omega)) h₁ h3

/-- **Two charts cover the curve**: `𝒳 = im(U_0) ∪ im(V_0)`. Every `φ^ℤ`-orbit meets
`U_0 ∪ V_0`, by the covering and the translation lemmas.

Source: [Kedlaya-AWS, Rem. 3.1.9]: "The spaces U_0 and V_0 map isomorphically to their
images in X_S and cover the latter." -/
theorem curve_eq_image_window_zero :
    toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0} ∪
      toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0} =
      Set.univ := by
  refine Set.eq_univ_of_forall (fun c => ?_)
  obtain ⟨y, rfl⟩ := toCurve_surjective p F ϖ c
  have hy : (y.1 : Spv (Ainf p F)) ∈
      (⋃ n : ℤ, windowU p F ϖ n) ∪ ⋃ n : ℤ, windowV p F ϖ n := by
    rw [← Y_eq_iUnion_windows]
    exact y.2
  have horbit : ∀ (n : ℤ) (z : ↥(Y p F ϖ)),
      toCurve p F ϖ ((Multiplicative.ofAdd n) • z) = toCurve p F ϖ z := by
    intro n z
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit z _))
  rcases hy with hU | hV
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hU
    refine Or.inl ⟨(Multiplicative.ofAdd n) • y, ?_, horbit n y⟩
    show (((Multiplicative.ofAdd n) • y).1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0
    have : (((Multiplicative.ofAdd n) • y).1 : Spv (Ainf p F))
        ∈ windowU p F ϖ (n - n) := by
      rw [← zsmul_windowU p F ϖ n n]
      exact ⟨y.1, hn, rfl⟩
    simpa using this
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hV
    refine Or.inr ⟨(Multiplicative.ofAdd n) • y, ?_, horbit n y⟩
    show (((Multiplicative.ofAdd n) • y).1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0
    have : (((Multiplicative.ofAdd n) • y).1 : Spv (Ainf p F))
        ∈ windowV p F ϖ (n - n) := by
      rw [← zsmul_windowV p F ϖ n n]
      exact ⟨y.1, hn, rfl⟩
    simpa using this

private theorem not_vle_pow_p_zero' {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) (k : ℕ) :
    ¬ v.vle ((p : Ainf p F) ^ k) 0 := fun h =>
  v_p_ne_zero hv ((v.mem_supp_iff _).mp
    ((inferInstance : (v.supp).IsPrime).mem_of_pow_mem _ ((v.mem_supp_iff _).mpr h)))

private theorem not_vle_pow_teichPi_zero' {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ)
    (k : ℕ) : ¬ v.vle (teichPi p F ϖ ^ k) 0 := fun h =>
  v_teichPi_ne_zero hv ((v.mem_supp_iff _).mp
    ((inferInstance : (v.supp).IsPrime).mem_of_pow_mem _ ((v.mem_supp_iff _).mpr h)))

private theorem isOpen_windowU_Y (n : ℤ) :
    IsOpen {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ n} := by
  have heq : {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ n} =
      (Subtype.val ⁻¹' basicOpen (teichPi p F ϖ ^ ((p : ℚ) ^ n : ℚ).den)
          ((p : Ainf p F) ^ ((p : ℚ) ^ n : ℚ).num.toNat)) ∩
        (Subtype.val ⁻¹' basicOpen ((p : Ainf p F) ^ (cFF p * (p : ℚ) ^ n).num.toNat)
          (teichPi p F ϖ ^ (cFF p * (p : ℚ) ^ n).den)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, windowU,
      basicOpen, KGE, KLE]
    exact ⟨fun ⟨_, h1, h2⟩ =>
        ⟨⟨h1, not_vle_pow_p_zero' p F ϖ y.2 _⟩, ⟨h2, not_vle_pow_teichPi_zero' p F ϖ y.2 _⟩⟩,
      fun ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ => ⟨y.2, h1, h2⟩⟩
  rw [heq]
  exact (continuous_subtype_val.isOpen_preimage _ (isOpen_basicOpen _ _)).inter
    (continuous_subtype_val.isOpen_preimage _ (isOpen_basicOpen _ _))

private theorem isOpen_windowV_Y (n : ℤ) :
    IsOpen {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ n} := by
  have heq : {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ n} =
      (Subtype.val ⁻¹' basicOpen (teichPi p F ϖ ^ (cFF p * (p : ℚ) ^ n).den)
          ((p : Ainf p F) ^ (cFF p * (p : ℚ) ^ n).num.toNat)) ∩
        (Subtype.val ⁻¹' basicOpen ((p : Ainf p F) ^ ((p : ℚ) ^ (n + 1) : ℚ).num.toNat)
          (teichPi p F ϖ ^ ((p : ℚ) ^ (n + 1) : ℚ).den)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, windowV,
      basicOpen, KGE, KLE]
    exact ⟨fun ⟨_, h1, h2⟩ =>
        ⟨⟨h1, not_vle_pow_p_zero' p F ϖ y.2 _⟩, ⟨h2, not_vle_pow_teichPi_zero' p F ϖ y.2 _⟩⟩,
      fun ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ => ⟨y.2, h1, h2⟩⟩
  rw [heq]
  exact (continuous_subtype_val.isOpen_preimage _ (isOpen_basicOpen _ _)).inter
    (continuous_subtype_val.isOpen_preimage _ (isOpen_basicOpen _ _))

private theorem sep_of_chart {S : Set ↥(Y p F ϖ)} (hSopen : IsOpen S)
    (hinj : Set.InjOn (toCurve p F ϖ) S) {z₁ z₂ : ↥(Y p F ϖ)} (h₁ : z₁ ∈ S)
    (h₂ : z₂ ∈ S) (hne : toCurve p F ϖ z₁ ≠ toCurve p F ϖ z₂) :
    ∃ C : Set (Curve p F ϖ), IsOpen C ∧
      Xor (toCurve p F ϖ z₁ ∈ C) (toCurve p F ϖ z₂ ∈ C) := by
  have hzne : z₁ ≠ z₂ := fun h => hne (congrArg _ h)
  obtain ⟨O, hOopen, hxor⟩ :=
    ((t0Space_iff_exists_isOpen_xor_mem _).mp inferInstance) hzne
  rcases hxor with ⟨hz₁O, hz₂O⟩ | ⟨hz₂O, hz₁O⟩
  · refine ⟨toCurve p F ϖ '' (S ∩ O),
      (isOpenQuotientMap_toCurve p F ϖ).isOpenMap _ (hSopen.inter hOopen),
      Or.inl ⟨⟨z₁, ⟨h₁, hz₁O⟩, rfl⟩, ?_⟩⟩
    rintro ⟨w, ⟨hwS, hwO⟩, hweq⟩
    exact hz₂O ((hinj hwS h₂ hweq) ▸ hwO)
  · refine ⟨toCurve p F ϖ '' (S ∩ O),
      (isOpenQuotientMap_toCurve p F ϖ).isOpenMap _ (hSopen.inter hOopen),
      Or.inr ⟨⟨z₂, ⟨h₂, hz₂O⟩, rfl⟩, ?_⟩⟩
    rintro ⟨w, ⟨hwS, hwO⟩, hweq⟩
    exact hz₁O ((hinj hwS h₁ hweq) ▸ hwO)

/-- The curve is T0 (as the sources' adic spaces are; here proved directly from the
quotient structure and T0-ness of `Spa`). -/
instance instT0SpaceCurve : T0Space (Curve p F ϖ) := by
  rw [t0Space_iff_exists_isOpen_xor_mem]
  intro c₁ c₂ hne
  have h1 := Set.eq_univ_iff_forall.mp (curve_eq_image_window_zero p F ϖ) c₁
  have h2 := Set.eq_univ_iff_forall.mp (curve_eq_image_window_zero p F ϖ) c₂
  have hUopen : IsOpen (toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0}) :=
    (isOpenQuotientMap_toCurve p F ϖ).isOpenMap _ (isOpen_windowU_Y p F ϖ 0)
  by_cases hU₁ : c₁ ∈ toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0}
  · by_cases hU₂ : c₂ ∈ toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0}
    · obtain ⟨z₁, hz₁, rfl⟩ := hU₁
      obtain ⟨z₂, hz₂, rfl⟩ := hU₂
      exact sep_of_chart p F ϖ (isOpen_windowU_Y p F ϖ 0)
        (injOn_toCurve_windowU p F ϖ 0) hz₁ hz₂ hne
    · exact ⟨_, hUopen, Or.inl ⟨hU₁, hU₂⟩⟩
  · by_cases hU₂ : c₂ ∈ toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0}
    · exact ⟨_, hUopen, Or.inr ⟨hU₂, hU₁⟩⟩
    · obtain ⟨z₁, hz₁, rfl⟩ := h1.resolve_left hU₁
      obtain ⟨z₂, hz₂, rfl⟩ := h2.resolve_left hU₂
      exact sep_of_chart p F ϖ (isOpen_windowV_Y p F ϖ 0)
        (injOn_toCurve_windowV p F ϖ 0) hz₁ hz₂ hne

open Classical in
/-- The generic two-condition-to-rational-subset engine (Wedhorn Rem. 7.30(5)): on
`Spa`, the conjunction `v(t₁) ≤ v(s₁) ≠ 0 ∧ v(t₂) ≤ v(s₂) ≠ 0` equals membership in
`rationalOpen {t₁t₂, t₁s₂, s₁t₂, s₁s₂} (s₁s₂)`. -/
private theorem mem_rationalOpen_pair_iff {v : Spv (Ainf p F)}
    (hv : v ∈ Spa (Ainf p F) (ringPlus (Ainf p F))) {t₁ s₁ t₂ s₂ : Ainf p F} :
    v ∈ rationalOpen {t₁ * t₂, t₁ * s₂, s₁ * t₂, s₁ * s₂} (s₁ * s₂) ↔
      (v.vle t₁ s₁ ∧ ¬ v.vle s₁ 0) ∧ (v.vle t₂ s₂ ∧ ¬ v.vle s₂ 0) := by
  have hprime : (v.supp).IsPrime := inferInstance
  constructor
  · rintro ⟨-, hT, hs⟩
    have hs₁ : ¬ v.vle s₁ 0 := fun h0 => hs (by
      have := v.mul_vle_mul_left h0 s₂
      rwa [zero_mul] at this)
    have hs₂ : ¬ v.vle s₂ 0 := fun h0 => hs (by
      have := v.mul_vle_mul_left h0 s₁
      rwa [zero_mul, mul_comm] at this)
    refine ⟨⟨?_, hs₁⟩, ⟨?_, hs₂⟩⟩
    · have h12 : v.vle (t₁ * s₂) (s₁ * s₂) := hT _ (by simp)
      exact v.vle_mul_cancel hs₂ h12
    · have h12 : v.vle (s₁ * t₂) (s₁ * s₂) := hT _ (by simp)
      have h12' : v.vle (t₂ * s₁) (s₂ * s₁) := by
        rwa [mul_comm t₂ s₁, mul_comm s₂ s₁]
      exact v.vle_mul_cancel hs₁ h12'
  · rintro ⟨⟨h₁, hs₁⟩, ⟨h₂, hs₂⟩⟩
    have hmul : ∀ {x y : Ainf p F}, v.vle x s₁ → v.vle y s₂ →
        v.vle (x * y) (s₁ * s₂) := by
      intro x y hx hy
      refine v.vle_trans (v.mul_vle_mul_left hx y) ?_
      have := v.mul_vle_mul_left hy s₁
      rwa [mul_comm y s₁, mul_comm s₂ s₁] at this
    have hrefl₁ : v.vle s₁ s₁ := (v.vle_total s₁ s₁).elim id id
    have hrefl₂ : v.vle s₂ s₂ := (v.vle_total s₂ s₂).elim id id
    refine ⟨hv, fun t ht => ?_, fun h0 => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hmul h₁ h₂
      · exact hmul h₁ hrefl₂
      · exact hmul hrefl₁ h₂
      · exact hmul hrefl₁ hrefl₂
    · rcases hprime.mem_or_mem ((v.mem_supp_iff _).mpr h0) with hm | hm
      · exact hs₁ ((v.mem_supp_iff _).mp hm)
      · exact hs₂ ((v.mem_supp_iff _).mp hm)

private theorem cFF_num_toNat_pos : 0 < (cFF p).num.toNat := by
  have h1 : 0 < cFF p :=
    zero_lt_one.trans (one_lt_cFF (Fact.out : Nat.Prime p).one_lt)
  have h2 : 0 < (cFF p).num := Rat.num_pos.mpr h1
  omega

open Classical in
private theorem windowU_zero_trace_eq :
    (Subtype.val ⁻¹' windowU p F ϖ 0 :
        Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) =
      Subtype.val ⁻¹' rationalOpen
        {teichPi p F ϖ * (p : Ainf p F) ^ (cFF p).num.toNat,
         teichPi p F ϖ * teichPi p F ϖ ^ (cFF p).den,
         (p : Ainf p F) * (p : Ainf p F) ^ (cFF p).num.toNat,
         (p : Ainf p F) * teichPi p F ϖ ^ (cFF p).den}
        ((p : Ainf p F) * teichPi p F ϖ ^ (cFF p).den) := by
  ext v
  simp only [Set.mem_preimage]
  rw [mem_rationalOpen_pair_iff p F v.2]
  have hKGE : KGE p F ϖ ((p : ℚ) ^ (0 : ℤ)) (v : Spv (Ainf p F)) ↔
      (v : Spv (Ainf p F)).vle (teichPi p F ϖ) ((p : Ainf p F)) := by
    rw [show ((p : ℚ) ^ (0 : ℤ)) = 1 from zpow_zero _, KGE, Rat.den_one, Rat.num_one,
      Int.toNat_one, pow_one, pow_one]
  have hKLE : KLE p F ϖ (cFF p * (p : ℚ) ^ (0 : ℤ)) (v : Spv (Ainf p F)) ↔
      (v : Spv (Ainf p F)).vle ((p : Ainf p F) ^ (cFF p).num.toNat)
        (teichPi p F ϖ ^ (cFF p).den) := by
    rw [show cFF p * (p : ℚ) ^ (0 : ℤ) = cFF p from by rw [zpow_zero, mul_one], KLE]
  constructor
  · rintro ⟨hY, hge, hle⟩
    exact ⟨⟨hKGE.mp hge, fun h0 => v_p_ne_zero hY h0⟩,
      ⟨hKLE.mp hle, fun h0 => not_vle_pow_teichPi_zero' p F ϖ hY _ h0⟩⟩
  · rintro ⟨⟨h₁, hs₁⟩, ⟨h₂, hs₂⟩⟩
    have hprime : ((v : Spv (Ainf p F)).supp).IsPrime := inferInstance
    have hY : (v : Spv (Ainf p F)) ∈ Y p F ϖ := by
      refine ⟨v.2, fun h0 => ?_⟩
      rcases hprime.mem_or_mem
          (((v : Spv (Ainf p F)).mem_supp_iff _).mpr h0) with hm | hm
      · exact hs₁ (((v : Spv (Ainf p F)).mem_supp_iff _).mp hm)
      · exact hs₂ (((v : Spv (Ainf p F)).mem_supp_iff _).mp
          (Ideal.pow_mem_of_mem _ hm _ (cFF p).den_pos))
    exact ⟨hY, hKGE.mpr h₁, hKLE.mpr h₂⟩

open Classical in
private theorem windowV_zero_trace_eq :
    (Subtype.val ⁻¹' windowV p F ϖ 0 :
        Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) =
      Subtype.val ⁻¹' rationalOpen
        {teichPi p F ϖ ^ (cFF p).den * (p : Ainf p F) ^ ((p : ℚ)).num.toNat,
         teichPi p F ϖ ^ (cFF p).den * teichPi p F ϖ ^ ((p : ℚ)).den,
         (p : Ainf p F) ^ (cFF p).num.toNat * (p : Ainf p F) ^ ((p : ℚ)).num.toNat,
         (p : Ainf p F) ^ (cFF p).num.toNat * teichPi p F ϖ ^ ((p : ℚ)).den}
        ((p : Ainf p F) ^ (cFF p).num.toNat * teichPi p F ϖ ^ ((p : ℚ)).den) := by
  ext v
  simp only [Set.mem_preimage]
  rw [mem_rationalOpen_pair_iff p F v.2]
  have hKGE : KGE p F ϖ (cFF p * (p : ℚ) ^ (0 : ℤ)) (v : Spv (Ainf p F)) ↔
      (v : Spv (Ainf p F)).vle (teichPi p F ϖ ^ (cFF p).den)
        ((p : Ainf p F) ^ (cFF p).num.toNat) := by
    rw [show cFF p * (p : ℚ) ^ (0 : ℤ) = cFF p from by rw [zpow_zero, mul_one], KGE]
  have hKLE : KLE p F ϖ ((p : ℚ) ^ ((0 : ℤ) + 1)) (v : Spv (Ainf p F)) ↔
      (v : Spv (Ainf p F)).vle ((p : Ainf p F) ^ ((p : ℚ)).num.toNat)
        (teichPi p F ϖ ^ ((p : ℚ)).den) := by
    rw [show ((p : ℚ) ^ ((0 : ℤ) + 1)) = (p : ℚ) from by rw [zero_add, zpow_one], KLE]
  constructor
  · rintro ⟨hY, hge, hle⟩
    exact ⟨⟨hKGE.mp hge, fun h0 => not_vle_pow_p_zero' p F ϖ hY _ h0⟩,
      ⟨hKLE.mp hle, fun h0 => not_vle_pow_teichPi_zero' p F ϖ hY _ h0⟩⟩
  · rintro ⟨⟨h₁, hs₁⟩, ⟨h₂, hs₂⟩⟩
    have hprime : ((v : Spv (Ainf p F)).supp).IsPrime := inferInstance
    have hY : (v : Spv (Ainf p F)) ∈ Y p F ϖ := by
      refine ⟨v.2, fun h0 => ?_⟩
      rcases hprime.mem_or_mem
          (((v : Spv (Ainf p F)).mem_supp_iff _).mpr h0) with hm | hm
      · exact hs₁ (((v : Spv (Ainf p F)).mem_supp_iff _).mp
          (Ideal.pow_mem_of_mem _ hm _ (cFF_num_toNat_pos p)))
      · exact hs₂ (((v : Spv (Ainf p F)).mem_supp_iff _).mp
          (Ideal.pow_mem_of_mem _ hm _ (by
            rw [Rat.den_natCast]
            omega)))
    exact ⟨hY, hKGE.mpr h₁, hKLE.mpr h₂⟩

/-- Quasicompactness of the closed-window hull: each window is contained in a
quasicompact subset of `Spa(A_inf, A_inf)` cut out by the two `vle`-inequalities and the
nonvanishing conditions (a rational-subset-shaped set, quasicompact by the Boolean
product-embedding machinery of `SpaCompact`/`ValuationSpectrumCompact`). -/
private theorem ainf_pair_spec :
    ∃ P : PairOfDefinition (Ainf p F), ∃ g₁ g₂ : P.A₀,
      P.I = Ideal.span ({g₁, g₂} : Set P.A₀) ∧
      (∀ x : P.A₀, (x : Ainf p F) ∈ (ringPlus (Ainf p F) : Subring (Ainf p F))) ∧
      Iinf p F (IsTateRing.pseudoUniformizer (A := F)) =
        Ideal.span ({(g₁ : Ainf p F), (g₂ : Ainf p F)} : Set (Ainf p F)) := by
  refine ⟨pairOfDefinition_ofAdic (Iinf p F (IsTateRing.pseudoUniformizer (A := F)))
      (Submodule.fg_span (Set.toFinite _)),
    ⟨(p : Ainf p F), trivial⟩, ⟨teichPi p F (IsTateRing.pseudoUniformizer (A := F)),
      trivial⟩, ?_, fun _ => trivial, ?_⟩
  · show idealToTop (Iinf p F (IsTateRing.pseudoUniformizer (A := F))) = _
    rw [show idealToTop (Iinf p F (IsTateRing.pseudoUniformizer (A := F)))
        = Ideal.map (Subring.topEquiv (R := Ainf p F)).symm.toRingHom
          (Ideal.span {(p : Ainf p F),
            teichPi p F (IsTateRing.pseudoUniformizer (A := F))}) from rfl,
      Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  · rfl

private theorem iinf_le_radical_of_pure_powers {T : Finset (Ainf p F)}
    (hp : ∃ n : ℕ, (p : Ainf p F) ^ n ∈ T)
    (hϖ : ∃ m : ℕ, 0 < m ∧ teichPi p F ϖ ^ m ∈ T) :
    Iinf p F (IsTateRing.pseudoUniformizer (A := F)) ≤
      (Ideal.span (T : Set (Ainf p F))).radical := by
  rw [Iinf, Ideal.span_le]
  rintro x (rfl | rfl)
  · obtain ⟨n, hn⟩ := hp
    exact ⟨n, Ideal.subset_span hn⟩
  · obtain ⟨m, hm, hmem⟩ := hϖ
    obtain ⟨k, hk⟩ := exists_teichPi_pow_mem_span_teichPi p F ϖ
      (IsTateRing.pseudoUniformizer (A := F))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hk
    refine ⟨k * m, ?_⟩
    have hxm : teichPi p F (IsTateRing.pseudoUniformizer (A := F)) ^ (k * m)
        = c ^ m * teichPi p F ϖ ^ m := by
      rw [pow_mul, ← hc, mul_pow]
    rw [hxm]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hmem)

theorem isCompact_windowU_zero :
    IsCompact (Subtype.val ⁻¹' windowU p F ϖ 0 :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
  classical
  rw [windowU_zero_trace_eq]
  obtain ⟨P, g₁, g₂, hpair, hA₀le, hIeq⟩ := ainf_pair_spec p F
  refine isCompact_subtype_rationalOpen₂ P hpair hA₀le _ hIeq _ _ ?_
  refine iinf_le_radical_of_pure_powers p F ϖ ⟨1 + (cFF p).num.toNat, ?_⟩
    ⟨1 + (cFF p).den, by omega, ?_⟩
  · rw [pow_add, pow_one]
    simp
  · rw [pow_add, pow_one]
    simp

/-- Quasicompactness for `V_0`, as for `U_0`. -/
theorem isCompact_windowV_zero :
    IsCompact (Subtype.val ⁻¹' windowV p F ϖ 0 :
      Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
  classical
  rw [windowV_zero_trace_eq]
  obtain ⟨P, g₁, g₂, hpair, hA₀le, hIeq⟩ := ainf_pair_spec p F
  refine isCompact_subtype_rationalOpen₂ P hpair hA₀le _ hIeq _ _ ?_
  refine iinf_le_radical_of_pure_powers p F ϖ
    ⟨(cFF p).num.toNat + ((p : ℚ)).num.toNat, ?_⟩
    ⟨(cFF p).den + ((p : ℚ)).den, by positivity, ?_⟩
  · rw [pow_add]
    simp
  · rw [pow_add]
    simp

/-- **The curve is quasicompact**: it is the union of the images of the two
quasicompact charts `U_0`, `V_0`.

Source: [Kedlaya-AWS, Rem. 3.1.9]: "In particular, X_S can be covered by two affinoid
subspaces". -/
instance instCompactSpaceCurve : CompactSpace (Curve p F ϖ) := by
  have hWU : IsCompact (windowU p F ϖ 0) := by
    have h2 : Subtype.val '' (Subtype.val ⁻¹' windowU p F ϖ 0 :
        Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) = windowU p F ϖ 0 := by
      rw [Subtype.image_preimage_coe]
      exact Set.inter_eq_right.mpr (fun v hv => hv.1.1)
    exact h2 ▸ (isCompact_windowU_zero p F ϖ).image continuous_subtype_val
  have hWV : IsCompact (windowV p F ϖ 0) := by
    have h2 : Subtype.val '' (Subtype.val ⁻¹' windowV p F ϖ 0 :
        Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) = windowV p F ϖ 0 := by
      rw [Subtype.image_preimage_coe]
      exact Set.inter_eq_right.mpr (fun v hv => hv.1.1)
    exact h2 ▸ (isCompact_windowV_zero p F ϖ).image continuous_subtype_val
  have hSU : IsCompact
      {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0} := by
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr ?_
    have hset : (Subtype.val ''
        {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0}
          : Set (Spv (Ainf p F))) = windowU p F ϖ 0 := by
      rw [show {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0}
          = (Subtype.val ⁻¹' windowU p F ϖ 0 : Set ↥(Y p F ϖ)) from rfl,
        Subtype.image_preimage_coe]
      exact Set.inter_eq_right.mpr (fun v hv => hv.1)
    rw [hset]
    exact hWU
  have hSV : IsCompact
      {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0} := by
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr ?_
    have hset : (Subtype.val ''
        {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0}
          : Set (Spv (Ainf p F))) = windowV p F ϖ 0 := by
      rw [show {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0}
          = (Subtype.val ⁻¹' windowV p F ϖ 0 : Set ↥(Y p F ϖ)) from rfl,
        Subtype.image_preimage_coe]
      exact Set.inter_eq_right.mpr (fun v hv => hv.1)
    rw [hset]
    exact hWV
  rw [← isCompact_univ_iff, ← curve_eq_image_window_zero p F ϖ]
  exact (hSU.image (isOpenQuotientMap_toCurve p F ϖ).continuous).union
    (hSV.image (isOpenQuotientMap_toCurve p F ϖ).continuous)

/-- **The curve is nonempty** (equivalently `𝒴 ≠ ∅`): the `ρ = 1/2` Gauss point
`w_ρ(Σ pⁿ[aₙ]) = sup ρⁿ|aₙ|` is a continuous multiplicative valuation on `A_inf`
with `w(p·[ϖ]) = ρ·|ϖ| ≠ 0` (Fargues–Fontaine, *Courbes et fibrés vectoriels*,
§1.4; Kedlaya 1004.0466, Lemma 4.1 for multiplicativity — see `GaussPoint.lean`). -/
theorem Y_nonempty : (Y p F ϖ).Nonempty := Y_nonempty' p F ϖ

end FarguesFontaine

end
