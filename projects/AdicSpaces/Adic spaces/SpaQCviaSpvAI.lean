/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpvAITopology
import «Adic spaces».AdicSpectrum

/-!
# Quasi-compactness of `Spa A A⁺` via `Spv(A, I)` (Wedhorn 7.5 / 7.12 / 7.35)

The faithful route to the quasi-compactness of the adic spectrum and of its rational
subsets, mirroring Wedhorn's own assembly (re-based 2026-07-03; supersedes the
`(A × A → Bool)`-cube closedness keystone of `SpaCompactNoHArch`, which encodes the
STRICTLY STRONGER "`Spa` pro-constructible in `Spv A`" — a B2 candidate given
Remark 7.6):

* **`rhoR`** — the continuous map between Boolean cubes sending the `basicOpen`-profile
  of `v` to its `W(T/s)`-profile (`W(T/s) = { w ∈ Spv A ; ∀ t ∈ T, w(t) ≤ w(s) ≠ 0 }`).
* **Wedhorn 7.5(iii)** (`wedhorn.txt:2862-2872`): for `T` finite with `I ⊆ √(T·A)`,
  `W(T/s) = r⁻¹(Spv(A,I)(T/s))` where `r` is the 7.1.2 retraction. Hence
  `rhoR '' (range ιSpv_bool) = ιSpvR '' SpvAI A I`: the `R`-profile image of `Spv A`
  IS the `R`-profile image of `Spv(A, I)` — quasi-compactness of the latter as a
  continuous image of the (proven) compact `range ιSpv_bool` (7.5(iv),
  `wedhorn.txt:2873-2884`).
* **Theorem 7.10** (`wedhorn.txt:2908-2926`): `Cont A = { v ∈ Spv(A,I) ; v(a) < 1 ∀ a ∈ I }`
  — inside the profile cube these are clopen coordinate conditions.
* **Theorem 7.35** (`wedhorn.txt:3186-3207`): `Spa A = Cont A ∩ ⋂_{f ∈ A⁺} {v(f) ≤ 1}` —
  again clopen coordinate conditions; hence the `Spa`-profile image is compact, and the
  profile map is inducing and injective on `Spa` (rational subsets form a basis, 7.35(2)),
  so `Spa A A⁺` is a compact space and each rational subset is quasi-compact.

The principal case (`I = (π)`, Tate) uses the FAITHFUL `restrictIdealSingle` machinery
(T-SPVAI, 2026-06-22); the general-`I` `cGammaIdeal` is the known-unfaithful B2 and is
not used here.
-/

open ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-! ### R0 — the `W(T/s)`-profile cube and the connecting map `rhoR` -/

/-- The index of the profile cube: rational data `(T, s)` satisfying Wedhorn 7.5's side
condition `I ⊆ √(T·A)`. Only these coordinates are transported by the retraction
(7.5(iii)), and they suffice: they generate the topology of `Spv(A, I)` (7.5(ii)) and
encode the `Cont`/`Spa` conditions (`({1}, a)` and `({f}, 1)` both satisfy the side
condition trivially). -/
def RCoord (A : Type*) [CommRing A] (I : Ideal A) : Type _ :=
  {p : Finset A × A // I ≤ (Ideal.span (p.1 : Set A)).radical}

/-- The profile map between Boolean cubes: from the `basicOpen`-profile
`x = ιSpv_bool v` to the `W(T/s)`-profile. The `(T, s)`-coordinate is the finite
Boolean formula `(∀ t ∈ T, x (t, s)) ∧ x (s, s)`; note `x (t, s)` already encodes
`v(t) ≤ v(s) ≠ 0` and `x (s, s)` encodes `v(s) ≠ 0` (covering `T = ∅`). -/
noncomputable def rhoR (I : Ideal A) (x : A × A → Bool) : RCoord A I → Bool :=
  fun p => (p.1.1.toList.all fun t => x (t, p.1.2)) && x (p.1.2, p.1.2)

/-- Each `rhoR`-coordinate depends on finitely many input coordinates, so `rhoR` is
continuous for the product-of-discrete topologies. -/
theorem continuous_rhoR (I : Ideal A) : Continuous (rhoR (A := A) I) := by
  refine continuous_pi fun p => ?_
  have hall : ∀ l : List A, Continuous fun x : A × A → Bool => l.all fun t => x (t, p.1.2) := by
    intro l
    induction l with
    | nil => simpa using continuous_const
    | cons t l ih =>
      simp only [List.all_cons]
      exact (continuous_of_discreteTopology (f := fun q : Bool × Bool => q.1 && q.2)).comp
        ((continuous_apply (t, p.1.2)).prodMk ih)
  exact (continuous_of_discreteTopology (f := fun q : Bool × Bool => q.1 && q.2)).comp
    ((hall p.1.1.toList).prodMk (continuous_apply (p.1.2, p.1.2)))

/-- The `W(T/s)`-profile of a point of `Spv A`. -/
noncomputable def ιSpvR (I : Ideal A) (v : Spv A) : RCoord A I → Bool :=
  rhoR I (ιSpv_bool v)

@[simp]
theorem rhoR_ιSpv_bool (I : Ideal A) (v : Spv A) : rhoR I (ιSpv_bool v) = ιSpvR I v := rfl

/-- Coordinate semantics of the `W(T/s)`-profile. -/
theorem ιSpvR_eq_true_iff (I : Ideal A) (v : Spv A) (p : RCoord A I) :
    ιSpvR I v p = true ↔ (∀ t ∈ p.1.1, v.vle t p.1.2) ∧ ¬ v.vle p.1.2 0 := by
  unfold ιSpvR rhoR ιSpv_bool
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hT, -, hs0⟩
    exact ⟨fun t ht => (hT t (Finset.mem_toList.mpr ht)).1, hs0⟩
  · rintro ⟨hT, hs0⟩
    exact ⟨fun t ht => ⟨hT t (Finset.mem_toList.mp ht), hs0⟩,
      (v.vle_total p.1.2 p.1.2).elim id id, hs0⟩

/-! ### R1 — Wedhorn 7.5(iii): the profile image of `Spv A` is the profile image of
`Spv(A, I)`

The two order-transfer lemmas for the convex-window restriction: the `≤`-side is
preserved unconditionally (values outside the window truncate to `0`, and convexity
forces an in-window sandwich), and the order is reflected wherever the restricted upper
value is nonzero (same sandwich). -/

/-- Order transfer UP: `w g ≤ w h` implies the restricted values are ordered. -/
theorem restrictToConvexBounded_le_of_le
    {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : w a ≠ 0, 1 ≤ w a → Units.mk0 (w a) ha ∈ H)
    {g h : R} (hle : w g ≤ w h) :
    w.restrictToConvexBounded H hH_ge g ≤ w.restrictToConvexBounded H hH_ge h := by
  by_cases hg0 : w g = 0
  · rw [Valuation.restrictToConvexBounded_apply_zero w H hH_ge hg0]
    exact zero_le'
  by_cases hgm : Units.mk0 (w g) hg0 ∈ H
  · -- `g` in the window; then `h` is too (else `w g ≤ w h < 1` sandwiches `w h` in `H`).
    have hh0 : w h ≠ 0 := fun h0 => hg0 (le_antisymm (h0 ▸ hle) zero_le')
    have hhm : Units.mk0 (w h) hh0 ∈ H := by
      by_contra hhm
      have hh_lt : w h < 1 := by
        by_contra hge
        push_neg at hge
        exact hhm (hH_ge h hh0 hge)
      exact hhm (H.convex hgm (one_mem H)
        (Units.val_le_val.mp (by simpa using hle))
        (Units.val_le_val.mp (by simpa using hh_lt.le)))
    rw [Valuation.restrictToConvexBounded_apply_mem w H hH_ge hg0 hgm,
      Valuation.restrictToConvexBounded_apply_mem w H hH_ge hh0 hhm]
    exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr (Units.val_le_val.mp
      (by simpa using hle)))
  · rw [Valuation.restrictToConvexBounded_apply_not_mem w H hH_ge hg0 hgm]
    exact zero_le'

/-- Order transfer DOWN (specialization): ordered restricted values with nonzero upper
value give back `w g ≤ w h ≠ 0`. -/
theorem restrictToConvexBounded_le_reflect
    {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : w a ≠ 0, 1 ≤ w a → Units.mk0 (w a) ha ∈ H)
    {g h : R}
    (hle : w.restrictToConvexBounded H hH_ge g ≤ w.restrictToConvexBounded H hH_ge h)
    (hne : w.restrictToConvexBounded H hH_ge h ≠ 0) :
    w g ≤ w h ∧ w h ≠ 0 := by
  by_cases hh0 : w h = 0
  · exact absurd (Valuation.restrictToConvexBounded_apply_zero w H hH_ge hh0) hne
  by_cases hhm : Units.mk0 (w h) hh0 ∈ H
  swap
  · exact absurd (Valuation.restrictToConvexBounded_apply_not_mem w H hH_ge hh0 hhm) hne
  refine ⟨?_, hh0⟩
  by_cases hg0 : w g = 0
  · rw [hg0]
    exact zero_le'
  by_cases hgm : Units.mk0 (w g) hg0 ∈ H
  · rw [Valuation.restrictToConvexBounded_apply_mem w H hH_ge hg0 hgm,
      Valuation.restrictToConvexBounded_apply_mem w H hH_ge hh0 hhm] at hle
    have h1 := Subtype.mk_le_mk.mp (WithZero.coe_le_coe.mp hle)
    simpa using Units.val_le_val.mpr h1
  · -- `g` outside the window with `w h < w g < 1` would sandwich `w g` in `H`.
    by_contra hlt
    push_neg at hlt
    have hg_lt : w g < 1 := by
      by_contra hge
      push_neg at hge
      exact hgm (hH_ge g hg0 hge)
    exact hgm (H.convex hhm (one_mem H)
      (Units.val_le_val.mp (by simpa using hlt.le))
      (Units.val_le_val.mp (by simpa using hg_lt.le)))

variable [TopologicalSpace A]

/-- `vle`-bridge for the Spv-level retraction. -/
theorem restrictIdeal_vle_iff (v : Spv A) (I : Ideal A) (g h : A) :
    (restrictIdeal v I).vle g h ↔
      (letI : ValuativeRel A := v.toValuativeRel
       (ValuativeRel.valuation A).restrictIdeal I g ≤
         (ValuativeRel.valuation A).restrictIdeal I h) := by
  letI : ValuativeRel A := v.toValuativeRel
  exact Iff.rfl

/-- `vle`-bridge for `v` via its canonical valuation. -/
theorem vle_iff_canonical (v : Spv A) (g h : A) :
    v.vle g h ↔
      (letI : ValuativeRel A := v.toValuativeRel
       ValuativeRel.valuation A g ≤ ValuativeRel.valuation A h) := by
  letI : ValuativeRel A := v.toValuativeRel
  exact Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) g h

/-- Transitivity of `vle` (through the canonical valuation). -/
theorem vle_trans' {v : Spv A} {a b c : A} (h1 : v.vle a b) (h2 : v.vle b c) :
    v.vle a c := by
  rw [vle_iff_canonical] at h1 h2 ⊢
  exact le_trans h1 h2

/-- **Wedhorn 7.5(iii), preservation half**: `v.vle g h → (restrictIdeal v I).vle g h`. -/
theorem restrictIdeal_vle_of_vle {v : Spv A} {I : Ideal A} {g h : A}
    (hle : v.vle g h) : (restrictIdeal v I).vle g h := by
  letI : ValuativeRel A := v.toValuativeRel
  rw [restrictIdeal_vle_iff]
  rw [vle_iff_canonical] at hle
  exact restrictToConvexBounded_le_of_le _ _ _ hle

/-- **Wedhorn 7.5(iii), reflection half**. -/
theorem vle_of_restrictIdeal_vle {v : Spv A} {I : Ideal A} {g h : A}
    (hle : (restrictIdeal v I).vle g h) (hne : ¬ (restrictIdeal v I).vle h 0) :
    v.vle g h ∧ ¬ v.vle h 0 := by
  letI : ValuativeRel A := v.toValuativeRel
  rw [restrictIdeal_vle_iff] at hle
  have hne' : (ValuativeRel.valuation A).restrictIdeal I h ≠ 0 := by
    intro h0
    apply hne
    rw [restrictIdeal_vle_iff, h0]
    simp
  obtain ⟨h1, h2⟩ := restrictToConvexBounded_le_reflect _ _ _ hle hne'
  refine ⟨(vle_iff_canonical v g h).mpr h1, fun hcon => h2 ?_⟩
  have h3 := (vle_iff_canonical v h 0).mp hcon
  simpa using h3

/-- `v(I) = 0` puts `v` in `Spv(A, I)` (the cofinality disjunct holds vacuously on zero
values). -/
theorem isInSpvAI_of_forall_vle_zero {v : Spv A} {I : Ideal A}
    (h : ∀ a ∈ I, v.vle a 0) : v ∈ SpvAI A I := by
  letI : ValuativeRel A := v.toValuativeRel
  refine Or.inl fun a ha => ?_
  have h0 : ValuativeRel.valuation A a = 0 := by
    have h1 := (vle_iff_canonical v a 0).mp (h a ha)
    simpa using h1
  intro γ hγ
  exact ⟨1, by simpa [h0] using hγ⟩

/-- **Wedhorn 7.5(iii)** (`wedhorn.txt:2862-2872`, verbatim: *"Set `U := Spv(A, I)(T/s)`
and `W := Spv(A)(T/s)`. We claim that `W = r⁻¹(U)`."*), profile form: for `T` finite with
`I ⊆ √(T·A)` and every `v : Spv A`, the `(T, s)`-profile coordinate of `v` agrees with
that of the retraction. The pair-of-definition data threads `retraction_eq_self`'s
hypotheses for the `v(I) = 0` branch. -/
theorem ιSpvR_retraction_eq (I : Ideal A) (P : PairOfDefinition A)
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (v : Spv A) (p : RCoord A I) :
    ιSpvR I ((SpvAI.retraction I v : Spv A)) p = ιSpvR I v p := by
  obtain ⟨⟨T, s⟩, hTI⟩ := p
  by_cases hI0 : ∃ a ∈ I, ¬ v.vle a 0
  · rw [Bool.eq_iff_iff, ιSpvR_eq_true_iff, ιSpvR_eq_true_iff]
    constructor
    · rintro ⟨hT, hs⟩
      have hss : (restrictIdeal v I).vle s s :=
        ((restrictIdeal v I).vle_total s s).elim id id
      have hs_side := vle_of_restrictIdeal_vle hss hs
      exact ⟨fun t ht => (vle_of_restrictIdeal_vle (hT t ht) hs).1, hs_side.2⟩
    · rintro ⟨hT, hs0⟩
      have hTr : ∀ t ∈ T, (restrictIdeal v I).vle t s :=
        fun t ht => restrictIdeal_vle_of_vle (hT t ht)
      refine ⟨hTr, ?_⟩
      intro hs_zero
      obtain ⟨a, haI, ha_ne⟩ := SpvAI.retraction_ideal_ne_zero (I := I) (v := v) hI0
      apply ha_ne
      have hsupp : ∀ t ∈ T, t ∈ (restrictIdeal v I).supp := by
        intro t ht
        rw [mem_supp_iff]
        exact vle_trans' (hTr t ht) hs_zero
      have hspan : Ideal.span (T : Set A) ≤ (restrictIdeal v I).supp :=
        Ideal.span_le.mpr fun t ht => hsupp t ht
      have hrad : a ∈ (restrictIdeal v I).supp := by
        obtain ⟨n, hn⟩ := hTI haI
        exact (instIsPrimeSupp (restrictIdeal v I)).mem_of_pow_mem n (hspan hn)
      exact (mem_supp_iff _ a).mp hrad
  · push_neg at hI0
    have hv_mem : v ∈ SpvAI A I := isInSpvAI_of_forall_vle_zero hI0
    have hfix : (SpvAI.retraction I v : Spv A) = v :=
      congrArg Subtype.val (SpvAI.retraction_eq_self I P hIeq ⟨v, hv_mem⟩)
    rw [hfix]

/-- **Wedhorn 7.5(iii)+(iv), image form**: the `W`-profile image of all of `Spv A`
coincides with the profile image of `Spv(A, I)` — on the coordinates satisfying the
side condition `I ⊆ √(T·A)` (the profile values elsewhere are not constrained; the
downstream lemmas only read side-condition coordinates). Stated as: for every
`v : Spv A` there is `w ∈ SpvAI A I` whose profile agrees with `v`'s on all
side-condition coordinates, and conversely. -/
theorem exists_SpvAI_profile_agree (I : Ideal A) (P : PairOfDefinition A)
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) (v : Spv A) :
    ∃ w ∈ SpvAI A I, ιSpvR I w = ιSpvR I v :=
  ⟨(SpvAI.retraction I v : Spv A), (SpvAI.retraction I v).2,
    funext fun p => ιSpvR_retraction_eq I P hIeq v p⟩

/-! ### R2 — the compact profile set

To avoid quantifying images over non-side-condition coordinates, define the compact
carrier as the FULL `rhoR`-image of the (proven compact) `basicOpen`-profile range. -/

/-- The `W`-profile carrier: image of the compact `range ιSpv_bool` under the continuous
`rhoR`. Compact by construction; equals the profile image of `Spv(A, I)` by 7.5(iii). -/
noncomputable def profileCarrier (A : Type*) [CommRing A] (I : Ideal A) :
    Set (RCoord A I → Bool) :=
  rhoR I '' Set.range (ιSpv_bool : Spv A → A × A → Bool)

theorem isCompact_profileCarrier (I : Ideal A) : IsCompact (profileCarrier A I) :=
  (isCompact_range_ιSpv_bool).image (continuous_rhoR I)

/-! ### R3 — Wedhorn 7.10 / 7.35 as clopen coordinate conditions -/

variable [PlusSubring A]

/-- The `({1}, a)`-coordinate satisfies the side condition trivially
(`span {1} = ⊤`). -/
def RCoord.oneOver (I : Ideal A) (a : A) : RCoord A I :=
  ⟨(({1} : Finset A), a), by
    have h : Ideal.span (({1} : Finset A) : Set A) = ⊤ := by
      simp [Ideal.span_singleton_one]
    rw [h, Ideal.radical_top]
    exact le_top⟩

open Classical in
/-- The `({f, 1}, 1)`-coordinate (encoding `v(f) ≤ 1`) satisfies the side condition
trivially (`1 ∈ T` gives `span T = ⊤`). -/
noncomputable def RCoord.leOne (I : Ideal A) (f : A) : RCoord A I :=
  ⟨((({f, 1} : Finset A)), (1 : A)), by
    have h : Ideal.span ((({f, 1} : Finset A)) : Set A) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one
    rw [h, Ideal.radical_top]
    exact le_top⟩

/-- The `Spa`-profile conditions inside the profile cube: for EVERY element `a` of the
ideal of definition (image in `A`) the coordinate `({1}, a)` is `false` (encoding
`v(a) < 1`: `W({1}/a) = {v(a) ≥ 1}`), and for `f ∈ A⁺` the coordinate `({f}, 1)` is
`true` (encoding `v(f) ≤ 1`, as `v(1) ≠ 0` always). Quantifying over the whole ideal —
not just a generating set — matches Theorem 7.10's hypothesis (`v(a) < 1 for all a ∈ I`)
and is what the reverse direction's coefficient-absorption needs. -/
def spaProfileConditions (I : Ideal A) : Set (RCoord A I → Bool) :=
  { y | (∀ a ∈ I, y (RCoord.oneOver I a) = false) ∧
        ∀ f ∈ (A⁺ : Subring A), y (RCoord.leOne I f) = true }

/-- The conditions cut out a closed subset (an intersection of coordinate cylinders in a
product of discrete spaces). -/
theorem isClosed_spaProfileConditions (I : Ideal A) :
    IsClosed (spaProfileConditions (A := A) I) := by
  have hrw : spaProfileConditions (A := A) I =
      (⋂ a ∈ I, {y : RCoord A I → Bool | y (RCoord.oneOver I a) = false}) ∩
      ⋂ f ∈ (A⁺ : Subring A), {y : RCoord A I → Bool | y (RCoord.leOne I f) = true} := by
    ext y
    simp [spaProfileConditions]
  rw [hrw]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_biInter fun a _ => ?_
    have h : {y : RCoord A I → Bool | y (RCoord.oneOver I a) = false} =
        (fun y : RCoord A I → Bool => y (RCoord.oneOver I a)) ⁻¹' {false} := rfl
    rw [h]
    exact IsClosed.preimage (continuous_apply _) (isClosed_discrete _)
  · refine isClosed_biInter fun f _ => ?_
    have h : {y : RCoord A I → Bool | y (RCoord.leOne I f) = true} =
        (fun y : RCoord A I → Bool => y (RCoord.leOne I f)) ⁻¹' {true} := rfl
    rw [h]
    exact IsClosed.preimage (continuous_apply _) (isClosed_discrete _)

/-- **Wedhorn 7.10 + 7.35, profile form.** Let `I = span S` be a (principal-generated,
Tate-faithful) ideal of definition. The `Spa`-profile image equals the compact carrier
intersected with the clopen conditions:
`ιSpvR '' (Spa A A⁺) = profileCarrier A ∩ spaProfileConditions S`.

`⊆`: `Spa ⊆ Spv` gives carrier membership; a continuous `v` has `v(a) < 1` for `a ∈ S`
(topological nilpotence) and `v(f) ≤ 1` for `f ∈ A⁺` by `Spa`-membership.
`⊇`: given `y = rhoR (ιSpv_bool v)`, Wedhorn 7.5(iii) rewrites `y = ιSpvR w` for the
retraction `w := r v ∈ Spv(A, I)`; the conditions transported to `w` say `w(a) < 1` on
`S` and `w(f) ≤ 1` on `A⁺`; Theorem 7.10 (converse direction, *"Choose `n ∈ ℕ` such that
`t·aⁿ ∈ I` (this exists because `{t}` is bounded)"*, `wedhorn.txt:2919-2922`) then yields
`w ∈ Cont A`, hence `w ∈ Spa A A⁺` and `y ∈ ιSpvR '' Spa`. -/
theorem image_ιSpvR_spa_eq (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    ιSpvR I '' (Spa A A⁺) = profileCarrier A I ∩ spaProfileConditions I := by
  sorry

/-- The `Spa`-profile image is compact. -/
theorem isCompact_image_ιSpvR_spa (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    IsCompact (ιSpvR I '' (Spa A A⁺)) := by
  rw [image_ιSpvR_spa_eq P I hIeq]
  exact (isCompact_profileCarrier I).inter_right (isClosed_spaProfileConditions I)

/-! ### R4 — the profile map is inducing and injective on `Spa`; quasi-compactness -/

/-- **Wedhorn 7.35(2) substrate (via 7.5(ii), `wedhorn.txt:2836-2858`)**: on `Spa A A⁺`
the subspace topology from `Spv A` is generated by the rational subsets, i.e. by the
`W(T/s)`-profile coordinates with the side condition. Hence `ιSpvR` restricted to
`Spa A A⁺` is inducing. -/
theorem isInducing_ιSpvR_spa (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    Topology.IsInducing (fun v : ↥(Spa A A⁺) => ιSpvR I (v : Spv A)) := by
  sorry

/-- `ιSpvR` is injective on `Spa A A⁺` (rational subsets separate points of `Spa`;
`Spv A` is T0 on `basicOpen`s and the 7.5(ii) refinement keeps separation on the
side-condition coordinates). -/
theorem injOn_ιSpvR_spa (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    Set.InjOn (ιSpvR I) (Spa A A⁺) := by
  sorry

/-- **`Spa A A⁺` is a compact topological space** (Wedhorn 7.35(1): spectral, in
particular quasi-compact). -/
theorem compactSpace_spa (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    CompactSpace ↥(Spa A A⁺) := by
  sorry

/-- **Rational subsets are quasi-compact** (Wedhorn 7.35(2)): the trace of
`rationalOpen T s` on `Spa A A⁺` is compact whenever the datum satisfies the openness
side condition. -/
theorem isCompact_subtype_rationalOpen (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    (T : Finset A) (s : A)
    (hTI : I ≤ (Ideal.span (T : Set A)).radical) :
    IsCompact (Subtype.val ⁻¹' (rationalOpen T s) : Set ↥(Spa A A⁺)) := by
  sorry

end ValuationSpectrum
