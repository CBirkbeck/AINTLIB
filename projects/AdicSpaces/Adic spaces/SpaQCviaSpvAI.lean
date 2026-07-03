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

/-- The profile map between Boolean cubes: from the `basicOpen`-profile
`x = ιSpv_bool v` to the `W(T/s)`-profile. The `(T, s)`-coordinate is the finite
Boolean formula `(∀ t ∈ T, x (t, s)) ∧ x (s, s)`; note `x (t, s)` already encodes
`v(t) ≤ v(s) ≠ 0` and `x (s, s)` encodes `v(s) ≠ 0` (covering `T = ∅`). -/
noncomputable def rhoR (x : A × A → Bool) : Finset A × A → Bool :=
  fun p => (p.1.toList.all fun t => x (t, p.2)) && x (p.2, p.2)

/-- Each `rhoR`-coordinate depends on finitely many input coordinates, so `rhoR` is
continuous for the product-of-discrete topologies. -/
theorem continuous_rhoR : Continuous (rhoR (A := A)) := by
  refine continuous_pi fun p => ?_
  have hall : ∀ l : List A, Continuous fun x : A × A → Bool => l.all fun t => x (t, p.2) := by
    intro l
    induction l with
    | nil => simpa using continuous_const
    | cons t l ih =>
      simp only [List.all_cons]
      exact (continuous_of_discreteTopology (f := fun q : Bool × Bool => q.1 && q.2)).comp
        ((continuous_apply (t, p.2)).prodMk ih)
  exact (continuous_of_discreteTopology (f := fun q : Bool × Bool => q.1 && q.2)).comp
    ((hall p.1.toList).prodMk (continuous_apply (p.2, p.2)))

/-- The `W(T/s)`-profile of a point of `Spv A`. -/
noncomputable def ιSpvR (v : Spv A) : Finset A × A → Bool :=
  rhoR (ιSpv_bool v)

@[simp]
theorem rhoR_ιSpv_bool (v : Spv A) : rhoR (ιSpv_bool v) = ιSpvR v := rfl

/-- Coordinate semantics of the `W(T/s)`-profile:
`ιSpvR v (T, s) = true ↔ (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0`. -/
theorem ιSpvR_eq_true_iff (v : Spv A) (T : Finset A) (s : A) :
    ιSpvR v (T, s) = true ↔ (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 := by
  unfold ιSpvR rhoR ιSpv_bool
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hT, -, hs0⟩
    exact ⟨fun t ht => (hT t (Finset.mem_toList.mpr ht)).1, hs0⟩
  · rintro ⟨hT, hs0⟩
    exact ⟨fun t ht => ⟨hT t (Finset.mem_toList.mp ht), hs0⟩,
      (v.vle_total s s).elim id id, hs0⟩

/-! ### R1 — Wedhorn 7.5(iii): the profile image of `Spv A` is the profile image of
`Spv(A, I)` -/

variable [TopologicalSpace A]

/-- **Wedhorn 7.5(iii)** (`wedhorn.txt:2862-2872`, verbatim: *"Set `U := Spv(A, I)(T/s)`
and `W := Spv(A)(T/s)`. We claim that `W = r⁻¹(U)`."*), profile form: for `T` finite with
`I ⊆ √(T·A)` and every `v : Spv A`, the `(T, s)`-profile coordinate of `v` agrees with
that of the retraction `SpvAI.retraction I v`. Principal faithful case `I = (π)`. -/
theorem ιSpvR_retraction_eq (I : Ideal A) (v : Spv A)
    (T : Finset A) (s : A) (hTI : I ≤ (Ideal.span (T : Set A)).radical) :
    ιSpvR ((SpvAI.retraction I v : Spv A)) (T, s) = ιSpvR v (T, s) := by
  sorry

/-- **Wedhorn 7.5(iii)+(iv), image form**: the `W`-profile image of all of `Spv A`
coincides with the profile image of `Spv(A, I)` — on the coordinates satisfying the
side condition `I ⊆ √(T·A)` (the profile values elsewhere are not constrained; the
downstream lemmas only read side-condition coordinates). Stated as: for every
`v : Spv A` there is `w ∈ SpvAI A I` whose profile agrees with `v`'s on all
side-condition coordinates, and conversely. -/
theorem exists_SpvAI_profile_agree (I : Ideal A) (v : Spv A) :
    ∃ w ∈ SpvAI A I, ∀ T : Finset A, ∀ s : A,
      I ≤ (Ideal.span (T : Set A)).radical → ιSpvR w (T, s) = ιSpvR v (T, s) := by
  sorry

/-! ### R2 — the compact profile set

To avoid quantifying images over non-side-condition coordinates, define the compact
carrier as the FULL `rhoR`-image of the (proven compact) `basicOpen`-profile range. -/

/-- The `W`-profile carrier: image of the compact `range ιSpv_bool` under the continuous
`rhoR`. Compact by construction. -/
noncomputable def profileCarrier (A : Type*) [CommRing A] : Set (Finset A × A → Bool) :=
  rhoR '' Set.range (ιSpv_bool : Spv A → A × A → Bool)

theorem isCompact_profileCarrier : IsCompact (profileCarrier A) :=
  (isCompact_range_ιSpv_bool).image continuous_rhoR

/-! ### R3 — Wedhorn 7.10 / 7.35 as clopen coordinate conditions -/

variable [PlusSubring A]

/-- The `Spa`-profile conditions inside the profile cube: for the ideal-of-definition
generators `a ∈ S` the coordinate `({1}, a)` is `false` (this encodes `v(a) < 1`, since
`W({1}/a) = {v(1) ≤ v(a) ≠ 0} = {v(a) ≥ 1}`), and for `f ∈ A⁺` the coordinate
`({f}, 1)` is `true` (encoding `v(f) ≤ 1`, as `v(1) ≠ 0` always). -/
def spaProfileConditions (S : Finset A) : Set (Finset A × A → Bool) :=
  { y | (∀ a ∈ S, y (({1} : Finset A), a) = false) ∧
        ∀ f ∈ (A⁺ : Subring A), y (({f} : Finset A), (1 : A)) = true }

/-- The conditions cut out a closed subset (an intersection of coordinate cylinders in a
product of discrete spaces). -/
theorem isClosed_spaProfileConditions (S : Finset A) :
    IsClosed (spaProfileConditions (A := A) S) := by
  have hrw : spaProfileConditions (A := A) S =
      (⋂ a ∈ S, {y : Finset A × A → Bool | y (({1} : Finset A), a) = false}) ∩
      ⋂ f ∈ (A⁺ : Subring A), {y : Finset A × A → Bool | y (({f} : Finset A), (1 : A)) = true} := by
    ext y
    simp [spaProfileConditions]
  rw [hrw]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_biInter fun a _ => ?_
    have h : {y : Finset A × A → Bool | y (({1} : Finset A), a) = false} =
        (fun y : Finset A × A → Bool => y (({1} : Finset A), a)) ⁻¹' {false} := rfl
    rw [h]
    exact IsClosed.preimage (continuous_apply _) (isClosed_discrete _)
  · refine isClosed_biInter fun f _ => ?_
    have h : {y : Finset A × A → Bool | y (({f} : Finset A), (1 : A)) = true} =
        (fun y : Finset A × A → Bool => y (({f} : Finset A), (1 : A))) ⁻¹' {true} := rfl
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
    (S : Finset A) (hS : Ideal.span (S : Set A) = P.idealOfDefinition) :
    ιSpvR '' (Spa A A⁺) = profileCarrier A ∩ spaProfileConditions S := by
  sorry

/-- The `Spa`-profile image is compact. -/
theorem isCompact_image_ιSpvR_spa (P : PairOfDefinition A)
    (S : Finset A) (hS : Ideal.span (S : Set A) = P.idealOfDefinition) :
    IsCompact (ιSpvR '' (Spa A A⁺)) := by
  rw [image_ιSpvR_spa_eq P S hS]
  exact isCompact_profileCarrier.inter_right (isClosed_spaProfileConditions S)

/-! ### R4 — the profile map is inducing and injective on `Spa`; quasi-compactness -/

/-- **Wedhorn 7.35(2) substrate (via 7.5(ii), `wedhorn.txt:2836-2858`)**: on `Spa A A⁺`
the subspace topology from `Spv A` is generated by the rational subsets, i.e. by the
`W(T/s)`-profile coordinates with the side condition. Hence `ιSpvR` restricted to
`Spa A A⁺` is inducing. -/
theorem isInducing_ιSpvR_spa (P : PairOfDefinition A) :
    Topology.IsInducing (fun v : ↥(Spa A A⁺) => ιSpvR (v : Spv A)) := by
  sorry

/-- `ιSpvR` is injective on `Spa A A⁺` (rational subsets separate points of `Spa`;
`Spv A` is T0 on `basicOpen`s and the 7.5(ii) refinement keeps separation on the
side-condition coordinates). -/
theorem injOn_ιSpvR_spa (P : PairOfDefinition A) :
    Set.InjOn ιSpvR (Spa A A⁺) := by
  sorry

/-- **`Spa A A⁺` is a compact topological space** (Wedhorn 7.35(1): spectral, in
particular quasi-compact). -/
theorem compactSpace_spa (P : PairOfDefinition A)
    (S : Finset A) (hS : Ideal.span (S : Set A) = P.idealOfDefinition) :
    CompactSpace ↥(Spa A A⁺) := by
  sorry

/-- **Rational subsets are quasi-compact** (Wedhorn 7.35(2)): the trace of
`rationalOpen T s` on `Spa A A⁺` is compact whenever the datum satisfies the openness
side condition. -/
theorem isCompact_subtype_rationalOpen (P : PairOfDefinition A)
    (S : Finset A) (hS : Ideal.span (S : Set A) = P.idealOfDefinition)
    (T : Finset A) (s : A)
    (hTI : P.idealOfDefinition ≤ (Ideal.span (T : Set A)).radical) :
    IsCompact (Subtype.val ⁻¹' (rationalOpen T s) : Set ↥(Spa A A⁺)) := by
  sorry

end ValuationSpectrum
