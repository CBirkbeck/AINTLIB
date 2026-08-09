/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMPatching

/-!
# Uniqueness of the normalised splitting units on general opens (ticket AP-D5-uniq)

`WeilPairing/KMNormalisation.lean` normalises Katz–Mazur's splitting units `h_i`
(`exists_normalized_splitting`, KM p. 88) and `WeilPairing/KMPatching.lean` evaluates them at an
`N`-torsion section `P` (`exists_globalUnit_sectionEval_of_pullback_split`, KM p. 89). Both files
record the same loose end, documented at `eq_of_mem_sectionUnits`: `AP-D2` pins a normalised unit
only on opens that are **preimages of base opens**, whereas the `h_i` live on general opens `V i`
of the curve. So `h(P)` was unique only *given* a choice of the `h_i`. This file closes that and
repackages `h(P)` as a function of `P`.

## The argument, and the hypothesis the sketch omits

Two normalised splittings `h`, `h'` of the same cocycle `F` have ratios `h_i · h_i'⁻¹` agreeing on
the overlaps: in the commutative group `Γ(Y, V i ⊓ V j)ˣ` the relation `a_i · b_j⁻¹ = c_i · d_j⁻¹`
rearranges to `a_i · c_i⁻¹ = b_j · d_j⁻¹` (`mul_inv_comm_of_mul_inv_eq`). So they glue
(`exists_globalUnit_restrict`) to one unit `u` on `⊤`, which is normalised along `z` because units
are determined locally (`eq_of_forall_resUnit_eq`). Now `AP-D2` *does* apply to `u`, since `⊤` is a
preimage of a base open — `pullback.snd p g ⁻¹ᵁ ⊤ = ⊤` on the nose. Hence `u = 1`, i.e.
`h i = h' i`.

Gluing the ratios needs the `V i` to cover the **curve**, `iSup V = ⊤`. That is a hypothesis
`exists_normalized_splitting` does *not* carry: it asks only that the traces `z ⁻¹ᵁ V i` cover the
base. It is not removable — over `S = Spec k` with `Y = ℙ¹`, a single `V = 𝔾_m` and `z` the
section `t = 1`, the unit `t` is normalised along `z` and is not `1`, so on one non-covering open
normalised units are not unique, and neither is `h(P)`. In the situation the tickets use it the
hypothesis is free: the `V i` are the `[N]`-preimages `[N] ⁻¹ᵁ W i` of a trivialising cover `W` of
the curve, and `Scheme.Hom.iSup_preimage_eq_top` supplies it.

## Main results

* `normalizedSplittingEval` — **`h(P)`**: the value along `P` of a normalised splitting of the
  cocycle `F`, as a `Γ(T, 𝒪_T^×)`-valued function of the data. Defined by choice from `AP-D6`
  (`exists_globalUnit_sectionEval`); its content is that the choice does not matter.
* `eq_of_normalized_splitting` — **the loose end**: over a universally `O`-connected family, two
  normalised splittings of one cocycle over a cover of the curve are *equal*, `h i = h' i`. This is
  `AP-D2` on general opens, which is what `eq_of_mem_sectionUnits` could not reach.
* `eval_eq_of_normalized_splitting` — **independence of `h(P)`**: two global units reading two
  normalised splittings of the same cocycle along `P` coincide.
* `resUnit_normalizedSplittingEval` — the **spec**: `h(P)` restricts to `h_i ∘ P` for *every*
  normalised splitting `h`, not merely for the chosen one. This is the consumable form of
  independence.
* `eq_normalizedSplittingEval` — the converse pin: anything satisfying that spec *is* `h(P)`. With
  the previous lemma it upgrades `AP-D6`'s `∃!` (which was relative to a fixed `h`) to an absolute
  one.
* `exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints` — for the elliptic curve:
  `AP-D5`'s existence (`exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints`) composed with the
  normalisation, using `[N] ∘ 0 = 0` (`zero_comp_mulByHom_baseChange`) to see that the pulled-back
  transition units are normalised.
* `torsionSplittingEval`, `resUnit_torsionSplittingEval`, `eq_torsionSplittingEval` — **the
  ticket's deliverable**: `h(P)` for the curve, a well-defined `Γ(T, 𝒪_T^×)` attached to the pair
  of torsion sections `Q` (through `M`, `W`, `e`) and `P`, together with its spec and its pin.
  `AP-D7` consumes these three.

## What is *not* used

Neither half of Abel: nothing here touches `exists_torsionPoint_of_mem_kerMulByN`
(`WeilPairing/KMPairing.lean`), so no declaration below inherits its `sorryAx`. Only the proved `⊆`
direction of `AP-D4` enters, through `AP-D5`. Unlike `WeilPairing/KMPatching.lean`, this file
*does* use `UniversallyOConnected` — that is exactly the input of `AP-D2`, and it is what makes the
`h_i`, and hence `h(P)`, canonical. For the elliptic curve it is free
(`EllipticCurveGeom.universallyOConnected`), so no new hypothesis appears in the curve statements.

## Degenerate cases

For an empty index type `iSup V = ⊤` forces `Y = ∅`; then `Γ(Y, V i)ˣ` is empty of indices and the
uniqueness statement is vacuous, while `h(P)` is the unique unit of `Γ(T, ⊤)`, `T` being empty as
well. Nothing needs the cover to be finite, the index type to be nonempty, or `P` to differ from
the zero section.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-! ## `h(P)` as a function of the data -/

section General

variable {Y T : Scheme.{u}}

/-- Rearranging a coincidence of ratios in a commutative group: if `a / b = c / d` then
`a / c = b / d`. This is the whole reason two normalised splittings have ratios that agree on the
overlaps, and it is stated over abstract elements so that the `ac_rfl` normalisation runs on atoms
rather than on section terms. -/
private theorem mul_inv_comm_of_mul_inv_eq {G : Type*} [CommGroup G] {a b c d : G}
    (h : a * b⁻¹ = c * d⁻¹) : a * c⁻¹ = b * d⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul] at h ⊢
  rw [h]
  simp only [mul_comm, mul_left_comm]

/-- **KM's `h(P)` (p. 89)**: the value along the section `P` of a normalised splitting of the
cocycle `F` over the opens `V i` of the total space.

Existence of the glued unit is `AP-D6` (`exists_globalUnit_sectionEval`,
`WeilPairing/KMPatching.lean`) applied to a splitting extracted from `hex`; the point of the
definition is `resUnit_normalizedSplittingEval`, which says that the extracted splitting may be
replaced by *any* normalised splitting of `F`. The hypotheses are exactly KM's: `hFP` is his
`f_{i,j} ∈ K^×` transported by `πP = 0`, and `hex` is `AP-D5`. -/
noncomputable def normalizedSplittingEval (z P : T ⟶ Y) {ι : Type*} (V : ι → Y.Opens)
    (hV : iSup V = ⊤) (F : ∀ i j, Γ(Y, V i ⊓ V j)ˣ)
    (hFP : ∀ i j, F i j ∈ sectionUnits P (V i ⊓ V j))
    (hex : ∃ h : ∀ i, Γ(Y, V i)ˣ, (∀ i, h i ∈ sectionUnits z (V i)) ∧
      ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹) :
    Γ(T, ⊤)ˣ :=
  (exists_globalUnit_sectionEval V (P.iSup_preimage_eq_top hV) hex.choose
    (fun i j => hex.choose_spec.2 i j ▸ hFP i j)).choose

/-- The defining property of `normalizedSplittingEval`, for the splitting it happens to extract
from `hex`. Only an intermediate step: `resUnit_normalizedSplittingEval` upgrades it to every
normalised splitting, which is the statement consumers want. -/
theorem resUnit_normalizedSplittingEval_choose (z P : T ⟶ Y) {ι : Type*} (V : ι → Y.Opens)
    (hV : iSup V = ⊤) (F : ∀ i j, Γ(Y, V i ⊓ V j)ˣ)
    (hFP : ∀ i j, F i j ∈ sectionUnits P (V i ⊓ V j))
    (hex : ∃ h : ∀ i, Γ(Y, V i)ˣ, (∀ i, h i ∈ sectionUnits z (V i)) ∧
      ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹) (i : ι) :
    Scheme.resUnit (le_top : P ⁻¹ᵁ V i ≤ ⊤) (normalizedSplittingEval z P V hV F hFP hex) =
      sectionEval P (V i) (hex.choose i) :=
  (exists_globalUnit_sectionEval V (P.iSup_preimage_eq_top hV) hex.choose
    (fun i j => hex.choose_spec.2 i j ▸ hFP i j)).choose_spec i

end General

/-! ## `AP-D2` on general opens, and the independence of `h(P)` -/

section Bridge

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
variable (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
variable (hz : z ≫ pullback.snd p g = 𝟙 T)
variable {ι : Type*} (V : ι → (pullback p g).Opens) (hV : iSup V = ⊤)
variable {F : ∀ i j, Γ(pullback p g, V i ⊓ V j)ˣ} {h h' : ∀ i, Γ(pullback p g, V i)ˣ}

include hp hz hV in
/-- **(AP-D5 UNIQUENESS on general opens — the loose end of `eq_of_mem_sectionUnits`)** Over a
universally `O`-connected family, two normalised splittings of one cocycle over a cover of the
curve are equal: KM's *"uniquely in the form `f_{i,j} ∘ π = h_i / h_j`"* (p. 88), on the opens the
`h_i` really live on.

`eq_of_mem_sectionUnits` (`WeilPairing/KMNormalisation.lean`) is `AP-D2` on opens of the form
`π ⁻¹ᵁ U`; the `V i` here are arbitrary. The extra step is to glue the ratios `h_i · h_i'⁻¹`, which
agree on overlaps once the cocycle cancels, into a single unit on `⊤` — and `⊤` *is* a preimage of
a base open, so `AP-D2` closes it there.

`hV` is not decorative: with a single `V` that does not cover the curve the conclusion is false
(see the module docstring). -/
theorem eq_of_normalized_splitting
    (hn : ∀ i, h i ∈ sectionUnits z (V i)) (hn' : ∀ i, h' i ∈ sectionUnits z (V i))
    (hsplit : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    (hsplit' : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h' i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h' j))⁻¹) :
    ∀ i, h i = h' i := by
  have hn1 : ∀ i, sectionEval z (V i) (h i) = 1 := fun i => hn i
  have hn1' : ∀ i, sectionEval z (V i) (h' i) = 1 := fun i => hn' i
  obtain ⟨u, hu⟩ := exists_globalUnit_restrict V hV (fun i => h i * (h' i)⁻¹) (fun i j => by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact mul_inv_comm_of_mul_inv_eq ((hsplit i j).symm.trans (hsplit' i j)))
  have hloc : ∀ i, sectionEval z (V i) (Scheme.resUnit (le_top : V i ≤ ⊤) u) = 1 := fun i => by
    rw [hu i, map_mul, map_inv, hn1 i, hn1' i, inv_one, mul_one]
  have hu1 : u ∈ sectionUnits z (⊤ : (pullback p g).Opens) :=
    eq_of_forall_resUnit_eq (fun i => z ⁻¹ᵁ V i) (z.iSup_preimage_eq_top hV) fun i =>
      ((sectionEval_resUnit z (le_top : V i ≤ ⊤) u).symm.trans (hloc i)).trans (map_one _).symm
  have hu0 : u = 1 := eq_of_mem_sectionUnits g hz hp ⊤ hu1 (one_mem _)
  intro i
  have hi := hu i
  rw [hu0, map_one] at hi
  exact mul_inv_eq_one.mp hi.symm

include hp hz hV in
/-- **(AP-D6, independence of `h(P)`)** The unit `h(P)` of Katz–Mazur p. 89 does not depend on
which normalised splitting of the cocycle is used to compute it: if `C` reads `h` along `P` and
`C'` reads `h'` along `P`, and both `h` and `h'` are normalised splittings of the same `F`, then
`C = C'`.

This is `eq_of_normalized_splitting` followed by locality of units (`eq_of_forall_resUnit_eq`,
`WeilPairing/KMPatching.lean`), the traces `P ⁻¹ᵁ V i` covering the base because the `V i` cover
the curve. No hypothesis relates `P` to `z`; the torsion of `P` has already been spent in
producing `hC`, `hC'`. -/
theorem eval_eq_of_normalized_splitting
    (hn : ∀ i, h i ∈ sectionUnits z (V i)) (hn' : ∀ i, h' i ∈ sectionUnits z (V i))
    (hsplit : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    (hsplit' : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h' i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h' j))⁻¹)
    {P : T ⟶ pullback p g} {C C' : Γ(T, ⊤)ˣ}
    (hC : ∀ i, Scheme.resUnit (le_top : P ⁻¹ᵁ V i ≤ ⊤) C = sectionEval P (V i) (h i))
    (hC' : ∀ i, Scheme.resUnit (le_top : P ⁻¹ᵁ V i ≤ ⊤) C' = sectionEval P (V i) (h' i)) :
    C = C' :=
  eq_of_forall_resUnit_eq (fun i => P ⁻¹ᵁ V i) (P.iSup_preimage_eq_top hV) fun i =>
    ((hC i).trans (congrArg (sectionEval P (V i))
      (eq_of_normalized_splitting g hp hz V hV hn hn' hsplit hsplit' i))).trans (hC' i).symm

include hp hz in
/-- **The spec of `h(P)`**: `normalizedSplittingEval` restricts, on the trace `P ⁻¹ᵁ V i`, to the
value along `P` of *any* normalised splitting `h` of the cocycle — not only of the one chosen in
its definition. This is the consumable form of `eval_eq_of_normalized_splitting`: a consumer
holding its own normalised `h_i` (say from `exists_normalized_splitting`) may read `h(P)` off
them. -/
theorem resUnit_normalizedSplittingEval (P : T ⟶ pullback p g)
    (hFP : ∀ i j, F i j ∈ sectionUnits P (V i ⊓ V j))
    (hex : ∃ h : ∀ i, Γ(pullback p g, V i)ˣ, (∀ i, h i ∈ sectionUnits z (V i)) ∧
      ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    (hn : ∀ i, h i ∈ sectionUnits z (V i))
    (hsplit : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹) (i : ι) :
    Scheme.resUnit (le_top : P ⁻¹ᵁ V i ≤ ⊤) (normalizedSplittingEval z P V hV F hFP hex) =
      sectionEval P (V i) (h i) :=
  (resUnit_normalizedSplittingEval_choose z P V hV F hFP hex i).trans
    (congrArg (sectionEval P (V i)) (eq_of_normalized_splitting g hp hz V hV
      hex.choose_spec.1 hn hex.choose_spec.2 hsplit i))

include hp hz in
/-- **The pin**: any global unit restricting to the values along `P` of a normalised splitting *is*
`h(P)`. Together with `resUnit_normalizedSplittingEval` this turns `AP-D6`'s `∃!` — which was
relative to a fixed choice of the `h_i` — into an absolute characterisation. -/
theorem eq_normalizedSplittingEval (P : T ⟶ pullback p g)
    (hFP : ∀ i j, F i j ∈ sectionUnits P (V i ⊓ V j))
    (hex : ∃ h : ∀ i, Γ(pullback p g, V i)ˣ, (∀ i, h i ∈ sectionUnits z (V i)) ∧
      ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    (hn : ∀ i, h i ∈ sectionUnits z (V i))
    (hsplit : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    {C : Γ(T, ⊤)ˣ}
    (hC : ∀ i, Scheme.resUnit (le_top : P ⁻¹ᵁ V i ≤ ⊤) C = sectionEval P (V i) (h i)) :
    C = normalizedSplittingEval z P V hV F hFP hex :=
  eq_of_forall_resUnit_eq (fun i => P ⁻¹ᵁ V i) (P.iSup_preimage_eq_top hV) fun i =>
    (hC i).trans (resUnit_normalizedSplittingEval g hp hz V hV P hFP hex hn hsplit i).symm

end Bridge

/-! ## `h(P)` for the elliptic curve -/

section Curve

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-- **(AP-D5 COMPLETE for the curve — KM p. 88)** For an `N`-torsion section `Q` and an invertible
`M` representing `κ(Q)` trivialised over a cover `W` of the curve with transition units normalised
along the zero section, the splitting units of `AP-D5` can be taken **normalised**:

  `f_{i,j} ∘ [N] = h_i · h_j⁻¹`   with   `h_i ∈ K^×([N]⁻¹(W i))`.

Existence is `exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints`
(`WeilPairing/KMPairing.lean`), the normalisation is `exists_normalized_splitting`
(`WeilPairing/KMNormalisation.lean`), and the bridge between them is `[N] ∘ 0 = 0`
(`zero_comp_mulByHom_baseChange`), which is what makes the *pulled-back* transition units
normalised along the same zero section. -/
theorem exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) :
    ∃ h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ,
      (∀ i, h i ∈ sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
        (mulByN E t N ⁻¹ᵁ W i)) ∧
      ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
          (transitionUnitOfCover M W e i j) =
        Scheme.resUnit (inf_le_left : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
            mulByN E t N ⁻¹ᵁ W i) (h i) *
          (Scheme.resUnit (inf_le_right : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
            mulByN E t N ⁻¹ᵁ W j) (h j))⁻¹ := by
  obtain ⟨h, hh⟩ := exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W e
  exact exists_normalized_splitting (baseChangeZero_snd E.π E.zero E.zero_π t)
    (fun i => mulByN E t N ⁻¹ᵁ W i)
    (iSup_preimage_preimage_eq_top (mulByN E t N) (baseChangeZero E.π E.zero E.zero_π t) hW)
    _ h hh
    (fun i j => mem_sectionUnits_pullback (zero_comp_mulByHom_baseChange E t (N : ℤ))
      (W i ⊓ W j) (hnorm i j))

/-- **(AP-D6 COMPLETE — KM p. 89)** `h(P)` for the elliptic curve: a single unit of
`Γ(T, 𝒪_T^×)` attached to the `N`-torsion sections `Q` — through the invertible `M` representing
`κ(Q)`, its trivialising cover `W` and the trivialisations `e` — and `P`.

Unlike `exists_globalUnit_sectionEval_of_mem_torsionPoints`
(`WeilPairing/KMPatching.lean`), which produces a unit depending on a choice of splitting units,
this is a genuine function of the data: `resUnit_torsionSplittingEval` reads it off *any*
normalised splitting, and `eq_torsionSplittingEval` pins it. `AP-D7` (bilinearity, `μ_N`) consumes
this triple. -/
noncomputable def torsionSplittingEval (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) : Γ(T, ⊤)ˣ :=
  normalizedSplittingEval (baseChangeZero E.π E.zero E.zero_π t)
    (P.1 : T ⟶ pullback E.π t) (fun i => mulByN E t N ⁻¹ᵁ W i)
    ((mulByN E t N).iSup_preimage_eq_top hW)
    (fun i j => Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
      (transitionUnitOfCover M W e i j))
    (fun i j => mem_sectionUnits_pullback (comp_mulByN_eq_baseChangeZero E t N P hP)
      (W i ⊓ W j) (hnorm i j))
    (exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm)

/-- **The spec of `h(P)` for the curve**: whatever normalised splitting units `h_i` of the
pulled-back cocycle one holds, `h(P)` restricts on `P⁻¹([N]⁻¹(W i))` to `h_i ∘ P`. The universal
`O`-connectedness that `AP-D2` needs is free here
(`EllipticCurveGeom.universallyOConnected`), so this carries no hypothesis beyond `AP-D6`'s. -/
theorem resUnit_torsionSplittingEval (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
      (mulByN E t N ⁻¹ᵁ W i))
    (hsplit : ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      Scheme.resUnit (inf_le_left : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W i) (h i) *
        (Scheme.resUnit (inf_le_right : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W j) (h j))⁻¹) (i : ι) :
    Scheme.resUnit (le_top : (P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤)
        (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP) =
      sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i) :=
  resUnit_normalizedSplittingEval t E.toEllipticCurveGeom.universallyOConnected
    (baseChangeZero_snd E.π E.zero E.zero_π t) (fun i => mulByN E t N ⁻¹ᵁ W i)
    ((mulByN E t N).iSup_preimage_eq_top hW) (P.1 : T ⟶ pullback E.π t) _ _ hn hsplit i

/-- **The pin of `h(P)` for the curve**: a global unit of the base restricting to the values along
`P` of a normalised splitting is `h(P)`. This is what identifies the `C` produced by
`exists_globalUnit_sectionEval_of_mem_torsionPoints` (`WeilPairing/KMPatching.lean`) with
`torsionSplittingEval`, once its splitting units are taken normalised. -/
theorem eq_torsionSplittingEval (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
      (mulByN E t N ⁻¹ᵁ W i))
    (hsplit : ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      Scheme.resUnit (inf_le_left : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W i) (h i) *
        (Scheme.resUnit (inf_le_right : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W j) (h j))⁻¹)
    {C : Γ(T, ⊤)ˣ}
    (hC : ∀ i, Scheme.resUnit
        (le_top : (P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤) C =
      sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i)) :
    C = torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP :=
  eq_normalizedSplittingEval t E.toEllipticCurveGeom.universallyOConnected
    (baseChangeZero_snd E.π E.zero E.zero_π t) (fun i => mulByN E t N ⁻¹ᵁ W i)
    ((mulByN E t N).iSup_preimage_eq_top hW) (P.1 : T ⟶ pullback E.π t) _ _ hn hsplit hC

end Curve

end ModularCurves
