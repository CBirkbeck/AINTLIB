/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMNormalisation
import ModularCurves.WeilPairing.KMPairing

/-!
# `h(P)`: the units `h_i ∘ P` patch (ticket AP-D6, Katz–Mazur p. 89)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 89. `WeilPairing/KMSplitting.lean` and
`WeilPairing/KMNormalisation.lean` produce KM's splitting units `h_i` on the opens
`π⁻¹(U_i)` of the curve, with `f_{i,j} ∘ π = h_i / h_j` (`AP-D5`). KM then evaluates them at a
section `P` killed by `π` and observes, verbatim:

> *over the cover of `S` by `P^{-1}(π^{-1}U_i)`, the `h_i ∘ P` agree on overlaps, in view of the
> relations `f_{i,j} ∈ K^×`, `h_i/h_j = f_{i,j} ∘ π`, `πP = 0`.*

This file is exactly that sentence. The three relations enter as

* `f_{i,j} ∈ K^×` — `hF : F i j ∈ sectionUnits z (U i ⊓ U j)`, normalisation along the zero
  section `z` of the **target** curve (`AP-D1`/`AP-D3`);
* `h_i/h_j = f_{i,j} ∘ π` — `hsplit`, the conclusion of `AP-D5`, verbatim in the shape
  `exists_pullback_transitionUnit_eq_mul_inv` produces it;
* `πP = 0` — `hP : P ≫ π = z`, i.e. the composite `T → Y → X` is the zero section.

and they combine in one line: `P^#(h_i/h_j) = P^# π^# f_{i,j} = (P ≫ π)^# f_{i,j} = z^# f_{i,j} = 1`
(`mem_sectionUnits_pullback`), which is the overlap condition for `exists_globalUnit_restrict`.

## Main results

* `sectionEval_pullback` — the computational core: evaluating a pulled-back unit along `P` is
  evaluating it along `P ≫ π`. This is KM's `(f ∘ π) ∘ P = f ∘ (πP)`.
* `mem_sectionUnits_pullback` — **`πP = 0` transports normalisation**: the pullback along `π` of
  a unit normalised along `z` is normalised along `P`, as soon as `P ≫ π = z`. No hypothesis on
  `π`, `P` or the schemes.
* `eq_of_forall_resUnit_eq` — a global unit is determined by its restrictions to a cover; the
  uniqueness companion of `exists_globalUnit_restrict` (`WeilPairing/KMNormalisation.lean`),
  which is what makes `h(P)` *a single* unit.
* `exists_globalUnit_sectionEval` — the patching in its cover-free core form: if the ratios
  `h_i / h_j` are normalised along `P`, the `h_i ∘ P` glue.
* `exists_globalUnit_sectionEval_of_pullback_split` — **the ticket, generic form**: from KM's
  three relations, `∃! h(P) ∈ Γ(T, 𝒪_T^×)` restricting to `h_i ∘ P` on `P^{-1}(π^{-1}U_i)`.
* `transitionUnitOfCover` — KM's `f_{i,j}` for a family of trivialisations, named so that the
  hypotheses and conclusions of `AP-D5`/`AP-D6` fit on a line.
* `comp_mulByN_eq_baseChangeZero` — `πP = 0` for the curve: an `N`-torsion section composed with
  `[N]` is the zero section, at the level of morphisms.
* `exists_globalUnit_sectionEval_of_mem_torsionPoints` — **the ticket for the elliptic curve**:
  for `Q, P` both `N`-torsion and `M` an invertible sheaf representing `κ(Q)` trivialised over a
  cover of the curve with normalised transition units, the `AP-D5` splitting units exist and
  their values along `P` glue to a single `h(P) ∈ Γ(T, 𝒪_T^×)`.

## What is *not* used

Neither half of Abel is used, so nothing here inherits the `sorry` of
`exists_torsionPoint_of_mem_kerMulByN` (`WeilPairing/KMPairing.lean`); only the proved `⊆`
direction of `AP-D4` enters, through `AP-D5`. Nor is `UniversallyOConnected` needed: `AP-D2`
governs *uniqueness of the `h_i`*, not their evaluation. In particular **the `h_i` need not be
normalised** — KM's normalisation of the `h_i` (`AP-D5`, `exists_normalized_splitting`) is not a
hypothesis of any statement here; only the `f_{i,j}` must be normalised, and that is what `πP = 0`
converts into the overlap condition.

## Degenerate cases and the shape of the cover

The `W i` must be a trivialising cover of the **curve**, not preimages of base opens: `κ(Q)` is
fibrewise nontrivial, so a trivialisation over `π ⁻¹ᵁ (U i)` exists only degenerately (see
`WeilPairing/KMNormalisation.lean`, "Degenerate cases"). The opens that cover the *base* appear
only here, as the traces `P ⁻¹ᵁ (π ⁻¹ᵁ W i)` — which is precisely KM's "cover of `S` by
`P^{-1}(π^{-1}U_i)`". For an empty index type the covering hypothesis forces `T = ∅` and the
conclusion is the trivial unit group.

`h(P)` is unique *given* the splitting units `h_i` (`eq_of_forall_resUnit_eq`). Its independence
of the choice of the `h_i` is a separate statement: it needs uniqueness of the normalised `h_i` on
**general** opens of the curve, which is still open and documented at `eq_of_mem_sectionUnits`
(`WeilPairing/KMNormalisation.lean`). Nothing below assumes it.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-! ## `πP = 0`: evaluating a pulled-back unit along a section -/

section Core

variable {X Y T : Scheme.{u}}

/-- **(KM p. 89, `(f ∘ π) ∘ P = f ∘ (πP)`)** Evaluating the `π`-pullback of a unit along a
section `P` of the source is evaluating the unit itself along the composite `P ≫ π`. Both sides
live on `P ⁻¹ᵁ (π ⁻¹ᵁ U) = (P ≫ π) ⁻¹ᵁ U`, which is a definitional equality of opens, so no
transport is needed. -/
theorem sectionEval_pullback (π : Y ⟶ X) (P : T ⟶ Y) (U : X.Opens) (u : Γ(X, U)ˣ) :
    sectionEval P (π ⁻¹ᵁ U) (Units.map (π.app U).hom.toMonoidHom u) =
      sectionEval (P ≫ π) U u := by
  apply Units.ext
  show (P.app (π ⁻¹ᵁ U)).hom ((π.app U).hom (u : Γ(X, U))) = ((P ≫ π).app U).hom (u : Γ(X, U))
  rw [Scheme.Hom.comp_app]
  rfl

/-- **(KM p. 89, the relation `πP = 0` at work)** If `P` is killed by `π`, i.e. `P ≫ π` is the
zero section `z` of the target, then pulling back along `π` carries units normalised along `z`
to units normalised along `P`: `(f ∘ π) ∘ P = f ∘ 0 = 1`.

This is the only place the torsion of `P` is used, and it is used for nothing else. -/
theorem mem_sectionUnits_pullback {π : Y ⟶ X} {P : T ⟶ Y} {z : T ⟶ X} (hP : P ≫ π = z)
    (U : X.Opens) {u : Γ(X, U)ˣ} (hu : u ∈ sectionUnits z U) :
    Units.map (π.app U).hom.toMonoidHom u ∈ sectionUnits P (π ⁻¹ᵁ U) := by
  have key : sectionEval (P ≫ π) U u = 1 := by rw [hP]; exact hu
  exact (sectionEval_pullback π P U u).trans key

/-! ## The patching -/

/-- **Units are determined locally.** A global unit is pinned by its restrictions to an open
cover — the uniqueness companion of `exists_globalUnit_restrict`
(`WeilPairing/KMNormalisation.lean`), and what makes KM's `h(P)` *a single* unit. Proved from the
separatedness axiom for `𝒪` alone. -/
theorem eq_of_forall_resUnit_eq {Z : Scheme.{u}} {ι : Type*} (V : ι → Z.Opens) (hV : iSup V = ⊤)
    {C C' : Γ(Z, ⊤)ˣ}
    (h : ∀ i, Scheme.resUnit (le_top : V i ≤ ⊤) C = Scheme.resUnit (le_top : V i ≤ ⊤) C') :
    C = C' := by
  apply Units.ext
  exact TopCat.Sheaf.eq_of_locally_eq' Z.sheaf V ⊤ (fun _ => homOfLE le_top) (by rw [hV]) _ _
    (fun i => congrArg Units.val (h i))

/-- **(AP-D6, core)** Units `h_i` on opens `V i` of the total space, whose ratios `h_i / h_j` are
normalised along a section `P` whose traces `P ⁻¹ᵁ (V i)` cover the base, have values `h_i ∘ P`
that glue to a single unit of the base.

The hypothesis `hnorm` is what KM's three relations produce
(`mul_inv_mem_sectionUnits_of_pullback_split`); the gluing itself is
`exists_globalUnit_restrict`. -/
theorem exists_globalUnit_sectionEval {P : T ⟶ Y} {ι : Type*} (V : ι → Y.Opens)
    (hV : ⨆ i, P ⁻¹ᵁ V i = ⊤) (h : ∀ i, Γ(Y, V i)ˣ)
    (hnorm : ∀ i j, Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹ ∈ sectionUnits P (V i ⊓ V j)) :
    ∃ C : Γ(T, ⊤)ˣ, ∀ i,
      Scheme.resUnit (le_top : P ⁻¹ᵁ V i ≤ ⊤) C = sectionEval P (V i) (h i) :=
  exists_globalUnit_restrict (fun i => P ⁻¹ᵁ V i) hV (fun i => sectionEval P (V i) (h i))
    (fun i j => sectionEval_eq_of_mem_sectionUnits P rfl (hnorm i j))

/-- **(KM p. 89, the three relations combined)** If the transition unit `f_{i,j}` is normalised
along the zero section `z` of the target, if it splits as `f_{i,j} ∘ π = h_i / h_j`, and if
`πP = 0`, then the ratio `h_i / h_j` is normalised along `P`.

`h_i / h_j` is read on `π ⁻¹ᵁ W₁ ⊓ π ⁻¹ᵁ W₂`, which is definitionally `π ⁻¹ᵁ (W₁ ⊓ W₂)`. -/
theorem mul_inv_mem_sectionUnits_of_pullback_split {π : Y ⟶ X} {P : T ⟶ Y} {z : T ⟶ X}
    (hP : P ≫ π = z) {W₁ W₂ : X.Opens} {F : Γ(X, W₁ ⊓ W₂)ˣ}
    (hF : F ∈ sectionUnits z (W₁ ⊓ W₂)) {h₁ : Γ(Y, π ⁻¹ᵁ W₁)ˣ} {h₂ : Γ(Y, π ⁻¹ᵁ W₂)ˣ}
    (hsplit : Units.map (π.app (W₁ ⊓ W₂)).hom.toMonoidHom F =
      Scheme.resUnit (π.preimage_mono (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) h₁ *
        (Scheme.resUnit (π.preimage_mono (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) h₂)⁻¹) :
    Scheme.resUnit (inf_le_left : π ⁻¹ᵁ W₁ ⊓ π ⁻¹ᵁ W₂ ≤ π ⁻¹ᵁ W₁) h₁ *
        (Scheme.resUnit (inf_le_right : π ⁻¹ᵁ W₁ ⊓ π ⁻¹ᵁ W₂ ≤ π ⁻¹ᵁ W₂) h₂)⁻¹ ∈
      sectionUnits P (π ⁻¹ᵁ W₁ ⊓ π ⁻¹ᵁ W₂) := by
  have hmem := mem_sectionUnits_pullback hP (W₁ ⊓ W₂) hF
  rw [hsplit] at hmem
  exact hmem

/-- **(AP-D6 — KM p. 89)** Let `π : Y ⟶ X` be a morphism, `z : T ⟶ X` a section of the target and
`P : T ⟶ Y` a section of the source with `πP = 0`, i.e. `P ≫ π = z`. Let `W i` be opens of `X`
whose traces `P ⁻¹ᵁ (π ⁻¹ᵁ W i)` cover `T`, let `F i j` be units on `W i ⊓ W j` **normalised along
`z`**, and suppose they split after pullback,

  `π^# (F i j) = h_i · h_j⁻¹`   on `π ⁻¹ᵁ (W i ⊓ W j)`.

Then the values `h_i ∘ P` glue to a **single** unit `h(P) ∈ Γ(T, 𝒪_T^×)` of the base.

This is Katz–Mazur p. 89 verbatim; `hF`, `hsplit`, `hP` are their `f_{i,j} ∈ K^×`,
`h_i/h_j = f_{i,j} ∘ π`, `πP = 0`, and `hW` is their cover of `S` by the `P^{-1}(π^{-1}U_i)`
(supplied by `iSup_preimage_preimage_eq_top` from a cover of `X`). The `h_i` are *not* assumed
normalised. -/
theorem exists_globalUnit_sectionEval_of_pullback_split {π : Y ⟶ X} {P : T ⟶ Y} {z : T ⟶ X}
    (hP : P ≫ π = z) {ι : Type*} (W : ι → X.Opens) (hW : ⨆ i, P ⁻¹ᵁ (π ⁻¹ᵁ W i) = ⊤)
    (F : ∀ i j, Γ(X, W i ⊓ W j)ˣ) (hF : ∀ i j, F i j ∈ sectionUnits z (W i ⊓ W j))
    (h : ∀ i, Γ(Y, π ⁻¹ᵁ W i)ˣ)
    (hsplit : ∀ i j, Units.map (π.app (W i ⊓ W j)).hom.toMonoidHom (F i j) =
      Scheme.resUnit (π.preimage_mono (inf_le_left : W i ⊓ W j ≤ W i)) (h i) *
        (Scheme.resUnit (π.preimage_mono (inf_le_right : W i ⊓ W j ≤ W j)) (h j))⁻¹) :
    ∃! C : Γ(T, ⊤)ˣ, ∀ i,
      Scheme.resUnit (le_top : P ⁻¹ᵁ (π ⁻¹ᵁ W i) ≤ ⊤) C = sectionEval P (π ⁻¹ᵁ W i) (h i) := by
  obtain ⟨C, hC⟩ := exists_globalUnit_sectionEval (fun i => π ⁻¹ᵁ W i) hW h
    (fun i j => mul_inv_mem_sectionUnits_of_pullback_split hP (hF i j) (hsplit i j))
  exact ⟨C, hC, fun C' hC' =>
    eq_of_forall_resUnit_eq (fun i => P ⁻¹ᵁ (π ⁻¹ᵁ W i)) hW (fun i => (hC' i).trans (hC i).symm)⟩

/-- **KM's `f_{i,j}`**: the transition unit on `W i ⊓ W j` of a family of trivialisations of `M`
over the opens `W i`. Definitionally the term the `AP-D5` statements spell out
(`WeilPairing/KMSplitting.lean`, `WeilPairing/KMPairing.lean`); named so that the `AP-D6`
hypotheses and conclusions fit on a line. -/
noncomputable def transitionUnitOfCover (M : X.Modules) {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i))) (i j : ι) :
    Γ(X, W i ⊓ W j)ˣ :=
  trivializationTransitionUnit (W i ⊓ W j)
    (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (e i)
      (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
    (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (e j)
      (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))))

end Core

/-! ## `h(P)` for the elliptic curve -/

section Curve

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

omit [IsSeparated E.π] in
/-- **(KM's `πP = 0`, for the curve)** An `N`-torsion section composed with `[N]` is the zero
section, as morphisms `T ⟶ E ×_S T`. This is `smul_eq_zero_iff_comp_mulByHom` read through the
`pullback E.π t` presentation of the base-changed curve. -/
theorem comp_mulByN_eq_baseChangeZero (N : ℕ) (P : (E.baseChange t).Point (𝟙 T))
    (hP : P ∈ torsionPoints E t N) :
    (P.1 : T ⟶ pullback E.π t) ≫ mulByN E t N = baseChangeZero E.π E.zero E.zero_π t := by
  have h := (EllipticCurve.smul_eq_zero_iff_comp_mulByHom (E.baseChange t) (𝟙 T) N P).mp hP
  rw [Category.id_comp] at h
  exact h

/-- **(AP-D6 COMPLETE — KM pp. 88–89)** Let `Q` be an `N`-torsion section, `M` an invertible sheaf
representing `κ(Q)`, trivialised over opens `W i` covering the curve, with transition units
`f_{i,j} = transitionUnitOfCover M W e i j` **normalised along the zero section**. Let `P` be a
second `N`-torsion section. Then there are splitting units `h_i` on `[N]⁻¹(W i)` with

  `f_{i,j} ∘ [N] = h_i · h_j⁻¹`,

and their values along `P` glue to a **single** `h(P) ∈ Γ(T, 𝒪_T^×)`, with
`h(P)|_{P^{-1}([N]^{-1}W i)} = h_i ∘ P`.

Existence of the `h_i` is `exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints`
(`WeilPairing/KMPairing.lean`, i.e. the proved `⊆` half of `AP-D4` fed into `AP-D5`); the patching
is `exists_globalUnit_sectionEval_of_pullback_split`, whose `πP = 0` input is the torsion of `P`
via `comp_mulByN_eq_baseChangeZero`. The two torsion hypotheses play completely different roles:
`hQ` produces the splitting, `hP` makes it evaluable.

A consumer already holding its own `h_i` — for instance the *normalised* ones of
`exists_normalized_pullback_transitionUnit_eq_mul_inv` — should use
`exists_globalUnit_sectionEval_of_pullback_split` together with `comp_mulByN_eq_baseChangeZero`
directly. -/
theorem exists_globalUnit_sectionEval_of_mem_torsionPoints (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    ∃ h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ,
      (∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
            (transitionUnitOfCover M W e i j) =
          Scheme.resUnit ((mulByN E t N).preimage_mono (inf_le_left : W i ⊓ W j ≤ W i)) (h i) *
            (Scheme.resUnit ((mulByN E t N).preimage_mono
              (inf_le_right : W i ⊓ W j ≤ W j)) (h j))⁻¹) ∧
        ∃! C : Γ(T, ⊤)ˣ, ∀ i,
          Scheme.resUnit (le_top : (P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤) C =
            sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i) := by
  obtain ⟨h, hh⟩ := exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W e
  refine ⟨h, hh, ?_⟩
  exact exists_globalUnit_sectionEval_of_pullback_split
    (comp_mulByN_eq_baseChangeZero E t N P hP) W
    (iSup_preimage_preimage_eq_top (mulByN E t N) (P.1 : T ⟶ pullback E.π t) hW)
    (transitionUnitOfCover M W e) hnorm h hh

end Curve

end ModularCurves
