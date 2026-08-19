/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.SectionMarking
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The `ω^{⊗-2}`-valued abscissa difference ([O1], G0's ask-1)

**(STREAM-OMEGA 2026-07-17, CHARTER-O.)** For a pair of fibrewise-nonzero sections of a
geometric elliptic curve, the difference of their marked chart abscissae is
`u²`-covariant under chart comparisons (the marking chase), so it glues to a global
section of the `(−2)`-power of the `ω`-cocycle — the canonical `(ω^{⊗-2})`-valued
abscissa difference `d` of G0's `±ω` scale-torsor over the level-2 locus
(`Spec_W(𝒪[u]/(u² − d))`).

* `markedCoordsAt` — the (unique) marked chart coordinates of a section on an atlas
  chart, from the [hArb-1/2] marking pipeline.
* `abscissaDiff` — the glued section of `(omegaCocycle G).zpow (-2)`.
* `abscissaDiff_res` — its value in any chart: the marked abscissa difference.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation

variable {S : Scheme.{u}} {G : EllipticCurveGeom S}

/-- The marked chart coordinates of a fibrewise-nonzero section on an atlas chart
(unique by `marksAt_coords_unique`). -/
noncomputable def markedCoordsAt {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σ ≠ t ≫ G.zero) (i : G.atlas.ι) :
    Γ(S, (G.atlas.U i).1) × Γ(S, (G.atlas.U i).1) :=
  ⟨((G.atlas.presentation i).marksAt_of_forall_pull_ne_zero hσ hne).choose,
    ((G.atlas.presentation i).marksAt_of_forall_pull_ne_zero hσ hne).choose_spec.choose⟩

theorem markedCoordsAt_marksAt {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σ ≠ t ≫ G.zero) (i : G.atlas.ι) :
    (G.atlas.presentation i).MarksAt hσ (markedCoordsAt hσ hne i).1
      (markedCoordsAt hσ hne i).2 :=
  ((G.atlas.presentation i).marksAt_of_forall_pull_ne_zero hσ hne).choose_spec.choose_spec

variable {σP σQ : S ⟶ G.E}

set_option backward.isDefEq.respectTransparency false in
/-- **([O1] the compatibility)** The marked abscissa differences are `u⁻²`-compatible
across charts: both markings chase through the chart comparison
(`e3_markChase`), and the translation part cancels in the difference. -/
theorem abscissaDiff_compatible (hσP : σP ≫ G.π = 𝟙 S) (hσQ : σQ ≫ G.π = 𝟙 S)
    (hneP : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σP ≠ t ≫ G.zero)
    (hneQ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σQ ≠ t ≫ G.zero) :
    ((omegaCocycle G).zpow (-2)).Compatible ⊤ (fun i =>
      Scheme.resLE (inf_le_right : ⊤ ⊓ ((omegaCocycle G).zpow (-2)).U i ≤ _)
        ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1)) := by
  intro i j
  refine Scheme.ext_of_affine_res S (fun V hV => ?_)
  have hVi : V.1 ≤ (G.atlas.U i).1 := hV.trans (inf_le_left.trans inf_le_right)
  have hVj : V.1 ≤ (G.atlas.U j).1 := hV.trans inf_le_right
  have hVij : V.1 ≤ (G.atlas.U i).1 ⊓ (G.atlas.U j).1 := le_inf hVi hVj
  -- the restricted markings
  have hMPi := (markedCoordsAt_marksAt hσP hneP i).restrict hVi
  have hMPj := (markedCoordsAt_marksAt hσP hneP j).restrict hVj
  have hMQi := (markedCoordsAt_marksAt hσQ hneQ i).restrict hVi
  have hMQj := (markedCoordsAt_marksAt hσQ hneQ j).restrict hVj
  -- the chart comparison chases
  obtain ⟨hxP, -⟩ := e3_markChase hMPi hMPj
  obtain ⟨hxQ, -⟩ := e3_markChase hMQi hMQj
  set C := ((G.atlas.presentation i).restrict hVi).transVC
    ((G.atlas.presentation j).restrict hVj) with hC
  -- the difference transforms by `u²`
  have hdiff : Scheme.resLE hVj ((markedCoordsAt hσQ hneQ j).1
      - (markedCoordsAt hσP hneP j).1)
      = ((C.u : Γ(S, V.1))) ^ 2 * Scheme.resLE hVi
        ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1) := by
    rw [map_sub, map_sub]
    linear_combination hxP - hxQ
  simp only [Scheme.resLE_resLE, map_mul]
  rw [Scheme.resLE_resUnit_val]
  rw [show ((omegaCocycle G).zpow (-2)).u i j
    = ((omegaCocycle G).u i j) ^ (-2 : ℤ) from rfl]
  rw [map_zpow]
  show Scheme.resLE hVi ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1)
    = ((Scheme.resUnit hVij ((omegaCocycle G).u i j) ^ (-2 : ℤ) : Γ(S, V.1)ˣ) :
        Γ(S, V.1))
      * Scheme.resLE hVj ((markedCoordsAt hσQ hneQ j).1
        - (markedCoordsAt hσP hneP j).1)
  rw [omegaCocycle_res G i j V hVij]
  rw [show ((G.atlas.presentation i).restrict (hVij.trans inf_le_left)).transUnit
      ((G.atlas.presentation j).restrict (hVij.trans inf_le_right)) = C.u from rfl]
  rw [hdiff]
  rw [show (C.u ^ (-2 : ℤ)) = ((C.u⁻¹) ^ 2 : Γ(S, V.1)ˣ) from by group]
  rw [show ((((C.u⁻¹) ^ 2 : Γ(S, V.1)ˣ)) : Γ(S, V.1))
      * (((C.u : Γ(S, V.1))) ^ 2 * Scheme.resLE hVi
        ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1))
    = (((C.u⁻¹ * C.u : Γ(S, V.1)ˣ)) : Γ(S, V.1)) ^ 2 * Scheme.resLE hVi
        ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1) from by
    push_cast
    ring]
  simp

/-- **([O1] ★★, G0's ask-1)** The `ω^{⊗-2}`-valued abscissa difference of a pair of
fibrewise-nonzero sections: the global section of the `(−2)`-power `ω`-cocycle whose
chart components are the marked abscissa differences. For a naive level-2 pair this is
the `d` of the `±ω` scale-torsor `Spec_W(𝒪[u]/(u² − d))`. -/
noncomputable def abscissaDiff (hσP : σP ≫ G.π = 𝟙 S) (hσQ : σQ ≫ G.π = 𝟙 S)
    (hneP : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σP ≠ t ≫ G.zero)
    (hneQ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σQ ≠ t ≫ G.zero) :
    ((omegaCocycle G).zpow (-2)).sections ⊤ :=
  ⟨fun i => Scheme.resLE (inf_le_right : ⊤ ⊓ ((omegaCocycle G).zpow (-2)).U i ≤ _)
      ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1),
    abscissaDiff_compatible hσP hσQ hneP hneQ⟩

/-- The chart component of the abscissa difference is the marked abscissa
difference. -/
theorem abscissaDiff_component (hσP : σP ≫ G.π = 𝟙 S) (hσQ : σQ ≫ G.π = 𝟙 S)
    (hneP : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σP ≠ t ≫ G.zero)
    (hneQ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σQ ≠ t ≫ G.zero) (i : G.atlas.ι) :
    (abscissaDiff hσP hσQ hneP hneQ).1 i =
      Scheme.resLE (inf_le_right : ⊤ ⊓ ((omegaCocycle G).zpow (-2)).U i ≤ _)
        ((markedCoordsAt hσQ hneQ i).1 - (markedCoordsAt hσP hneP i).1) :=
  rfl


end ModularCurves
