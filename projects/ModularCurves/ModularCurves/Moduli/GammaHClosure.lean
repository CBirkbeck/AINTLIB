/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaHMaster

/-!
# The T-H8/T-H9 closure layer: Drinfeld representability from the boxed keystones

**[T-H8-CLOSURE]** (v10.302 closer window). The T-H8 statement
(`gammaFullDrinfeld_representable`, `Moduli/GammaH.lean`) asserts
`(gammaFullDrinfeldProblem R N).Rigid ∧ Representable` for `N ≥ 3` invertible. This file
reduces it to EXACTLY the tracked boxes — nothing else:

* the **Rigid conjunct is a free rider**: `rigid_of_representable` (PROVEN) derives it from
  the Representable conjunct — the L2-parked unrestricted-rigidity wall does NOT touch
  T-H8/T-H9;
* `gammaFullDrinfeldNaiveIso` — the T-D8 dictionary `isFullLevel_iff_naive` packaged as a
  functor isomorphism `Drinfeld ≅ naive` (`N` invertible); carries the T-D8-⟸ box;
* `ModuliProblem.representable_of_iso` — representability transports along functor
  isomorphisms (mathlib `RepresentableBy.ofIso`);
* `gammaFullNaive_rigidNoeth` — the naive problem is noetherian-locally rigid (the PROVEN
  detection + the classical Γ(N) k̄-core `gammaFullNaive_fix_absurd`; carries the
  KM 2.7.2 keystone boxes);
* `gammaFullNaive_affineOverEll` — [GHA4]'s relative representation data is affine
  (finite ⟹ affine);
* **`gammaFullDrinfeld_rigid_and_representable`** — the T-H8 content, gated on exactly
  {T-D8-⟸ (KM), the KM 2.7.2 endomorphism keystones (item 4), the shared KM 4.7.0 engine
  (`representable_iff_rigidNoeth`'s `⇐`)};
* **`gammaOneDrinfeld_rigid_and_representable_of_hbound`** — the T-H9 content at the
  `hbound` register box: {hbound (KM [KEY-DEG]), the engine} and nothing else.

The `GammaH.lean` statements themselves cannot import this file (they sit upstream);
these closure theorems are the library forms of record — downstream consumers should use
them.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- Representability of moduli problems transports along functor isomorphisms
(mathlib `RepresentableBy.ofIso`). -/
theorem ModuliProblem.representable_of_iso {R : CommRingCat.{u}}
    {P Q : ModuliProblem R} (e : P ≅ Q) (hQ : Q.Representable) : P.Representable := by
  obtain ⟨Y, ⟨rep⟩⟩ := hQ.has_representation
  exact ⟨⟨Y, ⟨rep.ofIso e.symm⟩⟩⟩

variable (R : CommRingCat.{u})

/-- **The T-D8 dictionary as a functor isomorphism**: over bases with `N` invertible,
the Drinfeld full-level problem and the naive full-level problem coincide
(`isFullLevel_iff_naive`, carrying the T-D8-⟸ box). Both problems' transition maps are
the same `pullSection` pairs, so naturality is definitional. -/
noncomputable def gammaFullDrinfeldNaiveIso (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    gammaFullDrinfeldProblem R N ≅ gammaFullNaiveProblem R N :=
  NatIso.ofComponents
    (fun X => Equiv.toIso (Equiv.subtypeEquiv (Equiv.refl _) (fun PQ =>
      X.unop.curve.isFullLevel_iff_naive N
        (YFull.nIsInvertible_over_spec R X.unop.structMap hinv) PQ.1 PQ.2)))
    (fun {X Y} f => by
      ext PQ
      exact Subtype.ext rfl)

/-- **The naive full-level problem is noetherian-locally rigid** (`N ≥ 3` invertible):
the PROVEN detection (`exists_isoFibre_ne_refl`) finds a geometric fibre where a
base-identical iso stays nontrivial; the fixed structure transports along the fibre
square; the classical Γ(N) k̄-core (`gammaFullNaive_fix_absurd`) kills. Carries the
KM 2.7.2 keystone boxes (through the k̄-core), no `hLN`. -/
theorem gammaFullNaive_rigidNoeth (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) : (gammaFullNaiveProblem R N).RigidNoeth := by
  intro X hX e he hne a hfix
  haveI := hX
  obtain ⟨k, _, _, t, hfib⟩ := EllObj.exists_isoFibre_ne_refl N hN
    (YFull.nIsInvertible_over_spec R X.structMap hinv) e he hne
  set eT := EllObj.isoFibre e he t with heT
  have hcomp : eT.hom ≫ X.pullbackAlongπ t = X.pullbackAlongπ t ≫ e.hom :=
    EllHom.fibre_pullbackAlongπ e.hom he t
  set aT := (gammaFullNaiveProblem R N).map (X.pullbackAlongπ t).op a with haT
  have hfixT : (gammaFullNaiveProblem R N).map eT.hom.op aT = aT := by
    calc (gammaFullNaiveProblem R N).map eT.hom.op aT
        = (gammaFullNaiveProblem R N).map ((X.pullbackAlongπ t).op ≫ eT.hom.op) a := by
          rw [haT, ← Functor.map_comp_apply]
      _ = (gammaFullNaiveProblem R N).map (e.hom.op ≫ (X.pullbackAlongπ t).op) a := by
          rw [← op_comp, ← op_comp, hcomp]
      _ = (gammaFullNaiveProblem R N).map (X.pullbackAlongπ t).op
            ((gammaFullNaiveProblem R N).map e.hom.op a) := by
          rw [Functor.map_comp_apply]
      _ = aT := by rw [hfix, haT]
  exact gammaFullNaive_fix_absurd N hN hinv k (t ≫ X.structMap) (X.curve.baseChange t)
    eT rfl hfib aT hfixT

/-- **The naive full-level problem is affine over `Ell`** (`N` invertible): [GHA4]'s
relative representation data (`gammaFullNaive_relRepData`) has finite structure maps,
and finite morphisms are affine. -/
theorem gammaFullNaive_affineOverEll (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    (gammaFullNaiveProblem R N).AffineOverEll := by
  intro X
  obtain ⟨d, hfin, het⟩ := gammaFullNaive_relRepData R N hinv X
  haveI := hfin
  exact ⟨d.Z, d.f, inferInstance, @d.eqv, @d.nat⟩

/-- **[T-E9 CONTENT, first half] (Loeffler Prop 3.8.2–3.8.3)** — the closure form of the
`Rigid ∧ Representable` half of `gammaFullNaive_representable` (Representability:646,
YN-side): for `N ≥ 3` invertible the naive full-level problem is rigid and representable,
gated on exactly {KM 2.7.2 keystones, the shared engine}. The smooth-affine conjunct of
T-E9 (an engine-output refinement) is NOT covered here. -/
theorem gammaFullNaive_rigid_and_representable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    (gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable := by
  have hrep : (gammaFullNaiveProblem R N).Representable :=
    (ModuliProblem.representable_iff_rigidNoeth _
      (gammaFullNaive_affineOverEll R N hinv)).mpr
      ⟨(gammaFullNaive_affineOverEll R N hinv).relativelyRepresentable,
       gammaFullNaive_rigidNoeth R N hN hinv⟩
  exact ⟨ModuliProblem.rigid_of_representable hrep, hrep⟩

/-- **[T-H8 CONTENT] (GME Thm 2.6.8 scope; KM 4.7.2/5.1)** — the closure form of
`gammaFullDrinfeld_representable`: for `N ≥ 3` invertible, the Drinfeld full-level
problem is rigid and representable, gated on EXACTLY the tracked boxes:
T-D8-⟸ (through `gammaFullDrinfeldNaiveIso`), the KM 2.7.2 endomorphism keystones
(through `gammaFullNaive_rigidNoeth`), and the shared KM 4.7.0 engine (through
`representable_iff_rigidNoeth`'s `⇐`). The Rigid conjunct is the
`rigid_of_representable` free rider. -/
theorem gammaFullDrinfeld_rigid_and_representable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    (gammaFullDrinfeldProblem R N).Rigid ∧
      (gammaFullDrinfeldProblem R N).Representable := by
  have hnaive : (gammaFullNaiveProblem R N).Representable :=
    (ModuliProblem.representable_iff_rigidNoeth _
      (gammaFullNaive_affineOverEll R N hinv)).mpr
      ⟨(gammaFullNaive_affineOverEll R N hinv).relativelyRepresentable,
       gammaFullNaive_rigidNoeth R N hN hinv⟩
  have hrep : (gammaFullDrinfeldProblem R N).Representable :=
    ModuliProblem.representable_of_iso (gammaFullDrinfeldNaiveIso R N hinv) hnaive
  exact ⟨ModuliProblem.rigid_of_representable hrep, hrep⟩

/-- **[T-H9 CONTENT at the register box]** — the closure form of
`gammaOneDrinfeld_representable`: for `N ≥ 4` invertible, given the KM kernel-degree
keystone `hbound` ([KEY-DEG], KM's ledger), the Drinfeld `Γ₁(N)` problem is rigid and
representable — gated on exactly {`hbound`, the shared engine}. The Rigid conjunct is
the `rigid_of_representable` free rider. -/
theorem gammaOneDrinfeld_rigid_and_representable_of_hbound (N : ℕ) [NeZero N]
    (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    (hbound : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (ε : E.asOver ⟶ E.asOver), η[E.asOver] ≫ ε = η[E.asOver] →
      letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
      letI : CommGroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ E.asOver) := Hom.commGroup
      ε * (𝟙 E.asOver)⁻¹ ≠ 1 →
      ∀ pts : Fin N → E.Point (𝟙 (Spec (CommRingCat.of k))), Function.Injective pts →
        (∀ i, (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) (pts i) ≫
          (ε * (𝟙 E.asOver)⁻¹) = 1) → False) :
    (gammaOneDrinfeldProblem R N).Rigid ∧
      (gammaOneDrinfeldProblem R N).Representable := by
  have hrep : (gammaOneDrinfeldProblem R N).Representable :=
    gammaOneDrinfeld_representable_prep R N hN hinv hbound
  exact ⟨ModuliProblem.rigid_of_representable hrep, hrep⟩

end ModularCurves
