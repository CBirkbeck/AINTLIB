/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.TorsionFibre
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# The combination-clopen locus in `E[N] ×_S E[N]` (ENGINE AXIOM 2 carrier)

The **de-Weiled carrier** for KM's engine axiom 2 (board v10.266-OMEGA): the locus of
pairs `(P, Q)` of `N`-torsion points all of whose nontrivial combinations `iP + jQ`
avoid the zero section. Over a base with `N` invertible this is a **clopen** subscheme
of the finite étale `E[N] ×_S E[N]`, hence **finite étale over `S`** — with no Weil
pairing anywhere.

* `torsionZero` — the zero section of `E[N] → S`; a clopen immersion (open by
  `IsOpenImmersion.of_flat_of_mono` through `Etale.of_comp`, closed as a section of a
  separated morphism).
* `torsionPair`, `torsionPairπ` — `E[N] ×_S E[N]` and its structure morphism.
* `combinationHom v` (`v : ZMod N × ZMod N`) — the morphism
  `E[N] ×_S E[N] ⟶ E[N]`, `(P, Q) ↦ v₁•P + v₂•Q`, built from the tautological pair of
  points by the universal-point trick (`pointToTorsion`; no group-scheme structure on
  `E[N]` is needed).
* `fullLevelLocus` — the open subscheme on
  `⋂_{v ≠ 0} combinationHom v ⁻¹ (E[N] ∖ zero)`; `fullLevelLocusπ` is finite étale.

The identification of its points with naive full level structures (via
`PairGeneratesOfCardSq` and `torsion_geometricFibre_rank_two`) is the next layer
(`Moduli`-side); this file is the geometry.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### The zero section of `E[N]` -/

/-- The zero section `S ⟶ E[N]` — the torsion point attached to `0 ∈ E(S)`. -/
noncomputable def torsionZero : S ⟶ E.torsion N :=
  E.pointToTorsion (0 : E.Point (𝟙 S))
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 S) N 0).mp (smul_zero _))

@[simp]
theorem torsionZero_torsionπ : E.torsionZero N ≫ E.torsionπ N = 𝟙 S :=
  E.pointToTorsion_torsionπ _ _

@[simp]
theorem torsionZero_torsionι :
    E.torsionZero N ≫ E.torsionι N = ((0 : E.Point (𝟙 S)) : S ⟶ E.E) :=
  E.pointToTorsion_torsionι _ _

/-- The zero section is a closed immersion (section of the separated `torsionπ`). -/
theorem torsionZero_isClosedImmersion : IsClosedImmersion (E.torsionZero N) := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsClosedImmersion (E.torsionZero N ≫ E.torsionπ N) := by
    rw [torsionZero_torsionπ]
    infer_instance
  exact IsClosedImmersion.of_comp (E.torsionZero N) (E.torsionπ N)

/-- The zero section is an open immersion when `N` is invertible: it is étale
(section of the étale `torsionπ`, by postcomposition cancellation), flat and locally
of finite presentation, and a (split) monomorphism. -/
theorem torsionZero_isOpenImmersion (h : NIsInvertible S N) :
    IsOpenImmersion (E.torsionZero N) := by
  haveI het : Etale (E.torsionπ N) := E.torsionπ_etale N h
  haveI : Etale (E.torsionZero N ≫ E.torsionπ N) := by
    rw [torsionZero_torsionπ]
    infer_instance
  haveI : Etale (E.torsionZero N) :=
    Etale.of_comp (E.torsionZero N) (E.torsionπ N)
  haveI : IsSplitMono (E.torsionZero N) :=
    ⟨⟨⟨E.torsionπ N, E.torsionZero_torsionπ N⟩⟩⟩
  exact IsOpenImmersion.of_flat_of_mono _

/-! ### The pair scheme `E[N] ×_S E[N]` and its tautological points -/

/-- The scheme of pairs of `N`-torsion points, `E[N] ×_S E[N]`. -/
noncomputable abbrev torsionPair : Scheme.{u} :=
  pullback (E.torsionπ N) (E.torsionπ N)

/-- The structure morphism `E[N] ×_S E[N] ⟶ S`. -/
noncomputable abbrev torsionPairπ : E.torsionPair N ⟶ S :=
  pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N

theorem torsionPairπ_etale (h : NIsInvertible S N) : Etale (E.torsionPairπ N) := by
  haveI het : Etale (E.torsionπ N) := E.torsionπ_etale N h
  haveI : Etale (pullback.fst (E.torsionπ N) (E.torsionπ N)) :=
    MorphismProperty.pullback_fst _ _ het
  show Etale (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
  infer_instance

theorem torsionPairπ_isFinite : IsFinite (E.torsionPairπ N) := by
  haveI hfin : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsFinite (pullback.fst (E.torsionπ N) (E.torsionπ N)) :=
    MorphismProperty.pullback_fst _ _ hfin
  exact MorphismProperty.comp_mem _ _ _ inferInstance hfin

/-- The first tautological torsion point over `E[N] ×_S E[N]`. -/
noncomputable def torsionPairFst : E.Point (E.torsionPairπ N) :=
  ⟨pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N, by
    rw [Category.assoc, E.torsionι_π]⟩

/-- The second tautological torsion point over `E[N] ×_S E[N]`. -/
noncomputable def torsionPairSnd : E.Point (E.torsionPairπ N) :=
  ⟨pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N, by
    rw [Category.assoc, E.torsionι_π, ← pullback.condition]⟩

theorem torsionPairFst_killed : (N : ℤ) • E.torsionPairFst N = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom]
  show (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) ≫
      E.mulByHom (N : ℤ) = E.torsionPairπ N ≫ E.zero
  rw [Category.assoc]
  rw [show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero from
    pullback.condition]
  rw [← Category.assoc]

theorem torsionPairSnd_killed : (N : ℤ) • E.torsionPairSnd N = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom]
  show (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) ≫
      E.mulByHom (N : ℤ) = E.torsionPairπ N ≫ E.zero
  rw [Category.assoc]
  rw [show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero from
    pullback.condition]
  rw [← Category.assoc, ← pullback.condition]

/-! ### The combination morphisms -/

/-- The `v`-combination of the tautological pair, `v₁•P + v₂•Q`, as a point of `E`
over `E[N] ×_S E[N]`. -/
noncomputable def combinationPoint (v : ZMod N × ZMod N) :
    E.Point (E.torsionPairπ N) :=
  (v.1.val : ℤ) • E.torsionPairFst N + (v.2.val : ℤ) • E.torsionPairSnd N

theorem combinationPoint_killed (v : ZMod N × ZMod N) :
    (N : ℤ) • E.combinationPoint N v = 0 := by
  rw [combinationPoint, smul_add, smul_comm (N : ℤ) (v.1.val : ℤ),
    smul_comm (N : ℤ) (v.2.val : ℤ), E.torsionPairFst_killed, E.torsionPairSnd_killed,
    smul_zero, smul_zero, add_zero]

/-- The combination morphism `E[N] ×_S E[N] ⟶ E[N]`, `(P, Q) ↦ v₁•P + v₂•Q` — the
universal-point trick: the combination of the tautological pair is `N`-killed, so it
factors through the kernel `E[N]`. -/
noncomputable def combinationHom (v : ZMod N × ZMod N) :
    E.torsionPair N ⟶ E.torsion N :=
  E.pointToTorsion (E.combinationPoint N v)
    ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (E.combinationPoint_killed N v))

@[simp]
theorem combinationHom_torsionπ (v : ZMod N × ZMod N) :
    E.combinationHom N v ≫ E.torsionπ N = E.torsionPairπ N :=
  E.pointToTorsion_torsionπ _ _

@[simp]
theorem combinationHom_torsionι (v : ZMod N × ZMod N) :
    E.combinationHom N v ≫ E.torsionι N =
      ((E.combinationPoint N v : E.Point (E.torsionPairπ N)) : _ ⟶ E.E) :=
  E.pointToTorsion_torsionι _ _

/-! ### The full-level locus -/

/-- The full-level set: pairs all of whose nontrivial combinations avoid the zero
section. -/
def fullLevelSet : Set (E.torsionPair N) :=
  ⋂ v ∈ {v : ZMod N × ZMod N | v ≠ 0},
    (E.combinationHom N v).base ⁻¹' (Set.range (E.torsionZero N).base)ᶜ

theorem isClopen_fullLevelSet (h : NIsInvertible S N) :
    IsClopen (E.fullLevelSet N) := by
  have hz : IsClopen (Set.range (E.torsionZero N).base) := by
    constructor
    · exact (E.torsionZero_isClosedImmersion N).isClosedEmbedding.isClosed_range
    · exact (E.torsionZero_isOpenImmersion N h).base_open.isOpen_range
  exact Set.Finite.isClopen_biInter (Set.toFinite _)
    (fun v _ => (hz.compl.preimage (E.combinationHom N v).continuous))

/-- The full-level locus as an open of `E[N] ×_S E[N]`. -/
noncomputable def fullLevelOpens (h : NIsInvertible S N) : (E.torsionPair N).Opens :=
  ⟨E.fullLevelSet N, (E.isClopen_fullLevelSet N h).isOpen⟩

/-- The full-level locus: the open subscheme of `E[N] ×_S E[N]` where every
nontrivial combination avoids the zero section. -/
noncomputable abbrev fullLevelLocus (h : NIsInvertible S N) : Scheme.{u} :=
  E.fullLevelOpens N h

/-- The inclusion of the full-level locus. -/
noncomputable abbrev fullLevelLocusι (h : NIsInvertible S N) :
    E.fullLevelLocus N h ⟶ E.torsionPair N :=
  (E.fullLevelOpens N h).ι

/-- The structure morphism of the full-level locus. -/
noncomputable abbrev fullLevelLocusπ (h : NIsInvertible S N) :
    E.fullLevelLocus N h ⟶ S :=
  E.fullLevelLocusι N h ≫ E.torsionPairπ N

/-- The inclusion of the full-level locus is a closed immersion (an open immersion
with closed range). -/
theorem fullLevelLocusι_isClosedImmersion (h : NIsInvertible S N) :
    IsClosedImmersion (E.fullLevelLocusι N h) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [Scheme.Opens.range_ι]
  exact (E.isClopen_fullLevelSet N h).isClosed

/-- The full-level locus is finite over `S`. -/
theorem fullLevelLocusπ_isFinite (h : NIsInvertible S N) :
    IsFinite (E.fullLevelLocusπ N h) := by
  haveI hpair : IsFinite (E.torsionPairπ N) := E.torsionPairπ_isFinite N
  haveI := E.fullLevelLocusι_isClosedImmersion N h
  haveI : IsFinite (E.fullLevelLocusι N h) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ inferInstance hpair

/-- The full-level locus is étale over `S`. -/
theorem fullLevelLocusπ_etale (h : NIsInvertible S N) :
    Etale (E.fullLevelLocusπ N h) := by
  haveI hpair : Etale (E.torsionPairπ N) := E.torsionPairπ_etale N h
  haveI : IsOpenImmersion (E.fullLevelLocusι N h) :=
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))
  haveI : Etale (E.fullLevelLocusι N h) := inferInstance
  exact inferInstanceAs (Etale (_ ≫ _))

end EllipticCurve

end ModularCurves
