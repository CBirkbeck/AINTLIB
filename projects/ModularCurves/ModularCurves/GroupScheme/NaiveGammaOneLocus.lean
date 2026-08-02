/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TorsionCombination

/-!
# The naive `Γ₁(N)` locus in `E[N]` (WP-D1c-rel)

`GroupScheme/TorsionCombination.lean` builds the full-level locus as the clopen subscheme of
`E[N] ×_S E[N]` where **every** nontrivial combination `v₁P + v₂Q` avoids the zero section.
This file is the one-generator mirror: the clopen subscheme of `E[N]` where every proper
multiple `aP`, `0 < a < N`, avoids the zero section — i.e. where the tautological point has
exact order `N` in the **naive** (geometric-pointwise) sense.

That is deliberate. `gammaOneNaiveProblem` (`Moduli/Representability.lean`) is stated with
`IsNaiveGammaOne`, not with the Drinfeld `Section.HasExactOrder`, so the naive locus is the
one it needs — and using it **avoids register box T-D6**
(`Section.hasExactOrder_of_geometric`, still a `sorry`), which the Drinfeld route through
`exists_exactOrderLocus` would have pulled in.

Everything mirrors `TorsionCombination`: the multiple morphisms `multipleHom` replace
`combinationHom`, and finiteness/étaleness of the locus come from the same two facts — the
zero section of `E[N] → S` is clopen when `N` is invertible, and `E[N] → S` is finite étale.

The payoff (WP-D1c) is that the forgetful map `fullLevelLocus ⟶ naiveGammaOneLocus` is then
finite étale by `Etale.of_comp`, with no further input.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### The tautological torsion point and its multiples -/

/-- The tautological torsion point over `E[N]`. -/
noncomputable def torsionTaut : E.Point (E.torsionπ N) :=
  ⟨E.torsionι N, E.torsionι_π N⟩

theorem torsionTaut_killed : (N : ℤ) • E.torsionTaut N = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom]
  show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero
  exact pullback.condition

/-- The `a`-th multiple of the tautological point, as a point of `E` over `E[N]`. -/
noncomputable def multiplePoint (a : ℕ) : E.Point (E.torsionπ N) :=
  (a : ℤ) • E.torsionTaut N

theorem multiplePoint_killed (a : ℕ) : (N : ℤ) • E.multiplePoint N a = 0 := by
  rw [multiplePoint, smul_comm (N : ℤ) (a : ℤ), E.torsionTaut_killed, smul_zero]

/-- The multiplication morphism `E[N] ⟶ E[N]`, `P ↦ a • P` — the universal-point trick:
the multiple of the tautological point is `N`-killed, so it factors through the kernel. -/
noncomputable def multipleHom (a : ℕ) : E.torsion N ⟶ E.torsion N :=
  E.pointToTorsion (E.multiplePoint N a)
    ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (E.multiplePoint_killed N a))

@[simp]
theorem multipleHom_torsionπ (a : ℕ) :
    E.multipleHom N a ≫ E.torsionπ N = E.torsionπ N :=
  E.pointToTorsion_torsionπ _ _

@[simp]
theorem multipleHom_torsionι (a : ℕ) :
    E.multipleHom N a ≫ E.torsionι N =
      ((E.multiplePoint N a : E.Point (E.torsionπ N)) : _ ⟶ E.E) :=
  E.pointToTorsion_torsionι _ _

/-! ### The naive `Γ₁(N)` locus -/

/-- The naive `Γ₁(N)` set: torsion points all of whose proper multiples avoid the zero
section. -/
def naiveGammaOneSet : Set (E.torsion N) :=
  ⋂ a ∈ {a : ℕ | 0 < a ∧ a < N},
    (E.multipleHom N a).base ⁻¹' (Set.range (E.torsionZero N).base)ᶜ

theorem isClopen_naiveGammaOneSet (h : NIsInvertible S N) :
    IsClopen (E.naiveGammaOneSet N) := by
  have hz : IsClopen (Set.range (E.torsionZero N).base) := by
    constructor
    · exact (E.torsionZero_isClosedImmersion N).isClosedEmbedding.isClosed_range
    · exact (E.torsionZero_isOpenImmersion N h).base_open.isOpen_range
  refine Set.Finite.isClopen_biInter (Set.Finite.subset (Set.finite_Iio N) ?_)
    (fun a _ => (hz.compl.preimage (E.multipleHom N a).continuous))
  exact fun a ha => ha.2

/-- The naive `Γ₁(N)` locus as an open of `E[N]`. -/
noncomputable def naiveGammaOneOpens (h : NIsInvertible S N) : (E.torsion N).Opens :=
  ⟨E.naiveGammaOneSet N, (E.isClopen_naiveGammaOneSet N h).isOpen⟩

/-- **(WP-D1c-rel)** The naive `Γ₁(N)` locus: the open subscheme of `E[N]` where every
proper multiple of the tautological point avoids the zero section. -/
noncomputable abbrev naiveGammaOneLocus (h : NIsInvertible S N) : Scheme.{u} :=
  E.naiveGammaOneOpens N h

/-- The inclusion of the naive `Γ₁(N)` locus. -/
noncomputable abbrev naiveGammaOneLocusι (h : NIsInvertible S N) :
    E.naiveGammaOneLocus N h ⟶ E.torsion N :=
  (E.naiveGammaOneOpens N h).ι

/-- The structure morphism of the naive `Γ₁(N)` locus. -/
noncomputable abbrev naiveGammaOneLocusπ (h : NIsInvertible S N) :
    E.naiveGammaOneLocus N h ⟶ S :=
  E.naiveGammaOneLocusι N h ≫ E.torsionπ N

/-- The inclusion is a closed immersion (an open immersion with closed range). -/
theorem naiveGammaOneLocusι_isClosedImmersion (h : NIsInvertible S N) :
    IsClosedImmersion (E.naiveGammaOneLocusι N h) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [Scheme.Opens.range_ι]
  exact (E.isClopen_naiveGammaOneSet N h).isClosed

/-- **(WP-D1c-rel)** The naive `Γ₁(N)` locus is finite over the base. -/
theorem naiveGammaOneLocusπ_isFinite (h : NIsInvertible S N) :
    IsFinite (E.naiveGammaOneLocusπ N h) := by
  haveI htor : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI := E.naiveGammaOneLocusι_isClosedImmersion N h
  haveI : IsFinite (E.naiveGammaOneLocusι N h) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ inferInstance htor

/-- **(WP-D1c-rel)** The naive `Γ₁(N)` locus is étale over the base — the fact that makes
the forgetful map `Y(N) ⟶ Y₁(N)` étale, via `Etale.of_comp`. -/
theorem naiveGammaOneLocusπ_etale (h : NIsInvertible S N) :
    Etale (E.naiveGammaOneLocusπ N h) := by
  haveI htor : Etale (E.torsionπ N) := E.torsionπ_etale N h
  haveI : IsOpenImmersion (E.naiveGammaOneLocusι N h) :=
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))
  haveI : Etale (E.naiveGammaOneLocusι N h) := inferInstance
  exact inferInstanceAs (Etale (_ ≫ _))

/-! ### The relative forgetful map `fullLevelLocus ⟶ naiveGammaOneLocus` (WP-D1c-rel)

The full-level condition specialises to the `Γ₁` condition by taking the combination
`v = (a, 0)`: if *every* nontrivial `v₁P + v₂Q` avoids the zero section then in particular
every `aP` with `0 < a < N` does. So the first projection carries `fullLevelSet` into
`naiveGammaOneSet` — no counting argument is needed at this level (WP-D1a's counting is what
the *moduli-problem* morphism needs, which is a statement about level structures, not loci).
-/

/-- The `(a, 0)`-combination is the `a`-th multiple of the first coordinate. -/
theorem combinationHom_fst (a : ℕ) :
    E.combinationHom N ((a : ZMod N), 0) =
      pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.multipleHom N (a : ZMod N).val := by
  refine pullback.hom_ext ?_ ?_
  · show E.combinationHom N _ ≫ E.torsionι N = _ ≫ E.torsionι N
    rw [E.combinationHom_torsionι, Category.assoc, E.multipleHom_torsionι]
    show ((E.combinationPoint N ((a : ZMod N), 0) : E.Point (E.torsionPairπ N)) : _ ⟶ E.E) =
      pullback.fst (E.torsionπ N) (E.torsionπ N) ≫
        ((E.multiplePoint N (a : ZMod N).val : E.Point (E.torsionπ N)) : _ ⟶ E.E)
    rw [combinationPoint, multiplePoint, torsionTaut]
    show _ = pullback.fst (E.torsionπ N) (E.torsionπ N) ≫
      (((((a : ZMod N).val : ℤ) • (⟨E.torsionι N, E.torsionι_π N⟩ :
        E.Point (E.torsionπ N))) : E.Point (E.torsionπ N)) : _ ⟶ E.E)
    rw [ZMod.val_zero, Nat.cast_zero, zero_smul, add_zero,
      E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy]
    show (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) ≫ _ =
      pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N ≫ _
    rw [Category.assoc]
  · show E.combinationHom N _ ≫ E.torsionπ N = _ ≫ E.torsionπ N
    rw [E.combinationHom_torsionπ, Category.assoc, E.multipleHom_torsionπ]

/-- The first projection carries the full-level locus into the naive `Γ₁(N)` locus:
specialise the full-level condition to the combination `v = (a, 0)`. -/
theorem fullLevelSet_subset_preimage_naiveGammaOneSet (h : NIsInvertible S N) :
    Set.range (E.fullLevelLocusι N h ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)).base ⊆
      Set.range (E.naiveGammaOneLocusι N h).base := by
  rw [Scheme.Opens.range_ι]
  rintro y ⟨x, rfl⟩
  have hx : (E.fullLevelLocusι N h).base x ∈ E.fullLevelSet N := by
    have := Set.mem_range_self (f := (E.fullLevelLocusι N h).base) x
    rwa [Scheme.Opens.range_ι] at this
  simp only [fullLevelSet, Set.mem_iInter₂] at hx
  show (E.fullLevelLocusι N h ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)).base x
      ∈ E.naiveGammaOneSet N
  refine Set.mem_iInter₂.mpr ?_
  rintro a ⟨ha0, haN⟩
  have hane : ((a : ZMod N), (0 : ZMod N)) ≠ 0 := by
    intro hz
    have h1 : (a : ZMod N) = 0 := congrArg Prod.fst hz
    have h2 : (a : ZMod N).val = 0 := by rw [h1]; simp
    rw [ZMod.val_natCast_of_lt haN] at h2
    omega
  have hval : ((a : ZMod N)).val = a := ZMod.val_natCast_of_lt haN
  have hmem := hx ((a : ZMod N), (0 : ZMod N)) hane
  rw [E.combinationHom_fst N a, hval] at hmem
  exact hmem

/-- **(WP-D1c-rel)** The relative level-forgetting map `fullLevelLocus ⟶ naiveGammaOneLocus`,
`(P, Q) ↦ P`. -/
noncomputable def fullLevelToNaiveGammaOne (h : NIsInvertible S N) :
    E.fullLevelLocus N h ⟶ E.naiveGammaOneLocus N h :=
  IsOpenImmersion.lift (E.naiveGammaOneLocusι N h)
    (E.fullLevelLocusι N h ≫ pullback.fst (E.torsionπ N) (E.torsionπ N))
    (E.fullLevelSet_subset_preimage_naiveGammaOneSet N h)

@[simp] theorem fullLevelToNaiveGammaOne_ι (h : NIsInvertible S N) :
    E.fullLevelToNaiveGammaOne N h ≫ E.naiveGammaOneLocusι N h =
      E.fullLevelLocusι N h ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The forgetful map lies over the base. -/
theorem fullLevelToNaiveGammaOne_π (h : NIsInvertible S N) :
    E.fullLevelToNaiveGammaOne N h ≫ E.naiveGammaOneLocusπ N h =
      E.fullLevelLocusπ N h := by
  rw [naiveGammaOneLocusπ, ← Category.assoc, E.fullLevelToNaiveGammaOne_ι N h,
    Category.assoc]

/-- **(WP-D1c-rel, the payoff)** The relative level-forgetting map is étale. Both loci are
étale over `S`, so this is pure cancellation (`Etale.of_comp`) — no new input. -/
theorem fullLevelToNaiveGammaOne_etale (h : NIsInvertible S N) :
    Etale (E.fullLevelToNaiveGammaOne N h) := by
  haveI hg : Etale (E.naiveGammaOneLocusπ N h) := E.naiveGammaOneLocusπ_etale N h
  haveI : Etale (E.fullLevelToNaiveGammaOne N h ≫ E.naiveGammaOneLocusπ N h) := by
    rw [E.fullLevelToNaiveGammaOne_π N h]
    exact E.fullLevelLocusπ_etale N h
  exact Etale.of_comp _ (E.naiveGammaOneLocusπ N h)

/-- **(WP-D1c-rel)** The relative level-forgetting map is finite. -/
theorem fullLevelToNaiveGammaOne_isFinite (h : NIsInvertible S N) :
    IsFinite (E.fullLevelToNaiveGammaOne N h) := by
  haveI hg : IsFinite (E.naiveGammaOneLocusπ N h) := E.naiveGammaOneLocusπ_isFinite N h
  haveI : IsFinite (E.fullLevelToNaiveGammaOne N h ≫ E.naiveGammaOneLocusπ N h) := by
    rw [E.fullLevelToNaiveGammaOne_π N h]
    exact E.fullLevelLocusπ_isFinite N h
  exact IsFinite.of_comp _ (E.naiveGammaOneLocusπ N h)

end EllipticCurve

end ModularCurves
