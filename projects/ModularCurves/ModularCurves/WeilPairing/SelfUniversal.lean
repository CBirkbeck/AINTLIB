/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.AlternationReduction
import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.AdditionBaseChange

/-!
# Alternation via the universal Weierstrass family (AP-E4a, skeleton)

`weilPairingEval_self` (`e_N(x,x) = 1`, arbitrary base) by reduction to the universal
case, per the plan validated 2026-08-10 (ChatGPT 5.6 consultation; see
`.mathlib-quality/decomposition-e4a-self.md`):

1. **Transport** (U1): the pairing is invariant under pointed isomorphisms of elliptic
   records over the same base — the `φ`-sibling of `torsionSplittingEval_restrictBase`
   and `torsionSplittingEval_mulByN_pullback` (the `localPullback` gadgets are already
   `f`-generic).
2. **Classification** (U2/U3): `localModel` presents `(E, x)` affine-locally as a
   Weierstrass model pair; `classifyRingHomU`/`universalWeierstrassLocU_map_classifyRingHomU`
   present every model as a base change of the universal curve `𝕌`; sheaf-gluing of the
   value plus the proved base-change naturality reduce alternation to the tautological
   `N`-torsion point over `X_N := (modelEllipticCurve 𝕌).torsion N`.
3. **Universal vanishing** (U4): `X_N = Spec B` is affine, `B` is `ℤ`-flat, so
   `B ↪ B[1/N]`; `B[1/N]` embeds in the torsion algebra of the generic fibre, which is
   finite étale over a field, hence reduced; the value − 1 vanishes at every residue
   field of `B[1/N]` by the field leaf, hence is zero.
4. **Field leaf** (U5, the API gap with its own sub-development): alternation over a
   field with `N` invertible, via the translation characterisation
   (`eq_mul_globalTwist_of_translate` on the KM side, `weilPairing_spec` on the
   HasseWeil side) and HasseWeil's proved `weilPairing_self`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- **(U1, the transport theorem — `φ`-sibling of the base-change naturality)** The
pairing is invariant under pointed isomorphisms of elliptic records over the same
base. -/
theorem weilPairingEval_mapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {N : ℕ} [NeZero N]
    {T : Scheme.{u}} {g : T ⟶ S} (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : (Point.mapIso φ x).1 ≫ F.mulByHom N = g ≫ F.zero)
    (hy' : (Point.mapIso φ y).1 ≫ F.mulByHom N = g ≫ F.zero) :
    (F.weilPairingEval (Point.mapIso φ x) (Point.mapIso φ y) hx' hy' : Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) := by
  have hsndx : ((EllipticCurve.Point.asSection E g x).1 ≫ (pullbackMapIso φ g).hom) ≫
      pullback.snd F.π g = 𝟙 T := by
    rw [asSection_mapIso φ x]
    exact (EllipticCurve.Point.asSection F g (Point.mapIso φ x)).2
  have hsndy : ((EllipticCurve.Point.asSection E g y).1 ≫ (pullbackMapIso φ g).hom) ≫
      pullback.snd F.π g = 𝟙 T := by
    rw [asSection_mapIso φ y]
    exact (EllipticCurve.Point.asSection F g (Point.mapIso φ y)).2
  have hpx : EllipticCurve.Point.asSection F g (Point.mapIso φ x) =
      (⟨(EllipticCurve.Point.asSection E g x).1 ≫ (pullbackMapIso φ g).hom, hsndx⟩ :
        (F.baseChange g).Point (𝟙 T)) := Subtype.ext (asSection_mapIso φ x).symm
  have hpy : EllipticCurve.Point.asSection F g (Point.mapIso φ y) =
      (⟨(EllipticCurve.Point.asSection E g y).1 ≫ (pullbackMapIso φ g).hom, hsndy⟩ :
        (F.baseChange g).Point (𝟙 T)) := Subtype.ext (asSection_mapIso φ y).symm
  have hmxF : (⟨(EllipticCurve.Point.asSection E g x).1 ≫ (pullbackMapIso φ g).hom, hsndx⟩ :
      (F.baseChange g).Point (𝟙 T)) ∈ torsionPoints F g N :=
    hpx ▸ asSection_mem_torsionPoints F (Point.mapIso φ x) hx'
  have hmyF : (⟨(EllipticCurve.Point.asSection E g y).1 ≫ (pullbackMapIso φ g).hom, hsndy⟩ :
      (F.baseChange g).Point (𝟙 T)) ∈ torsionPoints F g N :=
    hpy ▸ asSection_mem_torsionPoints F (Point.mapIso φ y) hy'
  rw [E.weilPairingEval_eq_weilPairingKM x y hx hy,
    F.weilPairingEval_eq_weilPairingKM (Point.mapIso φ x) (Point.mapIso φ y) hx' hy']
  refine congrArg Units.val ?_
  rw [weilPairingKM_congr F F.smooth g N hpx hpy
    (asSection_mem_torsionPoints F (Point.mapIso φ x) hx')
    (asSection_mem_torsionPoints F (Point.mapIso φ y) hy')]
  obtain ⟨A, hA0, ι0, W, hW, e, hnorm⟩ := exists_normalized_dataset F F.smooth g
    (⟨(EllipticCurve.Point.asSection E g y).1 ≫ (pullbackMapIso φ g).hom, hsndy⟩ :
      (F.baseChange g).Point (𝟙 T))
  rw [weilPairingKM_eq_torsionSplittingEval F F.smooth g N _ hmxF _ hmyF A hA0 W hW e hnorm]
  rw [weilPairingKM_eq_torsionSplittingEval E E.smooth g N
    (EllipticCurve.Point.asSection E g x) (asSection_mem_torsionPoints E x hx)
    (EllipticCurve.Point.asSection E g y) (asSection_mem_torsionPoints E y hy)
    ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A)
    (hM_mapIso E.smooth F.smooth φ g (EllipticCurve.Point.asSection E g y) hsndy A hA0)
    (fun i => (pullbackMapIso φ g).hom ⁻¹ᵁ W i)
    (((pullbackMapIso φ g).hom).iSup_preimage_eq_top hW)
    (fun i => Scheme.Modules.localPullbackTrivializationT (pullbackMapIso φ g).hom A (W i) (e i))
    (hnorm_mapIso φ g A W e hnorm)]
  exact (torsionSplittingEval_mapIso E.smooth F.smooth φ g N
    (EllipticCurve.Point.asSection E g y) (asSection_mem_torsionPoints E y hy)
    hsndy hmyF A hA0 W hW e hnorm
    (EllipticCurve.Point.asSection E g x) (asSection_mem_torsionPoints E x hx)
    hsndx hmxF).symm
  case hP' => exact hmxF
  case hQ' => exact hmyF

/-! ## U5 — the field leaf

**PROVED** in `WeilPairing/SelfField.lean` as
`weilPairingEval_self_of_field'` (any field with `N` invertible), by descent from the
algebraically closed leaf `weilPairingEval_self_of_isAlgClosed`. The `hfield`-hypothesis
of `weilPairingEval_self_universal` below is discharged there. -/

/-! ## U4 — vanishing over the universal torsion base -/

/-- The tautological point of `E.torsion N`: the inclusion `torsionι`, as a point of
`E` over the structure map `torsionπ`. Its kill-by-`N` condition is literally
`pullback.condition` of the defining fibre square. -/
noncomputable def tautTorsionPoint (E : EllipticCurve S) (N : ℕ) :
    E.Point (E.torsionπ N) :=
  ⟨E.torsionι N, E.torsionι_π N⟩

/-- The tautological point is killed by `N` — `pullback.condition` verbatim. -/
theorem tautTorsionPoint_killedBy (E : EllipticCurve S) (N : ℕ) :
    (tautTorsionPoint E N).1 ≫ E.mulByHom N = E.torsionπ N ≫ E.zero :=
  pullback.condition

/-! ## U4 — the universal vanishing and the final assembly

**PROVED** in `WeilPairing/SelfUniversalVanishing.lean`:
`weilPairingEval_self_universal_eq_one` (the universal diagonal value is `1`),
`weilPairingEval_self_model_map` (the model case over any ring), and
`weilPairingEval_self_of_locally` (the locality principle). The final assembly for an
arbitrary record lives there too. -/

end EllipticCurve

end ModularCurves
