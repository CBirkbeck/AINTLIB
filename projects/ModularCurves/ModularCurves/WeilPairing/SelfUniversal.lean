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

/-! ## U1 — transport along pointed isomorphisms of elliptic records -/

/-- Transport of a `T`-point along a pointed isomorphism of elliptic records over the
same base. -/
noncomputable def Point.mapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) : F.Point g :=
  ⟨x.1 ≫ φ.hom.left, by
    rw [Category.assoc, show φ.hom.left ≫ F.π = E.π from Over.w φ.hom, x.2]⟩

/-- Kill-by-`N` transports along a pointed (monoid) isomorphism:
`mulByHom_comp_left_of_isMonHom` conjugates the `[N]`s. -/
theorem zero_comp_left_of_isMonHom {E F : EllipticCurve S}
    (φ : E.asOver ⟶ F.asOver) [IsMonHom φ] :
    E.zero ≫ φ.left = F.zero := by
  have h2' : ((𝟙_ (Over S)).hom ≫ E.zero) ≫ φ.left = (𝟙_ (Over S)).hom ≫ F.zero := by
    have h1 : η[E.asOver] ≫ φ = η[F.asOver] := IsMonHom.one_hom φ
    have h2 := congrArg CommaMorphism.left h1
    simp only [Over.comp_left] at h2
    rw [← E.one_eq_zero, ← F.one_eq_zero]
    exact h2
  simpa using h2'

theorem Point.mapIso_killedBy {E F : EllipticCurve S} [IsLocallyNoetherian S]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} {g : T ⟶ S}
    {N : ℕ} {x : E.Point g} (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (Point.mapIso φ x).1 ≫ F.mulByHom N = g ≫ F.zero := by
  show (x.1 ≫ φ.hom.left) ≫ F.mulByHom N = g ≫ F.zero
  rw [Category.assoc, ← mulByHom_comp_left_of_isMonHom E F φ.hom (N : ℤ),
    ← Category.assoc, hx, Category.assoc, zero_comp_left_of_isMonHom φ.hom]

/-- **([PB-ISO])** The induced isomorphism on `π`-pullbacks from a record iso over the
same base: `pullback.map` along `φ.hom.left`, `𝟙 T`, `𝟙 S`. -/
noncomputable def pullbackMapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} (g : T ⟶ S) : pullback E.π g ≅ pullback F.π g := by
  haveI : IsIso φ.hom := inferInstance
  haveI : IsIso φ.hom.left := (Over.forget S).map_isIso φ.hom
  exact asIso (pullback.map E.π g F.π g φ.hom.left (𝟙 T) (𝟙 S)
    (by rw [Category.comp_id]; exact (Over.w φ.hom).symm) (by simp))

@[simp] theorem pullbackMapIso_hom_fst {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} (g : T ⟶ S) :
    (pullbackMapIso φ g).hom ≫ pullback.fst F.π g = pullback.fst E.π g ≫ φ.hom.left :=
  pullback.lift_fst _ _ _

@[simp] theorem pullbackMapIso_hom_snd {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} (g : T ⟶ S) :
    (pullbackMapIso φ g).hom ≫ pullback.snd F.π g = pullback.snd E.π g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The zero sections correspond under [PB-ISO] (pointedness). -/
theorem baseChangeZero_comp_pullbackMapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫ (pullbackMapIso φ g).hom =
      Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMapIso_hom_fst, ← Category.assoc]
    rw [show Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫ pullback.fst E.π g =
      g ≫ E.zero from pullback.lift_fst _ _ _,
      show Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g ≫ pullback.fst F.π g =
      g ≫ F.zero from pullback.lift_fst _ _ _]
    rw [Category.assoc, zero_comp_left_of_isMonHom φ.hom]
  · rw [Category.assoc, pullbackMapIso_hom_snd]
    rw [show Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫ pullback.snd E.π g =
      𝟙 T from pullback.lift_snd _ _ _,
      show Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g ≫ pullback.snd F.π g =
      𝟙 T from pullback.lift_snd _ _ _]

/-- **([ASSEC-MAPISO])** `asSection` intertwines the point transport and [PB-ISO]. -/
theorem asSection_mapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) :
    (EllipticCurve.Point.asSection E g x).1 ≫ (pullbackMapIso φ g).hom =
      (EllipticCurve.Point.asSection F g (Point.mapIso φ x)).1 := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllipticCurve.Point.asSection E g x).1 ≫ m)
        (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ φ.hom.left)
        (EllipticCurve.Point.asSection_val_fst E g x)).trans
      (EllipticCurve.Point.asSection_val_fst F g (Point.mapIso φ x)).symm)))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllipticCurve.Point.asSection E g x).1 ≫ m)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))).trans
      ((EllipticCurve.Point.asSection_val_snd E g x).trans
      (EllipticCurve.Point.asSection_val_snd F g (Point.mapIso φ x)).symm))

/-- **(U1, the transport theorem — `φ`-sibling of the base-change naturality)** The
pairing is invariant under pointed isomorphisms of elliptic records over the same
base. -/
theorem weilPairingEval_mapIso {E F : EllipticCurve S} [IsLocallyNoetherian S]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {N : ℕ} [NeZero N]
    {T : Scheme.{u}} {g : T ⟶ S} (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : (Point.mapIso φ x).1 ≫ F.mulByHom N = g ≫ F.zero)
    (hy' : (Point.mapIso φ y).1 ≫ F.mulByHom N = g ≫ F.zero) :
    (F.weilPairingEval (Point.mapIso φ x) (Point.mapIso φ y) hx' hy' : Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) := by sorry

/-! ## U5 — the field leaf (API gap: own sub-development, see the decomposition doc) -/

/-- **(U5, THE FIELD LEAF — the irreducible input, KM 2.8.3 over a field)** Alternation
of the pairing over a field in which `N` is invertible. Route: descend to an algebraic
closure (`Γ`-injectivity of a field extension), instantiate the KM dataset through the
classical Weil function `g_Q`, match the translation characterisations
(`eq_mul_globalTwist_of_translate` ↔ `HasseWeil.weilPairing_spec`), and import
HasseWeil's `weilPairing_self`. Sub-decomposition in its own `/develop` pass. -/
theorem weilPairingEval_self_of_field {K : Type u} [Field K]
    (E : EllipticCurve (Spec (CommRingCat.of K))) {N : ℕ} [NeZero N]
    (hNK : (N : K) ≠ 0)
    (x : E.Point (𝟙 (Spec (CommRingCat.of K))))
    (hx : x.1 ≫ E.mulByHom N = 𝟙 _ ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(Spec (CommRingCat.of K), ⊤)) = 1 := by sorry

/-! ## U4 — vanishing over the universal torsion base -/

/-- The tautological point of `E.torsion N`: the inclusion `torsionι`, as a point of
`E` over the structure map `torsionπ`. Its kill-by-`N` condition is literally
`pullback.condition` of the defining fibre square. -/
noncomputable def tautTorsionPoint (E : EllipticCurve S) (N : ℕ) :
    E.Point (E.torsionπ N) :=
  ⟨E.torsionι N, by sorry⟩

/-- The tautological point is killed by `N` — `pullback.condition` verbatim. -/
theorem tautTorsionPoint_killedBy (E : EllipticCurve S) (N : ℕ) :
    (tautTorsionPoint E N).1 ≫ E.mulByHom N = E.torsionπ N ≫ E.zero := by sorry

/-- **(U4, universal vanishing — conditional on the field leaf U5)** Over
`X_N := (modelEllipticCurve 𝕌).torsion N`, the diagonal pairing of the tautological
point is `1`. Proof: `X_N` is affine (torsion is finite over the affine atlas) and its
section ring is `ℤ`-flat (torsion flat over the `ℤ`-flat atlas ring), so sections
inject into the `N`-inverted locus, which is reduced (it embeds into the generic-fibre
torsion algebra, finite étale over a field); the value − 1 vanishes at every residue
field there by base-change naturality and the field leaf; a section of a reduced ring
vanishing at every residue field is zero. -/
theorem weilPairingEval_self_universal {N : ℕ} [NeZero N]
    (hfield : ∀ (K : Type u) [Field K] (E' : EllipticCurve (Spec (CommRingCat.of K))),
      (N : K) ≠ 0 → ∀ (x : E'.Point (𝟙 (Spec (CommRingCat.of K))))
      (hx : x.1 ≫ E'.mulByHom N = 𝟙 _ ≫ E'.zero),
      (E'.weilPairingEval (N := N) x x hx hx : Γ(Spec (CommRingCat.of K), ⊤)) = 1) :
    ((modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval (N := N)
        (tautTorsionPoint _ N) (tautTorsionPoint _ N)
        (by sorry) (by sorry) :
      Γ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N, ⊤)) = 1 := by sorry

/-- **(FINAL ASSEMBLY — the statement of `Basic.lean:372`, proven downstream)**
`e_N(x, x) = 1` over an arbitrary base: classification (U2) + transport (U1) +
gluing/naturality (U3) + universal vanishing (U4) + the field leaf (U5). -/
theorem weilPairingEval_self' {N : ℕ} [NeZero N] (E : EllipticCurve S)
    {T : Scheme.{u}} {g : T ⟶ S}
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by sorry

end EllipticCurve

end ModularCurves
