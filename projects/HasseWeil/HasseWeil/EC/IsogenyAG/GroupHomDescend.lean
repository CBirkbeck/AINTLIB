/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.CoordHomFinite
import HasseWeil.EC.IsogenyAG.BaseChange
import HasseWeil.EC.IsogenyAG.GroupHom
import HasseWeil.EC.AffinePointMap
import HasseWeil.Ramification

/-!
# ISO-L7: descent of Silverman III.4.8 to a general base field

`EC.Isogeny.addHomProperty` (`GroupHom.lean`) proves Silverman III.4.8 — every
isogeny `φ : E₁ → E₂` is a group homomorphism on rational points — over an
**algebraically closed** base field `F`.  Silverman's theorem is geometric
(`P, Q ∈ E(K̄)`); the statement over a general base field `K` (e.g. a finite
field `𝔽_q`) is the *restriction* of the geometric statement to the `K`-rational
points.

This file performs that descent.  The mathematical content splits in two:

* **The descent engine** (`addHomProperty_descend_of_baseChange`, axiom-clean):
  given a base-changed isogeny `φ_F` over `F := AlgebraicClosure K` together with
  a coordinate-ring witness `cd_F` and the
  **point-map compatibility** (writing `ι := Affine.Point.map (algebraMap K F)`)
  `ι ∘ φ.toPointMap cd = φ_F.toPointMap cd_F ∘ ι`,
  the `K`-rational `AddHomProperty` of `φ` follows by applying the alg-closed
  `addHomProperty` to `φ_F` and pulling the conclusion back along the injective
  additive map `Affine.Point.map (algebraMap K F) : E(K) ↪ E(K̄)`.

* **The base-change construction** (`EC/IsogenyAG/BaseChange.lean`, ISO-BC):
  the base-changed isogeny `baseChangeIsogeny` (via the `ofEquation` builder),
  the base-changed coordinate-ring witness `baseChangeCoordHom`, the point-map
  compatibility `baseChange_toPointMap_compat`, and the `Module.Finite`
  transport `CurveMap.CoordHom.baseChange_module_finite`.  All four are proven;
  the finiteness input (the standing finite-map hypothesis of Silverman
  II.2/II.3) is supplied unconditionally by `CurveMap.CoordHom.module_finite`.

## Main results

* `EC.Isogeny.addHomProperty_descend_of_baseChange` — the descent engine
  (axiom-clean; the reusable part).
* `EC.Isogeny.addHomProperty_descend_of_finite` — Silverman III.4.8 over a
  general base field `K` (**axiom-clean**; the `K`-level module-finiteness
  witness is supplied by `CurveMap.CoordHom.module_finite`).
* `EC.Isogeny.toBasicIsogenyDescend` — the `K`-rational
  `EC.Isogeny → HasseWeil.Isogeny` promotion (no `IsAlgClosed` hypothesis).
* `EC.Isogeny.addHomProperty_descend` — the hypothesis-free form
  (**fully proven, axiom-clean**): the `K`-level `Module.Finite` witness is
  *derived* from `(φ, cd)` alone by `CurveMap.CoordHom.module_finite`
  (`Curves/CoordHomFinite.lean`), with no separability assumption — the
  conjugate-pair/parity argument works for inseparable isogenies as well.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.8 (geometric
  statement); I.2 (base change / "defined over `K`").
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

open HasseWeil.Curves

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

omit [DecidableEq K] [W.toAffine.IsElliptic] in
/-- The induced map on affine points `HasseWeil.Affine.Point.map f hf` is
injective whenever the ring homomorphism `f` is injective.

This is the injectivity reduction underlying the descent: the conclusion of the
algebraically-closed III.4.8 is pulled back along this injective inclusion of
`K`-points into `K̄`-points (see `addHomProperty_descend_of_baseChange`). -/
private theorem map_injective_of_injective {L : Type*} [Field L] [DecidableEq L]
    (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (HasseWeil.Affine.Point.map (W := W) f hf) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP
  · rfl
  · exact absurd hP (by simp)
  · exact absurd hP (by simp)
  · rw [HasseWeil.Affine.Point.map_some, HasseWeil.Affine.Point.map_some,
      Affine.Point.some.injEq] at hP
    obtain ⟨hx, hy⟩ := hP
    obtain rfl := hf hx
    obtain rfl := hf hy
    rfl

/-- **The descent engine for ISO-L7** (axiom-clean).

Let `F := AlgebraicClosure K`.  Given an isogeny `φ` over `K` with coord-ring
witness `cd`, a base-changed isogeny `φ_F` over `F` with coord-ring witness
`cd_F`, and the point-map compatibility `hcompat`
relating `φ.toPointMap cd` to `φ_F.toPointMap cd_F` through the inclusion
`Affine.Point.map (algebraMap K F) : E(K) → E(K̄)`, the induced point map
`φ.toPointMap cd` is a group homomorphism on `E(K)`.

This is Silverman's geometric III.4.8 (over the algebraically closed `F`,
supplied by `EC.Isogeny.addHomProperty`) descended along the injective additive
inclusion of `K`-points into `K̄`-points. -/
theorem addHomProperty_descend_of_baseChange
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (φ_F : EC.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
    (cd_F : φ_F.toCurveMap.CoordHom)
    (hcompat : ∀ P : W.toAffine.Point,
      HasseWeil.Affine.Point.map (algebraMap K (AlgebraicClosure K))
          (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) (φ.toPointMap cd P) =
        φ_F.toPointMap cd_F
          (HasseWeil.Affine.Point.map (algebraMap K (AlgebraicClosure K))
            (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) P)) :
    ∀ P Q : W.toAffine.Point,
      φ.toPointMap cd (P + Q) =
        φ.toPointMap cd P + φ.toPointMap cd Q := by
  classical
  intro P Q
  -- Abbreviations.  `f` is the inclusion `K → K̄`; `δ` the induced `E(K) → E(K̄)`.
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)
  let δ : W.toAffine.Point → (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
    HasseWeil.Affine.Point.map (W := W) f hf
  -- `δ` is injective (`Affine.Point.map` of an injective ring hom).
  have hδ_inj : Function.Injective δ := map_injective_of_injective W f hf
  -- The alg-closed III.4.8 (Silverman, geometric) for the base-changed isogeny.
  -- (`Ramification.lean` supplies the Dedekind / integrally-closed instances on the
  -- base-changed coordinate ring; `AlgebraicClosure K` is `IsAlgClosed`.)
  have halg : φ_F.AddHomProperty cd_F := φ_F.addHomProperty cd_F
  -- `δ` is additive on points over a field (`AffinePointMap.lean`).
  have hδ_add : ∀ A B : W.toAffine.Point, δ (A + B) = δ A + δ B :=
    fun A B ↦ HasseWeil.Affine.Point.map_add (W := W) f A B
  -- It suffices to prove the identity after applying the injective `δ`.
  refine hδ_inj ?_
  calc δ (φ.toPointMap cd (P + Q))
      = φ_F.toPointMap cd_F (δ (P + Q)) := hcompat (P + Q)
    _ = φ_F.toPointMap cd_F (δ P + δ Q) := congrArg (φ_F.toPointMap cd_F) (hδ_add P Q)
    _ = φ_F.toPointMap cd_F (δ P) + φ_F.toPointMap cd_F (δ Q) := halg (δ P) (δ Q)
    _ = δ (φ.toPointMap cd P) + δ (φ.toPointMap cd Q) :=
          congrArg₂ (· + ·) (hcompat P).symm (hcompat Q).symm
    _ = δ (φ.toPointMap cd P + φ.toPointMap cd Q) :=
          (hδ_add (φ.toPointMap cd P) (φ.toPointMap cd Q)).symm

/-- **Silverman III.4.8 over a general base field `K`** (ISO-L7 + ISO-BC,
**axiom-clean**).

For an isogeny `φ : EC.Isogeny W W` over `K` with a coordinate-ring witness `cd`,
the induced point map `φ.toPointMap cd : E(K) → E(K)` is a group homomorphism
(the `K`-level module-finiteness, the finite-map hypothesis of Silverman
II.2/II.3, is supplied by `CurveMap.CoordHom.module_finite`).

The proof base-changes to `F := AlgebraicClosure K` with the ISO-BC
infrastructure (`EC/IsogenyAG/BaseChange.lean`): `baseChangeIsogeny` (via the
`ofEquation` builder), `baseChangeCoordHom`, the `Module.Finite` transport
`baseChange_module_finite`, and the point-map compatibility
`baseChange_toPointMap_compat` — then descends along the injective
`Affine.Point.map (algebraMap K F)` via `addHomProperty_descend_of_baseChange`. -/
theorem addHomProperty_descend_of_finite
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom) :
    ∀ P Q : W.toAffine.Point,
      φ.toPointMap cd (P + Q) =
        φ.toPointMap cd P + φ.toPointMap cd Q := by
  classical
  exact addHomProperty_descend_of_baseChange W φ cd
    (baseChangeIsogeny W φ (AlgebraicClosure K))
    (baseChangeCoordHom W φ (AlgebraicClosure K) cd)
    (baseChange_toPointMap_compat W φ (AlgebraicClosure K) cd)

/-- **The `K`-rational `EC.Isogeny → HasseWeil.Isogeny` promotion** (Silverman
III.4.8 over a general base field, bundled; the `K`-rational counterpart of
`toBasicIsogeny`, with no `IsAlgClosed` hypothesis).  The group-homomorphism
property on `E(K)` is supplied by `addHomProperty_descend_of_finite`. -/
noncomputable def toBasicIsogenyDescend
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom) :
    HasseWeil.Isogeny W.toAffine W.toAffine where
  pullback := φ.toCurveMap.pullback
  toAddMonoidHom := φ.toAddMonoidHomOfWitness cd (addHomProperty_descend_of_finite W φ cd)

@[simp] theorem toBasicIsogenyDescend_pullback
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom) :
    (φ.toBasicIsogenyDescend W cd).pullback = φ.toCurveMap.pullback := rfl

@[simp] theorem toBasicIsogenyDescend_toAddMonoidHom_apply
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (P : W.toAffine.Point) :
    (φ.toBasicIsogenyDescend W cd).toAddMonoidHom P = φ.toPointMap cd P := rfl

/-- **The hypothesis-free `K`-rational `EC.Isogeny → HasseWeil.Isogeny`
promotion**: `toBasicIsogenyDescend` with the module-finiteness witness
supplied by `CurveMap.CoordHom.module_finite` — no carried hypotheses, over
any base field, for any (possibly inseparable) isogeny-with-`CoordHom`. -/
noncomputable def toBasicIsogenyOfCoordHom
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom) :
    HasseWeil.Isogeny W.toAffine W.toAffine :=
  φ.toBasicIsogenyDescend W cd

@[simp] theorem toBasicIsogenyOfCoordHom_pullback
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom) :
    (φ.toBasicIsogenyOfCoordHom W cd).pullback = φ.toCurveMap.pullback := rfl

@[simp] theorem toBasicIsogenyOfCoordHom_toAddMonoidHom_apply
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (P : W.toAffine.Point) :
    (φ.toBasicIsogenyOfCoordHom W cd).toAddMonoidHom P = φ.toPointMap cd P := rfl

/-- **Silverman III.4.8 over a general base field `K`** (ISO-L7,
hypothesis-free form, **fully proven, axiom-clean**).

For an isogeny `φ : EC.Isogeny W W` with a coordinate-ring witness `cd`, the
induced point map `φ.toPointMap cd : E(K) → E(K)` is a group homomorphism —
with **no** carried hypotheses.

The `K`-level finiteness witness `Module.Finite K[E] K[E]` (via
`cd.toAlgebra`) is now *derived* from `(φ, cd)` alone by
`CurveMap.CoordHom.module_finite` (`Curves/CoordHomFinite.lean`): the
coordinate generator `x` is integral over `cd`'s image via the explicit
conjugate-pair relation in the `{1, Y}` basis, whose leading coefficient is a
unit of `K` by the even/odd degree parity `max(2 deg p, 2 deg q + 3)` — no
separability, no places classification, valid for inseparable isogenies. -/
theorem addHomProperty_descend
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom) :
    ∀ P Q : W.toAffine.Point,
      φ.toPointMap cd (P + Q) =
        φ.toPointMap cd P + φ.toPointMap cd Q := by
  classical
  exact addHomProperty_descend_of_finite W φ cd

end HasseWeil.EC.Isogeny
