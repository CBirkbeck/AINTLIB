/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldPairingUnique

/-!
# The field pairing as a root of unity in the base field (WP-D3d step 2)

`fieldWeilPairingHom` (`WeilPairing/FieldPairingUnique.lean`) is a morphism of finite étale
`K`-algebras `μ_N-algebra ⟶ torsionPair-algebra`. Composing it with a **`K`-rational** point of the
torsion-pair algebra and reading the result through `muNAlgebraFibreEquiv`
(`WeilPairing/GaloisFibre.lean`) turns it into an honest element of `{ a : K // a ^ N = 1 }`.

That is the shape the componentwise construction of `ζ` needs (`factorRootOfUnityDescend`,
`WeilPairing/FactorRoot.lean`, then `nonempty_weilPairing_of_cover_of_values`): at the generic point of
each component of the cover, the pairing of the tautological basis is a root of unity in that
component's function field.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

variable (K : Type u) [Field K] [PerfectField K] [DecidableEq (AlgebraicClosure K)]
  (E : EllipticCurve (Spec (CommRingCat.of K))) (N : ℕ) [NeZero N] (hK : (N : K) ≠ 0)

/-- **(WP-D3d step 2)** The value of the field-level Weil pairing at a `K`-rational point of the
torsion-pair algebra, as a root of unity in `K` itself.

`fieldWeilPairingHom` composed with the point is a `K`-point of the `μ_N`-algebra, and
`muNAlgebraFibreEquiv` reads such points as `N`-th roots of unity. -/
noncomputable def fieldPairingValue
    (f : (EllipticCurve.torsionPairAlgebra K E N hK).obj →ₐ[K] K) : { a : K // a ^ N = 1 } :=
  muNAlgebraFibreEquiv K N hK K (f.comp (fieldWeilPairingHom K E N hK).hom.hom)

/-- The defining property, transported: the pairing value is the reading of
`fieldWeilPairingHom` at the point — by construction, so that consumers can rewrite through it
without unfolding `muNAlgebraFibreEquiv`. -/
theorem fieldPairingValue_eq
    (f : (EllipticCurve.torsionPairAlgebra K E N hK).obj →ₐ[K] K) :
    fieldPairingValue K E N hK f =
      muNAlgebraFibreEquiv K N hK K (f.comp (fieldWeilPairingHom K E N hK).hom.hom) :=
  rfl

/-- …and it really is an `N`-th root of unity in `K` (the subtype's own property, named for use at
`rootOfUnityDescend`'s interface). -/
theorem fieldPairingValue_pow
    (f : (EllipticCurve.torsionPairAlgebra K E N hK).obj →ₐ[K] K) :
    (fieldPairingValue K E N hK f : K) ^ N = 1 :=
  (fieldPairingValue K E N hK f).2

/-- **(WP-D3d step 4, the push-up)** The image of the field pairing value in the algebraic closure is
the reading of `fieldWeilPairingHom` at the *closure-valued* point obtained from `f`.

`muNAlgebraFibreEquiv_comp_algHom` (`WeilPairing/GaloisFibre.lean`) is what makes this work: the fibre
dictionary is natural in the coefficient ring, so pushing the point up pushes its root of unity up. With
this, `fieldWeilPairingHom_spec` — which is stated for closure-valued points — becomes applicable to the
`K`-rational pairing value, and `fieldWeilPairing_det_of_galois` can be run upstairs and brought back by
injectivity of `algebraMap K (AlgebraicClosure K)`. -/
theorem algebraMap_fieldPairingValue
    (f : (EllipticCurve.torsionPairAlgebra K E N hK).obj →ₐ[K] K) :
    algebraMap K (AlgebraicClosure K) (fieldPairingValue K E N hK f : K) =
      (muNAlgebraFibreEquiv K N hK (AlgebraicClosure K)
        ((Algebra.ofId K (AlgebraicClosure K)).comp
          (f.comp (fieldWeilPairingHom K E N hK).hom.hom)) : AlgebraicClosure K) := by
  rw [fieldPairingValue_eq]
  exact (muNAlgebraFibreEquiv_comp_algHom K N hK K (AlgebraicClosure K)
    (Algebra.ofId K (AlgebraicClosure K))
    (f.comp (fieldWeilPairingHom K E N hK).hom.hom)).symm

/-- **(WP-D3d step 4, move 1)** …and that reading **is** the Silverman pairing of the corresponding
geometric points.

`weilPairingFibreMap` is by definition `(muNAlgebraFibreEquiv …).symm (C.pairing …)`, so applying the
fibre dictionary to it is `Equiv.apply_symm_apply` — no unfolding of the dictionary is needed. The only
bridge is `AlgHom.comp_assoc`, since the push-up produces `ofId.comp (f.comp hom)` while
`fieldWeilPairingHom_spec` speaks of `(ofId.comp f).comp hom`. -/
theorem algebraMap_fieldPairingValue_eq_pairing
    (f : (EllipticCurve.torsionPairAlgebra K E N hK).obj →ₐ[K] K) :
    algebraMap K (AlgebraicClosure K) (fieldPairingValue K E N hK f : K) =
      (((globalGaloisFibreChart K (AlgebraicClosure K) E).pairing N
          (natCast_ne_zero_of_algebra K N hK)
          (torsionFibrePoint K N hK E
            (EllipticCurve.torsionPairAlgebraPointsEquiv K E N hK
              ((Algebra.ofId K (AlgebraicClosure K)).comp f)).1)
          (torsionFibrePoint K N hK E
            (EllipticCurve.torsionPairAlgebraPointsEquiv K E N hK
              ((Algebra.ofId K (AlgebraicClosure K)).comp f)).2)
          (torsionFibrePoint_torsion K N hK E _)
          (torsionFibrePoint_torsion K N hK E _) : AlgebraicClosure K)) := by
  rw [algebraMap_fieldPairingValue, ← AlgHom.comp_assoc,
    fieldWeilPairingHom_spec, weilPairingFibreMap, Equiv.apply_symm_apply]

/- **(WP-D3d step 4, move 3) — what it must actually say.** A first attempt here stated
`σ (algebraMap … ζ) = algebraMap … (ζ ^ det g)` *taking the closure-level identity as a hypothesis* — i.e.
`map_pow` with the conclusion assumed. That is scaffolding, not content, so it was removed.

Moves 1 and 2 give the determinant law in **σ-action form**: for a `k`-automorphism `σ` of the geometric
point carrying the torsion pair per `g`,

  `σ (algebraMap K (AlgebraicClosure K) ζ) = (algebraMap K (AlgebraicClosure K) ζ) ^ det g`,   `ζ := fieldPairingValue …`

by `algebraMap_fieldPairingValue_eq_pairing` then `GaloisFibreChart.pairing_det`. Since `σ` fixes `K`
pointwise (it is a `K`-algebra map) the left side is `algebraMap … ζ`, so this *already* forces
`ζ = ζ ^ det g` in `K` by injectivity — i.e. the σ-action form is **vacuous for `K`-rational values**.

That is the real content of move 3, and it is a *finding*, not a gap: the value equations of
`nonempty_weilPairing_of_cover_of_values` compare `ζ` at **two different points of the cover**
(`Γ(α)(ζ)` versus `Γ(β)(ζ)`), which no automorphism of a single geometric point can express. Supplying
them needs the **component transition**: the two points lie on components exchanged by the `GL₂`-action,
and on a component's stabiliser the transition is an automorphism of that component's *function field*
fixing the curve — which is where `fieldWeilPairing_det_of_galois` genuinely bites, with `K` the function
field and `k` the fixed subfield, **not** with `σ` a `K`-automorphism of `AlgebraicClosure K`.

So the remaining work is the orbit/stabiliser bookkeeping over the components of the cover (recorded on
the board), and moves 1–2 are its *inputs at the generic point*, not the whole of it. -/

end ModularCurves
