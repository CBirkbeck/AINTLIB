/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.FrobeniusFunctionFieldEquiv
import HasseWeil.WeilPairing.FrobeniusGenericCovariance

/-!
# The translation conjugation for the arithmetic Frobenius `σ` (Silverman III.8.1d)

This file discharges the **conjugation / translation-covariance** of the concrete arithmetic
Frobenius `σ = frobeniusFunctionFieldEquiv W` of `K̄(E)`:

  `σ (τ_S g) = τ_{π̄ S} (σ g)`   for every `g : K̄(E)`,

where `τ_S = translateAlgEquivOfPoint (W.baseChange K̄) S` and
`π̄ S = frobeniusHomBaseChange S = geomFrobeniusPoint S = (S_x^q, S_y^q)`.

This was the last residual of leaf 1 (`frobeniusGaloisGeometric_holds`); it is now **proved**
axiom-clean (`frobeniusFunctionFieldEquiv_conj`), so `frobeniusScaling_holds` is axiom-clean.

## Route (point-level via the generic point, then ring-hom ext)

`σ` and `τ_S` are ring endomorphisms of `K̄(E)`, so `σ ∘ τ_S = τ_{π̄ S} ∘ σ` follows by **ring-hom
extensionality** once it holds on the generators `x_gen, y_gen` *and* on the base `algebraMap K̄`
(`ringHom_ext_base_x_y_gen`).  The base agreement is elementary (both sides `q`-power the
coefficients, `frobeniusFunctionFieldEquiv_algebraMap`).  The generator agreement is read off
**coordinates of the generic point**:

* `σ` **fixes** the generators (`frobeniusFunctionFieldEquiv_x_gen/_y_gen`: it `q`-powers the
  `K̄`-coefficients and fixes the `𝔽_q`-rational `x_gen, y_gen`), so `Point.map σ_K` *fixes the
  generic point* `P_gen = (x_gen, y_gen)`;
* `Point.map σ_K` sends the lift of a `K̄`-point `S` to the lift of its geometric Frobenius
  `π̄ S = (S_x^q, S_y^q)` (`sigmaConjugation_lift_twist`), mirroring
  `frobeniusGenericCovariance_lift_twist`;
* therefore both `Point.map σ_K (Point.map τ_S P_gen)` and
  `Point.map τ_{π̄ S} (Point.map σ_K P_gen)` equal `P_gen + lift (π̄ S)` (`sigmaConjugation_point`),
  via the master translation lemma `translateAlgEquivOfPoint_map_genericPoint`.

Reading off coordinates (`Point.map_map`) gives the two generator equalities, and the ring-hom ext
upgrades them to the pointwise conjugation `frobeniusFunctionFieldEquiv_conj`.

`σ_K` is `σ` viewed as a `K`-algebra hom `K̄(E) →ₐ[K] K̄(E)` (`frobeniusFunctionFieldEquivK`), which
exists because `σ` fixes the base field `K = 𝔽_q` (`a^q = a` for `a ∈ K`,
`FiniteField.pow_card`).  Typing the `Point.map` over the *base* curve `W : WeierstrassCurve K`
(`W' := W`) sidesteps the `K̄`-linearity diamond, exactly as in `FrobeniusGenericCovariance.lean`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Galois equivariance of the Weil pairing).
-/

open WeierstrassCurve HasseWeil.Curves Polynomial

namespace HasseWeil.WeilPairing

open HasseWeil

-- The section variables (`[Fintype K]`/`[DecidableEq K]`/`IsElliptic`) are required by the section
-- context but unused in some individual statements; the base-changed-isogeny coordinate terms
-- `(W.baseChange (AlgebraicClosure K))` are atomic and exceed the line limit irreducibly.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

section RingHomExt

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- **Ring-hom extensionality from agreement on the base `algebraMap F`, `x_gen` and `y_gen`.**
Two ring endomorphisms `ψ₁, ψ₂ : K(E) →+* K(E)` are equal iff they agree on every base constant
`algebraMap F K(E) a`, on `x_gen` and on `y_gen`.  Unlike `algHom_ext_x_y_gen` (which gets the base
agreement for free from `F`-linearity), this version takes it as a hypothesis, so it applies to ring
homs that are *not* `F`-linear (e.g. the arithmetic Frobenius `σ`, which `q`-powers the
coefficients).

Reduction chain: `IsFractionRing.ringHom_ext` (peeling `Frac`), `AdjoinRoot.ringHom_ext` (peeling
`AdjoinRoot`, splitting into the `F[X]`-inclusion and the root), `Polynomial.ringHom_ext` (peeling
`F[X]`, splitting into `C a` (= base) and `X` (= `x_gen`)). -/
theorem ringHom_ext_base_x_y_gen (ψ₁ ψ₂ : KE →+* KE)
    (hbase : ∀ a : F, ψ₁ (algebraMap F KE a) = ψ₂ (algebraMap F KE a))
    (hx : ψ₁ (x_gen W) = ψ₂ (x_gen W)) (hy : ψ₁ (y_gen W) = ψ₂ (y_gen W)) :
    ψ₁ = ψ₂ := by
  -- Peel `Frac` (`IsFractionRing.ringHom_ext`), then `AdjoinRoot`, then `F[X]`.
  apply IsFractionRing.ringHom_ext (A := W.toAffine.CoordinateRing)
  suffices h : (ψ₁.comp (algebraMap W.toAffine.CoordinateRing KE)) =
      (ψ₂.comp (algebraMap W.toAffine.CoordinateRing KE)) by
    intro r; exact RingHom.congr_fun h r
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · -- `C a`: base agreement.
      intro a
      change ψ₁ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) (C a))) =
        ψ₂ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) (C a)))
      have hca : (algebraMap W.toAffine.CoordinateRing KE)
          ((AdjoinRoot.of W.toAffine.polynomial) (C a)) = algebraMap F KE a := by
        rw [show (AdjoinRoot.of W.toAffine.polynomial) (C a) =
            algebraMap F W.toAffine.CoordinateRing a from rfl,
          ← IsScalarTower.algebraMap_apply]
      rw [hca]; exact hbase a
    · -- `X`: `x_gen` agreement.
      change ψ₁ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) X)) =
        ψ₂ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) X))
      exact hx
  · -- The root: `y_gen` agreement.
    change ψ₁ (algebraMap W.toAffine.CoordinateRing KE
        (AdjoinRoot.root W.toAffine.polynomial)) =
      ψ₂ (algebraMap W.toAffine.CoordinateRing KE
        (AdjoinRoot.root W.toAffine.polynomial))
    exact hy

end RingHomExt

/-- **`CoordinateRing.map f` fixes the `X`-generator** `algebraMap F[X] R X`.  The coordinate-ring
shadow of "a field map fixes the variable `X`": `algebraMap F[X] R X = of poly X = mk (C X)`, and
`CoordinateRing.map f` sends `mk x ↦ mk (x.map (mapRingHom f))`, with `(C X).map (mapRingHom f) =
C X` because the variable `X ∈ F[X]` has coefficients `0, 1` fixed by `f`.  Hence
`map f (of poly X) = of (mapped poly) X`. -/
theorem coordRingMap_X {R S : Type*} [CommRing R] [CommRing S] (W' : WeierstrassCurve.Affine R)
    (f : R →+* S) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f
        (algebraMap (Polynomial R) W'.CoordinateRing Polynomial.X) =
      algebraMap (Polynomial S) (W'.map f).toAffine.CoordinateRing Polynomial.X := by
  have h1 : (algebraMap (Polynomial R) W'.CoordinateRing Polynomial.X) =
      WeierstrassCurve.Affine.CoordinateRing.mk W' (Polynomial.C Polynomial.X) := by
    change (AdjoinRoot.of W'.polynomial) Polynomial.X = _
    rw [AdjoinRoot.of]
    rfl
  rw [h1, WeierstrassCurve.Affine.CoordinateRing.map_mk]
  have h2 : ((Polynomial.C Polynomial.X).map (Polynomial.mapRingHom f)) =
      Polynomial.C Polynomial.X := by
    simp
  rw [h2]
  change (AdjoinRoot.mk (W'.map f).toAffine.polynomial) (Polynomial.C Polynomial.X) = _
  rw [show (algebraMap (Polynomial S) (W'.map f).toAffine.CoordinateRing Polynomial.X) =
      (AdjoinRoot.of (W'.map f).toAffine.polynomial) Polynomial.X from rfl, AdjoinRoot.of]
  rfl

/-- **`CoordinateRing.map f` fixes the root** `AdjoinRoot.root poly`.  By definition
`CoordinateRing.map f = AdjoinRoot.lift _ (root of mapped poly) _`, and `lift _ r _ (root) = r`
(`AdjoinRoot.lift_root`). -/
theorem coordRingMap_root {R S : Type*} [CommRing R] [CommRing S] (W' : WeierstrassCurve.Affine R)
    (f : R →+* S) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f (AdjoinRoot.root W'.polynomial) =
      AdjoinRoot.root (W'.map f).toAffine.polynomial := by
  rw [WeierstrassCurve.Affine.CoordinateRing.map]
  exact AdjoinRoot.lift_root _

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACFC : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **`σ` fixes `x_gen`** (Silverman III.8.1): the arithmetic Frobenius `σ =
frobeniusFunctionFieldEquiv W` `q`-powers the `K̄`-coefficients and fixes the `𝔽_q`-rational
generator `x_gen`.  Via the raw lift `ffFrobEquivRaw` (which sends `algebraMap R KE r ↦ algebraMap
(map R) (map KE) (crFrobEquiv r)`, `IsFractionRing.ringEquivOfRingEquiv_algebraMap`) and
`coordRingMap_X` (`crFrobEquiv` fixes the `X`-generator), then the codomain cast `ffFrobCast` carries
the `X`-generator back. -/
theorem frobeniusFunctionFieldEquiv_x_gen :
    frobeniusFunctionFieldEquiv W (x_gen (W.baseChange (AlgebraicClosure K))) =
      x_gen (W.baseChange (AlgebraicClosure K)) := by
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply]
  rw [show x_gen (W.baseChange (AlgebraicClosure K)) =
      algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (algebraMap (Polynomial (AlgebraicClosure K))
          (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing Polynomial.X) from rfl]
  rw [ffFrobEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap, crFrobEquiv_apply,
    coordRingMap_X]
  -- Now `ffFrobCast (algebraMap (mapped R) (mapped KE) (algebraMap (map Kbar)[X] X))`.
  -- The cast carries it back to `x_gen` over `W.baseChange Kbar`.
  rw [ffFrobCast]
  have key : ∀ (V : WeierstrassCurve (AlgebraicClosure K))
      (h : V = W.baseChange (AlgebraicClosure K)),
      (RingEquiv.cast
          (R := fun (U : WeierstrassCurve (AlgebraicClosure K)) ↦ U.toAffine.FunctionField) h)
        (algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
          (algebraMap (Polynomial (AlgebraicClosure K)) V.toAffine.CoordinateRing Polynomial.X)) =
      x_gen (W.baseChange (AlgebraicClosure K)) := by
    intro V h; subst h; rfl
  exact key _ (map_coeffFrobEquiv_eq W)

/-- **`σ` fixes `y_gen`** (Silverman III.8.1): the arithmetic Frobenius fixes the `𝔽_q`-rational
generator `y_gen = algebraMap R KE (root poly)`.  Via the raw lift and `coordRingMap_root`
(`crFrobEquiv` fixes the root), then the codomain cast carries the root back. -/
theorem frobeniusFunctionFieldEquiv_y_gen :
    frobeniusFunctionFieldEquiv W (y_gen (W.baseChange (AlgebraicClosure K))) =
      y_gen (W.baseChange (AlgebraicClosure K)) := by
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply]
  rw [show y_gen (W.baseChange (AlgebraicClosure K)) =
      algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (AdjoinRoot.root (W.baseChange (AlgebraicClosure K)).toAffine.polynomial) from rfl]
  rw [ffFrobEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap, crFrobEquiv_apply,
    coordRingMap_root]
  rw [ffFrobCast]
  have key : ∀ (V : WeierstrassCurve (AlgebraicClosure K))
      (h : V = W.baseChange (AlgebraicClosure K)),
      (RingEquiv.cast
          (R := fun (U : WeierstrassCurve (AlgebraicClosure K)) ↦ U.toAffine.FunctionField) h)
        (algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
          (AdjoinRoot.root V.toAffine.polynomial)) =
      y_gen (W.baseChange (AlgebraicClosure K)) := by
    intro V h; subst h; rfl
  exact key _ (map_coeffFrobEquiv_eq W)

/-- **`σ` fixes the base field `K = 𝔽_q`** (Silverman III.8.1): the arithmetic Frobenius
`σ = frobeniusFunctionFieldEquiv W` fixes every constant from the base field `K`,
`σ (algebraMap K KE a) = algebraMap K KE a`.  Via the scalar tower `K → K̄ → KE` and the `q`-power on
`K̄`-constants (`frobeniusFunctionFieldEquiv_algebraMap`), the value is `algebraMap K̄ KE
((algebraMap K K̄ a) ^ #K)`, and `(algebraMap K K̄ a) ^ #K = algebraMap K K̄ a` since `a ^ #K = a`
in `K` (`FiniteField.pow_card`). -/
theorem frobeniusFunctionFieldEquiv_baseField (a : K) :
    frobeniusFunctionFieldEquiv W
        (algebraMap K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) =
      algebraMap K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a := by
  rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField,
    frobeniusFunctionFieldEquiv_algebraMap]
  congr 1
  rw [← map_pow, FiniteField.pow_card]

/-- **The arithmetic Frobenius `σ` as a `K`-algebra hom** `KE →ₐ[K] KE`.  Built from the ring hom
`σ = frobeniusFunctionFieldEquiv W` together with `frobeniusFunctionFieldEquiv_baseField` (`σ` fixes
`K`).  This is the form `Affine.Point.map (W' := W)` (over the *base* curve `W : WeierstrassCurve K`)
consumes — sidestepping the `K̄`-linearity diamond (`σ` is not `K̄`-linear). -/
noncomputable def frobeniusFunctionFieldEquivK :
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField where
  __ := (frobeniusFunctionFieldEquiv W).toRingHom
  commutes' a := frobeniusFunctionFieldEquiv_baseField W a

@[simp] theorem frobeniusFunctionFieldEquivK_apply
    (z : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    frobeniusFunctionFieldEquivK W z = frobeniusFunctionFieldEquiv W z := rfl

/-- **`Point.map (W' := W) h` of the generic point in coordinate form** for any `K`-AlgHom `h`:
`Point.map h P_gen = some (h x_gen) (h y_gen) _`.  The `show` re-types the generic point's `some`
into the `Point.map (W' := W)` codomain (the scalar-tower diamond), then `map_some` (a propositional
lemma) computes the coordinates.  Crucially this is **forward** (on its own goal, where `show`
bridges the diamond) and uses `map_some` rather than `some.inj`, so the kernel never has to reduce
`h.injective` (which, for the heavy arithmetic Frobenius `σ`, overruns the kernel). -/
theorem map_genericPoint_some
    (h : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ∃ hns, WeierstrassCurve.Affine.Point.map (W' := W) h
        (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      Affine.Point.some (h (x_gen (W.baseChange (AlgebraicClosure K))))
        (h (y_gen (W.baseChange (AlgebraicClosure K)))) hns := by
  rw [HasseWeil.genericPoint_xOf_some]
  exact ⟨_, WeierstrassCurve.Affine.Point.map_some (W' := W) (f := h)
    (generic_nonsingular (W.baseChange (AlgebraicClosure K)))⟩

/-- **The point-level geometric action of `σ`** on function-field points of `E_{K̄}`:
`Affine.Point.map` of `σ_K = frobeniusFunctionFieldEquivK W`, typed via the *base* curve
`W : WeierstrassCurve K`.  Mirror of `frobFunctionFieldPointKbar` (which uses the `q`-power
`frobeniusAlgHom`); the two differ precisely because `σ` *fixes* `x_gen, y_gen` whereas the
`q`-power Frobenius `q`-powers them. -/
noncomputable def sigmaFunctionFieldPointKbar :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)

theorem sigmaFunctionFieldPointKbar_apply
    (P : (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point) :
    sigmaFunctionFieldPointKbar W P =
      WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W) P := rfl

/-- **Cross-`W'` `Point.map` bridge for the translation `τ_S`** (the scalar-tower diamond fix), the
`σ`-analogue of `frobeniusGenericCovariance_tau_mapW`.  The `K̄`-linear translation `τ_S`, applied
via `Affine.Point.map (W' := W.baseChange K̄)`, equals its `K`-restriction applied via
`Affine.Point.map (W' := W)`.  Both act through the same underlying ring hom on coordinates, so the
equality is `cases <;> rfl`. -/
theorem sigmaConjugation_tau_mapW (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (P : (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom P =
      WeierstrassCurve.Affine.Point.map (W' := W)
        ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
        P := by
  cases P <;> rfl

/-- **The lift-twist for `σ`** (Silverman III.8.1): the point-level action `Point.map σ_K` sends the
lift of a `K̄`-point `S` to the lift of its **geometric Frobenius** `π̄ S = geomFrobeniusPointFun S`:

  `Point.map σ_K (lift S) = lift (π̄ S)`.

Coordinate case split: `lift (some sx sy) = some (algebraMap sx) (algebraMap sy)`, and
`σ (algebraMap sx) = algebraMap (sx ^ q)` (`frobeniusFunctionFieldEquiv_algebraMap`), so the image is
`some (algebraMap (sx^q)) (algebraMap (sy^q)) = lift (some (sx^q, sy^q)) = lift (π̄ S)`
(`geomFrobeniusPointFun_some`). -/
theorem sigmaConjugation_lift_twist (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    sigmaFunctionFieldPointKbar W (HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) S) =
      HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) (geomFrobeniusPointFun W S) := by
  rcases S with _ | ⟨sx, sy, hns⟩
  · change sigmaFunctionFieldPointKbar W
        (HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) 0) =
        HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) (geomFrobeniusPointFun W 0)
    rw [geomFrobeniusPointFun_zero, map_zero, map_zero]
  · rw [geomFrobeniusPointFun_some, HasseWeil.liftPointToKE_some, HasseWeil.liftPointToKE_some,
      HasseWeil.liftSomePoint, HasseWeil.liftSomePoint]
    change WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
        (Affine.Point.some _ _ _) = Affine.Point.some _ _ _
    rw [WeierstrassCurve.Affine.Point.map_some (W' := W) (f := frobeniusFunctionFieldEquivK W)]
    refine (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩ <;>
      · simp only [frobeniusFunctionFieldEquivK_apply, FiniteField.coe_frobeniusAlgHom]
        rw [frobeniusFunctionFieldEquiv_algebraMap]

/-- **`Point.map σ_K` fixes the generic point** `P_gen = (x_gen, y_gen)`.  Since `σ` fixes the
generators (`frobeniusFunctionFieldEquiv_x_gen/_y_gen`), `Point.map σ_K (some x_gen y_gen) =
some (σ x_gen) (σ y_gen) = some x_gen y_gen = P_gen`. -/
theorem sigmaConjugation_fix_genericPoint :
    sigmaFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)) := by
  rw [HasseWeil.genericPoint_xOf_some]
  change WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
      (Affine.Point.some _ _ _) = _
  rw [WeierstrassCurve.Affine.Point.map_some (W' := W) (f := frobeniusFunctionFieldEquivK W)]
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
    ⟨frobeniusFunctionFieldEquiv_x_gen W, frobeniusFunctionFieldEquiv_y_gen W⟩

/-- **The translation conjugation at the generic point** (Silverman III.8.1d, the geometric core).
For the arithmetic Frobenius `σ` and the `q`-power Frobenius point map `π̄`:

  `Point.map σ_K (Point.map τ_S P_gen) = Point.map τ_{π̄ S} (Point.map σ_K P_gen)`.

Both sides equal `P_gen + lift (π̄ S)`:
* LHS: `Point.map τ_S P_gen = P_gen + lift S` (master lemma), then `Point.map σ_K` is additive,
  fixes `P_gen` (`sigmaConjugation_fix_genericPoint`) and twists the lift to `lift (π̄ S)`
  (`sigmaConjugation_lift_twist`);
* RHS: `Point.map σ_K P_gen = P_gen` (`sigmaConjugation_fix_genericPoint`), then
  `Point.map τ_{π̄ S} P_gen = P_gen + lift (π̄ S)` (master lemma). -/
theorem sigmaConjugation_point (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
        (WeierstrassCurve.Affine.Point.map (W' := W)
          ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
          (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)))) =
      WeierstrassCurve.Affine.Point.map (W' := W)
        ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            (geomFrobeniusPointFun W S)).toAlgHom.restrictScalars K)
        (WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
          (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)))) := by
  -- Both `Point.map (W' := W) σ_K` are `sigmaFunctionFieldPointKbar` (`_apply`); rewrite via the def
  -- so the fix/lift lemmas apply, then assemble both sides to `P_gen + lift (π̄ S)`.
  rw [← sigmaFunctionFieldPointKbar_apply, ← sigmaFunctionFieldPointKbar_apply]
  -- RHS: `Point.map σ_K P_gen = P_gen`, then master lemma at `π̄ S`.
  rw [sigmaConjugation_fix_genericPoint W, ← sigmaConjugation_tau_mapW W (geomFrobeniusPointFun W S),
    HasseWeil.translateAlgEquivOfPoint_map_genericPoint (W.baseChange (AlgebraicClosure K))
      (geomFrobeniusPointFun W S)]
  -- LHS: master lemma at `S`, then distribute `Point.map σ_K`, fix `P_gen`, twist the lift.
  rw [← sigmaConjugation_tau_mapW W S,
    HasseWeil.translateAlgEquivOfPoint_map_genericPoint (W.baseChange (AlgebraicClosure K)) S,
    map_add, sigmaConjugation_fix_genericPoint W, sigmaConjugation_lift_twist W]

/-- **The translation conjugation for `σ` on the generators** (Silverman III.8.1d): reading off the
coordinates of `sigmaConjugation_point` via `Point.map_map`,

  `σ (τ_S x_gen) = τ_{π̄ S} (σ x_gen)`  and  `σ (τ_S y_gen) = τ_{π̄ S} (σ y_gen)`. -/
theorem sigmaConjugation_x_y_gen (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          (x_gen (W.baseChange (AlgebraicClosure K)))) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S)
        (frobeniusFunctionFieldEquiv W (x_gen (W.baseChange (AlgebraicClosure K)))) ∧
    frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          (y_gen (W.baseChange (AlgebraicClosure K)))) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S)
        (frobeniusFunctionFieldEquiv W (y_gen (W.baseChange (AlgebraicClosure K)))) := by
  have hpt := sigmaConjugation_point W S
  -- Peel the **inner** `Point.map` on each side (`map_genericPoint_some`, single non-composed map:
  -- its `injective` is `restrictScalars τ_S` resp. `σ_K` *alone*, which the kernel reduces fine —
  -- unlike a composed map).  This turns the inner generic point into `some` of the generator images.
  obtain ⟨_, e1⟩ := map_genericPoint_some W
    ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
  obtain ⟨_, e2⟩ := map_genericPoint_some W (frobeniusFunctionFieldEquivK W)
  rw [e1, e2] at hpt
  -- Peel the **outer** `Point.map` on each side: the argument is now an explicit `some` (no
  -- scalar-tower diamond), so `map_some` rewrites directly, again with a single map's `injective`.
  rw [WeierstrassCurve.Affine.Point.map_some (W' := W) (f := frobeniusFunctionFieldEquivK W),
    WeierstrassCurve.Affine.Point.map_some (W' := W)
      (f := (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S)).toAlgHom.restrictScalars K),
    WeierstrassCurve.Affine.Point.some.injEq] at hpt
  obtain ⟨hx, hy⟩ := hpt
  -- Reduce the `restrictScalars`/`σ_K` wrappers to plain function applications.
  simp only [AlgHom.coe_restrictScalars',
    frobeniusFunctionFieldEquivK_apply] at hx hy
  exact ⟨hx, hy⟩

/-- **Comp-unfold helper** for the `σ ∘ τ_S` side: `(σ.toRingHom.comp τ_S.toRingHom) g = σ (τ_S g)`.
Proven by the bare term `RingHom.comp_apply _ _ g` — the residual coercion equalities
(`σ.toRingHom z = σ z`, `τ_S.toRingEquiv.toRingHom g = τ_S g`) are closed by `rfl`, which is
kernel-cheap.  Crucially we **avoid** `simp`'s coercion lemmas here: rewriting with
`RingEquiv.coe_toRingHom`/`AlgEquiv.coe_ringEquiv` against the heavy `frobeniusFunctionFieldEquiv`
(a `RingEquiv.trans` whose codomain is a `RingEquiv.cast`) forces a kernel `whnf` that overruns the
heartbeat budget. -/
theorem frob_comp_tau_apply (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ((frobeniusFunctionFieldEquiv W).toRingHom.comp
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toRingEquiv.toRingHom)
        g =
      frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S g) :=
  RingHom.comp_apply _ _ g

/-- **Comp-unfold helper** for the `τ_{π̄ S} ∘ σ` side: `(τ_{π̄ S}.toRingHom.comp σ.toRingHom) g =
τ_{π̄ S} (σ g)`.  Companion of `frob_comp_tau_apply`, same bare-`comp_apply` term route. -/
theorem tau_comp_frob_apply (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (geomFrobeniusPointFun W S)).toRingEquiv.toRingHom.comp
        (frobeniusFunctionFieldEquiv W).toRingHom)
        g =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S) (frobeniusFunctionFieldEquiv W g) :=
  RingHom.comp_apply _ _ g

/-- **The translation conjugation for `σ`, as a ring-hom composition equality** (Silverman III.8.1d).
The two ring endomorphisms `σ ∘ τ_S` and `τ_{π̄ S} ∘ σ` of `K̄(E)` agree on the base `algebraMap K̄`
(both `q`-power the coefficients) and on the generators `x_gen, y_gen` (`sigmaConjugation_x_y_gen`),
hence are equal by `ringHom_ext_base_x_y_gen`.  The heavy comps are passed explicitly so Lean never
unifies them by `whnf`; the kernel check of this equality alone is cheap. -/
theorem frobeniusFunctionFieldEquiv_comp_translate_eq
    (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    (frobeniusFunctionFieldEquiv W).toRingHom.comp
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toRingEquiv.toRingHom
      = (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (geomFrobeniusPointFun W S)).toRingEquiv.toRingHom.comp
        (frobeniusFunctionFieldEquiv W).toRingHom := by
  obtain ⟨hx, hy⟩ := sigmaConjugation_x_y_gen W S
  refine ringHom_ext_base_x_y_gen (W.baseChange (AlgebraicClosure K)) _ _ (fun a ↦ ?_)
    (by rw [frob_comp_tau_apply, tau_comp_frob_apply]; exact hx)
    (by rw [frob_comp_tau_apply, tau_comp_frob_apply]; exact hy)
  -- Base agreement: both sides `q`-power the coefficients (`τ`s fix `algebraMap`, `σ` `q`-powers it).
  -- These *clean* rewrite lemmas (no coercion-of-`σ` unfolding) reduce both sides to
  -- `algebraMap (a ^ #K)` regardless of traversal order.
  rw [frob_comp_tau_apply, tau_comp_frob_apply]
  simp only [AlgEquiv.commutes, frobeniusFunctionFieldEquiv_algebraMap]

/-- **The translation conjugation for the arithmetic Frobenius `σ`** (Silverman III.8.1d, pointwise
form) — the geometric residual of leaf 1.  For every `g : K̄(E)`:

  `σ (τ_S g) = τ_{π̄ S} (σ g)`,

where `τ_S = translateAlgEquivOfPoint (W.baseChange K̄) S` and `π̄ S = geomFrobeniusPointFun S =
(S_x^q, S_y^q)`.  Read off at `g` from the ring-hom composition equality
`frobeniusFunctionFieldEquiv_comp_translate_eq`, bridging through the comp-unfold helpers (a
controlled `rw`, never a `whnf` of the coercion tower). -/
theorem frobeniusFunctionFieldEquiv_conj (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S g) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S) (frobeniusFunctionFieldEquiv W g) := by
  rw [← frob_comp_tau_apply, ← tau_comp_frob_apply]
  exact RingHom.congr_fun (frobeniusFunctionFieldEquiv_comp_translate_eq W S) g

end BaseChange

end HasseWeil.WeilPairing
