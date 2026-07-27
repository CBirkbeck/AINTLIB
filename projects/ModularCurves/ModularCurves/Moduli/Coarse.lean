/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaH

/-!
# Coarse moduli statements: the j-line, Y₀(N), and coarse Y_{P_H} (KM Ch. 8 ⧗)

The scheme-level answer for the NON-rigid levels — level 1, `N ≤ 2`, `Γ₀(N)` — where
only a stack exists (`gammaFullNaive_not_rigid_of_le_two`) and the classical objects
are *coarse* moduli schemes.

Sources: Loeffler §3.6 (verbatim, on `ι_S : {(E,C)/S} → Y₀(N)(S)`: "In general, this
is neither injective nor surjective, but if `S = Spec(k̄)` for `k̄` algebraically
closed, then it is bijective"), §3.8 Remark (1) (verbatim: "the proof of Theorem 3.7.4
gives a scheme `Y_{P_H}` over `ℤ[1/N]` that is 'the best possible approximation' to
representing the functor `P̃_H`: there are maps `P̃_H(S) → Y_{P_H}(S)` which are
surjective for `S` a field, and bijective if `S` is algebraically closed … These
schemes `Y_{P_H}` for non-rigid `P_H` are sometimes called *coarse moduli spaces*");
KM Ch. 8 ("coarse moduli schemes, cusps, and compactifications" — ⧗KM, on the
do-not-formalize-from-memory list: these statements may be *stated* from [Loe] but
their KM-route proofs wait for the full text).

The universal property (initiality among maps to schemes) requires the
moduli-problem-morphism vocabulary of stream Q (T-Q6/T-Q7); here we state the
geometric-points characterisation, which is what downstream consumers use.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- Transport of points along a pointed `S`-morphism of elliptic curves. -/
def HomOver.mapPoint {E E' : EllipticCurve S} (f : E.HomOver E') {T : Scheme.{u}}
    {g : T ⟶ S} (P : E.Point g) : E'.Point g :=
  ⟨P.1 ≫ f.hom, by rw [Category.assoc, f.over_w, P.2]⟩

end EllipticCurve

section Coarse

variable (R : CommRingCat.{u})

open EllipticCurve in
/-- Isomorphism classes of elliptic curves with an `H`-orbit of full level-`N`
structures, over a base — the point-set that a coarse `Y_{P_H}` must have at
algebraically closed points: the quotient by the join of the `H`-action and pointed
**isomorphism** (`(E, L) ∼ (E', L')` iff some pointed `S`-isomorphism carries `g • L`
to `L'` for some `g ∈ H`; `Quot` takes the generated equivalence).

The `IsIso f.hom` clause is required: general `HomOver`s include non-isomorphisms, and
without it a 3-isogeny (an isomorphism on `E[2]`) would collapse non-isomorphic curves
in `GammaHClasses S 2 H`, while at `N = 1` the zero morphism would collapse everything
to a point. -/
def GammaHClasses (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) : Type (u + 1) :=
  Quot (fun (a b : Σ E : EllipticCurve S, E.FullLevelPt N) =>
    ∃ (f : a.1.HomOver b.1) (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)),
      IsIso f.hom ∧ g ∈ H ∧
      f.mapPoint (a.1.glSmul g a.2).1.1 = b.2.1.1 ∧
      f.mapPoint (a.1.glSmul g a.2).1.2 = b.2.1.2)

/-- The class of a levelled curve in `GammaHClasses`. -/
def GammaHClasses.mk {S : Scheme.{u}} {N : ℕ} [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (E : EllipticCurve S) (L : E.FullLevelPt N) : GammaHClasses S N H :=
  Quot.mk _ ⟨E, L⟩

/-- **(T-M1 = KM 8.2 ⧗ "The j-line as a coarse moduli scheme"; Silverman III.1.4(b))**
The j-line `Spec R[j]` is a coarse moduli scheme for elliptic curves (level 1): over
every algebraically closed field, isomorphism classes of elliptic curves biject with
points of the affine line, via the `j`-invariant of any Weierstrass model of the
curve. (Universal-property half: T-Q7, needs stream-Q vocabulary.) -/
theorem jLine_coarse_points (k : Type u) [Field k] [IsAlgClosed k] :
    Nonempty (EllipticCurve.IsoClasses (Spec (.of k)) ≃ k) := by sorry

/-- **(T-M1a, j-compatibility of the bijection)** The bijection of
`jLine_coarse_points` can be chosen to send (the class of) an elliptic curve whose
fibre is the Weierstrass model of `W` to `W.j`. -/
theorem jLine_coarse_points_j (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ β : EllipticCurve.IsoClasses (Spec (.of k)) ≃ k,
      ∀ (W : WeierstrassCurve k) (_ : W.IsElliptic) (E : EllipticCurve (Spec (.of k)))
        (e : E.E ≅ projModel W), e.hom ≫ projModelπ W = E.π →
        β ⟦E⟧ = W.j := by sorry

/-- **(T-M2 = Loeffler §3.6 / §3.8 Remark (1); KM Ch. 8 ⧗)** Coarse `Y_{P_H}` exists:
for every `H ≤ GL₂(ℤ/N)` (in particular the Borel — `Y₀(N)` — and `N ≤ 2` full level)
there is a scheme over `Spec R`, affine over the `j`-line, whose points over every
algebraically closed field biject with the classes `GammaHClasses` ("the maps
`P̃_H(S) → Y_{P_H}(S)` … are bijective if `S` is algebraically closed"),
**compatibly with `j`**. Construction route: quotient of the fine `Y(N')` (auxiliary
rigid level) by the finite group action — stream Q.

ADVERSARIAL FIX (2026-07-06): the previous conclusion — an unconstrained `∃ Y` with a
bare `Nonempty (≃)` per point — was a pure cardinality claim (satisfied by `𝔸¹_R`
outright) and asserted nothing about moduli. The bijection is now pinned by the
`j`-line factorisation: sending a class to its point of `Y` and then down `jY`
computes the `j`-invariant of (any Weierstrass model of) the curve, mirroring
`jLine_coarse_points_j`. Loeffler's full pin (the natural transformation
`P̃_H(S) → Y(S)` for all `S`) is stream-Q vocabulary, ticket `T-Q7`. -/
theorem exists_coarse_gammaH (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec R) (jY : Y ⟶ Spec (.of (Polynomial R))),
      jY ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) = σ ∧
      IsAffineHom jY ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
        ∃ e : GammaHClasses (Spec (.of k)) N H ≃
            { h : Spec (.of k) ⟶ Y //
              h ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap R k)) },
          ∀ (E : EllipticCurve (Spec (.of k))) (L : E.FullLevelPt N)
            (W : WeierstrassCurve k) (_ : W.IsElliptic)
            (i : E.E ≅ projModel W), i.hom ≫ projModelπ W = E.π →
            (e (GammaHClasses.mk H E L)).1 ≫ jY =
              Spec.map (CommRingCat.ofHom
                (Polynomial.eval₂RingHom (algebraMap R k) W.j)) := by sorry

end Coarse

end ModularCurves
