/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.Basic
import ModularCurves.WeilPairing.DescentFaithful

/-!
# Reduction of `e_N(x, x) = 1` to the level-`2N` diagonal square (AP-E4, KM Notes on Ch. 2)

KM's "Notes Added in Proof" (print p. 505) prove the alternation `e_N(R, R) = 1` of the
`e_N`-pairing from three inputs: fppf-locally `R = 2P` for a `2N`-torsion point `P`
(`[2]`-surjectivity), the level compatibility `e_N(2P, 2Q) = e_{2N}(2P, Q)` (2.8.4.1, our
`AP-E6`), and the *diagonal square* `e_{2N}(P, P)² = 1` (an instance of the 2.8.3
alternation, cited to [Oda]). This file formalises the **reduction**: given a cover
`π' : T' ⟶ T` that is injective on global sections and over which `x` halves, together
with the diagonal square at level `N·2` on the cover, the alternation at level `N`
follows. The proof is the KM chain

  `e_N(x,x)|_{T'} = e_N(2P, 2P) = e_{N·2}(2P, P) = e_{N·2}(P,P)² = 1`,

using only the *proved* register laws: base-change naturality (`weilPairingEval_restrict`),
the mixed level shift (`weilPairingKM_mul_smul_right`, AP-E6-e, through the bridge), and
**left** additivity (`weilPairingEval_add_left`) — deliberately avoiding
`weilPairingEval_zsmul_left`/`_antisymm`, which derive from `_self` and would be circular.

The two remaining inputs are tracked separately: the halving cover (finite locally free
surjective `[2]`-splitting cover, gated on the `mulByHom`-flatness substrate) and the
diagonal square (AP-E4a, biextension-theoretic).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(AP-E4 reduction, KM Notes on Ch. 2)** If `x` halves over a cover `π' : T' ⟶ T` that
is injective on global sections — `2 • P = x|_{T'}` with `P` killed by `N·2` — and the
level-`N·2` diagonal square `e_{N·2}(P, P)² = 1` holds on the cover, then `e_N(x, x) = 1`.
Combined with a finite locally free surjective `[2]`-splitting cover (which is
`Γ`-injective) and AP-E4a, this yields the register's `weilPairingEval_self`. -/
theorem weilPairingEval_self_of_halving {N : ℕ} [NeZero N] {T T' : Scheme.{u}}
    {g : T ⟶ S} (π' : T' ⟶ T)
    (hinj : Function.Injective ((Scheme.Γ.map π'.op).hom : Γ(T, ⊤) → Γ(T', ⊤)))
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (P : E.Point (π' ≫ g))
    (hP : P.1 ≫ E.mulByHom (N * 2) = (π' ≫ g) ≫ E.zero)
    (hhalf : (2 : ℤ) • P = Point.restrict E π' x)
    (halt : haveI : NeZero (N * 2) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
      (E.weilPairingEval (N := N * 2) P P hP hP : Γ(T', ⊤)) ^ 2 = 1) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by
  haveI : NeZero (N * 2) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- kill-hypotheses for every point that appears
  have hxr : (Point.restrict E π' x).1 ≫ E.mulByHom N = (π' ≫ g) ≫ E.zero := by
    show (π' ≫ x.1) ≫ E.mulByHom N = (π' ≫ g) ≫ E.zero
    rw [Category.assoc, hx, ← Category.assoc]
  have h2P : ((2 : ℤ) • P).1 ≫ E.mulByHom N = (π' ≫ g) ≫ E.zero := by
    rw [hhalf]; exact hxr
  have h2P' : ((2 : ℤ) • P).1 ≫ E.mulByHom (N * 2) = (π' ≫ g) ≫ E.zero :=
    E.point_zsmul_killedBy 2 hP
  have hPP : (P + P).1 ≫ E.mulByHom (N * 2) = (π' ≫ g) ≫ E.zero :=
    E.point_add_killedBy hP hP
  -- the mixed level shift `e_N(2P, 2P) = e_{N·2}(2P, P)`: bridge + AP-E6-e + `asSection`
  -- scalar compatibility (`2 • ` spelled additively to avoid any `ℤ`/`ℕ` cast fight)
  have hshift : (E.weilPairingEval ((2 : ℤ) • P) ((2 : ℤ) • P) h2P h2P : Γ(T', ⊤)) =
      (E.weilPairingEval (N := N * 2) ((2 : ℤ) • P) P h2P' hP : Γ(T', ⊤)) := by
    rw [E.weilPairingEval_eq_weilPairingKM ((2 : ℤ) • P) ((2 : ℤ) • P) h2P h2P,
      E.weilPairingEval_eq_weilPairingKM (N := N * 2) ((2 : ℤ) • P) P h2P' hP]
    refine congrArg Units.val ?_
    refine Eq.trans ?_ (weilPairingKM_mul_smul_right E E.smooth (π' ≫ g) N 2
      (EllipticCurve.Point.asSection E (π' ≫ g) ((2 : ℤ) • P))
      (asSection_mem_torsionPoints E _ h2P)
      (asSection_mem_torsionPoints E _ h2P')
      (EllipticCurve.Point.asSection E (π' ≫ g) P)
      (asSection_mem_torsionPoints E P hP)
      (smul_mem_torsionPoints_of_mul E (π' ≫ g)
        (asSection_mem_torsionPoints E P hP))).symm
    exact weilPairingKM_congr E E.smooth (π' ≫ g) N rfl
      ((asSection_zsmul E (π' ≫ g) 2 P).trans
        ((two_zsmul _).trans (two_nsmul _).symm))
      (asSection_mem_torsionPoints E _ h2P)
      (asSection_mem_torsionPoints E _ h2P)
      (asSection_mem_torsionPoints E _ h2P)
      (smul_mem_torsionPoints_of_mul E (π' ≫ g)
        (asSection_mem_torsionPoints E P hP))
  -- the KM chain, descended along `π'`
  apply hinj
  refine Eq.trans ?_ (map_one _).symm
  refine (((E.weilPairingEval_restrict π' x x hx hx hxr hxr).symm.trans
    (E.weilPairingEval_congr hhalf.symm hhalf.symm hxr hxr h2P h2P)).trans ?_)
  refine (hshift.trans ?_)
  refine ((E.weilPairingEval_congr (two_zsmul P) rfl h2P' hP hPP hP).trans ?_)
  refine ((E.weilPairingEval_add_left P P P hP hP hP hPP).trans ?_)
  exact (pow_two _).symm.trans halt

/-- **(AP-E4 reduction, flat-cover form)** The same reduction with the `Γ`-injectivity
discharged by WP-C1 (`injective_appTop_of_flat_of_surjective`): any flat surjective halving
cover works — in particular the finite locally free `[2]`-splitting torsor, once its
substrate lands. -/
theorem weilPairingEval_self_of_halving_of_flat {N : ℕ} [NeZero N] {T T' : Scheme.{u}}
    {g : T ⟶ S} (π' : T' ⟶ T) [Flat π'] [AlgebraicGeometry.Surjective π']
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (P : E.Point (π' ≫ g))
    (hP : P.1 ≫ E.mulByHom (N * 2) = (π' ≫ g) ≫ E.zero)
    (hhalf : (2 : ℤ) • P = Point.restrict E π' x)
    (halt : haveI : NeZero (N * 2) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
      (E.weilPairingEval (N := N * 2) P P hP hP : Γ(T', ⊤)) ^ 2 = 1) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 :=
  E.weilPairingEval_self_of_halving π'
    (by rw [Scheme.Γ_map_op]; exact injective_appTop_of_flat_of_surjective π')
    x hx P hP hhalf halt

end EllipticCurve

end ModularCurves
