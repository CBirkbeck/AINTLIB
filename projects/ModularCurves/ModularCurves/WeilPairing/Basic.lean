/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.RootOfUnityIntPow
import ModularCurves.GroupScheme.MuN
import ModularCurves.WeilPairing.KMNaturality

/-!
# The Weil pairing over a base scheme (KM 2.8)

The pairing `e_N : E[N] ×_S E[N] ⟶ μ_N` for an elliptic curve `E/S`, needed (a) as the
determinant constraint in full-level moduli (`Y(N)`, `Y(ρ,p)`), and (b) as the source of
the `μ_N`-valued "representations-with-pairing" in the FLT application.

Because the pairing is *canonical data*, not a property — and the literature pins it down
only up to the standard inverse ambiguity ("there are two standard normalizations for the
Weil pairing — pick one", Buzzard, Lecture 8 p. 33) — it is registered as construction DS4
(ticket chain `T-C*`; construction of record KM 2.8). The normalisation is fixed by
comparison with the fibrewise field-level Weil pairing already proved in this repository
(`projects/HasseWeil/…/HasseBound/WeilPairing/Pairing.lean`, Silverman III.8); that
comparison is `T-C4` in `WeilPairing/FibreComparison.lean` (kept out of the definitional
spine to isolate the cross-project import). Normalisation choice: review questions
Q-WP1/Q-WP2.

Everything downstream must consume the pairing through `weilPairing` and the specification
statements below; no other properties may be assumed of it.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(DS4, ticket chain T-C1)** The Weil pairing of `E[N]`, as an `S`-morphism
`E[N] ×_S E[N] ⟶ μ_{N,S}`. Construction of record: KM 2.8 (the norm/divisor construction) —
**filled 2026-08-09 by the Katz–Mazur backend**: the canonical value `weilPairingKM`
(existence of a normalised dataset: `WeilPairing/KMDataset.lean`; independence of the choice:
`WeilPairing/KMIndependence.lean`) evaluated at the tautological pair of `N`-torsion points
over the universal base `E[N] ×_S E[N]` (`WeilPairing/KMNaturality.lean`), turned into a
morphism to `μ_N` by the points description `muNPointsEquiv` — it lands there by
`weilPairingKM_pow_eq_one`, KM p. 89. -/
noncomputable def weilPairing (N : ℕ) [NeZero N] :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N :=
  ((muNPointsEquiv S N (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).symm
    ⟨((weilPairingKM E E.smooth (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        N (univTorsionFst E N) (univTorsionFst_mem E N)
        (univTorsionSnd E N) (univTorsionSnd_mem E N) :
      Γ(pullback (E.torsionπ N) (E.torsionπ N), ⊤)ˣ) : Γ(pullback (E.torsionπ N)
        (E.torsionπ N), ⊤)),
      (Units.val_pow_eq_pow_val _ _).symm.trans
        ((congrArg Units.val (weilPairingKM_pow_eq_one E E.smooth
          (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N
          (univTorsionFst E N) (univTorsionFst_mem E N)
          (univTorsionSnd E N) (univTorsionSnd_mem E N))).trans Units.val_one)⟩).val

/-- **(T-C1a, specification of DS4)** The Weil pairing is a morphism over `S` — the
subtype witness of the points description used to construct it. -/
theorem weilPairing_over (N : ℕ) [NeZero N] :
    E.weilPairing N ≫ muNπ S N = pullback.fst _ _ ≫ E.torsionπ N :=
  ((muNPointsEquiv S N (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).symm
    ⟨((weilPairingKM E E.smooth (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        N (univTorsionFst E N) (univTorsionFst_mem E N)
        (univTorsionSnd E N) (univTorsionSnd_mem E N) :
      Γ(pullback (E.torsionπ N) (E.torsionπ N), ⊤)ˣ) : Γ(pullback (E.torsionπ N)
        (E.torsionπ N), ⊤)),
      (Units.val_pow_eq_pow_val _ _).symm.trans
        ((congrArg Units.val (weilPairingKM_pow_eq_one E E.smooth
          (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N
          (univTorsionFst E N) (univTorsionFst_mem E N)
          (univTorsionSnd E N) (univTorsionSnd_mem E N))).trans Units.val_one)⟩).2

/-- Pair two `T`-points of `E[N]` into a `T`-point of `E[N] ×_S E[N]`, and evaluate the
Weil pairing, landing in the `N`-th roots of unity of `Γ(T, O_T)` via the points
description of `μ_N` (DS3-spec `muNPointsEquiv`). Real construction modulo the registered
data it consumes. -/
noncomputable def weilPairingEval {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    { a : Γ(T, ⊤) // a ^ N = 1 } :=
  muNPointsEquiv S N g
    ⟨pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
        (by simp) ≫ E.weilPairing N, by
      rw [Category.assoc, E.weilPairing_over N, ← Category.assoc,
        pullback.lift_fst, E.pointToTorsion_torsionπ]⟩

/-- **(AP-E1-YON3, the bridge)** `weilPairingEval` computes the canonical Katz–Mazur value
`weilPairingKM` on every pair of `N`-torsion points. This is what AP-E2…E6 consume: it
converts each register specification into a statement about `weilPairingKM`, where the KM
machinery (`torsionSplittingEval_add`, `torsionSplittingEval_pow_eq_one`, …) applies.

Proof: substitute `g = k ≫ t₀` for the classifying map `k` of the pair; naturality of the
`μ_N`-points description reads the evaluation as the `k`-pullback of the universal value;
the restriction law `weilPairingKM_restrictBase` computes the same pullback as the
canonical value at the restricted tautological points, which the reconstruction lemmas
identify with `x` and `y`. -/
theorem weilPairingEval_eq_weilPairingKM {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x y hx hy : Γ(T, ⊤)) =
      ((weilPairingKM E E.smooth g N
        (EllipticCurve.Point.asSection E g x) (asSection_mem_torsionPoints E x hx)
        (EllipticCurve.Point.asSection E g y) (asSection_mem_torsionPoints E y hy) :
          Γ(T, ⊤)ˣ) : Γ(T, ⊤)) := by
  -- generalize the classifying map so the base can be substituted (the raw lift mentions
  -- `x`, so `subst` on it directly would fail the occurs-check)
  obtain ⟨k, hgen⟩ : ∃ k, (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
      (by simp) : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) = k := ⟨_, rfl⟩
  have hk : k ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) = g := by
    rw [← hgen, ← Category.assoc, pullback.lift_fst, E.pointToTorsion_torsionπ]
  subst hk
  -- naturality of the points description along `k`, at the universal subtype element
  have hnat := muNPointsEquiv_natural S N
    (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) k
    ((muNPointsEquiv S N
      (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).symm
      ⟨((weilPairingKM E E.smooth
          (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
          N (univTorsionFst E N) (univTorsionFst_mem E N)
          (univTorsionSnd E N) (univTorsionSnd_mem E N) :
        Γ(pullback (E.torsionπ N) (E.torsionπ N), ⊤)ˣ) : Γ(pullback (E.torsionπ N)
          (E.torsionπ N), ⊤)),
        (Units.val_pow_eq_pow_val _ _).symm.trans
          ((congrArg Units.val (weilPairingKM_pow_eq_one E E.smooth
            (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N
            (univTorsionFst E N) (univTorsionFst_mem E N)
            (univTorsionSnd E N) (univTorsionSnd_mem E N))).trans Units.val_one)⟩)
  -- the evaluation is the equiv-value at the pair whose value component is
  -- `k ≫ weilPairing` (via `hgen`)
  have hpair : (E.weilPairingEval x y hx hy : Γ(T, ⊤)) =
      (muNPointsEquiv S N
        (k ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N))
        ⟨k ≫ ((muNPointsEquiv S N
            (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).symm
            ⟨((weilPairingKM E E.smooth
                (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
                N (univTorsionFst E N) (univTorsionFst_mem E N)
                (univTorsionSnd E N) (univTorsionSnd_mem E N) :
              Γ(pullback (E.torsionπ N) (E.torsionπ N), ⊤)ˣ) : Γ(pullback (E.torsionπ N)
                (E.torsionπ N), ⊤)),
              (Units.val_pow_eq_pow_val _ _).symm.trans
                ((congrArg Units.val (weilPairingKM_pow_eq_one E E.smooth
                  (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N
                  (univTorsionFst E N) (univTorsionFst_mem E N)
                  (univTorsionSnd E N) (univTorsionSnd_mem E N))).trans
                  Units.val_one)⟩).1, by
          rw [Category.assoc]
          exact congrArg _ ((muNPointsEquiv S N _).symm _).2⟩ : Γ(T, ⊤)) :=
    congrArg (fun h => (muNPointsEquiv S N
        (k ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)) h : Γ(T, ⊤)))
      (Subtype.ext (congrArg (· ≫ E.weilPairing N) hgen))
  refine hpair.trans (hnat.trans ?_)
  -- the universal value reads back through `apply_symm_apply`
  have happ := congrArg Subtype.val ((muNPointsEquiv S N
    (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).apply_symm_apply
    ⟨((weilPairingKM E E.smooth
        (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        N (univTorsionFst E N) (univTorsionFst_mem E N)
        (univTorsionSnd E N) (univTorsionSnd_mem E N) :
      Γ(pullback (E.torsionπ N) (E.torsionπ N), ⊤)ˣ) : Γ(pullback (E.torsionπ N)
        (E.torsionπ N), ⊤)),
      (Units.val_pow_eq_pow_val _ _).symm.trans
        ((congrArg Units.val (weilPairingKM_pow_eq_one E E.smooth
          (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N
          (univTorsionFst E N) (univTorsionFst_mem E N)
          (univTorsionSnd E N) (univTorsionSnd_mem E N))).trans Units.val_one)⟩)
  refine (congrArg (Scheme.Γ.map k.op).hom happ).trans ?_
  -- identify with the restricted canonical value: the restriction law at `k` plus the
  -- reconstruction of the tautological points (transported along `hgen`)
  have hrx := (restrictBase_congr_hom E
    (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) hgen.symm rfl
    (congrArg (· ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)) hgen)
    (univTorsionFst E N)).trans
    (restrictBase_univTorsionFst E x y hx hy
      (congrArg (· ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)) hgen))
  have hry := (restrictBase_congr_hom E
    (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) hgen.symm rfl
    (congrArg (· ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)) hgen)
    (univTorsionSnd E N)).trans
    (restrictBase_univTorsionSnd E x y hx hy
      (congrArg (· ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)) hgen))
  have hrestr := weilPairingKM_restrictBase E E.smooth
    (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) k rfl N
    (univTorsionFst E N) (univTorsionFst_mem E N)
    (univTorsionSnd E N) (univTorsionSnd_mem E N)
  have hcongrpts := weilPairingKM_congr E E.smooth
    (k ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)) N
    hrx hry
    (restrictBase_mem_torsionPoints E _ _ rfl (univTorsionFst_mem E N))
    (restrictBase_mem_torsionPoints E _ _ rfl (univTorsionSnd_mem E N))
    (asSection_mem_torsionPoints E x hx) (asSection_mem_torsionPoints E y hy)
  refine Eq.trans ?_ (congrArg Units.val (hcongrpts.symm.trans hrestr).symm)
  -- the two `Γ`-map spellings agree
  show (Scheme.Γ.map k.op).hom _ = (k.appLE ⊤ ⊤ le_rfl).hom _
  rw [Scheme.Γ_map_op]
  rw [show (k.appLE ⊤ ⊤ le_rfl : Γ(pullback (E.torsionπ N) (E.torsionπ N), ⊤) ⟶
      Γ(T, ⊤)) = k.app ⊤ from Scheme.Hom.appLE_eq_app _]
  rfl

/-- **(T-A6d closure)** The raw kill-by-`N` condition is closed under addition of points.
This is the lemma the bilinearity specifications' docstrings call `point_add_killedBy`;
it was referenced but never stated. -/
theorem point_add_killedBy {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} {x y : E.Point g}
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (x + y).1 ≫ E.mulByHom N = g ≫ E.zero := by
  have hx' := (E.smul_eq_zero_iff_comp_mulByHom g N x).mpr hx
  have hy' := (E.smul_eq_zero_iff_comp_mulByHom g N y).mpr hy
  exact (E.smul_eq_zero_iff_comp_mulByHom g N (x + y)).mp
    (by rw [smul_add, hx', hy', add_zero])

/-- **(T-A6d closure)** The raw kill-by-`N` condition is closed under integer scalars. -/
theorem point_zsmul_killedBy {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} {x : E.Point g} (a : ℤ)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (a • x).1 ≫ E.mulByHom N = g ≫ E.zero := by
  have hx' := (E.smul_eq_zero_iff_comp_mulByHom g N x).mpr hx
  refine (E.smul_eq_zero_iff_comp_mulByHom g N (a • x)).mp ?_
  rw [smul_comm, hx', smul_zero]

/-- `weilPairingEval` depends only on the points: the kill-by-`N` witnesses are
proof-irrelevant. -/
theorem weilPairingEval_congr {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    {x x' y y' : E.Point g} (ex : x = x') (ey : y = y')
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = g ≫ E.zero) (hy' : y'.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x y hx hy : Γ(T, ⊤)) = E.weilPairingEval x' y' hx' hy' := by
  subst ex; subst ey; rfl

/-- The zero point is `N`-torsion. -/
theorem point_zero_killedBy {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} :
    ((0 : E.Point g)).1 ≫ E.mulByHom N = g ≫ E.zero :=
  (E.smul_eq_zero_iff_comp_mulByHom g N 0).mp (smul_zero _)

/-- **(T-C2 = KM 2.8, bilinearity)** `e_N(x + x', y) = e_N(x, y) · e_N(x', y)` on
`T`-points, where the addition is the registered group structure (DS2) and the raw
kill-by-`N` hypotheses transport by `point_add_killedBy` (T-A6d).
Source: KM 2.8.2; Silverman III.8.1(a). -/
theorem weilPairingEval_add_left {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x x' y : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hxx' : (x + x').1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (x + x') y hxx' hy : Γ(T, ⊤)) =
      E.weilPairingEval x y hx hy * E.weilPairingEval x' y hx' hy := by sorry

/-- **(T-C2-R = KM 2.8.2, bilinearity in the second slot)** The mirror of
`weilPairingEval_add_left`: `e_N(x, y + y') = e_N(x, y) · e_N(x, y')` on
`T`-points. Same source and status as the left law — the DS4 bilinearity
covers both slots (KM 2.8.2; Silverman III.8.1(a)). -/
theorem weilPairingEval_add_right {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y y' : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) (hy' : y'.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hyy' : (y + y').1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x (y + y') hx hyy' : Γ(T, ⊤)) =
      E.weilPairingEval x y hx hy * E.weilPairingEval x y' hx hy' := by sorry

/-- Pairing with the zero point is trivial — from bilinearity in the second slot alone
(`e(x,0) = e(x,0)²` and `e(x,0)` is a unit). -/
theorem weilPairingEval_zero_right {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x (0 : E.Point g) hx E.point_zero_killedBy : Γ(T, ⊤)) = 1 := by
  have h := E.weilPairingEval_add_right x (0 : E.Point g) (0 : E.Point g) hx
    E.point_zero_killedBy E.point_zero_killedBy
    (by rw [add_zero]; exact E.point_zero_killedBy)
  rw [E.weilPairingEval_congr (x := x) (x' := x) (y := (0 : E.Point g) + 0)
      (y' := (0 : E.Point g)) rfl (add_zero _) _ _ hx E.point_zero_killedBy] at h
  have hunit : IsUnit (E.weilPairingEval x (0 : E.Point g) hx
      E.point_zero_killedBy : Γ(T, ⊤)) :=
    isUnit_of_pow_eq_one (E.weilPairingEval x (0 : E.Point g) hx E.point_zero_killedBy).2
  refine (hunit.mul_left_inj).mp ?_
  rw [one_mul]
  exact h.symm

/-- The power law in the second slot for natural-number scalars, by induction from
bilinearity. -/
theorem weilPairingEval_nsmul_right {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) (n : ℕ) :
    (E.weilPairingEval x ((n : ℤ) • y) hx (E.point_zsmul_killedBy (n : ℤ) hy) :
        Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      refine Eq.trans ?_ (E.weilPairingEval_zero_right x hx)
      exact E.weilPairingEval_congr rfl (by rw [Nat.cast_zero, zero_smul]) _ _ hx
        E.point_zero_killedBy
  | succ n ih =>
      have hsplit : ((n + 1 : ℕ) : ℤ) • y = (n : ℤ) • y + y := by
        push_cast
        rw [add_smul, one_smul]
      have hstep := E.weilPairingEval_add_right x ((n : ℤ) • y) y hx
        (E.point_zsmul_killedBy (n : ℤ) hy) hy
        (E.point_add_killedBy (E.point_zsmul_killedBy (n : ℤ) hy) hy)
      calc (E.weilPairingEval x (((n + 1 : ℕ) : ℤ) • y) hx
              (E.point_zsmul_killedBy _ hy) : Γ(T, ⊤))
          = (E.weilPairingEval x ((n : ℤ) • y + y) hx
              (E.point_add_killedBy (E.point_zsmul_killedBy (n : ℤ) hy) hy) : Γ(T, ⊤)) :=
            E.weilPairingEval_congr rfl hsplit _ _ hx _
        _ = _ := hstep
        _ = (E.weilPairingEval x y hx hy : Γ(T, ⊤)) ^ (n + 1) := by
            rw [ih, pow_succ]

/-- **(T-C2-R′ = KM 2.8.2, integer scalars in the second slot)** The power law
`e_N(x, a • y) = e_N(x, y)^(a mod N)` (exponent taken as the canonical
non-negative representative), the iterated form of the right bilinearity.
Source: KM 2.8.2; Silverman III.8.1(a).

**PROVED (2026-08-02) — no longer a register entry.** Bilinearity in the second slot
already forces it. The `mod N` in the statement is not an extra hypothesis but a
consequence: `y` is `N`-torsion, so `a • y = (a % N) • y` outright, and `a % N` is
non-negative, which reduces the integer law to the natural-number induction. -/
theorem weilPairingEval_zsmul_right {N : ℕ} [NeZero N] {T : Scheme.{u}}
    {g : T ⟶ S} (x y : E.Point g) (a : ℤ)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hay : (a • y).1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x (a • y) hx hay : Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat) := by
  have hNy : (N : ℤ) • y = 0 := (E.smul_eq_zero_iff_comp_mulByHom g N y).mpr hy
  have hnn : (0 : ℤ) ≤ a % (N : ℤ) :=
    Int.emod_nonneg a (Int.natCast_ne_zero.mpr (NeZero.ne N))
  -- `y` is `N`-torsion, so only `a mod N` matters — and that is `≥ 0`
  have hred : a • y = (((a % (N : ℤ)).toNat : ℕ) : ℤ) • y := by
    rw [Int.toNat_of_nonneg hnn]
    conv_lhs => rw [← Int.mul_ediv_add_emod a (N : ℤ)]
    rw [add_smul, mul_smul, smul_comm, hNy, smul_zero, zero_add]
  refine Eq.trans ?_ (E.weilPairingEval_nsmul_right x y hx hy ((a % (N : ℤ)).toNat))
  exact E.weilPairingEval_congr rfl hred _ _ hx _

/-- **(T-C2′ = KM 2.8, alternating)** `e_N(x, x) = 1`.
Source: KM 2.8; Silverman III.8.1(b). -/
theorem weilPairingEval_self {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by sorry

/-! ### Consequences of the register (proved, not registered)

The four bilinearity/alternation entries above generate more of the pairing's algebra than
the register admits. Everything in this section is **derived**: the torsion-closure lemmas
the bilinearity docstrings already refer to as `point_add_killedBy`, the first-slot power
law that mirrors the registered second-slot one, and — most importantly — the symplectic
formula `weilPairingEval_symplectic`, which is the register's most-consumed entry
(11 call sites in `RhoPairingBridge`, `RhoSections` and `YRho`) and needs no new input.
-/

/-- **Antisymmetry** `e_N(x,y) · e_N(y,x) = 1`, from alternation applied to `x + y` and
bilinearity in both slots. Silverman III.8.1(c) derives antisymmetry from (a) and (b) in
exactly this way. -/
theorem weilPairingEval_antisymm {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x y hx hy : Γ(T, ⊤)) * E.weilPairingEval y x hy hx = 1 := by
  have hxy := E.point_add_killedBy hx hy
  have h := E.weilPairingEval_self (x + y) hxy
  rw [E.weilPairingEval_add_left x y (x + y) hx hy hxy hxy,
    E.weilPairingEval_add_right x x y hx hx hy hxy,
    E.weilPairingEval_add_right y x y hy hx hy hxy,
    E.weilPairingEval_self x hx, E.weilPairingEval_self y hy, one_mul, mul_one] at h
  exact h

/-- **The power law in the first slot** `e_N(a • x, y) = e_N(x, y)^(a mod N)` — the mirror
of the registered `weilPairingEval_zsmul_right`, obtained from it by antisymmetry. -/
theorem weilPairingEval_zsmul_left {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g) (a : ℤ)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hax : (a • x).1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (a • x) y hax hy : Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat) := by
  have hef : (E.weilPairingEval x y hx hy : Γ(T, ⊤)) *
      E.weilPairingEval y x hy hx = 1 := E.weilPairingEval_antisymm x y hx hy
  have h1 : (E.weilPairingEval (a • x) y hax hy : Γ(T, ⊤)) *
      E.weilPairingEval y (a • x) hy hax = 1 :=
    E.weilPairingEval_antisymm (a • x) y hax hy
  have h2 : (E.weilPairingEval y (a • x) hy hax : Γ(T, ⊤)) =
      (E.weilPairingEval y x hy hx : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat) :=
    E.weilPairingEval_zsmul_right y x a hy hx hax
  have hunit : IsUnit ((E.weilPairingEval y x hy hx : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat)) :=
    (isUnit_of_pow_eq_one (E.weilPairingEval y x hy hx).2).pow _
  refine (hunit.mul_left_inj).mp ?_
  rw [pow_mul_pow_eq_one hef, ← h2]
  exact h1

/-- **(T-C3 = KM 2.8, fibrewise nondegeneracy — `N` invertible)** On a geometric point of
`S` where `N` is invertible, the pairing is nondegenerate: a torsion point pairing
trivially with everything is zero.

The hypothesis `(N : k) ≠ 0` is **necessary**: for `k = k̄` of characteristic `p ∣ N` and
`E/k` ordinary, `E[p](k)` has a nonzero (étale) point while `μ_p(k) = {1}`, so every
pairing *value* is `1` — pointwise nondegeneracy fails, and only the scheme-theoretic
perfectness `E[N] ≅ E[N]^D` (Cartier duality, API gap AG-CD) survives. This fibrewise
form is perfectness's faithful surrogate when `N` is invertible, sufficient for the
`Y(ρ,p)` application over `ℚ`, and is where the comparison with the HasseWeil field-level
pairing enters — `T-C4`. Source: KM 2.8; Silverman III.8.1(c) (which carries the same
invertibility, via `char K ∤ N`). Statement fixed 2026-07-30 (adversarial review):
added `hNk`. -/
theorem weilPairingEval_nondegenerate {N : ℕ} [NeZero N]
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0) (t : Spec (.of k) ⟶ S)
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (h : ∀ (y : E.Point t) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      (E.weilPairingEval x y hx hy : Γ(Spec (.of k), ⊤)) = 1) :
    x = E.zeroPoint t := by sorry

/-- **(T-C2a, base-change naturality — required pinning spec per expert review Q4:
"compatible with arbitrary base change", since fibrewise agreement does not pin
morphisms over non-reduced bases)** Restriction along `k : T' ⟶ T` commutes with the
pairing: `e_N(x|_{T'}, y|_{T'}) = (e_N(x,y))|_{T'}` in `Γ(T', O)`.

**PROVED (2026-08-02) — no longer a register entry.** This specification needs nothing
about the pairing beyond `weilPairing_over`: restriction is naturality of the points
dictionary (`muNPointsEquiv_natural`) composed with naturality of `pullback.lift`
(`comp_pointToTorsion`). Whatever construction eventually fills the DS4 data-sorry, this
law comes for free. -/
theorem weilPairingEval_restrict {N : ℕ} [NeZero N] {T T' : Scheme.{u}} {g : T ⟶ S}
    (k : T' ⟶ T) (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : (Point.restrict E k x).1 ≫ E.mulByHom N = (k ≫ g) ≫ E.zero)
    (hy' : (Point.restrict E k y).1 ≫ E.mulByHom N = (k ≫ g) ≫ E.zero) :
    (E.weilPairingEval (Point.restrict E k x) (Point.restrict E k y) hx' hy' : Γ(T', ⊤))
      = (Scheme.Γ.map k.op).hom (E.weilPairingEval x y hx hy : Γ(T, ⊤)) := by
  -- The pairing morphism itself never enters: restriction is naturality of the points
  -- dictionary composed with naturality of `pullback.lift`, so this specification is a
  -- formal consequence of `weilPairing_over` alone.
  have hc : E.pointToTorsion x hx ≫ E.torsionπ N =
      E.pointToTorsion y hy ≫ E.torsionπ N := by
    rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]
  have hc' : E.pointToTorsion (Point.restrict E k x) hx' ≫ E.torsionπ N =
      E.pointToTorsion (Point.restrict E k y) hy' ≫ E.torsionπ N := by
    rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]
  have hlift : pullback.lift (E.pointToTorsion (Point.restrict E k x) hx')
        (E.pointToTorsion (Point.restrict E k y) hy') hc' =
      k ≫ pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) hc := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst,
        E.pointToTorsion_restrict k x hx hx']
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd,
        E.pointToTorsion_restrict k y hy hy']
  have hnat := muNPointsEquiv_natural S N g k
    ⟨pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) hc ≫
        E.weilPairing N, by
      rw [Category.assoc, E.weilPairing_over N, ← Category.assoc,
        pullback.lift_fst, E.pointToTorsion_torsionπ]⟩
  rw [Scheme.Γ_map_op]
  refine Eq.trans ?_ hnat
  refine congrArg (fun v => ((muNPointsEquiv S N (k ≫ g) v : Γ(T', ⊤)))) (Subtype.ext ?_)
  simp only [hlift, Category.assoc]

/-- **(T-C2b, divisibility — expert review Q5: "compatibility with N ∣ M")** For
points killed by `N`, the `N·M`-pairing is the `M`-th power of the `N`-pairing:
`e_{NM}(x, y) = e_N(x, y)^M`. (Lattice check: for `x = a/N`, `y = b/N`,
`e_N = exp(2πi(ad−bc)/N)` and as `NM`-torsion points `e_{NM} = e_N^M`.)
Source: Silverman III.8.4-type compatibility; ⧗KM 2.8 for the KM form. -/
theorem weilPairingEval_mul {N M : ℕ} [NeZero N] [NeZero M] {T : Scheme.{u}}
    {g : T ⟶ S} (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x.1 ≫ E.mulByHom (N * M) = g ≫ E.zero)
    (hy' : y.1 ≫ E.mulByHom (N * M) = g ≫ E.zero) :
    (haveI : NeZero (N * M) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩;
      (E.weilPairingEval (N := N * M) x y hx' hy' : Γ(T, ⊤))) =
      (E.weilPairingEval (N := N) x y hx hy : Γ(T, ⊤)) ^ M := by sorry

/-- **(T-C2c, the symplectic-formula pin — expert review Q6, Silverman convention)**
On a pair of torsion points, `e_N(aP + bQ, cP + dQ) = e_N(P,Q)^{ad − bc}` (exponent
taken mod `N`). Together with Galois equivariance over fields (recorded in ticket
`T-C4`) and `det ∘ ρ_E = χ_N`, this fixes the project's normalisation once and for
all.

**PROVED (2026-08-02) — no longer a register entry.** This was the register's
most-consumed sorry (11 call sites) and it needs no new input: expand both slots by
bilinearity, strip the four scalars by the two power laws, kill the diagonal terms by
alternation, and cancel the off-diagonal one against `e(Q,P)` by antisymmetry. It is
exactly Silverman III.8.1(a)+(b)+(c) ⟹ the determinant law, the same derivation as the
field-level `weilPairing_gl2` in `WeilPairing/FieldPairingDet.lean`. -/
theorem weilPairingEval_symplectic {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) (a b c d : ℤ)
    (hP : P.1 ≫ E.mulByHom N = g ≫ E.zero) (hQ : Q.1 ≫ E.mulByHom N = g ≫ E.zero)
    (h₁ : (a • P + b • Q).1 ≫ E.mulByHom N = g ≫ E.zero)
    (h₂ : (c • P + d • Q).1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (a • P + b • Q) (c • P + d • Q) h₁ h₂ : Γ(T, ⊤)) =
      (E.weilPairingEval P Q hP hQ : Γ(T, ⊤)) ^ (((a * d - b * c) % (N : ℤ)).toNat) := by
  have haP := E.point_zsmul_killedBy a hP
  have hbQ := E.point_zsmul_killedBy b hQ
  have hcP := E.point_zsmul_killedBy c hP
  have hdQ := E.point_zsmul_killedBy d hQ
  -- expand both slots
  rw [E.weilPairingEval_add_left (a • P) (b • Q) (c • P + d • Q) haP hbQ h₂ h₁,
    E.weilPairingEval_add_right (a • P) (c • P) (d • Q) haP hcP hdQ h₂,
    E.weilPairingEval_add_right (b • Q) (c • P) (d • Q) hbQ hcP hdQ h₂]
  -- strip the left scalars, then the right ones
  rw [E.weilPairingEval_zsmul_left P (c • P) a hP hcP haP,
    E.weilPairingEval_zsmul_left P (d • Q) a hP hdQ haP,
    E.weilPairingEval_zsmul_left Q (c • P) b hQ hcP hbQ,
    E.weilPairingEval_zsmul_left Q (d • Q) b hQ hdQ hbQ,
    E.weilPairingEval_zsmul_right P P c hP hP hcP,
    E.weilPairingEval_zsmul_right P Q d hP hQ hdQ,
    E.weilPairingEval_zsmul_right Q P c hQ hP hcP,
    E.weilPairingEval_zsmul_right Q Q d hQ hQ hdQ]
  -- the diagonal terms are `1`
  rw [E.weilPairingEval_self P hP, E.weilPairingEval_self Q hQ, one_pow, one_pow,
    one_pow, one_pow, one_mul, mul_one]
  -- collect the two surviving exponents
  rw [pow_toNat_emod_mul (E.weilPairingEval P Q hP hQ).2,
    pow_toNat_emod_mul (E.weilPairingEval Q P hQ hP).2]
  -- cancel `e(Q,P)^{bc}` against `e(P,Q)^{bc}` using antisymmetry
  have hanti : (E.weilPairingEval Q P hQ hP : Γ(T, ⊤)) *
      E.weilPairingEval P Q hP hQ = 1 := by
    rw [mul_comm]; exact E.weilPairingEval_antisymm P Q hP hQ
  have hunit : IsUnit ((E.weilPairingEval P Q hP hQ : Γ(T, ⊤)) ^
      ((b * c % (N : ℤ)).toNat)) :=
    (isUnit_of_pow_eq_one (E.weilPairingEval P Q hP hQ).2).pow _
  refine (hunit.mul_left_inj).mp ?_
  rw [pow_toNat_emod_add (E.weilPairingEval P Q hP hQ).2, sub_add_cancel, mul_assoc,
    pow_mul_pow_eq_one hanti, mul_one]

end EllipticCurve

end ModularCurves
