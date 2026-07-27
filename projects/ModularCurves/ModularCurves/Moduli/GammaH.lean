/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.Groupoid
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.Moduli.PullSectionCanonicity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import ModularCurves.EllipticCurve.MulByHomUnramified
import ModularCurves.Moduli.NaiveProblems

/-!
# General level structures P_H, and full level N over an arbitrary base

The level-uniform layer, answering "what about other levels, and full level N?"
concretely (owner question, 2026-07-05; Loeffler §3.8; KM Ch. 3–5, 7).

## Contents

* The `GL₂(ℤ/N)`-action on full level structures (a full level structure is an
  isomorphism `(ℤ/N)² ≅ E[N]`; the group acts by precomposition — in the `(P,Q)`
  coordinates `g • (P,Q) = (g₁₁P + g₂₁Q, g₁₂P + g₂₂Q)`).
* For each subgroup `H ≤ GL₂(ℤ/N)`, the moduli problem `P_H` of `H`-orbits of full
  level structures (Loeffler Fact 3.8.1, verbatim: "`P_H(E/k̄) = {H`-orbits of
  isomorphisms `(ℤ/N)² ≅ E[N]}`"), specialising to `Γ(N)` (`H = 1`), `Γ₁(N)`
  (`H = {(1 *; 0 *)}`), `Γ₀(N)` (`H = {(* *; 0 *)}`).
* **Relative representability of `P_H`** (Loeffler Prop 3.8.2, verbatim: "P_H is
  relatively representable and étale over `Ell/ℤ[1/N]` … For `H = {1}` … it is an open
  subscheme of `E[N] ×_S E[N]` given by non-vanishing of Weil pairings. For general
  `H` just take the quotient of this by `H`.").
* **The rigidity criterion** (Loeffler Prop 3.8.3, verbatim: "`P_H` is rigid on
  `Ell/R[1/6]` if and only if the preimage in `SL₂(ℤ)` of `H ∩ SL₂(ℤ/N)` contains no
  elements of finite order (i.e. has no elliptic points and does not contain `−1`)").
* **Fine modular curves of arbitrary level**: rigid ⟹ representable, smooth over
  `ℤ[1/N]` (Loeffler §3.8: "there is a scheme `Y = Y_{P_H}` … One can check that
  `Y_{P_H}` is smooth over `ℤ[1/N]`").
* **Full level N over an arbitrary base (Drinfeld form)**: the problem is defined
  with no invertibility hypothesis (that is the point of the Drinfeld register), and
  its representability is stated for `N ≥ 3` **with `N` invertible** (GME Thm 2.6.8
  scope). The over-ℤ refinement is KM 4.7.2/5.1 territory (⧗KM) — NOT stated here:
  the bare over-ℤ form is false (supersingular `(0,0)` in char `p ∣ N` is a Drinfeld
  structure fixed by `[-1]`), and GME's in-hand over-ℤ Aut-triviality needs coprime
  `m, n ≥ 3` dividing `N`. Cut the over-ℤ statements verbatim when the full KM text
  lands.
* **The honest stack content at small N**: for `N ≤ 2` the set-valued problem is NOT
  rigid (`[-1]` acts trivially on `E[2]`), so there is no fine scheme — the object of
  record is the levelled groupoid (`FullLevelGroupoid`), per design D6. Coarse spaces:
  `Moduli/Coarse.lean`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

-- The `MulByHomFibresGlobal` import subtree (BB-QF closure via `Torsion`) enlarges the
-- instance pool; `map_zsmul`/`map_zero` synthesis on `≃+` needs more headroom here.
set_option synthInstance.maxHeartbeats 80000

namespace ModularCurves

variable {S : Scheme.{u}}

namespace EllipticCurve

/-- A (naive) full level-`N` point: a pair of sections forming a naive full level-`N`
structure. The bundled object on which `GL₂(ℤ/N)` acts. -/
def FullLevelPt (E : EllipticCurve S) (N : ℕ) [NeZero N] : Type u :=
  { PQ : E.Section × E.Section // E.IsNaiveFullLevel N PQ.1 PQ.2 }

variable (E : EllipticCurve S)

/-- On an element killed by `N`, an integer scalar depends only on its residue mod `N`:
if `a ≡ b (mod N)` in `ZMod N`, then `a • R = b • R`. The workhorse for lifting `ZMod N`
matrix arithmetic (via `ZMod.val`) onto `N`-torsion points. -/
theorem zsmul_eq_of_intCast_eq {G : Type*} [AddCommGroup G] {N : ℕ} (R : G)
    (hR : (N : ℤ) • R = 0) {a b : ℤ} (h : (a : ZMod N) = (b : ZMod N)) :
    a • R = b • R := by
  have hdvd : (N : ℤ) ∣ (a - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h, sub_self]
  obtain ⟨j, hj⟩ := hdvd
  have hz : (a - b) • R = 0 := by rw [hj, mul_comm, mul_zsmul, hR, smul_zero]
  rw [sub_zsmul] at hz
  exact add_neg_eq_zero.mp hz

/-- Reduction step for `GL₂`-recovery: a `ZMod N`-linear combination
`(a.val)•P' + (b.val)•Q'` of the transformed points `P' = m₀₀·pp + m₁₀·pq`,
`Q' = m₀₁·pp + m₁₁·pq` contracts, on `N`-torsion `pp, pq`, to the combination with
`ZMod N`-multiplied coefficients. -/
theorem recover_combo {N : ℕ} [NeZero N] {T : Scheme.{u}} (t : T ⟶ S)
    (pp pq P' Q' : E.Point t) (hpp : (N : ℤ) • pp = 0) (hpq : (N : ℤ) • pq = 0)
    (m00 m10 m01 m11 a b : ZMod N)
    (hP' : P' = (m00.val : ℤ) • pp + (m10.val : ℤ) • pq)
    (hQ' : Q' = (m01.val : ℤ) • pp + (m11.val : ℤ) • pq) :
    (a.val : ℤ) • P' + (b.val : ℤ) • Q'
      = ((a * m00 + b * m01).val : ℤ) • pp + ((a * m10 + b * m11).val : ℤ) • pq := by
  have key : (a.val : ℤ) • P' + (b.val : ℤ) • Q'
      = ((a.val : ℤ) * (m00.val : ℤ) + (b.val : ℤ) * (m01.val : ℤ)) • pp
        + ((a.val : ℤ) * (m10.val : ℤ) + (b.val : ℤ) * (m11.val : ℤ)) • pq := by
    rw [hP', hQ']; module
  rw [key]
  congr 1
  · exact zsmul_eq_of_intCast_eq pp hpp
      (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
  · exact zsmul_eq_of_intCast_eq pq hpq
      (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)

/-- The `GL₂(ℤ/N)`-action on full level structures, by precomposition of the
isomorphism `(ℤ/N)² ≅ E[N]`: in coordinates,
`g • (P, Q) = (g₁₁·P + g₂₁·Q, g₁₂·P + g₂₂·Q)` (entries lifted via `ZMod.val`;
well-defined because level points are killed by `N`). Membership preservation is
`T-H2`. Source: Loeffler Fact 3.8.1 ("H-orbits of isomorphisms (ℤ/N)² ≅ E[N]"). -/
noncomputable def glSmul {N : ℕ} [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.FullLevelPt N :=
  let m : Matrix (Fin 2) (Fin 2) (ZMod N) := g
  ⟨((((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2,
     ((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)),
    by
      have hP : (N : ℤ) • L.1.1 = 0 := L.2.1.1
      have hQ : (N : ℤ) • L.1.2 = 0 := L.2.1.2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [smul_add, smul_comm (N : ℤ) ((m 0 0).val : ℤ),
          smul_comm (N : ℤ) ((m 1 0).val : ℤ), hP, hQ, smul_zero, smul_zero, add_zero]
      · rw [smul_add, smul_comm (N : ℤ) ((m 0 1).val : ℤ),
          smul_comm (N : ℤ) ((m 1 1).val : ℤ), hP, hQ, smul_zero, smul_zero, add_zero]
      · intro k _ _ t x hx
        set pp := Point.pull E t L.1.1 with hpp_def
        set pq := Point.pull E t L.1.2 with hpq_def
        set gi := (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) (ZMod N)) with hgi_def
        have hppN : (N : ℤ) • pp = 0 := by
          rw [hpp_def, ← Point.pull_zsmul, hP, Point.pull_zero]
        have hpqN : (N : ℤ) • pq = 0 := by
          rw [hpq_def, ← Point.pull_zsmul, hQ, Point.pull_zero]
        have hPP : Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2)
            = ((m 0 0).val : ℤ) • pp + ((m 1 0).val : ℤ) • pq := by
          rw [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul, ← hpp_def, ← hpq_def]
        have hQQ : Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)
            = ((m 0 1).val : ℤ) • pp + ((m 1 1).val : ℤ) • pq := by
          rw [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul, ← hpp_def, ← hpq_def]
        have hgg : m * gi = 1 := by
          change (↑g : Matrix (Fin 2) (Fin 2) (ZMod N)) * gi = 1
          rw [hgi_def, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.GeneralLinearGroup.coe_one]
        have e00 : m 0 0 * gi 0 0 + m 0 1 * gi 1 0 = 1 := by
          have h := congrFun (congrFun hgg 0) 0
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
        have e10 : m 1 0 * gi 0 0 + m 1 1 * gi 1 0 = 0 := by
          have h := congrFun (congrFun hgg 1) 0
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
        have e01 : m 0 0 * gi 0 1 + m 0 1 * gi 1 1 = 0 := by
          have h := congrFun (congrFun hgg 0) 1
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
        have e11 : m 1 0 * gi 0 1 + m 1 1 * gi 1 1 = 1 := by
          have h := congrFun (congrFun hgg 1) 1
          simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
        have hpp_mem : pp ∈ AddSubgroup.closure
            {Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2),
             Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)} := by
          have hrec := recover_combo E t pp pq
            (Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2))
            (Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2))
            hppN hpqN (m 0 0) (m 1 0) (m 0 1) (m 1 1) (gi 0 0) (gi 1 0) hPP hQQ
          have key : ((gi 0 0).val : ℤ) •
                Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2)
              + ((gi 1 0).val : ℤ) •
                Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2) = pp := by
            rw [hrec,
              zsmul_eq_of_intCast_eq pp hppN
                (a := ((gi 0 0 * m 0 0 + gi 1 0 * m 0 1).val : ℤ)) (b := 1)
                (by push_cast [ZMod.natCast_val, ZMod.cast_id]; linear_combination e00),
              zsmul_eq_of_intCast_eq pq hpqN
                (a := ((gi 0 0 * m 1 0 + gi 1 0 * m 1 1).val : ℤ)) (b := 0)
                (by push_cast [ZMod.natCast_val, ZMod.cast_id]; linear_combination e10),
              one_zsmul, zero_zsmul, add_zero]
          rw [← key]
          exact add_mem (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) _)
            (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) _)
        have hpq_mem : pq ∈ AddSubgroup.closure
            {Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2),
             Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)} := by
          have hrec := recover_combo E t pp pq
            (Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2))
            (Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2))
            hppN hpqN (m 0 0) (m 1 0) (m 0 1) (m 1 1) (gi 0 1) (gi 1 1) hPP hQQ
          have key : ((gi 0 1).val : ℤ) •
                Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2)
              + ((gi 1 1).val : ℤ) •
                Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2) = pq := by
            rw [hrec,
              zsmul_eq_of_intCast_eq pp hppN
                (a := ((gi 0 1 * m 0 0 + gi 1 1 * m 0 1).val : ℤ)) (b := 0)
                (by push_cast [ZMod.natCast_val, ZMod.cast_id]; linear_combination e01),
              zsmul_eq_of_intCast_eq pq hpqN
                (a := ((gi 0 1 * m 1 0 + gi 1 1 * m 1 1).val : ℤ)) (b := 1)
                (by push_cast [ZMod.natCast_val, ZMod.cast_id]; linear_combination e11),
              zero_zsmul, one_zsmul, zero_add]
          rw [← key]
          exact add_mem (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) _)
            (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) _)
        have hmem := L.2.2 k t x hx
        rw [← hpp_def, ← hpq_def] at hmem
        have hle : AddSubgroup.closure {pp, pq} ≤ AddSubgroup.closure
            {Point.pull E t (((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2),
             Point.pull E t (((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)} := by
          rw [AddSubgroup.closure_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact hpp_mem
          · exact hpq_mem
        exact hle hmem⟩

/-- If `N • P = 0` then `m • P = 0` whenever `N ∣ m` — so `m • P` depends only on
`m mod N`. Used to lift `ZMod N` matrix entries via `ZMod.val`. -/
theorem smul_eq_zero_of_dvd {N : ℕ} (P : E.Section) (hP : (N : ℤ) • P = 0)
    {m : ℤ} (hm : (N : ℤ) ∣ m) : m • P = 0 := by
  obtain ⟨k, rfl⟩ := hm
  rw [mul_comm, mul_zsmul, hP, smul_zero]

/-- `((x : ZMod N).val : ℤ) • P` is additive in `x` when `P` is killed by `N`. -/
theorem val_smul_add {N : ℕ} [NeZero N] (P : E.Section) (hP : (N : ℤ) • P = 0)
    (x y : ZMod N) :
    (((x + y).val : ℤ) • P) = ((x.val : ℤ) • P) + ((y.val : ℤ) • P) := by
  have hv : (x + y).val = (x.val + y.val) % N := ZMod.val_add x y
  have hle : (x.val + y.val) % N ≤ x.val + y.val := Nat.mod_le _ _
  have hdvd : (N : ℤ) ∣ (((x.val + y.val : ℕ) : ℤ) - ((x + y).val : ℤ)) := by
    rw [hv, ← Nat.cast_sub hle]
    exact_mod_cast Nat.dvd_sub_mod (x.val + y.val)
  have h0 := smul_eq_zero_of_dvd E P hP hdvd
  have h1 : ((x.val + y.val : ℕ) : ℤ) • P = ((x + y).val : ℤ) • P := by
    rw [← sub_eq_zero, sub_eq_add_neg, ← neg_zsmul, ← add_zsmul]
    convert h0 using 2
    ring
  rw [← h1, Nat.cast_add, add_zsmul]

/-- `((x*y : ZMod N).val : ℤ) • P = (x.val * y.val) • P` when `P` is killed by `N`. -/
theorem val_smul_mul {N : ℕ} [NeZero N] (P : E.Section) (hP : (N : ℤ) • P = 0)
    (x y : ZMod N) :
    (((x * y).val : ℤ) • P) = ((x.val : ℤ) * (y.val : ℤ)) • P := by
  have hv : (x * y).val = (x.val * y.val) % N := ZMod.val_mul x y
  have hle : (x.val * y.val) % N ≤ x.val * y.val := Nat.mod_le _ _
  have hdvd : (N : ℤ) ∣ (((x.val * y.val : ℕ) : ℤ) - ((x * y).val : ℤ)) := by
    rw [hv, ← Nat.cast_sub hle]
    exact_mod_cast Nat.dvd_sub_mod (x.val * y.val)
  have h0 := smul_eq_zero_of_dvd E P hP hdvd
  have h1 : ((x.val * y.val : ℕ) : ℤ) • P = ((x * y).val : ℤ) • P := by
    rw [← sub_eq_zero, sub_eq_add_neg, ← neg_zsmul, ← add_zsmul]
    convert h0 using 2
    ring
  rw [← h1, Nat.cast_mul]

/-- The `GL₂`-action fixes level structures under the identity matrix (all `N`:
`ZMod.val_one` for `N ≥ 2`; for `N = 1`, level points are `0`). -/
theorem glSmul_one {N : ℕ} [NeZero N] (L : E.FullLevelPt N) :
    E.glSmul 1 L = L := by
  have hm : ∀ i j, (((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
      Matrix (Fin 2) (Fin 2) (ZMod N)) i j) = (1 : Matrix _ _ (ZMod N)) i j := by
    intro i j; rw [Matrix.GeneralLinearGroup.coe_one]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · simp only [glSmul, hm, Matrix.one_apply_eq, Matrix.one_apply_ne (show (1:Fin 2) ≠ 0 by decide)]
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) with h1 | h2
    · have hP : L.1.1 = 0 := by simpa [← h1] using L.2.1.1
      simp [hP]
    · haveI : Fact (1 < N) := ⟨h2⟩
      simp [ZMod.val_one, ZMod.val_zero]
  · simp only [glSmul, hm, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0:Fin 2) ≠ 1 by decide)]
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) with h1 | h2
    · have hQ : L.1.2 = 0 := by simpa [← h1] using L.2.1.2
      simp [hQ]
    · haveI : Fact (1 < N) := ⟨h2⟩
      simp [ZMod.val_one, ZMod.val_zero]

/-- **(T-H2a)** The action law. `glSmul` is *precomposition* of the trivialisation
`(ℤ/N)² ≅ E[N]` with `g`, hence a **right** action: `(φ∘g)∘h = φ∘(g*h)` reads
`(g*h) • L = h • (g • L)`. (Uses that level points are killed by `N`, so the
`ZMod.val` lifts compose correctly mod `N`.)

ADVERSARIAL FIX (2026-07-06): the previous left-action law `(g*h) • L = g • (h • L)`
was FALSE — by `Matrix.mul_apply` it asserts `(g*h) • L = (h*g) • L` for all `g, h`,
refuted on any honest basis of `E[N](ℂ)` by `g = (1 1; 0 1)`, `h = (1 0; 1 1)`.
H-orbits are unaffected (right orbits = left orbits as partitions). -/
theorem glSmul_mul {N : ℕ} [NeZero N]
    (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.glSmul (g * h) L = E.glSmul h (E.glSmul g L) := by
  have hP : (N : ℤ) • L.1.1 = 0 := L.2.1.1
  have hQ : (N : ℤ) • L.1.2 = 0 := L.2.1.2
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
  · simp only [glSmul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    rw [val_smul_add E L.1.1 hP, val_smul_add E L.1.2 hQ,
      val_smul_mul E L.1.1 hP, val_smul_mul E L.1.1 hP,
      val_smul_mul E L.1.2 hQ, val_smul_mul E L.1.2 hQ]
    module

/-- The `H`-orbit equivalence on full level structures, for `H ≤ GL₂(ℤ/N)`. -/
noncomputable def hOrbitSetoid {N : ℕ} [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
    Setoid (E.FullLevelPt N) :=
  ⟨fun L L' => ∃ g ∈ H, E.glSmul g L = L', by
    refine ⟨fun L => ⟨1, H.one_mem, E.glSmul_one L⟩, ?_, ?_⟩
    · rintro L L' ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, H.inv_mem hg, by
        rw [← E.glSmul_mul, mul_inv_cancel, E.glSmul_one]⟩
    · rintro L L' L'' ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
      exact ⟨g * g', H.mul_mem hg hg', by rw [E.glSmul_mul]⟩⟩

/-- **(T-H2b, membership)** The naive full-level condition is stable under base change:
killing transports through `pull_zsmul`/`asSection_zsmul`, and fibrewise generation
transports through the additive base-change point dictionary `Point.baseChangeEquiv`
(a geometric point of the base-changed curve is a geometric point of `E` over the
composite). -/
private lemma isNaiveFullLevel_pullAlong {T T' : Scheme.{u}} {E : EllipticCurve T}
    {N : ℕ} [NeZero N] (σ : T' ⟶ T) {P Q : E.Section}
    (h : E.IsNaiveFullLevel N P Q) :
    (E.baseChange σ).IsNaiveFullLevel N
      (Point.asSection E σ (Point.pull E σ P))
      (Point.asSection E σ (Point.pull E σ Q)) := by
  obtain ⟨⟨hP, hQ⟩, hgen⟩ := h
  have hzero : Point.asSection E σ (0 : E.Point σ) = (0 : (E.baseChange σ).Section) := by
    have h0 := Point.asSection_zsmul E σ 0 (0 : E.Point σ)
    simpa using h0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← Point.asSection_zsmul, ← Point.pull_zsmul, hP, Point.pull_zero, hzero]
  · rw [← Point.asSection_zsmul, ← Point.pull_zsmul, hQ, Point.pull_zero, hzero]
  · intro k _ _ t x hx
    have hdx : (N : ℤ) • Point.baseChangeEquiv E σ t x = 0 := by
      rw [← map_zsmul (Point.baseChangeEquiv E σ t), hx, map_zero]
    have hcompatP : Point.baseChangeEquiv E σ t
        (Point.pull (E.baseChange σ) t (Point.asSection E σ (Point.pull E σ P)))
        = Point.pull E (t ≫ σ) P := by
      refine Subtype.ext ?_
      exact (Category.assoc _ _ _).trans <|
        (congrArg (t ≫ ·) (Point.asSection_val_fst E σ _)).trans <|
        (Category.assoc _ _ _).symm
    have hcompatQ : Point.baseChangeEquiv E σ t
        (Point.pull (E.baseChange σ) t (Point.asSection E σ (Point.pull E σ Q)))
        = Point.pull E (t ≫ σ) Q := by
      refine Subtype.ext ?_
      exact (Category.assoc _ _ _).trans <|
        (congrArg (t ≫ ·) (Point.asSection_val_fst E σ _)).trans <|
        (Category.assoc _ _ _).symm
    have h1 := hgen k (t ≫ σ) (Point.baseChangeEquiv E σ t x) hdx
    rw [← hcompatP, ← hcompatQ] at h1
    have hKle : AddSubgroup.closure
        ({Point.baseChangeEquiv E σ t
            (Point.pull (E.baseChange σ) t (Point.asSection E σ (Point.pull E σ P))),
          Point.baseChangeEquiv E σ t
            (Point.pull (E.baseChange σ) t (Point.asSection E σ (Point.pull E σ Q)))} :
          Set (E.Point (t ≫ σ)))
        ≤ (AddSubgroup.closure
            {Point.pull (E.baseChange σ) t (Point.asSection E σ (Point.pull E σ P)),
             Point.pull (E.baseChange σ) t (Point.asSection E σ (Point.pull E σ Q))}).map
          (Point.baseChangeEquiv E σ t).toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro z (rfl | rfl)
      · exact ⟨_, AddSubgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨_, AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hKle h1
    exact ((Point.baseChangeEquiv E σ t).injective hyx) ▸ hy

/-- Pull a full level point back along a base morphism `σ : T' ⟶ T`: the level of the
base-changed curve. -/
noncomputable def FullLevelPt.pullAlong {T T' : Scheme.{u}} {E : EllipticCurve T}
    {N : ℕ} [NeZero N] (σ : T' ⟶ T) (L : E.FullLevelPt N) :
    (E.baseChange σ).FullLevelPt N :=
  ⟨(EllipticCurve.Point.asSection E σ
      ⟨σ ≫ L.1.1.1, by rw [Category.assoc, L.1.1.2, Category.comp_id]⟩,
    EllipticCurve.Point.asSection E σ
      ⟨σ ≫ L.1.2.1, by rw [Category.assoc, L.1.2.2, Category.comp_id]⟩),
    isNaiveFullLevel_pullAlong σ L.2⟩

end EllipticCurve

section GammaH

variable (R : CommRingCat.{u})

/-- **(T-H3a)** `pullSection` commutes with integer scalars (from the T-E4a
additivity). -/
theorem EllHom.pullSection_zsmul {X Y : EllObj R} (f : X ⟶ Y) (a : ℤ)
    (P : Y.curve.Section) :
    EllHom.pullSection R f (a • P) = a • EllHom.pullSection R f P :=
  map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f)
    (EllHom.pullSection_add R f)) a P

/-- **(T-H3b ★)** `pullSection` is `GL₂(ℤ/N)`-equivariant: `glSmul` is an integer
matrix acting through the section group, and `pullSection` is additive (T-E4a). -/
theorem EllHom.pullSection_glSmul {X Y : EllObj R} (f : X ⟶ Y) {N : ℕ} [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : Y.curve.FullLevelPt N) :
    X.curve.glSmul g
        ⟨⟨EllHom.pullSection R f L.1.1, EllHom.pullSection R f L.1.2⟩,
          EllHom.isNaiveFullLevel_pullSection R f L.2⟩ =
      ⟨⟨EllHom.pullSection R f (Y.curve.glSmul g L).1.1,
        EllHom.pullSection R f (Y.curve.glSmul g L).1.2⟩,
        EllHom.isNaiveFullLevel_pullSection R f (Y.curve.glSmul g L).2⟩ := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) •
        EllHom.pullSection R f L.1.1 +
      (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) •
        EllHom.pullSection R f L.1.2 =
      EllHom.pullSection R f
        ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • L.1.1 +
         (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • L.1.2)
    rw [EllHom.pullSection_add, EllHom.pullSection_zsmul, EllHom.pullSection_zsmul]
  · show (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) •
        EllHom.pullSection R f L.1.1 +
      (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) •
        EllHom.pullSection R f L.1.2 =
      EllHom.pullSection R f
        ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • L.1.1 +
         (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • L.1.2)
    rw [EllHom.pullSection_add, EllHom.pullSection_zsmul, EllHom.pullSection_zsmul]

/-- **The moduli problem `P_H`** for `H ≤ GL₂(ℤ/N)`: `E/S ↦ {H`-orbits of (naive) full
level-`N` structures on `E/S}`. Specialisations: `H = ⊥` is `[Γ(N)]`-naive
(`gammaHNaive_bot`); `H = {(1 *; 0 *)}` is `[Γ₁(N)]`; `H = {(* *; 0 *)}` is
`[Γ₀(N)]` (upper-triangular Borel). Source: Loeffler Fact 3.8.1; KM Ch. 3 + 7 (the
quotient presentation, ⧗KM for closure). Functor laws and orbit-compatibility of
section-pullback are `T-H3`. -/
noncomputable def gammaHNaiveProblem (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) : ModuliProblem R where
  obj X := Quotient (X.unop.curve.hOrbitSetoid H)
  map f := ↾Quotient.map
    (fun L => ⟨⟨EllHom.pullSection R f.unop L.1.1, EllHom.pullSection R f.unop L.1.2⟩,
      EllHom.isNaiveFullLevel_pullSection R f.unop L.2⟩)
    (by
      rintro L L' ⟨g, hg, rfl⟩
      exact ⟨g, hg, EllHom.pullSection_glSmul R f.unop g L⟩)
  map_id X := by
    ext L
    induction L using Quotient.ind with
    | _ L =>
      refine congrArg (Quotient.mk ((Opposite.unop X).curve.hOrbitSetoid H)) ?_
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact EllHom.pullSection_id R L.1.1
      · exact EllHom.pullSection_id R L.1.2
  map_comp {X Y Z} f g := by
    ext L
    induction L using Quotient.ind with
    | _ L =>
      refine congrArg (Quotient.mk ((Opposite.unop Z).curve.hOrbitSetoid H)) ?_
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact EllHom.pullSection_comp R g.unop f.unop L.1.1
      · exact EllHom.pullSection_comp R g.unop f.unop L.1.2

/-- **(T-H1)** `P_⊥` is the naive full-level problem: the `H = ⊥` orbits are
singletons, recovering `gammaFullNaiveProblem`. -/
theorem gammaHNaive_bot (N : ℕ) [NeZero N] :
    Nonempty ((gammaHNaiveProblem R N ⊥) ≅ gammaFullNaiveProblem R N) :=
  ⟨NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := Quotient.lift (fun L => L)
          fun L L' ⟨g, hg, hgl⟩ => by
            rw [Subgroup.mem_bot] at hg
            subst hg
            rwa [X.unop.curve.glSmul_one] at hgl
        invFun := Quotient.mk _
        left_inv := fun q => by
          induction q using Quotient.ind with
          | _ L => rfl
        right_inv := fun L => rfl })
    (fun {X Y} f => by
      ext q
      induction q using Quotient.ind with
      | _ L => exact Subtype.ext rfl)⟩

/-- **(T-H4 = Loeffler Prop 3.8.2, BOTH halves)** `P_H` is relatively representable
**and the representing objects are finite étale** over the base when `N` is invertible
(verbatim: "relatively representable and étale … finite étale") — the étale conjunct
was missing from the statement until 2026-07-06. (Proof route for `H = {1}`: the open
subscheme of `E[N] ×_S E[N]` cut by non-vanishing of Weil pairings — consumes
workstream C; for general `H`: the quotient by `H` — consumes stream Q. The two
conjuncts share one representing object; identifying them across the two ∃'s is part
of the ticket.) -/
theorem gammaHNaive_relativelyRepresentable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    (gammaHNaiveProblem R N H).RelativelyRepresentable ∧
      ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
          ({ h : T ⟶ Z // h ≫ f = g } ≃
            (gammaHNaiveProblem R N H).obj (Opposite.op (X.pullbackAlong g))) := by
  sorry

/-- **(T-H5 = Loeffler Prop 3.8.3, the rigidity criterion for arbitrary level)** Over
`R` with `6N` invertible: `P_H` is rigid iff the preimage of `H` in `SL₂(ℤ)` is
torsion-free ("contains no elements of finite order — i.e. has no elliptic points and
does not contain `−1`"). -/
theorem gammaHNaive_rigid_iff (N : ℕ) [NeZero N] [Nontrivial R]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit ((6 * N : ℕ) : R)) :
    (gammaHNaiveProblem R N H).Rigid ↔
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) ∈ H) →
        IsOfFinOrder γ → γ = 1 := by sorry

/-- **(T-H6, fine modular curves of arbitrary level)** For rigid `P_H` (and `N`
invertible), `P_H` is representable — "there is a scheme `Y = Y_{P_H}`, an elliptic
curve `ℰ/Y` and an `α ∈ P_H(ℰ/Y)` representing the functor" — and the base is smooth
and affine over `Spec R`. Every fine modular curve of every level arises here.
Source: Loeffler §3.8 (after 3.8.3); via `representable_iff` (T-E5) + T-H4. -/
theorem gammaHNaive_representable_of_rigid (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) (hrig : (gammaHNaiveProblem R N H).Rigid) :
    (gammaHNaiveProblem R N H).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaHNaiveProblem R N H).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry

/-! ### T-H7 helpers (T-H7a–T-H7d): the negation automorphism and its witnesses

Machinery for `gammaFullNaive_not_rigid_of_le_two`: multiplication morphisms compose
(`[m] ≫ [n] = [m·n]`, convolution powers of `𝟙` via `GrpObj.comp_zpow`); `[-1]`
packages as an `Ell/R`-automorphism over the identity base; section pullback along it
is negation; `[-1] ≠ 𝟙` on any curve with a geometric point (odd fibre torsion,
T-B6); and naive full level structures exist over an algebraically closed base for
`N ≤ 2`. Helper home: this file (H-lane owned); `/cleanup` may relocate the
`EllipticCurve`-level lemmas next to `mulBy` later. -/

/-- **(T-H7a)** Multiplication morphisms compose multiplicatively:
`[m] ≫ [n] = [m·n]` (both are convolution powers of the identity). -/
theorem EllipticCurve.mulBy_comp_mulBy (E : EllipticCurve S) (m n : ℤ) :
    E.mulBy m ≫ E.mulBy n = E.mulBy (m * n) := by
  letI : Group (E.asOver ⟶ E.asOver) := Hom.group
  show E.mulBy m ≫ (𝟙 E.asOver) ^ n = (𝟙 E.asOver) ^ (m * n)
  rw [GrpObj.comp_zpow, Category.comp_id]
  exact (zpow_mul (𝟙 E.asOver) m n).symm

-- **(T-H7a)** `mulBy_one` (`[1] = 𝟙 E.asOver`) moved to `EllipticCurve/EndomorphismDegree.lean`
-- (its natural low home, next to the other `mulBy`/degree algebra); available here by import.

/-- **(T-H7a)** Scheme-level composition law for the multiplication morphisms. -/
theorem EllipticCurve.mulByHom_comp_mulByHom (E : EllipticCurve S) (m n : ℤ) :
    E.mulByHom m ≫ E.mulByHom n = E.mulByHom (m * n) := by
  have h := congrArg CommaMorphism.left (E.mulBy_comp_mulBy m n)
  simp only [Over.comp_left] at h
  exact h

/-- **(T-H7a)** Scheme-level: `[1] = 𝟙`. -/
theorem EllipticCurve.mulByHom_one (E : EllipticCurve S) :
    E.mulByHom 1 = 𝟙 E.E := by
  have h := congrArg CommaMorphism.left E.mulBy_one
  simp only [Over.id_left] at h
  exact h

/-- **(T-H7a)** `[-1]` is a (self-inverse) involution. -/
theorem EllipticCurve.mulByHom_neg_one_involutive (E : EllipticCurve S) :
    E.mulByHom (-1) ≫ E.mulByHom (-1) = 𝟙 E.E := by
  rw [E.mulByHom_comp_mulByHom, show ((-1 : ℤ) * -1) = 1 by norm_num, E.mulByHom_one]

/-- **(T-H7a)** `[n]` is pointed: it carries the zero section to the zero section. -/
theorem EllipticCurve.zero_comp_mulByHom (E : EllipticCurve S) (n : ℤ) :
    E.zero ≫ E.mulByHom n = E.zero := by
  have h : ((n • (0 : E.Point (𝟙 S)) : E.Point (𝟙 S)) : S ⟶ E.E)
      = ((0 : E.Point (𝟙 S)) : S ⟶ E.E) :=
    congrArg _ (smul_zero n)
  rw [E.point_smul_eq_comp_mulBy, E.point_zero_val] at h
  simp only [Category.id_comp] at h
  exact h

/-- **(T-H7a)** Negation `[-1]` as an `Ell/R`-endomorphism over the identity of the
base: cartesian because `[-1]` is a self-inverse isomorphism. -/
noncomputable def EllObj.negHom (X : EllObj R) : X ⟶ X where
  baseHom := 𝟙 X.base
  base_w := Category.id_comp _
  top := X.curve.mulByHom (-1)
  isPullback := by
    haveI : IsIso (X.curve.mulByHom (-1)) :=
      ⟨⟨X.curve.mulByHom (-1), X.curve.mulByHom_neg_one_involutive,
        X.curve.mulByHom_neg_one_involutive⟩⟩
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  zero_w := by
    rw [X.curve.zero_comp_mulByHom]
    exact (Category.id_comp _).symm

/-- **(T-H7a)** `[-1]` is a self-inverse `Ell/R`-endomorphism. -/
theorem EllObj.negHom_comp_negHom (X : EllObj R) :
    EllObj.negHom R X ≫ EllObj.negHom R X = 𝟙 X := by
  apply EllHom.ext
  · show 𝟙 X.base ≫ 𝟙 X.base = 𝟙 X.base
    exact Category.id_comp _
  · show X.curve.mulByHom (-1) ≫ X.curve.mulByHom (-1) = 𝟙 X.curve.E
    exact X.curve.mulByHom_neg_one_involutive

/-- **(T-H7a)** `[-1]` as an automorphism of `X` in `Ell/R` (self-inverse). -/
noncomputable def EllObj.negIso (X : EllObj R) : X ≅ X where
  hom := EllObj.negHom R X
  inv := EllObj.negHom R X
  hom_inv_id := EllObj.negHom_comp_negHom R X
  inv_hom_id := EllObj.negHom_comp_negHom R X

/-- **(T-H7a, the fixity engine)** Pulling a section back along `[-1]` is negation. -/
theorem EllObj.pullSection_negHom (X : EllObj R) (P : X.curve.Section) :
    EllHom.pullSection R (EllObj.negHom R X) P = -P := by
  refine Subtype.ext ((EllObj.negHom R X).isPullback.hom_ext ?_ ?_)
  · have h1 : (EllHom.pullSection R (EllObj.negHom R X) P).1 ≫ (EllObj.negHom R X).top
        = (EllObj.negHom R X).baseHom ≫ P.1 :=
      (EllObj.negHom R X).isPullback.lift_fst _ _ _
    have h2 : ((-P : X.curve.Section) : X.base ⟶ X.curve.E)
        = (P : X.base ⟶ X.curve.E) ≫ X.curve.mulByHom (-1) :=
      (congrArg Subtype.val (neg_one_zsmul P)).symm.trans
        (X.curve.point_smul_eq_comp_mulBy (𝟙 X.base) (-1) P)
    rw [h1, h2]
    show 𝟙 X.base ≫ (P : X.base ⟶ X.curve.E)
        = ((P : X.base ⟶ X.curve.E) ≫ X.curve.mulByHom (-1)) ≫ X.curve.mulByHom (-1)
    rw [Category.id_comp, Category.assoc, X.curve.mulByHom_neg_one_involutive,
      Category.comp_id]
  · rw [(EllHom.pullSection R (EllObj.negHom R X) P).2, (-P).2]

/-- **(T-H7c)** Over a base with a geometric point, `[-1] ≠ 𝟙`: the geometric fibre
has a nonzero point of odd order `M ∈ {3,5}` (T-B6), while `[-1] = 𝟙` forces every
point to be `2`-torsion. -/
theorem EllipticCurve.mulByHom_neg_one_ne_id (E : EllipticCurve S) (k : Type u)
    [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) :
    E.mulByHom (-1) ≠ 𝟙 E.E := by
  intro hid
  -- If `[-1] = 𝟙`, every point over the geometric point is 2-torsion.
  have h2tor : ∀ x : E.Point t, (2 : ℤ) • x = 0 := by
    intro x
    have hsm := E.point_smul_eq_comp_mulBy t (-1) x
    rw [hid, Category.comp_id] at hsm
    have hneg : -x = x := by
      apply Subtype.ext
      calc ((-x : E.Point t) : Spec (CommRingCat.of k) ⟶ E.E)
          = (((-1 : ℤ) • x : E.Point t) : Spec (CommRingCat.of k) ⟶ E.E) := by
            rw [neg_one_zsmul]
        _ = (x : Spec (CommRingCat.of k) ⟶ E.E) := hsm
    rw [two_zsmul]
    nth_rewrite 2 [← hneg]
    exact add_neg_cancel x
  -- But for odd `M ≥ 3` invertible in `k`, `E[M](k) ≅ (ℤ/M)²` has a nonzero point,
  -- and a 2-torsion `M`-torsion point with `gcd(2,M) = 1` is zero.
  have key : ∀ M : ℕ, 3 ≤ M → Odd M → (M : k) ≠ 0 → False := by
    intro M hM3 hModd hMk
    haveI : NeZero M := ⟨by omega⟩
    obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two M k t hMk
    set xt := e.symm ![1, 0] with hxtdef
    have hx0 : xt ≠ 0 := by
      intro h0
      have h1 : (![1, 0] : Fin 2 → ZMod M) = 0 := by
        have h := congrArg e h0
        rwa [hxtdef, AddEquiv.apply_symm_apply, map_zero] at h
      have hone : (1 : ZMod M) = 0 := by simpa using congrFun h1 0
      haveI : Fact (1 < M) := ⟨by omega⟩
      exact one_ne_zero hone
    have hxM : (M : ℤ) • (xt : E.Point t) = 0 :=
      (Submodule.mem_torsionBy_iff _ _).mp xt.2
    have hcop : IsCoprime (2 : ℤ) (M : ℤ) := by
      have hnot2 : ¬ (2 ∣ M) := by
        rw [Nat.odd_iff] at hModd
        omega
      have hnat : Nat.Coprime 2 M := (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    apply hx0
    have hcoe : (xt : E.Point t) = 0 := by
      calc (xt : E.Point t)
          = (1 : ℤ) • (xt : E.Point t) := (one_zsmul _).symm
        _ = (u * 2 + v * (M : ℤ)) • (xt : E.Point t) := by rw [huv]
        _ = u • ((2 : ℤ) • (xt : E.Point t)) + v • ((M : ℤ) • (xt : E.Point t)) := by
            rw [add_zsmul, mul_zsmul, mul_zsmul]
        _ = 0 := by rw [h2tor, hxM, smul_zero, smul_zero, add_zero]
    exact_mod_cast hcoe
  -- Choose `M ∈ {3, 5}` by the residue characteristic.
  by_cases h3 : (3 : k) = 0
  · refine key 5 (by norm_num) ⟨2, by norm_num⟩ ?_
    intro h5
    haveI : CharP k (ringChar k) := ringChar.charP k
    have hd3 : ringChar k ∣ 3 :=
      (CharP.cast_eq_zero_iff k (ringChar k) 3).mp (by exact_mod_cast h3)
    have hd5 : ringChar k ∣ 5 :=
      (CharP.cast_eq_zero_iff k (ringChar k) 5).mp (by exact_mod_cast h5)
    have hd2 : ringChar k ∣ 2 := by
      have h := Nat.dvd_sub hd5 hd3
      norm_num at h
      exact h
    have h := Nat.dvd_sub hd3 hd2
    norm_num at h
    exact not_subsingleton k h
  · exact key 3 le_rfl ⟨1, by norm_num⟩ h3

/-- **(T-H7b-i)** Sections of an elliptic curve over `Spec k̄` are separated by their
value at the closed point (`AlgebraicGeometry.ext_of_apply_closedPoint_eq`: `E` is
locally of finite type over the algebraically closed base since it is proper). -/
theorem EllipticCurve.section_ext (k : Type u) [Field k] [IsAlgClosed k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) {P Q : E.Section}
    (h : P.1 (IsLocalRing.closedPoint k) = Q.1 (IsLocalRing.closedPoint k)) : P = Q :=
  Subtype.ext (ext_of_apply_closedPoint_eq E.π P.2 Q.2 h)

set_option backward.isDefEq.respectTransparency false in
/-- **(T-H7b-i)** Pulling sections back along any morphism of field-Specs is
injective: the base spaces are single points, so the closed-point values are
preserved, and `section_ext` separates. -/
theorem EllipticCurve.pull_injective (k k' : Type u) [Field k] [IsAlgClosed k]
    [Field k'] (E : EllipticCurve (Spec (CommRingCat.of k)))
    (t : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    Function.Injective (EllipticCurve.Point.pull E t) := by
  intro P Q hPQ
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have h1 : t ≫ P.1 = t ≫ Q.1 := congrArg Subtype.val hPQ
  have h2 := congrArg
    (fun f : Spec (CommRingCat.of k') ⟶ E.E => f (IsLocalRing.closedPoint k')) h1
  have h4 : ∀ Z : E.Section,
      (t ≫ Z.1) (IsLocalRing.closedPoint k') = Z.1 (IsLocalRing.closedPoint k) := by
    intro Z
    rw [Scheme.Hom.comp_apply]
    exact congrArg (fun z => Z.1 z) (Subsingleton.elim _ _)
  rw [h4 P, h4 Q] at h2
  exact E.section_ext k h2

set_option backward.isDefEq.respectTransparency false in
/-- **(T-H7b-i)** `Spec` of a field embedding is an epimorphism onto morphisms into any
scheme: two morphisms from `Spec k` agree as soon as they agree after the extension
`Spec k' ⟶ Spec k`. The point components agree since the source spaces are single
points; the residue components agree after composing with the injective `f`, via the
canonical `stalkClosedPointTo` factorization and the mono `fromSpecResidueField`. -/
theorem _root_.AlgebraicGeometry.Scheme.hom_ext_of_comp_specMap_field
    {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') {Y : Scheme.{u}} (u v : Spec (CommRingCat.of k) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ u = Spec.map (CommRingCat.ofHom f) ≫ v) :
    u = v := by
  have hpt : u (IsLocalRing.closedPoint k) = v (IsLocalRing.closedPoint k) := by
    have h0 := congrArg
      (fun m : Spec (CommRingCat.of k') ⟶ Y => m (IsLocalRing.closedPoint k')) h
    simp only [Scheme.Hom.comp_apply] at h0
    have huniq : (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint k')
        = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rwa [huniq] at h0
  have hu := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y u
  have hv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y v
  -- transport `v`'s factorization to the common point via the congr iso
  have hv' : Spec.map ((Y.residueFieldCongr hpt).hom
        ≫ Y.descResidueField (Scheme.stalkClosedPointTo v))
      ≫ Y.fromSpecResidueField (u (IsLocalRing.closedPoint k)) = v := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact hv
  rw [← hu, ← hv']
  have hcomp : Spec.map (CommRingCat.ofHom f)
        ≫ (Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo u))
          ≫ Y.fromSpecResidueField (u (IsLocalRing.closedPoint k)))
      = Spec.map (CommRingCat.ofHom f)
        ≫ (Spec.map ((Y.residueFieldCongr hpt).hom
            ≫ Y.descResidueField (Scheme.stalkClosedPointTo v))
          ≫ Y.fromSpecResidueField (u (IsLocalRing.closedPoint k))) := by
    rw [hu, hv']
    exact h
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp] at hcomp
  have h2 := (cancel_mono (Y.fromSpecResidueField (u (IsLocalRing.closedPoint k)))).mp hcomp
  have h3 := Spec.map_injective h2
  haveI : Mono (CommRingCat.ofHom f) :=
    ConcreteCategory.mono_of_injective _ f.injective
  have h4 := (cancel_mono (CommRingCat.ofHom f)).mp h3
  rw [h4]

/-- **(T-H7b-i)** Point separation along extensions of the base field: restricting
`k`-points of `E/S` along `Spec k' ⟶ Spec k` is injective, for ANY field embedding
`f : k →+* k'` (no algebraic closure needed, any base `S`). -/
theorem EllipticCurve.Point.restrict_injective {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') (E : EllipticCurve S) (t : Spec (CommRingCat.of k) ⟶ S) :
    Function.Injective
      (fun x : E.Point t =>
        EllipticCurve.Point.restrict E (Spec.map (CommRingCat.ofHom f)) x) := by
  intro x y hxy
  have h1 : Spec.map (CommRingCat.ofHom f) ≫ x.1 = Spec.map (CommRingCat.ofHom f) ≫ y.1 :=
    congrArg Subtype.val hxy
  exact Subtype.ext (Scheme.hom_ext_of_comp_specMap_field f x.1 y.1 h1)

/-- **(T-H7b)** Naive full level-`N` structures exist over an algebraically closed
base when `N ≤ 2` and `N` is invertible: for `N = 1` the zero pair works (the killing
clause forces it); for `N = 2` a basis of `E[2]` from the geometric-fibre structure
(T-B6) does. -/
theorem EllipticCurve.exists_isNaiveFullLevel_of_le_two (k : Type u) [Field k]
    [IsAlgClosed k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ)
    [NeZero N] (hN : N ≤ 2) (hk : (N : k) ≠ 0) :
    ∃ P Q : E.Section, E.IsNaiveFullLevel N P Q := by
  have hcases : N = 1 ∨ N = 2 := by
    have := NeZero.ne N
    omega
  rcases hcases with rfl | rfl
  · -- N = 1: the zero pair; killing forces everything, generation is vacuous.
    refine ⟨0, 0, ⟨⟨by simp, by simp⟩, ?_⟩⟩
    intro k' _ _ _t x hx
    have hx0 : x = 0 := by simpa using hx
    rw [hx0]
    exact zero_mem _
  · -- N = 2: a basis of `E[2](k)` from the T-B6 geometric-fibre structure.
    obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two 2 k (𝟙 _) hk
    refine ⟨(e.symm ![1, 0]).1, (e.symm ![0, 1]).1,
      ⟨⟨(Submodule.mem_torsionBy_iff _ _).mp (e.symm ![1, 0]).2,
        (Submodule.mem_torsionBy_iff _ _).mp (e.symm ![0, 1]).2⟩, ?_⟩⟩
    intro k' _ _ t x hx
    -- Transport `IsUnit 2` along `t` for the fibre count over `k'`.
    have hk2' : ((2 : ℕ) : k') ≠ 0 := by
      have h2u : IsUnit ((2 : ℕ) : k) := isUnit_iff_ne_zero.mpr hk
      have hm := h2u.map (Spec.preimage t).hom
      rw [map_natCast] at hm
      exact hm.ne_zero
    obtain ⟨e'⟩ := E.torsion_geometricFibre_rank_two 2 k' t hk2'
    -- The two pulled basis sections and `x`, as 2-torsion elements over `k'`.
    have hmem : ∀ Z : E.Section, ((2 : ℕ) : ℤ) • Z = 0 →
        ((2 : ℕ) : ℤ) • EllipticCurve.Point.pull E t Z = 0 := by
      intro Z hZ
      rw [← EllipticCurve.Point.pull_zsmul, hZ, EllipticCurve.Point.pull_zero]
    set p : Submodule.torsionBy ℤ (E.Point t) ((2 : ℕ) : ℤ) :=
      ⟨EllipticCurve.Point.pull E t (e.symm ![1, 0]).1,
        (Submodule.mem_torsionBy_iff _ _).mpr
          (hmem _ ((Submodule.mem_torsionBy_iff _ _).mp (e.symm ![1, 0]).2))⟩ with hpdef
    set q : Submodule.torsionBy ℤ (E.Point t) ((2 : ℕ) : ℤ) :=
      ⟨EllipticCurve.Point.pull E t (e.symm ![0, 1]).1,
        (Submodule.mem_torsionBy_iff _ _).mpr
          (hmem _ ((Submodule.mem_torsionBy_iff _ _).mp (e.symm ![0, 1]).2))⟩ with hqdef
    set x' : Submodule.torsionBy ℤ (E.Point t) ((2 : ℕ) : ℤ) :=
      ⟨x, (Submodule.mem_torsionBy_iff _ _).mpr hx⟩ with hxdef
    -- Nonvanishing and distinctness, via `pull_injective` + the `e`-coordinates.
    haveI : Fact (1 < 2) := ⟨one_lt_two⟩
    have hbase : ∀ v : Fin 2 → ZMod 2, (e.symm v).1 = 0 → v = 0 := by
      intro v hv
      have h0 : e.symm v = 0 := by
        apply Subtype.ext
        simpa using hv
      have := congrArg e h0
      rwa [AddEquiv.apply_symm_apply, map_zero] at this
    have hp0 : p ≠ 0 := by
      intro h0
      have hval : EllipticCurve.Point.pull E t (e.symm ![1, 0]).1 =
          (0 : E.Point t) := congrArg Subtype.val h0
      have h00 : (e.symm ![1, 0]).1 = (0 : E.Section) :=
        E.pull_injective k k' t (by rw [hval, EllipticCurve.Point.pull_zero])
      have hv := hbase ![1, 0] h00
      have h1 : (1 : ZMod 2) = 0 := by simpa using congrFun hv 0
      exact one_ne_zero h1
    have hq0 : q ≠ 0 := by
      intro h0
      have hval : EllipticCurve.Point.pull E t (e.symm ![0, 1]).1 =
          (0 : E.Point t) := congrArg Subtype.val h0
      have h00 : (e.symm ![0, 1]).1 = (0 : E.Section) :=
        E.pull_injective k k' t (by rw [hval, EllipticCurve.Point.pull_zero])
      have hv := hbase ![0, 1] h00
      have h1 : (1 : ZMod 2) = 0 := by simpa using congrFun hv 1
      exact one_ne_zero h1
    have hpq : p ≠ q := by
      intro h0
      have hval : EllipticCurve.Point.pull E t (e.symm ![1, 0]).1 =
          EllipticCurve.Point.pull E t (e.symm ![0, 1]).1 :=
        congrArg Subtype.val h0
      have h00 := E.pull_injective k k' t hval
      have hsymm : e.symm ![1, 0] = e.symm ![0, 1] := Subtype.ext h00
      have hv : (![1, 0] : Fin 2 → ZMod 2) = ![0, 1] := by
        have := congrArg e hsymm
        rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at this
      have h1 : (1 : ZMod 2) = 0 := by simpa using congrFun hv 0
      exact one_ne_zero h1
    -- Klein-four exhaustion, in pair coordinates (where `decide` computes).
    let π2 : (Fin 2 → ZMod 2) ≃+ ZMod 2 × ZMod 2 :=
      { toFun := fun v => (v 0, v 1)
        invFun := fun z => ![z.1, z.2]
        left_inv := fun v => by
          funext i
          fin_cases i <;> rfl
        right_inv := fun z => rfl
        map_add' := fun _ _ => rfl }
    let e'' := e'.trans π2
    have hd : ∀ v w u : ZMod 2 × ZMod 2, w ≠ 0 → u ≠ 0 → w ≠ u →
        v = 0 ∨ v = w ∨ v = u ∨ v = w + u := by decide
    have hew : e'' p ≠ 0 := fun h0 => hp0 (e''.injective (by rw [h0, map_zero]))
    have heu : e'' q ≠ 0 := fun h0 => hq0 (e''.injective (by rw [h0, map_zero]))
    have hwu : e'' p ≠ e'' q := fun h0 => hpq (e''.injective h0)
    have hfour := hd (e'' x') (e'' p) (e'' q) hew heu hwu
    have hcases4 : x' = 0 ∨ x' = p ∨ x' = q ∨ x' = p + q := by
      rcases hfour with h | h | h | h
      · exact Or.inl (e''.injective (by rw [h, map_zero]))
      · exact Or.inr (Or.inl (e''.injective h))
      · exact Or.inr (Or.inr (Or.inl (e''.injective h)))
      · exact Or.inr (Or.inr (Or.inr (e''.injective (by rw [h, map_add]))))
    -- Land in the closure.
    rcases hcases4 with h | h | h | h
    · have hx0 : x = (0 : E.Point t) := congrArg Subtype.val h
      rw [hx0]
      exact zero_mem _
    · have hxp : x = EllipticCurve.Point.pull E t (e.symm ![1, 0]).1 :=
        congrArg Subtype.val h
      rw [hxp]
      exact AddSubgroup.subset_closure (Set.mem_insert _ _)
    · have hxq : x = EllipticCurve.Point.pull E t (e.symm ![0, 1]).1 :=
        congrArg Subtype.val h
      rw [hxq]
      exact AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · have hxpq : x = EllipticCurve.Point.pull E t (e.symm ![1, 0]).1 +
          EllipticCurve.Point.pull E t (e.symm ![0, 1]).1 :=
        congrArg Subtype.val h
      rw [hxpq]
      exact add_mem (AddSubgroup.subset_closure (Set.mem_insert _ _))
        (AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

/-- **(T-H7d)** A nonempty `R`-scheme base has a geometric point in which every
`R`-invertible `N` stays invertible: take the algebraic closure of a residue field. -/
theorem EllObj.exists_geometricPoint (X : EllObj R) (hne : Nonempty X.base)
    (N : ℕ) (hinv : IsUnit ((N : ℕ) : R)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (_t : Spec (CommRingCat.of k) ⟶ X.base), (N : k) ≠ 0 := by
  obtain ⟨s⟩ := hne
  refine ⟨AlgebraicClosure (X.base.residueField s), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField s)
      (AlgebraicClosure (X.base.residueField s)))) ≫ X.base.fromSpecResidueField s, ?_⟩
  have hu : IsUnit ((N : ℕ) : AlgebraicClosure (X.base.residueField s)) := by
    have φ := Spec.preimage
      ((Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField s)
          (AlgebraicClosure (X.base.residueField s)))) ≫
        X.base.fromSpecResidueField s) ≫ X.structMap)
    have h := hinv.map φ.hom
    rwa [map_natCast] at h
  exact hu.ne_zero

/-- **(T-G3a-SUB1)** The point-anchored refinement of `EllObj.exists_geometricPoint`:
at any prescribed point `s` of the base there is a geometric point lying over `s`
(with `N` still invertible in the residue-closure). The witness is the same one the
unanchored version builds; only the anchoring conclusion is new. -/
theorem EllObj.exists_geometricPoint_at (X : EllObj R) (s : X.base)
    (N : ℕ) (hinv : IsUnit ((N : ℕ) : R)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (t : Spec (CommRingCat.of k) ⟶ X.base),
      (N : k) ≠ 0 ∧ Set.range t.base = {s} := by
  refine ⟨AlgebraicClosure (X.base.residueField s), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField s)
      (AlgebraicClosure (X.base.residueField s)))) ≫ X.base.fromSpecResidueField s,
    ?_, ?_⟩
  · have hu : IsUnit ((N : ℕ) : AlgebraicClosure (X.base.residueField s)) := by
      have φ := Spec.preimage
        ((Spec.map (CommRingCat.ofHom (algebraMap (X.base.residueField s)
            (AlgebraicClosure (X.base.residueField s)))) ≫
          X.base.fromSpecResidueField s) ≫ X.structMap)
      have h := hinv.map φ.hom
      rwa [map_natCast] at h
    exact hu.ne_zero
  · apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨Nonempty.some inferInstance, ?_⟩, ?_⟩
    · show (X.base.fromSpecResidueField s).base _ = s
      simp
    · rintro y ⟨z, rfl⟩
      show (X.base.fromSpecResidueField s).base _ = s
      simp

private theorem neg_eq_self_of_zsmul_eq_zero_of_le_two {G : Type*} [AddGroup G] {N : ℕ} [NeZero N]
    (hN : N ≤ 2) {Z : G} (hZ : (N : ℤ) • Z = 0) : -Z = Z := by
  rw [neg_eq_iff_add_eq_zero, ← two_zsmul]
  rcases (by have := NeZero.ne N; lia : N = 1 ∨ N = 2) with rfl | rfl
  · simp [show Z = 0 by simpa using hZ]
  · exact_mod_cast hZ

private theorem gammaFullNaiveProblem_map_negIso_of_le_two (N : ℕ) [NeZero N] (hN : N ≤ 2)
    (X : EllObj R) (L : (gammaFullNaiveProblem R N).obj (Opposite.op X)) :
    (gammaFullNaiveProblem R N).map (EllObj.negIso R X).hom.op L = L := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact (EllObj.pullSection_negHom R X L.1.1).trans
      (neg_eq_self_of_zsmul_eq_zero_of_le_two hN L.2.1.1)
  · exact (EllObj.pullSection_negHom R X L.1.2).trans
      (neg_eq_self_of_zsmul_eq_zero_of_le_two hN L.2.1.2)

/-- **(T-H7, the honest stack statement at small `N`)** For `N ≤ 2` the full-level
problem is NOT rigid — `[-1]` is a nontrivial automorphism acting trivially on all
level data (on `E[2]`, `−P = P`) — so no fine scheme exists and the object of record
is the levelled groupoid (design D6). This is the precise sense in which "for full
level `N ≤ 2` we only get a stack".

Hypotheses per the adversarial pass (2026-07-05, DEF-1): `N` invertible (over an
`𝔽₂`-algebra naive full level-2 structures do not exist — `E[2]` is infinitesimal —
so the problem is vacuously rigid), and an object with nonempty base (empty-base
objects witness nothing). Proof route: base-change any `X` to a geometric point of
its base keeping `N` invertible (T-H7d), where a naive full level structure exists
(T-H7b) and is fixed by the non-identity automorphism `[-1]` (T-H7a/T-H7c). -/
theorem gammaFullNaive_not_rigid_of_le_two (N : ℕ) [NeZero N] (hN : N ≤ 2)
    (hinv : IsUnit ((N : ℕ) : R)) (hR : ∃ X : EllObj R, Nonempty X.base) :
    ¬ (gammaFullNaiveProblem R N).Rigid := by
  intro hrig
  obtain ⟨X₀, hne⟩ := hR
  obtain ⟨k, fk, ak, t, hk⟩ := EllObj.exists_geometricPoint R X₀ hne N hinv
  letI := fk
  letI := ak
  set X : EllObj R := X₀.pullbackAlong t
  obtain ⟨P, Q, hPQ⟩ := EllipticCurve.exists_isNaiveFullLevel_of_le_two k X.curve N hN hk
  have hne' : EllObj.negIso R X ≠ Iso.refl X := fun h ↦
    EllipticCurve.mulByHom_neg_one_ne_id X.curve k (𝟙 _) (congrArg (fun i : X ≅ X ↦ i.hom.top) h)
  exact hrig X (EllObj.negIso R X) rfl hne' ⟨(P, Q), hPQ⟩
    (gammaFullNaiveProblem_map_negIso_of_le_two R N hN X ⟨(P, Q), hPQ⟩)

/-- **(T-H7-positive, `N ≥ 3`)** The `[-1]` automorphism acts WITHOUT fixed points on the
naive full-level-`N` problem for `N ≥ 3` (invertible): over any object with a nonempty base,
`[-1]` moves every naive full level structure. The exact positive counterpart to
`gammaFullNaiveProblem_map_negIso_of_le_two` (for `N ≤ 2`, `[-1]` FIXES every structure): if it
fixed `(P, Q)` then `−P = P` and `−Q = Q`, so at a geometric point `pull P, pull Q` are
`2`-torsion and the subgroup they generate is entirely `2`-torsion — yet by the full-level
condition it contains all of `E[N] ≅ (ℤ/N)²`, forcing `2 = 0` in `ℤ/N`, i.e. `N ≤ 2`.

This is the `[-1]`-part of KM/Loeffler rigidity for `N ≥ 3` — the generic-automorphism case
(`Aut(E) = {±1}`, all `j ∉ {0, 1728}`). Full `Rigid` (every automorphism, including the extra
ones at `j ∈ {0, 1728}`) needs the automorphism group scheme and is the ⧗KM-gated
`gammaFullDrinfeld_representable`. -/
theorem gammaFullNaiveProblem_map_negIso_ne_of_three_le (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit ((N : ℕ) : R)) (X : EllObj R) (hne : Nonempty X.base)
    (L : (gammaFullNaiveProblem R N).obj (Opposite.op X)) :
    (gammaFullNaiveProblem R N).map (EllObj.negIso R X).hom.op L ≠ L := by
  intro heq
  -- A fixed point forces `−P = P` and `−Q = Q`.
  have hP : -L.1.1 = L.1.1 :=
    (EllObj.pullSection_negHom R X L.1.1).symm.trans (congrArg (fun z => z.1.1) heq)
  have hQ : -L.1.2 = L.1.2 :=
    (EllObj.pullSection_negHom R X L.1.2).symm.trans (congrArg (fun z => z.1.2) heq)
  -- Base change to a geometric point where `N` is invertible.
  obtain ⟨k, fk, ak, t, hk⟩ := EllObj.exists_geometricPoint R X hne N hinv
  letI := fk; letI := ak
  -- There, the pulled sections are `2`-torsion.
  have h2 : ∀ Z : X.curve.Section, -Z = Z →
      (2 : ℤ) • EllipticCurve.Point.pull X.curve t Z = 0 := by
    intro Z hZ
    have hneg : -(EllipticCurve.Point.pull X.curve t Z) =
        EllipticCurve.Point.pull X.curve t Z := by
      rw [← neg_one_zsmul, ← EllipticCurve.Point.pull_zsmul, neg_one_zsmul, hZ]
    rw [two_zsmul]; nth_rewrite 2 [← hneg]; exact add_neg_cancel _
  -- Hence the whole subgroup they generate is `2`-torsion.
  let dbl : X.curve.Point t →+ X.curve.Point t :=
    AddMonoidHom.mk' (fun x => (2 : ℤ) • x) (fun a b => smul_add 2 a b)
  have hsub : AddSubgroup.closure {EllipticCurve.Point.pull X.curve t L.1.1,
      EllipticCurve.Point.pull X.curve t L.1.2} ≤ dbl.ker := by
    rw [AddSubgroup.closure_le]
    rintro y (rfl | rfl)
    · exact h2 _ hP
    · exact h2 _ hQ
  -- But `E[N] ≅ (ℤ/N)²` supplies an `N`-torsion point; the full-level condition puts it in
  -- that subgroup, so it is `2`-torsion — impossible for `N ≥ 3`.
  obtain ⟨e⟩ := X.curve.torsion_geometricFibre_rank_two N k t hk
  have hxtN : (N : ℤ) • ((e.symm ![1, 0] :
      Submodule.torsionBy ℤ (X.curve.Point t) (N : ℤ)) : X.curve.Point t) = 0 :=
    (Submodule.mem_torsionBy_iff _ _).mp (e.symm ![1, 0]).2
  have hxt2 : (2 : ℤ) • ((e.symm ![1, 0] :
      Submodule.torsionBy ℤ (X.curve.Point t) (N : ℤ)) : X.curve.Point t) = 0 :=
    AddMonoidHom.mem_ker.mp (hsub (L.2.2 k t _ hxtN))
  have hy2 : (2 : ℤ) • (e.symm ![1, 0] :
      Submodule.torsionBy ℤ (X.curve.Point t) (N : ℤ)) = 0 := by
    rw [← Submodule.coe_eq_zero, Submodule.coe_smul]
    exact hxt2
  have h20 : (2 : ℤ) • (![1, 0] : Fin 2 → ZMod N) = 0 := by
    have h := congrArg e hy2
    rwa [map_zsmul, AddEquiv.apply_symm_apply, map_zero] at h
  have h2z : ((2 : ℤ) : ZMod N) = 0 := by
    have h := congrFun h20 0
    rwa [Pi.smul_apply, Matrix.cons_val_zero, zsmul_eq_mul, mul_one, Pi.zero_apply] at h
  have hdvd : (N : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 N).mp h2z
  have hle : N ≤ 2 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
  omega

end GammaH

section DrinfeldOverZ

variable (R : CommRingCat.{u})

/-- **Full level N over an arbitrary base — the Drinfeld form.** The moduli problem
`E/S ↦ {Drinfeld full level-N structures}` (KM 3.1: pairs with `Σ [aP+bQ] = E[N]` as
divisors), with NO invertibility hypothesis on `N`. Over `ℤ[1/N]`-schemes it agrees
with the naive problem (T-D8); at primes dividing `N` it is the correct object.
Functor laws `T-H8a`. Source: KM 3.1 ⧗ (statement via [Loe]/KM-Ch.1 machinery, which
is fully sourced). -/
noncomputable def gammaFullDrinfeldProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, EllHom.isFullLevel_pullSection R f.unop PQ.2⟩
  map_id X := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.2)
  map_comp f g := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.2)

/-- The Drinfeld `Γ₁(N)` problem over an arbitrary base: points of exact order `N`
(KM 3.2 via KM 1.4.1 — fully sourced Ch. 1 machinery). -/
noncomputable def gammaOneDrinfeldProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1,
    EllHom.hasExactOrder_pullSection R f.unop P.2⟩
  map_id X := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_id R P.1)
  map_comp f g := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop P.1)

/-- **(T-H8 = GME Thm 2.6.8 scope; over-ℤ refinements = KM 4.7.2/5.1, ⧗KM)** For
`N ≥ 3` with `N` **invertible**, the Drinfeld full-level problem is rigid and
representable.

ADVERSARIAL FIX (2026-07-06): the previous arbitrary-ring form was FALSE — in char
`p ∣ N` with `N = p^k` (e.g. `N = 3`, supersingular `E/F̄₃`), the pair `(0, 0)` IS a
Drinfeld Γ(N)-structure (`Σ_{a,b} [a·0 + b·0] = N²[0] = E[N]` as divisors, and
`Norm(f) = f(0)^{N²} = ∏ f(0)` on the local ring `k[t]/(t^{N²})` — independently
verified), and `[-1] ≠ 𝟙` fixes it, so the problem is not rigid, hence (Yoneda +
cartesian-square rigidity) not representable. The over-ℤ statement has genuine fine
print — GME's in-hand over-ℤ Aut-triviality needs coprime `m, n ≥ 3` dividing `N`
(decomposition-gme2 B9/Y.6) — and is ⧗KM: cut it verbatim from the full text, never
from memory. (KM refinements for phase 2: `Y(N)` affine, flat finite over the
`j`-line, regular.) -/
theorem gammaFullDrinfeld_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaFullDrinfeldProblem R N).Rigid ∧
      (gammaFullDrinfeldProblem R N).Representable := by sorry

/-- **(T-H9, `Γ₁` analogue — over-ℤ refinement is KM 5.x, ⧗KM)** For `N ≥ 4` with `N`
**invertible**, the Drinfeld `Γ₁(N)` problem is rigid and representable.

ADVERSARIAL FIX (2026-07-06): over an arbitrary ring this was FALSE, refuted by a
source already in hand — KM Caution 1.4.3: over `F̄_p` the zero section has exact
order `pⁿ` for every `n` (it generates `Ker Fⁿ`), so for `N = p^k ≥ 4` in char `p`
the zero section is a Drinfeld Γ₁(N)-structure fixed by `[-1] ≠ 𝟙`: not rigid, not
representable. "`Y₁(N)` over `ℤ`" awaits the verbatim KM statement. -/
theorem gammaOneDrinfeld_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneDrinfeldProblem R N).Rigid ∧
      (gammaOneDrinfeldProblem R N).Representable := by sorry

end DrinfeldOverZ

namespace EllipticCurve

/-- The **levelled category**: elliptic curves over `S` with (naive) full level-`N`
structure; morphisms are pointed `S`-morphisms carrying one level structure to the
other. Its **core** is the levelled groupoid — the value at `S` of the moduli
**stack** of full level-`N` structures; as with `HomOver`, non-invertible levelled
endomorphisms exist (`[1+N]`), so the category itself is not a groupoid (adversarial
pass 2026-07-06). For `N ≥ 3` (invertible) the *automorphisms* are trivial
(`aut_trivial_of_fullLevel`); for `N ≤ 2` the levelled groupoid is the object of
record (`gammaFullNaive_not_rigid_of_le_two`). -/
@[ext]
structure LevelledHom {N : ℕ} [NeZero N]
    (X Y : Σ E : EllipticCurve S, E.FullLevelPt N) where
  hom : X.1 ⟶ Y.1
  level_w₁ : X.2.1.1.1 ≫ hom.hom = Y.2.1.1.1
  level_w₂ : X.2.1.2.1 ≫ hom.hom = Y.2.1.2.1

noncomputable instance levelledCategory (N : ℕ) [NeZero N] :
    Category (Σ E : EllipticCurve S, E.FullLevelPt N) where
  Hom := LevelledHom
  id X := ⟨𝟙 X.1, Category.comp_id _, Category.comp_id _⟩
  comp f g := ⟨f.hom ≫ g.hom,
    by rw [show (f.hom ≫ g.hom).hom = f.hom.hom ≫ g.hom.hom from rfl,
      ← Category.assoc, f.level_w₁, g.level_w₁],
    by rw [show (f.hom ≫ g.hom).hom = f.hom.hom ≫ g.hom.hom from rfl,
      ← Category.assoc, f.level_w₂, g.level_w₂]⟩
  id_comp := by intros; ext; simp
  comp_id := by intros; ext; simp
  assoc := by intros; ext; simp

end EllipticCurve

end ModularCurves
