/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.FieldTheory.Finiteness

/-!
# Pair generation in a `p²`-torsion group ([T-E15-NORM]/AX2-e leaf)

In an abelian group of cardinality `p²` killed by a prime `p`, a pair `(P, Q)` generates
iff **every** nontrivial combination `a•P + b•Q` (`(a,b) ∈ (ℤ/p)² ∖ 0`) is nonzero.

This is the fibrewise heart of the **combination-clopen** route to the two engine
axioms 2 (`naiveLevelThree_relativelyRepresentable_finiteEtale` and its Legendre twin):
it replaces the Weil-pairing non-vanishing cut of the Isom-scheme
`Isom((ℤ/p)², E[p])` by `p²−1` avoid-the-zero-section clopen conditions — for `p = 3`
the 8 combinations, for `p = 2` the classical `P ≠ 0, Q ≠ 0, P+Q ≠ 0`. Applied at a
geometric fibre with `G = E[p](k̄)` (`#G = p²` from BB-DEG rank + étaleness).

`zmodModule_closure_pair_eq_top_iff` is the core (stated for a registered
`Module (ℤ/p)`-structure — NB a `letI`-provided instance with *variable* `p` jams the
`Top (Submodule (ZMod p) G)` synthesis, hence the binder form); the public
`addSubgroup_closure_pair_eq_top_iff` takes the torsion hypothesis and speaks
`ℕ`-multiples only.
-/

open Module

namespace ModularCurves

variable {p : ℕ} [Fact p.Prime] {G : Type*} [AddCommGroup G]

set_option maxHeartbeats 800000 in
/-- **(AX2-e core)** In a `(ℤ/p)`-vector space of cardinality `p²`, a pair spans (as an
additive subgroup) iff all `p²−1` nontrivial `(ℤ/p)`-combinations avoid zero. -/
theorem zmodModule_closure_pair_eq_top_iff [Module (ZMod p) G]
    (hcard : Nat.card G = p ^ 2) (P Q : G) :
    AddSubgroup.closure {P, Q} = ⊤ ↔
      ∀ a b : ZMod p, ¬(a = 0 ∧ b = 0) → a • P + b • Q ≠ 0 := by
  haveI hfin : Finite G := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    have := (Fact.out : p.Prime).pos
    positivity)
  haveI : Fintype G := Fintype.ofFinite G
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- subgroup closure = linear span
  have hspan : AddSubgroup.closure {P, Q} = ⊤ ↔
      Submodule.span (ZMod p) ({P, Q} : Set G) = ⊤ := by
    constructor
    · intro h
      rw [Submodule.eq_top_iff']
      intro x
      have hx : x ∈ AddSubgroup.closure {P, Q} := h ▸ AddSubgroup.mem_top x
      exact (AddSubgroup.closure_le
        ((Submodule.span (ZMod p) ({P, Q} : Set G)).toAddSubgroup)).mpr
        Submodule.subset_span hx
    · intro h
      rw [AddSubgroup.eq_top_iff']
      intro x
      have hx : x ∈ Submodule.span (ZMod p) ({P, Q} : Set G) :=
        Submodule.eq_top_iff'.mp h x
      have hle : Submodule.span (ZMod p) ({P, Q} : Set G) ≤
          AddSubgroup.toZModSubmodule p (AddSubgroup.closure {P, Q}) :=
        Submodule.span_le.mpr (fun y hy => AddSubgroup.subset_closure hy)
      exact hle hx
  -- finrank = 2
  have hrank : finrank (ZMod p) G = 2 := by
    have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := G)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at hc
    exact ((Nat.pow_right_injective hp1) hc).symm
  -- the pair as a `Fin 2`-family
  set v : Fin 2 → G := ![P, Q] with hv
  have hrange : (Set.range v : Set G) = {P, Q} := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (by simp [hv])
      · exact Or.inr (by simp [hv])
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [hv]⟩
      · exact ⟨1, by simp [hv]⟩
  -- independence ↔ the combination form
  have hindep : LinearIndependent (ZMod p) v ↔
      ∀ a b : ZMod p, ¬(a = 0 ∧ b = 0) → a • P + b • Q ≠ 0 := by
    rw [Fintype.linearIndependent_iff]
    constructor
    · intro h a b hab hc
      refine hab ⟨h ![a, b] ?_ 0, h ![a, b] ?_ 1⟩ <;>
        · rw [show ∑ i : Fin 2, ![a, b] i • v i = a • P + b • Q by
            simp [hv, Fin.sum_univ_two]]
          exact hc
    · intro h g hg
      by_contra hne
      push_neg at hne
      obtain ⟨i, hi⟩ := hne
      refine h (g 0) (g 1) ?_ ?_
      · rintro ⟨h0, h1⟩
        fin_cases i
        · exact hi h0
        · exact hi h1
      · rw [show (g 0) • P + (g 1) • Q = ∑ i : Fin 2, g i • v i by
          simp [hv, Fin.sum_univ_two]]
        exact hg
  rw [hspan, ← hrange, ← hindep]
  constructor
  · -- spanning ⟹ independent (2 vectors in dimension 2)
    intro htop
    exact linearIndependent_of_top_le_span_of_card_eq_finrank htop.symm.le
      (by rw [Fintype.card_fin, hrank])
  · -- independent ⟹ spanning
    intro hind
    have hcard2 : Fintype.card (Fin 2) = finrank (ZMod p) G := by
      rw [Fintype.card_fin, hrank]
    have hspan_eq := (basisOfLinearIndependentOfCardEqFinrank hind hcard2).span_eq
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank hind hcard2] at hspan_eq

/-- **(AX2-e ★, the `ℕ`-multiples form)** In an abelian group of cardinality `p²`
killed by the prime `p`, a pair generates iff every combination `a•P + b•Q` with
`(a, b)` not both divisible by `p` avoids zero. `ZMod`-free interface for the
geometric-fibre consumers. -/
theorem addSubgroup_closure_pair_eq_top_iff (hcard : Nat.card G = p ^ 2)
    (hexp : ∀ g : G, p • g = 0) (P Q : G) :
    AddSubgroup.closure {P, Q} = ⊤ ↔
      ∀ a b : ℕ, ¬(p ∣ a ∧ p ∣ b) → a • P + b • Q ≠ 0 := by
  letI : Module (ZMod p) G := AddCommGroup.zmodModule hexp
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [zmodModule_closure_pair_eq_top_iff hcard P Q]
  constructor
  · intro h a b hab
    have hcast : (a : ZMod p) • P + (b : ZMod p) • Q = a • P + b • Q := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [← hcast]
    refine h _ _ ?_
    rintro ⟨ha, hb⟩
    exact hab ⟨(ZMod.natCast_eq_zero_iff a p).mp ha,
      (ZMod.natCast_eq_zero_iff b p).mp hb⟩
  · intro h a b hab
    have ha' : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_rightInverse a
    have hb' : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_rightInverse b
    rw [← ha', ← hb', Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    refine h _ _ ?_
    rintro ⟨hda, hdb⟩
    refine hab ⟨?_, ?_⟩
    · rw [← ha', Nat.eq_zero_of_dvd_of_lt hda (ZMod.val_lt a), Nat.cast_zero]
    · rw [← hb', Nat.eq_zero_of_dvd_of_lt hdb (ZMod.val_lt b), Nat.cast_zero]

end ModularCurves

/-- **(E[2]-generation reduction)** For `2`-torsion sections: the three nonzero
`ZMod 2`-combinations of an independent pair are nonzero. Feeds
`pair_generates_iff_combos_ne_zero` at `N = 2`. -/
theorem combos2_ne_zero {G : Type*} [AddCommGroup G] {P Q : G}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : P + Q ≠ 0) :
    ∀ ab : ZMod 2 × ZMod 2, ab ≠ 0 →
      ((ab.1.val : ℤ)) • P + ((ab.2.val : ℤ)) • Q ≠ 0 := by
  rintro ⟨a, b⟩ hab
  show ((a.val : ℤ)) • P + ((b.val : ℤ)) • Q ≠ 0
  have hval : ∀ c : ZMod 2, (c.val : ℤ) = 0 ∨ (c.val : ℤ) = 1 := by
    intro c
    have h := ZMod.val_lt c
    omega
  have hzero : ∀ c : ZMod 2, (c.val : ℤ) = 0 → c = 0 := fun c hc =>
    (ZMod.val_eq_zero c).mp (Int.natCast_eq_zero.mp hc)
  rcases hval a with ha | ha <;> rcases hval b with hb | hb <;>
    rw [ha, hb] <;> simp only [zero_zsmul, one_zsmul, zero_add, add_zero]
  · exact absurd (Prod.ext (hzero a ha) (hzero b hb)) hab
  · exact hQ
  · exact hP
  · exact hPQ

/-- **(the independence → combos reduction at `p = 3`)** For `3`-torsion elements of any
abelian group, the four independence conditions `P ≠ 0, Q ≠ 0, Q ≠ ±P` force all eight
nontrivial `(ℤ/3)²`-combinations away from zero (`2•x = −x` collapses every case). -/
theorem combos3_ne_zero {G : Type*} [AddCommGroup G] {P Q : G}
    (hP3 : (3 : ℤ) • P = 0) (hQ3 : (3 : ℤ) • Q = 0)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hQP : Q ≠ P) (hQnP : Q ≠ -P) :
    ∀ ab : ZMod 3 × ZMod 3, ab ≠ 0 →
      ((ab.1.val : ℤ)) • P + ((ab.2.val : ℤ)) • Q ≠ 0 := by
  have h2P : (2 : ℤ) • P = -P := by
    rw [show (2 : ℤ) = 3 - 1 by norm_num, sub_smul, hP3, one_zsmul, zero_sub]
  have h2Q : (2 : ℤ) • Q = -Q := by
    rw [show (2 : ℤ) = 3 - 1 by norm_num, sub_smul, hQ3, one_zsmul, zero_sub]
  rintro ⟨a, b⟩ hab
  show ((a.val : ℤ)) • P + ((b.val : ℤ)) • Q ≠ 0
  have hval : ∀ c : ZMod 3, (c.val : ℤ) = 0 ∨ (c.val : ℤ) = 1 ∨ (c.val : ℤ) = 2 := by
    intro c
    have h := ZMod.val_lt c
    omega
  have hzero : ∀ c : ZMod 3, (c.val : ℤ) = 0 → c = 0 := fun c hc =>
    (ZMod.val_eq_zero c).mp (Int.natCast_eq_zero.mp hc)
  rcases hval a with ha | ha | ha <;> rcases hval b with hb | hb | hb <;>
    rw [ha, hb] <;> simp only [zero_zsmul, one_zsmul, h2P, h2Q, zero_add, add_zero]
  · exact absurd (Prod.ext (hzero a ha) (hzero b hb)) hab
  · exact hQ
  · exact fun hc => hQ (neg_eq_zero.mp hc)
  · exact hP
  · exact fun hc => hQnP (eq_neg_of_add_eq_zero_right hc)
  · exact fun hc => hQP (neg_inj.mp (eq_neg_of_add_eq_zero_right hc))
  · exact fun hc => hP (neg_eq_zero.mp hc)
  · exact fun hc => hQP (neg_add_eq_zero.mp hc).symm
  · exact fun hc => hQnP (eq_neg_of_add_eq_zero_right
      (neg_eq_zero.mp (by rwa [← neg_add] at hc)))
