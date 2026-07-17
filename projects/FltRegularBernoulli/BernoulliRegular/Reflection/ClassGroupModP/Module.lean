/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.HilbertClassField
public import Mathlib.Algebra.Module.ZMod

/-!
# `Additive (ClassGroupModP K p)` is a `ZMod p`-module

This file establishes the standard `ZMod p`-module structure on
`Additive (ClassGroupModP K p)` (where
`ClassGroupModP K p := ClassGroup (𝓞 K) ⧸ (powMonoidHom p).range`).

Every element `x : ClassGroupModP K p` satisfies `x^p = 1`
(multiplicatively), hence `p • (Additive.ofMul x) = 0` in additive
notation. By `AddCommGroup.zmodModule`, this gives a canonical
`Module (ZMod p)` instance. We also record that divisibility of the
class number by `p` makes `ClassGroupModP K p` nontrivial.

## Atom (B) — partial

This is the first piece of REF-26's substantive Atom (B): construct the
`ZMod p`-module structure on `V := Cl(K)/p`. The Δ-action is built
in subsequent files.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]

omit hp in
/-- Every element of `ClassGroupModP K p` is `p`-torsion (multiplicatively). -/
theorem classGroupModP_pow_p_eq_one (x : ClassGroupModP K p) : x ^ p = 1 := by
  -- x is the class of some y ∈ ClassGroup
  refine QuotientGroup.induction_on x ?_
  intro y
  rw [← QuotientGroup.mk_pow]
  -- y^p ∈ (powMonoidHom p).range
  exact (QuotientGroup.eq_one_iff (y ^ p)).mpr <| ⟨y, rfl⟩

/-- If `p` divides the class number of `K`, then `ClassGroupModP K p` is nontrivial. -/
theorem nontrivial_classGroupModP_of_dvd_card
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [Fintype (ClassGroup (𝓞 K))]
    (hp_dvd : p ∣ Fintype.card (ClassGroup (𝓞 K))) :
    Nontrivial (ClassGroupModP K p) := by
  rw [nontrivial_iff_exists_ne (1 : ClassGroupModP K p)]
  by_contra! h_triv
  have h_subsing : Subsingleton (ClassGroupModP K p) :=
    ⟨fun a b => by rw [h_triv a, h_triv b]⟩
  have h_surj : Function.Surjective
      (powMonoidHom p : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)) := by
    rw [← MonoidHom.range_eq_top, Subgroup.eq_top_iff']
    exact fun x => (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have h_inj : Function.Injective
      (powMonoidHom p : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)) :=
    Finite.injective_iff_surjective.mpr h_surj
  have h_no_p_tors : ∀ x : ClassGroup (𝓞 K), x ^ p = 1 → x = 1 := fun x hx =>
    h_inj (by simpa [powMonoidHom] using hx)
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card (G := ClassGroup (𝓞 K)) p hp_dvd
  rw [h_no_p_tors x (orderOf_dvd_iff_pow_eq_one.mp (hx_ord ▸ dvd_refl p)), orderOf_one]
    at hx_ord
  exact (Fact.out : Nat.Prime p).one_lt.ne hx_ord

/-- `Additive (ClassGroupModP K p)` is a `ZMod p`-module via
`AddCommGroup.zmodModule`. -/
instance instModuleZModAdditiveClassGroupModP :
    Module (ZMod p) (Additive (ClassGroupModP K p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact classGroupModP_pow_p_eq_one x.toMul

end BernoulliRegular

end
