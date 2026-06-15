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
`Module (ZMod p)` instance.

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
