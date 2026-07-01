import BernoulliRegular.Reflection.ClassGroupModP.GalAction
import Mathlib.NumberTheory.NumberField.CMField

/-!
# K-side ClassGroup minus eigenspace `Cl(K)⁻`

For `K = ℚ(ζ_p)` (CM field), complex conjugation `σ : (𝓞 K) ≃+* (𝓞 K)`
acts on `ClassGroup (𝓞 K)` via `Ideal.map`. The **minus eigenspace**
`Cl(K)⁻ = {[I] : σ([I]) = [I]⁻¹}` is the part where σ acts as inversion
(equivalently, as `-1` in additive notation).

This file ships the K-side `Cl(K)⁻` definition and basic API, which
plays a role in the LV-route Stickelberger / Sinnott analysis. It is
**LV007a** of the FLT37 ticket board.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- The complex-conjugation action on `ClassGroup (𝓞 K)`.

This is the σ-action where `σ` is the unique non-trivial element of
`Gal(K/K⁺)` (= the complex conjugation for CM fields).

Implemented as `cyclotomicGalActionOnClassGroup` at index `-1 ∈ (ZMod p)ˣ`,
which corresponds to `σ(ζ) = ζ^{p-1} = ζ^{-1}` (the complex conjugation
on the cyclotomic field). -/
noncomputable def complexConjOnClassGroup :
    ClassGroup (𝓞 K) → ClassGroup (𝓞 K) :=
  cyclotomicGalActionOnClassGroup (p := p) (K := K) (-1 : CyclotomicUnitDelta p)

/-- The **minus eigenspace** `Cl(K)⁻ ⊆ ClassGroup (𝓞 K)`: the subgroup
of class group elements `c` such that `σ(c) = c⁻¹` (i.e., σ acts as
inversion, the multiplicative analog of acting as `-1`).

Mathematically, `|Cl(K)⁻| = h⁻(K) = h(K) / h⁺(K)` (the relative class
number). -/
def classGroupMinus : Subgroup (ClassGroup (𝓞 K)) where
  carrier := {c | complexConjOnClassGroup p K c = c⁻¹}
  one_mem' := by
    change complexConjOnClassGroup p K 1 = 1⁻¹
    rw [inv_one]
    -- σ(1) = 1 since σ is a group hom.
    unfold complexConjOnClassGroup
    -- cyclotomicGalActionOnClassGroup is a group hom
    exact map_one (cyclotomicGalActionMonoidHom (p := p) (K := K)
      (-1 : CyclotomicUnitDelta p))
  mul_mem' := by
    intro c₁ c₂ h₁ h₂
    change complexConjOnClassGroup p K (c₁ * c₂) = (c₁ * c₂)⁻¹
    unfold complexConjOnClassGroup at *
    rw [cyclotomicGalActionOnClassGroup_mul]
    rw [show cyclotomicGalActionOnClassGroup (p := p) (K := K) (-1) c₁ = c₁⁻¹ from h₁]
    rw [show cyclotomicGalActionOnClassGroup (p := p) (K := K) (-1) c₂ = c₂⁻¹ from h₂]
    exact (mul_inv c₁ c₂).symm
  inv_mem' := by
    intro c h
    change complexConjOnClassGroup p K c⁻¹ = (c⁻¹)⁻¹
    unfold complexConjOnClassGroup at *
    -- σ(c⁻¹) = σ(c)⁻¹ = (c⁻¹)⁻¹ = c, and (c⁻¹)⁻¹ = c.
    rw [show cyclotomicGalActionOnClassGroup (p := p) (K := K) (-1) c⁻¹ =
      (cyclotomicGalActionOnClassGroup (p := p) (K := K) (-1) c)⁻¹ from
      map_inv (cyclotomicGalActionMonoidHom (p := p) (K := K)
        (-1 : CyclotomicUnitDelta p)) _]
    rw [h, inv_inv]

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **Membership** in `classGroupMinus`: `c ∈ classGroupMinus K ↔ σ(c) = c⁻¹`. -/
theorem mem_classGroupMinus {c : ClassGroup (𝓞 K)} :
    c ∈ classGroupMinus p K ↔ complexConjOnClassGroup p K c = c⁻¹ :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- **MonoidHom version** of `complexConjOnClassGroup`. -/
noncomputable def complexConjOnClassGroupHom :
    ClassGroup (𝓞 K) →* ClassGroup (𝓞 K) :=
  cyclotomicGalActionMonoidHom (p := p) (K := K) (-1 : CyclotomicUnitDelta p)

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The function and MonoidHom forms agree. -/
@[simp]
theorem complexConjOnClassGroupHom_apply (c : ClassGroup (𝓞 K)) :
    complexConjOnClassGroupHom p K c = complexConjOnClassGroup p K c := rfl

omit [IsCMField K] in
/-- **Involutivity** of complex conjugation on the class group: applying
σ twice gives identity. Direct from `(-1) * (-1) = 1` in `(ZMod p)ˣ` and
`cyclotomicGalActionMonoidHom_one_apply`. -/
@[simp]
theorem complexConjOnClassGroup_involutive (c : ClassGroup (𝓞 K)) :
    complexConjOnClassGroup p K (complexConjOnClassGroup p K c) = c := by
  unfold complexConjOnClassGroup
  -- σ_{(-1)} ∘ σ_{(-1)} = σ_{(-1)·(-1)} = σ_{1} = id.
  have h_compose :
      cyclotomicGalActionMonoidHom (p := p) (K := K) ((-1) * (-1)) c =
      cyclotomicGalActionMonoidHom (p := p) (K := K) (-1)
        (cyclotomicGalActionMonoidHom (p := p) (K := K) (-1) c) :=
    cyclotomicGalActionMonoidHom_mul_apply (p := p) (K := K) (-1) (-1) c
  have h_neg_one_sq : ((-1 : CyclotomicUnitDelta p)) * ((-1 : CyclotomicUnitDelta p)) =
      1 := by
    rw [neg_one_mul, neg_neg]
  rw [h_neg_one_sq] at h_compose
  rw [cyclotomicGalActionMonoidHom_one_apply] at h_compose
  exact h_compose.symm

omit [IsCMField K] in
/-- **Membership of `c²` in `classGroupMinus` for any `c`**: the squaring
trick. `σ(c²) = σ(c)² = (c⁻¹·c⁻¹) = (c²)⁻¹`. Hence `c² ∈ classGroupMinus` for any
`c` such that `σ(c) = c⁻¹`.

(More precisely: this follows from `mul_mem` applied to `c · c`.) -/
theorem classGroupMinus_pow_two_mem {c : ClassGroup (𝓞 K)} (hc : c ∈ classGroupMinus p K) :
    c ^ 2 ∈ classGroupMinus p K := by
  rw [pow_two]
  exact (classGroupMinus p K).mul_mem hc hc

omit [IsCMField K] in
/-- **`σ` is a `MonoidHom` (preserves inverses)**: `σ(c⁻¹) = σ(c)⁻¹`. -/
@[simp]
theorem complexConjOnClassGroup_inv (c : ClassGroup (𝓞 K)) :
    complexConjOnClassGroup p K c⁻¹ = (complexConjOnClassGroup p K c)⁻¹ := by
  unfold complexConjOnClassGroup
  exact map_inv (cyclotomicGalActionMonoidHom (p := p) (K := K)
    (-1 : CyclotomicUnitDelta p)) c

omit [IsCMField K] in
/-- **`σ` preserves powers**: `σ(c^n) = σ(c)^n`. -/
@[simp]
theorem complexConjOnClassGroup_pow (c : ClassGroup (𝓞 K)) (n : ℕ) :
    complexConjOnClassGroup p K (c ^ n) = (complexConjOnClassGroup p K c) ^ n := by
  unfold complexConjOnClassGroup
  exact map_pow (cyclotomicGalActionMonoidHom (p := p) (K := K)
    (-1 : CyclotomicUnitDelta p)) c n

omit [IsCMField K] in
/-- **`classGroupMinus` is closed under all integer powers**: c ∈ Cl(K)⁻ → c^n ∈ Cl(K)⁻
for any `n : ℕ`. Direct from `Subgroup.pow_mem`. -/
theorem classGroupMinus_pow_mem
    {c : ClassGroup (𝓞 K)} (hc : c ∈ classGroupMinus p K) (n : ℕ) :
    c ^ n ∈ classGroupMinus p K :=
  (classGroupMinus p K).pow_mem hc n

end Sinnott

end FLT37

end BernoulliRegular

end
