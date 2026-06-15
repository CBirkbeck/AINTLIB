module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Character
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Residue Gauss sum (REF-18c2b)

This file packages the Gauss sum at a residue character `χ_q` (REF-18c2a).
For a finite field `k` with `p ∣ #k - 1`, a chosen primitive `p`-th root of
unity in a target field `R'`, and a non-trivial additive character
`ψ_q : AddChar k R'`, the residue Gauss sum is

  `g(χ_q, ψ_q) := Σ_{x ∈ k} χ_q(x) · ψ_q(x) ∈ R'`

defined via mathlib's general `gaussSum`. The basic norm relation
`g(χ) · g(χ⁻¹, ψ⁻¹) = #k` follows from
`gaussSum_mul_gaussSum_eq_card` once we feed it `IsPrimitive ψ_q` and
`χ_q ≠ 1`.

This commit lands the Gauss-sum *definition* and the immediate norm
corollary; the substantive Frobenius / Galois-action facts (the rest of
REF-18c2b) are left for follow-ups since they need additional setup
(choice of additive character, ambient cyclotomic extension, Galois
trasport).

## Main definitions

* `BernoulliRegular.Furtwaengler.residueGaussSum`: the Gauss sum
  `g(χ_q, ψ_q)`.
* `residueGaussSum_mul_inv_eq_card`: the basic norm identity, valid when
  `χ_q ≠ 1` and `ψ_q` is primitive.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable {p : ℕ}

/-- The residue Gauss sum `g(χ_q, ψ_q) := Σ_x χ_q(x) ψ_q(x)`, where `χ_q`
is the residue character at `q ∤ p` (REF-18c2a) and `ψ_q` is a chosen
additive character on `k = 𝓞_K/q` valued in the target ring `R'`. -/
def residueGaussSum [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R') : R' :=
  gaussSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) psi_q

omit [IsDomain R'] in
@[simp]
theorem residueGaussSum_def [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R') :
    residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q =
      gaussSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) psi_q :=
  rfl

/-- **Norm relation for the residue Gauss sum.** When `χ_q ≠ 1` and
`ψ_q` is primitive, the product
`g(χ_q, ψ_q) · g(χ_q⁻¹, ψ_q⁻¹) = #k`. This is the residue-Gauss-sum
specialisation of mathlib's `gaussSum_mul_gaussSum_eq_card`. -/
theorem residueGaussSum_mul_inv_eq_card [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive)
    (hχ : residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ≠ 1) :
    residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q *
      gaussSum (residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R)⁻¹ psi_q⁻¹ =
        Fintype.card k :=
  gaussSum_mul_gaussSum_eq_card hχ hpsi

end Furtwaengler

end BernoulliRegular

/-!
### Galois action on Gauss sums

The Gauss sum behaves naturally under ring homomorphisms of the target:
post-composing `χ` and `ψ` with a ring hom `σ` and applying `σ` to the
Gauss sum coincide. This is the core lemma from which Galois-equivariance
of residue Gauss sums follows.
-/

namespace BernoulliRegular

namespace Furtwaengler

/-- General Galois action: applying a ring hom `σ : R' →+* R''` to a Gauss
sum is the same as taking the Gauss sum of the post-composed multiplicative
and additive characters. -/
theorem _root_.gaussSum_ringHomComp
    {R : Type*} [CommRing R] [Fintype R]
    {R' R'' : Type*} [CommRing R'] [CommRing R'']
    (χ : MulChar R R') (ψ : AddChar R R') (σ : R' →+* R'') :
    σ (gaussSum χ ψ) = gaussSum (χ.ringHomComp σ) (σ.toMonoidHom.compAddChar ψ) := by
  unfold gaussSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [MulChar.ringHomComp_apply, MonoidHom.compAddChar_apply,
    map_mul, Function.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]

variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable {p : ℕ}

omit [IsDomain R'] in
/-- **Galois action on the residue Gauss sum.** For any ring hom
`σ : R' →+* R''`, applying `σ` to `residueGaussSum` yields the Gauss sum
of the post-composed character data. -/
theorem residueGaussSum_ringHomComp [NeZero p]
    {R'' : Type*} [CommRing R'']
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (psi_q : AddChar k R') (σ : R' →+* R'') :
    σ (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) =
      gaussSum
        ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R).ringHomComp σ)
        (σ.toMonoidHom.compAddChar psi_q) :=
  gaussSum_ringHomComp _ _ σ

end Furtwaengler

end BernoulliRegular

/-!
### Non-triviality bridge

The exponent vanishes exactly when the underlying finite-field power
`x ^ ((#k - 1) / p)` is `1`. This bridge lets the user demonstrate
non-triviality of `residueMulChar` by exhibiting an element of `kˣ`
with non-trivial `(#k - 1)/p`-power.
-/

namespace BernoulliRegular

namespace Furtwaengler

open Reflection.ResidueSymbol.PowerResidue

/-- `finiteFieldExponent` vanishes on `x` iff `finiteFieldUnit hdiv x = 1`,
i.e. `x ^ ((#k - 1) / p) = 1`. -/
theorem finiteFieldExponent_eq_zero_iff
    {k : Type*} [Field k] [Fintype k]
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldExponent zeta_q hzeta_q hdiv x = 0 ↔
      finiteFieldUnit hdiv x = 1 := by
  unfold finiteFieldExponent
  rw [(hzeta_q.zmodEquivZPowers).symm.map_eq_zero_iff]
  -- Goal: Additive.ofMul ⟨finiteFieldUnit hdiv x, _⟩ = 0 ↔ finiteFieldUnit hdiv x = 1
  constructor
  · intro h
    have hh : (⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta_q hdiv x⟩ :
              Subgroup.zpowers zeta_q) = 1 := by
      have := congrArg Additive.toMul h
      simpa using this
    exact congrArg Subtype.val hh
  · intro h
    have hh : (⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta_q hdiv x⟩ :
              Subgroup.zpowers zeta_q) = 1 := Subtype.ext h
    have := congrArg Additive.ofMul hh
    simpa using this

/-- Non-trivial finite-field power gives non-trivial residue character on
that input. Useful for witnessing `residueMulChar ≠ 1`. -/
theorem residueMulChar_apply_ne_one_of_finiteFieldUnit_ne_one
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommMonoidWithZero R']
    {p : ℕ} [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {x : kˣ} (hx : finiteFieldUnit hdiv x ≠ 1) :
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R (x : k) ≠ 1 := by
  rw [residueMulChar_apply_unit]
  intro h
  -- h : ((zeta_R : R')) ^ (finiteFieldExponent ...).val = 1
  -- Use that zeta_R has order p in R'ˣ to deduce p ∣ (...).val.
  have h_zeta : ((zeta_R : R'ˣ) : R') ^ (finiteFieldExponent zeta_q hzeta_q hdiv x).val = 1 := h
  have h_units : (zeta_R ^ (finiteFieldExponent zeta_q hzeta_q hdiv x).val : R'ˣ) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h_zeta
  have h_dvd : p ∣ (finiteFieldExponent zeta_q hzeta_q hdiv x).val :=
    hzeta_R.dvd_of_pow_eq_one _ h_units
  have h_lt : (finiteFieldExponent zeta_q hzeta_q hdiv x).val < p := ZMod.val_lt _
  have h_zero : (finiteFieldExponent zeta_q hzeta_q hdiv x).val = 0 := by
    rcases Nat.eq_zero_or_pos (finiteFieldExponent zeta_q hzeta_q hdiv x).val with h0 | hpos
    · exact h0
    · exact absurd (Nat.le_of_dvd hpos h_dvd) (Nat.not_le_of_gt h_lt)
  have : finiteFieldExponent zeta_q hzeta_q hdiv x = 0 :=
    (ZMod.val_eq_zero _).mp <| h_zero
  rw [(finiteFieldExponent_eq_zero_iff zeta_q hzeta_q hdiv x).mp this] at hx
  exact hx rfl

/-- For `p` prime and `p ∣ #k - 1`, a generator of `kˣ` has `(#k - 1)/p`-power
not equal to `1`. The proof uses that `kˣ` is cyclic of order `#k - 1`. -/
theorem exists_finiteFieldUnit_ne_one
    {k : Type*} [Field k] [Fintype k]
    {p : ℕ} [hp : Fact p.Prime]
    (hdiv : p ∣ Fintype.card k - 1) :
    ∃ x : kˣ, finiteFieldUnit hdiv x ≠ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  refine ⟨g, ?_⟩
  intro h_eq
  unfold finiteFieldUnit at h_eq
  have h_order : orderOf g = Fintype.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
        Fintype.card_units]
  have h_dvd : orderOf g ∣ (Fintype.card k - 1) / p :=
    orderOf_dvd_of_pow_eq_one h_eq
  rw [h_order] at h_dvd
  have h_card_ge_2 : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have h_card_pos : 0 < Fintype.card k - 1 := by omega
  have h_div_lt : (Fintype.card k - 1) / p < Fintype.card k - 1 :=
    Nat.div_lt_self h_card_pos hp.out.one_lt
  have h_div_pos : 0 < (Fintype.card k - 1) / p :=
    Nat.div_pos (Nat.le_of_dvd h_card_pos hdiv) hp.out.pos
  have h_le : Fintype.card k - 1 ≤ (Fintype.card k - 1) / p :=
    Nat.le_of_dvd h_div_pos h_dvd
  omega

/-- The residue character `χ_q` is non-trivial: there is some unit in `kˣ`
mapping to a non-`1` value. -/
theorem residueMulChar_ne_one
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommMonoidWithZero R']
    {p : ℕ} [hp : Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_finiteFieldUnit_ne_one (k := k) (p := p) hdiv
  intro h_eq
  have h_apply :=
    residueMulChar_apply_ne_one_of_finiteFieldUnit_ne_one
      zeta_q hzeta_q hdiv zeta_R hzeta_R hx
  apply h_apply
  rw [h_eq]
  exact MulChar.one_apply_coe x

end Furtwaengler

end BernoulliRegular
