module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Teichmuller
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Characters of `Gal(ℚ(ζ_p)/ℚ)` — Teichmüller character

Let `p` be a prime. The Teichmüller character `ω : ZMod p →*₀ ℤ_[p]`
sends each nonzero residue class `a ∈ (ZMod p)ˣ` to the unique `(p-1)`-th
root of unity in `ℤ_[p]` that reduces to `a` modulo `p`, and sends the
zero residue class to `0`.

The construction reuses mathlib's `Perfection.teichmuller₀`: since the
residue field `ℤ_[p] ⧸ maximalIdeal ℤ_[p]` is canonically isomorphic to
`ZMod p`, which is perfect (finite of characteristic `p`), `ZMod p` is
identified with the perfection, after which the generic Teichmüller map
lands in `ℤ_[p]`.

## Main definitions

- `BernoulliRegular.teichmuller` — `ω : ZMod p →*₀ ℤ_[p]`.

## Main results

- `toZMod_teichmuller` — `ω(a) ≡ a (mod p)`.
- `teichmuller_pow_sub_one` — `ω(a)^{p-1} = 1` for `a ≠ 0`.
- The `MonoidWithZeroHom` structure is provided by the bundled
  definition, so `teichmuller_zero`, `teichmuller_one`,
  `teichmuller_mul` follow.

## References

- Diekmann, *FLT for regular primes* (2023), Lemma 20.
- Washington, *Introduction to Cyclotomic Fields*, §5.1.
-/

@[expose] public section

noncomputable section

open Perfection PadicInt IsLocalRing

namespace BernoulliRegular

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Instances on `ℤ_[p] ⧸ maximalIdeal ℤ_[p]`

We need `CharP _ p`, `Finite`, and `PerfectRing _ p` on the raw
quotient ring to feed into `Perfection.teichmuller₀`. All three propagate
across the canonical ring equivalence with `ZMod p` (mathlib's
`PadicInt.residueField` has codomain `IsLocalRing.ResidueField ℤ_[p]`,
which is definitionally the quotient; we rebuild it explicitly to avoid
typeclass-resolution friction through that wrapper). -/

/-- `ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p`. Reuses
`PadicInt.residueField` (whose codomain `IsLocalRing.ResidueField ℤ_[p]`
is definitionally `ℤ_[p] ⧸ maximalIdeal ℤ_[p]`). -/
noncomputable def maximalIdealQuotientEquivZMod : ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

instance maximalIdealQuotient_charP : CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p :=
  charP_of_injective_ringHom (f := (maximalIdealQuotientEquivZMod p).symm.toRingHom)
    (maximalIdealQuotientEquivZMod p).symm.injective p

instance maximalIdealQuotient_finite : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
  Finite.of_equiv _ (maximalIdealQuotientEquivZMod p).symm.toEquiv

/-! ### Teichmüller character via `Perfection.teichmuller₀` -/

/-- The Teichmüller character `ω : ZMod p →*₀ ℤ_[p]`. Composition of:

- `(maximalIdealQuotientEquivZMod p).symm : ZMod p ≃+* ℤ_[p] ⧸ maximalIdeal`,
- `(PerfectionMap.id p _).equiv : (ℤ_[p] ⧸ maximalIdeal) ≃+*
  Perfection (ℤ_[p] ⧸ maximalIdeal) p`,
- `Perfection.teichmuller₀ p (maximalIdeal ℤ_[p]) :
  Perfection (ℤ_[p] ⧸ maximalIdeal) p →*₀ ℤ_[p]`.

Its image is `μ_{p-1} ∪ {0}` in `ℤ_[p]`. -/
noncomputable def teichmuller : ZMod p →*₀ ℤ_[p] :=
  (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])).comp <|
    (PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom.comp
      (maximalIdealQuotientEquivZMod p).symm.toRingHom.toMonoidWithZeroHom

variable {p}

@[simp]
lemma teichmuller_zero : teichmuller p 0 = 0 := map_zero _

@[simp]
lemma teichmuller_one : teichmuller p 1 = 1 := map_one _

@[simp]
lemma teichmuller_mul (a b : ZMod p) : teichmuller p (a * b) = teichmuller p a * teichmuller p b :=
  map_mul _ _ _

/-- `ω(a) ≡ a (mod p)` for every `a ∈ ZMod p`. -/
@[simp]
lemma toZMod_teichmuller (a : ZMod p) : PadicInt.toZMod (teichmuller p a) = a := by
  change PadicInt.toZMod
    (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])
      ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv
        ((maximalIdealQuotientEquivZMod p).symm a))) = a
  rw [PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  change PadicInt.residueField (Ideal.Quotient.mk _ _) = a
  rw [Perfection.mk_teichmuller₀, PerfectionMap.comp_equiv]
  -- Goal now: `residueField (maximalIdealQuotientEquivZMod.symm a) = a`. Since
  -- `maximalIdealQuotientEquivZMod = residueField` (same construction), this is
  -- just `apply_symm_apply`.
  exact (maximalIdealQuotientEquivZMod p).apply_symm_apply a

/-- `ω(a)^(p-1) = 1` for nonzero `a ∈ ZMod p`. -/
lemma teichmuller_pow_sub_one {a : ZMod p} (ha : a ≠ 0) : teichmuller p a ^ (p - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one ha, map_one]

/-- `ω(a)` is a unit of `ℤ_[p]` whenever `a ≠ 0`. -/
lemma isUnit_teichmuller {a : ZMod p} (ha : a ≠ 0) : IsUnit (teichmuller p a) :=
  IsUnit.of_pow_eq_one (teichmuller_pow_sub_one ha) (by have := hp.1.one_lt; omega)

/-- `ω(a) = 0` iff `a = 0`. -/
@[simp]
lemma teichmuller_eq_zero_iff {a : ZMod p} : teichmuller p a = 0 ↔ a = 0 :=
  ⟨fun h => not_imp_not.mp (fun ha => (isUnit_teichmuller ha).ne_zero) h,
    fun h => h ▸ teichmuller_zero⟩

/-- `ω` is injective on `ZMod p` (follows from `toZMod ∘ ω = id`). -/
lemma teichmuller_injective : Function.Injective (teichmuller p) := fun _ _ hab => by
  simpa using congrArg PadicInt.toZMod hab

/-- Fixed point of Frobenius: `ω(a)^p = ω(a)` for any `a : ZMod p`.
This follows from `a^p = a` in `ZMod p` (Fermat) and multiplicativity. -/
lemma teichmuller_pow_card (a : ZMod p) : teichmuller p a ^ p = teichmuller p a := by
  rw [← map_pow, ZMod.pow_card]

/-- **Sharper Teichmüller congruence**: `ω(a) ≡ a^p (mod p²)` in `ℤ_[p]`,
where the lift of `a` to `ℤ_[p]` is taken via `ZMod.val`.

Proof: `ω(a) ≡ (a.val : ℤ_[p]) (mod p)` (basic Teichmüller property),
so `ω(a)^p ≡ (a.val)^p (mod p²)` by `SModEq.pow_pow_add_one`. But
`ω(a)^p = ω(a)` by `teichmuller_pow_card`, giving the claim. -/
lemma teichmuller_sModEq_pow_val (a : ZMod p) :
    teichmuller p a ≡ (a.val : ℤ_[p]) ^ p [SMOD (maximalIdeal ℤ_[p]) ^ 2] := by
  -- Step A: `ω(a) ≡ (a.val : ℤ_[p]) [SMOD maximalIdeal]`.
  have h_base : teichmuller p a ≡ (a.val : ℤ_[p]) [SMOD maximalIdeal ℤ_[p]] := by
    rw [SModEq.sub_mem, ← ker_toZMod, RingHom.mem_ker, map_sub, toZMod_teichmuller,
      map_natCast, ZMod.natCast_val, ZMod.cast_id, sub_self]
  -- Step B: raise to the `p`-th power, gaining one factor of the maximal ideal.
  have hp_mem : ((p : ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  have h_pow := h_base.pow_pow_add_one hp_mem 1
  -- Step C: `(teichmuller p a)^p = teichmuller p a`.
  rwa [pow_one, teichmuller_pow_card] at h_pow

/-- `ω(a) - (a.val : ℤ_[p])^p ∈ p² · ℤ_[p]`. Equivalent reformulation
of `teichmuller_sModEq_pow_val`. -/
lemma teichmuller_sub_pow_val_mem_pow_two (a : ZMod p) :
    teichmuller p a - (a.val : ℤ_[p]) ^ p ∈ (maximalIdeal ℤ_[p]) ^ 2 :=
  SModEq.sub_mem.mp (teichmuller_sModEq_pow_val a)

/-! ### The Teichmüller character as a Dirichlet character -/

/-- The Teichmüller character `ω : ZMod p →*₀ ℤ_[p]` packaged as a
`DirichletCharacter ℤ_[p] p`. A Dirichlet character must send
non-units to `0`; for `ZMod p` (a field for `p` prime), non-unit
means `0`, and `ω(0) = 0` by construction. -/
noncomputable def teichmullerChar (p : ℕ) [Fact p.Prime] : DirichletCharacter ℤ_[p] p where
  toFun := teichmuller p
  map_one' := map_one _
  map_mul' := map_mul _
  map_nonunit' := fun a ha => by
    rw [show a = 0 from by_contra fun hne => ha (isUnit_iff_ne_zero.mpr hne), teichmuller_zero]

@[simp]
lemma teichmullerChar_apply (a : ZMod p) : teichmullerChar p a = teichmuller p a := rfl

/-! ### Primitive `(p-1)`-th root of unity and
`HasEnoughRootsOfUnity` instance -/

/-- If `g : (ZMod p)ˣ` generates the unit group, then
`ω(g) = teichmuller p (g : ZMod p)` is a primitive `(p-1)`-th root of
unity in `ℤ_[p]`. -/
lemma teichmuller_isPrimitiveRoot_of_generator {g : (ZMod p)ˣ}
    (hg_gen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (teichmuller p (g : ZMod p)) (p - 1) := by
  refine ⟨?_, fun l hl => ?_⟩
  · -- `ω(g)^(p-1) = ω(g^(p-1)) = ω(1) = 1` (Fermat in `(ZMod p)ˣ`).
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one,
      Units.val_one, map_one]
  · -- `ω(g)^l = 1` ⟹ `ω(g^l) = ω(1)` ⟹ `g^l = 1` in `ZMod p` (injectivity)
    -- ⟹ `g^l = 1` in `(ZMod p)ˣ` ⟹ `(p-1) ∣ l` (since `g` has order `p-1`).
    have h_units : g ^ l = 1 := Units.ext <| by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact teichmuller_injective (by rwa [map_pow, map_one])
    have h_order : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card, ZMod.card_units]
    rw [← h_order]; exact orderOf_dvd_of_pow_eq_one h_units

instance : NeZero (p - 1) := ⟨by have := hp.1.two_le; omega⟩

/-- `ℤ_[p]` contains enough `(p-1)`-th roots of unity. -/
instance : HasEnoughRootsOfUnity ℤ_[p] (p - 1) where
  prim := by
    obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    exact ⟨teichmuller p (g : ZMod p), teichmuller_isPrimitiveRoot_of_generator hg_gen⟩
  cyc := inferInstance

/-! ### T002: the character group is cyclic of order `p - 1` -/

lemma exponent_zmod_units : Monoid.exponent (ZMod p)ˣ = p - 1 := by
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units]

variable (p) in
/-- **Diekmann Lemma 21** (mathlib form): the group of `ℤ_[p]`-valued
Dirichlet characters mod `p` is (noncanonically) isomorphic to
`(ZMod p)ˣ`, hence cyclic of order `p - 1`. -/
lemma dirichletCharacter_mulEquiv_zmodUnits :
    Nonempty (DirichletCharacter ℤ_[p] p ≃* (ZMod p)ˣ) := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  haveI : HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (ZMod p)ˣ) :=
    exponent_zmod_units (p := p) ▸ inferInstance
  exact DirichletCharacter.mulEquiv_units ℤ_[p] p

/-- The `ℤ_[p]`-valued Dirichlet character group mod `p` has `p - 1`
elements. -/
lemma card_dirichletCharacter : Nat.card (DirichletCharacter ℤ_[p] p) = p - 1 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  haveI : HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (ZMod p)ˣ) :=
    exponent_zmod_units (p := p) ▸ inferInstance
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,
    Nat.totient_prime hp.1]

/-- `ω^(p-1) = 1` in the Dirichlet character group: the `(p-1)`-th power
of the Teichmüller character is the trivial character. This is the
concrete form of "characters cycle with period `p-1`". -/
lemma teichmullerChar_pow_sub_one_eq_one : (teichmullerChar p) ^ (p - 1) = 1 := by
  ext a
  rw [MulChar.pow_apply_coe, teichmullerChar_apply, MulChar.one_apply_coe]
  exact teichmuller_pow_sub_one a.ne_zero

/-- The Teichmüller character has order exactly `p - 1` in
`DirichletCharacter ℤ_[p] p`. Combined with
`card_dirichletCharacter`, this says `ω` generates the character
group. -/
lemma orderOf_teichmullerChar : orderOf (teichmullerChar p) = p - 1 := by
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one teichmullerChar_pow_sub_one_eq_one) ?_
  -- `(p-1) ∣ orderOf ω`: `ω^(orderOf ω) = 1`, so at a generator `g`,
  -- `(teichmuller g)^(orderOf ω) = 1`. Since `teichmuller g` is a
  -- primitive `(p-1)`-th root of unity, `(p-1) ∣ orderOf ω`.
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have h_apply := congrArg (fun χ : DirichletCharacter ℤ_[p] p => χ (g : ZMod p))
    (pow_orderOf_eq_one (teichmullerChar p))
  simp only [MulChar.pow_apply_coe, teichmullerChar_apply, MulChar.one_apply_coe] at h_apply
  exact (teichmuller_isPrimitiveRoot_of_generator hg_gen).2 _ h_apply

/-- A power of the Teichmueller character is trivial exactly when the
exponent is a multiple of `p - 1`. -/
lemma teichmullerChar_pow_eq_one_iff (n : ℕ) : (teichmullerChar p) ^ n = 1 ↔ (p - 1) ∣ n := by
  refine ⟨fun hpow => ?_, ?_⟩
  · simpa [orderOf_teichmullerChar (p := p)] using orderOf_dvd_of_pow_eq_one hpow
  · rintro ⟨m, rfl⟩
    rw [← orderOf_teichmullerChar (p := p), pow_mul, pow_orderOf_eq_one, one_pow]

lemma teichmullerChar_pow_ne_one_of_not_dvd {n : ℕ} (hn : ¬ (p - 1) ∣ n) :
    (teichmullerChar p) ^ n ≠ 1 :=
  mt (teichmullerChar_pow_eq_one_iff (p := p) n).mp hn

/-- `DirichletCharacter ℤ_[p] p` is cyclic. Together with
`orderOf_teichmullerChar`, this gives the Diekmann Lemma 21 statement
that every character is some power of `ω`. -/
instance : IsCyclic (DirichletCharacter ℤ_[p] p) :=
  isCyclic_of_orderOf_eq_card (teichmullerChar p) <| by
    rw [orderOf_teichmullerChar, ← card_dirichletCharacter (p := p)]

/-! ### T004 — Character sum identity (Diekmann Lemma 24) -/

/-- **Diekmann Lemma 24**: the sum `∑_{a ∈ ZMod p} χ(a)` is zero for
any non-trivial Dirichlet character `χ` mod `p` with values in `ℤ_[p]`.
Since `χ(0) = 0`, this agrees with the summation `∑_{n=1}^{p-1} χ(n)`. -/
lemma dirichletCharacter_sum_eq_zero_of_ne_one
    {χ : DirichletCharacter ℤ_[p] p} (hχ : χ ≠ 1) :
    ∑ a : ZMod p, χ a = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

/-! ### T003 — Character parity (Diekmann Lemmas 23, 25) -/

/-- `ω(-1) = -1` for any odd prime `p`.

Proof: `(ω(-1))^2 = ω(1) = 1`, so `ω(-1) ∈ {1, -1}` in the integral
domain `ℤ_[p]`. Reducing mod `p` gives `-1`, which is distinct from `1`
when `p ≠ 2`, forcing `ω(-1) = -1`. -/
lemma teichmuller_neg_one (hp_odd : p ≠ 2) : teichmuller p (-1) = -1 := by
  have h_sq : teichmuller p (-1 : ZMod p) ^ 2 = 1 := by
    rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
  rcases sq_eq_one_iff.mp h_sq with h1 | h_neg
  · haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)⟩
    exact absurd (by simpa using congrArg PadicInt.toZMod h1) ZMod.neg_one_ne_one
  · exact h_neg

/-- The Teichmüller character is odd: `ω(-1) = -1`, for `p` odd. -/
lemma teichmullerChar_odd (hp_odd : p ≠ 2) : (teichmullerChar p).Odd :=
  show teichmullerChar p (-1) = -1 by rw [teichmullerChar_apply]; exact teichmuller_neg_one hp_odd

/-- `(-1 : ℤ_[p]) ≠ 1`. -/
lemma padicInt_neg_one_ne_one : (-1 : ℤ_[p]) ≠ 1 := fun h => by
  have : (2 : ℤ) = 0 := by exact_mod_cast (by linear_combination -h : (2 : ℤ_[p]) = 0)
  norm_num at this

/-- `ω^i(-1) = (-1)^i` for `p` an odd prime. -/
lemma teichmullerChar_pow_apply_neg_one (hp_odd : p ≠ 2) (i : ℕ) :
    ((teichmullerChar p) ^ i) (-1 : ZMod p) = (-1 : ℤ_[p]) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero, pow_zero]; exact MulChar.one_apply isUnit_one.neg
  · rw [MulChar.pow_apply' _ hi.ne', teichmullerChar_apply, teichmuller_neg_one hp_odd]

/-- **Diekmann Lemmas 23 & 25**: `ω^i` is an even Dirichlet character
iff `i` is an even natural number. -/
lemma teichmullerChar_pow_even_iff (hp_odd : p ≠ 2) (i : ℕ) :
    ((teichmullerChar p) ^ i).Even ↔ Even i := by
  change ((teichmullerChar p) ^ i) (-1) = 1 ↔ Even i
  rw [teichmullerChar_pow_apply_neg_one hp_odd, neg_one_pow_eq_one_iff_even padicInt_neg_one_ne_one]

/-- `ω^i` is an odd Dirichlet character iff `i` is an odd natural number. -/
lemma teichmullerChar_pow_odd_iff (hp_odd : p ≠ 2) (i : ℕ) :
    ((teichmullerChar p) ^ i).Odd ↔ Odd i := by
  change ((teichmullerChar p) ^ i) (-1) = -1 ↔ Odd i
  rw [teichmullerChar_pow_apply_neg_one hp_odd,
    neg_one_pow_eq_neg_one_iff_odd padicInt_neg_one_ne_one]

end BernoulliRegular
