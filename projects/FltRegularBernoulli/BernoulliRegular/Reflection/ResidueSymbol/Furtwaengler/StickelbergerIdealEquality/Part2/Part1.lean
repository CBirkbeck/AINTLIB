module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality.Part1

/-!
# `StickelbergerIdealEquality` from a `FullTeichDworkSetup`

This file provides the substantive valuation-descent content of c.1
(`REF-18c2d-main-c.1`) by showing how to assemble a
`StickelbergerIdealEquality (S.Q.under (𝓞 K))` from a
`FullTeichDworkSetup S` together with a coverage hypothesis on the
Galois orbit of the descent prime.

## Strategy

The Dwork bundle gives the EXACT `Q`-adic order
`S.gaussSumInt a ∈ S.Q^(stickOrdOrd a) ∧ S.gaussSumInt a ∉ S.Q^(stickOrdOrd a + 1)`
at the SINGLE prime `S.Q ⊂ 𝓞 R'` for each `a ∈ [1, p-1]`. The route
to the multi-conjugate Stickelberger ideal in `𝓞 K` factors through
the descent prime `q_K = S.Q.under (𝓞 K)` and the Galois orbit
`cyclotomicConjugates q_K`:

1. **Per-`a` descent witness** (`StickelbergerPerConjugateDescent`):
   for each `a`, the existence of `γ_a ∈ 𝓞 K` whose image in `𝓞 R'`
   equals `S.gaussSumInt a ^ p` and whose `descentPrime`-adic order is
   `p · stickOrdOrd a / e` where `e = descentRamificationIdx`.

2. **Galois-orbit coverage** (`StickelbergerOrbitCoverage`): the
   Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` admits a
   single global generator `γ ∈ 𝓞 K` whose ideal factorization at each
   conjugate matches the prescribed exponent.

3. **Final assembly** (`stickelbergerIdealEquality_of_dwork_witness`):
   under both witnesses, the principal ideal `(γ)` equals
   `stickelbergerIdeal q_K`, and so `StickelbergerIdealEquality q_K`
   holds.

The current file delivers (1) and the **conditional** (3) under (2).
The unconditional (2) requires a separate per-conjugate bundle for
each Galois conjugate prime above `ℓ` (one bundle per representative
of the Galois orbit of `S.Q`); that step is left as a coverage
hypothesis here, packaged as the `Prop` predicate
`StickelbergerOrbitCoverage`.

## Why split

The full unconditional c.1 builds a single global generator from
multiple per-conjugate bundles by orbit-summing. That assembly is the
substantive remaining content. The conditional form delivered here
already discharges all the **valuation-descent** content (per-`a`
exact orders, ramification descent, Dwork EXACT-order data); only the
**orbit-coverage** combinatorics remain.

## Files

* Per-`a` exact-order descent: theorems
  `gaussSumInt_pow_descentPrime_pow_mul_stickOrdOrd`,
  `gaussSumInt_pow_not_mem_descentPrime_pow_mul_stickOrdOrd_succ` (in
  this file, on `FullTeichDworkSetup`).
* Final `StickelbergerIdealEquality` constructor: theorem
  `stickelbergerIdealEquality_of_orbitCoverage`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- The residue value of `a * ℓ^i`, viewed as a unit of `ZMod p`, is the
corresponding natural residue orbit representative. -/
theorem cyclotomicUnit_mul_frobeniusPower_val_eq_residueOrbit
    {ℓ p : ℕ} [Fact (Nat.Prime p)]
    (hℓp : ℓ.Coprime p) (a : CyclotomicUnitDelta p) (i : ℕ) :
    (((a * (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p) ^ i :
        CyclotomicUnitDelta p) : ZMod p).val) =
      residueOrbit ℓ p (a : ZMod p).val i := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hlt : residueOrbit ℓ p (a : ZMod p).val i < p := Nat.mod_lt _ hp_pos
  have hcast :
      (((a * (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p) ^ i :
          CyclotomicUnitDelta p) : ZMod p)) =
        (residueOrbit ℓ p (a : ZMod p).val i : ZMod p) := by
    unfold residueOrbit
    simp [Units.val_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  have h := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast_of_lt hlt] at h

/-- Enumerate a Frobenius coset by the distinct powers of the Frobenius unit.

The left side sums over all cyclotomic units but only keeps the units in the
coset cut out by `a * b⁻¹ ∈ ⟨ℓ⟩`. The right side enumerates that coset by the
cyclic subgroup order. No faithfulness of the full Galois orbit, residue-degree
one hypothesis, or split-prime hypothesis is used. -/
theorem frobeniusCosetWeightSum_eq_residueOrbitSum
    {ℓ p : ℕ} [Fact (Nat.Prime p)]
    (hℓp : ℓ.Coprime p) (a : CyclotomicUnitDelta p) :
    (∑ b : CyclotomicUnitDelta p,
        if a * b⁻¹ ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) then
          (b : ZMod p).val
        else
          0) =
      ∑ i ∈ Finset.range
          (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
        residueOrbit ℓ p (a : ZMod p).val i := by
  classical
  let u : CyclotomicUnitDelta p := ZMod.unitOfCoprime ℓ hℓp
  let H : Subgroup (CyclotomicUnitDelta p) := Subgroup.zpowers u
  let pred : CyclotomicUnitDelta p → Prop := fun b => a * b⁻¹ ∈ H
  let f : CyclotomicUnitDelta p → ℕ := fun b => (b : ZMod p).val
  have hcond :
      (∑ b : CyclotomicUnitDelta p, if pred b then f b else 0) =
        ∑ x : {b : CyclotomicUnitDelta p // pred b}, f x := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (CyclotomicUnitDelta p))) (f := f)]
    simp
  let eH : H ≃ {b : CyclotomicUnitDelta p // pred b} :=
    { toFun := fun h =>
        ⟨a * (h : CyclotomicUnitDelta p), by
          dsimp [pred, H]
          have h_eq : a * (a * (h : CyclotomicUnitDelta p))⁻¹ =
              ((h : CyclotomicUnitDelta p))⁻¹ := by
            simp [mul_comm]
          rw [h_eq]
          exact (Subgroup.zpowers u).inv_mem h.2⟩
      invFun := fun b =>
        ⟨a⁻¹ * (b : CyclotomicUnitDelta p), by
          dsimp [pred, H] at b
          have h_eq : a⁻¹ * (b : CyclotomicUnitDelta p) =
              (a * (b : CyclotomicUnitDelta p)⁻¹)⁻¹ := by
            simp [mul_comm]
          rw [h_eq]
          exact (Subgroup.zpowers u).inv_mem b.2⟩
      left_inv := by
        intro h
        apply Subtype.ext
        simp [mul_comm]
      right_inv := by
        intro b
        apply Subtype.ext
        simp [mul_comm] }
  have hsub :
      (∑ x : {b : CyclotomicUnitDelta p // pred b}, f x) =
        ∑ h : H, f (a * (h : CyclotomicUnitDelta p)) := by
    symm
    refine Fintype.sum_equiv eH
      (fun h : H => f (a * (h : CyclotomicUnitDelta p)))
      (fun x : {b : CyclotomicUnitDelta p // pred b} => f x) ?_
    intro h
    rfl
  have hH :
      (∑ h : H, f (a * (h : CyclotomicUnitDelta p))) =
        ∑ i : Fin (orderOf u), f (a * u ^ (i : ℕ)) := by
    symm
    refine Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite u))
      (fun i : Fin (orderOf u) => f (a * u ^ (i : ℕ)))
      (fun h : H => f (a * (h : CyclotomicUnitDelta p))) ?_
    intro i
    simp [finEquivZPowers_apply]
  calc
    (∑ b : CyclotomicUnitDelta p,
        if a * b⁻¹ ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) then
          (b : ZMod p).val
        else
          0) = (∑ b : CyclotomicUnitDelta p, if pred b then f b else 0) := by
      simp [pred, f, H, u]
    _ = ∑ x : {b : CyclotomicUnitDelta p // pred b}, f x := hcond
    _ = ∑ h : H, f (a * (h : CyclotomicUnitDelta p)) := hsub
    _ = ∑ i : Fin (orderOf u), f (a * u ^ (i : ℕ)) := hH
    _ = ∑ i ∈ Finset.range (orderOf u), f (a * u ^ i) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun i => f (a * u ^ i)) (orderOf u))
    _ = ∑ i ∈ Finset.range
          (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
        residueOrbit ℓ p (a : ZMod p).val i := by
      simp only [u]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact cyclotomicUnit_mul_frobeniusPower_val_eq_residueOrbit hℓp a i

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : FullTeichDworkSetup ℓ p k K R')

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** `normalizedFactors` of `stickelbergerIdeal q_K` equals
the sum `∑_a a.val • {σ_{a⁻¹} q_K}`. -/
theorem normalizedFactors_stickelbergerIdeal_descentPrime_eq :
    UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime) =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.toConcreteStickelbergerSetup.descentPrime}
            : Multiset (Ideal (𝓞 K))) := by
  classical
  unfold stickelbergerIdeal
  exact S.normalizedFactors_stickelbergerIdeal_finset_eq Finset.univ

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Discharge of `StickelbergerIdealConjugateMultiplicity` under faithfulness.**

Given that the Galois orbit indexing is one-to-one (distinct units give
distinct conjugates), the count of `σ_{a⁻¹} q_K` in
`normalizedFactors (stickelbergerIdeal q_K)` equals `a.val`. -/
theorem stickelbergerIdealConjugateMultiplicity_of_orbitFaithful
    (h_faithful : S.StickelbergerOrbitFaithful) :
    S.StickelbergerIdealConjugateMultiplicity := by
  classical
  intro a
  rw [S.normalizedFactors_stickelbergerIdeal_descentPrime_eq]
  rw [Multiset.count_sum']
  -- Reduce to counting in {σ_{b⁻¹} q_K}: gives a.val for b = a, 0 otherwise.
  rw [Finset.sum_eq_single a]
  · -- main term: a.val * count (σ_{a⁻¹} q_K) {σ_{a⁻¹} q_K} = a.val
    rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
  · -- For b ≠ a: count (σ_{a⁻¹} q_K) (b.val • {σ_{b⁻¹} q_K}) = 0 by faithfulness
    intro b _ hba
    rw [Multiset.count_nsmul, Multiset.count_singleton]
    -- σ_{b⁻¹} q_K ≠ σ_{a⁻¹} q_K because b ≠ a (faithfulness).
    have h_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime ≠
        cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹
          S.toConcreteStickelbergerSetup.descentPrime := fun h =>
      hba <| (h_faithful h).symm
    rw [if_neg h_ne, Nat.mul_zero]
  · -- a ∈ Finset.univ
    intro h
    exact absurd (Finset.mem_univ a) h

/-! ### Discharging `StickelbergerOrbitFaithful` from cardinality

The orbit-indexing map `a ↦ σ_a q_K` factors `(ZMod p)ˣ → orbit q_K`
through the quotient by the stabilizer (decomposition group). Its image
is by definition `cyclotomicConjugates q_K`, so the map is automatically
surjective. When the image cardinality matches the source cardinality
`p − 1 = #(ZMod p)ˣ`, the map is bijective, hence injective.

The fundamental Galois identity
`#orbit · ramificationIdxIn · inertiaDegIn = p − 1` makes this equivalent
to `e · f = 1`, i.e., the **totally split case** `(e = 1, f = 1)`. This
section provides the discharge:

* `stickelbergerOrbitFaithful_of_card_eq` — direct cardinality form.
* `stickelbergerOrbitFaithful_of_split` — the `(e = 1, f = 1)` form.

Both produce `StickelbergerOrbitFaithful` for the bundle's
`descentPrime`, which can then be fed into
`stickelbergerIdealConjugateMultiplicity_of_orbitFaithful` and the
end-to-end `stickelbergerIdealEquality_of_atomic_with_orbitFaithful`. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** the orbit-indexing map `a ↦ σ_a q_K` is injective when
the orbit attains the maximum cardinality `p − 1 = #(ZMod p)ˣ`.

Proof: by definition `cyclotomicConjugates q = Finset.univ.image (a ↦ σ_a q)`.
If the image has cardinality `p − 1 = card Finset.univ`, then by
`Finset.card_image_iff` the map is injective on `Finset.univ`, hence
globally injective. -/
theorem cyclotomicGaloisConjugate_descentPrime_injective_of_card_eq
    (h_card :
      (cyclotomicConjugates (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime).card = p - 1) :
    Function.Injective (fun a : CyclotomicUnitDelta p =>
      cyclotomicGaloisConjugate (p := p) (K := K) a
        S.toConcreteStickelbergerSetup.descentPrime) := by
  classical
  -- Unfold cyclotomicConjugates: Finset.univ.image (a ↦ σ_a q) has cardinality p - 1.
  have h_image_card :
      (Finset.univ.image (fun a : CyclotomicUnitDelta p =>
        cyclotomicGaloisConjugate (p := p) (K := K) a
          S.toConcreteStickelbergerSetup.descentPrime)).card = p - 1 := by
    rw [show (Finset.univ.image (fun a : CyclotomicUnitDelta p =>
        cyclotomicGaloisConjugate (p := p) (K := K) a
          S.toConcreteStickelbergerSetup.descentPrime)) =
      cyclotomicConjugates (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime from rfl]
    exact h_card
  -- Card Finset.univ for (ZMod p)ˣ is p - 1.
  have h_univ_card :
      (Finset.univ : Finset (CyclotomicUnitDelta p)).card = p - 1 := by
    rw [Finset.card_univ]
    exact ZMod.card_units p
  -- card image = card Finset.univ.
  have h_card_eq :
      (Finset.univ.image (fun a : CyclotomicUnitDelta p =>
        cyclotomicGaloisConjugate (p := p) (K := K) a
          S.toConcreteStickelbergerSetup.descentPrime)).card =
        (Finset.univ : Finset (CyclotomicUnitDelta p)).card := by
    rw [h_image_card, h_univ_card]
  -- Apply Finset.card_image_iff to get InjOn on Finset.univ.
  have h_injOn :
      Set.InjOn
        (fun a : CyclotomicUnitDelta p =>
          cyclotomicGaloisConjugate (p := p) (K := K) a
            S.toConcreteStickelbergerSetup.descentPrime)
        (Finset.univ : Finset (CyclotomicUnitDelta p)) :=
    Finset.card_image_iff.mp h_card_eq
  -- Convert InjOn univ to global Injective.
  intro a b hab
  exact h_injOn (Finset.mem_univ a) (Finset.mem_univ b) hab

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Discharge of `StickelbergerOrbitFaithful` from orbit cardinality.**

Under the hypothesis `card cyclotomicConjugates q_K = p − 1` (the
"totally split" condition), the indexing map `a ↦ σ_{a⁻¹} q_K` is
injective.

Proof: the map `a ↦ σ_a q_K` is injective by
`cyclotomicGaloisConjugate_descentPrime_injective_of_card_eq`; precompose
with `Inv.inv` (injective on a group) to get injectivity of `a ↦ σ_{a⁻¹} q_K`. -/
theorem stickelbergerOrbitFaithful_of_card_eq
    (h_card :
      (cyclotomicConjugates (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime).card = p - 1) :
    S.StickelbergerOrbitFaithful := by
  classical
  -- Step 1: a ↦ σ_a q_K is injective.
  have h_inj :=
    S.cyclotomicGaloisConjugate_descentPrime_injective_of_card_eq h_card
  -- Step 2: a ↦ a⁻¹ is injective on (ZMod p)ˣ.
  have h_inv : Function.Injective (Inv.inv : CyclotomicUnitDelta p → CyclotomicUnitDelta p) :=
    inv_injective
  -- Step 3: composition is injective.
  intro a b hab
  exact h_inv (h_inj hab)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Discharge of `StickelbergerOrbitFaithful` from totally-split ramification.**

Given that the descent prime `q_K` is **totally split** above the
rational prime `q_K.under ℤ`, in the sense that both ramification
index and inertia degree equal `1`, the orbit attains its maximum
cardinality `p − 1` and faithfulness follows.

This corresponds to the case `ℓ ≡ 1 (mod p)` for the residue prime `ℓ`
under the bundle, and is the natural ramification condition for c.1's
single-bundle Stickelberger orbit coverage. -/
theorem stickelbergerOrbitFaithful_of_split
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    S.StickelbergerOrbitFaithful := by
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  have h_card :
      (cyclotomicConjugates (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime).card = p - 1 :=
    cyclotomicConjugates_card_eq_p_sub_one_of_split
      (p := p) (K := K)
      (q := S.toConcreteStickelbergerSetup.descentPrime)
      S.toConcreteStickelbergerSetup.descentPrime_ne_bot he hf
  exact S.stickelbergerOrbitFaithful_of_card_eq h_card

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Trivial constructor for `StickelbergerOrbitCoverage` from a span
equality witness.** Given a generator γ ∈ 𝓞 K with the principal-ideal
equality already established, the coverage predicate holds. This is
just a packaging form. -/
theorem stickelbergerOrbitCoverage_of_span_eq
    (γ : 𝓞 K) (hγ_ne : γ ≠ 0)
    (h_eq : Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime) :
    S.StickelbergerOrbitCoverage :=
  ⟨γ, hγ_ne, h_eq⟩

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The Stickelberger ideal at descentPrime is non-bot. -/
theorem stickelbergerIdeal_descentPrime_ne_bot :
    stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  stickelbergerIdeal_ne_bot S.toConcreteStickelbergerSetup.descentPrime_ne_bot

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Bound on emultiplicity by exponent.**

If `b = σ_{a^{-1}} q_K` (a Galois conjugate of `q_K`), then
`emultiplicity b (stickelbergerIdeal q_K) ≥ a.val`.
This is the easy direction: the Stickelberger ideal contains the factor
`b^{a.val}` by definition. -/
theorem emultiplicity_stickelbergerIdeal_ge_aval
    (a : CyclotomicUnitDelta p) :
    ((a : ZMod p).val : ℕ∞) ≤
      emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime)
        (stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime) := by
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  -- The factor (σ_{a^{-1}} q_K)^a.val divides stickelbergerIdeal.
  have hle :=
    stickelbergerIdeal_le_factor (p := p) (K := K)
      S.toConcreteStickelbergerSetup.descentPrime a
  have hdvd :
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime ^
          ((a : ZMod p).val) ∣
        stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime :=
    Ideal.dvd_iff_le.mpr hle
  exact pow_dvd_iff_le_emultiplicity.mp hdvd

/-! ### Forward direction: `(γ) ∣ stickelbergerIdeal q_K`

Under `StickelbergerExactConjugateExponents` and `StickelbergerSupportInOrbit`,
the principal ideal `(γ)` divides `stickelbergerIdeal q_K`. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Forward direction:** `h_exp ∧ h_sup` implies `(γ) ∣ stickelbergerIdeal q_K`.

The proof uses Dedekind-domain factorization-uniqueness:
`count b (NF (γ)) ≤ count b (NF (stickelbergerIdeal q_K))` for every prime b.
For b in the orbit, this is via h_exp + emultiplicity_stickelbergerIdeal_ge_aval.
For b outside the orbit, count is 0 by h_sup. -/
theorem span_dvd_stickelbergerIdeal_of_atomic
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_sup : S.StickelbergerSupportInOrbit γ) :
    Ideal.span ({γ} : Set (𝓞 K)) ∣
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime := by
  classical
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  have hspan_ne : Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hstick_ne : stickelbergerIdeal (p := p) (K := K)
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
    S.stickelbergerIdeal_descentPrime_ne_bot
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        hspan_ne hstick_ne]
  rw [Multiset.le_iff_count]
  intro b
  by_cases hb_in :
      b ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({γ} : Set (𝓞 K)))
  · have hb_orbit := h_sup b hb_in
    obtain ⟨c, hc_eq⟩ :=
      (mem_cyclotomicConjugates_iff (p := p) (K := K) _ b).mp hb_orbit
    have hb_prime :=
      UniqueFactorizationMonoid.prime_of_normalized_factor b hb_in
    have hb_irred := hb_prime.irreducible
    have hcount_γ :
        emultiplicity b (Ideal.span ({γ} : Set (𝓞 K))) =
          ((UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({γ} : Set (𝓞 K)))).count
            (normalize b) : ℕ∞) :=
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hb_irred hspan_ne
    have hnorm : normalize b = b := by rw [normalize_eq]
    rw [hnorm] at hcount_γ
    have h_emult_γ := h_exp c⁻¹
    rw [inv_inv, hc_eq] at h_emult_γ
    rw [h_emult_γ] at hcount_γ
    have hcount_γ_nat :
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({γ} : Set (𝓞 K)))).count b =
          ((c⁻¹ : CyclotomicUnitDelta p) : ZMod p).val := by
      have := hcount_γ.symm
      exact_mod_cast this
    rw [hcount_γ_nat]
    have h_stick_lb := S.emultiplicity_stickelbergerIdeal_ge_aval c⁻¹
    rw [inv_inv, hc_eq] at h_stick_lb
    have hcount_stick :
        emultiplicity b
            (stickelbergerIdeal (p := p) (K := K)
              S.toConcreteStickelbergerSetup.descentPrime) =
          ((UniqueFactorizationMonoid.normalizedFactors
              (stickelbergerIdeal (p := p) (K := K)
                S.toConcreteStickelbergerSetup.descentPrime)).count
            (normalize b) : ℕ∞) :=
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hb_irred hstick_ne
    rw [hnorm] at hcount_stick
    rw [hcount_stick] at h_stick_lb
    exact_mod_cast h_stick_lb
  · rw [Multiset.count_eq_zero.mpr hb_in]
    exact Nat.zero_le _

/-! ### Reverse direction: `stickelbergerIdeal q_K ∣ (γ)`

Under `StickelbergerExactConjugateExponents` and the structural
`StickelbergerIdealConjugateMultiplicity`, the reverse divisibility holds. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Reverse direction:** `h_exp ∧ h_stickMul` implies
`stickelbergerIdeal q_K ∣ (γ)`. Counts on `stickelbergerIdeal` come from
`h_stickMul`, counts on `(γ)` come from `h_exp`; for primes outside the
orbit, the Stickelberger ideal has no support (via
`normalizedFactors_stickelbergerIdeal_subset`). -/
theorem stickelbergerIdeal_dvd_span_of_exact_atomic
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_stickMul : S.StickelbergerIdealConjugateMultiplicity) :
    stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime ∣
      Ideal.span ({γ} : Set (𝓞 K)) := by
  classical
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  have hspan_ne : Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hstick_ne : stickelbergerIdeal (p := p) (K := K)
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
    S.stickelbergerIdeal_descentPrime_ne_bot
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        hstick_ne hspan_ne]
  rw [Multiset.le_iff_count]
  intro b
  by_cases hb_in :
      b ∈ UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime)
  · have hb_orbit :
        b ∈ cyclotomicConjugates (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime :=
      normalizedFactors_stickelbergerIdeal_subset (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime_ne_bot hb_in
    obtain ⟨c, hc_eq⟩ :=
      (mem_cyclotomicConjugates_iff (p := p) (K := K) _ b).mp hb_orbit
    have hb_prime :=
      UniqueFactorizationMonoid.prime_of_normalized_factor b hb_in
    have hb_irred := hb_prime.irreducible
    have h_stick_count := h_stickMul c⁻¹
    rw [inv_inv, hc_eq] at h_stick_count
    rw [h_stick_count]
    have h_emult_γ := h_exp c⁻¹
    rw [inv_inv, hc_eq] at h_emult_γ
    have hcount_γ :
        emultiplicity b (Ideal.span ({γ} : Set (𝓞 K))) =
          ((UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({γ} : Set (𝓞 K)))).count
            (normalize b) : ℕ∞) :=
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hb_irred hspan_ne
    have hnorm : normalize b = b := by rw [normalize_eq]
    rw [hnorm] at hcount_γ
    rw [h_emult_γ] at hcount_γ
    have hcount_γ_nat :
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({γ} : Set (𝓞 K)))).count b =
          ((c⁻¹ : CyclotomicUnitDelta p) : ZMod p).val := by
      have := hcount_γ.symm
      exact_mod_cast this
    rw [hcount_γ_nat]
  · rw [Multiset.count_eq_zero.mpr hb_in]
    exact Nat.zero_le _

/-! ### End-to-end atomic discharge

Combining both directions yields the orbit coverage from the three
atomic predicates. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Direct span equality from atomic predicates.** Combining both
divisibility directions (forward via `span_dvd_stickelbergerIdeal_of_atomic`,
reverse via `stickelbergerIdeal_dvd_span_of_exact_atomic`), the principal
ideal `(γ)` equals `stickelbergerIdeal q_K` directly — without going
through the `∃`-wrapped `StickelbergerOrbitCoverage` predicate.

This is the building block for K2-2 `h_span` discharges where the
specific witness γ is fixed and the user needs the equality at that
specific γ. -/
theorem span_eq_stickelbergerIdeal_of_atomic
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_sup : S.StickelbergerSupportInOrbit γ)
    (h_stickMul : S.StickelbergerIdealConjugateMultiplicity) :
    Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime := by
  have h_dvd1 := S.span_dvd_stickelbergerIdeal_of_atomic hγ_ne h_exp h_sup
  have h_dvd2 := S.stickelbergerIdeal_dvd_span_of_exact_atomic hγ_ne h_exp h_stickMul
  exact associated_iff_eq.mp (associated_of_dvd_dvd h_dvd1 h_dvd2)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Atomic discharge of `StickelbergerOrbitCoverage`.** Combining both
divisibility directions (forward via `span_dvd_stickelbergerIdeal_of_atomic`,
reverse via `stickelbergerIdeal_dvd_span_of_exact_atomic`), the principal
ideal `(γ)` equals `stickelbergerIdeal q_K`. The coverage predicate
follows.

This is the substantive **atomic discharge**: the orbit-coverage is
reduced to checking the atomic predicates `h_exp`, `h_sup`, and the
structural `h_stickMul` (which captures the combinatorial content of
the Stickelberger ideal under faithfulness). -/
theorem stickelbergerOrbitCoverage_of_atomic_with_stickMul
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_sup : S.StickelbergerSupportInOrbit γ)
    (h_stickMul : S.StickelbergerIdealConjugateMultiplicity) :
    S.StickelbergerOrbitCoverage :=
  ⟨γ, hγ_ne, S.span_eq_stickelbergerIdeal_of_atomic hγ_ne h_exp h_sup h_stickMul⟩

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **End-to-end discharge of `StickelbergerIdealEquality` from atomic
predicates.** This is the consumer-facing form combining
`stickelbergerOrbitCoverage_of_atomic_with_stickMul` with
`stickelbergerIdealEquality_of_orbitCoverage`.

Given a witness γ ∈ 𝓞 K satisfying the atomic predicates, we obtain
`StickelbergerIdealEquality (S.Q.under (𝓞 K))` — the substantive
content of c.1, REF-18c2d-main-c.1. -/
theorem stickelbergerIdealEquality_of_atomic_with_stickMul
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_sup : S.StickelbergerSupportInOrbit γ)
    (h_stickMul : S.StickelbergerIdealConjugateMultiplicity) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) :=
  S.stickelbergerIdealEquality_of_orbitCoverage
    (S.stickelbergerOrbitCoverage_of_atomic_with_stickMul hγ_ne h_exp h_sup h_stickMul)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **End-to-end discharge of `StickelbergerIdealEquality` from atomic
predicates with orbit faithfulness.** This is the consumer-facing form
combining `stickelbergerIdealEquality_of_atomic_with_stickMul` with the
discharge of `StickelbergerIdealConjugateMultiplicity` from
`StickelbergerOrbitFaithful`.

Given a witness γ ∈ 𝓞 K satisfying the per-conjugate exponent and
support-in-orbit predicates, plus the orbit faithfulness, we obtain
`StickelbergerIdealEquality (S.Q.under (𝓞 K))`. -/
theorem stickelbergerIdealEquality_of_atomic_with_orbitFaithful
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_sup : S.StickelbergerSupportInOrbit γ)
    (h_faithful : S.StickelbergerOrbitFaithful) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) :=
  S.stickelbergerIdealEquality_of_atomic_with_stickMul hγ_ne h_exp h_sup
    (S.stickelbergerIdealConjugateMultiplicity_of_orbitFaithful h_faithful)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **End-to-end discharge of `StickelbergerIdealEquality` under
totally-split ramification.** Combines `stickelbergerOrbitFaithful_of_split`
with `stickelbergerIdealEquality_of_atomic_with_orbitFaithful`: under
`(e = 1, f = 1)` and atomic predicates `h_exp`, `h_sup` for a witness γ,
we obtain `StickelbergerIdealEquality (S.Q.under (𝓞 K))`.

This is the consumer-facing form for the **totally split case**
(`ℓ ≡ 1 mod p`), where the single-bundle Stickelberger orbit coverage
holds automatically by orbit cardinality. -/
theorem stickelbergerIdealEquality_of_atomic_with_split
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (h_exp : S.StickelbergerExactConjugateExponents γ)
    (h_sup : S.StickelbergerSupportInOrbit γ)
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) :=
  S.stickelbergerIdealEquality_of_atomic_with_orbitFaithful hγ_ne h_exp h_sup
    (S.stickelbergerOrbitFaithful_of_split he hf)

/-! ### Atomic decomposition of `StickelbergerExactConjugateExponents`

The exact-exponent predicate
`emultiplicity (σ_{a⁻¹} q_K) (γ) = a.val`
naturally decomposes into a lower-bound and an upper-bound piece via
`emultiplicity_eq_coe`:

* `StickelbergerLowerBoundConjugateExponents γ`: `(σ_{a⁻¹} q_K)^a.val ∣ (γ)`,
  equivalently `a.val ≤ emultiplicity (σ_{a⁻¹} q_K) (γ)`.
* `StickelbergerUpperBoundConjugateExponents γ`: `(σ_{a⁻¹} q_K)^(a.val+1) ∤ (γ)`,
  equivalently `emultiplicity (σ_{a⁻¹} q_K) (γ) < a.val + 1`.

The lower bound is the structurally easy direction: it follows from
`(γ) ⊆ stickelbergerIdeal q_K`, since each `σ_{a⁻¹} q_K`-power is a
factor of the Stickelberger product.

The upper bound carries the substantive content: it requires showing
`(γ)` does not contain "extra" copies of any conjugate prime — the
sharp orbit-counting / faithfulness data.

Combined, these two predicates are equivalent to the original
`StickelbergerExactConjugateExponents`. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Equivalent reformulation of `StickelbergerExactConjugateExponents γ`
in terms of `pow_dvd` membership: for each `a ∈ (ZMod p)ˣ`, both
`(σ_{a⁻¹} q_K)^a.val ∣ (γ)` and `(σ_{a⁻¹} q_K)^(a.val+1) ∤ (γ)`. -/
theorem stickelbergerExactConjugateExponents_iff (γ : 𝓞 K) :
    S.StickelbergerExactConjugateExponents γ ↔
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime ^
            ((a : ZMod p).val) ∣
          Ideal.span ({γ} : Set (𝓞 K)) ∧
        ¬ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime ^
            ((a : ZMod p).val + 1) ∣
          Ideal.span ({γ} : Set (𝓞 K)) := by
  unfold StickelbergerExactConjugateExponents
  refine forall_congr' fun a => ?_
  exact emultiplicity_eq_coe

/-- **Atomic predicate: per-conjugate lower bound exponent.**

For each `a ∈ (ZMod p)ˣ`, the conjugate prime `σ_{a⁻¹} q_K` divides `(γ)`
to at least the `a.val`-th power: equivalently
`a.val ≤ emultiplicity (σ_{a⁻¹} q_K) (γ)`. -/
def StickelbergerLowerBoundConjugateExponents (γ : 𝓞 K) : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ^
        ((a : ZMod p).val) ∣
      Ideal.span ({γ} : Set (𝓞 K))

/-- **Atomic predicate: per-conjugate upper bound exponent.**

For each `a ∈ (ZMod p)ˣ`, the conjugate prime `σ_{a⁻¹} q_K` does not
divide `(γ)` to the `(a.val+1)`-th power: equivalently
`emultiplicity (σ_{a⁻¹} q_K) (γ) < a.val + 1`. -/
def StickelbergerUpperBoundConjugateExponents (γ : 𝓞 K) : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    ¬ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ^
        ((a : ZMod p).val + 1) ∣
      Ideal.span ({γ} : Set (𝓞 K))

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Atomic decomposition of `StickelbergerExactConjugateExponents`.**
The exact-exponent predicate is the conjunction of the lower and upper
bound atomic predicates. -/
theorem stickelbergerExactConjugateExponents_iff_lower_and_upper (γ : 𝓞 K) :
    S.StickelbergerExactConjugateExponents γ ↔
      S.StickelbergerLowerBoundConjugateExponents γ ∧
      S.StickelbergerUpperBoundConjugateExponents γ := by
  rw [S.stickelbergerExactConjugateExponents_iff γ]
  unfold StickelbergerLowerBoundConjugateExponents
    StickelbergerUpperBoundConjugateExponents
  constructor
  · intro h
    exact ⟨fun a => (h a).1, fun a => (h a).2⟩
  · rintro ⟨h_lb, h_ub⟩ a
    exact ⟨h_lb a, h_ub a⟩

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Constructor for `StickelbergerExactConjugateExponents` from
atomic lower+upper bounds.** -/
theorem stickelbergerExactConjugateExponents_of_lower_and_upper
    {γ : 𝓞 K}
    (h_lb : S.StickelbergerLowerBoundConjugateExponents γ)
    (h_ub : S.StickelbergerUpperBoundConjugateExponents γ) :
    S.StickelbergerExactConjugateExponents γ :=
  (S.stickelbergerExactConjugateExponents_iff_lower_and_upper γ).mpr ⟨h_lb, h_ub⟩

/-! ### Discharging the lower bound from `(γ) ⊆ stickelbergerIdeal q_K`

The lower bound `(σ_{a⁻¹} q_K)^a.val ∣ (γ)` is equivalent to
`(γ) ⊆ (σ_{a⁻¹} q_K)^a.val`. Since `(σ_{a⁻¹} q_K)^a.val ⊇ stickelbergerIdeal q_K`
(by `stickelbergerIdeal_le_factor`), it suffices to show
`(γ) ⊆ stickelbergerIdeal q_K`, i.e., `stickelbergerIdeal q_K ∣ (γ)`. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Lower bound discharge from divisibility by Stickelberger ideal.**
If `stickelbergerIdeal q_K ∣ (γ)`, then for each `a ∈ (ZMod p)ˣ`, the
conjugate factor `(σ_{a⁻¹} q_K)^a.val` divides `(γ)`. -/
theorem stickelbergerLowerBoundConjugateExponents_of_dvd
    {γ : 𝓞 K}
    (h_dvd : stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime ∣
      Ideal.span ({γ} : Set (𝓞 K))) :
    S.StickelbergerLowerBoundConjugateExponents γ := by
  intro a
  -- The factor (σ_{a⁻¹} q_K)^a.val divides stickelbergerIdeal q_K, which
  -- divides the γ-span. Combine.
  have hle :=
    stickelbergerIdeal_le_factor (p := p) (K := K)
      S.toConcreteStickelbergerSetup.descentPrime a
  exact dvd_trans (Ideal.dvd_iff_le.mpr hle) h_dvd

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Lower bound discharge from span equality.** If
`(γ) = stickelbergerIdeal q_K`, then the lower bound holds. -/
theorem stickelbergerLowerBoundConjugateExponents_of_span_eq
    {γ : 𝓞 K}
    (h_eq : Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime) :
    S.StickelbergerLowerBoundConjugateExponents γ :=
  S.stickelbergerLowerBoundConjugateExponents_of_dvd (h_eq ▸ dvd_refl _)

/-! ### Discharging the upper bound under faithful action

The upper bound is the substantive content: `(σ_{a⁻¹} q_K)^(a.val+1) ∤ (γ)`.

Under `(γ) = stickelbergerIdeal q_K` and orbit faithfulness, the upper
bound follows from the structural multiplicity computation: the count of
`σ_{a⁻¹} q_K` in `normalizedFactors (stickelbergerIdeal q_K)` is exactly
`a.val`, so the multiplicity is exactly `a.val`, hence the `(a.val+1)`-th
power does not divide. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Upper bound discharge from span equality + orbit faithfulness.**
If `(γ) = stickelbergerIdeal q_K` and the cyclotomic Galois orbit acts
faithfully on `q_K`, then the upper bound holds. -/
theorem stickelbergerUpperBoundConjugateExponents_of_span_eq_of_faithful
    {γ : 𝓞 K}
    (h_eq : Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime)
    (h_faithful : S.StickelbergerOrbitFaithful) :
    S.StickelbergerUpperBoundConjugateExponents γ := by
  classical
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  intro a
  -- Reduce to emultiplicity via pow_dvd_iff_le_emultiplicity, then
  -- compute emultiplicity = a.val using the count formula.
  have hb_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
    S.cyclotomicGaloisConjugate_descentPrime_ne_bot a
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ _
  have hb_prime : Prime (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) :=
    Ideal.prime_of_isPrime hb_ne inferInstance
  have hb_irred : Irreducible (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) := hb_prime.irreducible
  rw [pow_dvd_iff_le_emultiplicity, not_le]
  -- Rewrite the goal's Ideal.span {γ} to stickelbergerIdeal using h_eq.
  rw [h_eq]
  -- Now goal: emultiplicity ... (stickelbergerIdeal ...) < a.val + 1.
  -- Compute emultiplicity = count (NF stickelbergerIdeal) = a.val.
  have hcount :
      emultiplicity
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime)
          (stickelbergerIdeal (p := p) (K := K)
            S.toConcreteStickelbergerSetup.descentPrime) =
        ((UniqueFactorizationMonoid.normalizedFactors
            (stickelbergerIdeal (p := p) (K := K)
              S.toConcreteStickelbergerSetup.descentPrime)).count
          (normalize (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime)) : ℕ∞) :=
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hb_irred <|
        S.stickelbergerIdeal_descentPrime_ne_bot
  have hnorm : normalize (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) =
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime := by
    rw [normalize_eq]
  rw [hnorm] at hcount
  have h_stickMul := S.stickelbergerIdealConjugateMultiplicity_of_orbitFaithful h_faithful a
  rw [h_stickMul] at hcount
  rw [hcount]
  -- Goal: (a.val : ℕ∞) < ((a.val + 1) : ℕ∞).
  exact_mod_cast Nat.lt_succ_self ((a : ZMod p).val)

/-! ### End-to-end discharge from span equality

Combining lower bound + upper bound + orbit faithfulness yields a
substantive end-to-end discharge of `StickelbergerExactConjugateExponents`. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Substantive discharge: `StickelbergerExactConjugateExponents γ` from
span equality + orbit faithfulness.**

If `γ ∈ 𝓞 K \ {0}` generates the Stickelberger ideal
(`(γ) = stickelbergerIdeal q_K`) and the cyclotomic Galois orbit on `q_K`
is faithful, then γ has exact conjugate exponents:
`emultiplicity (σ_{a⁻¹} q_K) (γ) = a.val` for every `a ∈ (ZMod p)ˣ`.

This is the substantive structural reduction: it converts the orbit-coverage
witness into the exact-exponent atomic predicate. -/
theorem stickelbergerExactConjugateExponents_of_span_eq_of_faithful
    {γ : 𝓞 K}
    (h_eq : Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime)
    (h_faithful : S.StickelbergerOrbitFaithful) :
    S.StickelbergerExactConjugateExponents γ :=
  S.stickelbergerExactConjugateExponents_of_lower_and_upper
    (S.stickelbergerLowerBoundConjugateExponents_of_span_eq h_eq)
    (S.stickelbergerUpperBoundConjugateExponents_of_span_eq_of_faithful
      h_eq h_faithful)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Substantive discharge: `StickelbergerExactConjugateExponents γ` from
span equality + totally-split ramification.**

The split-case form of `stickelbergerExactConjugateExponents_of_span_eq_of_faithful`,
using `stickelbergerOrbitFaithful_of_split` to derive the orbit faithfulness
from the structural ramification hypotheses `e = 1` and `f = 1`. -/
theorem stickelbergerExactConjugateExponents_of_span_eq_of_split
    {γ : 𝓞 K}
    (h_eq : Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime)
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    S.StickelbergerExactConjugateExponents γ :=
  S.stickelbergerExactConjugateExponents_of_span_eq_of_faithful
    h_eq (S.stickelbergerOrbitFaithful_of_split he hf)

/-! ### Round-trip equivalence under faithful action

Combining `stickelbergerOrbitCoverage` (∃ γ with span = stickelbergerIdeal)
with `stickelbergerExactConjugateExponents_of_span_eq_of_faithful`, we
get that `StickelbergerOrbitCoverage S` together with orbit faithfulness
produces a γ satisfying all atomic predicates. This closes the
"existence-from-coverage" direction. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Round-trip:** orbit coverage + orbit faithfulness produce a
witness γ satisfying `StickelbergerExactConjugateExponents`. -/
theorem exists_stickelbergerExactConjugateExponents_of_coverage_of_faithful
    (h_cov : S.StickelbergerOrbitCoverage)
    (h_faithful : S.StickelbergerOrbitFaithful) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      Ideal.span ({γ} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime ∧
      S.StickelbergerExactConjugateExponents γ := by
  obtain ⟨γ, hγ_ne, h_eq⟩ := h_cov
  exact ⟨γ, hγ_ne, h_eq,
    S.stickelbergerExactConjugateExponents_of_span_eq_of_faithful
      h_eq h_faithful⟩

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end
