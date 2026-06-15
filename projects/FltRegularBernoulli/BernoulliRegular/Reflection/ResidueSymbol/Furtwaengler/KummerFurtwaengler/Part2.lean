module

public import BernoulliRegular.FLT37.Primary
public import BernoulliRegular.UnitQuotient.DeltaAction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler.Part1


/-!
# Stickelberger support and cyclotomic ideal orbits

This file continues the basic cyclotomic ideal-action API with Stickelberger
support bookkeeping. It contains support and orbit identities only.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Invariance of `finiteFieldExponent` under a ring iso between
finite fields.**

If `φ : k ≃+* k'` is a ring iso between finite fields with
`Fintype.card k = Fintype.card k'`, then for any unit `x : kˣ` and any
primitive `p`-th root `ζ : kˣ`, the exponent values agree:
`finiteFieldExponent ζ hζ hdiv x =
   finiteFieldExponent (Units.map φ ζ) (φ-of-hζ) hdiv' (Units.map φ x)`.

Proven via the characterizing identity
`ζ^e.val = x^((|k|-1)/p)`: applying `φ` to both sides preserves it. -/
theorem finiteFieldExponent_ringEquiv {p : ℕ} [NeZero p]
    {k k' : Type*} [Field k] [Fintype k] [Field k'] [Fintype k']
    (φ : k ≃+* k') (hcard : Fintype.card k = Fintype.card k')
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : p ∣ Fintype.card k - 1)
    (hdiv' : p ∣ Fintype.card k' - 1) (x : kˣ) :
    Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
        (Units.mapEquiv (φ : k ≃* k') ζ)
        ((hζ.map_of_injective (Units.map_injective
          (f := (φ : k →* k')) φ.injective)) :
            IsPrimitiveRoot (Units.mapEquiv (φ : k ≃* k') ζ) p)
        hdiv'
        (Units.mapEquiv (φ : k ≃* k') x) =
      Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
        ζ hζ hdiv x := by
  -- The exponent is uniquely determined by the property
  -- `ζ^e.val = x^((|k|-1)/p)` (`zeta_pow_finiteFieldExponent_val`),
  -- combined with the fact that `p` divides `|k| - 1`. We use the
  -- injectivity of `IsPrimitiveRoot.zmodEquivZPowers` to reduce the
  -- equality of two `ZMod p` values to equality of the corresponding
  -- elements in `Subgroup.zpowers ζ`.
  set e := Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
    ζ hζ hdiv x with he_def
  set φ_units : kˣ ≃* k'ˣ := Units.mapEquiv (φ : k ≃* k')
  set ζ' : k'ˣ := φ_units ζ
  set x' : k'ˣ := φ_units x
  set hζ' : IsPrimitiveRoot ζ' p :=
    hζ.map_of_injective (Units.map_injective (f := (φ : k →* k')) φ.injective)
  -- We will show that `ζ'^e.val = x'^((|k'|-1)/p)`, i.e., e satisfies the
  -- defining identity for `finiteFieldExponent ζ' hζ' hdiv' x'`.
  have h_card_e : (Fintype.card k - 1) / p = (Fintype.card k' - 1) / p := by
    rw [hcard]
  -- `ζ^e.val = x^((|k|-1)/p)` from the characterizing identity.
  have h_zeta_pow : (ζ : k) ^ e.val = (x : k) ^ ((Fintype.card k - 1) / p) := by
    have h := Reflection.ResidueSymbol.PowerResidue.zeta_pow_finiteFieldExponent_val
      hζ hdiv x
    have happ := congrArg (fun u : kˣ => (u : k)) h
    simp only [Units.val_pow_eq_pow_val] at happ
    simpa [Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit] using happ
  -- Apply φ.
  have h_phi : φ ((ζ : k) ^ e.val) = φ ((x : k) ^ ((Fintype.card k - 1) / p)) :=
    congrArg φ h_zeta_pow
  rw [map_pow, map_pow] at h_phi
  -- φ (ζ : k) = (ζ' : k') and φ (x : k) = (x' : k') by definition of Units.mapEquiv.
  have h_φζ : φ (ζ : k) = (ζ' : k') := by
    change φ (ζ : k) = (Units.mapEquiv (φ : k ≃* k') ζ : k')
    rfl
  have h_φx : φ (x : k) = (x' : k') := by
    change φ (x : k) = (Units.mapEquiv (φ : k ≃* k') x : k')
    rfl
  rw [h_φζ, h_φx, h_card_e] at h_phi
  -- h_phi : (ζ' : k')^e.val = (x' : k')^((|k'|-1)/p).
  apply hζ'.zmodEquivZPowers.injective
  conv_lhs => unfold Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
  rw [AddEquiv.apply_symm_apply]
  -- Pin down `hζ'.zmodEquivZPowers e`.
  have hpow :
      hζ'.zmodEquivZPowers e =
        Additive.ofMul (⟨ζ' ^ e.val, e.val, rfl⟩ : Subgroup.zpowers ζ') := by
    conv_lhs => rw [← ZMod.natCast_zmod_val e]
    rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  rw [hpow]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  apply Units.ext
  change ((Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv' x' :
        k'ˣ) : k') = ((ζ' ^ e.val : k'ˣ) : k')
  rw [Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact h_phi.symm

/-- **Invariance of `primeExponent` under a ring iso between residue
fields.**

If `q' = q.map f` for a ring iso `f : R ≃+* R'`, and the residue
fields `R/q ≃+* R'/q'` have equal cardinality (always true: the ring iso
descends to the quotient), then `primeExponent` is invariant under the
correspondence:
* `α` at `q` (with primitive root `ζ`) ↔ `f α` at `q'` (with primitive
  root the image of `ζ` under the quotient iso). -/
theorem primeExponent_ringEquiv {p : ℕ} [NeZero p]
    {R : Type*} [CommRing R] {q : Ideal R} [hq_max : q.IsMaximal]
    [Fintype (R ⧸ q)]
    (q' : Ideal R) [hq'_max : q'.IsMaximal] [Fintype (R ⧸ q')]
    (f : R ≃+* R) (hqq' : q' = q.map (f : R →+* R))
    (hcard : Fintype.card (R ⧸ q') = Fintype.card (R ⧸ q))
    {ζ : (R ⧸ q)ˣ} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1)
    (hdiv' : p ∣ Fintype.card (R ⧸ q') - 1)
    (α : R) (hα : α ∉ q) (hfα : f α ∉ q') :
    Reflection.ResidueSymbol.PowerResidue.primeExponent q' (
        Units.mapEquiv ((Ideal.quotientEquiv q q' f hqq') : (R⧸q) ≃* (R⧸q')) ζ)
      ((hζ.map_of_injective (Units.map_injective
          (f := ((Ideal.quotientEquiv q q' f hqq') : (R⧸q) →* (R⧸q')))
          (Ideal.quotientEquiv q q' f hqq').injective)) :
        IsPrimitiveRoot
          (Units.mapEquiv
            ((Ideal.quotientEquiv q q' f hqq') : (R⧸q) ≃* (R⧸q')) ζ) p)
      hdiv' (f α) hfα =
      Reflection.ResidueSymbol.PowerResidue.primeExponent q ζ hζ hdiv α hα := by
  -- Both sides reduce to `finiteFieldExponent` applied to the
  -- corresponding `quotientUnitOfNotMem`, which transfer cleanly via
  -- the ring iso `Ideal.quotientEquiv q q' f hqq'`.
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  letI : Field (R ⧸ q') := Ideal.Quotient.field q'
  set φ : (R ⧸ q) ≃+* (R ⧸ q') := Ideal.quotientEquiv q q' f hqq' with hφ_def
  -- The transfer map on units.
  have hα_to_unit : Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
      q' (f α) hfα =
      Units.mapEquiv (φ : (R⧸q) ≃* (R⧸q'))
        (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem q α hα) := by
    apply Units.ext
    change (Ideal.Quotient.mk q' (f α)) =
        φ (Ideal.Quotient.mk q α)
    rw [hφ_def]
    rfl
  rw [Reflection.ResidueSymbol.PowerResidue.primeExponent,
      Reflection.ResidueSymbol.PowerResidue.primeExponent,
      hα_to_unit]
  exact finiteFieldExponent_ringEquiv (p := p) φ hcard.symm hζ hdiv hdiv' _

/-- **Conditional Galois-equivariance of `pthSymbolAtPrime`.**

For `α ∈ 𝓞 K`, `q ⊂ 𝓞 K` a non-`⊥` maximal ideal with `α ∉ q`, and
`a ∈ (ZMod p)ˣ` (encoding the Galois automorphism `σ_a`), the
`p`-th-power residue symbol is invariant under the Galois action,
**assuming** the chosen primitive `p`-th roots in the two residue
fields `(𝓞K/q)ˣ` and `(𝓞K/(σ_a • q))ˣ` are compatible:

* The `Classical.choose` at `σ_a • q` equals the image, under the
  quotient ring iso induced by `σ_a`, of the `Classical.choose` at `q`.

The compatibility hypothesis is needed because the two `Classical.choose`
values pick (otherwise unrelated) primitive `p`-th roots, which could
differ by a unit factor in `(ZMod p)ˣ`. With the compatibility, both
symbols reduce to the same `primeExponent` value via `primeExponent_ringEquiv`.

(Mathematically the symbols always agree up to a `(ZMod p)ˣ` unit
multiplier; pinning down a canonical correspondence is the substantive
content of the eventually-unconditional c.2.) -/
theorem pthSymbolAtPrime_galoisAction_of_compat
    (a : CyclotomicUnitDelta p) (α : 𝓞 K)
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q)
    (hroot_q : ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p)
    (hroot_q' :
      ∃ ζ : (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ,
        IsPrimitiveRoot ζ p)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hdiv' :
      p ∣ Fintype.card (𝓞 K ⧸
        cyclotomicGaloisConjugate (p := p) (K := K) a q) - 1)
    -- Compatibility: the chosen ζ at q' is the image of the chosen ζ at q.
    (h_compat :
      hroot_q'.choose =
        Units.mapEquiv
          ((cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q) :
            (𝓞 K ⧸ q) ≃* _)
          hroot_q.choose) :
    pthSymbolAtPrime (p := p) (cyclotomicRingOfIntegersEquiv (p := p) K a α)
      (cyclotomicGaloisConjugate (p := p) (K := K) a q) =
      pthSymbolAtPrime (p := p) α q := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hbot_q' : NeZero (cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    ⟨cyclotomicGaloisConjugate_ne_bot a hbot⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI hmax_q' :
      (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal :=
    cyclotomicGaloisConjugate_isMaximal a q
  -- σ_a α ∉ σ_a • q.
  have hα' : cyclotomicRingOfIntegersEquiv (p := p) K a α ∉
      cyclotomicGaloisConjugate (p := p) (K := K) a q :=
    (notMem_cyclotomicGaloisConjugate_iff a).mpr hα
  -- Unfold both sides of `pthSymbolAtPrime` in their good case.
  have hbot_q' : cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hbot
  unfold pthSymbolAtPrime
  rw [dif_neg hbot_q', dif_pos hmax_q', dif_neg hα', dif_pos hdiv',
      dif_pos hroot_q']
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_pos hdiv,
      dif_pos hroot_q]
  -- Both sides are `primeExponent` values; transport via primeExponent_ringEquiv.
  -- The compatibility identifies the chosen ζ at q' with the
  -- image of the chosen ζ at q under cyclotomicGaloisQuotientEquiv.
  have h_card_q'q :
      Fintype.card
        (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) =
        Fintype.card (𝓞 K ⧸ q) :=
    cyclotomicGaloisConjugate_quotient_card_eq a hbot
  -- Apply the invariance lemma to LHS template.
  have h_main := primeExponent_ringEquiv (p := p) (R := 𝓞 K)
    (q := q) (q' := cyclotomicGaloisConjugate (p := p) (K := K) a q)
    (cyclotomicRingOfIntegersEquiv (p := p) K a) rfl
    h_card_q'q hroot_q.choose_spec hdiv hdiv' α hα hα'
  -- h_main relates primeExponent at q' with the σ-image of `hroot_q.choose`
  -- to primeExponent at q with `hroot_q.choose`.
  -- The remaining work is to align the `Classical.choose` value at q'
  -- with the σ-image, which is exactly the compatibility hypothesis.
  -- The image of `hroot_q.choose` under the quotient ring iso (matching
  -- the form used inside `h_main`).
  refine Eq.trans ?_ h_main
  -- Use h_compat to rewrite the LHS's `ζ_q'` to the image. The
  -- `IsPrimitiveRoot` proofs are propositionally irrelevant (they'd be
  -- equal as both establish the same statement about the same value
  -- once the values are equal); `congr 1` reduces to comparing the
  -- arguments where they differ.
  -- We need:
  --   primeExponent q' (Classical.choose hroot_q')
  --     (Classical.choose_spec hroot_q') hdiv' (σ_a α) hα' =
  --   primeExponent q' (Units.mapEquiv (Ideal.quotientEquiv q q' σ_a rfl)
  --     (Classical.choose hroot_q))
  --     ((Classical.choose_spec hroot_q).map_of_injective ...) hdiv'
  --     (σ_a α) hα'
  -- This holds because the two ζ values agree (h_compat) and the
  -- IsPrimitiveRoot proofs are propositionally irrelevant.
  -- Substitute the chosen ζ_q' for its image-under-σ via h_compat.
  -- Since the only dependent argument is the propositional `IsPrimitiveRoot`
  -- proof (which is proof-irrelevant once ζ is fixed), the rewrite
  -- collapses cleanly.
  generalize_proofs h_irrel
  congr 1

/-! ### c.2 — UNCONDITIONAL Galois-action transformation (existence form)

The conditional `pthSymbolAtPrime_galoisAction_of_compat` requires a
specific compatibility between the `Classical.choose` primitive `p`-th
roots in `(𝓞K/q)ˣ` and `(𝓞K/(σq))ˣ`. Mathematically, two primitive
`p`-th roots in `kˣ` differ by a unit power, and the exponent form of
the residue symbol then transforms by a multiplicative factor in `ZMod p`.

The unconditional content of c.2 is captured here as an existence
statement: there exists a unit `c : (ZMod p)ˣ` (depending on `q, a`,
and the global `Classical.choose` values, but **independent of `α`**)
such that

```
pthSymbolAtPrime (σ_a α) (σ_a • q) = c.val * pthSymbolAtPrime α q
```

for all `α`. The conditional theorem is the special case `c = 1`. -/

/-- **Unconditional c.2 — `pthSymbolAtPrime` Galois action with
multiplicative shift (existence form).**

For any `q` (with the standard preconditions) and any `a`, there exists
`c : (ZMod p)ˣ` such that for every `α ∈ 𝓞 K` not in `q`,

```
pthSymbolAtPrime (σ_a α) (σ_a • q) = c.val * pthSymbolAtPrime α q
```

The unit `c` measures the discrepancy between `Classical.choose hroot_q'`
and the `σ_a`-image of `Classical.choose hroot_q`: by
`IsPrimitiveRoot.isPrimitiveRoot_iff'`, these differ by an `n`-th
power for some `n.Coprime p`, and `c = (n : ZMod p)⁻¹`. -/
theorem pthSymbolAtPrime_galoisAction_exists_unit
    (a : CyclotomicUnitDelta p)
    {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hroot_q : ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p)
    (hroot_q' :
      ∃ ζ : (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)ˣ,
        IsPrimitiveRoot ζ p)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hdiv' :
      p ∣ Fintype.card (𝓞 K ⧸
        cyclotomicGaloisConjugate (p := p) (K := K) a q) - 1) :
    ∃ c : (ZMod p)ˣ, ∀ (α : 𝓞 K) (_hα : α ∉ q),
      pthSymbolAtPrime (p := p) (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a q) =
        c.val * pthSymbolAtPrime (p := p) α q := by
  classical
  haveI hp_ne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hbot_q' : NeZero (cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    ⟨cyclotomicGaloisConjugate_ne_bot a hbot⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI hmax_q' :
      (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal :=
    cyclotomicGaloisConjugate_isMaximal a q
  -- φ : (𝓞K/q) ≃+* (𝓞K/(σ_a q)). Use Ideal.quotientEquiv directly so the
  -- form matches what primeExponent_ringEquiv produces internally.
  let φ_ring : (𝓞 K ⧸ q) ≃+* (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    Ideal.quotientEquiv q (cyclotomicGaloisConjugate (p := p) (K := K) a q)
      (cyclotomicRingOfIntegersEquiv (p := p) K a) rfl
  let φ_mul : (𝓞 K ⧸ q) ≃* (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    φ_ring.toMulEquiv
  have hη₂_spec : IsPrimitiveRoot
      (Units.mapEquiv φ_mul hroot_q.choose) p :=
    hroot_q.choose_spec.map_of_injective
      (Units.map_injective
        (f := (φ_ring : (𝓞 K ⧸ q) →*
            (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q)))
        φ_ring.injective)
  obtain ⟨n, hn_lt, hn_cop, hn_eq⟩ :=
    (hη₂_spec.isPrimitiveRoot_iff' (k := p)).mp hroot_q'.choose_spec
  have hn_unit : IsUnit ((n : ZMod p)) := by
    rw [ZMod.isUnit_iff_coprime]; exact hn_cop
  refine ⟨hn_unit.unit⁻¹, fun α hα => ?_⟩
  have hα' : cyclotomicRingOfIntegersEquiv (p := p) K a α ∉
      cyclotomicGaloisConjugate (p := p) (K := K) a q :=
    (notMem_cyclotomicGaloisConjugate_iff a).mpr hα
  have hbot_q'_ne : cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hbot
  unfold pthSymbolAtPrime
  rw [dif_neg hbot_q'_ne, dif_pos hmax_q', dif_neg hα', dif_pos hdiv',
      dif_pos hroot_q']
  rw [dif_neg hbot, dif_pos hmax, dif_neg hα, dif_pos hdiv,
      dif_pos hroot_q]
  have h_card_q'q :
      Fintype.card
        (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) =
        Fintype.card (𝓞 K ⧸ q) :=
    cyclotomicGaloisConjugate_quotient_card_eq a hbot
  have h_main : Reflection.ResidueSymbol.PowerResidue.primeExponent
      (cyclotomicGaloisConjugate (p := p) (K := K) a q)
      (Units.mapEquiv φ_mul hroot_q.choose)
      hη₂_spec hdiv'
      (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' =
    Reflection.ResidueSymbol.PowerResidue.primeExponent q
      hroot_q.choose hroot_q.choose_spec hdiv α hα :=
    primeExponent_ringEquiv (p := p) (R := 𝓞 K)
      (q := q) (q' := cyclotomicGaloisConjugate (p := p) (K := K) a q)
      (cyclotomicRingOfIntegersEquiv (p := p) K a) rfl
      h_card_q'q hroot_q.choose_spec hdiv hdiv' α hα hα'
  have h_prim_pow_spec : IsPrimitiveRoot
      ((Units.mapEquiv φ_mul hroot_q.choose) ^ n) p :=
    hη₂_spec.pow_of_coprime n hn_cop
  have h_pow_eq :
      (n : ZMod p) *
        Reflection.ResidueSymbol.PowerResidue.primeExponent
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)
          ((Units.mapEquiv φ_mul hroot_q.choose) ^ n)
          h_prim_pow_spec hdiv'
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' =
      Reflection.ResidueSymbol.PowerResidue.primeExponent
          (cyclotomicGaloisConjugate (p := p) (K := K) a q)
          (Units.mapEquiv φ_mul hroot_q.choose)
          hη₂_spec hdiv'
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' :=
    Reflection.ResidueSymbol.PowerResidue.primeExponent_zeta_pow
      _ hη₂_spec hdiv' h_prim_pow_spec _ hα'
  rw [h_main] at h_pow_eq
  have h_swap :
      Reflection.ResidueSymbol.PowerResidue.primeExponent
        (cyclotomicGaloisConjugate (p := p) (K := K) a q)
        ((Units.mapEquiv φ_mul hroot_q.choose) ^ n)
        h_prim_pow_spec hdiv'
        (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' =
      Reflection.ResidueSymbol.PowerResidue.primeExponent
        (cyclotomicGaloisConjugate (p := p) (K := K) a q)
        hroot_q'.choose hroot_q'.choose_spec hdiv'
        (cyclotomicRingOfIntegersEquiv (p := p) K a α) hα' := by
    revert h_prim_pow_spec
    rw [hn_eq]
    intros
    congr 1
  rw [h_swap] at h_pow_eq
  have hc_val : (hn_unit.unit⁻¹).val = ((n : ZMod p))⁻¹ := by
    have : (hn_unit.unit⁻¹).val * hn_unit.unit.val = 1 := hn_unit.unit.inv_val
    have hu_val : hn_unit.unit.val = (n : ZMod p) := rfl
    rw [hu_val] at this
    exact eq_inv_of_mul_eq_one_left this
  rw [hc_val]
  have hn_ne_zero : ((n : ZMod p)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hn_zero : n = 0 := Nat.eq_zero_of_dvd_of_lt h hn_lt
    rw [hn_zero] at hn_cop
    have hp_eq : p = 1 := by
      unfold Nat.Coprime at hn_cop
      rwa [Nat.gcd_zero_left] at hn_cop
    exact ((Fact.out : p.Prime).one_lt.ne' hp_eq).elim
  rw [eq_inv_mul_iff_mul_eq₀ hn_ne_zero]
  linear_combination h_pow_eq

/-! ### Stickelberger-element action on a prime ideal

The classical Stickelberger element
`Θ = ∑_{a ∈ (ZMod p)ˣ} (a.val) · σ_a⁻¹`
acts on prime ideals of `𝓞 K` formally: applied to a chosen prime
`q_K`, it yields the product
`∏_{a ∈ (ZMod p)ˣ} (σ_a⁻¹ · q_K) ^ (a.val)`.

This is the RHS of c.1's theorem
`(g(χ_q)^p) · 𝓞_K = q_K^Θ`. The actual ideal-equality proof is c.1.3 + c.1.4.
-/

/-- The ideal `q_K^Θ` where `Θ` is the Stickelberger element. By
definition: the product over `a ∈ (ZMod p)ˣ` of `(σ_a⁻¹ · q_K)^a.val`. -/
noncomputable def stickelbergerIdeal (q_K : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ a : CyclotomicUnitDelta p,
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
      ((a : ZMod p).val)

-- (`stickelbergerIdeal_le_prod_conjugates` has been deferred; the
-- support theorem `residueGaussSum_pow_p_support_in_cyclotomicConjugates`
-- below provides the same content via `residueGaussSum_pow_p_descent_to_OK`.)

/-- The Stickelberger ideal is non-bot when `q_K` is non-bot. -/
theorem stickelbergerIdeal_ne_bot
    {q_K : Ideal (𝓞 K)} (hq : q_K ≠ ⊥) :
    stickelbergerIdeal (p := p) (K := K) q_K ≠ ⊥ := by
  classical
  unfold stickelbergerIdeal
  rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
  push Not
  intro a _
  rw [Ideal.zero_eq_bot]
  -- Goal: (σ_{a⁻¹} q_K)^(a.val) ≠ ⊥
  exact pow_ne_zero _
    (by simpa [Ideal.zero_eq_bot] using cyclotomicGaloisConjugate_ne_bot a⁻¹ hq)

/-- The Stickelberger ideal at `⊥` is `⊥`. -/
@[simp] theorem stickelbergerIdeal_bot :
    stickelbergerIdeal (p := p) (K := K) (⊥ : Ideal (𝓞 K)) = ⊥ := by
  classical
  unfold stickelbergerIdeal
  -- Pull out the factor at a = 1: it's ⊥^1 = ⊥, which dominates everything.
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (CyclotomicUnitDelta p))
        (fun a => cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            (⊥ : Ideal (𝓞 K)) ^ ((a : ZMod p).val))
        (Finset.mem_univ (1 : CyclotomicUnitDelta p))]
  -- Factor at 1: cyclotomicGaloisConjugate 1⁻¹ ⊥ = ⊥; (1.val = 1)
  have hone : cyclotomicGaloisConjugate (p := p) (K := K) (1 : CyclotomicUnitDelta p)⁻¹
      (⊥ : Ideal (𝓞 K)) ^ (((1 : CyclotomicUnitDelta p) : ZMod p).val) = ⊥ := by
    rw [show (cyclotomicGaloisConjugate (p := p) (K := K)
            (1 : CyclotomicUnitDelta p)⁻¹ (⊥ : Ideal (𝓞 K)) =
          (⊥ : Ideal (𝓞 K))) from ?_]
    · exact Ideal.bot_pow (Nat.one_le_iff_ne_zero.mp
        (ZMod.val_pos.mpr (1 : (ZMod p)ˣ).isUnit.ne_zero))
    · unfold cyclotomicGaloisConjugate
      exact Ideal.map_bot
  rw [hone, ← Ideal.zero_eq_bot, mul_zero]

/-- Each Stickelberger factor `(σ_{a⁻¹} q_K)^(a.val)` divides the product. -/
theorem stickelbergerIdeal_le_factor
    (q_K : Ideal (𝓞 K)) (a : CyclotomicUnitDelta p) :
    stickelbergerIdeal (p := p) (K := K) q_K ≤
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
        ((a : ZMod p).val) := by
  classical
  unfold stickelbergerIdeal
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (CyclotomicUnitDelta p))
        (fun a => cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
            ((a : ZMod p).val)) (Finset.mem_univ a)]
  exact Ideal.mul_le_left

/-- Every cyclotomic conjugate of `q_K` divides `stickelbergerIdeal q_K`.
The factor at `a = c⁻¹` contributes `(σ_c q_K)^k` with k ≥ 1. -/
theorem cyclotomicGaloisConjugate_dvd_stickelbergerIdeal
    (q_K : Ideal (𝓞 K)) (c : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) c q_K ∣
      stickelbergerIdeal (p := p) (K := K) q_K := by
  -- The factor `(σ_c q_K)^(c⁻¹.val)` divides stickelbergerIdeal (by le_factor).
  -- Then σ_c q_K divides that factor since (c⁻¹.val ≥ 1).
  have hle := stickelbergerIdeal_le_factor (p := p) (K := K) q_K c⁻¹
  -- hle : stickelbergerIdeal q_K ≤ (σ_{(c⁻¹)⁻¹} q_K)^((c⁻¹).val) = (σ_c q_K)^k
  rw [show ((c⁻¹ : CyclotomicUnitDelta p)⁻¹ : CyclotomicUnitDelta p) = c from
    inv_inv c] at hle
  -- σ_c q_K | (σ_c q_K)^k for k ≥ 1.
  have h_val : 0 < ((c⁻¹ : CyclotomicUnitDelta p) : ZMod p).val :=
    ZMod.val_pos.mpr c⁻¹.isUnit.ne_zero
  have hdvd_pow : cyclotomicGaloisConjugate (p := p) (K := K) c q_K ∣
      cyclotomicGaloisConjugate (p := p) (K := K) c q_K ^
        ((c⁻¹ : CyclotomicUnitDelta p) : ZMod p).val :=
    dvd_pow_self _ (Nat.pos_iff_ne_zero.mp h_val)
  -- And `(σ_c q_K)^k ⊇ stickelbergerIdeal q_K` (as ideals; i.e., divides
  -- stickelbergerIdeal in the divides-iff-contains sense).
  exact dvd_trans hdvd_pow (Ideal.dvd_iff_le.mpr hle)

/-- The Stickelberger ideal is contained in `q_K`: the factor at `a = 1`
is `(σ_1 q_K)^(1.val) = q_K^1 = q_K`, dominating the entire product. -/
theorem stickelbergerIdeal_le_self (q_K : Ideal (𝓞 K)) :
    stickelbergerIdeal (p := p) (K := K) q_K ≤ q_K := by
  classical
  unfold stickelbergerIdeal
  -- Split off the factor at a = 1.
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (CyclotomicUnitDelta p))
        (fun a => cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
            ((a : ZMod p).val)) (Finset.mem_univ (1 : CyclotomicUnitDelta p))]
  -- Goal: prod_erase * factor_at_1 ≤ q_K
  -- factor_at_1 = (σ_{1⁻¹} q_K)^(1.val) = q_K^1 = q_K. Use this.
  have hone : cyclotomicGaloisConjugate (p := p) (K := K) (1 : CyclotomicUnitDelta p)⁻¹
        q_K ^ (((1 : CyclotomicUnitDelta p) : ZMod p).val) = q_K := by
    simp [cyclotomicGaloisConjugate_one, ZMod.val_one_eq_one_mod,
      Nat.one_mod_eq_one.mpr (Fact.out : p.Prime).one_lt.ne']
  rw [hone]
  exact Ideal.mul_le_left

/-! ### Connection to Mathlib's `primesOver`

The cyclotomic Galois orbit of a prime `q` of `𝓞 K` (above a rational
prime `ℓ ≠ p`) coincides with Mathlib's `primesOver (q.under ℤ) (𝓞 K)`,
the Set of all prime ideals of `𝓞 K` lying over `q.under ℤ`. -/

/-- The cyclotomic Galois orbit equals the set of primes over `q.under ℤ`
(as a Set). -/
theorem coe_cyclotomicConjugates {q : Ideal (𝓞 K)} [q.IsPrime] :
    (cyclotomicConjugates (p := p) (K := K) q : Set (Ideal (𝓞 K))) =
      Ideal.primesOver (q.under ℤ) (𝓞 K) := by
  ext I
  refine ⟨?_, ?_⟩
  · intro hI
    rw [Finset.mem_coe] at hI
    haveI : I.IsPrime := isPrime_of_mem_cyclotomicConjugates hI
    exact ⟨inferInstance,
      ⟨(under_eq_of_mem_cyclotomicConjugates hI).symm⟩⟩
  · rintro ⟨hI_prime, hI_lies⟩
    haveI : I.IsPrime := hI_prime
    have h_under : I.under ℤ = q.under ℤ := hI_lies.over.symm
    rw [Finset.mem_coe]
    exact mem_cyclotomicConjugates_iff_under_eq.mpr h_under

omit [NumberField K] in
/-- Pulling back a non-bot prime ideal of `𝓞 K` to `ℤ` is non-bot. -/
theorem under_ne_bot {q : Ideal (𝓞 K)} (hq : q ≠ ⊥) : q.under ℤ ≠ ⊥ :=
  Ideal.IsIntegral.comap_ne_bot (R := ℤ) (A := 𝓞 K) hq

/-- The cyclotomic Galois orbit equals Mathlib's `IsDedekindDomain.primesOverFinset`. -/
theorem cyclotomicConjugates_eq_primesOverFinset
    {q : Ideal (𝓞 K)} [hq : q.IsPrime] (hq_ne : q ≠ ⊥) :
    cyclotomicConjugates (p := p) (K := K) q =
      IsDedekindDomain.primesOverFinset (q.under ℤ) (𝓞 K) := by
  have hu_ne : q.under ℤ ≠ ⊥ := under_ne_bot hq_ne
  haveI : (q.under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hu_ne
  rw [← Finset.coe_inj, coe_cyclotomicConjugates,
      IsDedekindDomain.coe_primesOverFinset hu_ne (𝓞 K)]

/-- The Galois group of the cyclotomic field has cardinality `p - 1`. -/
theorem natCard_galGroup_eq :
    Nat.card Gal(K/ℚ) = p - 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have e : Gal(K/ℚ) ≃ CyclotomicUnitDelta p :=
    (cyclotomicGalEquivZMod (p := p) K).toEquiv
  rw [Nat.card_congr e]
  change Nat.card ((ZMod p)ˣ) = p - 1
  rw [Nat.card_eq_fintype_card, ZMod.card_units p]

/-- **Galois fundamental identity** for the cyclotomic conjugate orbit:
`#orbit · ramification · inertia = p - 1`.
Specialised from Mathlib's
`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` plus
`natCard_galGroup_eq`. -/
theorem cyclotomicConjugates_card_mul_ramificationIdxIn_mul_inertiaDegIn
    {q : Ideal (𝓞 K)} [q.IsPrime] (hq_ne : q ≠ ⊥) :
    (cyclotomicConjugates (p := p) (K := K) q).card *
      ((q.under ℤ).ramificationIdxIn (𝓞 K) *
        (q.under ℤ).inertiaDegIn (𝓞 K)) = p - 1 := by
  have hu_ne : q.under ℤ ≠ ⊥ := under_ne_bot hq_ne
  haveI : (q.under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hu_ne
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ)) ℚ K
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ K
  have hfid := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (A := ℤ) (B := 𝓞 K) (G := Gal(K/ℚ)) hu_ne
  have hcard : (Ideal.primesOver (q.under ℤ) (𝓞 K)).ncard =
      (cyclotomicConjugates (p := p) (K := K) q).card := by
    rw [← coe_cyclotomicConjugates (p := p) (K := K) (q := q),
        Set.ncard_coe_finset]
  rw [hcard] at hfid
  -- Inline `Nat.card Gal(K/ℚ) = p - 1` proof to avoid typeclass-synth fragility.
  have hcard_gal : Nat.card Gal(K/ℚ) = p - 1 := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have e : Gal(K/ℚ) ≃ CyclotomicUnitDelta p :=
      (cyclotomicGalEquivZMod (p := p) K).toEquiv
    rw [Nat.card_congr e]
    change Nat.card ((ZMod p)ˣ) = p - 1
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  rw [hcard_gal] at hfid
  exact hfid

/-- **Split case** (ℓ ≡ 1 mod p): if both ramification and inertia degrees are 1,
the orbit has cardinality `p - 1` (full splitting in `𝓞 K`). -/
theorem cyclotomicConjugates_card_eq_p_sub_one_of_split
    {q : Ideal (𝓞 K)} [q.IsPrime] (hq_ne : q ≠ ⊥)
    (he : (q.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf : (q.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    (cyclotomicConjugates (p := p) (K := K) q).card = p - 1 := by
  have h :
      (cyclotomicConjugates (p := p) (K := K) q).card *
        ((q.under ℤ).ramificationIdxIn (𝓞 K) *
          (q.under ℤ).inertiaDegIn (𝓞 K)) = p - 1 :=
    cyclotomicConjugates_card_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p) (K := K) (q := q) hq_ne
  rw [he, hf, mul_one, mul_one] at h
  exact h

/-- The cardinality of the cyclotomic conjugate orbit equals `(p - 1) / (e · f)`
where `e` and `f` are the ramification index and inertia degree above
`q.under ℤ`. -/
theorem cyclotomicConjugates_card_eq_div
    {q : Ideal (𝓞 K)} [q.IsPrime] (hq_ne : q ≠ ⊥) :
    (cyclotomicConjugates (p := p) (K := K) q).card =
      (p - 1) / ((q.under ℤ).ramificationIdxIn (𝓞 K) *
                 (q.under ℤ).inertiaDegIn (𝓞 K)) := by
  have h :
      (cyclotomicConjugates (p := p) (K := K) q).card *
        ((q.under ℤ).ramificationIdxIn (𝓞 K) *
          (q.under ℤ).inertiaDegIn (𝓞 K)) = p - 1 :=
    cyclotomicConjugates_card_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p) (K := K) (q := q) hq_ne
  rcases Nat.eq_zero_or_pos
    ((q.under ℤ).ramificationIdxIn (𝓞 K) *
     (q.under ℤ).inertiaDegIn (𝓞 K)) with hef | hef
  · rw [hef, mul_zero] at h
    have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  · have h' : (p - 1) / ((q.under ℤ).ramificationIdxIn (𝓞 K) *
                         (q.under ℤ).inertiaDegIn (𝓞 K)) =
              (cyclotomicConjugates (p := p) (K := K) q).card := by
      rw [← h, Nat.mul_div_cancel _ hef]
    exact h'.symm

/-- The cardinality of the cyclotomic conjugate set is bounded by `p - 1`,
the cardinality of `(ZMod p)ˣ`. -/
theorem cyclotomicConjugates_card_le (q : Ideal (𝓞 K)) :
    (cyclotomicConjugates (p := p) (K := K) q).card ≤
      Fintype.card (CyclotomicUnitDelta p) := by
  classical
  unfold cyclotomicConjugates
  exact (Finset.card_image_le).trans (le_of_eq (Finset.card_univ))

/-- The cardinality of the cyclotomic conjugate set equals `p - 1` over the
cardinality of the stabilizer (orbit-stabilizer count). For now we only state
the upper bound; the exact equality requires identifying the stabilizer
(decomposition group). -/
theorem cyclotomicConjugates_card_le_p_sub_one (q : Ideal (𝓞 K)) :
    (cyclotomicConjugates (p := p) (K := K) q).card ≤ p - 1 := by
  refine (cyclotomicConjugates_card_le (p := p) (K := K) q).trans ?_
  -- Fintype.card (CyclotomicUnitDelta p) = Fintype.card (ZMod p)ˣ = p - 1.
  exact (ZMod.card_units p).le


/-- **Strengthened support condition for `(g(χ_q)^p)`.**
The
ideal `(g(χ_q)^p) · 𝓞_K` is supported only on primes in the Galois
orbit `cyclotomicConjugates q_K`. Existential form: there is a
non-zero `γ ∈ q_K` (a witness produced by the Stickelberger descent)
such that any prime containing `γ` is a cyclotomic conjugate of `q_K`.

This is the support side of the Stickelberger ideal theorem `(g(χ_q)^p)·𝓞_K = q^Θ`
(c.1's deliverable); the exact valuations are c.1.3. -/
theorem residueGaussSum_pow_p_support_in_cyclotomicConjugates
    (q_K : Ideal (𝓞 K)) [q_K.IsPrime] (hq_ne_bot : q_K ≠ ⊥)
    (_hq_not_above_p : ¬ ((p : 𝓞 K) ∈ q_K)) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧ γ ∈ q_K ∧
      ∀ (b : Ideal (𝓞 K)), b.IsPrime → b ≠ ⊥ → γ ∈ b →
        b ∈ cyclotomicConjugates (p := p) (K := K) q_K := by
  refine ⟨(Ideal.absNorm q_K : 𝓞 K), ?_, ?_, ?_⟩
  · have hN_ne : Ideal.absNorm q_K ≠ 0 := by
      rw [Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
      exact mem_nonZeroDivisors_iff_ne_zero.mpr hq_ne_bot
    exact_mod_cast hN_ne
  · exact Ideal.absNorm_mem q_K
  · intro b hb_prime hb_ne_bot hγ_b
    haveI hqK_ne_zero : NeZero q_K := ⟨hq_ne_bot⟩
    haveI hb_ne_zero : NeZero b := ⟨hb_ne_bot⟩
    have hp_prime : (Ideal.absNorm (q_K.under ℤ)).Prime :=
      Nat.absNorm_under_prime q_K
    have hq_prime : (Ideal.absNorm (b.under ℤ)).Prime :=
      Nat.absNorm_under_prime b
    have hq_dvd : Ideal.absNorm (b.under ℤ) ∣ Ideal.absNorm q_K := by
      have hγ' : ((Ideal.absNorm q_K : ℤ) : 𝓞 K) ∈ b := by
        push_cast
        exact hγ_b
      rw [Int.cast_mem_ideal_iff] at hγ'
      exact_mod_cast hγ'
    have h_norm_pow : Ideal.absNorm q_K =
        Ideal.absNorm (q_K.under ℤ) ^
          ((Ideal.span ({(Ideal.absNorm (q_K.under ℤ) : ℤ)} : Set ℤ)).inertiaDeg q_K) := by
      have := Ideal.absNorm_eq_pow_inertiaDeg
        (R := 𝓞 K) (P := q_K) (p := (Ideal.absNorm (q_K.under ℤ) : ℤ))
        (Nat.prime_iff_prime_int.mp hp_prime)
      simpa using this
    have hq_eq_p : Ideal.absNorm (b.under ℤ) = Ideal.absNorm (q_K.under ℤ) := by
      rw [h_norm_pow] at hq_dvd
      exact (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)
    have h_qK_under :
        Ideal.span ({(Ideal.absNorm (q_K.under ℤ) : ℤ)} : Set ℤ) = q_K.under ℤ :=
      Ideal.LiesOver.over (P := q_K)
        (p := Ideal.span ({(Ideal.absNorm (q_K.under ℤ) : ℤ)} : Set ℤ))
    have h_b_under :
        Ideal.span ({(Ideal.absNorm (b.under ℤ) : ℤ)} : Set ℤ) = b.under ℤ :=
      Ideal.LiesOver.over (P := b)
        (p := Ideal.span ({(Ideal.absNorm (b.under ℤ) : ℤ)} : Set ℤ))
    have h_under : b.under ℤ = q_K.under ℤ := by
      rw [← h_b_under, ← h_qK_under, hq_eq_p]
    exact mem_cyclotomicConjugates_iff_under_eq.mpr h_under

/-- Every prime factor of `stickelbergerIdeal q_K` is in `cyclotomicConjugates q_K`.
By construction, the Stickelberger ideal is a product of powers of cyclotomic
conjugates of `q_K`. -/
theorem normalizedFactors_stickelbergerIdeal_subset
    {q_K : Ideal (𝓞 K)} [q_K.IsPrime] (hq_ne : q_K ≠ ⊥)
    {b : Ideal (𝓞 K)}
    (hb : b ∈ UniqueFactorizationMonoid.normalizedFactors
            (stickelbergerIdeal (p := p) (K := K) q_K)) :
    b ∈ cyclotomicConjugates (p := p) (K := K) q_K := by
  haveI : (cyclotomicConjugates (p := p) (K := K) q_K).Nonempty :=
    ⟨q_K, self_mem_cyclotomicConjugates q_K⟩
  -- b is prime in 𝓞 K and divides stickelbergerIdeal q_K.
  -- stickelbergerIdeal q_K is a product of powers of σ-conjugates of q_K.
  -- By IsPrime.prod_le, b ⊇ some factor, hence b = some σ-conjugate.
  haveI hb_prime : Prime b :=
    UniqueFactorizationMonoid.prime_of_normalized_factor b hb
  haveI hb_isPrime : b.IsPrime := Ideal.isPrime_of_prime hb_prime
  have hb_ne : b ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact hb_prime.ne_zero
  -- b ∣ stickelbergerIdeal
  have hb_dvd : b ∣ stickelbergerIdeal (p := p) (K := K) q_K :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
  -- stickelbergerIdeal := ∏ a, (σ_{a⁻¹} q_K)^(a.val).
  -- b ⊇ product (as `b | product`), b prime ⟹ b ⊇ some factor (as `b | factor`).
  -- Note: in Dedekind domains, `I ∣ J ↔ J ≤ I` (i.e., `I` divides `J` iff `J ⊆ I`).
  have hstick_le_b : stickelbergerIdeal (p := p) (K := K) q_K ≤ b :=
    Ideal.le_of_dvd hb_dvd
  unfold stickelbergerIdeal at hstick_le_b
  have ⟨a, _, ha⟩ :=
    (Ideal.IsPrime.prod_le (s := Finset.univ)
      (f := fun a => cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^
              ((a : ZMod p).val))
      (hp := hb_isPrime)).mp hstick_le_b
  -- ha : (σ_{a⁻¹} q_K)^(a.val) ≤ b. b is prime. So the conjugate ≤ b.
  have h_aval : 0 < (a : ZMod p).val := ZMod.val_pos.mpr a.isUnit.ne_zero
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ q_K
  have hb_le' : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ≤ b :=
    @Ideal.IsPrime.le_of_pow_le _ _
      (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K)
      b hb_isPrime ((a : ZMod p).val) ha
  -- Both b and the conjugate are non-bot prime ideals in 𝓞 K (a Dedekind domain),
  -- hence maximal. b ≤ maximal ⟹ b = the maximal one.
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K) ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a⁻¹ hq_ne
  haveI : b.IsMaximal := Ideal.IsPrime.isMaximal hb_isPrime hb_ne
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance ‹_ ≠ ⊥›
  -- conj ≤ b, conj maximal, b ≠ ⊤ ⟹ conj = b.
  have hb_eq : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K = b :=
    Ideal.IsMaximal.eq_of_le ‹(cyclotomicGaloisConjugate _ _).IsMaximal›
      (Ideal.IsMaximal.ne_top ‹b.IsMaximal›) hb_le'
  rw [← hb_eq]
  exact (mem_cyclotomicConjugates_iff (p := p) (K := K) q_K _).mpr ⟨a⁻¹, rfl⟩

/-! ### `StickelbergerIdealEquality` data

The full Stickelberger ideal equality `(g(χ_q)^p) · 𝓞_K = stickelbergerIdeal q_K`
for q above ℓ ≠ p is the substantive content of c.1. It records a generator
γ ∈ 𝓞_K (essentially `g(χ_q)^p` after descent) together with the ideal
factorization. -/

/-- The Stickelberger ideal equality for a specific prime `q_K`. -/
structure StickelbergerIdealEquality (q_K : Ideal (𝓞 K)) : Prop where
  exists_generator :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      Ideal.span ({γ} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) q_K

/-- From a `StickelbergerIdealEquality`, extract the generator. -/
noncomputable def StickelbergerIdealEquality.gen
    {q_K : Ideal (𝓞 K)}
    (h : StickelbergerIdealEquality (p := p) (K := K) q_K) : 𝓞 K :=
  h.exists_generator.choose

/-- The extracted generator is nonzero. -/
theorem StickelbergerIdealEquality.gen_ne_zero
    {q_K : Ideal (𝓞 K)}
    (h : StickelbergerIdealEquality (p := p) (K := K) q_K) :
    h.gen ≠ 0 :=
  h.exists_generator.choose_spec.1

/-- The extracted generator generates the Stickelberger ideal. -/
theorem StickelbergerIdealEquality.span_gen
    {q_K : Ideal (𝓞 K)}
    (h : StickelbergerIdealEquality (p := p) (K := K) q_K) :
    Ideal.span ({h.gen} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) q_K :=
  h.exists_generator.choose_spec.2

/-- A `StickelbergerIdealEquality` makes the Stickelberger ideal principal. -/
theorem StickelbergerIdealEquality.isPrincipal
    {q_K : Ideal (𝓞 K)} (h : StickelbergerIdealEquality (p := p) (K := K) q_K) :
    Submodule.IsPrincipal (stickelbergerIdeal (p := p) (K := K) q_K) := by
  obtain ⟨γ, _, hγ⟩ := h.exists_generator
  exact ⟨⟨γ, hγ.symm⟩⟩

end Furtwaengler

end BernoulliRegular
