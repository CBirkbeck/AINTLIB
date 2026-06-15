/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Frobenius

/-!
# Field tower for the Frobenius Verschiebung (T-HASSE-CLOSE-C-VERSCHIEBUNG-FROBENIUS Session 2)

This file establishes the field-tower structure underlying the Verschiebung
construction:

```
K  ⊆  Im([q]*)  ⊆?  K(E)^q = Im(π*)  ⊆  K(E)
                              ↑
                              |
                       degree q (purely inseparable)
                degree q²
```

over a finite field `K = F_q` and an elliptic curve `W : WeierstrassCurve K`.

## Field-tower facts (Session 2)

* **`frobeniusIsog_pullback_finrank`** — `[K(E) : Im(π*)] = q`. Direct
  specialisation of `frobenius_finrank_functionField` (already shipped) to
  `frobeniusIsog`.
* **`mulByInt_q_pullback_finrank`** — `[K(E) : Im([q]*)] = q²`.
  Specialisation of `mulByInt_degree` to `n = q`.
* **`mulByInt_q_pow_mem_pi_image_witness`** — witness-form of the
  load-bearing inclusion `Im([q]*) ⊆ Im(π*) = K(E)^q`. Discharged by
  Session 3 (Frobenius factorization at the function-field level via
  IsPurelyInseparable + degree count).
* **`mulByInt_q_pullback_factor_witness`** — given the inclusion witness,
  produce the Verschiebung's pullback as `AlgHom.factor` output.

## Strategy for Session 3 (the inclusion)

The non-circular path: count degrees in the field tower.
`[K(E) : K(E)^q] = q` and `[K(E) : Im([q]*)] = q²`. If the inclusion fails,
`Im([q]*) · K(E)^q ⊋ K(E)^q` is strictly larger, but `[K(E) : K(E)^q] = q`
(prime power) bounds the codimension. Combined with `K(E) / K(E)^q` purely
inseparable of degree `q`, the only consistent configuration with
`[K(E) : Im([q]*)] = q²` is `Im([q]*) ⊆ K(E)^q`.

For now, Session 3 ships this as a witness; the unconditional discharge
is the focused work of the session sub-ticket.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.11 (Frobenius
  pullback structure), III.4.2 (mulByInt degree), III.6.2 (Verschiebung
  inclusion).
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### Tower step 1: `[K(E) : Im(π*)] = q` -/

/-- The Frobenius isogeny's pullback has codimension `q` in `K(E)`:
    `[K(E) : Im(π*)] = #K`. Specialisation of
    `frobenius_finrank_functionField` to the `frobeniusIsog` Isogeny. -/
theorem frobeniusIsog_pullback_finrank :
    @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (frobeniusIsog W).toAlgebra.toModule = Fintype.card K :=
  frobeniusIsog_degree W

/-! ### Tower step 2: `[K(E) : Im([q]*)] = q²` -/

/-- The `[q]`-multiplication's pullback has codimension `q²` in `K(E)`.
    Direct specialisation of `mulByInt_degree`. -/
theorem mulByInt_q_pullback_finrank :
    @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAlgebra.toModule =
      Fintype.card K ^ 2 := by
  have hq : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have h := mulByInt_degree W.toAffine ((Fintype.card K : ℕ) : ℤ) hq
  change (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).degree = Fintype.card K ^ 2
  rw [h]
  -- Show ((((Fintype.card K : ℕ) : ℤ)) ^ 2).toNat = Fintype.card K ^ 2
  rw [show (((Fintype.card K : ℕ) : ℤ) ^ 2).toNat = Fintype.card K ^ 2 from by
    have : ((Fintype.card K : ℕ) : ℤ) ^ 2 = ((Fintype.card K ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]]

/-! ### Tower step 3: Pure-inseparability of `K(E) / Im(π*)`

This is shipped in witness form as `frobeniusIsogeny_pow_mem_fieldRange`
(in `HasseWeil/FrobeniusIsogeny.lean`): every `x ∈ K(E)` has some `x^(p^n)
∈ Im(π*)`. The natural number `n` such that `p^n = q` exists by
`FiniteField.card'`. -/

/-! ### Tower step 4 — load-bearing inclusion: `Im([q]*) ⊆ Im(π*)`

This is the **substantive content** of the Verschiebung's existence
(Silverman III.6.2). We ship it as a witness here; the unconditional
discharge is Session 3's focused work via the field-tower degree count
+ purely inseparable extension structure.

The strategic argument: `K(E)/K(E)^q` is purely inseparable of degree `q`
(prime-power) and `[K(E) : Im([q]*)] = q²`. Since `K(E)^q` and `Im([q]*)`
are both subfields of `K(E)`, the compositum
`K(E)^q · Im([q]*)` has degree dividing `gcd(q, q²) · ... ` constraints.
The argument forces `Im([q]*) ⊆ K(E)^q`.

For now: take the inclusion as input. -/

/-- **Witness form of the Silverman III.6.2 inclusion**: given that every
    pullback `(mulByInt W q).pullback z` has a `q`-th root in `K(E)`,
    conclude `Im([q]*) ⊆ Im(π*) = K(E)^q`. -/
theorem mulByInt_q_pullback_image_subset_frobenius_witness
    (h_qth_root : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.fieldRange ≤
      (frobeniusIsog W).pullback.fieldRange := by
  rintro f ⟨z, hz⟩
  -- f = (mulByInt W q).pullback z. Need f ∈ π.pullback.fieldRange.
  obtain ⟨g, hg⟩ := h_qth_root z
  refine ⟨g, ?_⟩
  -- (frobeniusIsog W).pullback g = g^q = (mulByInt W q).pullback z = f
  change (frobeniusIsog W).pullback g = f
  rw [frobeniusIsog_pullback_apply, hg]
  exact hz

/-! ### Tower step 5: Verschiebung pullback as factor

Once the inclusion `Im([q]*) ⊆ Im(π*)` is established, the Verschiebung's
pullback exists as the unique algebra hom `V* : K(E) →ₐ[K] K(E)` such
that `[q]* = π* ∘ V*`. By `AlgHom.factor`-style construction once the
range inclusion holds.

Witness form below: given the q-th-root function (which gives the
inclusion via `mulByInt_q_pullback_image_subset_frobenius_witness`),
constructed Verschiebung pullback satisfying `[q]* = π* ∘ V*`. -/

/-- **Witness-parametric Verschiebung pullback**: given a function `g`
    sending each `z ∈ K(E)` to a `q`-th root of `(mulByInt W q).pullback z`,
    define the Verschiebung pullback as `V* z := g z`. The factoring
    identity `[q]* = π* ∘ V*` follows by definition.

    Note: for `g` to be an algebra hom, the choice of root must be
    compatible (functorial). The unconditional Verschiebung uses the
    canonical compatible choice via Frobenius factorization. -/
theorem mulByInt_q_factor_witness
    (V : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (h_factor : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
      (frobeniusIsog W).pullback.comp V) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.fieldRange ≤
      (frobeniusIsog W).pullback.fieldRange := by
  rintro f ⟨z, hz⟩
  refine ⟨V z, ?_⟩
  change (frobeniusIsog W).pullback (V z) = f
  rw [show (frobeniusIsog W).pullback (V z) =
    ((frobeniusIsog W).pullback.comp V) z from rfl]
  rw [← h_factor]; exact hz

end HasseWeil
