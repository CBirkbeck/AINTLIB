/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.Pairing
import HasseWeil.WeilPairing.FrobMatrixData
import HasseWeil.WeilPairing.FrobeniusFunctionFieldEquiv
import HasseWeil.WeilPairing.FrobeniusDivisorGalois
import HasseWeil.WeilPairing.OneSubWitnesses
import HasseWeil.WeilPairing.FrobeniusConjugation

/-!
# Galois equivariance of the Weil pairing (Silverman III.8.1d), the algebra core

This file ships the **pure-algebra core** of the Galois route to Silverman's Prop III.8.1d, the
Frobenius scaling `e_ℓ(π̄ S, π̄ T) = e_ℓ(S, T)^{#K}` on `E_{K̄}[ℓ]`.

## The Galois route (reviewer round-20 Q4)

The `q`-power *arithmetic* Frobenius `σ` of `K̄ / 𝔽_q` is a field automorphism of `K̄` (`c ↦ c^q`),
bijective because `K̄` is algebraically closed.  It extends to a **ring automorphism** of the
function field `K̄(E)` that fixes the `𝔽_q`-rational subfield `𝔽_q(E)` (the generators `x_gen,
y_gen` are defined over `𝔽_q`) and acts as the `q`-power on the `K̄`-coefficients.  On `L`-points
of `E_{K̄}` it acts coordinatewise, `(x, y) ↦ (x^q, y^q)`, which is **exactly** the geometric
Frobenius point map `π̄ = geomFrobeniusPoint` (`frobeniusHomBaseChange = geomFrobeniusPoint`).

The Weil pairing is **Galois equivariant**: `e_ℓ(σ S, σ T) = σ(e_ℓ(S, T))`, and on the `ℓ`-th roots
of unity `μ_ℓ ⊂ K̄` the arithmetic Frobenius `σ` acts as `ζ ↦ ζ^q = ζ^{#K}`.  Combined with `σ S =
π̄ S` this is `e_ℓ(π̄ S, π̄ T) = e_ℓ(S, T)^{#K}`, i.e. III.8.1d.

## What this file proves (axiom-clean, no `sorry`)

`weilPairing_galois_core` — the **constant-ratio identity** behind Galois equivariance, written
abstractly so it has no geometric dependencies.  Given:

* a ring automorphism `σ : K(E) ≃+* K(E)` of the function field;
* the **conjugation** of the translation: `σ ∘ τ_S = τ_{S'} ∘ σ` at the relevant Weil functions,
  where `S'` is `σ`'s action on `S` (for the arithmetic Frobenius, `S' = π̄ S`);
* the **`σ`-naturality of the Weil function**: `σ(g_T) = c · g_{T'}` for a nonzero constant
  `c ∈ F` (the two Weil functions `g_T`, `g_{T'}` have the same divisor up to the `σ`-twist, so they
  differ by a unit);
* the **`q`-power on constants**: `σ(algebraMap a) = algebraMap (a ^ q)` for `a ∈ F` (the arithmetic
  Frobenius `q`-powers the `K̄`-coefficients);

then `e_ℓ(S', T') = e_ℓ(S, T) ^ q`.

This is the genuine algebraic heart of III.8.1d.  The three hypotheses are the function-field
shadow of "the group law, the translation action and the Weil function are all `𝔽_q`-rational, so
they commute with the arithmetic Frobenius `σ`".  The conjugation and the `q`-power-on-constants are
elementary for the concrete arithmetic `σ`; the `σ`-naturality of the Weil function is the divisor
Galois-descent `div(σ g_T) = [ℓ]^*(σ T) − [ℓ]^*(O) = div(g_{σ T})`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Prop 8.1d, Galois equivariance).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

section GaloisCore

variable [IsAlgClosed F]

/-- **The Galois-equivariance constant-ratio identity** (Silverman III.8.1d, the algebra core).

Let `σ : K(E) ≃+* K(E)` be a ring automorphism of the function field, and let `S, T, S', T'` be
`ℓ`-torsion points, where `S', T'` are the `σ`-images of `S, T` (for the arithmetic `q`-power
Frobenius, `S' = π̄ S`, `T' = π̄ T`).  Suppose:

* `hconj` — the conjugation of the translation by `σ` at `g_T`:
  `σ (τ_S (g_T)) = τ_{S'} (σ (g_T))`;
* `hnat` — the `σ`-naturality of the Weil function:
  `σ (g_T) = algebraMap c · g_{T'}` for a nonzero `c : F`;
* `hpow` — the `q`-power on constants: `σ (algebraMap a) = algebraMap (a ^ q)` for all `a : F`.

Then `e_ℓ(S', T') = e_ℓ(S, T) ^ q`.

Proof: apply `σ` to the pairing relation `τ_S (g_T) = algebraMap (e_ℓ(S,T)) · g_T`.  The left side is
`τ_{S'} (σ g_T)` by `hconj`; the right side is `algebraMap (e_ℓ(S,T)^q) · σ(g_T)` by `hpow` and
multiplicativity.  Substituting `σ(g_T) = algebraMap c · g_{T'}` (`hnat`), using that the `F`-algebra
map `τ_{S'}` fixes `algebraMap c` and the pairing relation `τ_{S'} (g_{T'}) = algebraMap (e_ℓ(S',T')) ·
g_{T'}`, and cancelling the nonzero `algebraMap c · g_{T'}`, gives `e_ℓ(S',T') = e_ℓ(S,T)^q`. -/
theorem weilPairing_galois_core (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (q : ℕ)
    (σ : KE ≃+* KE)
    (S T S' T' : W.toAffine.Point)
    (hS : ℓ • S = 0) (hT : ℓ • T = 0) (hS' : ℓ • S' = 0) (hT' : ℓ • T' = 0)
    (hconj : σ (translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT)) =
      translateAlgEquivOfPoint W S' (σ (weilFunction W ℓ hℓ T hT)))
    {c : F} (hc : c ≠ 0)
    (hnat : σ (weilFunction W ℓ hℓ T hT) =
      algebraMap F KE c * weilFunction W ℓ hℓ T' hT')
    (hpow : ∀ a : F, σ (algebraMap F KE a) = algebraMap F KE (a ^ q)) :
    weilPairing W ℓ hℓ S' T' hS' hT' = weilPairing W ℓ hℓ S T hS hT ^ q := by
  -- Abbreviations.
  set e := weilPairing W ℓ hℓ S T hS hT
  set e' := weilPairing W ℓ hℓ S' T' hS' hT'
  set gT := weilFunction W ℓ hℓ T hT
  set gT' := weilFunction W ℓ hℓ T' hT'
  have hgT'_ne : gT' ≠ 0 := weilFunction_ne_zero W ℓ hℓ T' hT'
  have hc_ne : algebraMap F KE c ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap F KE) (algebraMap F KE).injective).mpr hc
  -- Apply `σ` to the pairing relation `τ_S g_T = algebraMap e · g_T`.
  have hrel : σ (translateAlgEquivOfPoint W S gT) =
      σ (algebraMap F KE e * gT) := by
    rw [weilPairing_translate W ℓ hℓ S T hS hT]
  -- LHS via `hconj`: `τ_{S'} (σ g_T)`.
  rw [hconj] at hrel
  -- RHS via `hpow` and multiplicativity: `algebraMap (e^q) · σ g_T`.
  rw [map_mul, hpow] at hrel
  -- Substitute `σ g_T = algebraMap c · g_{T'}` (`hnat`) on both sides.
  rw [hnat] at hrel
  -- Left side: `τ_{S'}` fixes `algebraMap c` and acts on `g_{T'}` by `e'`.
  rw [map_mul, (translateAlgEquivOfPoint W S').commutes,
    weilPairing_translate W ℓ hℓ S' T' hS' hT'] at hrel
  -- Now `hrel : algebraMap c * (algebraMap e' * g_{T'}) = algebraMap (e^q) * (algebraMap c * g_{T'})`.
  -- Reassociate to cancel `algebraMap c * g_{T'} ≠ 0`.
  have hcancel : algebraMap F KE e' * (algebraMap F KE c * gT') =
      algebraMap F KE (e ^ q) * (algebraMap F KE c * gT') := by
    rw [← hrel]; ring
  have hprod_ne : algebraMap F KE c * gT' ≠ 0 := mul_ne_zero hc_ne hgT'_ne
  have hfin := mul_right_cancel₀ hprod_ne hcancel
  exact (algebraMap F KE).injective hfin

end GaloisCore

/-! ### The base-changed Frobenius Galois leaf and the discharge of `FrobeniusScaling`

`FrobeniusGaloisData` bundles, per `ℓ`-torsion `S, T ∈ E_{K̄}[ℓ]`, the single arithmetic-Frobenius
witness that `weilPairing_galois_core` consumes for the base-changed `q`-power Frobenius
`π̄ = frobeniusHomBaseChange`: a ring automorphism `σ` of `K̄(E)` together with

* the **conjugation** `σ ∘ τ_S = τ_{π̄ S} ∘ σ` at the Weil function `g_T`;
* the **`σ`-naturality** `σ(g_T) = c · g_{π̄ T}` for a nonzero `c : K̄` (same divisor up to the
  `σ`-twist);
* the **`q`-power on constants** `σ(algebraMap a) = algebraMap (a ^ #K)`.

`frobeniusScaling_of_galoisData` discharges `FrobeniusScaling` from this leaf, axiom-clean, via
`weilPairing_galois_core` with `S' = π̄ S`, `T' = π̄ T`, `q = #K`.  This is the Galois route to
Silverman III.8.1d; the leaf is the genuine arithmetic content (the existence of `σ` with these
properties — the `𝔽_q`-rationality of the group law, translation and Weil function combined with the
arithmetic `q`-power Frobenius of `K̄ / 𝔽_q`), carried per isogeny exactly as
`ProjOrdTransport`/`Naturality` are throughout the project. -/

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACFGS : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

/-- **The base-changed Frobenius Galois leaf** (Silverman III.8.1d, the Galois-route content).
For the base-changed `q`-power Frobenius point map `π̄ = frobeniusHomBaseChange p r K̄` on `E_{K̄}`,
this bundles, per `ℓ`-torsion `S, T`, the arithmetic-Frobenius witness `weilPairing_galois_core`
consumes: a ring automorphism `σ` of `K̄(E)` with the conjugation `σ ∘ τ_S = τ_{π̄ S} ∘ σ` (at
`g_T`), the `σ`-naturality `σ(g_T) = c · g_{π̄ T}`, and the `q`-power on constants
`σ(algebraMap a) = algebraMap (a ^ #K)`.

This is the genuine arithmetic content of the Frobenius scaling: the `q`-power arithmetic Frobenius
`σ` of `K̄ / 𝔽_q` acts on `K̄(E)` (fixing the `𝔽_q`-rational generators, `q`-powering the `K̄`
coefficients), its action on `E_{K̄}`-points is `π̄ = geomFrobeniusPoint`, and the Weil function's
divisor is `𝔽_q`-rational so transports under `σ` (`div(σ g_T) = [ℓ]^*(π̄ T) − [ℓ]^*(O) =
div(g_{π̄ T})`). -/
def FrobeniusGaloisData
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] : Prop :=
  ∀ (ℓ : ℤ) (hℓ : (ℓ : AlgebraicClosure K) ≠ 0)
    (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (_hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (_hπS : ℓ • frobeniusHomBaseChange W p r (AlgebraicClosure K) S = 0)
    (hπT : ℓ • frobeniusHomBaseChange W p r (AlgebraicClosure K) T = 0),
    ∃ (σ : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField ≃+*
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
      (c : AlgebraicClosure K) (_hc : c ≠ 0),
      (σ (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT)) =
        translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (frobeniusHomBaseChange W p r (AlgebraicClosure K) S)
          (σ (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT))) ∧
      (σ (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT) =
        algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c *
          weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
            (frobeniusHomBaseChange W p r (AlgebraicClosure K) T) hπT) ∧
      (∀ a : AlgebraicClosure K,
        σ (algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) =
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a ^ Fintype.card K))

/-- **`FrobeniusScaling` discharged via the Galois leaf** (Silverman III.8.1d), CoordHom-free.
From the base-changed Frobenius Galois leaf `FrobeniusGaloisData`, the Frobenius scaling
`e_ℓ(π̄ S, π̄ T) = e_ℓ(S, T)^{#K}` on `E_{K̄}[ℓ]` holds for every prime `ℓ ≠ ringChar K`.

Pure application of the axiom-clean `weilPairing_galois_core` with `S' = π̄ S`, `T' = π̄ T`,
`q = #K`, fed by the leaf's arithmetic-Frobenius witness. -/
theorem frobeniusScaling_of_galoisData
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (hdata : FrobeniusGaloisData W p r) :
    FrobeniusScaling W p r (AlgebraicClosure K) := by
  intro ℓ hℓp hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  intro S T
  -- Torsion bookkeeping for `S, T` and their Frobenius images.
  set π := frobeniusHomBaseChange W p r (AlgebraicClosure K)
  have hS : ((ℓ : ℕ) : ℤ) • S.val = 0 := zsmul_eq_zero_of_mem_torsion (W.baseChange _) ℓ S
  have hT : ((ℓ : ℕ) : ℤ) • T.val = 0 := zsmul_eq_zero_of_mem_torsion (W.baseChange _) ℓ T
  have hπS : ((ℓ : ℕ) : ℤ) • π S.val = 0 := by
    rw [← map_zsmul π, hS, map_zero]
  have hπT : ((ℓ : ℕ) : ℤ) • π T.val = 0 := by
    rw [← map_zsmul π, hT, map_zero]
  -- The arithmetic-Frobenius witness for `(S, T)`.
  obtain ⟨σ, c, hc, hconj, hnat, hpow⟩ :=
    hdata ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val hS hT hπS hπT
  -- Apply the Galois constant-ratio core with `S' = π S`, `T' = π T`, `q = #K`.
  exact weilPairing_galois_core (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ)
    (by exact_mod_cast hℓF) (Fintype.card K) σ S.val T.val (π S.val) (π T.val)
    hS hT hπS hπT hconj hc hnat hpow

/-! ### The arithmetic-Frobenius leaf (the geometric residual of leaf 1)

With the arithmetic Frobenius automorphism `σ = frobeniusFunctionFieldEquiv W` of `K̄(E)` now
**concretely constructed** (and proven bijective + `q`-powering the constants) in
`FrobeniusFunctionFieldEquiv.lean`, the residual of `FrobeniusGaloisData` is sharpened to the **two
geometric facts** about this concrete `σ`, bundled as `FrobeniusGaloisGeometric`:

* the **conjugation** `σ ∘ τ_S = τ_{π̄ S} ∘ σ` (at the Weil function `g_T`) — the `𝔽_q`-rationality
  of the translation/group law (the function-field shadow of `σ ∘ (·+S) = (·+ σ S) ∘ σ`, with
  `σ S = π̄ S` the linchpin `frobeniusHomBaseChange = geomFrobeniusPoint`);
* the **`σ`-naturality** `σ(g_T) = c · g_{π̄ T}` for a nonzero `c` — **divisor Galois descent**:
  `div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)` is `𝔽_q`-rational, so `div(σ g_T) = [ℓ]^*(π̄ T) − [ℓ]^*(O) =
  div(g_{π̄ T})`, whence `σ(g_T)/g_{π̄ T}` is a nonzero constant.

The **third** property of `FrobeniusGaloisData` (the `q`-power on constants
`σ(algebraMap a) = algebraMap (a ^ #K)`) is now **discharged** axiom-clean by
`frobeniusFunctionFieldEquiv_algebraMap`; `frobeniusGaloisData_of_geometric` below feeds it in
automatically.  So the leaf is reduced from "construct `σ` + all three properties" (everything
opaque) to **exactly** the two geometric facts for a fixed, concrete `σ`.

`FrobeniusGaloisGeometric` is the named carrier for those two facts, and `frobeniusGaloisData_holds`
supplies them: both are now **proved** axiom-clean — the `σ`-naturality via
`frobeniusFunctionFieldEquiv_weilFunction_eq_smul` (`FrobeniusDivisorGalois.lean`) and the
conjugation/translation-covariance via `frobeniusFunctionFieldEquiv_conj`
(`FrobeniusConjugation.lean`). -/

/-- **The geometric residual of the Frobenius Galois leaf** (Silverman III.8.1d): for the concrete
arithmetic Frobenius `σ = frobeniusFunctionFieldEquiv W` and the `q`-power Frobenius point map
`π̄ = frobeniusHomBaseChange`, the two geometric facts per `ℓ`-torsion `S, T`:

* the **conjugation** `σ (τ_S g_T) = τ_{π̄ S} (σ g_T)`;
* the **`σ`-naturality** `σ(g_T) = c · g_{π̄ T}` for a nonzero `c : K̄`.

This is the divisor-Galois-descent content (the `𝔽_q`-rationality of the group law, translation and
Weil-function divisor combined with the arithmetic `q`-power Frobenius of `K̄ / 𝔽_q`); the third
`FrobeniusGaloisData` property (the `q`-power on constants) is *not* part of this residual — it is
proven axiom-clean by `frobeniusFunctionFieldEquiv_algebraMap`. -/
def FrobeniusGaloisGeometric
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] : Prop :=
  ∀ (ℓ : ℤ) (hℓ : (ℓ : AlgebraicClosure K) ≠ 0)
    (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (_hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (_hπS : ℓ • frobeniusHomBaseChange W p r (AlgebraicClosure K) S = 0)
    (hπT : ℓ • frobeniusHomBaseChange W p r (AlgebraicClosure K) T = 0),
    (frobeniusFunctionFieldEquiv W
        (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT)) =
      translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (frobeniusHomBaseChange W p r (AlgebraicClosure K) S)
        (frobeniusFunctionFieldEquiv W
          (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT))) ∧
    ∃ (c : AlgebraicClosure K) (_hc : c ≠ 0),
      frobeniusFunctionFieldEquiv W
          (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT) =
        algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c *
          weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
            (frobeniusHomBaseChange W p r (AlgebraicClosure K) T) hπT

/-- **`FrobeniusGaloisData` from the geometric residual** (axiom-clean): the concrete arithmetic
Frobenius `σ = frobeniusFunctionFieldEquiv W` realizes `FrobeniusGaloisData` once the two geometric
facts `FrobeniusGaloisGeometric` (conjugation + `σ`-naturality) hold.  The third property (the
`q`-power on constants) is supplied automatically by the axiom-clean
`frobeniusFunctionFieldEquiv_algebraMap`. -/
theorem frobeniusGaloisData_of_geometric
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (hgeom : FrobeniusGaloisGeometric W p r) :
    FrobeniusGaloisData W p r := by
  intro ℓ hℓ S T hS hT hπS hπT
  obtain ⟨hconj, c, hc, hnat⟩ := hgeom ℓ hℓ S T hS hT hπS hπT
  exact ⟨frobeniusFunctionFieldEquiv W, c, hc, hconj, hnat,
    fun a ↦ frobeniusFunctionFieldEquiv_algebraMap W a⟩

/-- **The geometric residual `FrobeniusGaloisGeometric` holds** (now **axiom-clean, no `sorry`**) —
leaf 1.  It is the divisor-Galois-descent content for the concrete arithmetic Frobenius
`σ = frobeniusFunctionFieldEquiv W`:

* **conjugation** `σ (τ_S g_T) = τ_{π̄ S} (σ g_T)` — the `𝔽_q`-rationality of the translation/group
  law combined with `σ` acting on points as `π̄` (`frobeniusHomBaseChange = geomFrobeniusPoint`);
* **`σ`-naturality** `σ(g_T) = c · g_{π̄ T}` — `div(σ g_T) = σ_*(div g_T) = [ℓ]^*(π̄ T) − [ℓ]^*(O) =
  div(g_{π̄ T})`, so the ratio is a nonzero constant.

**Status.** Both facts are now **proved** axiom-clean.

* The **`σ`-naturality** is `frobeniusFunctionFieldEquiv_weilFunction_eq_smul`
  (`FrobeniusDivisorGalois.lean`) via the divisor-Galois-descent engine `valuation_map_ringEquiv` +
  the cast bridge + the fibre place comparison.
* The **conjugation** (translation covariance) `σ ∘ τ_S = τ_{π̄ S} ∘ σ` is
  `frobeniusFunctionFieldEquiv_conj` (`FrobeniusConjugation.lean`): the two function-field ring
  endomorphisms `σ ∘ τ_S` and `τ_{π̄ S} ∘ σ` agree on the base `algebraMap K̄` (both `q`-power the
  coefficients) and on the generators `x_gen, y_gen` (`sigmaConjugation_x_y_gen`, read off the
  coordinates of `Point.map σ_K ∘ Point.map τ_S` at the generic point), hence coincide by the
  ring-hom extensionality `ringHom_ext_base_x_y_gen`.

It is **independent** of the divisor naturality (deriving it from naturality + the pairing relation
would be circular — it would presuppose III.8.1d itself). -/
theorem frobeniusGaloisGeometric_holds
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] :
    FrobeniusGaloisGeometric W p r := by
  intro ℓ hℓ S T hS hT hπS hπT
  -- The linchpin `frobeniusHomBaseChange = geomFrobeniusPoint` bridges the statement's `π̄` to
  -- `geomFrobeniusPoint` (the form of the naturality lemma).
  have hπbridge : frobeniusHomBaseChange W p r (AlgebraicClosure K) =
      HasseWeil.geomFrobeniusPoint W := frobeniusHomBaseChange_eq_geomFrobeniusPoint W p r
  -- Bridge `frobeniusHomBaseChange T = geomFrobeniusPoint T` at the point level.
  have hpt : frobeniusHomBaseChange W p r (AlgebraicClosure K) T =
      HasseWeil.geomFrobeniusPoint W T := DFunLike.congr_fun hπbridge T
  -- The two Weil functions at `frobeniusHomBaseChange T` and `geomFrobeniusPoint T` coincide
  -- (equal point, proof-irrelevant annihilation hypothesis).
  have hwfbridge : ∀ (hπT' : ℓ • HasseWeil.geomFrobeniusPoint W T = 0),
      weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
          (frobeniusHomBaseChange W p r (AlgebraicClosure K) T) hπT =
        weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
          (HasseWeil.geomFrobeniusPoint W T) hπT' := by
    intro hπT'
    -- Generalise the proof and substitute the point equality.
    clear hπS hT hS
    revert hπT
    rw [hpt]
    intro hπT
    rfl
  refine ⟨?_, ?_⟩
  · -- Conjugation (translation covariance): discharged by `frobeniusFunctionFieldEquiv_conj`
    -- (the generic-point/ring-hom-ext route), after bridging `π̄ S = geomFrobeniusPointFun S`.
    have hptS : frobeniusHomBaseChange W p r (AlgebraicClosure K) S =
        HasseWeil.geomFrobeniusPointFun W S := by
      rw [DFunLike.congr_fun hπbridge S, HasseWeil.geomFrobeniusPoint_apply]
    rw [hptS]
    exact frobeniusFunctionFieldEquiv_conj W S
      (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT)
  · -- σ-naturality: discharged by `frobeniusFunctionFieldEquiv_weilFunction_eq_smul`.
    have hπT' : ℓ • HasseWeil.geomFrobeniusPoint W T = 0 := hpt ▸ hπT
    obtain ⟨c, hc, hnat⟩ :=
      frobeniusFunctionFieldEquiv_weilFunction_eq_smul W ℓ hℓ T hT hπT'
    exact ⟨c, hc, by rw [hwfbridge hπT', hnat]⟩

/-- **`FrobeniusGaloisData` for the base-changed `q`-power Frobenius** (Silverman III.8.1d).  A pure
composition: the axiom-clean reduction `frobeniusGaloisData_of_geometric` (concrete `σ`, `q`-power on
constants discharged) applied to the now axiom-clean geometric residual
`frobeniusGaloisGeometric_holds` (conjugation + `σ`-naturality both proved).  Axiom-clean. -/
theorem frobeniusGaloisData_holds
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] :
    FrobeniusGaloisData W p r :=
  frobeniusGaloisData_of_geometric W p r
    (frobeniusGaloisGeometric_holds W p r)

/-- **The Frobenius Weil-pairing scaling `FrobeniusScaling`** (Silverman III.8.1d), CoordHom-free, via
the **Galois route**: `e_ℓ(π̄ S, π̄ T) = e_ℓ(S, T)^{#K}` on `E_{K̄}[ℓ]` for every prime
`ℓ ≠ ringChar K`, where `π̄ = frobeniusHomBaseChange` is the `q`-power Frobenius point map.

This is `frobeniusScaling_of_galoisData` (the axiom-clean reduction via the Galois constant-ratio core
`weilPairing_galois_core`) applied to the arithmetic-Frobenius leaf `frobeniusGaloisData_holds`.  With
the concrete `σ = frobeniusFunctionFieldEquiv` constructed and all of its `FrobeniusGaloisData`
properties (conjugation, `σ`-naturality, `q`-power on constants) now proved, this is **fully
axiom-clean**: `#print axioms frobeniusScaling_holds = [propext, Classical.choice, Quot.sound]`. -/
theorem frobeniusScaling_holds
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] :
    FrobeniusScaling W p r (AlgebraicClosure K) :=
  frobeniusScaling_of_galoisData W p r (frobeniusGaloisData_holds W p r)

end BaseChange

end HasseWeil.WeilPairing
