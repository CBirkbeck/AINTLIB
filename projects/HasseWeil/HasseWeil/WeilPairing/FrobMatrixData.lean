/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.HasseAssembly
import HasseWeil.IsogenyBaseChange

/-!
# Route 2A — the `F̄_q` base-change of the Frobenius representation: discharging `hres`

This file performs the **final geometric step** of the Weil-pairing route to the Hasse bound: it
supplies the per-`ℓ` Frobenius-matrix determinant data `hres` of `hasse_bound_via_weil_pairing`
(`HasseWeil/WeilPairing/HasseAssembly.lean`) by base-changing the elliptic curve `E/K` (`K = 𝔽_q`)
to the algebraic closure `K̄ = AlgebraicClosure K` and running the abstract Weil-pairing `DET-DEG`
machinery (`DetDeg.frob_det_residual_of_weil_scaling`) there.

## The reduction

Recall (`HasseAssembly.lean`) the hypothesis `hres` wants, for every separable `rπ − s` (`p ∤ s`)
and every auxiliary prime `ℓ ≠ p`, a matrix `M` over `ZMod ℓ` with

  `det M = q`,  `det(1 − M) = q + 1 − t (= #E)`,  `det(rM − sI) = deg r s`,

where `q = #K`, `t = isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq)` and `deg r s ≥ 0`.

The abstract bridge `DetDeg.frob_det_residual_of_weil_scaling`, run over the algebraically closed
`K̄`, produces **exactly** this existential from:

* a Frobenius `AddMonoidHom` `πbar` on `E_K̄.Point` (here the `q`-power Frobenius
  `frobeniusIsog_baseChange_charP_pow`, `IsogenyBaseChange.lean`);
* three natural degrees `dπ, d1, drs` and integer identifications
  `(dπ : ℤ) = q`, `(d1 : ℤ) = q + 1 − t`, `(drs : ℤ) = deg r s`;
* the three **per-isogeny Weil-pairing scalings** (`WeilScales`)
  `e_ℓ(ψ S, ψ T) = e_ℓ(S, T)^d` for `ψ ∈ {πbar, id − πbar, r·πbar − s·id}`.

**The degree identifications are pure arithmetic, discharged here in full.**  Indeed `dπ := q := #K`
gives `(dπ : ℤ) = q` definitionally; `d1 := (isogOneSub_negFrobenius W hq).degree` gives
`(d1 : ℤ) = q + 1 − t` because `t = 1 + #K − deg(1 − π)` *is* the definition of `isogTrace`; and
`drs := (deg r s).toNat` gives `(drs : ℤ) = deg r s` from `deg r s ≥ 0`.  Note in particular that
NO base-change degree-preservation lemma is required: the two K-level degrees `#K = deg π` and
`deg(1 − π)` feed `dπ`, `d1` directly through the trace identity, and `drs` is read straight off the
supplied non-negative degree function.

## The precise remaining geometric frontier

After this file, the **entire** remaining mathematical content of the unconditional Hasse bound is
the bundled leaf `FrobBaseChangeScalings` — the three per-`ℓ` Weil-pairing scalings for base-changed
Frobenius pencil over `K̄`.  Concretely:

* the **inseparable** Frobenius scaling `e_ℓ(πbar S, πbar T) = e_ℓ(S, T)^{#K}` is the
  **Galois/Frobenius equivariance** (Silverman III.8.1d: `e_ℓ(S^σ, T^σ) = e_ℓ(S, T)^σ` with
  `σ = q`-power Frobenius acting `ζ ↦ ζ^q` on `μ_ℓ`); it is *not yet* in the project (only mentioned
  in doc-comments), and is isolated below as the named leaf `weilPairing_frobenius_scaling`;
* the two **separable** scalings (`id − πbar`, `r·πbar − s·id`) are instances of the proven
  `weilPairing_scaling` (`PairingAdjoint.lean`) once the per-isogeny `picDual`/naturality/
  surjectivity witnesses are supplied for the base-changed pencil (the `hcomm`/`hfact`/`hdual` data,
  i.e. the resolved scaling of `weilPairing_scaling_of_genuine`).

These are carried as the single hypothesis `FrobBaseChangeScalings` of the capstone
`hasse_bound_unconditional_of_baseChange_scalings`, in the same style as the project's other
geometric residuals.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (the pairing + Galois equivariance),
  III.8.6 (`det φ_ℓ = deg φ`), V.1.1 / V.2.3.1 (the Hasse bound assembly).

## Name-clash note

`pullbackDivisor_kappaDivisor` is declared in both `HfactLemma.lean` and `PairingNondeg.lean`.  This
file imports neither directly: it imports only `HasseAssembly` (→ `DetDeg` → `PairingNondeg`, the
non-`HfactLemma` copy) and `IsogenyBaseChange`.  No clash arises and no rename was needed.
-/

open WeierstrassCurve Real Matrix

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

set_option linter.style.longLine false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

section BaseChange

/-! ### The base change to `K̄ = AlgebraicClosure K`

We fix the prime `p = ringChar K`, its exponent `r` (so `#K = p ^ r`), and the algebraic closure
`Kbar := AlgebraicClosure K`.  All the instances `DetDeg` needs over `Kbar` — `IsAlgClosed`,
`IsElliptic` and `IsIntegrallyClosed` of the base-changed curve, `(ℓ : Kbar) ≠ 0` — are derived
here. -/

/-- The `q`-power Frobenius `AddMonoidHom` on the `K̄`-points of `E`, for `K = 𝔽_{p^r}`.  This is the
underlying point map of `frobeniusIsog_baseChange_charP_pow`, the iterated relative `p`-Frobenius
endomorphism of `E_{K̄}` (`IsogenyBaseChange.lean`). -/
noncomputable def frobeniusHomBaseChange
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic] :
    (W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point :=
  (Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom

end BaseChange

/-! ### The bundled geometric leaf: the three Weil-pairing scalings over `K̄`

`FrobBaseChangeScalings` packages, per separable `(r,s)` and per prime `ℓ ≠ p`, the three
per-isogeny Weil-pairing scalings for the base-changed Frobenius pencil `{πbar, id − πbar,
r·πbar − s·id}` on `E_{K̄}[ℓ]`, with the prescribed exponents `#K`, `deg(1 − π)`, `(deg r s).toNat`.
This is the sole genuinely-geometric residual (see the module docstring). -/

/-- **Leaf 1 — the inseparable Frobenius scaling** (Silverman III.8.1d, the Galois/Frobenius
equivariance): `e_ℓ(πbar S, πbar T) = e_ℓ(S, T)^{#K}` on `E_{K̄}[ℓ]`, for every prime `ℓ ≠ p`.  Here
`πbar = frobeniusHomBaseChange` is the `q`-power Frobenius; the exponent `#K = q = deg π` is the
degree of (the inseparable) Frobenius.  This is the *only* one of the three scalings that is genuinely
new content: unfolding `WeilScales`, it is **exactly** Silverman's Prop III.8.1d,
`∀ S T, e_ℓ(πbar S, πbar T) = e_ℓ(S, T)^{#K}`, i.e. the Galois action `ζ ↦ ζ^q` on `μ_ℓ` — not
present in the project (only mentioned in `HasseAssembly.lean`'s doc-comments). -/
def FrobeniusScaling
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic] : Prop :=
  ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K → ∀ (hℓF : (ℓ : L) ≠ 0),
    letI : Fact ℓ.Prime := ⟨hℓp⟩
    WeilScales (W.baseChange L) ℓ hℓF (frobeniusHomBaseChange W p r L) (Fintype.card K)

/-- **Leaf 2 — the separable `1 − π` scaling** (Silverman III.8.6.1): `e_ℓ((id − πbar) S,
(id − πbar) T) = e_ℓ(S, T)^{deg(1 − π)}` on `E_{K̄}[ℓ]`, for every prime `ℓ ≠ p`.  The exponent is the
K-level degree `(isogOneSub_negFrobenius W hq).degree` (= `#E(𝔽_q)`).  This is an instance of the
*shipped* `weilPairing_scaling` (`PairingAdjoint.lean`) once the per-isogeny `picDual`/naturality/
surjectivity witnesses are supplied for the base-changed isogeny `(1 − π)_{K̄}` — which currently
requires the (not-yet-formalised) concrete `Isogeny.baseChange`. -/
def OneSubFrobeniusScaling
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) : Prop :=
  ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K → ∀ (hℓF : (ℓ : L) ≠ 0),
    letI : Fact ℓ.Prime := ⟨hℓp⟩
    WeilScales (W.baseChange L) ℓ hℓF
      (AddMonoidHom.id (W.baseChange L).toAffine.Point - frobeniusHomBaseChange W p r L)
      (isogOneSub_negFrobenius W hq).degree

/-- **Leaf 3 — the separable pencil `rπ − s` scaling** (Silverman III.8.6.1): `e_ℓ((r·πbar − s·id) S,
(r·πbar − s·id) T) = e_ℓ(S, T)^{(deg r s).toNat}` on `E_{K̄}[ℓ]`, for every separable `(r,s)` (`p ∤ s`)
and prime `ℓ ≠ p`.  The exponent `(deg r s).toNat` is read off the supplied non-negative degree
function (intended `deg r s = deg(rπ − s)`).  As with Leaf 2, an instance of the shipped
`weilPairing_scaling` once `(rπ − s)_{K̄}` is available as a concrete base-changed isogeny. -/
def PencilScaling
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (deg : ℤ → ℤ → ℤ) : Prop :=
  ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ s' → ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K →
    ∀ (hℓF : (ℓ : L) ≠ 0), letI : Fact ℓ.Prime := ⟨hℓp⟩
      WeilScales (W.baseChange L) ℓ hℓF
        (r' • frobeniusHomBaseChange W p r L -
          s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
        (deg r' s').toNat

/-- **Leaf 3, coprime-BOTH form** (reviewer round-23, Route B): the separable pencil `rπ − s` scaling
`e_ℓ((r·πbar − s·id) S, (r·πbar − s·id) T) = e_ℓ(S, T)^{(deg r s).toNat}` requested only on the
locus `p ∤ r' ∧ p ∤ s'` (both coordinates coprime to `p = ringChar K`).  This is the genuine /
canonical pencil locus: with `p ∤ r'` the pencil member `r'π − s'` is constructed from the canonical
genuine bundle `pencilScalingComapDataCard_canonical` — **no inseparable `p ∣ r'` input is required**,
so this leaf carries **no** `p ∣ r'` `sorry`.  Strictly weaker than `PencilScaling` (extra `¬p∣r'`
hypothesis). -/
def PencilScalingCoprime
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (deg : ℤ → ℤ → ℤ) : Prop :=
  ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ r' → ¬ ((ringChar K : ℤ)) ∣ s' →
    ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K →
    ∀ (hℓF : (ℓ : L) ≠ 0), letI : Fact ℓ.Prime := ⟨hℓp⟩
      WeilScales (W.baseChange L) ℓ hℓF
        (r' • frobeniusHomBaseChange W p r L -
          s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
        (deg r' s').toNat

/-- **The base-change Weil-pairing scaling leaf** (Silverman III.8.1d + III.8.6.1): the conjunction of
the three per-isogeny scalings `FrobeniusScaling`, `OneSubFrobeniusScaling`, `PencilScaling` for the
base-changed Frobenius pencil over `K̄`.  This is the sole genuinely-geometric residual of the
unconditional Hasse bound (see the module docstring). -/
def FrobBaseChangeScalings
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) : Prop :=
  FrobeniusScaling W p r L ∧ OneSubFrobeniusScaling W p r L hq ∧ PencilScaling W p r L deg

/-- **The base-change Weil-pairing scaling leaf, coprime-BOTH form** (reviewer round-23, Route B): the
conjunction of `FrobeniusScaling`, `OneSubFrobeniusScaling`, and the **coprime-BOTH** pencil scaling
`PencilScalingCoprime`.  This is the leaf the **axiom-clean** unconditional Hasse bound consumes:
leaves 1 and 2 are unchanged (axiom-clean), and the pencil leaf is required only on `p ∤ r' ∧ p ∤ s'`,
discharged by the canonical genuine bundle with **no** `p ∣ r'` `sorry`. -/
def FrobBaseChangeScalingsCoprime
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) : Prop :=
  FrobeniusScaling W p r L ∧ OneSubFrobeniusScaling W p r L hq ∧ PencilScalingCoprime W p r L deg

/-! ### The trace identity `#K + 1 − t = deg(1 − π)`

Pure arithmetic from the definition of `isogTrace` (`= 1 + deg π − deg(1 − π)`) and
`deg π = #K` (`frobeniusIsog_degree`).  This is what lets `d1 := deg(1 − π)` discharge the
`(d1 : ℤ) = q + 1 − t` identification of `frob_det_residual_of_weil_scaling` with no base-change
degree-preservation lemma. -/
omit [Fintype W.toAffine.Point] in
theorem card_add_one_sub_isogTrace_eq_degree (hq : 2 ≤ Fintype.card K) :
    (Fintype.card K + 1 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) =
      ((isogOneSub_negFrobenius W hq).degree : ℤ) := by
  unfold isogTrace
  rw [frobeniusIsog_degree]
  ring

/-! ### The `hres` existential over `K̄`

For a fixed prime `ℓ ≠ p` with `(ℓ : K̄) ≠ 0`, the abstract Weil-pairing
`frob_det_residual_of_weil_scaling`, applied to the base-changed Frobenius pencil over `K̄`, yields
the Frobenius matrix `M` over `ZMod ℓ` with the three determinant identities, with `q = #K`,
`t = isogTrace`, `Dν = deg r s`. The three degree identifications are discharged here by pure
arithmetic (the trace identity above + `(deg r s).toNat` cast). -/
omit [Fintype W.toAffine.Point] in
theorem frob_det_residual_baseChange
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (r' s' : ℤ) (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓF : (ℓ : L) ≠ 0)
    (hsc :
      letI : Fact ℓ.Prime := ⟨hℓp⟩
      WeilScales (W.baseChange L) ℓ hℓF (frobeniusHomBaseChange W p r L) (Fintype.card K) ∧
        WeilScales (W.baseChange L) ℓ hℓF
          (AddMonoidHom.id (W.baseChange L).toAffine.Point - frobeniusHomBaseChange W p r L)
          (isogOneSub_negFrobenius W hq).degree ∧
        WeilScales (W.baseChange L) ℓ hℓF
          (r' • frobeniusHomBaseChange W p r L -
            s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
          (deg r' s').toNat) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
      (1 - M).det = ((Fintype.card K + 1 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
      ((r' : ZMod ℓ) • M - (s' : ZMod ℓ) • 1).det = (deg r' s' : ZMod ℓ) := by
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨hπ, h1, hrs⟩ := hsc
  -- `(drs : ℤ) = deg r' s'` from `deg ≥ 0`.
  have hDd : ((deg r' s').toNat : ℤ) = deg r' s' := Int.toNat_of_nonneg (hdeg_nonneg r' s')
  exact frob_det_residual_of_weil_scaling (W.baseChange L) ℓ hℓF
    (frobeniusHomBaseChange W p r L)
    (Fintype.card K)
    (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))
    (deg r' s') r' s'
    (Fintype.card K) (isogOneSub_negFrobenius W hq).degree (deg r' s').toNat
    rfl
    (card_add_one_sub_isogTrace_eq_degree W hq).symm
    hDd
    hπ h1 hrs

/-! ### `(ℓ : L) ≠ 0` for `ℓ ≠ p` prime over a char-`p` field

If `L` has characteristic `p` (`CharP L p`, `p` prime) and `ℓ` is a prime `≠ p`, then the image of
`ℓ` in `L` is nonzero (a different prime is not a multiple of `p`). -/
theorem natCast_ne_zero_of_prime_ne_ringChar
    {p : ℕ} (hp : p.Prime) (L : Type*) [Field L] [CharP L p]
    (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓne : ℓ ≠ p) : (ℓ : L) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff L p ℓ]
  intro hdvd
  exact hℓne (((Nat.prime_dvd_prime_iff_eq hp hℓp).mp hdvd).symm)

/-! ### The full `hres` over `K̄`

Assembling `frob_det_residual_baseChange` across all `(r,s,ℓ)` with `p ∤ s`, `ℓ ≠ p`, gives the exact
`hres` hypothesis of `hasse_bound_via_weil_pairing` — from the single geometric leaf
`FrobBaseChangeScalings`.  The `(ℓ : K̄) ≠ 0` side-condition is discharged from `ℓ ≠ p`
(`natCast_ne_zero_of_prime_ne_ringChar`, using `ringChar K = p`). -/
omit [Fintype W.toAffine.Point] in
theorem hres_of_baseChange_scalings
    (p r : ℕ) [hp : Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hpchar : ringChar K = p)
    (hscale : FrobBaseChangeScalings W p r L hq deg) :
    ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ s' → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r' : ZMod ℓ) • M - (s' : ZMod ℓ) • 1).det = (deg r' s' : ZMod ℓ) := by
  haveI : CharP L p := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K L) p
  obtain ⟨hFrob, hOneSub, hPencil⟩ := hscale
  intro r' s' hps ℓ hℓp hℓne
  have hℓF : (ℓ : L) ≠ 0 :=
    natCast_ne_zero_of_prime_ne_ringChar hp.out L ℓ hℓp (by rwa [hpchar] at hℓne)
  exact frob_det_residual_baseChange W p r L hq deg hdeg_nonneg r' s' ℓ hℓp hℓF
    ⟨hFrob ℓ hℓp hℓne hℓF, hOneSub ℓ hℓp hℓne hℓF, hPencil r' s' hps ℓ hℓp hℓne hℓF⟩

/-! ### The full coprime-BOTH `hres` over `K̄`

Mirror of `hres_of_baseChange_scalings` for the coprime-BOTH leaf: assembling
`frob_det_residual_baseChange` across all `(r', s', ℓ)` with `p ∤ r'`, `p ∤ s'`, `ℓ ≠ p`, gives the
coprime-BOTH `hres` of `hasse_bound_via_weil_pairing_both` — from `FrobBaseChangeScalingsCoprime`.
The pencil scaling is now invoked only on `p ∤ r' ∧ p ∤ s'` (`hPencil r' s' hpr hps`). -/
omit [Fintype W.toAffine.Point] in
theorem hres_of_baseChange_scalings_coprime
    (p r : ℕ) [hp : Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hpchar : ringChar K = p)
    (hscale : FrobBaseChangeScalingsCoprime W p r L hq deg) :
    ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ r' → ¬ ((ringChar K : ℤ)) ∣ s' →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r' : ZMod ℓ) • M - (s' : ZMod ℓ) • 1).det = (deg r' s' : ZMod ℓ) := by
  haveI : CharP L p := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K L) p
  obtain ⟨hFrob, hOneSub, hPencil⟩ := hscale
  intro r' s' hpr hps ℓ hℓp hℓne
  have hℓF : (ℓ : L) ≠ 0 :=
    natCast_ne_zero_of_prime_ne_ringChar hp.out L ℓ hℓp (by rwa [hpchar] at hℓne)
  exact frob_det_residual_baseChange W p r L hq deg hdeg_nonneg r' s' ℓ hℓp hℓF
    ⟨hFrob ℓ hℓp hℓne hℓF, hOneSub ℓ hℓp hℓne hℓF, hPencil r' s' hpr hps ℓ hℓp hℓne hℓF⟩

/-! ### The unconditional Hasse bound from the base-change scaling leaf

`|#E(𝔽_q) − q − 1| ≤ 2√q`, assembled from the single geometric leaf `FrobBaseChangeScalings` over
`K̄ = AlgebraicClosure K` via `hres_of_baseChange_scalings` and the shipped
`hasse_bound_via_weil_pairing`.  All the `K̄` instances (`IsAlgClosed`, `ExpChar`, the base-changed
curve elliptic, the field structure) are derived here from `FiniteField.card' K`. -/
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

theorem hasse_bound_unconditional_of_baseChange_scalings
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hscale : ∀ (p r : ℕ) (_ : Fact p.Prime) (_ : CharP K p) (_ : Fact (Fintype.card K = p ^ r)),
      FrobBaseChangeScalings W p r (AlgebraicClosure K) hq deg) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by
  obtain ⟨p, hCharP, ⟨n, _hn⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP K p := hCharP
  haveI : Fact (Fintype.card K = p ^ (n : ℕ)) := ⟨hcard⟩
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; exact hCharP
  -- The algebraic closure `K̄` and its instances.
  haveI : ExpChar (AlgebraicClosure K) p :=
    haveI : CharP (AlgebraicClosure K) p :=
      charP_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) p
    ExpChar.prime hp_prime
  haveI : (W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic := inferInstance
  exact hasse_bound_via_weil_pairing W hq deg hdeg_nonneg
    (hres_of_baseChange_scalings W p (n : ℕ) (AlgebraicClosure K) hq deg hdeg_nonneg hpchar
      (hscale p (n : ℕ) ⟨hp_prime⟩ hCharP ⟨hcard⟩))

/-- **The unconditional Hasse bound from the coprime-BOTH base-change scaling leaf** (reviewer
round-23, Route B).

`|#E(𝔽_q) − q − 1| ≤ 2√q`, assembled from the single leaf `FrobBaseChangeScalingsCoprime` over
`K̄ = AlgebraicClosure K` via `hres_of_baseChange_scalings_coprime` and the coprime-BOTH
`hasse_bound_via_weil_pairing_both`.  This is the **axiom-clean** capstone: the pencil scaling is
requested only on the genuine locus `p ∤ r' ∧ p ∤ s'`, so the inseparable `p ∣ r'` `sorry` is never
demanded.  Identical instance bookkeeping to `hasse_bound_unconditional_of_baseChange_scalings`. -/
theorem hasse_bound_unconditional_of_baseChange_scalings_coprime
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hscale : ∀ (p r : ℕ) (_ : Fact p.Prime) (_ : CharP K p) (_ : Fact (Fintype.card K = p ^ r)),
      FrobBaseChangeScalingsCoprime W p r (AlgebraicClosure K) hq deg) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by
  obtain ⟨p, hCharP, ⟨n, _hn⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP K p := hCharP
  haveI : Fact (Fintype.card K = p ^ (n : ℕ)) := ⟨hcard⟩
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; exact hCharP
  haveI : ExpChar (AlgebraicClosure K) p :=
    haveI : CharP (AlgebraicClosure K) p :=
      charP_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) p
    ExpChar.prime hp_prime
  haveI : (W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic := inferInstance
  exact hasse_bound_via_weil_pairing_both W hq deg hdeg_nonneg
    (hres_of_baseChange_scalings_coprime W p (n : ℕ) (AlgebraicClosure K) hq deg hdeg_nonneg hpchar
      (hscale p (n : ℕ) ⟨hp_prime⟩ hCharP ⟨hcard⟩))

end HasseWeil.WeilPairing
