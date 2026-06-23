/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.GapSpines
import HasseWeil.WeilPairing.PencilDualDivisor
import HasseWeil.WeilPairing.IsogenyWitnessReductions
import HasseWeil.WeilPairing.OmegaBaseChange

/-!
# Separability of the base-changed pencil `(rπ − s)_{K̄}` (Silverman III.5.5)

The K-level separability of the genuine `r·π − s` isogeny is the substantive Silverman III.5.5
content: `a_{rπ − s} = r·a_π − s = −s ≠ 0` for `p ∤ s` (`HasseWeil.genuineIsogSmulSub_isSeparable`,
built from the general-pair III.5.2 additivity `omegaPullbackCoeff_addIsog_pair`).

This file carries that separability to the algebraic closure `K̄` for the *concrete* base-changed
pencil pullback `pencilBaseChangePullback := baseChangePullback (rπ − s).pullback` (the canonical
`pullback_L` for `PencilScalingData`, mirroring `oneSubFrobeniusPullback_L` for `1 − π`).  The
only remaining ingredient is the **base-change non-vanishing of the invariant-differential pullback
coefficient** — `omegaPullbackCoeff f ≠ 0 → omegaPullbackCoeff (baseChangePullback f) ≠ 0` — the
function-field-tensor naturality of the invariant differential `φ^*ω = a_φ·ω`.

## The transport (now DISCHARGED)

`OmegaBaseChangeNeZero` is the minimal naturality fact: an isogeny with non-vanishing
`omegaPullbackCoeff` (i.e. separable over `K`) stays so after base change.  It is **DISCHARGED**
(`omegaBaseChangeNeZero_holds`) from the omega-coefficient **value** transport
`omegaPullbackCoeff (E_L) α_L = functionFieldMap (omegaPullbackCoeff E α)`
(`omegaPullbackCoeff_baseChangePullback`, `WeilPairing/OmegaBaseChange.lean`): the invariant
differential transports along `KaehlerDifferential.map K L K(E) K(E_L)`, the pullback compatibility is
`baseChangePullback_functionFieldMap`, and `functionFieldMap` is injective, so `≠ 0` carries.  It is
the differential analogue of the **degree** base change `baseChangePullback_finrank_eq`
(`finrankBaseChange`).  `genuineIsogSmulSub_isSeparable` supplies the `K`-level value, so
`pencilIsogBaseChange_isSeparable` is **unconditional** and feeds
`pencil_hkerdeg_of_separable_witnesses`'s `hsep` (see `pencil_hkerdeg_galois`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.5.2, III.5.3, III.5.5.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [Algebra.IsAlgebraic K L] [ExpChar L p]
  [(W.baseChange L).toAffine.IsElliptic]

/-- **The concrete base-changed pencil pullback** `(rπ − s)_{K̄}^*` (CoordHom-free): the conjugate
`Φ ∘ (id_L ⊗ (rπ − s).pullback) ∘ Φ⁻¹` of the genuine `K`-level `r·π − s` pullback.  This is the
canonical `pullback_L` field for `PencilScalingData`, mirroring `oneSubFrobeniusPullback_L` for the
`1 − π` leaf. -/
noncomputable def pencilBaseChangePullback
    (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (W.baseChange L).toAffine.FunctionField →ₐ[L] (W.baseChange L).toAffine.FunctionField :=
  baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L
    (genuineIsogSmulSub W r' s' hr hs hrK hsK).pullback

/-- **The base-change naturality statement** (`OmegaBaseChangeNeZero`), now **DISCHARGED** by
`omegaBaseChangeNeZero_holds`: the invariant-differential pullback coefficient stays nonzero after
base change.  For an isogeny `α : E → E` over `K` with `a_α = omegaPullbackCoeff W α ≠ 0` (i.e. `α`
separable over `K`), the base-changed pullback `baseChangePullback α.pullback` over `L` again has
non-vanishing omega-coefficient.

This is the differential analogue of the finrank base change `baseChangePullback_finrank_eq`.  The
proof is the omega-coefficient **value** transport
`omegaPullbackCoeff (E_L) α_L = functionFieldMap (omegaPullbackCoeff E α)`
(`omegaPullbackCoeff_baseChangePullback`, via `KaehlerDifferential.map K L K(E) K(E_L)` and
`baseChangePullback_functionFieldMap`) plus injectivity of `functionFieldMap`.  Kept as a named
`Prop` only to read the statement; it is no longer carried by any downstream consumer. -/
def OmegaBaseChangeNeZero : Prop :=
  ∀ (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (α : Isogeny W.toAffine W.toAffine),
    α_L.pullback =
      baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback →
    omegaPullbackCoeff W α ≠ 0 →
    omegaPullbackCoeff (W.baseChange L) α_L ≠ 0

/-- **`OmegaBaseChangeNeZero` is DISCHARGED** (no longer carried): the invariant-differential
pullback coefficient stays nonzero after base change, because it transports *by value* —
`omegaPullbackCoeff (E_L) α_L = functionFieldMap (omegaPullbackCoeff E α)`
(`omegaPullbackCoeff_baseChangePullback`, the differential analogue of the finrank base change) — and
`functionFieldMap` is injective, so `≠ 0` carries.  This is the proved fact behind the named leaf;
all downstream consumers can use it instead of carrying the `Prop`. -/
theorem omegaBaseChangeNeZero_holds : OmegaBaseChangeNeZero W L := by
  intro α_L α hpb hα
  rw [omegaPullbackCoeff_baseChangePullback W L α α_L hpb]
  exact fun h0 ↦ hα (map_eq_zero_iff _
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap_injective L) |>.mp h0)

/-- **K̄-separability of the base-changed pencil from the isolated transport** (Silverman III.5.5,
base-change form), CoordHom-free.  Given the base-change naturality leaf `OmegaBaseChangeNeZero`, the
concrete base-changed pencil `pencilIsogBaseChange ... (pencilBaseChangePullback …)` over `L` is
separable, because:

* the `K`-level genuine `r·π − s` is separable, i.e. `omegaPullbackCoeff W (rπ − s) ≠ 0`
  (`genuineIsogSmulSub_isSeparable` via `omegaPullbackCoeff_addIsog_pair`, **the substantive
  Silverman III.5.5 content, axiom-clean**);
* the leaf transports `≠ 0` across base change to `omegaPullbackCoeff (E_L) (pencilIsog…) ≠ 0`;
* `isSeparable_iff_omegaPullbackCoeff_ne_zero` over `L` concludes `IsSeparable`.

This **discharges the `hsep` hypothesis** of `pencil_hkerdeg_of_separable_witnesses` /
`pencil_hkerdeg_of_hgcomm_separable` (the K̄-level separability of `(rπ − s)_{K̄}`), reducing it to
the single base-change transport `OmegaBaseChangeNeZero`. -/
theorem pencilIsogBaseChange_isSeparable_of_omegaBaseChange
    (hbc : OmegaBaseChangeNeZero W L)
    (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (pencilIsogBaseChange W p r L r' s'
      (pencilBaseChangePullback W L r' s' hr hs hrK hsK)).IsSeparable := by
  -- The K-level genuine `r·π − s` is separable (the substantive III.5.5 content).
  have hK : omegaPullbackCoeff W (genuineIsogSmulSub W r' s' hr hs hrK hsK) ≠ 0 :=
    (isSeparable_iff_omegaPullbackCoeff_ne_zero W
      (genuineIsogSmulSub W r' s' hr hs hrK hsK)).mp
      (genuineIsogSmulSub_isSeparable W r' s' hr hs hrK hsK)
  -- Transport `≠ 0` across base change via the isolated leaf.
  have hL : omegaPullbackCoeff (W.baseChange L)
      (pencilIsogBaseChange W p r L r' s' (pencilBaseChangePullback W L r' s' hr hs hrK hsK)) ≠ 0 := by
    refine hbc _ (genuineIsogSmulSub W r' s' hr hs hrK hsK) ?_ hK
    rw [pencilIsogBaseChange_pullback]
    rfl
  -- `IsSeparable` over `L` from `omegaPullbackCoeff ≠ 0`.
  exact (isSeparable_iff_omegaPullbackCoeff_ne_zero (W.baseChange L)
    (pencilIsogBaseChange W p r L r' s' (pencilBaseChangePullback W L r' s' hr hs hrK hsK))).mpr hL

/-- **K̄-separability of the base-changed pencil — UNCONDITIONAL** (Silverman III.5.5).  The
`OmegaBaseChangeNeZero` hypothesis of `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` is
discharged by the proved `omegaBaseChangeNeZero_holds` (the omega-coefficient value transport), so
the base-changed pencil `(rπ − s)_{K̄}` is separable with no carried base-change leaf. -/
theorem pencilIsogBaseChange_isSeparable
    (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (pencilIsogBaseChange W p r L r' s'
      (pencilBaseChangePullback W L r' s' hr hs hrK hsK)).IsSeparable :=
  pencilIsogBaseChange_isSeparable_of_omegaBaseChange W p r L
    (omegaBaseChangeNeZero_holds W L) r' s' hr hs hrK hsK

/-! ### Wiring: the pencil `#ker = deg` field with `hsep` discharged

Combining `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` with the general separable Galois
fibre-count `pencil_hkerdeg_of_separable_witnesses` removes the carried `hsep` hypothesis from the
pencil `hkerdeg` field — it is now *derived* from the base-change transport leaf
`OmegaBaseChangeNeZero` plus the (axiom-clean) `K`-level separability.  The remaining inputs
`h_normal` / `h_card` are the standard Galois-correspondence facts (Silverman III.4.10a), carried as
before. -/

section AlgClosure

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPencilSep : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **Pencil `#ker = deg` for `(rπ − s)_{K̄}` with `hsep` discharged via the base-change transport**
(Silverman III.4.10c), CoordHom-free.  For the *canonical* base-changed pullback
`pencilBaseChangePullback` (= `baseChangePullback (rπ − s).pullback`), the separable degree match
`#ker = deg` follows from:

* `hbc` — the isolated base-change naturality leaf `OmegaBaseChangeNeZero` (carries `K`-separability
  to `K̄`; the only deep transport, analogue of the finrank base change);
* `h_normal` / `h_card` — the standard Galois-correspondence inputs (Silverman III.4.10a).

The `hsep` input of `pencil_hkerdeg_of_separable_witnesses` is now *derived* from `hbc` + the
axiom-clean `K`-level `genuineIsogSmulSub_isSeparable` (Silverman III.5.5,
`omegaPullbackCoeff_addIsog_pair`), so it no longer appears as a separate parametric hypothesis. -/
theorem pencil_hkerdeg_of_omegaBaseChange_galois
    (hbc : OmegaBaseChangeNeZero W (AlgebraicClosure K))
    (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (h_normal : letI := (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAlgebra
      Normal (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (h_card :
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).kernel =
        Nat.card (@AlgEquiv
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField _ _ _
          (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAlgebra
          (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAlgebra)) :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).degree :=
  pencil_hkerdeg_of_separable_witnesses W p r r' s'
    (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)
    (pencilIsogBaseChange_isSeparable_of_omegaBaseChange W p r (AlgebraicClosure K) hbc
      r' s' hr hs hrK hsK)
    h_normal h_card

/-- **Pencil `#ker = deg` for `(rπ − s)_{K̄}` with `hbc` DISCHARGED** (Silverman III.4.10c),
CoordHom-free.  Identical to `pencil_hkerdeg_of_omegaBaseChange_galois` but with the base-change
transport leaf `OmegaBaseChangeNeZero` *no longer carried* — it is supplied by the proved
`omegaBaseChangeNeZero_holds` (the omega-coefficient value transport
`omegaPullbackCoeff_baseChangePullback`).  Only the standard Galois-correspondence inputs
`h_normal` / `h_card` (Silverman III.4.10a) remain. -/
theorem pencil_hkerdeg_galois
    (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (h_normal : letI := (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAlgebra
      Normal (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (h_card :
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).kernel =
        Nat.card (@AlgEquiv
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField _ _ _
          (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAlgebra
          (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAlgebra)) :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).degree :=
  pencil_hkerdeg_of_omegaBaseChange_galois W p r
    (omegaBaseChangeNeZero_holds W (AlgebraicClosure K)) r' s' hr hs hrK hsK h_normal h_card

end AlgClosure

end HasseWeil.WeilPairing
