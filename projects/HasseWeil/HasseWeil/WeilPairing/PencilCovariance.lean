/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.MapTranslateGenericAdditive
import HasseWeil.WeilPairing.FrobeniusGenericCovariance
import HasseWeil.WeilPairing.SeparableWitnesses
import HasseWeil.WeilPairing.PencilSeparable
import HasseWeil.WeilPairing.WallAGeometricRealization

/-!
# The generic-point covariance `hgcomm` for `(rπ − s)_{K̄}`, fully discharged (CoordHom-free)

This file discharges the translation covariance `hcomm'` (witness 3 of `PencilScalingData`) for the
base-changed separable pencil `(rπ − s)_{K̄}` over `L = AlgebraicClosure K`, with **no carried
`hgcomm` hypothesis** — the exact analogue of the `1 − π` Wall A discharge
`oneSub_hcommPrime_discharged` (`WallAGeometricRealization.lean`).

## The route (reviewer round-21 structural decomposition of `hgcomm`)

`rπ − s = addIsog(r·π, −s·id)`, so the generic-point covariance leaf `MapTranslateGenericPoint`
reduces (via `mapTranslateGenericPoint_add`, `MapTranslateGenericAdditive.lean`) to the two component
leaves:

* the `r·π` component: `MapTranslateGenericPoint (π.zsmul r) (r • frobₗ)`, obtained by `zsmul`-ing
  the **proved** Frobenius covariance `mapTranslateGenericPoint_frobenius_Kbar`
  (`FrobeniusGenericCovariance.lean`) through the general `mapTranslateGenericPoint_zsmul`;
* the `−s·id` component: `MapTranslateGenericPoint (mulByInt (−s)) (Point.map [−s]^*)`, the free
  `[m]` covariance `mapTranslateGenericPoint_mulByInt` (from `ScratchCov.map_pullback_genericPoint`
  + the master translation lemma).

The canonical-action form (the one the `SeparableWitnesses` reductions consume) follows via
`mapTranslateGenericPoint_canonical_of_genuine` from the Wall A pencil genuineness
`pencil_isGenuineWith_Kbar`: the concrete base-changed pullback `pencilBaseChangePullback =
baseChangePullback (rπ − s).pullback` is genuine with the geometric action `r·frobₗ + [−s]`, because
on the generic coordinates `pencilBaseChangePullback ?_gen = functionFieldMap ((rπ − s)^K.pullback
?_gen)` (`baseChangePullback_functionFieldMap`) and the `K`-level `genuineIsogSmulSub` is genuine with
the corresponding `K`-level action (`genuineIsogSmulSub_isGenuineWith`), transported by the
function-field base change.

Everything is **CoordHom-free**: the realisation goes purely through `functionFieldMap` (the natural
function-field inclusion) and the proved Frobenius generic-point covariance over `K̄`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.5.2 (the differential additivity), III.8.2
  (translation covariance), I.2 (base change).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

/-! ### The `zsmul` and `mulByInt` component leaves (general field) -/

section General

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- (Inlined from the unbuildable `ScratchCov.lean`.)  Translating the image `[ℓ](P_gen)` by `S`
gives `[ℓ]P_gen + lift(ℓ•S)`.  Pure additivity of `Point.map τ_S`. -/
private theorem map_translate_smul_genericPoint (ℓ : ℤ) (S : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W) (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom
        (ℓ • HasseWeil.genericPoint W) =
      ℓ • HasseWeil.genericPoint W + HasseWeil.liftPointToKE W (ℓ • S) := by
  set m : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom
      with hm
  have hmaster : m (HasseWeil.genericPoint W) =
      HasseWeil.genericPoint W + HasseWeil.liftPointToKE W S := by
    rw [hm]; exact HasseWeil.translateAlgEquivOfPoint_map_genericPoint W S
  calc m (ℓ • HasseWeil.genericPoint W)
      = ℓ • m (HasseWeil.genericPoint W) := map_zsmul m ℓ _
    _ = ℓ • (HasseWeil.genericPoint W + HasseWeil.liftPointToKE W S) := by rw [hmaster]
    _ = ℓ • HasseWeil.genericPoint W + ℓ • HasseWeil.liftPointToKE W S := zsmul_add _ _ _
    _ = ℓ • HasseWeil.genericPoint W + HasseWeil.liftPointToKE W (ℓ • S) := by rw [map_zsmul]

/-- **The generic-point covariance leaf is preserved by `zsmul` of the isogeny** (Silverman III.8.2 +
III.4.2(b)).  If `g` satisfies the generic-point covariance against `φ`, then `m • g` satisfies it
against `φ.zsmul m` (whose point map is `[m] ∘ φ`).

Pure additive bookkeeping: `Point.map τ_S` and `liftPointToKE` are `AddMonoidHom`s, so `m`-scaling
commutes through them; the component covariance `h S` rewrites the scaled image; and
`(φ.zsmul m).toAddMonoidHom S = m • φ.toAddMonoidHom S` (`zsmul_apply`) recombines the lift. -/
theorem mapTranslateGenericPoint_zsmul (φ : Isogeny W.toAffine W.toAffine)
    (g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point) (m : ℤ)
    (h : MapTranslateGenericPoint W φ g) :
    MapTranslateGenericPoint W (φ.zsmul m) (m • g) := by
  intro S
  set τ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (translateAlgEquivOfPoint W S).toAlgHom with hτ
  -- `(m • g) P_gen = m • (g P_gen)` and `(φ.zsmul m) S = m • φ S` are `rfl`/`zsmul_apply`.
  have e1 : (m • g) (genericPoint W) = m • g (genericPoint W) := rfl
  have e2 : (φ.zsmul m).toAddMonoidHom S = m • φ.toAddMonoidHom S := Isogeny.zsmul_apply m φ S
  have hS : τ (g (genericPoint W)) =
      g (genericPoint W) + liftPointToKE W (φ.toAddMonoidHom S) := h S
  have hlift : liftPointToKE W (m • φ.toAddMonoidHom S) =
      m • liftPointToKE W (φ.toAddMonoidHom S) :=
    (liftPointToKE W).map_zsmul m (φ.toAddMonoidHom S)
  calc τ ((m • g) (genericPoint W))
      = τ (m • g (genericPoint W)) := by rw [e1]
    _ = m • τ (g (genericPoint W)) := map_zsmul τ m (g (genericPoint W))
    _ = m • (g (genericPoint W) + liftPointToKE W (φ.toAddMonoidHom S)) := by rw [hS]
    _ = m • g (genericPoint W) + m • liftPointToKE W (φ.toAddMonoidHom S) := by module
    _ = (m • g) (genericPoint W) + liftPointToKE W ((φ.zsmul m).toAddMonoidHom S) := by
          rw [e1, e2, hlift]

/-- **The `[m]` generic-point covariance leaf** (Silverman III.8.2 for `[m]`), for the **geometric**
action `g = zsmulPointHom m` (`P ↦ m • P`, the genuine action of `[m]`, `mulByInt_isGenuineWith`).
Directly the master translation lemma scaled: `Point.map τ_S (m • P_gen) = m • P_gen + lift (m • S)`
(`map_translate_smul_genericPoint`), and `[m] S = m • S`, `(zsmulPointHom m) P_gen = m • P_gen`. -/
theorem mapTranslateGenericPoint_mulByInt (m : ℤ) :
    MapTranslateGenericPoint W (mulByInt W.toAffine m) (zsmulPointHom W m) := by
  intro S
  -- `(zsmulPointHom m) P_gen = m • P_gen` (`rfl`), then the scaled master lemma.
  show WeierstrassCurve.Affine.Point.map (W' := W) (translateAlgEquivOfPoint W S).toAlgHom
      (m • genericPoint W) = m • genericPoint W + liftPointToKE W ((mulByInt W.toAffine m).toAddMonoidHom S)
  rw [map_translate_smul_genericPoint W m S, mulByInt_apply]

end General

/-! ### Wall A pencil genuineness and the assembled covariance over `K̄` -/

section Pencil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPC : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **The geometric `K̄`-action `r·frobₗ + [−s]`** for `(rπ − s)_{K̄}`: the function-field point map
`r • frobFunctionFieldPointKbar + (· ↦ (−s)•·)` on `E_{K̄}`-points (the second summand the genuine
`[−s]` action `zsmulPointHom`).  This is the *translatable* geometric action realising the
base-changed pencil; it equals the function-field base change of the `K`-level `genuineIsogSmulSub`
action. -/
noncomputable def gKbarPencil (r' s' : ℤ) :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point :=
  r' • frobFunctionFieldPointKbar W + zsmulPointHom (W.baseChange (AlgebraicClosure K)) (-s')

/-- **The point-map sum decomposition of `pencilIsogBaseChange`** as `(r·π̄) + [−s]`, at the
`AddMonoidHom` level.  Reads `r' • π̄ − s' • id = (r·π).toAddMonoidHom + [−s].toAddMonoidHom`
pointwise (`frobeniusHomBaseChange`, `zsmul_apply`, `mulByInt_apply`). -/
theorem pencilIsogBaseChange_toAddMonoidHom_decomp (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom =
      ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K)).zsmul r').toAddMonoidHom +
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).toAddMonoidHom := by
  rw [pencilIsogBaseChange_toAddMonoidHom]
  ext P
  rw [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, Isogeny.zsmul_apply,
    mulByInt_apply, AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
  -- `r' • π̄ P - s' • P = r' • (π̄ P) + (-s') • P`.
  show r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) P - s' • P =
    r' • (Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K)).toAddMonoidHom P +
      (-s') • P
  rw [show (Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K)).toAddMonoidHom P =
      frobeniusHomBaseChange W p r (AlgebraicClosure K) P from rfl, neg_smul]
  abel

/-- **`gKbarPencil` satisfies the generic-point covariance leaf** (Silverman III.8.2), via the
additive decomposition `mapTranslateGenericPoint_add`: the `r·π` component is the `zsmul` of the
proved Frobenius covariance `mapTranslateGenericPoint_frobenius_Kbar`, the `−s·id` component is the
free `[m]` leaf `mapTranslateGenericPoint_mulByInt`.  Holds against any isogeny whose point map is
`r·π̄ + [−s]` — in particular `pencilIsogBaseChange r' s' pullback_L`. -/
theorem mapTranslateGenericPoint_gKbarPencil (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
      (gKbarPencil W r' s') :=
  mapTranslateGenericPoint_add (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
    ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K)).zsmul r')
    (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s'))
    (r' • frobFunctionFieldPointKbar W)
    (zsmulPointHom (W.baseChange (AlgebraicClosure K)) (-s'))
    (pencilIsogBaseChange_toAddMonoidHom_decomp W p r r' s' pullback_L)
    (mapTranslateGenericPoint_zsmul (W.baseChange (AlgebraicClosure K))
      (Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K))
      (frobFunctionFieldPointKbar W) r'
      (mapTranslateGenericPoint_frobenius_Kbar W p r))
    (mapTranslateGenericPoint_mulByInt (W.baseChange (AlgebraicClosure K)) (-s'))

/-! ### Wall A pencil genuineness and the canonical-action covariance -/

set_option maxHeartbeats 1000000 in
/-- **`gKbarPencil` at the generic point is the function-field base change of the `K`-level
`genuineIsogSmulSub` action** (Silverman III.8.2, base change).  The `K`-level genuine action is
`gK = r·(frobeniusW_KE) + [−s]` (`genuineIsogSmulSub_isGenuineWith`); `ffBaseChangePoint` is additive
and `zsmul`-compatible, intertwines `frobeniusW_KE` with `frobₗ` (`ffbc_frob_comm`) and sends `P_gen`
to `P_gen^{K̄}` (`ffBaseChangePoint_genericPoint`), so
`gKbarPencil (P_gen^{K̄}) = ffBaseChangePoint (gK (P_gen))`. -/
theorem gKbarPencil_genericPoint (r' s' : ℤ) :
    gKbarPencil W r' s' (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      ffBaseChangePoint W (AlgebraicClosure K)
        ((((zsmulPointHom W r').comp (frobeniusW_KE W)) + zsmulPointHom W (-s'))
          (HasseWeil.genericPoint W)) := by
  -- RHS: `ffBaseChange ((r·π + [−s]) P_gen) = ffBaseChange (r • frobeniusW_KE P_gen + (-s) • P_gen)`.
  have hrhs : ((((zsmulPointHom W r').comp (frobeniusW_KE W)) + zsmulPointHom W (-s'))
        (HasseWeil.genericPoint W)) =
      r' • frobeniusW_KE W (genericPoint W) + (-s') • genericPoint W := by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, zsmulPointHom_apply]
  -- `ffBaseChange` is additive and `zsmul`-compatible (term-mode to dodge the smul diamond).
  have hadd : ffBaseChangePoint W (AlgebraicClosure K)
        (r' • frobeniusW_KE W (genericPoint W) + (-s') • genericPoint W) =
      ffBaseChangePoint W (AlgebraicClosure K) (r' • frobeniusW_KE W (genericPoint W)) +
        ffBaseChangePoint W (AlgebraicClosure K) ((-s') • genericPoint W) :=
    map_add _ _ _
  have hz1 : ffBaseChangePoint W (AlgebraicClosure K) (r' • frobeniusW_KE W (genericPoint W)) =
      r' • ffBaseChangePoint W (AlgebraicClosure K) (frobeniusW_KE W (genericPoint W)) :=
    map_zsmul _ r' _
  have hz2 : ffBaseChangePoint W (AlgebraicClosure K) ((-s') • genericPoint W) =
      (-s') • ffBaseChangePoint W (AlgebraicClosure K) (genericPoint W) := map_zsmul _ (-s') _
  -- LHS `gKbarPencil P_gen^{K̄} = r' • frobₗ P_gen^{K̄} + (-s') • P_gen^{K̄}` (`rfl`).
  have hlhs : gKbarPencil W r' s' (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      r' • frobFunctionFieldPointKbar W (genericPoint (W.baseChange (AlgebraicClosure K))) +
        (-s') • genericPoint (W.baseChange (AlgebraicClosure K)) := rfl
  rw [hlhs, hrhs, hadd, hz1, hz2, ffbc_frob_comm, ffBaseChangePoint_genericPoint]
  rfl

set_option maxHeartbeats 1600000 in
/-- **Wall A pencil genuineness (CoordHom-free).**  The concrete base-changed pencil pullback
`pencilBaseChangePullback = baseChangePullback (rπ − s)^K.pullback` is *genuine* with the geometric
action `gKbarPencil = r·frobₗ + [−s]` over `K̄`:

  `IsGenuineWith (E_{K̄}) (pencilIsogBaseChange … pencilBaseChangePullback) gKbarPencil`.

Proof: `gKbarPencil (P_gen^{K̄}) = ffBaseChangePoint (gK (P_gen))` (`gKbarPencil_genericPoint`); the
`K`-level genuineness `genuineIsogSmulSub_isGenuineWith` gives `gK (P_gen) = some ((rπ−s)^K.pullback
x_gen) ((rπ−s)^K.pullback y_gen)`; `ffBaseChangePoint` of a `some` applies `functionFieldMap` to both
coordinates (`ffBaseChangePoint_some`); and `functionFieldMap ((rπ−s)^K.pullback ?_gen) =
pencilBaseChangePullback ?_gen^{K̄}` (`baseChangePullback_functionFieldMap` + `functionFieldMap_?_gen`).
This realises the opaque base-changed pullback at the generic point purely through `functionFieldMap`. -/
theorem pencil_isGenuineWith_Kbar (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    HasseWeil.IsGenuineWith (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (gKbarPencil W r' s') := by
  -- The `K`-level genuine action of `genuineIsogSmulSub`.
  obtain ⟨X, Y, hns, hgK, hXeq, hYeq⟩ :=
    HasseWeil.genuineIsogSmulSub_isGenuineWith W r' s' hr hs hrK hsK
  -- `gKbarPencil P_gen = ffBaseChange (gK P_gen) = ffBaseChange (some X Y) = some (ffmap X) (ffmap Y)`.
  have hgen : gKbarPencil W r' s' (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      Affine.Point.some
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) X)
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) Y)
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange (AlgebraicClosure K)).injective X Y).mpr hns) := by
    rw [gKbarPencil_genericPoint W r' s']
    rw [show (((zsmulPointHom W r').comp (frobeniusW_KE W)) + zsmulPointHom W (-s'))
        (HasseWeil.genericPoint W) = Affine.Point.some X Y hns from hgK]
    exact ffBaseChangePoint_some W (AlgebraicClosure K) X Y hns
  -- The pullback coordinates: `pencilBaseChangePullback ?_gen = functionFieldMap ((rπ−s)^K.pullback ?_gen)`.
  have hpbx : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) X := by
    simp only [pencilIsogBaseChange_pullback]
    rw [hXeq, ← functionFieldMap_x_gen W (AlgebraicClosure K)]
    unfold pencilBaseChangePullback
    exact baseChangePullback_functionFieldMap _ _ _ _
  have hpby : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) Y := by
    simp only [pencilIsogBaseChange_pullback]
    rw [hYeq, ← functionFieldMap_y_gen W (AlgebraicClosure K)]
    unfold pencilBaseChangePullback
    exact baseChangePullback_functionFieldMap _ _ _ _
  exact ⟨_, _, _, hgen, hpbx.symm, hpby.symm⟩

set_option maxHeartbeats 1600000 in
/-- **The canonical-action generic-point covariance `hgcomm` for `(rπ − s)_{K̄}`** (Silverman III.8.2),
CoordHom-free — the form the `SeparableWitnesses` reductions consume.  From `pencil_isGenuineWith_Kbar`
(genuineness with `gKbarPencil`) + `mapTranslateGenericPoint_gKbarPencil` (the covariance for
`gKbarPencil`), via `mapTranslateGenericPoint_canonical_of_genuine`. -/
theorem mapTranslateGenericPoint_pencil_canonical (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback) :=
  mapTranslateGenericPoint_canonical_of_genuine (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (pencil_isGenuineWith_Kbar W p r r' s' hr hs hrK hsK)
    (mapTranslateGenericPoint_gKbarPencil W p r r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))

set_option maxHeartbeats 1600000 in
/-- **The translation covariance `hcomm'` for `(rπ − s)_{K̄}`, fully discharged (CoordHom-free).**
The `hcomm'` field of `PencilScalingData`, with **no** carried `hgcomm` hypothesis: the canonical
generic-point covariance is supplied by Wall A (`mapTranslateGenericPoint_pencil_canonical`), and
`pencil_hcommPrime_of_hgcomm` (`SeparableWitnesses.lean`) turns it into the per-`(ℓ, S, T)`
covariance at `z = weilFunction …`.  This is Silverman III.8.2 for the base-changed separable
`rπ − s`, realised purely from the function-field base-change naturality. -/
theorem pencil_hcommPrime_discharged (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
      (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
      (hφT : ((ℓ : ℕ) : ℤ) •
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom T = 0),
      translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
                (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom T)
              hφT)) =
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
          (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
              (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom S)
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
                (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom T)
              hφT)) :=
  pencil_hcommPrime_of_hgcomm W p r r' s'
    (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)
    (mapTranslateGenericPoint_pencil_canonical W p r r' s' hr hs hrK hsK)

end Pencil

end HasseWeil.WeilPairing
