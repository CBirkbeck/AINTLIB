/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.Dual
import HasseWeil.EC.IsogenyAG.Bridge
import HasseWeil.EC.SeparableKernelTorsor
import HasseWeil.Hasse.PointFix
import HasseWeil.WeilPairing.IsogenyWitnessReductions
import HasseWeil.WeilPairing.PencilCovariance

/-!
# Discharging the dual-isogeny fixed-field equality from the project's Galois infra

The dual-isogeny construction (`HasseWeil/EC/IsogenyAG/Dual.lean`) reduces — via
the III.4.11 fixed-field core `EC.Isogeny.rangeIncl_of_fixedField` and the
package `EC.Isogeny.DualGaloisData` — to one genuinely deep input: the **Galois
fixed-field equality** `Im(φ*) = Fix(ker φ)` (Silverman III.4.10c), in the
shape `∀ z, z ∈ Im(φ*) ↔ ∀ k ∈ ker φ, τ_k z = z`.

This file proves that equality is **exactly** the output of the project's own
fixed-field theorem `HasseWeil.pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`
(`Hasse/PointFix.lean`): for a `Basic.Isogeny β` over a finite field, given the
per-`β` translation covariance (`xy_family`) and the cardinality match
`#ker β = deg β`, the image of `β.pullback` is precisely the subset of `K(E)`
fixed by the kernel translations `{τ_k : k ∈ ker β}`.

The point: the deep `hfix` field of `DualGaloisData` is *not* a new black box —
it is discharged, axiom-clean, by the existing Galois machinery from the two
genuine geometric facts. Those two facts are themselves discharged in the project
for concrete isogenies (e.g. `1 − π` in `Hasse/IsogOneSubXyFamily.lean`,
`finrank_pullback_fieldRange_eq_degree` + the torsion `#ker = deg`), which is what
makes the dual-witness reduction non-vacuous.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10c (the kernel
  translation Galois group), III.4.11 (factor through), III.6.1 (the dual).
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

-- `[Fintype F]` is genuinely required (it is consumed by
-- `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`), but the linter
-- only inspects the type signature, where it is resolved through instances.
set_option linter.unusedFintypeInType false in
/-- **`hfix` from `xy_family` + `#ker = deg`** (Silverman III.4.10c, packaged for
the dual witness). For a `Basic.Isogeny β` over a finite field, the image of
`β.pullback` is *exactly* the subset of `K(E)` fixed by the kernel translations
`G = {τ_k : k ∈ ker β}` — the `hfix` shape consumed by `EC.Isogeny.DualGaloisData`.

Reuses, axiom-clean, `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`
(the forward inclusion = translation invariance of `Im(β*)`; the equality from the
finrank/cardinality match). The two genuine inputs are:
* `h_xy_family` — the per-`β` translation covariance on `x_gen, y_gen`;
* `h_card_eq_degree` — the cardinality match `#ker β = deg β`. -/
theorem fixedField_hfix_of_xy_family_of_card
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (β : Isogeny W.toAffine W.toAffine)
    [hfin_ker : Fintype (Multiplicative β.kernel)]
    [hfindim : FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card_eq_degree : Fintype.card (Multiplicative β.kernel) = β.degree) :
    ∀ z : W.toAffine.FunctionField,
      z ∈ β.pullback.range ↔
        ∀ σ ∈ (Set.range (fun k : β.kernel ↦
            translateAlgEquivOfPoint W k.val)), σ z = z := by
  have h_eq := pullback_fieldRange_eq_fixedField_of_card_match_intrinsic W β
    h_xy_family h_card_eq_degree
  intro z
  constructor
  · rintro ⟨w, rfl⟩ σ ⟨k, rfl⟩
    have hmem : β.pullback w ∈ β.pullback.fieldRange := ⟨w, rfl⟩
    rw [h_eq] at hmem
    exact hmem (Multiplicative.ofAdd k)
  · intro hz
    have hmem : z ∈ (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
      intro g
      exact hz _ ⟨Multiplicative.toAdd g, rfl⟩
    rw [← h_eq, AlgHom.mem_fieldRange] at hmem
    rw [AlgHom.mem_range]
    exact hmem

/-! ### DUAL-1 — `ker β ⊆ ker [deg β]` for separable `β` (Lagrange)

Silverman III.4.10c gives `#ker β = deg β` for a separable isogeny `β`; Lagrange
on the finite group `ker β` (`card_nsmul_eq_zero'`) then yields `(deg β) • k = 0`
for every `k ∈ ker β`, i.e. `ker β ⊆ ker [deg β]`. This is the inclusion behind
"`[deg β]` factors through `β`" (Silverman III.6.1's range inclusion). -/

section DualOne

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **`ker β ⊆ ker [deg β]` (Silverman III.4.10c + Lagrange)**. For a `Basic.Isogeny β`
with finite kernel and `#ker β = deg β` (the separable cardinality match, e.g. from
`card_kernel_eq_degree_of_separable_concrete`), every kernel point `k` is
`(deg β)`-torsion: `(deg β) • k = 0`. The degree multiple of any kernel element
vanishes, so `ker β ≤ ker [deg β]`.

The proof is pure Lagrange (`card_nsmul_eq_zero'` on the finite additive group
`↥(ker β)`) plus the supplied cardinality match `h_card`. -/
theorem kernel_nsmul_degree_eq_zero (β : HasseWeil.Isogeny W₁ W₂)
    [Finite β.kernel] (h_card : Nat.card β.kernel = β.degree)
    {k : W₁.Point} (hk : k ∈ β.kernel) :
    (β.degree) • k = 0 := by
  -- Lagrange in the finite additive group `↥(ker β)`: `Nat.card • ⟨k, hk⟩ = 0`.
  have hsub : (Nat.card β.kernel) • (⟨k, hk⟩ : β.kernel) = 0 := card_nsmul_eq_zero'
  -- Push the subgroup nsmul down to the ambient group.
  have hpush : ((Nat.card β.kernel) • k) = 0 := by
    simpa using congrArg (β.kernel.subtype) hsub
  rwa [h_card] at hpush

/-- **`ker β ≤ ker [deg β]`, subgroup form** (Silverman III.4.10c + Lagrange).
Every kernel point of `β` is killed by `[deg β]`, packaged as a membership
implication `k ∈ ker β → (deg β) • k = 0`. -/
theorem kernel_subset_degTorsion (β : HasseWeil.Isogeny W₁ W₂)
    [Finite β.kernel] (h_card : Nat.card β.kernel = β.degree) :
    ∀ k ∈ β.kernel, (β.degree) • k = 0 :=
  fun _ hk ↦ kernel_nsmul_degree_eq_zero β h_card hk

end DualOne

/-! ### DUAL-2 — the per-`β` translation covariance `xy_family` ⚑

The `xy_family` covariance consumed by `fixedField_hfix_of_xy_family_of_card`
(`τ_k(β.pullback x_gen) = β.pullback x_gen` and likewise for `y_gen`, for
`k ∈ ker β`) is, for a **general** isogeny `β`, the function-field shadow of
Silverman III.4.10b's `τ_k* ∘ β* = β*` (because `β ∘ τ_k = β` when `β(k) = 0`).

The project already isolates this to ONE genuinely-geometric leaf: the
generic-point commutation `hgcomm`,

  `Point.map τ_S (Point.map β* P_gen) = Point.map β* P_gen + lift (β(S))`,

i.e. `β(P_gen + S) = β(P_gen) + β(S)` read at the **generic point** `P_gen`. With
`hgcomm`, the shipped `hcov_of_mapTranslateGenericPoint_canonical`
(`WeilPairing/SeparableWitnesses.lean`, via `hcomm_of_isGenuineWith` +
`isogeny_isGenuineWith_pointMap`) yields the covariance for all `z`, hence
`xy_family` at `z = x_gen, y_gen`.

`hgcomm` is **not** derivable from the abstract `Isogeny` fields: `addHomProperty`
(III.4.8) gives `β(P + T) = β(P) + β(T)` only for `F`-rational `P, T`, whereas
`hgcomm` is the same identity at the transcendental generic point `P_gen`
(a `(W_KE).Point`), for which `Point.map β* P_gen` has no closed form for a general
`β`. It is therefore carried as the single named residual `hgcomm` (the
function-field shadow of the group-law homomorphism property, per isogeny). -/

section DualTwo

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **The `xy_family` covariance from `hgcomm`** (Silverman III.4.10b ⚑, DUAL-2).
For a general `Basic.Isogeny β`, given the single generic-point commutation leaf
`WeilPairing.MapTranslateGenericPoint` (= `hgcomm`) for the **canonical** geometric
action `g = Affine.Point.map β.pullback`, the translation-covariance hypothesis
`xy_family` consumed by `fixedField_hfix_of_xy_family_of_card` /
`pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` holds: for every
`k ∈ ker β`, `τ_k` fixes both `β.pullback x_gen` and `β.pullback y_gen`.

This is the project's `hcov_of_mapTranslateGenericPoint_canonical` (via the free
canonical genuineness `isogeny_isGenuineWith_pointMap` + `hcomm_of_isGenuineWith`)
specialised to `S = k ∈ ker β` (where `β(k) = 0`, so `τ_{β k} = τ_0 = refl`),
read at `z = x_gen` and `z = y_gen`. The genuine remaining content is exactly the
`hgcomm` hypothesis: `Point.map β* P_gen` has no closed form for a general `β`, so
this generic-point identity is *not* derivable from the abstract `Isogeny` fields
(III.4.8's `addHomProperty` gives it only for `F`-rational points, not at the
transcendental generic point `P_gen`). -/
theorem xy_family_of_genericPointCommutes
    (β : HasseWeil.Isogeny W.toAffine W.toAffine)
    (hgcomm : WeilPairing.MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback)) :
    ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) = β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) = β.pullback (y_gen W)) :=
  fun k ↦
    ⟨WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β hgcomm k (x_gen W),
     WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β hgcomm k (y_gen W)⟩

end DualTwo

/-! ### Capstone: the dual witness with the Galois input fully discharged

We assemble a complete `EC.Isogeny.DualGaloisData` (hence a `HasDualWitness`) for
an `EC.Isogeny φ` whose pullback coincides with a `Basic.Isogeny β` (the same
field hom, named in the two `Isogeny` structures), with the **deep `hfix` field
discharged by reuse** of `fixedField_hfix_of_xy_family_of_card`. This is the
genuine non-vacuity demonstration: given the per-`β` translation covariance
(`xy_family`), the cardinality match `#ker β = deg β`, the `ν`-invariance, and the
basepoint / `∞`-regularity data, the dual witness is produced **axiom-clean** —
no `sorry`. The remaining inputs are exactly the project's standard per-isogeny
witnesses (discharged for `1 − π` etc.). -/

variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **`DualGaloisData` with `hfix` discharged by the Galois infra** (capstone).
For an `EC.Isogeny φ` whose pullback equals a `Basic.Isogeny β`'s pullback, the
Galois fixed-field equality `hfix` is supplied by
`fixedField_hfix_of_xy_family_of_card` (reuse of `Hasse/PointFix.lean`); the
remaining fields are the per-`φ` geometric witnesses. Axiom-clean. -/
noncomputable def dualGaloisData_of_basic_witnesses
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    [Fintype (Multiplicative β.kernel)]
    [FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (νPb : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Fintype.card (Multiplicative β.kernel) = β.degree)
    (hnu : ∀ σ ∈ (Set.range (fun k : β.kernel ↦
        translateAlgEquivOfPoint W k.val)), ∀ w, σ (νPb w) = νPb w)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (νPb f))
    (hrefl : ∀ g : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          (φ.toCurveMap.pullback g) →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g) :
    EC.Isogeny.DualGaloisData φ where
  νPb := νPb
  transAut := Set.range (fun k : β.kernel ↦ translateAlgEquivOfPoint W k.val)
  hfix := by
    intro z
    rw [h_pb]
    exact fixedField_hfix_of_xy_family_of_card W β h_xy_family h_card z
  hnu := hnu
  hν := hν
  hrefl := hrefl

/-- **The dual witness with the Galois input fully discharged** (capstone).
Composes `dualGaloisData_of_basic_witnesses` with
`EC.Isogeny.hasDualWitness_of_galoisData`: an `EC.Isogeny φ` (with pullback equal
to a `Basic.Isogeny β`'s) admits a `HasDualWitness` — **axiom-clean** — from the
project's standard per-isogeny witnesses. -/
noncomputable def hasDualWitness_of_basic_witnesses
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    [Fintype (Multiplicative β.kernel)]
    [FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (νPb : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Fintype.card (Multiplicative β.kernel) = β.degree)
    (hnu : ∀ σ ∈ (Set.range (fun k : β.kernel ↦
        translateAlgEquivOfPoint W k.val)), ∀ w, σ (νPb w) = νPb w)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (νPb f))
    (hrefl : ∀ g : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          (φ.toCurveMap.pullback g) →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g) :
    EC.Isogeny.HasDualWitness φ :=
  φ.hasDualWitness_of_galoisData
    (dualGaloisData_of_basic_witnesses W φ β h_pb νPb h_xy_family h_card hnu hν hrefl)

/-! ### DUAL-3 — `DualGaloisData φ` for a separable isogeny over a finite field

We assemble `EC.Isogeny.DualGaloisData φ` for a separable `EC.Isogeny φ` over a
**finite** base field `F`, against a `Basic.Isogeny β` carrying the III.4.8 point
map (`h_pb : φ* = β*`; e.g. a concrete isogeny, or the BRIDGE-1 image
`φ.toBasicIsogeny` when `F` is algebraically closed — those two settings are
disjoint, since the fixed-field step needs `[Fintype F]` and BRIDGE-1 needs
`[IsAlgClosed F]`). The deep fixed-field equality `hfix` is discharged by
`fixedField_hfix_of_xy_family_of_card` from:

* the per-`β` covariance `xy_family`, produced from the single generic-point leaf
  `hgcomm` by `xy_family_of_genericPointCommutes` (DUAL-2); and
* the cardinality match `#ker β = deg β`, which for separable `β` is
  `card_kernel_eq_degree_of_separable_concrete` (Silverman III.4.10c) — itself fed
  the **same** `hgcomm`-derived covariance `hcov` plus the normality `h_normal`
  and the generic-point translation-torsor descent `hdesc`.

The dual endomorphism is `ν = [deg β]` (Silverman III.6.1: `φ̂ ∘ φ = [deg φ]`); its
`hnu` covariance is **derived** from DUAL-1 (`ker β ⊆ ker [deg β]`,
`kernel_nsmul_degree_eq_zero`) + the *free* `[deg β]`-covariance
(`mapTranslateGenericPoint_mulByInt`, the division-polynomial fact), so the only
dual-endomorphism residual is the `[deg β]` basepoint `hν` (`MulByIntBasepoint`).
The `∞`-regularity reflection `hrefl` is supplied by
`reflects_ordAtInfty_of_ramificationIdx` (RAMI-1) from the ramification-at-`O`
identity `hramO` (`e = deg_i φ = 1` for separable `φ`).

This closes `EC.universal_dualGaloisData`, hence `universal_dual_witness` /
`exists_dual` / `IsIsogenous.symm`, for separable `φ`, modulo exactly the genuine
per-isogeny geometric residuals: `hgcomm` (the group-law shadow at the generic
point — *not* derivable from the abstract `Isogeny` fields), `h_normal`/`hdesc`
(Galois normality + torsor descent), `hramO` (ramification index at `O`), and the
`[deg β]` basepoint `hν`. -/

section DualThree

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

-- `[Fintype F]` is genuinely required: the proof cites the `[Fintype K]`-scoped
-- `mulByInt_isGenuineWith` (`GapSpines.lean`); the linter only inspects the type.
set_option linter.unusedFintypeInType false in
/-- **`hnu` for `ν = [n]` from DUAL-1** (Silverman III.6.1, the `[deg β]`-invariance).
For `n` with `n • k = 0` on every kernel point of `β` (DUAL-1: `n = deg β` and
`ker β ⊆ ker [deg β]`), the translation family `{τ_k : k ∈ ker β}` fixes the image
of `[n]*`: `τ_k([n]* w) = [n]* w`. Derived from the *free* `[n]`-covariance
`mapTranslateGenericPoint_mulByInt` (`P ↦ n • P` action, `mulByInt_isGenuineWith`)
via `hcomm_of_isGenuineWith`, specialised to `S = k` (where `[n] k = n • k = 0`, so
`τ_{[n]k} = τ_0 = refl`). This eliminates the `hnu` field of the dual data for the
Silverman choice `ν = [deg β]`. -/
theorem hnu_mulByInt_of_kernel_nsmul_zero
    (β : HasseWeil.Isogeny W.toAffine W.toAffine) (n : ℤ) (hn : n ≠ 0)
    (hdvd : ∀ k ∈ β.kernel, n • k = 0) :
    ∀ σ ∈ (Set.range (fun k : β.kernel ↦ translateAlgEquivOfPoint W k.val)),
      ∀ w, σ ((mulByInt W.toAffine n).pullback w) = (mulByInt W.toAffine n).pullback w := by
  rintro σ ⟨k, rfl⟩ w
  -- `[n]`-covariance: `τ_k([n]* w) = [n]*(τ_{[n]k} w)` (genuine, free leaf).
  rw [WeilPairing.hcomm_of_isGenuineWith W (mulByInt W.toAffine n)
    (mulByInt_isGenuineWith W n hn) k.val
    (WeilPairing.mapTranslateGenericPoint_mulByInt W n k.val) w]
  -- `[n] k = n • k = 0` for `k ∈ ker β` (DUAL-1), so `τ_{[n]k} = τ_0 = refl`.
  have hk0 : (mulByInt W.toAffine n).toAddMonoidHom k.val = 0 := by
    rw [mulByInt_apply]; exact hdvd k.val k.property
  rw [hk0]
  rfl

set_option linter.unusedFintypeInType false in
/-- **`DualGaloisData φ` for a separable isogeny over a finite field** (Silverman
III.4.11 / III.6.1, DUAL-3). For a separable `EC.Isogeny φ` whose pullback equals a
`Basic.Isogeny β`'s (`h_pb`), `φ` admits a `DualGaloisData`. The fixed-field `hfix`
is assembled from DUAL-2 (`xy_family` via `hgcomm`) + the separable cardinality
match `#ker β = deg β` (Silverman III.4.10c,
`card_kernel_eq_degree_of_separable_concrete`); the dual endomorphism is `ν = [deg β]`
with `hnu` **derived** from DUAL-1 (`hnu_mulByInt_of_kernel_nsmul_zero`); `hrefl`
from RAMI-1 (`reflects_ordAtInfty_of_ramificationIdx`).

The residuals are exactly the genuine per-isogeny geometric facts:
* `hgcomm` — the generic-point commutation (DUAL-2's irreducible leaf);
* `h_normal`, `hdesc` — the Galois normality and translation-torsor descent of
  `card_kernel_eq_degree_of_separable_concrete` (Silverman III.4.10c);
* `hramO` — the ramification index at `O` (`= deg_i φ = 1` for separable `φ`);
* `hν` — the `[deg β]` basepoint (`MulByIntBasepoint`). -/
noncomputable def dualGaloisData_of_separable
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : HasseWeil.Isogeny W.toAffine W.toAffine)
    [Fintype (Multiplicative β.kernel)]
    [FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    (hgcomm : WeilPairing.MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback))
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f))
    {e : ℕ} (he : 1 ≤ e)
    (hramO : ∀ g : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).FunctionField, g ≠ 0 →
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) =
        e • (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g) :
    EC.Isogeny.DualGaloisData φ :=
  -- The cardinality match `#ker β = deg β` (Silverman III.4.10c) — fed the same
  -- `hgcomm`-derived covariance `hcov`, plus `h_normal` and `hdesc`.
  have h_card_nat : Nat.card β.kernel = β.degree :=
    card_kernel_eq_degree_of_separable_concrete W β hsep
      (fun k z ↦ WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β hgcomm k z)
      h_normal hdesc
  -- DUAL-1: `ker β ⊆ ker [deg β]`, so `[deg β]`'s `hnu` covariance holds.
  have hdvd : ∀ k ∈ β.kernel, (β.degree : ℤ) • k = 0 :=
    fun k hk ↦ kernel_nsmul_degree_eq_zero β h_card_nat hk
  dualGaloisData_of_basic_witnesses W φ β h_pb
    (mulByInt W.toAffine (β.degree : ℤ)).pullback
    (xy_family_of_genericPointCommutes W β hgcomm)
    (by rw [Fintype.card_eq_nat_card]; exact h_card_nat)
    (hnu_mulByInt_of_kernel_nsmul_zero W β (β.degree : ℤ) (by exact_mod_cast hdeg) hdvd)
    hν
    (fun g hg ↦ EC.reflects_ordAtInfty_of_ramificationIdx φ he hramO g hg)

set_option linter.unusedFintypeInType false in
/-- **`HasDualWitness φ` for a separable isogeny** (Silverman III.6.1, DUAL-3).
Composes `dualGaloisData_of_separable` with `hasDualWitness_of_galoisData`: a
separable `EC.Isogeny φ` (with pullback equal to a `Basic.Isogeny β`'s, over a
finite field) admits a dual witness, from the genuine per-isogeny residuals. This is
`universal_dual_witness` discharged for separable `φ`. -/
noncomputable def hasDualWitness_of_separable
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : HasseWeil.Isogeny W.toAffine W.toAffine)
    [Fintype (Multiplicative β.kernel)]
    [FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    (hgcomm : WeilPairing.MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback))
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f))
    {e : ℕ} (he : 1 ≤ e)
    (hramO : ∀ g : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).FunctionField, g ≠ 0 →
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) =
        e • (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g) :
    EC.Isogeny.HasDualWitness φ :=
  φ.hasDualWitness_of_galoisData
    (dualGaloisData_of_separable W φ β h_pb hsep hdeg hgcomm h_normal hdesc hν he hramO)

set_option linter.unusedFintypeInType false in
/-- **`exists_dual` for a separable isogeny** (Silverman III.6.1, DUAL-3 capstone):
a separable `EC.Isogeny φ` (over a finite field, with pullback equal to a
`Basic.Isogeny β`'s) admits a reverse isogeny `φ̂ : E₂ → E₁`, from the genuine
per-isogeny residuals. This closes `IsIsogenous.symm` for separable `φ`. -/
theorem exists_dual_of_separable
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : HasseWeil.Isogeny W.toAffine W.toAffine)
    [Fintype (Multiplicative β.kernel)]
    [FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField]
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    (hgcomm : WeilPairing.MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback))
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f))
    {e : ℕ} (he : 1 ≤ e)
    (hramO : ∀ g : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).FunctionField, g ≠ 0 →
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) =
        e • (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty g) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (hasDualWitness_of_separable W φ β h_pb hsep hdeg hgcomm h_normal hdesc hν he hramO)

end DualThree

end HasseWeil
