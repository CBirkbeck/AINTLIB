/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.OneSubScaling
import HasseWeil.WeilPairing.PicDualDivisorClassLemma
import HasseWeil.WeilPairing.OneSubFrobeniusBaseChangeWitnesses
import HasseWeil.Curves.MillerAllChar

/-!
# The divisor-pushforward dual of a separable isogeny, and the `1 − π` scaling (CoordHom-free)

This file builds the **divisor-pushforward dual** `δ` of a separable isogeny `φ` as a genuine point
endomorphism `E.Point →+ E.Point` — *purely from the divisor pullback* `φ^*` (the multiplicity-free
fibre pullback `pullbackDivisor`) transported across the Abel–Jacobi isomorphism
`κ = picZeroIsoE : Pic⁰(E) ≅ E` — and proves the **dual relation `δ ∘ φ = [#ker φ]` outright**
(Silverman III.6.2(a)), *with no characteristic-polynomial / trace-relation input* and *no*
`Isogeny.CoordHom`.

It then specialises to the base-changed separable isogeny `(1 − π)_{K̄}` over
`L = AlgebraicClosure K` and feeds the shipped CoordHom-free `weilScales_of_dualComp` to
**discharge `OneSubFrobeniusScaling`** (leaf 2 of `FrobBaseChangeScalings`, `FrobMatrixData.lean`).

## The construction (Silverman III.6.1b: `φ̂ = κ⁻¹ ∘ φ^* ∘ κ`)

For a point-map endomorphism `f = φ.toAddMonoidHom` with finite kernel and the divisor-pullback
functoriality `hproj : ProjOrdTransport φ`, the fibre-pullback `pullbackDivisor f` is an
`AddMonoidHom` on projective divisors that

* multiplies degrees by `#ker f` (`degree_pullbackDivisor`), hence **preserves `Div⁰`**
  (`pullbackDegZero`), and
* sends **principal** divisors to **principal** divisors — because `φ^*(div h) = div(φ^* h)`
  (`projectiveDivisorOf_pullback_eq_pullbackDivisor`, from `hproj`), so it **descends to `Pic⁰(E)`**
  (`pullbackPicZero`, a `QuotientAddGroup.lift`).

Transporting this `Pic⁰`-endomorphism across the Abel–Jacobi iso `κ = picZeroIsoE_allChar` gives the
dual

  `δ := divisorPushforwardDual κ φ := κ ∘ (φ^* on Pic⁰) ∘ κ⁻¹ : E.Point →+ E.Point`,

an honest additive map.  This is *exactly* Silverman III.6.1b's `φ̂ = κ⁻¹ ∘ φ^* ∘ κ`, but with `φ^*`
realised as the geometric **divisor** pullback — no coordinate-ring comorphism.

## Why `δ ∘ φ = [#ker φ]` is *automatic* for separable `φ`

This is the reviewer's round-19 point ("for separable φ the σ-bridge is automatic").  Unfolding `δ`
at `f P`, with `κ⁻¹ (f P) = [(f P) − (O)]`:

  `δ (f P) = κ([φ^*((f P) − (O))]) = σ(φ^*((f P) − (O)))`,

and the **σ-bridge** `sigma_pullbackDivisor_kappaDivisor` (the multiplicity-free fibre sum, already
*proved* axiom-clean) gives `σ(φ^*((f P) − (O))) = #ker(f) · P` *directly* (taking `P` itself as the
preimage of `f P`).  So `δ(f P) = #ker(f) • P = [#ker f] P` — **no characteristic polynomial, no
`π + V = [t]` trace relation, no CoordHom**.  The dual relation falls straight out of the geometric
fibre count.

## What this file proves

* `degree_pullbackDivisor` — `deg(φ^*D) = #ker(φ) · deg D` (multiplicity-free pullback degree).
* `pullbackDegZero` / `pullbackPicZero` — the `Div⁰`- and `Pic⁰`-level pullback (the latter the
  `Pic⁰` descent, well-defined from `ProjOrdTransport`).
* `divisorPushforwardDual` — the dual point endomorphism `δ = κ ∘ φ^* ∘ κ⁻¹`.
* `divisorPushforwardDual_comp` — **`δ ∘ φ = [#ker φ]`** (Silverman III.6.2(a)), CoordHom-free,
  automatic via the σ-bridge.
* `oneSubScalingData_of_divisorDual` / `oneSubFrobeniusScaling_of_divisorDual` —
  **`OneSubFrobeniusScaling` discharged** from this dual (plus the project's standing
  `ProjOrdTransport`/translation-covariance residuals and V.1.3).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1(b) (`φ̂ = κ⁻¹ ∘ φ^* ∘ κ`),
  III.6.2(a) (`φ̂ ∘ φ = [deg φ]`), III.3.4 (`Pic⁰(E) ≅ E`), III.4.10c / III.8.6.1.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

/-! ### Step 0 — the `mk`-computation of `picZeroIsoE_allChar`

`picZeroIsoE_allChar` is the Abel–Jacobi iso `κ : Pic⁰(E) ≅ E`; its forward map is the descended
group-sum `σ̄`.  On a class `[D]` of a degree-zero divisor it is just `σ D = projectiveDivisorSum D`. -/

/-- **`picZeroIsoE_allChar` on a `Pic⁰` class is the group sum `σ`.** For a degree-zero divisor `D`,
`κ([D]) = projectiveDivisorSum D` — the Abel–Jacobi iso's forward map is the descended `σ̄`. -/
theorem picZeroIsoE_allChar_mk {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
    [IsAlgClosed F] [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (D : ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F)) :
    Curves.picZeroIsoE_allChar W (QuotientAddGroup.mk D) =
      Curves.projectiveDivisorSum W D.val :=
  rfl

/-! ### Step 1 — the divisor pullback multiplies degrees by `#ker` (preserves `Div⁰`)

The multiplicity-free fibre pullback `pullbackDiv f hf Q = Σ_{fP=Q}(P)` has degree `#ker f`
(`degree_pullbackDiv`, given a preimage of `Q`), and `pullbackDivisor f hf` is the `ℤ`-linear
extension over places.  Over `K̄` the point map `f` is **surjective**, so *every* place has a
preimage and the degree formula `deg(φ^*D) = #ker · deg D` holds on `single`s, hence (by additivity)
on all of `Div`.  In particular `φ^*` preserves degree `0`. -/

section AbstractDual

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **The degree of `pullbackDivisor f` on a `single`**: `deg(φ^*((v))) = #ker f · n`, for a
surjective point map `f` (so the place `v` has a preimage). The single-place fibre `φ^*((v))` has
degree `#ker f` by `degree_pullbackDiv`. -/
theorem degree_pullbackDivisor_single (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker)
    (hsurj : Function.Surjective f) (v : ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F))
    (n : ℤ) :
    (pullbackDivisor (W := W.toAffine) f hf (Finsupp.single v n)).degree =
      (Nat.card f.ker : ℤ) * n := by
  obtain ⟨P₀, hP₀⟩ := hsurj v.toAffinePoint
  rw [pullbackDivisor_single, ← Curves.ProjectiveDivisor.degreeHom_apply, map_zsmul,
    Curves.ProjectiveDivisor.degreeHom_apply, degree_pullbackDiv (W := W.toAffine) f hf hP₀,
    smul_eq_mul, mul_comm]

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **The degree formula `deg(φ^*D) = #ker(f) · deg D`** (multiplicity-free pullback), for a
surjective point map `f` over `K̄`. Each place pulls back to a fibre of size `#ker f`, so the degree
is multiplied by `#ker f`. -/
theorem degree_pullbackDivisor (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker)
    (hsurj : Function.Surjective f) (D : ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
    (pullbackDivisor (W := W.toAffine) f hf D).degree = (Nat.card f.ker : ℤ) * D.degree := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D hv hn ih =>
    rw [← pullbackDivisorHom_apply, map_add, pullbackDivisorHom_apply, pullbackDivisorHom_apply,
      Curves.ProjectiveDivisor.degree_add, Curves.ProjectiveDivisor.degree_add,
      degree_pullbackDivisor_single W f hf hsurj v n, ih, degree_single (W := W.toAffine) v n,
      mul_add]

/-- **`pullbackDivisor f` restricted to `Div⁰`** (preserves degree `0` over `K̄`). For a surjective
point map `f`, the degree formula `deg(φ^*D) = #ker(f) · deg D` makes `φ^*` send `Div⁰` into `Div⁰`,
so it restricts to an `AddMonoidHom` on the degree-zero subgroup. -/
noncomputable def pullbackDegZero (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker)
    (hsurj : Function.Surjective f) :
    ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F) →+
      ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F) :=
  AddMonoidHom.codRestrict
    ((pullbackDivisorHom (W := W.toAffine) f hf).comp
      (ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F)).subtype)
    (ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F))
    (fun D ↦ by
      rw [Curves.ProjectiveDivisor.mem_degZero, AddMonoidHom.comp_apply,
        AddSubgroup.coe_subtype, pullbackDivisorHom_apply,
        degree_pullbackDivisor W f hf hsurj,
        Curves.ProjectiveDivisor.mem_degZero.mp D.property, mul_zero])

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
@[simp] theorem pullbackDegZero_coe (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker)
    (hsurj : Function.Surjective f)
    (D : ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
    ((pullbackDegZero W f hf hsurj D :
        ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
      ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F)) =
      pullbackDivisor (W := W.toAffine) f hf
        (D : ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F)) := rfl

end AbstractDual

/-! ### Step 2 — `pullbackDivisor` preserves principal divisors (from `ProjOrdTransport`)

The key that lets `φ^*` descend to `Pic⁰`: a *principal* divisor `div h` pulls back to
`φ^*(div h) = div(φ^* h)`, again principal.  This is the divisor-pullback functoriality
`projectiveDivisorOf_pullback_eq_pullbackDivisor`, which holds under `ProjOrdTransport φ` (the
multiplicity-free order-transport of `φ`). -/

section Preserve

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **`φ^*` preserves principal divisors** (Silverman, divisor-pullback functoriality).  For an
isogeny `φ` with finite kernel and `hproj : ProjOrdTransport φ`, the fibre-pullback of a principal
projective divisor is principal: `φ^*(div h) = div(φ^* h)`. -/
theorem pullbackDivisor_mem_projPrincipal (φ : Isogeny W.toAffine W.toAffine)
    [Finite φ.toAddMonoidHom.ker] (hproj : ProjOrdTransport φ)
    {D : ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F)}
    (hD : D ∈ (⟨W.toAffine⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance D ∈
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projPrincipalSubgroup := by
  obtain ⟨h, hh_ne, hh_div⟩ := hD
  -- `φ^*(div h) = div(φ^* h)`, the pullback function's divisor — principal, with `φ^* h ≠ 0`.
  refine ⟨φ.pullback h, ?_, ?_⟩
  · exact fun h0 ↦ hh_ne (φ.pullback_injective (h0.trans (map_zero _).symm))
  · rw [projectiveDivisorOf_pullback_eq_pullbackDivisor hproj h, hh_div]

end Preserve

/-! ### Step 3 — the `Pic⁰`-level pullback `φ^*` and the dual `δ = κ ∘ φ^* ∘ κ⁻¹`

`pullbackPicZero` descends `pullbackDegZero` across the quotient `Pic⁰ = Div⁰ / principal`
(`QuotientAddGroup.lift`, well-defined by Step 2).  The dual `δ` is its transport across the
Abel–Jacobi iso `κ = picZeroIsoE_allChar`. -/

section PicZero

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

/-- **The divisor pullback `φ^*` descended to `Pic⁰(E)`** (Silverman III.6.1b's `φ^*` on classes).
For an isogeny `φ` with finite kernel, surjective point map (over `K̄`) and `ProjOrdTransport φ`,
the `Div⁰`-pullback `pullbackDegZero` descends to a `Pic⁰`-endomorphism, because `φ^*` preserves
principal divisors (`pullbackDivisor_mem_projPrincipal`). -/
noncomputable def pullbackPicZero (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hproj : ProjOrdTransport φ) (hsurj : Function.Surjective φ.toAddMonoidHom) :
    SmoothPlaneCurve.PicProj₀ (⟨W.toAffine⟩ : SmoothPlaneCurve F) →+
      SmoothPlaneCurve.PicProj₀ (⟨W.toAffine⟩ : SmoothPlaneCurve F) :=
  QuotientAddGroup.lift
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
      (ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F)))
    ((QuotientAddGroup.mk'
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
          (ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F)))).comp
      (pullbackDegZero W φ.toAddMonoidHom inferInstance hsurj))
    (fun D hD ↦ by
      -- Well-defined: `φ^*` of a principal `Div⁰` element is principal.
      change QuotientAddGroup.mk' _ (pullbackDegZero W φ.toAddMonoidHom inferInstance hsurj D) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      change (pullbackDegZero W φ.toAddMonoidHom inferInstance hsurj D).val ∈
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).projPrincipalSubgroup
      rw [pullbackDegZero_coe]
      exact pullbackDivisor_mem_projPrincipal W φ hproj hD)

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
@[simp] theorem pullbackPicZero_mk (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hproj : ProjOrdTransport φ) (hsurj : Function.Surjective φ.toAddMonoidHom)
    (D : ProjectiveDivisor.degZero (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
    pullbackPicZero W φ hproj hsurj (QuotientAddGroup.mk D) =
      QuotientAddGroup.mk (pullbackDegZero W φ.toAddMonoidHom inferInstance hsurj D) :=
  rfl

end PicZero

/-! ### Step 4 — the dual point endomorphism `δ` and the dual relation `δ ∘ φ = [#ker φ]`

The dual is `δ := κ ∘ (φ^* on Pic⁰) ∘ κ⁻¹`, the transport of `pullbackPicZero` across the
Abel–Jacobi iso `κ = picZeroIsoE_allChar`.  The dual relation `δ ∘ φ = [#ker φ]` is *automatic*: it
unfolds to the σ-bridge `σ(φ^*((f P) − (O))) = #ker(f) · P` (multiplicity-free fibre sum), with `P`
the preimage of `f P`. -/

section DualRelation

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsAlgClosed F]
  [IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

/-- **The divisor-pushforward dual `δ = κ ∘ φ^* ∘ κ⁻¹`** (Silverman III.6.1b), CoordHom-free.
Built from the Abel–Jacobi iso `κ = picZeroIsoE_allChar : Pic⁰(E) ≅ E` and the `Pic⁰`-level divisor
pullback `pullbackPicZero`, with no coordinate-ring comorphism. -/
noncomputable def divisorPushforwardDual (φ : Isogeny W.toAffine W.toAffine)
    [Finite φ.toAddMonoidHom.ker] (hproj : ProjOrdTransport φ)
    (hsurj : Function.Surjective φ.toAddMonoidHom) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (Curves.picZeroIsoE_allChar W.toAffine).toAddMonoidHom.comp
    ((pullbackPicZero W φ hproj hsurj).comp
      (Curves.picZeroIsoE_allChar W.toAffine).symm.toAddMonoidHom)

/-- **The dual relation `δ ∘ φ = [#ker φ]`** (Silverman III.6.2(a)), CoordHom-free and **automatic**
for separable `φ`.  Unfolding `δ` at `f P` (with `κ⁻¹(f P) = [(f P) − (O)]` and
`f = φ.toAddMonoidHom`): `δ(f P) = κ([φ^*((f P) − (O))]) = σ(φ^*((f P) − (O)))`, and the σ-bridge
`sigma_pullbackDivisor_kappaDivisor` (the multiplicity-free fibre sum, proved) yields
`σ(φ^*((f P) − (O))) = #ker(f) · P` taking `P` as the preimage of `f P`.  Hence `δ(f P) = #ker(f) • P`,
i.e. `δ ∘ φ = [#ker φ]` — **no characteristic polynomial / `π + V = [t]` trace relation**. -/
theorem divisorPushforwardDual_comp (φ : Isogeny W.toAffine W.toAffine)
    [Finite φ.toAddMonoidHom.ker] (hproj : ProjOrdTransport φ)
    (hsurj : Function.Surjective φ.toAddMonoidHom) :
    (divisorPushforwardDual W φ hproj hsurj).comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom := by
  ext P
  rw [AddMonoidHom.comp_apply, divisorPushforwardDual, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, mulByInt_apply]
  -- `κ⁻¹ (f P) = picZeroOfPoint (f P) = mk ⟨kappaDivisor (f P), _⟩`.
  have hsymm : (Curves.picZeroIsoE_allChar W.toAffine).symm (φ.toAddMonoidHom P) =
      QuotientAddGroup.mk ⟨Curves.kappaDivisor W.toAffine (φ.toAddMonoidHom P),
        Curves.ProjectiveDivisor.mem_degZero.mpr
          (Curves.kappaDivisor_degree W.toAffine (φ.toAddMonoidHom P))⟩ :=
    rfl
  rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, hsymm, pullbackPicZero_mk,
    picZeroIsoE_allChar_mk]
  -- `σ(φ^*((fP)−(O))) = #ker(f) • P` (preimage `P` of `f P`) via the σ-bridge.
  rw [pullbackDegZero_coe,
    sigma_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance (P₀ := P) rfl,
    natCast_zsmul]

end DualRelation

/-! ### Step 5 — discharging `OneSubFrobeniusScaling` via the divisor-pushforward dual

We instantiate the abstract dual `δ = divisorPushforwardDual` at the base-changed separable isogeny
`(1 − π)_{K̄}` over `L = AlgebraicClosure K` and assemble the leaf-2 data
(`mkOneSubScalingDataConcrete`), supplying the **divisor-pushforward** `δ`/`hdc` (CoordHom-free,
the σ-bridge dual of Step 4) in place of the char-poly dual `OneSubDual.oneSubFrobeniusDual`.  The
remaining inputs are the project's standing CoordHom-free geometric residuals
(`hproj : ProjOrdTransport`, the translation covariance `hcomm'`, surjectivity `hsurj`
(Silverman III.4.10a over `K̄`)) plus the V.1.3 degree identity `hdeg_eq`. -/

section Assemble

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACDiv : DecidableEq (AlgebraicClosure K) := Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

/-- **Leaf-2 `OneSubScalingData` from the divisor-pushforward dual** (Silverman III.6.1b/III.6.2(a)),
CoordHom-free.  Assembles the full `OneSubScalingData` for `(1 − π)_{K̄}` over `L = AlgebraicClosure K`
with the dual point `δ` supplied by `divisorPushforwardDual` (the divisor pushforward `κ ∘ φ^* ∘ κ⁻¹`)
and the dual relation `hdc` by `divisorPushforwardDual_comp` (**automatic via the σ-bridge**, no
characteristic polynomial / trace relation).

Inputs — all CoordHom-free, carried per isogeny exactly as the project's other base-change residuals:
* `hdeg_eq` — V.1.3 `φ_L.degree = pointCount` (already a field of the assembler);
* `hproj` — `ProjOrdTransport φ_L` (multiplicity-free divisor-pullback functoriality), which *also*
  feeds the dual construction (it makes `φ^*` descend to `Pic⁰`);
* `hsurj` — surjectivity of `φ_L` on `E_{K̄}`-points (Silverman III.4.10a over `K̄`), needed both for
  `δ`/`hdc` (the σ-bridge preimage) and by `weilScales_of_dualComp` (the adjoint preimage);
* `hcomm'` — the translation covariance (Silverman III.8.2). -/
noncomputable def mkOneSubScalingDataConcrete_of_divisorDual (hq : 2 ≤ Fintype.card K)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine)
    (hproj : ProjOrdTransport
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)))
    (hsurj : Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom)
    (hcomm' :
      ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
        (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
        (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) •
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T = 0),
        translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
              (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                  (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT)) =
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
              ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom S)
              (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                  (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT))) :
    OneSubScalingData W p r (AlgebraicClosure K) hq :=
  haveI : Finite
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker :=
    oneSubFrobeniusIsogBaseChange_finiteKer W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)
  mkOneSubScalingDataConcrete W p r (AlgebraicClosure K) hq
    (oneSubFrobeniusIsogBaseChange_finiteKer W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    hproj
    (divisorPushforwardDual (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) hproj hsurj)
    (divisorPushforwardDual_comp (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) hproj hsurj)
    hsurj
    (oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) hdeg_eq)
    hcomm'

/-- **`OneSubFrobeniusScaling` discharged via the divisor-pushforward dual** (Silverman III.8.6.1),
CoordHom-free.  For `(1 − π)_{K̄}` over `L = AlgebraicClosure K`, the symplectic scaling
`e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` on `E_{K̄}[ℓ]` (every prime `ℓ ≠ p`) holds,
from the divisor-pushforward dual `δ`/`hdc` (`divisorPushforwardDual` + `divisorPushforwardDual_comp`,
the σ-bridge dual of Step 4 — **no characteristic polynomial / `π + V = [t]` trace relation, no
`CoordHom`**) together with the project's standing CoordHom-free residuals:

* `hdeg_eq` — Silverman V.1.3 `deg(1 − π) = #E(𝔽_q)` (the project's known sharp residual, axiom-clean
  modulo `sorryAx` exactly as in `OneSubDual.lean`);
* `hproj` — `ProjOrdTransport` (multiplicity-free divisor-pullback functoriality);
* `hsurj` — surjectivity of `(1 − π)_{K̄}` over `K̄` (Silverman III.4.10a);
* `hcomm'` — the translation covariance (Silverman III.8.2).

This routes the leaf-2 scaling through the **divisor pushforward** dual the reviewer prescribed
(round 19 Q3) rather than the char-poly dual of `OneSubDual.lean`: the dual relation
`δ ∘ (1 − π) = [#E]` is *automatic* from the multiplicity-free fibre sum, eliminating the deep
carried `FrobeniusCharPolyBaseChange` identity. -/
theorem oneSubFrobeniusScaling_of_divisorDual (hq : 2 ≤ Fintype.card K)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine)
    (hproj : ProjOrdTransport
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)))
    (hsurj : Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom)
    (hcomm' :
      ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
        (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
        (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) •
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T = 0),
        translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
              (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                  (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT)) =
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
              ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom S)
              (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                  (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT))) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq :=
  oneSubFrobeniusScaling_of_data W p r (AlgebraicClosure K) hq
    (mkOneSubScalingDataConcrete_of_divisorDual W p r hq hdeg_eq hproj hsurj hcomm')

end Assemble

end HasseWeil.WeilPairing
