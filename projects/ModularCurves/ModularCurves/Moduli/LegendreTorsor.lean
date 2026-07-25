/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.Bootstrap
import ModularCurves.Moduli.LegendreDatumSymmetry
import ModularCurves.Moduli.LegendreChart

/-! ## ⚠ QUARANTINED SUBTREE (B2-DECISION, board v10.342/v10.343, 2026-07-20)

This file belongs to the **Legendre D(2)-mouth subtree**, removed from every
receipt cone by the adjudicated B2 resolution: the engine's D(2) leg now runs on
the naive level-4 rigidifier (`Moduli/UniversalLevelFour.lean` +
`Moduli/LevelFourTorsor.lean`; `EngineWiring.representable_baseChange_two`).
KM 4.6.2's constant-group torsor claim for the Legendre problem is FALSE as
stated (b2_log `B2-DECISION`: over the universal Legendre base the six
marking-components are pairwise non-isomorphic quadratic étale algebras, so no
constant finite group acts fibre-transitively; the honest torsor group is a
twisted μ₂-extension of GL₂(𝔽₂)). The sorried declarations below are DOCUMENTED
NON-GOALS (kept per statement-protection protocol; a groupoid-descent engine
would be required to make the Legendre route viable — see decomposition-e4.md).
Do NOT work these sorries as receipt leaves. -/



/-!
# T-E14 — the Legendre `TorsorData` package (KM 4.7, axiom 2, at `(N, G) = (2, GL₂(𝔽₂) × {±1})`)

The `ℤ[1/2]`-half instantiation boundary of the KM 4.7 engine: KM 4.6.2's **coupled**
Legendre problem `δ = legendreDeltaProblem R` (the subfunctor of the ambient product
`Γ(2)-naive × ω` cut out by *"the adapted `x` satisfies `x(P₂) = 0, x(Q₂) = 1`"*) carries,
at every `X : Ell/R` with `2` invertible, a `GL₂(ℤ/2) × {±1}`-equivariant finite étale
`G`-torsor datum on the scale-torsor carrier `legendreDelta_relRep_finiteEtale`
(KM 4.6.2; the `|G| = 12 = 6 × 2` torsor of orderings × `±ω`).

This is the **second** `TorsorData` package, mirroring `Moduli/LevelThreeTorsor.lean`'s
T-E15b at `(3, GL₂(𝔽₃))`. The problem-action-to-scheme-action transport is reused (NOT
re-proved) via `ModuliProblem.RelRepData.exists_equivariant` ([GHB1],
`Moduli/GammaHRepresentability.lean`) — the same underlying classifying transport as
`LevelThreeTorsor.relRepSchemeAction`, taken through the committed `GammaHRepresentability`
entry point so this file is decoupled from concurrent edits to `LevelThreeTorsor`.

## Contents

* **The `{±1}`-restriction (GENUINE, sorry-free modulo carrier `sorryAx`)**:
  `legendreDeltaNegAut` / `legendreDeltaSignAction` — the honest restriction of the
  ambient `legendreBootstrapSignAction` to `δ` along the subfunctor inclusion, via the
  datum-layer symmetry `IsLegendreDatum.neg`. This is the one engine-group factor that
  genuinely acts on the functor `δ` over a general base (see the adjudication below).
* **The concrete datum** `legendreDeltaData` (built on the carrier
  `legendreDelta_relRep_finiteEtale`), its finiteness/étaleness, and the equivariant
  package `legendreDeltaSignEquivariantData :
  EquivariantRelRepData (legendreDeltaSignAction R) X` over the `{±1}`-factor.
* **The full-`G` target** `exists_legendreTorsorData` + `exists_legendreTorsorData_ulift`.
* **Quarantined residuals**: `legendreDelta_exists_naturalFamily` ([T-E14-NAT]),
  `legendreDeltaGAction` ([T-E14-ACT']), `legendreDelta_surjective_of`,
  `legendreDelta_torsor_of`.

## ⚠️ THREE STATEMENT-LAYER DISCOVERIES (T-E14 adjudication)

1. **Universe wall** (identical to T-E15b discovery 1). `TorsorData` pins `G : Type u`,
   but `GL₂(ℤ/2) × ℤˣ : Type 0`, so the chartered full-`G` target elaborates only at
   `CommRingCat.{0}`. `exists_legendreTorsorData` is stated there; the `u`-generic
   consumer form `exists_legendreTorsorData_ulift` `ULift`s the group. (The `{±1}`
   package `legendreDeltaSignEquivariantData` uses `EquivariantRelRepData`'s widened
   `{G : Type*}` and is stated at general `u`.)

2. **The coupled `G`-action does NOT restrict from the ambient product action**
   (the `φ_coupled` construction outcome). The correction block in `Bootstrap.lean`
   (`legendreDelta_relativelyRepresentable_finiteEtale`, and the T-E14 statement-layer
   note) proposed building `φ_coupled : G →* Aut δ` as the **restriction of
   `legendreBootstrapGAction`** along `δ ↪ ambient`. Adversarial check shows this
   SUCCEEDS for the `{±1}`-factor but is **mathematically false for the `GL₂`-factor**:
   * `{±1}` (sign): `legendreBootstrapNegAut` fixes the level datum and negates `ω`;
     `IsLegendreDatum.neg` proves stability, so it restricts — delivered as
     `legendreDeltaNegAut`/`legendreDeltaSignAction` (GENUINE).
   * `GL₂(𝔽₂)`: `legendreBootstrapGlAction γ` re-marks `(P, Q) ↦ glSmul γ⁻¹ (P, Q)`
     while keeping `ω` **fixed**. Over char ≠ 2 the `ω`-adapted models form a
     translation-only torsor (`transVC_of_isAdapted_charNeTwo`, `u` pinned to `1` by
     `ω`); re-marking to a different ordered pair forces the abscissa difference
     `x(Q') − x(P') ∈ {λ, λ−1, …}` to equal `1`, which fails for `λ ∉ {2, …}`. So the
     ambient `GL₂`-action does **not** preserve `IsLegendreDatum` — there is no
     `IsLegendreDatum.glSmul` stability lemma, and asserting one would be sorrying a
     FALSE statement. The genuine coupled `GL₂`-action must **re-scale `ω`** by
     `√(x(Q') − x(P'))` (KM's coupling), which exists only étale-locally on the base
     (the `√λ` sqrt-cover of `SqrtCoverGlue`) — precisely why `δ` is a nontrivial
     torsor. Constructing it as a functor automorphism is the open datum-layer ticket
     **[T-E14-ACT']** (`abscissaDiff`/`basisUnitAt` + the `√`-extraction). It is
     therefore QUARANTINED here as `legendreDeltaGAction`; the honest `{±1}`-factor is
     exposed separately as `legendreDeltaSignAction`.

3. **The Legendre carrier is `∃`-form WITHOUT a natural family** ([T-E14-NAT], new
   vs. T-E15b). T-E15b's `levelThreeData` drew its classifying bijections from
   `YFull.exists_pointsEquiv_family`, which ships `⟨eqv, nat⟩` (naturality PROVEN). The
   Legendre carrier `legendreDelta_relRep_finiteEtale` supplies only `IsFinite`, `Etale`
   and a **`Nonempty`-per-`g`** family of bijections (`ScaleTorsorData.spec` is
   `Nonempty`-valued); a `Classical.choice` per `g` gives independent equivalences whose
   `RelRepData.nat` is genuinely unprovable (false for arbitrary choices). Packaging a
   NATURAL family is the leaf `legendreDelta_exists_naturalFamily` (TRUE — the funnel
   `sectionsCompSigmaEquiv`/`sigmaCongr…` IS natural, once the naturality of the
   scale-torsor `spec` + `fullLevelLocusPointsEquiv` is threaded). `Z`/`f`/finite/étale
   are GENUINE (carry only the `exists_scaleTorsorData` `sorryAx`, the expected
   scale-torsor propagation).

## `sorryAx` propagation

The carrier `legendreDelta_relRep_finiteEtale` is currently gated on the sibling leaf
`exists_scaleTorsorData` (`SqrtCoverGlue.lean`, `sorry`), so every declaration below that
touches `Z`/`f`/finite/étale carries `sorryAx` until it lands, then auto-cleans. This is
the expected, sanctioned propagation.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

variable (R : CommRingCat.{u})

/-! ### The `{±1}`-factor: the genuine restriction of the ambient sign action to `δ`

`legendreDeltaProblem R` is, objectwise, the subtype of `legendreBootstrapProblem R`'s
value (`= (gammaFullNaiveProblem R 2).obj X × (omegaProblem R).obj X`) cut out by
`IsLegendreDatum`. The ambient `{±1}`-automorphism `legendreBootstrapNegAut` (identity on
the level datum, `−1` on `ω`) preserves this subtype by `IsLegendreDatum.neg`, so it
descends to an automorphism of `δ`. -/

/-- **The `{±1}`-automorphism of the coupled Legendre problem `δ`** (GENUINE): the
restriction of `legendreBootstrapNegAut` along `δ ↪ Γ(2)-naive × ω`, using
`IsLegendreDatum.neg` for stability. Identity on the level datum, `−1` on `ω`. -/
noncomputable def legendreDeltaNegAut : Aut (legendreDeltaProblem R) where
  hom :=
    { app := fun X => ↾fun x : { p : (gammaFullNaiveProblem R 2).obj X ×
          OmegaBasis X.unop.curve.toEllipticCurveGeom // IsLegendreDatum X.unop p.1 p.2 } =>
        ⟨(x.1.1, (-1 : Γ(X.unop.base, ⊤)ˣ) • x.1.2), IsLegendreDatum.neg x.2⟩
      naturality := fun X Y φ => by
        ext x
        refine Subtype.ext (Prod.ext rfl ?_)
        refine Eq.trans ?_ (omegaBasisMap_smul φ.unop (-1) x.1.2).symm
        refine (congrArg (· • omegaBasisMap φ.unop x.1.2) (Units.ext ?_)).symm
        rw [Units.coe_map, Units.val_neg, Units.val_one]
        show ((φ.unop.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom) (-1) = -1
        rw [map_neg, map_one] }
  inv :=
    { app := fun X => ↾fun x : { p : (gammaFullNaiveProblem R 2).obj X ×
          OmegaBasis X.unop.curve.toEllipticCurveGeom // IsLegendreDatum X.unop p.1 p.2 } =>
        ⟨(x.1.1, (-1 : Γ(X.unop.base, ⊤)ˣ) • x.1.2), IsLegendreDatum.neg x.2⟩
      naturality := fun X Y φ => by
        ext x
        refine Subtype.ext (Prod.ext rfl ?_)
        refine Eq.trans ?_ (omegaBasisMap_smul φ.unop (-1) x.1.2).symm
        refine (congrArg (· • omegaBasisMap φ.unop x.1.2) (Units.ext ?_)).symm
        rw [Units.coe_map, Units.val_neg, Units.val_one]
        show ((φ.unop.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom) (-1) = -1
        rw [map_neg, map_one] }
  hom_inv_id := by
    ext X x
    refine Subtype.ext (Prod.ext rfl ?_)
    exact (OmegaBasis.mul_smul' _ _ _).trans
      (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)
  inv_hom_id := by
    ext X x
    refine Subtype.ext (Prod.ext rfl ?_)
    exact (OmegaBasis.mul_smul' _ _ _).trans
      (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)

/-- **The `{±1}`-action on `δ`** (GENUINE), in the engine's `G →* Aut Q` interface —
the honest restriction of `legendreBootstrapSignAction` to the coupled subfunctor. This
is the `{±1}`-factor of KM 4.6.2's `G = GL₂(ℤ/2) × {±1}`; the `GL₂`-factor is the
quarantined `[T-E14-ACT']` coupled action (module docstring, discovery 2). -/
noncomputable def legendreDeltaSignAction : ℤˣ →* Aut (legendreDeltaProblem R) where
  toFun u := if u = 1 then 1 else legendreDeltaNegAut R
  map_one' := if_pos rfl
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · rw [one_mul, if_pos rfl, one_mul]
    · rw [one_mul, if_pos rfl, one_mul]
    · rw [mul_one, if_pos rfl, mul_one]
    · rw [show (-1 : ℤˣ) * (-1) = 1 from by decide, if_pos rfl, if_neg (by decide)]
      refine Iso.ext ?_
      refine Eq.symm ?_
      ext X x
      refine Subtype.ext (Prod.ext rfl ?_)
      exact (OmegaBasis.mul_smul' _ _ _).trans
        (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)

/-! ### The concrete Legendre datum on the scale-torsor carrier

`Z`/`f` and their finiteness/étaleness are extracted GENUINELY from the carrier
`legendreDelta_relRep_finiteEtale` (they carry only the `exists_scaleTorsorData`
`sorryAx`). The classifying-bijection *natural family* is the quarantined leaf
`legendreDelta_exists_naturalFamily` (discovery 3). -/

/-- The relative representing scheme of the Legendre `δ` (from the carrier). -/
noncomputable def legendreDeltaZ (hR : IsUnit (2 : R)) (X : EllObj R) : Scheme.{u} :=
  (legendreDelta_relRep_finiteEtale R hR X).choose

/-- Its structure morphism to the base (from the carrier). -/
noncomputable def legendreDeltaF (hR : IsUnit (2 : R)) (X : EllObj R) :
    legendreDeltaZ R hR X ⟶ X.base :=
  (legendreDelta_relRep_finiteEtale R hR X).choose_spec.choose

/-- The structure map is finite (GENUINE, carrier). -/
theorem legendreDeltaF_isFinite (hR : IsUnit (2 : R)) (X : EllObj R) :
    IsFinite (legendreDeltaF R hR X) :=
  (legendreDelta_relRep_finiteEtale R hR X).choose_spec.choose_spec.1

/-- The structure map is étale (GENUINE, carrier). -/
theorem legendreDeltaF_etale (hR : IsUnit (2 : R)) (X : EllObj R) :
    Etale (legendreDeltaF R hR X) :=
  (legendreDelta_relRep_finiteEtale R hR X).choose_spec.choose_spec.2.1

/-- The carrier's per-`g` (`Nonempty`) classifying bijections. -/
theorem legendreDeltaF_nonempty_eqv (hR : IsUnit (2 : R)) (X : EllObj R)
    {T : Scheme.{u}} (g : T ⟶ X.base) :
    Nonempty ({ h : T ⟶ legendreDeltaZ R hR X // h ≫ legendreDeltaF R hR X = g } ≃
      (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g))) :=
  (legendreDelta_relRep_finiteEtale R hR X).choose_spec.choose_spec.2.2 g

/-- **QUARANTINED [T-E14-NAT] (TRUE)** — a NATURAL family of classifying bijections for
the Legendre carrier. The carrier `legendreDelta_relRep_finiteEtale` only ships a
`Nonempty`-per-`g` family (`ScaleTorsorData.spec` is `Nonempty`-valued), so `RelRepData`'s
`nat` field has no witness yet (module docstring, discovery 3). TRUE: the funnel
`legendreDelta_relRep_finiteEtale_of_scaleTorsor` (`sectionsCompSigmaEquiv` ∘
`sigmaCongrRight spec` ∘ `sigmaCongrLeft (fullLevelLocusPointsEquiv)` ∘
`sigmaSubtypePairEquiv`) IS natural in `T`, once the naturality of `spec` and of
`fullLevelLocusPointsEquiv` is threaded. -/
theorem legendreDelta_exists_naturalFamily (hR : IsUnit (2 : R)) (X : EllObj R) :
    ∃ eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
        { h : T ⟶ legendreDeltaZ R hR X // h ≫ legendreDeltaF R hR X = g } ≃
          (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g)),
      ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
        (h : { h : T ⟶ legendreDeltaZ R hR X // h ≫ legendreDeltaF R hR X = g }),
        eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
          (legendreDeltaProblem R).map (X.pullbackAlongMap g k).op (eqv g h) := by
  sorry

/-- **The Legendre relative representation datum** on the carrier: `Z`/`f` GENUINE from
`legendreDelta_relRep_finiteEtale`; the classifying natural family from
`legendreDelta_exists_naturalFamily` ([T-E14-NAT]). Mirror of `levelThreeData`. -/
noncomputable def legendreDeltaData (hR : IsUnit (2 : R)) (X : EllObj R) :
    ModuliProblem.RelRepData (legendreDeltaProblem R) X where
  Z := legendreDeltaZ R hR X
  f := legendreDeltaF R hR X
  eqv := (legendreDelta_exists_naturalFamily R hR X).choose
  nat := (legendreDelta_exists_naturalFamily R hR X).choose_spec

@[simp]
theorem legendreDeltaData_Z (hR : IsUnit (2 : R)) (X : EllObj R) :
    (legendreDeltaData R hR X).Z = legendreDeltaZ R hR X := rfl

@[simp]
theorem legendreDeltaData_f (hR : IsUnit (2 : R)) (X : EllObj R) :
    (legendreDeltaData R hR X).f = legendreDeltaF R hR X := rfl

/-- Finiteness of the datum's structure map (GENUINE, carrier). -/
theorem legendreDeltaData_finite (hR : IsUnit (2 : R)) (X : EllObj R) :
    IsFinite (legendreDeltaData R hR X).f :=
  legendreDeltaF_isFinite R hR X

/-- Étaleness of the datum's structure map (GENUINE, carrier). -/
theorem legendreDeltaData_etale (hR : IsUnit (2 : R)) (X : EllObj R) :
    Etale (legendreDeltaData R hR X).f :=
  legendreDeltaF_etale R hR X

/-- **The `{±1}`-equivariant package** on the Legendre carrier — the `{±1}`-factor
analogue of `levelThreeEquivariantData`, obtained by transporting `legendreDeltaSignAction`
through the datum via the stable `exists_equivariant` ([GHB1]). Genuine modulo the
[T-E14-NAT]/scale-torsor `sorryAx` carried through `legendreDeltaData`; witnesses that the
`{±1}`-action lifts to a finite étale equivariant datum on `δ`. -/
noncomputable def legendreDeltaSignEquivariantData (hR : IsUnit (2 : R)) (X : EllObj R) :
    ModuliProblem.EquivariantRelRepData (legendreDeltaSignAction R) X :=
  (ModuliProblem.RelRepData.exists_equivariant (legendreDeltaSignAction R)
    (legendreDeltaData R hR X) (legendreDeltaData_finite R hR X)
    (legendreDeltaData_etale R hR X)).some

/-! ### The full engine action `G = GL₂(𝔽₂) × {±1}` and the quarantined residuals -/

/-- **QUARANTINED [T-E14-ACT'] (the coupled `G`-action)** — KM 4.6.2's
`G = GL₂(ℤ/2) × {±1}` acting on the coupled Legendre problem `δ`. The `{±1}`-factor is
the GENUINE `legendreDeltaSignAction R`; the `GL₂(𝔽₂)`-factor is the open datum-layer
ticket (module docstring, discovery 2): it re-marks `(P, Q)` AND re-scales `ω` by
`√(x(Q') − x(P'))`, which is NOT the ambient `legendreBootstrapGAction` (that keeps `ω`
fixed and fails to preserve `IsLegendreDatum`) and exists only over the `√λ` sqrt-cover.
Building it as a functor automorphism awaits the `abscissaDiff`/`basisUnitAt` +
`√`-extraction machinery. -/
noncomputable def legendreDeltaGAction :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) × ℤˣ →* Aut (legendreDeltaProblem R) :=
  sorry

/-- **The coupled `G`-equivariant datum** on the carrier (via the stable
`exists_equivariant` transport, [GHB1]); gated on `legendreDeltaGAction` ([T-E14-ACT']).
Its `σZ`/`over_base`/`equivariant`/finite/étale feed the torsor target. -/
noncomputable def legendreDeltaGEquiv (hR : IsUnit (2 : R)) (X : EllObj R) :
    ModuliProblem.EquivariantRelRepData (legendreDeltaGAction R) X :=
  (ModuliProblem.RelRepData.exists_equivariant (legendreDeltaGAction R)
    (legendreDeltaData R hR X) (legendreDeltaData_finite R hR X)
    (legendreDeltaData_etale R hR X)).some

section Quarantine

variable {R}

/-- **PROVEN (T-G3a)** — surjectivity of the Legendre structure map (the covering half of
KM 4.6.2's axiom 2, KM's torsor over `S[1/2]`): the `N = 2` analogue of
`levelThree_surjective`. Over a point `y` of the base, take the anchored geometric point
`t : Spec k̄ ⟶ X.base` above it (`EllObj.exists_geometricPoint_at`), produce a Legendre
datum on the fibre (`exists_isLegendreDatum_of_isAlgClosed`, T-G3a-SUB2) and classify it
through `E.eqv t` to a `Z`-point over `t`; its image is `y`.

⚠ **B2 (statement fix, 2026-07-25).** The register as previously stated — without
`hR : IsUnit (2 : R)` — is FALSE: over `R = 𝔽₂` the Legendre problem has no objects over
any nonempty base (a Legendre chart forces `Δ = 16·λ²(λ−1)²` to be a unit), so the empty
scheme is an equivariant relative representing datum and its structure map `∅ ⟶ X.base`
is not surjective. The hypothesis is available at every call site (`2` invertible is the
standing hypothesis of the whole Legendre leg). -/
theorem legendreDelta_surjective_of (hR : IsUnit (2 : R)) {G : Type*} [Group G] [Finite G]
    {φ : G →* Aut (legendreDeltaProblem R)} {X : EllObj R}
    (E : ModuliProblem.EquivariantRelRepData φ X) :
    AlgebraicGeometry.Surjective E.toRelRepData.f := by
  constructor
  intro y
  have hR' : IsUnit ((2 : ℕ) : R) := by rwa [Nat.cast_ofNat]
  obtain ⟨k, hfk, hak, t, hk, hrange⟩ := EllObj.exists_geometricPoint_at R X y 2 hR'
  letI := hfk
  letI := hak
  obtain ⟨L, b, hLb⟩ := exists_isLegendreDatum_of_isAlgClosed X k (by exact_mod_cast hk) t
  obtain ⟨z, hz⟩ := (E.eqv t).symm ⟨⟨L, b⟩, hLb⟩
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨z.base pt, ?_⟩
  have h1 : E.toRelRepData.f.base (z.base pt) = t.base pt := by
    have h0 : (z ≫ E.toRelRepData.f).base pt = t.base pt := congrArg (fun m => m.base pt) hz
    rwa [Scheme.Hom.comp_apply] at h0
  rw [h1]
  have hmem : t.base pt ∈ Set.range t.base := ⟨pt, rfl⟩
  rw [hrange] at hmem
  exact hmem

/-- **QUARANTINED (geometric, TRUE)** — the torsor comparison
`(γ, z) ↦ (γ·z, z) : ∐_G E.Z ≅ E.Z ×_S E.Z` is an isomorphism: fibrewise simple
transitivity of `G` on Legendre data (`|G| = 12 = 6 × 2`, KM 4.6.2's heart). Route (as
`levelThree_torsor`): the comparison is a finite étale morphism of `Z`-schemes reduced to
constant fibre-rank `1` via `Scheme.Hom.isIso_iff_finrank_eq`. Stated for any equivariant
datum; instantiated at the coupled `legendreDeltaGEquiv` and its `ULift`. -/
theorem legendreDelta_torsor_of {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut (legendreDeltaProblem R)} {X : EllObj R}
    (E : ModuliProblem.EquivariantRelRepData φ X) :
    IsIso ((Sigma.desc fun γ : G =>
      pullback.lift (E.σZ.hom γ) (𝟙 E.toRelRepData.Z)
        (by rw [Category.id_comp]; exact E.over_base γ)) :
      (∐ fun _ : G => E.toRelRepData.Z) ⟶
        pullback E.toRelRepData.f E.toRelRepData.f) :=
  sorry

end Quarantine

/-! ### The chartered targets -/

/-- **T-E14 (the Legendre `TorsorData` package — KM 4.7 axiom 2 at
`(N, G) = (2, GL₂(𝔽₂) × {±1})`)**: the coupled Legendre problem `δ` carries a finite
étale `GL₂(ℤ/2) × {±1}`-torsor datum at every `X` with `2` invertible.

⚠️ Stated at `CommRingCat.{0}` — the unique universe where the statement elaborates
(discovery 1: `TorsorData` pins `G : Type u`, and `GL₂(ℤ/2) × ℤˣ : Type 0`).

Assembly: the coupled equivariant datum `legendreDeltaGEquiv` (datum + `σZ`/`over_base`/
`equivariant`/finite/étale via the `exists_equivariant` transport, [GHB1]) + the
quarantined geometric residuals `legendreDelta_surjective_of`/`legendreDelta_torsor_of`,
over the quarantined coupled action `legendreDeltaGAction` ([T-E14-ACT'], discovery 2).
The GENUINE `{±1}`-sub-package is `legendreDeltaSignEquivariantData`. -/
theorem exists_legendreTorsorData (R : CommRingCat.{0}) (hR : IsUnit (2 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData (legendreDeltaGAction R) X) :=
  ⟨{ toRelRepData := (legendreDeltaGEquiv R hR X).toRelRepData
     σZ := (legendreDeltaGEquiv R hR X).σZ
     over_base := (legendreDeltaGEquiv R hR X).over_base
     equivariant := (legendreDeltaGEquiv R hR X).equivariant
     finite := (legendreDeltaGEquiv R hR X).finite
     etale := (legendreDeltaGEquiv R hR X).etale
     surjective := legendreDelta_surjective_of hR (legendreDeltaGEquiv R hR X)
     torsor := legendreDelta_torsor_of (legendreDeltaGEquiv R hR X) }⟩

/-- **T-E14, the `u`-generic consumer form**: at `CommRingCat.{u}`, over the `ULift`ed
engine group `ULift (GL₂(ℤ/2) × {±1})` (via `MulEquiv.ulift`), sidestepping the
`TorsorData` `G : Type u` universe wall (discovery 1). Built directly from the
`exists_equivariant` transport of the `ULift`ed action (the `LevelThreeTorsor`
`Sigma.map'`-reindex recipe is unnecessary under this transport). -/
theorem exists_legendreTorsorData_ulift (R : CommRingCat.{u}) (hR : IsUnit (2 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData
      ((legendreDeltaGAction R).comp
        (MulEquiv.ulift
          (α := Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) × ℤˣ)).toMonoidHom) X) :=
  let E := (ModuliProblem.RelRepData.exists_equivariant
    ((legendreDeltaGAction R).comp
      (MulEquiv.ulift
        (α := Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) × ℤˣ)).toMonoidHom)
    (legendreDeltaData R hR X) (legendreDeltaData_finite R hR X)
    (legendreDeltaData_etale R hR X)).some
  ⟨{ toRelRepData := E.toRelRepData
     σZ := E.σZ
     over_base := E.over_base
     equivariant := E.equivariant
     finite := E.finite
     etale := E.etale
     surjective := legendreDelta_surjective_of hR E
     torsor := legendreDelta_torsor_of E }⟩

end ModularCurves
