/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.GammaH
import ModularCurves.Moduli.OmegaFunctor
import ModularCurves.Moduli.UniversalAdapted
import ModularCurves.Moduli.LegendreDelta
import ModularCurves.Moduli.UniversalLegendre
import ModularCurves.Moduli.UniversalLevelThree
import ModularCurves.Moduli.E3DatumAssembly
import ModularCurves.Moduli.BridgeAssembly
import ModularCurves.LevelStructure.CombinationLevel

/-!
# The KM 4.7 bootstrap objects (T-E12–T-E15)

The ⇐ direction of `representable_iff` (T-E5 = KM SCHOLIE 4.7.0 = Loeffler 3.7.4) is proved
by KM's axiomatized engine (KM p. 112, verbatim in `.mathlib-quality/km47-source-quotes.md`):

> "Let `N ≥ 1` be an integer, `G` a finite group, and `δ` a relatively representable and
> affine moduli problem on (Ell) which satisfies the following axioms: 1) `δ` is
> representable, by an affine `ℤ[1/N]`-scheme. 2) `G` operates upon `δ`, in such a way that
> for every elliptic curve `E/S` with `S` a `ℤ[1/N]`-scheme, the `S`-scheme `δ_{E/S}` is a
> finite etale `G`-torsor. We claim that over `ℤ[1/N]`, `𝒫` is represented by the affine
> `ℤ[1/N]`-scheme `𝕸(𝒫, δ)/G`."

applied twice — `(N, δ, G) = (2, Legendre, GL₂(ℤ/2) × {±1})` and `(3, naive level 3,
GL₂(𝔽₃))` — and then glued over `ℤ[1/6]` by "recollement". The engine itself is
`representable_of_rigid_of_torsor` (`Moduli/QuotientProblem.lean`, ticket T-Q6e). This file
holds the two **bootstrap objects** it consumes, i.e. the `δ`'s and their axioms.

## Status of the four bootstrap tickets (cut 2026-07-08, T-E5-KM47 part (2))

* **T-E15 (naive level 3, `ℰ₃`)** — statable *now*: the problem is
  `gammaFullNaiveProblem R 3`, already defined. Its two engine-axioms are the `sorry`d
  theorems below. Explicit model (KM Ex. 2.2.2, GME 2.2.10):
  `Spec ℤ[1/3][β, γ][((a₁³ − 27a₃)a₃)⁻¹]/(β³ − (β+γ)³)` with `a₁ = 3γ − 1`,
  `a₃ = −3γ² − β − 3βγ`, `P = (0,0)`, `Q = (γ, β+γ)`.
* **T-E12 (`M₁ = Spec ℤ[1/6, g₂, g₃, Δ⁻¹]`)**, **T-E13 (`Aut_S(E, ω) = {1}`)** and
  **T-E14 (Legendre, `M'₂ = Spec ℤ[1/2, λ, (λ(λ−1))⁻¹]`)** — **STATABLE as of 2026-07-13**
  (STREAM-OMEGA, ★★): [T-E-OMEGA] delivered `ω_{E/S}` as the chart-presented invertible
  sheaf `omegaModules` with its `𝔾ₘ`-torsor of bases `OmegaBasis`
  (`EllipticCurve/InvariantDifferential.lean`) and the `(Ell/R)`-functorial transport
  `omegaBasisMap` (`Moduli/OmegaFunctor.lean`), packaged as the moduli problem
  **`omegaProblem : ModuliProblem R`** — exactly KM 4.6.2's *"an `S`-basis `ω` of
  `ω_{E/S}`"* datum. Their statements are the `sorry`d theorems below; the Legendre
  problem is the product `Γ(2)`-naive × ω (`legendreBootstrapProblem`).

The `ℤ[1/2]`-half of the bootstrap is hence UNBLOCKED alongside the `ℤ[1/3]`-half. (The
level-4 alternative recorded on the board is now moot but retained there for history.)
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable (R : CommRingCat.{u})

/-! ### T-E15 — the naive level 3 bootstrap object `ℰ₃` over `ℤ[1/3]` -/

/-- **(T-E15a, KM engine axiom 1 for `δ = ` naive level 3; KM Ex. 2.2.2 / GME 2.2.10)**
Over a base in which `3` is invertible, the naive level-3 problem is representable by an
object whose base is **affine** — explicitly `Y(3) = Spec ℤ[1/3][β, γ][((a₁³−27a₃)a₃)⁻¹] /
(β³ − (β+γ)³)` with `a₁ = 3γ − 1`, `a₃ = −3γ² − β − 3βγ`, carrying `P = (0,0)`,
`Q = (γ, β+γ)`.

This is the `N = 3` instance of KM COROLLARY 4.7.2 *proved by hand* (not via 4.7.1 — that
would be circular: 4.7.1 is what this object bootstraps). Route: the AME 2.2.10 computation
— normalise a Weierstrass model so that `P` is a flex at the origin (`[3]P = 0`), read off
`a₁, a₃`, and check the universal property against `EllipticCurve.Point`; the repo's
`VariableChange` machinery (`EllipticCurve/ModelVariableChange.lean`, `WeierstrassModel`)
plus `ForMathlib/TateNormalForm.lean` are the intended engines. -/
theorem naiveLevelThree_representable_by_affine (hR : IsUnit (3 : R)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((gammaFullNaiveProblem R 3).RepresentableBy X) := by
  -- TURNKEY (STREAM-OMEGA v10.262): the entire ℰ₃ representability machine is applied here;
  -- the two remaining goals are EXACTLY the keystone (`hL`) + bridge (`hArb`) inputs, both
  -- bottoming out at KM brick 6 → BB-DEG (torsion→coord bridges + E[3] generation). The
  -- instant those land this becomes sorry-free.
  refine naiveLevelThree_representable_by_affine_of_conditions R hR ?_ ?_
  · -- `hL`: the universal marked pair `(P, Q) = ((0,0), (γ, β+γ))` is a naive full level-`3`
    -- structure — the unconditional Stage-D killing `[3]P = [3]Q = 0`
    -- (`three_zsmul_universalE3P/Q_of_isUnit`) + the geometric `E[3]`-generation
    -- (`universalE3_generation`: BB-DEG rank 9 + Stage-B dictionary + GH's B2 criterion).
    exact ⟨⟨by exact_mod_cast three_zsmul_universalE3P_of_isUnit R hR,
        by exact_mod_cast three_zsmul_universalE3Q_of_isUnit R hR⟩,
      fun k _ _ t x hx => universalE3_generation R hR k t x hx⟩
  · -- `hArb`: every naive level-`3` structure IS an `ℰ₃`-datum — TURNKEY (CHARTER-O (O2)):
    -- the whole assembly is `isE3Datum_of_bridges`; the two remaining goals are EXACTLY
    -- the KM-split bridge-Props (board v10.310/v10.312; `bridgeP/Q_of_psi3_eval` massage
    -- them from the `Ψ₃`-form `3•σ = 0 ⟹ Ψ₃(x(σ)) = 0` when KM's K1 lands).
    intro X L
    refine isE3Datum_of_bridges X hR L ?_ ?_
    · -- BRIDGE-P: RING-DBL + the negation coordinate + KM's certificate
      -- (`BridgeAssembly.bridgeP_holds`).
      exact fun V Pr hM => bridgeP_holds X hR L V Pr hM
    · -- BRIDGE-Q: RING-DBL + the Ψ₃ certificate + the abscissa unit
      -- (`BridgeAssembly.bridgeQ_holds`).
      exact fun V Pr ha₂ ha₄ ha₆ hMP p q hMQ =>
        bridgeQ_holds X hR L V Pr ha₂ ha₄ ha₆ hMP p q hMQ

/-- **(T-E15b, KM engine axiom 2 for `δ = ` naive level 3)** For every elliptic curve `E/S`
over a base in which `3` is invertible, the `S`-scheme `δ_{E/S}` relatively representing the
naive level-3 problem is **finite étale over `S`** — the underlying scheme of the
`GL₂(𝔽₃)`-torsor of KM's axiom 2 (KM p. 112).

Stated here in the torsor-free shape (finite + étale + the relative representability
bijection), matching `gammaHNaive_relativelyRepresentable`'s packaging; the
simply-transitive `GL₂(𝔽₃)`-action is supplied separately by `EllipticCurve.glSmul`
(`Moduli/GammaH.lean`) and the torsor property is `T-Q2`'s `InvariantTorsor` datum. Route:
`E[3]` is finite étale of rank 9 when `3` is invertible (T-B5), and a naive full level-3
structure is exactly a basis of it, so `δ_{E/S}` is the `Isom`-scheme
`Isom_S((ℤ/3)², E[3])`, an open-and-closed subscheme of `E[3] ×_S E[3]` cut out by the
non-vanishing of the Weil pairing (Loe 3.8.2 — consumes stream C). -/
theorem naiveLevelThree_relativelyRepresentable_finiteEtale (hR : IsUnit (3 : R))
    (X : EllObj R) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
        ({ h : T ⟶ Z // h ≫ f = g } ≃
          (gammaFullNaiveProblem R 3).obj (Opposite.op (X.pullbackAlong g))) := by
  -- the combination-clopen carrier (board v10.266-OMEGA route; no Weil pairing):
  -- `Z := {(P,Q) ∈ E[3] ×_S E[3] : all eight combinations avoid the zero section}`
  have h3 : NIsInvertible X.base 3 := by
    have h0 : NIsInvertible (Spec R) 3 := by
      rw [NIsInvertible, Nat.cast_ofNat]
      have := hR.map (Scheme.ΓSpecIso R).inv.hom
      rwa [map_ofNat] at this
    exact h0.of_hom X.structMap
  exact ⟨X.curve.fullLevelLocus 3 h3, X.curve.fullLevelLocusπ 3 h3,
    X.curve.fullLevelLocusπ_isFinite 3 h3, X.curve.fullLevelLocusπ_etale 3 h3,
    fun {T} g => ⟨X.curve.fullLevelLocusPointsEquiv 3 h3 g⟩⟩

/-! ### T-E12 / T-E13 — the `(E, ω)` problem over `ℤ[1/6]` (GME Thm 2.2.3 / Cor 2.2.4) -/

/-- **(T-E12, GME Thm 2.2.3; KM 2.2)** Over a base in which `6` is invertible, the
ω-moduli problem `[(E, ω)]` is representable by an object with **affine** base —
explicitly `M₁ = Spec ℤ[1/6][g₂, g₃][Δ⁻¹]`, universal curve `y² = 4x³ − g₂x − g₃`
with `ω = dx/y`. Route: A7 uniqueness of the `(g₂, g₃)`-normalised Weierstrass model
given `ω` (`WeierstrassModel.lean`'s normalisation machinery + `omegaCocycle_res` to
compare `ω`-data chartwise). -/
theorem omegaProblem_representable_by_affine (hR : IsUnit (6 : R)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((omegaProblem R).RepresentableBy X) :=
  ⟨universalEllObj R,
    inferInstanceAs (IsAffine (AlgebraicGeometry.Spec
      (CommRingCat.of (ModuliRingE12 R)))),
    ⟨omegaRepresentableBy R hR⟩⟩

/-- **(T-E13, GME Cor 2.2.4)** `Aut_S(E, ω) = {1}`: the ω-problem is **rigid** over
`ℤ[1/6]` — no nontrivial automorphism of `E/S` over the identity of `S` fixes an
`S`-basis of `ω_{E/S}`. One-liner from T-E12's representability; do NOT re-derive
rigidity from scratch — `EllipticCurve/Rigidity.lean`'s canonicity chain (in particular
`isMonHom_of_one_comp_eq'`) is the intended engine for "an automorphism fixing the zero
section". -/
theorem omegaProblem_rigid (hR : IsUnit (6 : R)) : (omegaProblem R).Rigid :=
  ModuliProblem.rigid_of_representable (omegaRepresentableBy R hR).isRepresentable

/-! ### T-E14 — the Legendre bootstrap object `M'₂` over `ℤ[1/2]` (KM 4.6.2 / GME Ex. 2.2.1) -/

/-- **(T-E14, the `δ` of KM 4.6.2)** The simultaneous **`Γ(2)`-naive × ω** problem:
`E/S ↦ {((P, Q), ω)}` with `(P, Q)` a naive full level-2 structure and `ω` an `S`-basis
of `ω_{E/S}`. KM 4.6.2 verbatim: *"pairs `(φ₂, ω)` consisting of an `S`-group-scheme
isomorphism `φ₂ : (ℤ/2ℤ)² ≅ E[2]` together with an `S`-basis `ω` of `ω_{E/S}`"*; the
engine group is `G = GL₂(ℤ/2) × {±1}`, acting through `EllipticCurve.glSmul` on the
level datum and `negVC_u : u = −1` (ω5) on the `ω`-datum. -/
noncomputable def legendreBootstrapProblem : ModuliProblem R where
  obj X := (gammaFullNaiveProblem R 2).obj X × (omegaProblem R).obj X
  map φ := ↾fun x => ⟨(gammaFullNaiveProblem R 2).map φ x.1, (omegaProblem R).map φ x.2⟩
  map_id X := by
    ext x
    · exact FunctorToTypes.map_id_apply (gammaFullNaiveProblem R 2) x.1
    · exact FunctorToTypes.map_id_apply (omegaProblem R) x.2
  map_comp φ ψ := by
    ext x
    · exact FunctorToTypes.map_comp_apply (gammaFullNaiveProblem R 2) φ ψ x.1
    · exact FunctorToTypes.map_comp_apply (omegaProblem R) φ ψ x.2

/-- **(T-E14-AX1, KM engine axiom 1 for the corrected Legendre `δ`; KM 4.6.2 / GME
Ex. 2.2.1)** Over a base in which `2` is invertible, the Legendre-marked problem is
representable by an object whose base is **affine** — explicitly
`M'₂ = Spec R[λ][(λ(λ−1))⁻¹]` carrying the Legendre curve `y² = x(x−1)(x−λ)` with the
tautological marking `P = (0,0), Q = (1,0)` and `ω = dx/y`. Route (the T-E12-D replay
for the Legendre datum): the universal Legendre object via `tautPresentation` +
`projModelAffineSection`; classification by the glued `λ`-function of the unique
marked adapted local models (`transVC_of_isAdapted_charNeTwo` + KM 2.2.9's marking
pins the translation; `legendreCurve_vc_marked` pins the rest). -/
theorem legendreDelta_representable_by_affine (hR : IsUnit (2 : R)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((legendreDeltaProblem R).RepresentableBy X) := by
  -- DISCHARGED modulo [T-E14-LVL-b] by `legendreDelta_representable_by_affine_of_level`
  -- (Moduli/UniversalLegendre.lean): the sole remaining input is the naive-full-level
  -- clause for the universal marked pair — killing ✓ (`two_zsmul_universalLegendreP/Q`);
  -- geometric `E[2]`-generation = the KM-keystone deferral.
  refine legendreDelta_representable_by_affine_of_level R hR ⟨?_, ?_⟩
  · exact ⟨two_zsmul_universalLegendreP R hR, two_zsmul_universalLegendreQ R hR⟩
  · -- geometric `E[2]`-generation: `#T₂ = 4` (KM rank-two count) + the Stage-B
    -- dictionary values `some(0,0)`, `some(1,0)` + `combos2_ne_zero` through the
    -- criterion of record `pair_generates_iff_combos_ne_zero`.
    exact fun k _ _ t x hx => universalLegendre_generation R hR k t x hx

/-- **(T-E14-AX2, KM engine axiom 2 for the corrected Legendre `δ`)** For every
elliptic curve `E/S` over a base in which `2` is invertible, the `S`-scheme relatively
representing the Legendre-marked problem is **finite étale over `S`** — the underlying
scheme of the `GL₂(ℤ/2) × {±1}`-torsor of KM 4.6.2's axiom 2 (`|G| = 12`: six
orderings of the three `2`-torsion abscissae × the `±ω` pair fixing the scale
`u² = x(Q) − x(P)`). Stated in the torsor-free shape matching
`naiveLevelThree_relativelyRepresentable_finiteEtale`; the `G`-action on `δ` itself is
the COUPLED action (the `GL₂`-factor re-marks the pair and re-scales `ω`
accordingly — NOT the ambient product action of `legendreBootstrapGAction`), tracked
as ticket [T-E14-ACT']. -/
theorem legendreDelta_relativelyRepresentable_finiteEtale (hR : IsUnit (2 : R))
    (X : EllObj R) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
        ({ h : T ⟶ Z // h ≫ f = g } ≃
          (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g))) := by
  sorry

/-! #### T-E14 statement-layer correction (2026-07-14, OMEGA — adversarial source check)

KM 4.6.2 VERBATIM defines the Legendre problem as pairs `(φ₂, ω)` **"for which the
adapted `x` satisfies `x(P₂) = 0, x(Q₂) = 1`"** — the `ω`-datum and the level datum are
COUPLED through the `ω`-adapted Weierstrass model (KM 2.2.5/2.2.9). The plain product
`legendreBootstrapProblem = Γ(2)-naive × ω` above is the AMBIENT functor, a `𝔾ₘ`-bundle
over KM's `δ`; the two engine axioms are FALSE for it (its fibres are not finite), so
the two axiom-statement skeletons previously recorded here were RETRACTED before any
proof work targeted them. Stating KM's true `δ` needs the `(E, ω)`-adapted-model layer
— exactly T-E12's A7-normalisation machinery — so the corrected order of battle is:
T-E12 (adapted models + `M₁`) → T-E14' (the adapted subfunctor + axioms 1/2 over
`M'₂ = Spec ℤ[1/2][λ][(λ(λ−1))⁻¹]`). The `GL₂(ℤ/2) × {±1}`-action infrastructure below
remains valid: KM's `δ` is a `G`-stable subfunctor of the ambient product, and the
action restricts. -/

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-ACT)** The `{±1}`-automorphism of the (ambient) Legendre problem:
identity on the level datum, sign on the `ω`-datum. -/
noncomputable def legendreBootstrapNegAut :
    Aut (legendreBootstrapProblem R) where
  hom :=
    { app := fun X => ↾fun x : (gammaFullNaiveProblem R 2).obj X ×
          OmegaBasis X.unop.curve.toEllipticCurveGeom =>
        (x.1, (-1 : Γ(X.unop.base, ⊤)ˣ) • x.2)
      naturality := fun X Y φ => by
        ext x
        refine Prod.ext rfl ?_
        refine Eq.trans ?_ (omegaBasisMap_smul φ.unop (-1) x.2).symm
        refine (congrArg (· • omegaBasisMap φ.unop x.2) (Units.ext ?_)).symm
        rw [Units.coe_map, Units.val_neg, Units.val_one]
        show ((φ.unop.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom) (-1) = -1
        rw [map_neg, map_one] }
  inv :=
    { app := fun X => ↾fun x : (gammaFullNaiveProblem R 2).obj X ×
          OmegaBasis X.unop.curve.toEllipticCurveGeom =>
        (x.1, (-1 : Γ(X.unop.base, ⊤)ˣ) • x.2)
      naturality := fun X Y φ => by
        ext x
        refine Prod.ext rfl ?_
        refine Eq.trans ?_ (omegaBasisMap_smul φ.unop (-1) x.2).symm
        refine (congrArg (· • omegaBasisMap φ.unop x.2) (Units.ext ?_)).symm
        rw [Units.coe_map, Units.val_neg, Units.val_one]
        show ((φ.unop.baseHom.appLE ⊤ ⊤ (fun x _ => trivial)).hom) (-1) = -1
        rw [map_neg, map_one] }
  hom_inv_id := by
    ext X x
    refine Prod.ext rfl ?_
    exact (OmegaBasis.mul_smul' _ _ _).trans
      (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)
  inv_hom_id := by
    ext X x
    refine Prod.ext rfl ?_
    exact (OmegaBasis.mul_smul' _ _ _).trans
      (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)

/-- **(T-E14-ACT)** The `{±1}`-half of KM 4.6.2's `G = GL₂(ℤ/2) × {±1}` on the
(ambient) Legendre problem, in the engine's `G →* Aut Q` interface. -/
noncomputable def legendreBootstrapSignAction :
    ℤˣ →* Aut (legendreBootstrapProblem R) where
  toFun u := if u = 1 then 1 else legendreBootstrapNegAut R
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
      refine Prod.ext rfl ?_
      exact (OmegaBasis.mul_smul' _ _ _).trans
        (by rw [neg_one_mul, neg_neg]; exact OmegaBasis.one_smul' _)

open EllipticCurve in
private theorem pullSection_zsmul' {X Y : EllObj R} (f : X ⟶ Y) (n : ℤ)
    (P : Y.curve.Section) :
    EllHom.pullSection R f (n • P) = n • EllHom.pullSection R f P :=
  map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f)
    (EllHom.pullSection_add R f)) n P

open EllipticCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-ACT)** The `GL₂(ℤ/N)`-automorphism of the naive full-level problem
induced by `glSmul` (T-H2). Natural because `glSmul` is an integer-linear combination
of the sections and `EllHom.pullSection` is `ℤ`-linear. -/
noncomputable def gammaFullNaiveGlAut (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    Aut (gammaFullNaiveProblem R N) where
  hom :=
    { app := fun X => ↾fun L : X.unop.curve.FullLevelPt N => X.unop.curve.glSmul γ L
      naturality := fun X Y φ => by
        ext L
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact ((EllHom.pullSection_add R φ.unop _ _).trans
            (congrArg₂ (· + ·) (pullSection_zsmul' R φ.unop _ _)
              (pullSection_zsmul' R φ.unop _ _))).symm
        · exact ((EllHom.pullSection_add R φ.unop _ _).trans
            (congrArg₂ (· + ·) (pullSection_zsmul' R φ.unop _ _)
              (pullSection_zsmul' R φ.unop _ _))).symm }
  inv :=
    { app := fun X => ↾fun L : X.unop.curve.FullLevelPt N => X.unop.curve.glSmul γ⁻¹ L
      naturality := fun X Y φ => by
        ext L
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact ((EllHom.pullSection_add R φ.unop _ _).trans
            (congrArg₂ (· + ·) (pullSection_zsmul' R φ.unop _ _)
              (pullSection_zsmul' R φ.unop _ _))).symm
        · exact ((EllHom.pullSection_add R φ.unop _ _).trans
            (congrArg₂ (· + ·) (pullSection_zsmul' R φ.unop _ _)
              (pullSection_zsmul' R φ.unop _ _))).symm }
  hom_inv_id := by
    ext X L
    exact (X.unop.curve.glSmul_mul γ γ⁻¹ L).symm.trans
      (by rw [mul_inv_cancel]; exact X.unop.curve.glSmul_one L)
  inv_hom_id := by
    ext X L
    exact (X.unop.curve.glSmul_mul γ⁻¹ γ L).symm.trans
      (by rw [inv_mul_cancel]; exact X.unop.curve.glSmul_one L)

open EllipticCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-ACT)** The `GL₂(ℤ/N)`-action on the naive full-level problem in the
engine's `G →* Aut Q` interface: `γ` acts through the `γ⁻¹`-automorphism (the inverse
compensates the precomposition anti-law `glSmul_mul`). -/
noncomputable def gammaFullNaiveGlAction (N : ℕ) [NeZero N] :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod N) →* Aut (gammaFullNaiveProblem R N) where
  toFun γ := gammaFullNaiveGlAut R N γ⁻¹
  map_one' := by
    rw [inv_one]
    refine Iso.ext ?_
    ext X L
    show X.unop.curve.glSmul 1 L = L
    exact X.unop.curve.glSmul_one L
  map_mul' γ δ := by
    refine Iso.ext ?_
    ext X L
    show X.unop.curve.glSmul (γ * δ)⁻¹ L =
      X.unop.curve.glSmul γ⁻¹ (X.unop.curve.glSmul δ⁻¹ L)
    rw [mul_inv_rev]
    exact X.unop.curve.glSmul_mul δ⁻¹ γ⁻¹ L

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(T-E14-ACT)** Lift an automorphism of the level problem to the Legendre product
(identity on the `ω`-datum). -/
noncomputable def legendreBootstrapLevelAut (α : Aut (gammaFullNaiveProblem R 2)) :
    Aut (legendreBootstrapProblem R) where
  hom :=
    { app := fun X => ↾fun x : (gammaFullNaiveProblem R 2).obj X ×
          OmegaBasis X.unop.curve.toEllipticCurveGeom =>
        (α.hom.app X x.1, x.2)
      naturality := fun X Y φ => by
        ext x
        refine Prod.ext ?_ rfl
        exact CategoryTheory.congr_fun (α.hom.naturality φ) x.1 }
  inv :=
    { app := fun X => ↾fun x : (gammaFullNaiveProblem R 2).obj X ×
          OmegaBasis X.unop.curve.toEllipticCurveGeom =>
        (α.inv.app X x.1, x.2)
      naturality := fun X Y φ => by
        ext x
        refine Prod.ext ?_ rfl
        exact CategoryTheory.congr_fun (α.inv.naturality φ) x.1 }
  hom_inv_id := by
    ext X x
    refine Prod.ext ?_ rfl
    exact CategoryTheory.congr_fun (NatTrans.congr_app α.hom_inv_id X) x.1
  inv_hom_id := by
    ext X x
    refine Prod.ext ?_ rfl
    exact CategoryTheory.congr_fun (NatTrans.congr_app α.inv_hom_id X) x.1

/-- **(T-E14-ACT)** The level-factor action on the Legendre problem. -/
noncomputable def legendreBootstrapGlAction :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) →* Aut (legendreBootstrapProblem R) where
  toFun γ := legendreBootstrapLevelAut R (gammaFullNaiveGlAction R 2 γ)
  map_one' := by
    rw [map_one]
    refine Iso.ext ?_
    ext X x
    exact Prod.ext rfl rfl
  map_mul' γ δ := by
    rw [map_mul]
    refine Iso.ext ?_
    ext X x
    exact Prod.ext rfl rfl

/-- The two factor-actions commute (they act on different components). -/
private theorem legendreBootstrap_actions_comm
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) (u : ℤˣ) :
    legendreBootstrapSignAction R u * legendreBootstrapGlAction R γ =
      legendreBootstrapGlAction R γ * legendreBootstrapSignAction R u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [map_one, one_mul, mul_one]
  · refine Iso.ext ?_
    ext X x
    exact Prod.ext rfl rfl

/-- **(T-E14-ACT ★)** KM 4.6.2's engine group `G = GL₂(ℤ/2) × {±1}` acting on the
Legendre bootstrap problem, in the `G →* Aut Q` interface of
`representable_of_rigid_of_torsor`: `GL₂` through the level datum, `{±1}` through the
`ω`-datum (the factors commute — they act on different components). -/
noncomputable def legendreBootstrapGAction :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) × ℤˣ →*
      Aut (legendreBootstrapProblem R) where
  toFun p := legendreBootstrapGlAction R p.1 * legendreBootstrapSignAction R p.2
  map_one' := by
    show legendreBootstrapGlAction R 1 * legendreBootstrapSignAction R 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' p q := by
    show legendreBootstrapGlAction R (p.1 * q.1) *
        legendreBootstrapSignAction R (p.2 * q.2) = _
    rw [map_mul, map_mul, mul_assoc,
      ← mul_assoc (legendreBootstrapGlAction R q.1),
      ← legendreBootstrap_actions_comm R q.1 p.2, mul_assoc, ← mul_assoc]

end ModularCurves
