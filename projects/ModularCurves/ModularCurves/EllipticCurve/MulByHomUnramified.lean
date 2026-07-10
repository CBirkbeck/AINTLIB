/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.NilpotentKerSpecMap
import ModularCurves.ForMathlib.FormallyUnramifiedFibre
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Unramifiedness of `[N]` via the `E[N]`-torsor (T-B5D / BB-DIFF, scoping skeleton)

`/develop --decompose` skeleton for **BB-DIFF** = `mulByHom_formallyUnramified` (`Torsion.lean:228`,
held): `[N] : E ⟶ E` is formally unramified when `N` is invertible on `S`. It states the leaves of
the **non-circular, HasseWeil-anchored** route (beastmode-B's `tb5z_architecture.md` route (c),
grounded in KM §2.3) as `:= by sorry`, and assembles the target from them. NEW bridge file; the held
`Torsion.lean` / `GroupLawConstruction.lean` are not edited. Full tree, verbatim KM 2.3 / Loeffler
3.4.2(2) quotes, adversarial passes and feasibility live in `.mathlib-quality/decomposition-km2.3-b5d.md`.

## Why not the "obvious" routes (mapped dead ends — do NOT re-litigate)
- **Invariant-differential / scheme `Ω¹`** (KM's own "tangent map at the origin is multiplication by
  `N`"): mathlib has NO invariant differential for `WeierstrassCurve` and NO relative-`Ω¹` sheaf API.
- **Chart route** (categorical `mulByHom = (mulBy N).left` on `GrpObj` ↔ Weierstrass-chart `[N]`):
  that comparison is **T-W7 scope** (A-lane, in progress) — collides.
- The `torsionπ_etale ⟸ mulBy_etale ⟸ mulByHom_formallyUnramified` chain (`Torsion.lean:233-250`)
  and the T-B6 fibre count are currently **circular** in `BB-DIFF`.

## The route (KM §2.3, non-circular)
KM Thm 2.3.1: `[N]` is finite locally free of rank `N²`, and its kernel `E[N]` is finite étale over
`S` when `N` is invertible. KM's proof reduces geometric-fibre-by-fibre and uses KM Cor 2.3.2:
**`[N]` is an f.p.p.f `E[N]`-torsor**, so `[N]` is unramified iff `E[N] → S` is. The fibre-level
`[N]`-separability that mathlib lacks is **already in AINTLIB's HasseWeil** (`InvariantDifferential`,
`OmegaPullbackCoeff`, `EC/KernelCountGeneral.card_kernel_eq_degree_of_separable`, `mulByInt_degree`,
`NTorsion/TorsionGeneralN`) — verified present. So the leaves:

* **L-A** (self-contained core, "build first", route-independent) — `formallyUnramified_mulByHom_of_torsionπ`:
  `FormallyUnramified (torsionπ N) → FormallyUnramified (mulByHom N)`, via the `E[N]`-torsor structure
  (KM 2.3.2) / group infinitesimal-lifting. Cannot collide with any lane.
* **L-BC** (API-gap sub-tree) — `formallyUnramified_torsionπ`: `E[N] → S` is formally unramified when
  `N` is invertible, from (L-B) HasseWeil geometric fibres `E[N]_{k̄}` étale (the crux **T-B6**
  scheme-fibre ↔ HasseWeil-`WeierstrassCurve` comparison) + (L-C = **T-DISC**) the "finite + geometric
  fibres unramified ⟹ unramified" criterion.
* **MASTER** — `mulByHom_formallyUnramified'` = L-A ∘ L-BC (assembled, term-mode; discharges
  `Torsion.lean:228` once L-A and L-BC land).

AINTLIB ModularCurves T-B5D + T-DISC (stream v10.10; planning-only, BB-DIFF discharge route).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- `pointEquivOverHom` carries point-subtraction to the division of `Over`-homs (companion to
`pointEquivOverHom_add`). -/
theorem pointEquivOverHom_sub {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom g) (P - Q) =
      (E.pointEquivOverHom g) P / (E.pointEquivOverHom g) Q := rfl

/-- Restriction of a point along `k` corresponds, under `pointEquivOverHom`, to precomposition by
the induced `Over`-morphism `Over.mk (k ≫ g) ⟶ Over.mk g`. -/
theorem pointEquivOverHom_restrict {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P : E.Point g) :
    E.pointEquivOverHom (k ≫ g) (Point.restrict E k P) =
      (Over.homMk k : Over.mk (k ≫ g) ⟶ Over.mk g) ≫ E.pointEquivOverHom g P := by
  apply Over.OverMorphism.ext
  simp only [pointEquivOverHom, Equiv.coe_fn_mk, Point.restrict, Over.comp_left, Over.homMk_left]
  rfl

/-- `Point.restrict` is additive on subtraction (precomposition is a group homomorphism). -/
theorem restrict_sub {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) :
    Point.restrict E k (P - Q) = Point.restrict E k P - Point.restrict E k Q := by
  apply (E.pointEquivOverHom (k ≫ g)).injective
  simp only [E.pointEquivOverHom_restrict, E.pointEquivOverHom_sub, GrpObj.comp_div]

/-- **(T-B5D, L-A — the self-contained core, build first)** If the `N`-torsion `E[N] → S` is formally
unramified, then so is `[N] : E ⟶ E`. Route-independent: `[N]` is an f.p.p.f `E[N]`-torsor (KM Cor.
2.3.2), so two infinitesimal lifts `g₁, g₂` of `[N]` agreeing on a square-zero closed subscheme differ
by a map into `E[N]` vanishing there, which is `0` once `E[N] → S` is formally unramified — hence
`g₁ = g₂`. Uses only the `GrpObj` group structure of `E` and mathlib's `FormallyUnramified` morphism
property; collides with no lane. This is the piece to land first. -/
theorem formallyUnramified_mulByHom_of_torsionπ (N : ℕ)
    (htors : FormallyUnramified (E.torsionπ N)) :
    FormallyUnramified (E.mulByHom N) := by
  apply FormallyUnramified.of_hom_ext
  intro R S' φ hφ hφ2 g₁ g₂ hthick hf
  -- both lifts share a base `s`
  have hbase : g₁ ≫ E.π = g₂ ≫ E.π := by
    have h := congrArg (fun m => m ≫ E.π) hf
    simpa only [Category.assoc, E.mulByHom_π] using h
  set s : Spec R ⟶ S := g₁ ≫ E.π with hs
  let P₁ : E.Point s := ⟨g₁, hs.symm⟩
  let P₂ : E.Point s := ⟨g₂, hbase.symm.trans hs.symm⟩
  -- the difference is killed by `N`
  have hNP : ((N : ℤ) • P₁ : E.Point s) = (N : ℤ) • P₂ := by
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy]
    exact hf
  have hNh : ((N : ℤ) • (P₁ - P₂) : E.Point s) = 0 := by rw [smul_sub, hNP, sub_self]
  have hkill : ((P₁ - P₂ : E.Point s) : Spec R ⟶ E.E) ≫ E.mulByHom N = s ≫ E.zero :=
    (E.smul_eq_zero_iff_comp_mulByHom s N (P₁ - P₂)).mp hNh
  have hzero : ((0 : E.Point s) : Spec R ⟶ E.E) ≫ E.mulByHom N = s ≫ E.zero :=
    (E.smul_eq_zero_iff_comp_mulByHom s N 0).mp (smul_zero _)
  -- on the thickening, the difference restricts to `0`
  have hci : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have hrestrict : Spec.map φ ≫ ((P₁ - P₂ : E.Point s) : Spec R ⟶ E.E) =
      Spec.map φ ≫ (s ≫ E.zero) := by
    have hPeq : Point.restrict E (Spec.map φ) P₁ = Point.restrict E (Spec.map φ) P₂ :=
      Subtype.ext hthick
    have hh0 : Point.restrict E (Spec.map φ) (P₁ - P₂) = 0 := by
      rw [E.restrict_sub, hPeq, sub_self]
    have hval := congrArg Subtype.val hh0
    simp only [Point.restrict, E.point_zero_val] at hval
    rw [hval, Category.assoc]
  -- the two torsion points agree after the thickening and after `torsionπ`
  have e1 : (Spec.map φ ≫ E.pointToTorsion (P₁ - P₂) hkill) ≫ E.torsionι N =
      (Spec.map φ ≫ E.pointToTorsion (0 : E.Point s) hzero) ≫ E.torsionι N := by
    rw [Category.assoc, Category.assoc, E.pointToTorsion_torsionι, E.pointToTorsion_torsionι,
      E.point_zero_val]
    exact hrestrict
  have e2 : (Spec.map φ ≫ E.pointToTorsion (P₁ - P₂) hkill) ≫ E.torsionπ N =
      (Spec.map φ ≫ E.pointToTorsion (0 : E.Point s) hzero) ≫ E.torsionπ N := by
    rw [Category.assoc, Category.assoc, E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]
  have hig : Spec.map φ ≫ E.pointToTorsion (P₁ - P₂) hkill =
      Spec.map φ ≫ E.pointToTorsion (0 : E.Point s) hzero :=
    pullback.hom_ext e1 e2
  have hgf : E.pointToTorsion (P₁ - P₂) hkill ≫ E.torsionπ N =
      E.pointToTorsion (0 : E.Point s) hzero ≫ E.torsionπ N := by
    rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]
  have hPz : E.pointToTorsion (P₁ - P₂) hkill = E.pointToTorsion (0 : E.Point s) hzero :=
    FormallyUnramified.hom_ext (Spec.map φ) (isNilpotent_ker_SpecMap φ hφ2) (E.torsionπ N) hig hgf
  -- project back to the points
  have hfin : ((P₁ - P₂ : E.Point s) : Spec R ⟶ E.E) = ((0 : E.Point s) : Spec R ⟶ E.E) := by
    have h := congrArg (fun m => m ≫ E.torsionι N) hPz
    rwa [E.pointToTorsion_torsionι, E.pointToTorsion_torsionι] at h
  have hP : (P₁ : E.Point s) = P₂ := sub_eq_zero.mp (Subtype.ext hfin)
  exact congrArg Subtype.val hP

/-- **(T-B5D, L-BC — the arithmetic input, API-gap sub-tree)** If `N` is invertible on `S`, then the
`N`-torsion `E[N] → S` is formally unramified. Route: `E[N] → S` is finite (`torsionπ_isFinite`,
proven) and its geometric fibres `E[N]_{k̄}` are étale — the latter from AINTLIB's **HasseWeil**
field-level theory (`[N]` separable when `char k̄ ∤ N` via the invariant differential
`OmegaPullbackCoeff`/`card_kernel_eq_degree_of_separable`; `TorsionGeneralN` gives `E[N]_{k̄} ≅
(ℤ/N)²`), transported across the crux **T-B6** scheme-fibre ↔ `WeierstrassCurve k̄` comparison — plus
the **T-DISC** "finite + geometric fibres unramified ⟹ unramified" criterion. Source: KM Thm 2.3.1. -/
theorem formallyUnramified_torsionπ (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by sorry

/-- **(L-BC funnel — hypothesis-funneled pre-wire, v10.123-CASCADE)** L-BC from its single
remaining fibre input: once every residue-field fibre of `E[N] ⟶ S` is formally unramified,
`E[N] ⟶ S` is formally unramified — T-DISC (`of_finite_fiberToSpecResidueField`) +
`torsionπ_isFinite`.

The `hfib` hypothesis is exactly the **[T-B6′]-shaped gate output** (board v10.123-CASCADE):
at gate-fire it is produced from the group-compatible fibre dictionary
(`geomFibrePointAddEquiv` with its `map_add'` filled + the `hz` zero-pin) transporting
HasseWeil's field-level separability/torsion count (`mulByInt_isSeparable`,
`torsion_genN_linearEquiv`) to the scheme fibres. Nothing else remains between this funnel
and BB-DIFF. -/
theorem formallyUnramified_torsionπ_of_fibres (N : ℕ) [NeZero N]
    (hfib : ∀ y, FormallyUnramified ((E.torsionπ N).fiberToSpecResidueField y)) :
    FormallyUnramified (E.torsionπ N) :=
  haveI := E.torsionπ_isFinite N
  FormallyUnramified.of_finite_fiberToSpecResidueField (f := E.torsionπ N) hfib

/-- **(BB-DIFF MASTER, hypothesis-funneled form)** `[N]` is formally unramified given only
the fibre input of the funnel — L-A ∘ the L-BC funnel. At gate-fire the `hfib` input
discharges and `mulByHom_formallyUnramified` (Torsion.lean) closes through
`mulByHom_formallyUnramified'`. -/
theorem mulByHom_formallyUnramified_of_fibres (N : ℕ) [NeZero N]
    (hfib : ∀ y, FormallyUnramified ((E.torsionπ N).fiberToSpecResidueField y)) :
    FormallyUnramified (E.mulByHom N) :=
  E.formallyUnramified_mulByHom_of_torsionπ N
    (E.formallyUnramified_torsionπ_of_fibres N hfib)

/-- **(T-B5D, MASTER — assembly)** BB-DIFF: `[N]` is formally unramified when `N` is invertible,
assembled from L-A ∘ L-BC. Term-mode (no `sorry` of its own): discharging `formallyUnramified_torsionπ`
(L-BC) and `formallyUnramified_mulByHom_of_torsionπ` (L-A) proves this, which is defeq to the held
`Torsion.lean:228` `mulByHom_formallyUnramified`. -/
theorem mulByHom_formallyUnramified' (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
  E.formallyUnramified_mulByHom_of_torsionπ N (E.formallyUnramified_torsionπ N h)

end EllipticCurve

end ModularCurves
