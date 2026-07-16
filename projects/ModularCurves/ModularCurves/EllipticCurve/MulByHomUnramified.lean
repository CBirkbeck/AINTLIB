/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.EllipticCurve.TorsionUnramifiedFibre
import ModularCurves.ForMathlib.NilpotentKerSpecMap
import ModularCurves.ForMathlib.FormallyUnramifiedFibre
import ModularCurves.ForMathlib.TorsionByEquiv
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Unramifiedness of `[N]` via the `E[N]`-torsor (T-B5D / BB-DIFF, scoping skeleton)

`/develop --decompose` skeleton for **BB-DIFF** = `MulByHom.formallyUnramified` (`Torsion.lean:228`,
held): `[N] : E ⟶ E` is formally unramified when `N` is invertible on `S`. It states the leaves of
the **non-circular, HasseWeil-anchored** route (beastmode-B's `tb5z_architecture.md` route (c),
grounded in KM §2.3) as `:= by sorry`, and assembles the target from them. NEW bridge file; the held
`Torsion.lean` / `GroupLawConstruction.lean` are not edited. Full tree, verbatim KM 2.3 / Loeffler
3.4.2(2) quotes, adversarial passes and feasibility live in
`.mathlib-quality/decomposition-km2.3-b5d.md`.

## Why not the "obvious" routes (mapped dead ends — do NOT re-litigate)
- **Invariant-differential / scheme `Ω¹`** (KM's own "tangent map at the origin is multiplication by
  `N`"): mathlib has NO invariant differential for `WeierstrassCurve` and NO relative-`Ω¹` sheaf
  API.
- **Chart route** (categorical `mulByHom = (mulBy N).left` on `GrpObj` ↔ Weierstrass-chart `[N]`):
  that comparison is **T-W7 scope** (A-lane, in progress) — collides.
- The `Torsionπ.etale ⟸ MulByHom.etale ⟸ MulByHom.formallyUnramified` chain (`Torsion.lean:233-250`)
  and the T-B6 fibre count are currently **circular** in `BB-DIFF`.

## The route (KM §2.3, non-circular)
KM Thm 2.3.1: `[N]` is finite locally free of rank `N²`, and its kernel `E[N]` is finite étale over
`S` when `N` is invertible. KM's proof reduces geometric-fibre-by-fibre and uses KM Cor 2.3.2:
**`[N]` is an f.p.p.f `E[N]`-torsor**, so `[N]` is unramified iff `E[N] → S` is. The fibre-level
`[N]`-separability that mathlib lacks is **already in AINTLIB's HasseWeil**
(`InvariantDifferential`,
`OmegaPullbackCoeff`, `EC/KernelCountGeneral.card_kernel_eq_degree_of_separable`, `mulByInt_degree`,
`NTorsion/TorsionGeneralN`) — verified present. So the leaves:

* **L-A** (self-contained core, "build first", route-independent) —
  `MulByHom.formallyUnramified_of_torsionπ`:
  `FormallyUnramified (torsionπ N) → FormallyUnramified (mulByHom N)`, via the `E[N]`-torsor
  structure
  (KM 2.3.2) / group infinitesimal-lifting. Cannot collide with any lane.
* **L-BC** (API-gap sub-tree) — `Torsionπ.formallyUnramified`: `E[N] → S` is formally unramified
  when
  `N` is invertible, from (L-B) HasseWeil geometric fibres `E[N]_{k̄}` étale (the crux **T-B6**
  scheme-fibre ↔ HasseWeil-`WeierstrassCurve` comparison) + (L-C = **T-DISC**) the "finite +
  geometric
  fibres unramified ⟹ unramified" criterion.
* **MASTER** — `MulByHom.formallyUnramified'` = L-A ∘ L-BC (assembled, term-mode; discharges
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

/- `pointEquivOverHom_sub`, `pointEquivOverHom_restrict`, `restrict_sub` RELOCATED
byte-identically to `EllipticCurve/TorsionUnramifiedFibre.lean` (imported above) — they are
needed on both sides of the L-A/L-BC split (Y1-CLOSER S2, hfib session). -/

/-- **(T-B5D, L-A — the self-contained core, build first)** If the `N`-torsion `E[N] → S` is
formally
unramified, then so is `[N] : E ⟶ E`. Route-independent: `[N]` is an f.p.p.f `E[N]`-torsor (KM Cor.
2.3.2), so two infinitesimal lifts `g₁, g₂` of `[N]` agreeing on a square-zero closed subscheme
differ
by a map into `E[N]` vanishing there, which is `0` once `E[N] → S` is formally unramified — hence
`g₁ = g₂`. Uses only the `GrpObj` group structure of `E` and mathlib's `FormallyUnramified` morphism
property; collides with no lane. This is the piece to land first. -/
theorem MulByHom.formallyUnramified_of_torsionπ (N : ℕ)
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

/-- **(T-B5D, L-BC — the arithmetic input, PROVEN)** If `N` is invertible on `S`, then the
`N`-torsion `E[N] → S` is formally unramified. Route (Y1-CLOSER S2, augmentation-ideal form of
KM Thm 2.3.1): `E[N] → S` is finite (`torsionπ_isFinite`, proven) and its residue-field fibres
are formally unramified — over a field, torsion points reducing to zero along a square-zero
thickening vanish, because evaluation on the augmentation ideal of a chart at the zero section
is additive mod `I² = 0` and `N` is a unit (`TorsionUnramifiedFibre.lean`; no differentials,
no degree counts, no algebraic closure) — plus the **T-DISC** "finite + fibres unramified ⟹
unramified" criterion. -/
theorem Torsionπ.formallyUnramified (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) :=
  Torsionπ.formallyUnramified_of_nIsInvertible E N h

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
theorem Torsionπ.formallyUnramified_of_fibres (N : ℕ) [NeZero N]
    (hfib : ∀ y, FormallyUnramified ((E.torsionπ N).fiberToSpecResidueField y)) :
    FormallyUnramified (E.torsionπ N) :=
  haveI := E.torsionπ_isFinite N
  FormallyUnramified.of_finite_fiberToSpecResidueField (f := E.torsionπ N) hfib

/-- **(BB-DIFF MASTER, hypothesis-funneled form)** `[N]` is formally unramified given only
the fibre input of the funnel — L-A ∘ the L-BC funnel. At gate-fire the `hfib` input
discharges and `MulByHom.formallyUnramified` (Torsion.lean) closes through
`MulByHom.formallyUnramified'`. -/
theorem MulByHom.formallyUnramified_of_fibres (N : ℕ) [NeZero N]
    (hfib : ∀ y, FormallyUnramified ((E.torsionπ N).fiberToSpecResidueField y)) :
    FormallyUnramified (E.mulByHom N) :=
  MulByHom.formallyUnramified_of_torsionπ E N
    (Torsionπ.formallyUnramified_of_fibres E N hfib)

/-- **(T-B5D, MASTER — assembly)** BB-DIFF: `[N]` is formally unramified when `N` is invertible,
assembled from L-A ∘ L-BC. Term-mode (no `sorry` of its own): discharging
`Torsionπ.formallyUnramified`
(L-BC) and `MulByHom.formallyUnramified_of_torsionπ` (L-A) proves this, which is defeq to the held
`Torsion.lean:228` `MulByHom.formallyUnramified`. -/
theorem MulByHom.formallyUnramified' (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
  MulByHom.formallyUnramified_of_torsionπ E N (Torsionπ.formallyUnramified E N h)

/-! ## The discharged BB-DIFF chain (relocated from `Torsion.lean`, Y1-CLOSER S2)

The three theorems below are relocated byte-identically (statements unchanged) from
`EllipticCurve/Torsion.lean` — pointer comments at the old site. Their proofs need the
L-A/L-BC machinery of this file and `TorsionUnramifiedFibre.lean`, which import
`Torsion.lean`, so the discharge must live here. `torsion_geometricFibre_rank_two` follows
its consumer `Torsionπ.etale` down from `TorsionFibre.lean` for the same reason. -/

/-- **Black box `BB-DIFF` (T-B5 = Loeffler 3.4.2(2), unramifiedness) — DISCHARGED
(Y1-CLOSER S2)**: if `N` is invertible on `S` then `[N]` is formally unramified.
Loeffler (verbatim): *"The morphism `[N]` multiplies a global differential by `N`, so it
induces an isomorphism of tangent space."* Proven differential-free: L-A (the `E[N]`-torsor
reduction) ∘ L-BC (the augmentation-ideal fibre argument + T-DISC). -/
theorem MulByHom.formallyUnramified (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
  MulByHom.formallyUnramified' E N h

/-- **(T-B5 = Loeffler 3.4.2(2))** If `N` is invertible on `S`, then `[N] : E ⟶ E` is étale
(it induces multiplication by `N`, an isomorphism, on the invariant differential). -/
theorem MulByHom.etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.mulByHom N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · haveI hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    haveI hE : IsEmpty E.E := ⟨fun x => hS.false (E.π x)⟩
    infer_instance
  · haveI : NeZero N := ⟨hN⟩
    haveI := E.mulByHom_flat N
    haveI := MulByHom.formallyUnramified E N h
    haveI := MulByHom.locallyOfFinitePresentation E N
    exact Etale.of_formallyUnramified_of_flat (E.mulByHom N)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-B5′)** If `N` is invertible on `S`, then `E[N] ⟶ S` is (finite) étale.
Source: Loeffler §3.4; KM 2.3.5. -/
theorem Torsionπ.etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.torsionπ N) := by
  have he := MulByHom.etale E N h
  exact MorphismProperty.pullback_snd _ _ he

/-- **(T-B6 headline)** Over an algebraically closed field in which `N` is invertible,
the `N`-torsion of the geometric point group is `(ℤ/N)²`. Proof route: counting
(KM 2.3.5/[Sil] III.6.4) — étale rank-`d²` kernels over `k̄` have exactly `d ^ 2`
points, and the divisor-count spectrum pins the group. Rests on the registered
KM 2.3.1/3.4.2 black boxes (`BB-QF`/`BB-FLAT`/`BB-DEG`/`BB-DIFF`) via
`torsionπ_isFinite`/`Torsionπ.etale`/`torsion_rank`. -/
theorem torsion_geometricFibre_rank_two (N : ℕ) [NeZero N] (k : Type u) [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Nonempty (Submodule.torsionBy ℤ (E.Point t) (N : ℤ) ≃+ (Fin 2 → ZMod N)) := by
  obtain ⟨x₀⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
  refine addEquiv_pi_fin_two_zmod_of_natCard N (NeZero.ne N) _ (fun x => ?_)
    (fun d hd hdN => ?_)
  · apply Subtype.ext
    have h2 : ((N • x : Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) : E.Point t) =
        N • (x : E.Point t) :=
      map_nsmul (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)).subtype N x
    rw [h2, ZeroMemClass.coe_zero, ← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).mp x.2
  · haveI : NeZero d := ⟨hd.ne'⟩
    have hdk : (d : k) ≠ 0 := by
      obtain ⟨c, hc⟩ := hdN
      intro h0
      apply hN
      rw [hc, Nat.cast_mul, h0, zero_mul]
    haveI hEt : Etale ((E.baseChange t).torsionπ d) :=
      Torsionπ.etale (E.baseChange t) d ((nIsInvertible_spec_iff k d).mpr hdk)
    haveI hFin : IsFinite ((E.baseChange t).torsionπ d) :=
      (E.baseChange t).torsionπ_isFinite d
    calc Nat.card {x : Submodule.torsionBy ℤ (E.Point t) (N : ℤ) // d • x = 0}
        = Nat.card (Submodule.torsionBy ℤ (E.Point t) (d : ℤ)) :=
          Nat.card_congr (Submodule.torsionByNsmulKerEquiv (E.Point t) N d hdN)
      _ = Nat.card {h : Spec (CommRingCat.of k) ⟶ E.torsion d //
            h ≫ E.torsionπ d = t} :=
          (Nat.card_congr (E.torsionPointsEquiv d t)).symm
      _ = Nat.card {s : Spec (CommRingCat.of k) ⟶ (E.baseChange t).torsion d //
            s ≫ (E.baseChange t).torsionπ d = 𝟙 (Spec (CommRingCat.of k))} :=
          (Nat.card_congr (E.sectionsEquivOverPoints d t)).symm
      _ = ((E.baseChange t).torsionπ d).finrank x₀ :=
          natCard_sections_eq_finrank ((E.baseChange t).torsionπ d) x₀
      _ = d ^ 2 := (E.baseChange t).torsion_rank d x₀

end EllipticCurve

end ModularCurves
