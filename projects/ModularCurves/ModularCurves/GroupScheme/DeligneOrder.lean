import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.ForMathlib.CartierDual
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Deligne's order theorem — Layer B: the geometric bridge (BB-DELIGNE)

Layer A (`ModularCurves.CartierDual.deligne_pointConv_pow_finrank` /
`deligne_point_pow_eq_one`) proves Deligne's theorem **abstractly**: for a commutative
cocommutative Hopf algebra `A` finite free over a ring `R`, every `B`-point `φ : A →ₐ[R] B`
satisfies `(toConv φ) ^ (finrank R A) = 1` in the convolution group of points
`WithConv (A →ₐ[R] B)` — i.e. the group of points of `G = Spec A` is killed by the order.

This file is **Layer B**: the bridge from that abstract statement to the geometric box
`RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (`LevelStructure/ExactOrder.lean`) — a
subgroup divisor `D ⊂ E` of constant degree `N` kills every point factoring through it,
`(N : ℤ) • Q = 0`. This is KM 1.4.2 / Tate CSS §3.8: *"a finite locally free commutative group
scheme of rank `N` is killed by `N`."*

## The route (source-faithful to Tate: `G` finite flat ⟹ `G = Spec A`, `A` a Hopf algebra)

The substrate audit (2026-07-08) confirmed **all of Layer B is absent** from both the project and
mathlib — there is no scheme group-object ↔ Hopf-algebra duality, and the group-object
multiplication on `D.subscheme` is deliberately deferred in `GroupScheme/Subgroup.lean`. The bridge
is therefore built here from scratch, along these leaves:

* **L1 (reduction to an affine base).** `(N : ℤ) • Q = 0` is local on `T` and stable under base
  change (`Point.pull_zsmul`/`_zero`, `RelEffCartierDiv.IsSubgroup.baseChange`, all proven), so the
  box reduces to `S = Spec R` affine and `T = Spec B` affine — where a genuine ring `R` and a point
  `φ : A →ₐ[R] B` are available.
* **L2 (the coordinate algebra).** `D.subscheme` is finite over `Spec R`, hence affine
  (`isAffine_of_isAffineHom`), so `A := Γ(D.subscheme, ⊤)` is a finite `R`-algebra (the
  `torsionAlgebra` pattern of `WeilPairing/EtaleDescent.lean`).
* **L3 (the Hopf structure).** The curve group law restricts to `D` (by `IsSubgroup`), giving a
  comultiplication `Δ : A →ₐ[R] A ⊗_R A` dual to `m : D ×_S D → D` (built by Yoneda from the sum of
  the two universal points of `D ×_S D`, which factors through `D`); counit dual to the unit
  section; antipode dual to inversion. `A` becomes a commutative cocommutative `HopfAlgebra R A`.
* **L5 (free-vs-projective).** `A` is finite *projective* (locally free); Deligne needs *free*, so
  Zariski-localize `Spec R` over a cover trivialising `A`, apply Deligne on each piece, and glue
  (the goal is local on `Spec R`).
* **L6 (points ↔ convolution).** The factoring points `Q ∈ D(Spec B)` correspond to `φ : A →ₐ[R] B`
  (`ΓSpec` adjunction, `Scheme.isoSpec`), and the curve group law on `D(Spec B)` matches convolution
  in `WithConv (A →ₐ[R] B)` (dual to `Δ`); in particular `(N : ℤ) • Q ↔ (toConv φ) ^ N` and
  `0 ↔ 1`.
* **L7 (assembly).** `deligne_point_pow_eq_one` gives `(toConv φ) ^ N = 1`, i.e. `N • Q = 0`.

Full plan: `.mathlib-quality/plan-deligne.md`. `sorry`s here are Layer-B leaves, tracked as
sub-tickets T-D5h..k (WIP, producer discipline).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

section AffineBase

variable {R : Type u} [CommRing R] (E : EllipticCurve (Spec (CommRingCat.of R)))
  (D : RelEffCartierDiv E.π)

/-- The structure map `q = subschemeι ≫ π : D.subscheme ⟶ Spec R` of the divisor's total space
over the affine base. -/
noncomputable abbrev subgroupStructMap : D.ideal.subscheme ⟶ Spec (CommRingCat.of R) :=
  D.ideal.subschemeι ≫ E.π

/-- **(Layer B, L2 — the coordinate algebra structure.)** `D.subscheme` is finite over the affine
base `Spec R` (`D.finite`), hence affine (`isAffine_of_isAffineHom`); its global sections
`Γ(D.subscheme, ⊤)` therefore carry an `R`-algebra structure through `R ≅ Γ(Spec R, ⊤)`. This is the
Hopf algebra `A_D` of Deligne's proof (Hopf structure added in L3). Mirrors the `torsionAlgebra`
construction of `WeilPairing/EtaleDescent.lean`. -/
noncomputable def subgroupAlgebra : Algebra R Γ(D.ideal.subscheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom.toAlgebra

/-- With the `R`-algebra structure `subgroupAlgebra`, the coordinate algebra `Γ(D.subscheme, ⊤)` is
a finite `R`-module — from finiteness of `D.subscheme` over `Spec R` (`D.finite`). -/
theorem subgroupAlgebra_finite :
    letI := E.subgroupAlgebra D
    Module.Finite R Γ(D.ideal.subscheme, ⊤) := by
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  letI := E.subgroupAlgebra D
  have h : RingHom.Finite
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.finite_respectsIso.cancel_left_isIso _ _).mpr
      ((E.subgroupStructMap D).finite_app ⊤ (isAffineOpen_top _))
  exact h

/-- **(Layer B, affine core.)** The box `smul_eq_zero_of_factors` over an *affine* base
`Spec R`, with the point taken as a section `Q : E.Section`: a subgroup divisor `D` of constant
degree `N` kills every section factoring through it. This is where Deligne's abstract theorem
applies (a genuine ring `R` and coordinate Hopf algebra `A = Γ(D.subscheme, ⊤)` are available). The
general box (`smul_eq_zero_of_factors'`, arbitrary base `S` and `T`-point `Q`) reduces to this by
L1. Proven via L2 (algebra) + L3/L4 (Hopf structure) + L5 (localise to free) + L6 (points ↔
convolution) + L7 (`deligne_point_pow_eq_one`). -/
theorem smul_eq_zero_of_factors_affine {N : ℕ} [NeZero N] (hD : D.IsSubgroup E)
    (hdeg : ∀ s, D.degree s = N) (Q : E.Section)
    (hQ : ∃ h : Spec (CommRingCat.of R) ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  sorry

end AffineBase

section GroupObject

variable {S : Scheme.{u}} (E : EllipticCurve S) {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E)

/-- The base structure map `D ×_S D ⟶ S` of the self-product of the divisor's total space. -/
noncomputable abbrev bimulBase :
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ⟶ S :=
  pullback.fst _ _ ≫ D.ideal.subschemeι ≫ E.π

/-- The first universal point of `D ×_S D`: the first projection, viewed as a point of `E`
factoring through `D`. -/
noncomputable def bipt₁ : E.Point (E.bimulBase (D := D)) :=
  ⟨pullback.fst _ _ ≫ D.ideal.subschemeι, by rw [Category.assoc]⟩

/-- The second universal point of `D ×_S D`: the second projection, viewed as a point of `E`
factoring through `D`. -/
noncomputable def bipt₂ : E.Point (E.bimulBase (D := D)) :=
  ⟨pullback.snd _ _ ≫ D.ideal.subschemeι, by
    rw [Category.assoc]; exact (pullback.condition).symm⟩

/-- The universal point of `D.subscheme`: the identity morphism, viewed as a point of `E` factoring
through `D` (over the structure map `subschemeι ≫ π`). Its negation gives the inversion morphism. -/
noncomputable def upt : E.Point (D.ideal.subschemeι ≫ E.π) :=
  ⟨D.ideal.subschemeι, rfl⟩

include hD

/-- **(Layer B, L3 core — the group-scheme multiplication exists.)** The sum `bipt₁ + bipt₂` of the
two universal points of `D ×_S D`, taken in the curve group `E.Point (bimulBase)`, factors through
`D` — because both summands factor through `D` and `D(T)` is a subgroup (`IsSubgroup`). This is the
Yoneda input for the multiplication morphism `m : D ×_S D ⟶ D`. -/
theorem exists_factor_bimul :
    ∃ m : pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ⟶ D.ideal.subscheme,
      m ≫ D.ideal.subschemeι = ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1 := by
  obtain ⟨H, hH⟩ := hD (E.bimulBase (D := D))
  exact (hH _).mp (H.add_mem ((hH _).mpr ⟨pullback.fst _ _, rfl⟩)
    ((hH _).mpr ⟨pullback.snd _ _, rfl⟩))

/-- **(Layer B, L3 core.)** The multiplication morphism `m : D ×_S D ⟶ D.subscheme` of the group
scheme structure on `D.subscheme` induced by `IsSubgroup` (the restriction of the curve group law).
Well-defined up to the mono `subschemeι`; its Hopf-dual `Δ = m^♯` is the comultiplication. -/
noncomputable def subgroupMul :
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ⟶ D.ideal.subscheme :=
  (E.exists_factor_bimul hD).choose

/-- The defining property of `subgroupMul`: composing with `subschemeι` recovers the curve sum of
the two universal points. -/
theorem subgroupMul_subschemeι :
    E.subgroupMul hD ≫ D.ideal.subschemeι = ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1 :=
  (E.exists_factor_bimul hD).choose_spec

/-- **(Layer B, L3 core — the unit section exists.)** The zero section factors through `D` (it lies
in the subgroup `D(S)`), giving the identity section of the group scheme `D.subscheme`. -/
theorem exists_factor_unit :
    ∃ e : S ⟶ D.ideal.subscheme, e ≫ D.ideal.subschemeι = (0 : E.Point (𝟙 S)).1 := by
  obtain ⟨H, hH⟩ := hD (𝟙 S)
  exact (hH 0).mp H.zero_mem

/-- **(Layer B, L3 core.)** The unit (identity-section) morphism `e : S ⟶ D.subscheme` of the group
scheme structure on `D.subscheme`. Its Hopf-dual is the counit `ε : A →ₐ[R] R`. -/
noncomputable def subgroupUnit : S ⟶ D.ideal.subscheme :=
  (E.exists_factor_unit hD).choose

theorem subgroupUnit_subschemeι :
    E.subgroupUnit hD ≫ D.ideal.subschemeι = (0 : E.Point (𝟙 S)).1 :=
  (E.exists_factor_unit hD).choose_spec

/-- **(Layer B, L3 core — the inversion morphism exists.)** The negation `-upt` of the universal
point of `D.subscheme` factors through `D` (it lies in the subgroup `D(D.subscheme)`), giving the
inversion of the group scheme. -/
theorem exists_factor_inv :
    ∃ n : D.ideal.subscheme ⟶ D.ideal.subscheme,
      n ≫ D.ideal.subschemeι = (-(E.upt (D := D))).1 := by
  obtain ⟨H, hH⟩ := hD (D.ideal.subschemeι ≫ E.π)
  exact (hH _).mp (H.neg_mem ((hH _).mpr ⟨𝟙 _, Category.id_comp _⟩))

/-- **(Layer B, L3 core.)** The inversion morphism `n : D.subscheme ⟶ D.subscheme` of the group
scheme structure on `D.subscheme`. Its Hopf-dual is the antipode `S : A →ₐ[R] A`. -/
noncomputable def subgroupInv : D.ideal.subscheme ⟶ D.ideal.subscheme :=
  (E.exists_factor_inv hD).choose

theorem subgroupInv_subschemeι :
    E.subgroupInv hD ≫ D.ideal.subschemeι = (-(E.upt (D := D))).1 :=
  (E.exists_factor_inv hD).choose_spec

end GroupObject

section GeneralBase

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(Layer B, L1 + assembly — the box.)** Deligne's order theorem in the project's
subgroup-divisor encoding, over an arbitrary base `S` and for an arbitrary `T`-point `Q`
(the statement of `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`,
`LevelStructure/ExactOrder.lean`). Reduces to the affine core `smul_eq_zero_of_factors_affine`:
`(N : ℤ) • Q = 0` is stable under base change (`RelEffCartierDiv.IsSubgroup.baseChange`,
`Point.pull_zsmul`/`_zero`) and local on `S`, so one may assume `S = Spec R` affine and `Q` a
section. Once landed sorry-free this discharges the `ExactOrder.lean` box (final wiring step). -/
theorem smul_eq_zero_of_factors' {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ}
    [NeZero N] (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  sorry

end GeneralBase

end EllipticCurve

end ModularCurves
