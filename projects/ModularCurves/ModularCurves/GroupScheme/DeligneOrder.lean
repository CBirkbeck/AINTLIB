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

section AffineHopf

variable {R : Type u} [CommRing R] (E : EllipticCurve (Spec (CommRingCat.of R)))
  {D : RelEffCartierDiv E.π}

/-- The `R`-algebra structure on `Γ(D ×_{Spec R} D, ⊤)` induced by the base map `bimulBase`
(mirrors `subgroupAlgebra`). The tensor comparison `A ⊗_R A ≅ Γ(D ×_R D)` below is an `R`-algebra
iso for this structure; it is the coordinate-ring incarnation of `pullbackSpecIso`. -/
noncomputable def biproductAlgebra :
    Algebra R Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom.toAlgebra

/-- **(Layer B, κ-bijectivity foundation.)** `D ×_{Spec R} D` is affine: `D.subscheme` is finite —
hence affine — over `Spec R`, so both projections are affine morphisms and the fibre product of
affines over an affine base is affine. This is what makes `Γ(D ×_R D)` a genuine coordinate ring and
`κ : A ⊗_R A → Γ(D ×_R D)` an isomorphism (`pullbackSpecIso`). -/
theorem subgroupBiproduct_isAffine :
    IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) := by
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffineHom (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact isAffine_of_isAffineHom
    (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))

/-- `bimulBase` is the first projection followed by the structure map (by definition, up to
associativity). -/
theorem bimulBase_eq_fst_structMap :
    E.bimulBase (D := D) =
      Limits.pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫
        E.subgroupStructMap D :=
  (Category.assoc _ _ _).symm

/-- `bimulBase` is also the second projection followed by the structure map (pullback condition). -/
theorem bimulBase_eq_snd_structMap :
    E.bimulBase (D := D) =
      Limits.pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫
        E.subgroupStructMap D := by
  rw [bimulBase_eq_fst_structMap]
  exact Limits.pullback.condition

/-- The first coordinate projection `A →ₐ[R] Γ(D ×_R D)`, i.e. `Γ(pullback.fst)`. It is an
`R`-algebra map because `fst ≫ structMap = bimulBase` (`bimulBase_eq_fst_structMap`). -/
noncomputable def subgroupProj₁ :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← bimulBase_eq_fst_structMap]
      show (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The second coordinate projection `A →ₐ[R] Γ(D ×_R D)`, i.e. `Γ(pullback.snd)`. -/
noncomputable def subgroupProj₂ :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← bimulBase_eq_snd_structMap]
      show (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The tensor comparison `κ : A ⊗_R A →ₐ[R] Γ(D ×_R D)`, `κ = ⟨Γ(fst), Γ(snd)⟩` — the
coordinate-ring incarnation of the canonical map `Spec Γ(D ×_R D) ⟶ Spec A ×_{Spec R} Spec A`. It
is an isomorphism (`pullbackSpecIso` transported across `D.subscheme.isoSpec` on each factor); its
inverse composed with `Γ(m)` is the comultiplication. -/
noncomputable def subgroupTensorCompare :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    TensorProduct R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  Algebra.TensorProduct.lift (E.subgroupProj₁ (D := D)) (E.subgroupProj₂ (D := D))
    (fun _ _ => Commute.all _ _)

/-- **BOARDED `[T-D5h-κbij]`.** The tensor comparison `κ` is bijective — the sole genuinely-heavy
input to `Δ`. This is `pullbackSpecIso` (`Γ(Spec S ×_{Spec R} Spec T) ≅ S ⊗_R T`) transported
across `D.subscheme.isoSpec` on each factor (both factors affine: `D.subscheme` is finite over
`Spec R`). Once landed, `Δ = κ⁻¹ ∘ Γ(m)`, its `_apply` characterisation, and the Hopf axioms all
follow mechanically. -/
theorem subgroupTensorCompare_bijective :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Function.Bijective (E.subgroupTensorCompare (D := D)) := by
  sorry

/-- The multiplication is a morphism over the base: `m ≫ structMap = bimulBase` (dualizing to the
`R`-linearity of `Γ(m)`). -/
theorem subgroupMul_structMap (hD : D.IsSubgroup E) :
    E.subgroupMul hD ≫ E.subgroupStructMap D = E.bimulBase (D := D) := by
  show E.subgroupMul hD ≫ (D.ideal.subschemeι ≫ E.π) = E.bimulBase (D := D)
  rw [← Category.assoc, E.subgroupMul_subschemeι hD]
  exact ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).2

/-- `Γ(m) : A →ₐ[R] Γ(D ×_R D)`, the algebra map underlying the comultiplication (before the tensor
identification). `R`-linear because `m` is a morphism over the base (`subgroupMul_structMap`). -/
noncomputable def subgroupComulHom (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (E.subgroupMul hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (E.subgroupMul hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.subgroupMul_structMap hD]
      show (E.subgroupMul hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- **(Layer B, L3 — the comultiplication.)** `Δ = m^♯ : A →ₐ[R] A ⊗_R A`, the Hopf-dual of the
group-scheme multiplication `subgroupMul` (`m : D ×_S D ⟶ D`) over the affine base: `Δ = κ⁻¹ ∘ Γ(m)`,
where `Γ(m)` pulls regular functions back along `m` into `Γ(D ×_{Spec R} D)` and `κ⁻¹` identifies
that with `A ⊗_R A` (`subgroupTensorCompare`). Coassociativity dualizes associativity of `m`. -/
noncomputable def subgroupComul (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      TensorProduct R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  (AlgEquiv.ofBijective (E.subgroupTensorCompare (D := D))
      (E.subgroupTensorCompare_bijective (D := D))).symm.toAlgHom.comp (E.subgroupComulHom hD)

/-- **The comultiplication interface pin (v10.24(b) opaque interface).** `κ (Δ a) = Γ(m) a`: `Δ` is
characterised by pushing forward through the tensor comparison `κ` to `Γ(m)`. Downstream (Hopf
axioms, L6 points↔convolution) consumes only this pin; `subgroupComul` is then marked `irreducible`
so its heavy `κ⁻¹` core is never unfolded — dodging the whnf/kernel-poison wall that scheme-iso
definitions trigger (the T-W7.1b lesson). -/
theorem subgroupTensorCompare_subgroupComul (hD : D.IsSubgroup E)
    (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    E.subgroupTensorCompare (D := D) (E.subgroupComul hD a) = E.subgroupComulHom hD a := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  exact AlgEquiv.apply_symm_apply
    (AlgEquiv.ofBijective (E.subgroupTensorCompare (D := D))
      (E.subgroupTensorCompare_bijective (D := D))) (E.subgroupComulHom hD a)

attribute [irreducible] subgroupComul

/-- The unit section `e` is a section of the structure map: `e ≫ (subschemeι ≫ π) = 𝟙 S`
(the zero point lies over the identity of the base). -/
theorem subgroupUnit_structMap (hD : D.IsSubgroup E) :
    E.subgroupUnit hD ≫ E.subgroupStructMap D = 𝟙 (Spec (CommRingCat.of R)) := by
  show E.subgroupUnit hD ≫ (D.ideal.subschemeι ≫ E.π) = 𝟙 _
  rw [← Category.assoc, E.subgroupUnit_subschemeι hD]
  exact (0 : E.Point (𝟙 (Spec (CommRingCat.of R)))).2

/-- **(Layer B, L3 — the counit.)** `ε : A →ₐ[R] R`, the Hopf-dual of the unit section
`subgroupUnit` (`e : S ⟶ D`). Concretely `ε = Γ(e)` followed by `Γ(Spec R, ⊤) ≅ R`; it is
`R`-linear because `e` is a section of the structure map (`subgroupUnit_structMap`). Counit laws
dualize the unit laws of the group scheme. -/
noncomputable def subgroupCounit (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Γ(D.ideal.subscheme, ⊤) →ₐ[R] R :=
  letI := E.subgroupAlgebra D
  { ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) =
            𝟙 (CommRingCat.of R) := by
        rw [Category.assoc, ← Category.assoc (E.subgroupStructMap D).appTop,
          ← Scheme.Hom.comp_appTop,
          show E.subgroupUnit hD ≫ E.subgroupStructMap D = 𝟙 _ from E.subgroupUnit_structMap hD]
        simp
      show ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) = r
      rw [← CommRingCat.comp_apply, hcomp, CommRingCat.id_apply] }

/-- The inversion `n` is a morphism over the base: `n ≫ (subschemeι ≫ π) = subschemeι ≫ π`
(the negation of the universal point lies over the same base map). -/
theorem subgroupInv_structMap (hD : D.IsSubgroup E) :
    E.subgroupInv hD ≫ E.subgroupStructMap D = E.subgroupStructMap D := by
  show E.subgroupInv hD ≫ (D.ideal.subschemeι ≫ E.π) = D.ideal.subschemeι ≫ E.π
  rw [← Category.assoc, E.subgroupInv_subschemeι hD]
  exact (-(E.upt (D := D))).2

/-- **(Layer B, L3 — the antipode.)** `antipode : A →ₐ[R] A`, the Hopf-dual of the inversion
`subgroupInv` (`n : D ⟶ D`). Concretely `Γ(n)`; it is `R`-linear because `n` is a morphism over
the base (`subgroupInv_structMap`). The antipode laws dualize the inverse laws of the group scheme. -/
noncomputable def subgroupAntipode (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Γ(D.ideal.subscheme, ⊤) →ₐ[R] Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  { (E.subgroupInv hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (E.subgroupInv hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.subgroupInv_structMap hD]
      show (E.subgroupInv hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

end AffineHopf

section GeneralBase

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(Layer B, L1 intermediate — section over a general base.)** The box for a *section*
`Q : E.Section` over an arbitrary base `S` (not yet assumed affine). Reduces to the affine core
`smul_eq_zero_of_factors_affine` by covering `S` with affine opens and using locality of morphism
equality on `S` (`(N : ℤ) • Q = 0 ↔ (N • Q).1 = 0.1 : S ⟶ E.E`, checkable on an affine cover; each
restriction is handled by the affine core after `Scheme.isoSpec`). The general box
`smul_eq_zero_of_factors'` in turn reduces to *this* by base-changing along `g : T ⟶ S`
(`Point.asSection`, `RelEffCartierDiv.IsSubgroup.baseChange`). -/
theorem smul_eq_zero_of_factors_section {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ}
    [NeZero N] (hdeg : ∀ s : S, D.degree s = N) (Q : E.Section)
    (hQ : ∃ h : S ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  sorry

/-- **(Layer B, L1 — the relative degree is base-change invariant.)** BOARDED `[T-D5h-degBC]`.
The degree (fibre `finrank` of the finite flat structure map `D.subscheme ⟶ S`) is stable under
base change: constant degree `N` on `S` gives constant degree `N` on any `T`. This is the
`finrank`-base-change fact for the finite locally free module, applied fibrewise
(`Module.finrank_baseChange` at the affine-local level; the fibre of `D.baseChange g` over `t`
is that of `D` over `g t`, base-changed to `κ(t)`). Sole genuinely-absent input to the L1
reduction below; everything else (factoring transport, `asSection` descent) is proven. -/
theorem degree_baseChange_eq {D : RelEffCartierDiv E.π} {N : ℕ}
    (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (t : T) :
    (D.baseChange g).degree t = N := by
  sorry

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
  -- Base-change along `g : T ⟶ S`. `Q` becomes the section `asSection Q` of `E ×_S T / T`, `D`
  -- becomes the subgroup divisor `D.baseChange g` (`IsSubgroup.baseChange`) of constant degree `N`
  -- (`degree_baseChange_eq`), and `asSection Q` factors through it (`exists_factor_comap_iff` +
  -- `asSection_val_fst`). The section box kills it; `asSection`, injective and `zsmul`-linear,
  -- descends the vanishing back to `Q`.
  have hfac : ∃ h : T ⟶ (D.baseChange g).ideal.subscheme,
      h ≫ (D.baseChange g).ideal.subschemeι = (Point.asSection E g Q).1 := by
    rw [RelEffCartierDiv.baseChange_ideal]
    refine (AlgebraicGeometry.Scheme.IdealSheafData.exists_factor_comap_iff D.ideal
      (Limits.pullback.fst E.π g) (Point.asSection E g Q).1).mpr ?_
    obtain ⟨h, hh⟩ := hQ
    exact ⟨h, hh.trans (Point.asSection_val_fst E g Q).symm⟩
  have hbc : (N : ℤ) • Point.asSection E g Q = 0 :=
    smul_eq_zero_of_factors_section (E.baseChange g)
      (RelEffCartierDiv.IsSubgroup.baseChange E hD g)
      (fun t => degree_baseChange_eq E hdeg g t) (Point.asSection E g Q) hfac
  -- `asSection` is injective and intertwines `zsmul`, and sends `0` to `0`.
  have hzero : Point.asSection E g (0 : E.Point g) = 0 := by
    have h := Point.asSection_zsmul E g 0 (0 : E.Point g)
    rwa [zero_zsmul, zero_zsmul] at h
  have hinj : Function.Injective (Point.asSection E g) := by
    intro P P' hPP'
    apply Subtype.ext
    have h := congrArg
      (fun s : (E.baseChange g).Point (𝟙 T) => s.1 ≫ Limits.pullback.fst E.π g) hPP'
    simpa only [Point.asSection_val_fst] using h
  exact hinj (by rw [Point.asSection_zsmul, hbc, hzero])

end GeneralBase

end EllipticCurve

end ModularCurves
