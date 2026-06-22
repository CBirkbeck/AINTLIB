/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Basic
import HasseWeil.Curves.Transcendence
import HasseWeil.Auxiliary.PullbackKaehler
import HasseWeil.InvariantDifferentialPullback
import HasseWeil.OmegaPullbackCoeff
import HasseWeil.EC.IsogenyKernel
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Field

/-!
# Differentials on a smooth plane curve

For a smooth plane curve `C` over a field `F`, the space of (meromorphic)
differentials is the module of Kähler differentials of the function field
`F(C)` over `F`:

```
Ω_C := Ω[F(C) ⁄ F].
```

This file also establishes the elliptic-curve form of Silverman II.4.2(c)
(ticket `T-II-4-004`): a non-constant isogeny `α` is separable iff the pullback
on differentials is injective, equivalently iff its omega-pullback coefficient
is nonzero. The argument runs through mathlib's formal-unramifiedness API and
the cotangent exact sequence, with the relative finiteness of `K(E)` over the
image of `α.pullback` discharged via a transcendence-degree computation.

This closes tickets `T-II-4-001` and `T-II-4-004`.

## Main definitions

* `Differentials`: the space `Ω[F(C)⁄F]` of differentials on `C`.
* `Differentials.d`: the universal derivation `f ↦ df`.
* `IsogenyAlgebraSource`: type synonym carrying the source-side `α.pullback`
  algebra structure, used to elaborate the cotangent base-change cleanly.

## Main results

* `isSeparable_iff_omegaPullbackCoeff_ne_zero`: Silverman II.4.2(c), elliptic
  form — `α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0`.
* `isSeparable_iff_pullbackKaehler_injective`: the algebra-Kähler glue —
  `α.IsSeparable ↔ Function.Injective α.pullbackKaehler`.
* `isogeny_finiteDimensional`: `K(E)` is finite over the image of `α.pullback`.
* `isogeny_degree_pos`: every isogeny has positive degree.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.4
-/

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-- The space of differentials on a smooth plane curve `C`, defined as the
module of Kähler differentials of the function field `F(C)` over `F`.
Reference: Silverman II.4. -/
noncomputable abbrev Differentials (C : SmoothPlaneCurve F) : Type _ :=
  Ω[C.FunctionField⁄F]

/-- The differential `df` of a function `f ∈ F(C)`.
Reference: Silverman II.4. -/
noncomputable abbrev Differentials.d {C : SmoothPlaneCurve F}
    (f : C.FunctionField) : Differentials C :=
  KaehlerDifferential.D F C.FunctionField f

namespace Differentials

variable {C : SmoothPlaneCurve F}

@[simp] theorem d_add (f g : C.FunctionField) :
    Differentials.d (f + g) = Differentials.d f + Differentials.d g :=
  (KaehlerDifferential.D F C.FunctionField).map_add f g

@[simp] theorem d_mul (f g : C.FunctionField) :
    Differentials.d (f * g) = f • Differentials.d g + g • Differentials.d f :=
  (KaehlerDifferential.D F C.FunctionField).leibniz f g

@[simp] theorem d_algebraMap (a : F) :
    Differentials.d (algebraMap F C.FunctionField a) = 0 :=
  (KaehlerDifferential.D F C.FunctionField).map_algebraMap a

@[simp] theorem d_zero : Differentials.d (0 : C.FunctionField) = 0 :=
  (KaehlerDifferential.D F C.FunctionField).map_zero

@[simp] theorem d_one : Differentials.d (1 : C.FunctionField) = 0 :=
  (KaehlerDifferential.D F C.FunctionField).map_one_eq_zero

@[simp] theorem d_neg (f : C.FunctionField) :
    Differentials.d (-f) = -Differentials.d f :=
  (KaehlerDifferential.D F C.FunctionField).map_neg f

@[simp] theorem d_sub (f g : C.FunctionField) :
    Differentials.d (f - g) = Differentials.d f - Differentials.d g :=
  (KaehlerDifferential.D F C.FunctionField).map_sub f g

theorem d_pow (f : C.FunctionField) (n : ℕ) :
    Differentials.d (f ^ n) = n • f ^ (n - 1) • Differentials.d f :=
  (KaehlerDifferential.D F C.FunctionField).leibniz_pow f n

theorem d_inv (f : C.FunctionField) :
    Differentials.d f⁻¹ = -f⁻¹ ^ 2 • Differentials.d f :=
  (KaehlerDifferential.D F C.FunctionField).leibniz_inv f

theorem d_zpow (f : C.FunctionField) (n : ℤ) :
    Differentials.d (f ^ n) = n • f ^ (n - 1) • Differentials.d f :=
  (KaehlerDifferential.D F C.FunctionField).leibniz_zpow f n

@[simp] theorem d_smul (a : F) (f : C.FunctionField) :
    Differentials.d (a • f) = a • Differentials.d f :=
  (KaehlerDifferential.D F C.FunctionField).map_smul a f

end Differentials

end HasseWeil.Curves

open HasseWeil

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **T-II-4-004 forward direction (axiom-clean)**: if the differential
pullback `α.pullbackKaehler` is injective on `Ω[K(E)/F]`, then the
omega-pullback coefficient is nonzero.

Contrapositive: if `omegaPullbackCoeff W α = 0`, then `α.pullbackKaehler ω = 0`
(via `Isogeny.pullbackKaehler_invariantDifferential`), but `ω ≠ 0`, so the
pullback's kernel contains `ω`, contradicting injectivity. -/
theorem omegaPullbackCoeff_ne_zero_of_pullbackKaehler_injective
    (α : Isogeny W.toAffine W.toAffine) (h_inj : Function.Injective α.pullbackKaehler) :
    omegaPullbackCoeff W α ≠ 0 := by
  intro h_zero
  refine invariantDifferential_ne_zero W.toAffine (h_inj ?_)
  rw [Isogeny.pullbackKaehler_invariantDifferential, h_zero, zero_smul, map_zero]

/-- **T-II-4-004 reverse direction (axiom-clean)**: if `omegaPullbackCoeff W α ≠ 0`,
then the differential pullback `α.pullbackKaehler` is injective on `Ω[K(E)/F]`.

Proof: It suffices to show the kernel is trivial. Take `η ∈ Ω` with
`α.pullbackKaehler η = 0`. Using 1-dim of `Ω` (`kaehler_rank_one`), write
`η = a • ω`. Then
`α.pullbackKaehler (a • ω) = α.pullback a • (omegaPullbackCoeff W α • ω)
= (α.pullback a · c) • ω`. Setting this to `0` with `ω ≠ 0` gives
`α.pullback a · c = 0`. Since `c ≠ 0` and `K(E)` is a field, `α.pullback a = 0`.
By injectivity of `α.pullback` (any AlgHom on a field is injective), `a = 0`,
so `η = 0`. -/
theorem pullbackKaehler_injective_of_omegaPullbackCoeff_ne_zero
    (α : Isogeny W.toAffine W.toAffine)
    (h_ne : omegaPullbackCoeff W α ≠ 0) :
    Function.Injective α.pullbackKaehler := by
  intro x y h_eq
  have h_diff : α.pullbackKaehler (x - y) = 0 := by rw [map_sub, h_eq, sub_self]
  rw [← sub_eq_zero]
  have h_ω_ne : invariantDifferential W.toAffine ≠ 0 :=
    invariantDifferential_ne_zero W.toAffine
  obtain ⟨a, h_a⟩ := exists_smul_eq_of_finrank_eq_one
    (kaehler_rank_one W.toAffine) h_ω_ne (x - y)
  rw [← h_a]
  rw [← h_a, Isogeny.pullbackKaehler_smul_KE,
    Isogeny.pullbackKaehler_invariantDifferential, smul_smul] at h_diff
  -- `α.pullback a * c = 0` with `c ≠ 0` and `a ↦ α.pullback a` injective gives `a = 0`.
  have h_a_zero : a = 0 := α.pullback_injective <| by
    rw [map_zero]
    exact (mul_eq_zero.mp ((smul_eq_zero.mp h_diff).resolve_right h_ω_ne)).resolve_right h_ne
  rw [h_a_zero, zero_smul]

/-- **T-II-4-004 intermediate iff (axiom-clean)**: the differential pullback
`α.pullbackKaehler` is injective on `Ω[K(E)/F]` iff `omegaPullbackCoeff W α ≠ 0`.

Combined statement of the two directions above. This is the scalar half; the
full T-II-4-004 (`IsSeparable α ↔ omegaPullbackCoeff α ≠ 0`) also needs the
algebra-Kähler glue `IsSeparable α ↔ pullbackKaehler injective`
(`isSeparable_iff_pullbackKaehler_injective`), the actual Silverman II.4.2(c)
content. -/
theorem pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero
    (α : Isogeny W.toAffine W.toAffine) :
    Function.Injective α.pullbackKaehler ↔ omegaPullbackCoeff W α ≠ 0 :=
  ⟨omegaPullbackCoeff_ne_zero_of_pullbackKaehler_injective W α,
   pullbackKaehler_injective_of_omegaPullbackCoeff_ne_zero W α⟩

/-- **T-II-4-004 from both halves**: composes the scalar half
(`pullbackKaehler injective ↔ ω-coeff ≠ 0`) with the algebra-Kähler half
(`IsSeparable ↔ pullbackKaehler injective`).

When the algebra-Kähler half lands axiom-clean, this gives the original
T-II-4-004 target via transitive iff chaining — no further plumbing needed. -/
theorem isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler
    (α : Isogeny W.toAffine W.toAffine)
    (h_alg : α.IsSeparable ↔ Function.Injective α.pullbackKaehler) :
    α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0 :=
  h_alg.trans (pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero W α)

/-- **T-II-4-004 forward chain step 1 (axiom-clean)**: separability of `α`
implies that the algebra structure from `α.pullback` is formally unramified.

Direct from mathlib's `Algebra.FormallyUnramified.of_isSeparable` lifted
through the explicit algebra instance from `α.toAlgebra`. -/
theorem isogeny_formallyUnramified_of_isSeparable
    (α : Isogeny W.toAffine W.toAffine) (h : α.IsSeparable) :
    @Algebra.FormallyUnramified W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra := by
  letI : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  haveI : Algebra.IsSeparable W.toAffine.FunctionField W.toAffine.FunctionField := h
  exact Algebra.FormallyUnramified.of_isSeparable _ _

/-- **T-II-4-004 forward chain step 2 (axiom-clean)**: separability of `α`
implies the Kähler differential module `Ω[K(E)/(image of α.pullback)]` is
trivial.

Direct extraction from the previous step (formally unramified) via the
mathlib instance projection
`FormallyUnramified.subsingleton_kaehlerDifferential`. -/
theorem isogeny_subsingleton_kaehler_of_isSeparable
    (α : Isogeny W.toAffine W.toAffine) (h : α.IsSeparable) :
    @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ α.toAlgebra) := by
  letI : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  haveI := isogeny_formallyUnramified_of_isSeparable W α h
  exact Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

/-- **Cotangent surjectivity (axiom-clean abstract form)**: for a tower
`R → A → B` of commutative algebras with `IsScalarTower`, if the relative
Kähler module `Ω[B/A]` is trivial (Subsingleton), then the natural base-
change map `B ⊗[A] Ω[A/R] → Ω[B/R]` is surjective.

Direct from `KaehlerDifferential.exact_mapBaseChange_map` plus the fact
that any map into a Subsingleton is zero. -/
theorem mapBaseChange_surjective_of_subsingleton_relativeKaehler
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Subsingleton (Ω[B⁄A])] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := fun y ↦
  (KaehlerDifferential.exact_mapBaseChange_map R A B y).mp (Subsingleton.elim _ _)

/-- **Cotangent Subsingleton (axiom-clean abstract form, reverse)**: for a tower
`R → A → B` of commutative algebras with `IsScalarTower`, if the natural
base-change map `B ⊗[A] Ω[A/R] → Ω[B/R]` is surjective, then the relative
Kähler module `Ω[B/A]` is `Subsingleton`. -/
theorem subsingleton_relativeKaehler_of_mapBaseChange_surjective
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h_surj : Function.Surjective (KaehlerDifferential.mapBaseChange R A B)) :
    Subsingleton (Ω[B⁄A]) := by
  refine ⟨fun x y ↦ ?_⟩
  have h_map_zero : KaehlerDifferential.map R A B B = 0 := by
    refine LinearMap.ext fun ω ↦ ?_
    obtain ⟨z, hz⟩ := h_surj ω
    rw [← hz, (KaehlerDifferential.exact_mapBaseChange_map (R := R) (A := A)
      (B := B)).apply_apply_eq_zero]
    rfl
  have h_surj_map : Function.Surjective (KaehlerDifferential.map R A B B) :=
    KaehlerDifferential.map_surjective_of_surjective R A B B Function.surjective_id
  obtain ⟨a, ha⟩ := h_surj_map x
  obtain ⟨b, hb⟩ := h_surj_map y
  have hx : x = 0 := by rw [← ha, h_map_zero]; rfl
  have hy : y = 0 := by rw [← hb, h_map_zero]; rfl
  rw [hx, hy]

/-- **Forward chain step 4 (axiom-clean)**: the smul_assoc identity for the
algebra structure `F → K(E) → K(E)` where the inner step is `α.pullback`.

Direct from `α.pullback` being an `F`-algebra hom (commutes with `algebraMap F`)
plus `mul_assoc`. This is the underlying mathematical fact needed for the
IsScalarTower instance; ship as a bare equation to bypass typeclass-instance
defeq issues (mathlib's default `SMul F K(E)` from `OreLocalization` vs.
`α.toAlgebra.toSMul` are both defeq but syntactically distinct). -/
theorem isogeny_smul_assoc_identity (α : Isogeny W.toAffine W.toAffine)
    (a : F) (b c : W.toAffine.FunctionField) :
    α.pullback (algebraMap F W.toAffine.FunctionField a * b) * c =
      algebraMap F W.toAffine.FunctionField a * (α.pullback b * c) := by
  rw [map_mul, AlgHom.commutes, mul_assoc]

/-- **Forward chain step 4 (axiom-clean)**: the `IsScalarTower` instance for the
algebra structure from an isogeny.

Stated with `@`-explicit instance arguments fixing the middle SMul to
`α.toAlgebra.toSMul`, which forces the elaborator to use `α.toAlgebra`
rather than the global `OreLocalization.instSMul` (the standard mul-based
K(E)-self SMul, defeq to but syntactically distinct from the α-twisted
one). Once the goal type pins the right SMul, the proof closes via
`IsScalarTower.of_algebraMap_eq` from `α.pullback.commutes` (the F-algebra
hom property).

This unblocks `mapBaseChange F K(E) K(E)` and the full cotangent-sequence
argument for the reverse direction of T-II-4-004. -/
theorem isogeny_isScalarTower
    (α : Isogeny W.toAffine W.toAffine) :
    @IsScalarTower F W.toAffine.FunctionField W.toAffine.FunctionField
      _ α.toAlgebra.toSMul _ := by
  letI : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun x ↦ (α.pullback.commutes x).symm

/-- **EssFiniteType from FiniteDimensional (axiom-clean)**: if `K(E)` is a
finite-dimensional `K(E)_α`-module (via `α.toAlgebra`), then it is essentially
of finite type as a `K(E)_α`-algebra.

This is Witness #2 (the bound's `FiniteDimensional` hypothesis) discharged into
the `EssFiniteType` form needed for mathlib's `FormallyUnramified.iff_isSeparable`.
Direct application of `Module.Finite.finiteType` then `EssFiniteType.of_finiteType`. -/
theorem isogeny_essFiniteType_of_finiteDimensional
    (α : Isogeny W.toAffine W.toAffine)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule) :
    @Algebra.EssFiniteType W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra := by
  haveI : @Algebra.FiniteType W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra :=
    @Module.Finite.finiteType W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra h_fin
  exact @Algebra.EssFiniteType.of_finiteType W.toAffine.FunctionField
    W.toAffine.FunctionField _ _ α.toAlgebra _

/-- **FiniteDimensional discharge from IsAlgebraic + EssFiniteType
(witness-parametric, axiom-clean)**: given `IsAlgebraic K(E)_α K(E)` and
`EssFiniteType K(E)_α K(E)` (over `α.toAlgebra`), `K(E)` is finite-dimensional
over `K(E)_α`.

Direct application of mathlib's `Algebra.finite_of_essFiniteType_of_isAlgebraic`
(`Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:185`).

When both witnesses discharge unconditionally (transcendence-degree argument
for `IsAlgebraic`; `IsFractionRing` argument for `EssFiniteType`), this becomes
the unconditional Witness #2 producer for the bound. -/
theorem isogeny_finiteDimensional_of_isAlgebraic_essFiniteType
    (α : Isogeny W.toAffine W.toAffine)
    (h_alg : @Algebra.IsAlgebraic W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra)
    (h_ess : @Algebra.EssFiniteType W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra) :
    @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule := by
  letI : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  haveI : Algebra.IsAlgebraic W.toAffine.FunctionField W.toAffine.FunctionField := h_alg
  haveI : Algebra.EssFiniteType W.toAffine.FunctionField W.toAffine.FunctionField := h_ess
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- **IsAlgebraic discharge from finite intermediate witness (witness-parametric)**:
if `K(E)` is finite-dimensional over some intermediate algebra `L` (with
`Algebra L K(E)_α` and the appropriate scalar tower), then `K(E)` is algebraic
over `K(E)_α`.

The witness `Module.Finite L K(E)` produces `Algebra.IsAlgebraic L K(E)`
(via mathlib's `Algebra.IsAlgebraic.of_finite`); `tower_top` then lifts
to `K(E)_α`. -/
theorem isogeny_isAlgebraic_of_finite_intermediate
    (α : Isogeny W.toAffine W.toAffine) (L : Type*) [Field L]
    [Algebra L W.toAffine.FunctionField] [Module.Finite L W.toAffine.FunctionField]
    (h_tower : @IsScalarTower L W.toAffine.FunctionField W.toAffine.FunctionField
      _ α.toAlgebra.toSMul _) :
    @Algebra.IsAlgebraic W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra := by
  letI : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  haveI := h_tower
  haveI : Algebra.IsAlgebraic L W.toAffine.FunctionField :=
    Algebra.IsAlgebraic.of_finite L W.toAffine.FunctionField
  exact Algebra.IsAlgebraic.tower_top (K := L)
    (L := W.toAffine.FunctionField) (A := W.toAffine.FunctionField)

/-- **T-II-4-004 reverse direction (witness-parametric, axiom-clean)**:
if the relative Kähler module `Ω[K(E)/K(E)_α]` is trivial (`Subsingleton`)
and the algebra structure from `α.pullback` is essentially of finite type
(`EssFiniteType`), then `α` is separable.

Direct application of mathlib's `Algebra.FormallyUnramified.iff_isSeparable`,
unwrapping `FormallyUnramified` via its `Subsingleton`-of-Kähler constructor.
The two witnesses correspond exactly to the two hypotheses of mathlib's iff:
`Subsingleton Ω[L/K]` is the unfolded form of `FormallyUnramified K L`, and
`EssFiniteType K L` is the iff's standing hypothesis.

When both witnesses are discharged unconditionally, this becomes the
unconditional reverse half of T-II-4-004. -/
theorem isogeny_isSeparable_of_kaehler_witnesses
    (α : Isogeny W.toAffine W.toAffine)
    (h_sub : @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ α.toAlgebra))
    (h_ess : @Algebra.EssFiniteType W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra) :
    α.IsSeparable := by
  letI : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  haveI : Algebra.EssFiniteType W.toAffine.FunctionField W.toAffine.FunctionField := h_ess
  haveI : Algebra.FormallyUnramified W.toAffine.FunctionField W.toAffine.FunctionField :=
    ⟨h_sub⟩
  exact (Algebra.FormallyUnramified.iff_isSeparable
    W.toAffine.FunctionField W.toAffine.FunctionField).mp inferInstance

/-- **T-II-4-004 reverse direction (combined witness form, axiom-clean)**:
if `Ω[K(E)/K(E)_α]` is trivial and `K(E)` is finite-dimensional over
`K(E)_α` (Witness #2 of the bound), then `α` is separable.

This composes `isogeny_essFiniteType_of_finiteDimensional` with
`isogeny_isSeparable_of_kaehler_witnesses`. The two substantive inputs are
exactly `FiniteDimensional` (Witness #2) and the relative-Kähler vanishing
(which the cotangent-sequence chain delivers from `pullbackKaehler injective`). -/
theorem isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional
    (α : Isogeny W.toAffine W.toAffine)
    (h_sub : @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ α.toAlgebra))
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule) :
    α.IsSeparable :=
  isogeny_isSeparable_of_kaehler_witnesses W α h_sub
    (isogeny_essFiniteType_of_finiteDimensional W α h_fin)

/-- **T-II-4-004 algebra-Kähler iff (axiom-clean witness form)**: `α` is separable
iff the relative Kähler module `Ω[K(E)/K(E)_α]` vanishes, given the
`FiniteDimensional` witness (Witness #2 of the bound).

The `FiniteDimensional` is essential for the reverse direction (gives
`EssFiniteType`, the standing hypothesis of `FormallyUnramified.iff_isSeparable`).
Forward direction is unconditional. -/
theorem isSeparable_iff_subsingleton_kaehler_of_finiteDimensional
    (α : Isogeny W.toAffine W.toAffine)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule) :
    α.IsSeparable ↔
      @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ α.toAlgebra) :=
  ⟨isogeny_subsingleton_kaehler_of_isSeparable W α,
   fun h_sub ↦
     isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional W α h_sub h_fin⟩

/-- **T-II-4-004 (witness-parametric, axiom-clean)**: the full iff
`α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0`, parametric on `FiniteDimensional`
(Witness #2) and the Subsingleton ↔ pullbackKaehler-injective bridge.

Composes:
* `isSeparable_iff_subsingleton_kaehler_of_finiteDimensional`: ties
  IsSeparable to Subsingleton via mathlib's iff (with FiniteDim hypothesis).
* The bridge witness: ties Subsingleton to pullbackKaehler injective (the
  cotangent-sequence connection).
* `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`: ties
  pullbackKaehler injective to ω-coeff ≠ 0 (axiom-clean scalar half). -/
theorem isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses
    (α : Isogeny W.toAffine W.toAffine)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule)
    (h_bridge : @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ α.toAlgebra) ↔
      Function.Injective α.pullbackKaehler) :
    α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0 :=
  (isSeparable_iff_subsingleton_kaehler_of_finiteDimensional W α h_fin).trans
    (h_bridge.trans (pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero W α))

/-- **Algebra-Kähler iff (witness-parametric)**: combines a forward-direction
implication and the reverse-direction implication into the full iff
`IsSeparable α ↔ pullbackKaehler injective`.

Forward direction: takes a witness `h_fwd : IsSeparable α → pullbackKaehler injective`.
Reverse direction: takes a witness `h_rev : pullbackKaehler injective → IsSeparable α`.

When both land axiom-clean, this fires the composition. -/
theorem isSeparable_iff_pullbackKaehler_injective_of_witnesses
    (α : Isogeny W.toAffine W.toAffine)
    (h_fwd : α.IsSeparable → Function.Injective α.pullbackKaehler)
    (h_rev : Function.Injective α.pullbackKaehler → α.IsSeparable) :
    α.IsSeparable ↔ Function.Injective α.pullbackKaehler :=
  ⟨h_fwd, h_rev⟩

/-- A type synonym for `K(E)` on the source side of the algebra structure
induced by an isogeny `α`. Carries `α.toAlgebra` as its only `Algebra` instance,
avoiding the `OreLocalization.instSMul` vs `α.toAlgebra.toSMul` defeq fight that
blocks the cotangent-sequence bridge `Subsingleton ↔ pullbackKaehler injective`. -/
def IsogenyAlgebraSource (_ : Isogeny W.toAffine W.toAffine) : Type _ :=
  W.toAffine.FunctionField

namespace IsogenyAlgebraSource

variable (α : Isogeny W.toAffine W.toAffine)

/-- The `IsogenyAlgebraSource` synonym is a `CommRing`, inheriting from `K(E)`. -/
noncomputable instance commRing : CommRing (IsogenyAlgebraSource W α) :=
  inferInstanceAs (CommRing W.toAffine.FunctionField)

/-- The `IsogenyAlgebraSource` synonym is a `Field`, inheriting from `K(E)`. -/
noncomputable instance field : Field (IsogenyAlgebraSource W α) :=
  inferInstanceAs (Field W.toAffine.FunctionField)

/-- The `IsogenyAlgebraSource` synonym carries the `F`-algebra structure
inherited from `K(E)`. -/
noncomputable instance algebraF : Algebra F (IsogenyAlgebraSource W α) :=
  inferInstanceAs (Algebra F W.toAffine.FunctionField)

/-- The `IsogenyAlgebraSource` synonym carries the `α.toAlgebra` structure as its
`Algebra (IsogenyAlgebraSource W α) K(E)` instance — the source-side
algebra-twist by `α.pullback`, with no competing `OreLocalization.instAlgebra`
on the synonym type. -/
noncomputable instance algebra : Algebra (IsogenyAlgebraSource W α)
    W.toAffine.FunctionField :=
  α.toAlgebra

/-- The synonym's `IsScalarTower F (IsogenyAlgebraSource W α) K(E)` is the
break-through `isogeny_isScalarTower` lifted to the synonym wrapper. -/
noncomputable instance isScalarTower :
    IsScalarTower F (IsogenyAlgebraSource W α) W.toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (α.pullback.commutes x).symm

end IsogenyAlgebraSource

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **trdeg F K(E) = 1 (axiom-clean, Weierstrass form)**: for any Weierstrass
curve `W`, the transcendence degree of `K(E) = W.toAffine.FunctionField` over
the base field `F` is 1.

Specializes the smooth-plane-curve trdeg result to Weierstrass curves. -/
theorem weierstrass_functionField_trdeg_eq_one :
    Algebra.trdeg F W.toAffine.FunctionField = 1 :=
  ({ toAffine := W.toAffine } : HasseWeil.Curves.SmoothPlaneCurve F).functionField_trdeg_eq_one

/-- **Witness #2 producer via the type-synonym wrapper** (witness-parametric,
axiom-clean): given `Algebra.IsAlgebraic (IsogenyAlgebraSource W α)
W.toAffine.FunctionField` and `Algebra.EssFiniteType (IsogenyAlgebraSource W α)
W.toAffine.FunctionField`, derive Witness #2 (`@FiniteDimensional` for
`α.toAlgebra.toModule`).

Both the type-synonym `Algebra` instance and `α.toAlgebra` are defeq, so this
mediates between the synonym world (where mathlib's IsAlgebraic/EssFiniteType
fire cleanly) and the @-α.toAlgebra world used by the bound's Witness #2. -/
theorem isogeny_finiteDimensional_of_isAlgebraic_synonym
    (α : Isogeny W.toAffine W.toAffine)
    [h_alg : Algebra.IsAlgebraic (IsogenyAlgebraSource W α) W.toAffine.FunctionField]
    [h_ess : Algebra.EssFiniteType (IsogenyAlgebraSource W α) W.toAffine.FunctionField] :
    @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule :=
  @Algebra.finite_of_essFiniteType_of_isAlgebraic (IsogenyAlgebraSource W α) _
    W.toAffine.FunctionField _ _ h_ess h_alg

/-- **EssFiniteType F K(E) (axiom-clean)**: K(E) is essentially of finite type
over F. K(E) is the FractionRing of CoordRing, which is itself FiniteType over F.
Localization preserves EssFiniteType (mathlib instance). -/
instance functionField_essFiniteType_F :
    Algebra.EssFiniteType F W.toAffine.FunctionField := by
  haveI : Algebra.FiniteType F W.toAffine.CoordinateRing := inferInstance
  haveI : Algebra.EssFiniteType F W.toAffine.CoordinateRing :=
    Algebra.EssFiniteType.of_finiteType F W.toAffine.CoordinateRing
  -- K(E) = FractionRing(CoordRing) = Localization(nonZeroDivisors).
  -- IsLocalization gives EssFiniteType from CoordRing-side.
  haveI : Algebra.EssFiniteType W.toAffine.CoordinateRing W.toAffine.FunctionField :=
    Algebra.EssFiniteType.of_isLocalization W.toAffine.FunctionField
      (nonZeroDivisors W.toAffine.CoordinateRing)
  exact Algebra.EssFiniteType.comp F W.toAffine.CoordinateRing W.toAffine.FunctionField

/-- **EssFiniteType `IsogenyAlgebraSource` K(E) (axiom-clean)**: derived from
`EssFiniteType F K(E)` via `EssFiniteType.of_comp`, using the
`IsScalarTower F (IsogenyAlgebraSource W α) K(E)` from the synonym wrapper. -/
instance isogenyAlgebraSource_essFiniteType
    (α : Isogeny W.toAffine W.toAffine) :
    Algebra.EssFiniteType (IsogenyAlgebraSource W α) W.toAffine.FunctionField :=
  Algebra.EssFiniteType.of_comp F (IsogenyAlgebraSource W α) W.toAffine.FunctionField

/-- The `F`-action on the `IsogenyAlgebraSource` synonym is faithful (the
algebra map `F → K(E)` is injective, being a ring hom out of a field). -/
instance isogenyAlgebraSource_faithfulSMul_F
    (α : Isogeny W.toAffine W.toAffine) :
    FaithfulSMul F (IsogenyAlgebraSource W α) :=
  (faithfulSMul_iff_algebraMap_injective F (IsogenyAlgebraSource W α)).mpr
    (algebraMap F (IsogenyAlgebraSource W α)).injective

/-- The `IsogenyAlgebraSource`-action on `K(E)` is faithful: its algebra map is
`α.pullback`, which is injective for any isogeny. -/
instance isogenyAlgebraSource_faithfulSMul_KE
    (α : Isogeny W.toAffine W.toAffine) :
    FaithfulSMul (IsogenyAlgebraSource W α) W.toAffine.FunctionField :=
  (faithfulSMul_iff_algebraMap_injective (IsogenyAlgebraSource W α)
    W.toAffine.FunctionField).mpr α.pullback_injective

/-- **Witness #2 producer step (axiom-clean)**: `K(E)` is algebraic over
`K(E)_α` (the `IsogenyAlgebraSource` synonym). Proof by transcendence-degree
additivity over `F → K(E)_α → K(E)`: both `trdeg F K(E)_α` and `trdeg F K(E)`
equal `1`, so `trdeg (K(E)_α) K(E) = 0`, which is `IsAlgebraic`. -/
instance isogenyAlgebraSource_isAlgebraic
    (α : Isogeny W.toAffine W.toAffine) :
    Algebra.IsAlgebraic (IsogenyAlgebraSource W α) W.toAffine.FunctionField := by
  rw [← trdeg_eq_zero_iff]
  have h_add :
      Algebra.trdeg F (IsogenyAlgebraSource W α) +
        Algebra.trdeg (IsogenyAlgebraSource W α) W.toAffine.FunctionField =
      Algebra.trdeg F W.toAffine.FunctionField :=
    trdeg_add_eq F (IsogenyAlgebraSource W α)
  have h_src : Algebra.trdeg F (IsogenyAlgebraSource W α) = 1 :=
    weierstrass_functionField_trdeg_eq_one W
  have h_top : Algebra.trdeg F W.toAffine.FunctionField = 1 :=
    weierstrass_functionField_trdeg_eq_one W
  rw [h_src, h_top] at h_add
  -- `1 + x = 1 ⟹ x = 0` in `Cardinal`: cancel the leading `1` via `add_one_inj`.
  refine Cardinal.add_one_inj.mp ?_
  rw [zero_add, add_comm]
  exact h_add

/-- **Witness #2 (axiom-clean, unconditional)**: for any isogeny `α`, the
function field `K(E)` is finite-dimensional over `K(E)_α` (the image of
`α.pullback`), i.e. the bound's Witness #2 holds with no extra hypothesis.

Direct from `isogeny_finiteDimensional_of_isAlgebraic_synonym` once the
`IsAlgebraic` and `EssFiniteType` instances above are in scope. -/
theorem isogeny_finiteDimensional (α : Isogeny W.toAffine W.toAffine) :
    @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule :=
  isogeny_finiteDimensional_of_isAlgebraic_synonym W α

/-- **Isogeny degrees are positive (axiom-clean, unconditional)**: for any isogeny
`α : E → E`, `0 < α.degree`.

`α.degree` is `Module.finrank K(E) K(E)` over the `K(E)`-module structure
`α.toAlgebra.toModule` induced by the pullback `α.pullback`.  This module is
finite-dimensional (`isogeny_finiteDimensional`, same instance) and `K(E)` is a
field hence `Nontrivial`, so `Module.finrank_pos` applies.  The instance is pinned
explicitly to `α.toAlgebra.toModule` so it matches `degree`'s definition (plain
`Module.finrank_pos` would otherwise synthesize the trivial self-module). -/
theorem isogeny_degree_pos (α : Isogeny W.toAffine W.toAffine) :
    0 < α.degree := by
  unfold Isogeny.degree
  exact @Module.finrank_pos W.toAffine.FunctionField W.toAffine.FunctionField _ _
    α.toAlgebra.toModule _ (isogeny_finiteDimensional W α) _ _ _

/-- **Bridge: mapBaseChange (1 ⊗ D x) = D (α.pullback x) (axiom-clean)**: applied
to the universal D-element under the type-synonym wrapper. -/
theorem isogeny_mapBaseChange_one_tmul_D
    (α : Isogeny W.toAffine W.toAffine) (x : W.toAffine.FunctionField) :
    KaehlerDifferential.mapBaseChange F (IsogenyAlgebraSource W α)
        W.toAffine.FunctionField
      ((1 : W.toAffine.FunctionField) ⊗ₜ
        KaehlerDifferential.D F (IsogenyAlgebraSource W α) x) =
      KaehlerDifferential.D F W.toAffine.FunctionField (α.pullback x) := by
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

/-- **Bridge: image of mapBaseChange contains the invariant differential** when
`omegaPullbackCoeff W α ≠ 0` (axiom-clean).

Direct preimage: `mapBaseChange (b ⊗ₜ D x_gen_full) = invariantDifferential` for
`b = (alpha_star_u • omegaPullbackCoeff)⁻¹` — derived from `omegaPullbackCoeff_spec`. -/
theorem isogeny_mapBaseChange_surjective_of_omegaCoeff_ne_zero
    (α : Isogeny W.toAffine W.toAffine)
    (h_coeff : omegaPullbackCoeff W α ≠ 0) :
    Function.Surjective (KaehlerDifferential.mapBaseChange F
      (IsogenyAlgebraSource W α) W.toAffine.FunctionField) := by
  intro y
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (kaehler_rank_one W.toAffine) (invariantDifferential_ne_zero W.toAffine) y
  refine ⟨a • (((omegaPullbackCoeff W α)⁻¹ * (alpha_star_u W α)⁻¹ :
      W.toAffine.FunctionField) ⊗ₜ
    KaehlerDifferential.D F (IsogenyAlgebraSource W α)
      (algebraMap (W.toAffine.CoordinateRing) W.toAffine.FunctionField
        (algebraMap (Polynomial F) (W.toAffine.CoordinateRing) Polynomial.X))), ?_⟩
  rw [map_smul, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
  have hu_ne : alpha_star_u W α ≠ 0 := by
    rw [alpha_star_u_eq]
    exact (map_ne_zero_iff α.pullback α.pullback_injective).mpr
      (u_gen_ne_zero W.toAffine)
  -- Rewrite `D(α.pullback X)` via `omegaPullbackCoeff_spec`, then cancel scalars.
  have h_D_eq :
      KaehlerDifferential.D F W.toAffine.FunctionField (α.pullback
        (algebraMap (W.toAffine.CoordinateRing) W.toAffine.FunctionField
          (algebraMap (Polynomial F) (W.toAffine.CoordinateRing) Polynomial.X))) =
      (alpha_star_u W α * omegaPullbackCoeff W α) •
        invariantDifferential W.toAffine := by
    have h2 : alpha_star_u W α •
        (omegaPullbackCoeff W α • invariantDifferential W.toAffine) =
        alpha_star_u W α • ((alpha_star_u W α)⁻¹ •
          KaehlerDifferential.D F W.toAffine.FunctionField (α.pullback
            (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
              (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)))) := by
      rw [omegaPullbackCoeff_spec W α]
    rw [smul_smul, smul_smul, mul_inv_cancel₀ hu_ne, one_smul] at h2
    exact h2.symm
  change a • (((omegaPullbackCoeff W α)⁻¹ * (alpha_star_u W α)⁻¹) •
    KaehlerDifferential.D F W.toAffine.FunctionField (α.pullback _)) = y
  rw [h_D_eq, smul_smul, smul_smul]
  have h_prod : a *
      ((omegaPullbackCoeff W α)⁻¹ * (alpha_star_u W α)⁻¹) *
      (alpha_star_u W α * omegaPullbackCoeff W α) = a := by
    field_simp
  rw [h_prod, ha]

/-- **Bridge: Subsingleton Ω[K(E)/K(E)_α] from omegaPullbackCoeff ≠ 0
(via type synonym, axiom-clean)**: the cotangent-sequence iff in the form needed
to discharge T-II-4-004's bridge witness. -/
theorem isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero
    (α : Isogeny W.toAffine W.toAffine) (h_coeff : omegaPullbackCoeff W α ≠ 0) :
    Subsingleton (Ω[W.toAffine.FunctionField⁄IsogenyAlgebraSource W α]) :=
  subsingleton_relativeKaehler_of_mapBaseChange_surjective F
    (IsogenyAlgebraSource W α) W.toAffine.FunctionField
    (isogeny_mapBaseChange_surjective_of_omegaCoeff_ne_zero W α h_coeff)

/-- **Bridge: Subsingleton via type synonym = Subsingleton via α.toAlgebra**
(axiom-clean, defeq). The two formulations of the relative Kähler module
coincide since `IsogenyAlgebraSource W α := K(E)` (defeq) and the synonym's
`Algebra` instance is `α.toAlgebra`. -/
theorem isogeny_subsingleton_via_synonym_eq
    (α : Isogeny W.toAffine W.toAffine) :
    Subsingleton (Ω[W.toAffine.FunctionField⁄IsogenyAlgebraSource W α]) ↔
    @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ α.toAlgebra) :=
  Iff.rfl

/-- Helper for `isogeny_omegaCoeff_ne_zero_of_isSeparable`: if the omega-based
pullback coefficient vanishes, then `α.pullbackKaehler` is identically zero on
`Ω[K(E)/F]`. Since `Ω` is one-dimensional over `K(E)` (`kaehler_rank_one`),
vanishing on the invariant differential `ω` spreads to every differential by
`α`-semilinearity (`pullbackKaehler_smul_KE`). -/
private theorem pullbackKaehler_eq_zero_of_omegaPullbackCoeff_eq_zero
    (α : Isogeny W.toAffine W.toAffine)
    (h_zero : omegaPullbackCoeff W α = 0)
    (ω' : Ω[W.toAffine.FunctionField⁄F]) :
    α.pullbackKaehler ω' = 0 := by
  have h_pK_ω : α.pullbackKaehler (invariantDifferential W.toAffine) = 0 := by
    rw [Isogeny.pullbackKaehler_invariantDifferential, h_zero, zero_smul]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine) ω'
  rw [← ha, Isogeny.pullbackKaehler_smul_KE, h_pK_ω, smul_zero]

/-- Helper for `isogeny_omegaCoeff_ne_zero_of_isSeparable`: if `α.pullbackKaehler`
vanishes identically, then the cotangent map `KaehlerDifferential.map` for the
square `F → F → K(E)_α → K(E)` is zero. The map agrees with `α.pullbackKaehler`
on the `D`-generator `D x` (both `0`), hence is `0` on the invariant differential
`ω = u⁻¹ • D x`, and `Ω` being one-dimensional then forces it to be `0` everywhere. -/
private theorem kaehlerMap_eq_zero_of_pullbackKaehler_eq_zero
    (α : Isogeny W.toAffine W.toAffine)
    (h_pK_zero : ∀ ω' : Ω[W.toAffine.FunctionField⁄F], α.pullbackKaehler ω' = 0) :
    KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField = 0 := by
  refine LinearMap.ext fun ω' ↦ ?_
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine) ω'
  change KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
    W.toAffine.FunctionField ω' = (0 : Ω[W.toAffine.FunctionField⁄F])
  rw [← ha]
  have h_map_D : KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField (KaehlerDifferential.D F (IsogenyAlgebraSource W α)
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X))) = 0 := by
    rw [KaehlerDifferential.map_D]
    exact (Isogeny.pullbackKaehler_D α _).symm.trans (h_pK_zero _)
  have h_map_ω : KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField (invariantDifferential W.toAffine) = 0 := by
    change KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField (((u_gen W)⁻¹ : IsogenyAlgebraSource W α) •
        KaehlerDifferential.D F (IsogenyAlgebraSource W α) _) = 0
    rw [LinearMap.map_smul, h_map_D, smul_zero]
  exact (LinearMap.map_smul (KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
    W.toAffine.FunctionField) a (invariantDifferential W.toAffine)).trans
    (by rw [h_map_ω, smul_zero])

/-- Helper for `isogeny_omegaCoeff_ne_zero_of_isSeparable`: if the cotangent map
`KaehlerDifferential.map` is zero, then so is `KaehlerDifferential.mapBaseChange`,
by tensor induction (`mapBaseChange (x ⊗ₜ y) = x • map y`). -/
private theorem mapBaseChange_eq_zero_of_kaehlerMap_eq_zero
    (α : Isogeny W.toAffine W.toAffine)
    (h_map_zero : KaehlerDifferential.map F F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField = 0) :
    KaehlerDifferential.mapBaseChange F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField = 0 := by
  refine LinearMap.ext fun η ↦ ?_
  induction η with
  | zero => simp
  | tmul x y => simp [KaehlerDifferential.mapBaseChange_tmul, h_map_zero]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **T-II-4-004 forward direction (axiom-clean)**: if `α` is separable,
then `omegaPullbackCoeff W α ≠ 0`.

Pipeline: `IsSeparable → Subsingleton Ω[K(E)/K(E)_α]` →
`mapBaseChange surjective` (via the type synonym) → in particular,
`invariantDifferential ∈ image(mapBaseChange)` (cotangent exact sequence).
A nonzero image element forces `α.pullbackKaehler` not-identically-zero,
which (with the 1-dim Ω structure) forces `omegaPullbackCoeff ≠ 0`. -/
theorem isogeny_omegaCoeff_ne_zero_of_isSeparable
    (α : Isogeny W.toAffine W.toAffine)
    (h_sep : α.IsSeparable) :
    omegaPullbackCoeff W α ≠ 0 := by
  intro h_zero
  -- `α.pullbackKaehler` is `α`-semilinear and `Ω` is 1-dim, so vanishing on `ω`
  -- forces it to vanish everywhere.
  have h_pK_zero : ∀ ω' : Ω[W.toAffine.FunctionField⁄F],
      α.pullbackKaehler ω' = 0 :=
    pullbackKaehler_eq_zero_of_omegaPullbackCoeff_eq_zero W α h_zero
  haveI : Subsingleton (Ω[W.toAffine.FunctionField⁄IsogenyAlgebraSource W α]) :=
    (isogeny_subsingleton_via_synonym_eq W α).mpr
      (isogeny_subsingleton_kaehler_of_isSeparable W α h_sep)
  have h_surj : Function.Surjective (KaehlerDifferential.mapBaseChange F
      (IsogenyAlgebraSource W α) W.toAffine.FunctionField) :=
    mapBaseChange_surjective_of_subsingleton_relativeKaehler F
      (IsogenyAlgebraSource W α) W.toAffine.FunctionField
  obtain ⟨t, ht⟩ := h_surj (invariantDifferential W.toAffine)
  -- The cotangent map `map : Ω[K(E)/F] → Ω[K(E)/F]` agrees with `α.pullbackKaehler`
  -- on `D`-generators (both are `0`), and is determined on the 1-dim `Ω` by `ω`;
  -- `map = 0` then forces `mapBaseChange = 0`, contradicting surjectivity.
  have h_mbc_zero : KaehlerDifferential.mapBaseChange F (IsogenyAlgebraSource W α)
      W.toAffine.FunctionField = 0 :=
    mapBaseChange_eq_zero_of_kaehlerMap_eq_zero W α
      (kaehlerMap_eq_zero_of_pullbackKaehler_eq_zero W α h_pK_zero)
  rw [h_mbc_zero, LinearMap.zero_apply] at ht
  exact (invariantDifferential_ne_zero W.toAffine) ht.symm

/-- **T-II-4-004 reverse direction (witness-parametric on FiniteDim only,
axiom-clean)**: if `omegaPullbackCoeff W α ≠ 0` and `K(E)` is finite-dimensional
over `K(E)_α` (Witness #2), then `α` is separable.

Combines the cotangent-sequence bridge (omega-coeff ≠ 0 → Subsingleton) with the
algebra-Kähler reverse direction (Subsingleton + FiniteDim → IsSeparable). -/
theorem isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim
    (α : Isogeny W.toAffine W.toAffine)
    (h_coeff : omegaPullbackCoeff W α ≠ 0)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule) :
    α.IsSeparable :=
  isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional W α
    ((isogeny_subsingleton_via_synonym_eq W α).mp
      (isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero W α h_coeff))
    h_fin

/-- **T-II-4-004 full iff (witness-parametric on FiniteDim only, axiom-clean)**:
the deliverable iff `α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0` modulo only
the Witness #2 hypothesis (FiniteDimensional).

Combines the forward direction (no extra hypothesis) and the reverse direction
(needs FiniteDim).

Once Witness #2 discharges unconditionally, the full T-II-4-004 lands. -/
theorem isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim
    (α : Isogeny W.toAffine W.toAffine)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule) :
    α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0 :=
  ⟨isogeny_omegaCoeff_ne_zero_of_isSeparable W α,
   fun h ↦ isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim W α h h_fin⟩

/-- **T-II-4-004 reverse direction (witness-parametric, axiom-clean)**: if
`α.pullbackKaehler` is injective on `Ω[K(E)/F]`, then given Witness #2
(`FiniteDimensional`) and the algebra-Kähler bridge
(`Subsingleton ↔ pullbackKaehler injective`), `α` is separable.

Composes the bridge's reverse direction (`pullbackKaehler injective →
Subsingleton`) with `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`. -/
theorem isogeny_isSeparable_of_pullbackKaehler_injective_witnesses
    (α : Isogeny W.toAffine W.toAffine)
    (h_inj : Function.Injective α.pullbackKaehler)
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ α.toAlgebra.toModule)
    (h_bridge : @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ α.toAlgebra) ↔
      Function.Injective α.pullbackKaehler) :
    α.IsSeparable :=
  isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional W α
    (h_bridge.mpr h_inj) h_fin

/-- **T-II-4-004 reverse direction (axiom-clean, unconditional)**: if the
differential pullback `α.pullbackKaehler` is injective on `Ω[K(E)/F]`, then `α`
is separable.

Discharge path:
* Witness #2 (`FiniteDimensional` of `K(E)/(image)`) — gives `EssFiniteType`.
* Connection from `omegaPullbackCoeff ≠ 0` (the scalar form of injectivity)
  to `Subsingleton Ω[K(E)/(image)]` (the algebra-side condition).
* Mathlib's `Algebra.FormallyUnramified.iff_isSeparable` for the final
  conclusion. -/
theorem isogeny_isSeparable_of_pullbackKaehler_injective
    (α : Isogeny W.toAffine W.toAffine)
    (h_inj : Function.Injective α.pullbackKaehler) :
    α.IsSeparable :=
  isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim W α
    ((pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero W α).mp h_inj)
    (isogeny_finiteDimensional W α)

/-- **T-II-4-004 algebra-Kähler half (axiom-clean)**: an isogeny `α` is separable
(in the `Algebra.IsSeparable` sense) iff its differential pullback
`α.pullbackKaehler` is injective on `Ω[K(E)/F]`.

This is the substantive Silverman II.4.2(c) algebra-Kähler glue.
The forward direction: `Algebra.IsSeparable → FormallyUnramified
→ Ω[K(E)/(image)] = 0 → cotangent surjective → pullbackKaehler injective`.
The reverse: the converse chain via `FormallyUnramified.iff_isSeparable`. -/
theorem isSeparable_iff_pullbackKaehler_injective
    (α : Isogeny W.toAffine W.toAffine) :
    α.IsSeparable ↔ Function.Injective α.pullbackKaehler :=
  ⟨fun h ↦ (pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero W α).mpr
      (isogeny_omegaCoeff_ne_zero_of_isSeparable W α h),
   isogeny_isSeparable_of_pullbackKaehler_injective W α⟩

/-- **T-II-4-004 (elliptic curve form, deliverable target)**: separability of
an isogeny `α` is equivalent to its omega-pullback coefficient being nonzero
(equivalently, to the differential pullback `α*` being injective on
`Ω[K(E)/F]`).

Reference: Silverman II.4.2(c). -/
theorem isSeparable_iff_omegaPullbackCoeff_ne_zero
    (α : Isogeny W.toAffine W.toAffine) :
    α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0 :=
  isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler W α
    (isSeparable_iff_pullbackKaehler_injective W α)

end HasseWeil
