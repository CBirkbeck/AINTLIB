/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-!
# The relative Picard functor (GME §2.2.2, functor layer of (2.16))

For `p : E ⟶ S` with a section `z : S ⟶ E` (the zero section of an elliptic curve, but
stated for any retraction pair), GME p. 108 introduces the contravariant functor

`Pic_{E/S}(T) = Pic(E ×_S T)/f_T^* Pic(T)` for `f_T : E ×_S T → T`,

and p. 109 gives the working model: "Since we have the 0-section `0 : S ↪ E`, we have a
group homomorphism `0* : Pic(E) → Pic(S)` for which `f*` is a section. Thus
`Pic(E) = Ker(0*) ⊕ Im(f*)`". We take the kernel `Ker(0*)` as the definition (`picRel`)
and record the comparison with the displayed quotient as `nonempty_picRel_mulEquiv_quotient`.

This file is the skeleton produced by the `/develop --decompose` pass recorded in
`.mathlib-quality/decomposition-pic-rel-functor.md`; the degree-0 subfunctor and Abel's
isomorphism `E ≅ Pic⁰` ((2.16) proper) are explicitly deferred there.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.picRel`: the relative Picard group of `T ⟶ S`, as the
  kernel of the zero-section pullback on `Pic (E ×_S T)`.
* `AlgebraicGeometry.Scheme.Modules.picRelFunctor`: `Pic_{E/S}` as a contravariant
  group-valued functor on `S`-schemes.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {S E : Scheme.{u}} (p : E ⟶ S) (z : S ⟶ E) (hz : z ≫ p = 𝟙 S)

variable {T T' T'' : Scheme.{u}}

/-- The base change to `T` of the section `z`: `z_T : T ⟶ E ×_S T`. -/
noncomputable def baseChangeZero (t : T ⟶ S) : T ⟶ Limits.pullback p t :=
  Limits.pullback.lift (t ≫ z) (𝟙 T)
    (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])

/-- The base-changed section is a section of the base-changed structure map. -/
theorem baseChangeZero_snd (t : T ⟶ S) :
    baseChangeZero p z hz t ≫ Limits.pullback.snd p t = 𝟙 T :=
  Limits.pullback.lift_snd _ _ _

/-- **The relative Picard group in its kernel model** (GME p. 109: "Thus
`Pic(E) = Ker(0*) ⊕ Im(f*)` and therefore `Pic_{E/S}` is actually a subfunctor of
`Pic_{/E}`"): classes on `E ×_S T` whose zero-section pullback is trivial. -/
noncomputable def picRel (t : T ⟶ S) : Subgroup (Pic (Limits.pullback p t)) :=
  (Pic.map (baseChangeZero p z hz t)).ker

/-- Normalizing a class by its zero-section pullback lands in the relative Picard
group. -/
theorem mul_inv_map_map_mem (t : T ⟶ S) (x : Pic (Limits.pullback p t)) :
    x * (Pic.map (Limits.pullback.snd p t)
      (Pic.map (baseChangeZero p z hz t) x))⁻¹ ∈ picRel p z hz t := by
  refine MonoidHom.mem_ker.mpr ?_
  rw [map_mul, map_inv]
  have hrs : Pic.map (baseChangeZero p z hz t)
      (Pic.map (Limits.pullback.snd p t) (Pic.map (baseChangeZero p z hz t) x)) =
      Pic.map (baseChangeZero p z hz t) x := by
    calc (Pic.map (baseChangeZero p z hz t)
          (Pic.map (Limits.pullback.snd p t) (Pic.map (baseChangeZero p z hz t) x)))
        = Pic.map (baseChangeZero p z hz t ≫ Limits.pullback.snd p t)
            (Pic.map (baseChangeZero p z hz t) x) := by rw [Pic.map_comp]; rfl
      _ = Pic.map (baseChangeZero p z hz t) x := by
          rw [baseChangeZero_snd, Pic.map_id]; rfl
  rw [hrs, mul_inv_cancel]

/-- The retraction projection onto the relative Picard group: normalize a class by its
zero-section pullback, `x ↦ x * (f_T^*(z_T^* x))⁻¹` (the kernel projection of the
GME p. 109 splitting `Pic(E) = Ker(0*) ⊕ Im(f*)`). -/
noncomputable def picRelProj (t : T ⟶ S) :
    Pic (Limits.pullback p t) →* picRel p z hz t :=
  (MonoidHom.id (Pic (Limits.pullback p t)) *
    ((Pic.map (Limits.pullback.snd p t)).comp
      (Pic.map (baseChangeZero p z hz t)))⁻¹).codRestrict _
    (mul_inv_map_map_mem p z hz t)

/-- Classes pulled back from the base die in the relative Picard group: `f_T^* Pic(T)` is
exactly the kernel of the projection (GME p. 109's splitting). -/
theorem picRelProj_map_snd (t : T ⟶ S) (M : Pic T) :
    picRelProj p z hz t (Pic.map (Limits.pullback.snd p t) M) = 1 := by
  refine Subtype.ext ?_
  have h : Pic.map (baseChangeZero p z hz t) (Pic.map (Limits.pullback.snd p t) M) = M := by
    calc Pic.map (baseChangeZero p z hz t) (Pic.map (Limits.pullback.snd p t) M)
        = Pic.map (baseChangeZero p z hz t ≫ Limits.pullback.snd p t) M := by
          rw [Pic.map_comp]; rfl
      _ = M := by rw [baseChangeZero_snd, Pic.map_id]; rfl
  show Pic.map (Limits.pullback.snd p t) M *
      (Pic.map (Limits.pullback.snd p t)
        (Pic.map (baseChangeZero p z hz t) (Pic.map (Limits.pullback.snd p t) M)))⁻¹ = 1
  rw [h, mul_inv_cancel]

/-- Two classes with the same image in the relative Picard group are exactly those differing
by a class pulled back from the base. This is the form in which the theorem of the square is
consumed: the difference bundle need only be shown to come from `T`. -/
theorem picRelProj_eq_of_mul_inv_eq_map_snd (t : T ⟶ S)
    {x y : Pic (Limits.pullback p t)} {M : Pic T}
    (h : x * y⁻¹ = Pic.map (Limits.pullback.snd p t) M) :
    picRelProj p z hz t x = picRelProj p z hz t y := by
  have h1 : picRelProj p z hz t (x * y⁻¹) = 1 := by
    rw [h]; exact picRelProj_map_snd p z hz t M
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- **Comparison with the displayed definition** (GME p. 108, the definition preceding
(2.16): "`Pic_{E/S}(T) = Pic(E ×_S T)/f_T^* Pic(T)`"): the zero-section splitting
identifies the quotient with the kernel model. -/
theorem nonempty_picRel_mulEquiv_quotient (t : T ⟶ S) :
    Nonempty ((Pic (Limits.pullback p t) ⧸ (Pic.map (Limits.pullback.snd p t)).range) ≃*
      picRel p z hz t) := by
  set r := Pic.map (baseChangeZero p z hz t) with hr
  set sec := Pic.map (Limits.pullback.snd p t) with hsec
  have hrs : ∀ y, r (sec y) = y := by
    intro y
    calc r (sec y)
        = Pic.map (baseChangeZero p z hz t ≫ Limits.pullback.snd p t) y := by
          rw [Pic.map_comp]; rfl
      _ = y := by rw [baseChangeZero_snd, Pic.map_id]; rfl
  let π : Pic (Limits.pullback p t) →* Pic (Limits.pullback p t) :=
    MonoidHom.id _ * (sec.comp r)⁻¹
  have hπ_apply : ∀ x, π x = x * (sec (r x))⁻¹ := fun x => rfl
  have hπ_mem : ∀ x, π x ∈ picRel p z hz t := by
    intro x
    refine MonoidHom.mem_ker.mpr ?_
    show r (x * (sec (r x))⁻¹) = 1
    rw [map_mul, map_inv, hrs, mul_inv_cancel]
  let π' : Pic (Limits.pullback p t) →* picRel p z hz t := π.codRestrict _ hπ_mem
  have hsurj : Function.Surjective π' := by
    rintro ⟨k, hk⟩
    refine ⟨k, Subtype.ext ?_⟩
    show k * (sec (r k))⁻¹ = k
    rw [MonoidHom.mem_ker.mp hk, map_one, inv_one, mul_one]
  have hker : π'.ker = sec.range := by
    ext x
    constructor
    · intro hx
      have hx1 : x * (sec (r x))⁻¹ = 1 := congrArg Subtype.val hx
      exact ⟨r x, (mul_inv_eq_one.mp hx1).symm⟩
    · rintro ⟨y, rfl⟩
      refine Subtype.ext ?_
      show sec y * (sec (r (sec y)))⁻¹ = 1
      rw [hrs, mul_inv_cancel]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π' hsurj)⟩

/-- The base change `g_E = 1_E ×_S g` of `g : T' ⟶ T` over `S` (GME p. 108: "If
`g : T' → T` is an `S`-morphism, we have `g_E = 1_E ×_S g : E'_T → E_T`"). -/
noncomputable def baseChangeMap {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    Limits.pullback p t' ⟶ Limits.pullback p t :=
  Limits.pullback.map p t' p t (𝟙 E) g (𝟙 S) (by simp) (by simp [hg])

/-- Base change of the zero section is compatible with base change of the curve. -/
theorem baseChangeZero_baseChangeMap {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') :
    baseChangeZero p z hz t' ≫ baseChangeMap p g hg = g ≫ baseChangeZero p z hz t := by
  ext <;> simp [baseChangeZero, baseChangeMap, Limits.pullback.map, ← hg,
    Limits.pullback.lift_fst, Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc]

/-- Pullback along `g_E` preserves the kernel model (GME p. 108: "This induces
`Pic^ν(g)(L) = g_E^*(L)`"). -/
theorem pic_map_baseChangeMap_mem {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') {L : Pic (Limits.pullback p t)} (hL : L ∈ picRel p z hz t) :
    Pic.map (baseChangeMap p g hg) L ∈ picRel p z hz t' := by
  refine MonoidHom.mem_ker.mpr ?_
  calc Pic.map (baseChangeZero p z hz t') (Pic.map (baseChangeMap p g hg) L)
      = Pic.map (baseChangeZero p z hz t' ≫ baseChangeMap p g hg) L := by
        rw [Pic.map_comp]; rfl
    _ = Pic.map (g ≫ baseChangeZero p z hz t) L := by
        rw [baseChangeZero_baseChangeMap]
    _ = Pic.map g (Pic.map (baseChangeZero p z hz t) L) := by
        rw [Pic.map_comp]; rfl
    _ = Pic.map g 1 := by rw [MonoidHom.mem_ker.mp hL]
    _ = 1 := map_one _

/-- Base change of maps is functorial. -/
theorem baseChangeMap_id (t : T ⟶ S) :
    baseChangeMap p (𝟙 T) (Category.id_comp t) = 𝟙 (Limits.pullback p t) := by
  ext <;> simp [baseChangeMap, Limits.pullback.map,
    Limits.pullback.lift_fst, Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc]

/-- Base change of maps is functorial. -/
theorem baseChangeMap_comp {t : T ⟶ S} {t' : T' ⟶ S} {t'' : T'' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t') (g' : T'' ⟶ T') (hg' : g' ≫ t' = t'') :
    baseChangeMap p (g' ≫ g) (by rw [Category.assoc, hg, hg']) =
      baseChangeMap p g' hg' ≫ baseChangeMap p g hg := by
  ext <;> simp [baseChangeMap, Limits.pullback.map,
    Limits.pullback.lift_fst, Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc]

/-- **`Pic_{E/S}` as a contravariant group functor on `S`-schemes** (GME p. 108: "we
consider the following contravariant functors `Pic_{E/S}, Pic^ν : SCH_{/S} → SETS`";
the group structure is GME p. 108 bottom: "`Pic⁰` is a group functor with the identity
`O_E` under the multiplication: `L · L' = L ⊗ L'`"). -/
noncomputable def picRelFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (picRel p z hz T.unop.hom)
  map {T T'} g := CommGrpCat.ofHom
    (((Pic.map (baseChangeMap p g.unop.left (Over.w g.unop))).comp
      (picRel p z hz T.unop.hom).subtype).codRestrict _
      (fun L => pic_map_baseChangeMap_mem p z hz g.unop.left (Over.w g.unop) L.2))
  map_id := by
    intro T
    ext L
    show Pic.map (baseChangeMap p (𝟙 T).unop.left (Over.w (𝟙 T).unop)) L.1 = L.1
    rw [show baseChangeMap p (𝟙 T).unop.left (Over.w (𝟙 T).unop) =
        𝟙 (Limits.pullback p T.unop.hom) from baseChangeMap_id p T.unop.hom,
      Pic.map_id]
    rfl
  map_comp := by
    intro T T' T'' g g'
    ext L
    show Pic.map (baseChangeMap p (g ≫ g').unop.left (Over.w (g ≫ g').unop)) L.1 =
      Pic.map (baseChangeMap p g'.unop.left (Over.w g'.unop))
        (Pic.map (baseChangeMap p g.unop.left (Over.w g.unop)) L.1)
    rw [show baseChangeMap p (g ≫ g').unop.left (Over.w (g ≫ g').unop) =
        baseChangeMap p g'.unop.left (Over.w g'.unop) ≫
          baseChangeMap p g.unop.left (Over.w g.unop) from
      baseChangeMap_comp p g.unop.left (Over.w g.unop) g'.unop.left (Over.w g'.unop),
      Pic.map_comp]
    rfl

end AlgebraicGeometry.Scheme.Modules
