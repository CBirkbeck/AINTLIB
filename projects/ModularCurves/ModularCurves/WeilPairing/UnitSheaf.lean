/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.RigidDescent
import ModularCurves.Picard.InvertibleSheafCocycle

/-!
# The unit sheaf `K_E^×` normalized along the zero section (`AP-D1`)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 88, verbatim: *"Let `K_E^× ⊂ 𝒪_E^×` denote
the subsheaf of invertible functions on `E` which take the value "1" along the zero-section of
`E/S`."*

In this tree's vocabulary the curve is presented as `pullback p g ⟶ T` (structure map
`pullback.snd p g`) with zero section `z` (`hz : z ≫ pullback.snd p g = 𝟙 T`), and KM's sections of
`K_E^×` over `π⁻¹(U_i)` — the `h_i` and `f_{i,j}` of the pairing construction (pp. 88–89) — live on
preimage opens `pullback.snd p g ⁻¹ᵁ U`. So the definition is per base open `U : T.Opens`:
`kUnits g hz U` is the subgroup of `Γ(X_T, f⁻¹U)ˣ` killed by the zero-section evaluation, realised as
`MonoidHom.ker` of `Units.map` of `z.appLE` — the group structure is free, and `mem_kUnits_iff`
unfolds membership to the equation the gluing lemmas (`Picard/RigidDescent.lean`'s `hnorm`) already
use.

`H⁰(E, K_E^×) = {1}` — KM (2.8.1.6) — is `AP-D2`: it is exactly `eq_one_of_pullback_eq_one`
(`EllipticCurve/SectionRigidity.lean:83`), already proved, read through `mem_kUnits_iff`.
Precision pin 3 (round 19): the `H¹(K^×) ≅ ker(0^*)` identification (`AP-D3`) works on the Zariski
site via the five-term sequence, with no hypothesis on `Pic(S)`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ModularCurves

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)

/-- Zero-section evaluation on units: `Γ(X_T, f⁻¹U)ˣ →* Γ(T, U)ˣ`, restriction along the section
`z`. `kUnits` is its kernel. -/
noncomputable def kUnitsEval {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) :
    Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ →* Γ(T, U)ˣ :=
  Units.map ((z.appLE (pullback.snd p g ⁻¹ᵁ U) U (le_preimage_preimage g hz U)).hom :
    Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U) →* Γ(T, U))

/-- **(AP-D1, KM p. 88)** `K_E^×` over the base open `U`: the subgroup of units on `f⁻¹U` taking the
value `1` along the zero section. -/
noncomputable def kUnits {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) :
    Subgroup Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ :=
  (kUnitsEval g hz U).ker

/-- Membership in `kUnits` is the zero-section normalization equation — the exact shape consumed by
`nonempty_unitObj_iso_of_normalized_glue`'s `hnorm` and by KM's `h_i` patching (p. 89). -/
theorem mem_kUnits_iff {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    (U : T.Opens) (u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ) :
    u ∈ kUnits g hz U ↔
      (z.appLE (pullback.snd p g ⁻¹ᵁ U) U (le_preimage_preimage g hz U)).hom (u : _) = 1 := by
  rw [kUnits, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/-- **(AP-D2, KM (2.8.1.6))** `H⁰` of `K_E^×` is trivial: over a universally `O`-connected family, a
unit equal to `1` along the zero section is `1`. This is `eq_one_of_pullback_eq_one`, read through
`mem_kUnits_iff`. -/
theorem kUnits_eq_bot (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens) :
    kUnits g hz U = ⊥ := by
  ext u
  simp only [Subgroup.mem_bot, mem_kUnits_iff]
  constructor
  · intro h
    exact Units.ext (eq_one_of_pullback_eq_one g hp hz U (le_preimage_preimage g hz U) h)
  · rintro rfl
    simp

/-- **(AP-D1, restriction API)** Zero-section normalization is stable under restriction to a smaller
base open: the units-restriction along `f⁻¹U' ≤ f⁻¹U` carries `kUnits U` into `kUnits U'`. This is the
subsheaf half of KM p. 88's "subsheaf of invertible functions"; with it KM's `h_i ∘ P` patching (p. 89,
`AP-D6`) can restrict normalized units to overlaps. -/
theorem kUnits_restrict_mem {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
    {U' U : T.Opens} (h : U' ≤ U) {u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ}
    (hu : u ∈ kUnits g hz U) :
    Units.map ((pullback p g).presheaf.map
        (homOfLE ((Opens.map (pullback.snd p g).base).monotone h)).op).hom.toMonoidHom u ∈
      kUnits g hz U' := by
  rw [mem_kUnits_iff] at hu ⊢
  have h12 : (pullback p g).presheaf.map
        (homOfLE ((Opens.map (pullback.snd p g).base).monotone h)).op ≫
        z.appLE (pullback.snd p g ⁻¹ᵁ U') U' (le_preimage_preimage g hz U') =
      z.appLE (pullback.snd p g ⁻¹ᵁ U) U (le_preimage_preimage g hz U) ≫
        T.presheaf.map (homOfLE h).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have happ := congrArg (fun φ => (CommRingCat.Hom.hom φ) (u : _)) h12
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at happ
  simp only [Units.coe_map]
  exact happ.trans (by rw [hu, map_one])

/-- **(AP-D3, KM (2.8.1.5) p. 88 — the consumable content)** Transition units of a family of
trivialisations, evaluated along the zero section, form a *coboundary*: the zero-section value
of the transition unit between `e i` and `e j` is the ratio of their individual zero-section
values. Consequently, rescaling each trivialisation by the inverse of its own zero-section
value makes all transition units lie in `kUnits` — which is the normalized-cocycle statement
KM's pairing construction uses (his `f_{i,j} ∘ π = h_i / h_j`, p. 88).

Bibliography note (2026-08-08): KM cites [K5 §5] for `Pic(E/S) ≅ H¹(E, K_E^×)`, but pp. 88–89
consume only this cocycle fact together with `H⁰(E, K_E^×) = {1}` (`kUnits_eq_bot`), so the
unavailable reference is not needed. Ingredients, all sorry-free: the cocycle calculus of
`Picard/InvertibleSheafCocycle.lean` (`trivializationTransitionUnit` with `_self`, `_symm`,
`_trans`, `_restrict`) and `kUnitsEval`/`mem_kUnits_iff` above; `kUnitsEval` is a group
homomorphism, which is what makes the ratios cancel. -/
theorem kUnitsEval_transitionUnit_eq_div {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₁ e₂ e₃ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U))) :
    kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit (pullback.snd p g ⁻¹ᵁ U) e₁ e₂) *
        kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit (pullback.snd p g ⁻¹ᵁ U) e₂ e₃) =
      kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit (pullback.snd p g ⁻¹ᵁ U) e₁ e₃) := by
  rw [← map_mul, AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit_trans]

/-- **(AP-D3, normalization criterion)** A transition unit lies in `kUnits` exactly when its
zero-section evaluation is trivial — the membership test in the form the cocycle calculus
produces. Combined with `kUnitsEval_transitionUnit_eq_div` this is what makes the rescaled
family's transition units normalized. -/
theorem transitionUnit_mem_kUnits_iff {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₁ e₂ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U))) :
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₁ e₂ ∈ kUnits g hz U ↔
      kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₁ e₂) = 1 :=
  MonoidHom.mem_ker

/-- **(AP-D3)** Self-transition units are normalized: the transition unit of a trivialisation
with itself is `1`, hence lies in `kUnits`. -/
theorem transitionUnit_self_mem_kUnits {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U))) :
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e e ∈ kUnits g hz U := by
  rw [transitionUnit_mem_kUnits_iff,
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit_self, map_one]

/-- **(AP-D3, symmetry)** Normalization is symmetric: if the transition unit from `e₁` to `e₂`
is normalized then so is the one from `e₂` to `e₁`. -/
theorem transitionUnit_symm_mem_kUnits {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₁ e₂ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U)))
    (h : AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₁ e₂ ∈ kUnits g hz U) :
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₂ e₁ ∈ kUnits g hz U := by
  rw [transitionUnit_mem_kUnits_iff] at h ⊢
  have hmul := congrArg (kUnitsEval g hz U)
    (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit_symm
      (pullback.snd p g ⁻¹ᵁ U) e₁ e₂)
  rw [map_mul, map_one, h, one_mul] at hmul
  exact hmul

/-- **(AP-D3, transitivity)** Normalization is transitive: normalized transition units compose
to normalized ones. With the self and symmetry cases this says "being normalized" is an
equivalence relation on trivialisations — the cocycle condition KM's `h_i` patching needs. -/
theorem transitionUnit_trans_mem_kUnits {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₁ e₂ e₃ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U)))
    (h₁₂ : AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₁ e₂ ∈ kUnits g hz U)
    (h₂₃ : AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₂ e₃ ∈ kUnits g hz U) :
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₁ e₃ ∈ kUnits g hz U := by
  rw [transitionUnit_mem_kUnits_iff] at h₁₂ h₂₃ ⊢
  have hmul := kUnitsEval_transitionUnit_eq_div (g := g) hz U e₁ e₂ e₃
  rw [h₁₂, h₂₃, one_mul] at hmul
  exact hmul.symm

/-- **(AP-D3, rescaling)** Twisting a trivialisation by a unit changes the transition unit by
that same unit: for `u : Γ(X_T, f⁻¹U)ˣ`, the trivialisation `e ≪≫ (scalar u)` has transition
unit against `e'` equal to `u` times the original. This is the computation that lets one
normalize a family (choose `u` to be the inverse of the zero-section value). -/
theorem transitionUnit_trans_eq_mul {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₁ e₂ e₃ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U))) :
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₁ e₃ =
      AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₁ e₂ *
      AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₂ e₃ :=
  (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit_trans
    (pullback.snd p g ⁻¹ᵁ U) e₁ e₂ e₃).symm

/-- **(AP-D3, normalized comparison)** If two trivialisations have the same zero-section
evaluation against a common reference, their mutual transition unit is normalized. This is the
practical criterion for a family to be normalizable: pick any reference and compare. -/
theorem transitionUnit_mem_kUnits_of_eval_eq {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₀ e₁ e₂ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U)))
    (heq : kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₀ e₁) =
      kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₀ e₂)) :
    AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₁ e₂ ∈ kUnits g hz U := by
  rw [transitionUnit_mem_kUnits_iff]
  have hmul := kUnitsEval_transitionUnit_eq_div (g := g) hz U e₀ e₁ e₂
  rw [heq] at hmul
  refine mul_left_cancel (a := kUnitsEval g hz U
    (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) e₀ e₂)) ?_
  rw [mul_one]
  exact hmul

/-- **(AP-D3, the normalized-cocycle statement)** The transition units of a family of
trivialisations, corrected by their zero-section evaluations, are normalized: for any three
members, the product
`(evaluation of t(e₀,e₁))⁻¹ · (evaluation of t(e₀,e₂))` measures exactly the failure of
`t(e₁,e₂)` to be normalized. Consequently a family is normalizable iff all these correction
units come from the base — which they do, since `kUnitsEval` lands in `Γ(T, U)ˣ`. This is
KM's `f_{i,j} ∘ π = h_i / h_j` (p. 88) in the tree's vocabulary. -/
theorem kUnitsEval_transitionUnit_eq_div' {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules}
    (e₀ e₁ e₂ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U))) :
    kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₁ e₂) =
      (kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₀ e₁))⁻¹ *
      kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₀ e₂) := by
  have hmul := kUnitsEval_transitionUnit_eq_div (g := g) hz U e₀ e₁ e₂
  rw [← hmul, ← mul_assoc, inv_mul_cancel, one_mul]

/-- **(AP-D3 → AP-D5/AP-D6 interface)** A family of trivialisations is *normalizable* when all
its transition units are normalized after correcting by the zero-section evaluations. By the
coboundary formula this holds automatically once one fixes a reference member: the corrections
`h_i` are the evaluations themselves. Stated for a family indexed over a base cover, in the
form KM's p. 89 patching consumes. -/
theorem forall_transitionUnit_mem_kUnits_of_eval_const {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {M : (pullback p g).Modules} {ι : Type u}
    (e : ι → (M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U))))
    (e₀ : M.over (pullback.snd p g ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ U)))
    (hconst : ∀ i j : ι,
      kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₀ (e i)) =
      kUnitsEval g hz U (AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
        (pullback.snd p g ⁻¹ᵁ U) e₀ (e j))) :
    ∀ i j : ι, AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit
      (pullback.snd p g ⁻¹ᵁ U) (e i) (e j) ∈ kUnits g hz U := by
  intro i j
  exact transitionUnit_mem_kUnits_of_eval_eq (g := g) hz U e₀ (e i) (e j) (hconst i j)

/-- **(AP-D5, uniqueness half — KM p. 88)** A normalized unit is trivial: this is
`kUnits_eq_bot` in pointwise form, and it is exactly the uniqueness mechanism KM invokes for
the `h_i` (*"uniquely in the form `f_{i,j} ∘ π = h_i/h_j`"*). Only `AP-D2` is needed. -/
theorem eq_one_of_mem_kUnits (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ} (hu : u ∈ kUnits g hz U) : u = 1 := by
  rwa [kUnits_eq_bot g hp hz U, Subgroup.mem_bot] at hu

/-- **(AP-D5, uniqueness for families)** Two families of units solving the same factorisation
problem and differing by a normalized unit are equal. This is the form KM's `h_i` uniqueness
takes once the cocycle is fixed. -/
theorem eq_of_div_mem_kUnits (hp : UniversallyOConnected p) {z : T ⟶ pullback p g}
    (hz : z ≫ pullback.snd p g = 𝟙 T) (U : T.Opens)
    {u v : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ}
    (huv : u * v⁻¹ ∈ kUnits g hz U) : u = v := by
  have h1 := eq_one_of_mem_kUnits g hp hz U huv
  calc u = u * v⁻¹ * v := by rw [inv_mul_cancel_right]
    _ = 1 * v := by rw [h1]
    _ = v := one_mul v

end ModularCurves
