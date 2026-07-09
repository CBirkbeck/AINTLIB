/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import ModularCurves.ForMathlib.SheafOfModulesMonoidal
import ModularCurves.Picard.InvertibleSheaf

/-!
# Strong monoidality of the sheaf-of-modules pullback — decomposition skeleton

`/develop --decompose` skeleton for the AINTLIB ModularCurves stream leaf **[PIC-P1b-MONO]**
(board v10.77): the strong monoidality of the sheaf-of-modules pullback,
`f^*(M ⊗ N) ≅ f^* M ⊗ f^* N`, which gates `nonempty_pullback_tensorObj` in
`ModularCurves/Picard/InvertibleSheaf.lean` (and, downstream, the whole Pic group law).

**Route D (direct)** — chosen adversarially over route M (mates on a `SheafOfModules`
monoidal category, which is *out*: mathlib has no `SheafOfModules/Monoidal.lean`; the
sheaf-level tensor `tensorObj := sheafify(M.val ⊗ N.val)` is this project's own
construction, so there is no `MonoidalCategory (SheafOfModules R)` for
`leftAdjointOplaxMonoidal` to consume without first building the entire group-law layer
this leaf gates). Route D assembles, at the sheaf level:

* `SheafOfModules.sheafificationCompPullback` (mathlib): `sh_S ⋙ f^* ≅ f^*ᵖ ⋙ sh_R`,
  applied at `M.val ⊗ N.val`, gives `f^*(M ⊗ N) ≅ sh_R(f^*ᵖ(M.val ⊗ N.val))`.
* `SheafOfModules.pullbackIso` (mathlib): `f^* ≅ forget ⋙ f^*ᵖ ⋙ sh_R`, giving
  `(f^* M).val ≅ (sh_R(f^*ᵖ M.val)).val`, so
  `f^* M ⊗ f^* N ≅ sh_R((sh_R(f^*ᵖ M.val)).val ⊗ (sh_R(f^*ᵖ N.val)).val)`.
* `nonempty_sheafify_tensor_idem` below (**this project's GAP1-W-MONO leaf**): collapses
  the double sheafification, `sh_R(sh_R(A).val ⊗ sh_R(B).val) ≅ sh_R(A ⊗ B)`.
* `nonempty_sheafify_presheafPullback_tensor` below (**the one genuinely new leaf, D-PresPB′**):
  `sh_R(f^*ᵖ(P ⊗ Q)) ≅ sh_R(f^*ᵖ P ⊗ f^*ᵖ Q)` — the presheaf pullback commutes with the
  tensor *after sheafification*. NOTE (adversarial): the presheaf pullback is **not** strong
  monoidal for general `f` at the presheaf level (`pullback φ := (pushforward φ).leftAdjoint`
  hides an inverse-image left-Kan-extension along the site functor, which does not commute
  with the presheaf tensor); the comparison map is only a *stalkwise* iso, hence *locally
  bijective*, hence inverted by `sh_R`. So the sheafified form here is the correct true
  statement, provable by the same `sheafificationW`-membership technology as D-Idem.

Both new leaves stated `sorry` (skeleton only — no tickets; see
`.mathlib-quality/decomposition-pullback-monoidal.md`). The top assembly target
`nonempty_pullback_tensorObj` already lives (sorried) in `Picard/InvertibleSheaf.lean`.
-/

universe u

open CategoryTheory MonoidalCategory Functor

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

/-- **[PIC-P1b-MONO], leaf D-Idem — this project's GAP1-W-MONO, repackaged.**
The presheaf sheafification is strong monoidal for the presheaf tensor: the canonical map
`sh(A ⊗ B) → sh(sh(A).val ⊗ sh(B).val)` induced by the sheafification units is an iso.
Proved from `sheafificationW_tensorHom` (the GAP1-W-MONO leaf: the tensor of two
locally-bijective maps is locally bijective) applied to the two unit maps `η_A, η_B`
(each in `sheafificationW`, since `sh.map η` is inverse to the iso counit by the triangle
identity), then "`sh` inverts `sheafificationW`". Stated over a sheaf of commutative rings
`⟨S ⋙ forget₂, hS⟩` (the reflective `α = 𝟙` setting where the localization machinery
resolves, mirroring `SheafOfModulesMonoidal`'s instantiation) and `Nonempty`-wrapped. -/
theorem nonempty_sheafify_tensor_idem
    (A B : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    Nonempty
      ((sheafification (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj
          (A ⊗ B) ≅
        (sheafification (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj
          (((sheafification
                (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj A).val ⊗
            ((sheafification
                (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).obj B).val)) := by
  -- PARKED (v10.79, coordinator refocus to Y1). Proof plan is sound and mostly assembled; the
  -- residual is pure v10.36 instance-clothing plumbing (banked for resume):
  --   * hunit := ⟨η_A, η_B⟩ ∈ sheafificationW via either
  --       (a) counit route: `isIso_of_comp_hom_eq_id _ (sheafificationAdjunction _).left_triangle_components`
  --           — needs `IsIso (sheafificationAdjunction (𝟙 R'.obj)).counit`, which fails to synthesize
  --           because R cannot be inferred from `𝟙 R'.obj` (`set R'` hides the `⟨_,hS⟩` head; spell it
  --           literally per the SheafOfModulesMonoidal Instantiation antidote), or
  --       (b) toSheafify route: `sheafificationW_iff_isLocallyBijective` +
  --           `toPresheaf_map_sheafificationAdjunction_unit_app` reduces to
  --           `IsLocallyInjective/Surjective J (toSheafify J M.presheaf)` — needs
  --           `[J.HasSheafCompose (forget AddCommGrpCat)]` + `[J.PreservesSheafification (forget AddCommGrpCat)]`
  --           in the variable block (add them; the scheme site supplies them).
  --   * then `sheafificationW_tensorHom (𝟙 R'.obj) η_A η_B (hunit A) (hunit B)` (α=𝟙 loc-bij of the
  --     identity resolves cleanly here via `[IsIso (𝟙 _)]`), `rw [sheafificationW_iff] at ·`, `asIso`.
  -- The α=𝟙 loc-inj/surj and the sheafificationW R-inference already work in this abstract setting
  -- (only the counit / toSheafify anchors above remain). Resume: pick route (a) with literal `⟨_,hS⟩`.
  sorry

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **[PIC-P1b-MONO], leaf D-PresPB′ — the one genuinely new leaf (refined, general `f`).**
The presheaf pullback commutes with the presheaf tensor *after sheafification*:
`sh_Y(f^*ᵖ(P ⊗ Q)) ≅ sh_Y(f^*ᵖ P ⊗ f^*ᵖ Q)`, where `f^*ᵖ := PresheafOfModules.pullback
f.toRingCatSheafHom.hom`. The un-sheafified comparison `f^*ᵖ(P⊗Q) → f^*ᵖP ⊗ f^*ᵖQ` (the
oplax structure map of the pullback, whose lax partner comes from `restrictScalars`) is a
*stalkwise* isomorphism — the stalk of an inverse image is the stalk at the image point and
tensor commutes with stalks — hence locally bijective, hence inverted by `sh_Y`. This is the
step that would be *false* if stated at the presheaf level for general `f`. `Nonempty`-wrapped. -/
theorem nonempty_sheafify_presheafPullback_tensor (f : Y ⟶ X) (P Q : X.PresheafOfModules) :
    Nonempty ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj (P ⊗ Q)) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj P ⊗
          (PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj Q)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
