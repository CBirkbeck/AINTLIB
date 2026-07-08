import Mathlib

open CategoryTheory Abelian Limits ModuleCat
open scoped ModuleCat.Algebra

universe u

namespace ModuleCat.BaseChangeExt

variable {S : Type u} [CommRing S] (𝔪 : Submonoid S)

/-! ### The localization functor is `S`-linear -/

/-- The localization functor `ModuleCat S ⥤ ModuleCat (Localization 𝔪)` is `S`-linear. -/
instance functorLinear : (ModuleCat.localizedModuleFunctor.{u} 𝔪).Linear S where
  map_smul {M N} f s := by
    apply ModuleCat.hom_ext
    rw [show s • (ModuleCat.localizedModuleFunctor.{u} 𝔪).map f
        = (algebraMap S (Localization 𝔪) s) • (ModuleCat.localizedModuleFunctor.{u} 𝔪).map f
        from ModuleCat.hom_ext rfl, ModuleCat.hom_smul,
      show ModuleCat.Hom.hom ((ModuleCat.localizedModuleFunctor.{u} 𝔪).map (s • f))
        = IsLocalizedModule.mapExtendScalars 𝔪 (M.localizedModuleMkLinearMap 𝔪)
          (N.localizedModuleMkLinearMap 𝔪) (Localization 𝔪) (s • f.hom) from rfl,
      map_smul, ← IsScalarTower.algebraMap_smul (Localization 𝔪) s]
    rfl

/-! ### Transport of `Ext` along isomorphisms in both variables -/

/-- An isomorphism in each variable induces an equivalence of `Ext` groups. -/
noncomputable def extEquivOfIso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃ Ext X' Y' n where
  toFun f := (Ext.mk₀ eX.inv).comp (f.comp (Ext.mk₀ eY.hom) (add_zero n)) (zero_add n)
  invFun g := (Ext.mk₀ eX.hom).comp (g.comp (Ext.mk₀ eY.inv) (add_zero n)) (zero_add n)
  left_inv f := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
      Ext.mk₀_id_comp, Ext.comp_mk₀_id]
  right_inv g := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id,
      Ext.mk₀_id_comp, Ext.comp_mk₀_id]

/-! ### Object isomorphisms: localizing `S` and `S ⧸ I` -/

/-- `LocalizedModule 𝔪 S` is `Localization 𝔪` as a `Localization 𝔪`-module. -/
noncomputable def ringLocEquiv : LocalizedModule 𝔪 S ≃ₗ[Localization 𝔪] Localization 𝔪 :=
  LinearEquiv.extendScalarsOfIsLocalization 𝔪 (Localization 𝔪)
    (IsLocalizedModule.iso 𝔪 (Algebra.linearMap S (Localization 𝔪)))

/-- The localization of `S` (as an object of `ModuleCat`) is `Localization 𝔪`. -/
noncomputable def ringObjIso :
    (ModuleCat.localizedModuleFunctor.{u} 𝔪).obj (ModuleCat.of S S)
      ≅ ModuleCat.of (Localization 𝔪) (Localization 𝔪) :=
  ((Shrink.linearEquiv (Localization 𝔪) (LocalizedModule 𝔪 S)).trans (ringLocEquiv 𝔪)).toModuleIso

/-- `ringLocEquiv` sends `mkLinearMap x` to `algebraMap x`. -/
lemma ringLocEquiv_mkLinearMap (x : S) :
    (ringLocEquiv 𝔪) (LocalizedModule.mkLinearMap 𝔪 S x)
      = algebraMap S (Localization 𝔪) x := by
  rw [LocalizedModule.mkLinearMap_apply, ringLocEquiv]
  simp [IsLocalizedModule.iso_mk_one]

/-- Under `ringLocEquiv`, the localized submodule `I.localized 𝔪` corresponds to the extended
ideal `I.map (algebraMap S (Localization 𝔪))`. -/
lemma hmap (I : Ideal S) :
    Submodule.map (ringLocEquiv 𝔪).toLinearMap (I.localized 𝔪)
      = I.map (algebraMap S (Localization 𝔪)) := by
  rw [Submodule.localized, Submodule.localized'_eq_span, Submodule.map_span,
    ← Set.image_comp, Ideal.map, ← Ideal.submodule_span_eq]
  congr 1
  ext y
  simp only [Set.mem_image, Function.comp_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (ringLocEquiv_mkLinearMap 𝔪 x).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, ringLocEquiv_mkLinearMap 𝔪 x⟩

/-- The localization of `S ⧸ I` is `Localization 𝔪 ⧸ I.map (algebraMap …)`.
This is base change of a quotient module along the flat map `S → Localization 𝔪`. -/
noncomputable def quotObjIso (I : Ideal S) :
    (ModuleCat.localizedModuleFunctor.{u} 𝔪).obj (ModuleCat.of S (S ⧸ I))
      ≅ ModuleCat.of (Localization 𝔪)
        (Localization 𝔪 ⧸ I.map (algebraMap S (Localization 𝔪))) :=
  (((Shrink.linearEquiv (Localization 𝔪) (LocalizedModule 𝔪 (S ⧸ I))).trans
    ((LinearEquiv.extendScalarsOfIsLocalization 𝔪 (Localization 𝔪)
      (IsLocalizedModule.iso 𝔪 (I.toLocalizedQuotient 𝔪))).trans
      (Submodule.Quotient.equiv (I.localized 𝔪)
        (I.map (algebraMap S (Localization 𝔪))) (ringLocEquiv 𝔪) (hmap 𝔪 I))))).toModuleIso

/-! ### Flat base change for `Ext` (the analytic core) -/

/-- **Flat base change for Ext.** For a finite module `X` over a Noetherian ring `S`, the
comparison map from `Ext_S(X, Y)` to `Ext_L(X_𝔪, Y_𝔪)` (`L = Localization 𝔪`) exhibits the
latter as the localization of the former at `𝔪`.

This is the sole remaining `sorry` in this file; everything downstream
(`localizedModule_ext_subsingleton_iff`) is proved from it. It is a genuine, mathlib-absent,
PR-scale result. Proof strategy (mirrors `Functor.mapExt_bijective_of_preservesProjectiveObjects`
in `Mathlib/.../Ext/MapBijective.lean`, replacing "bijective for a fully faithful functor" by
"`IsLocalizedModule` for the localization functor"):

* **Induction on `n`, generalizing `X`.**
* **Base case `n = 0`.** Via `Ext.mapExactFunctor₀`, `F.mapExtLinearMap S X Y 0` is conjugate,
  by the `Ext.linearEquiv₀` isomorphisms `Ext _ _ 0 ≃ₗ (· ⟶ ·)`, to `F.mapLinearMap S` on the
  Hom-modules, which in turn is conjugate (by `ModuleCat.homLinearEquiv`) to
  `IsLocalizedModule.mapExtendScalars 𝔪 (X.localizedModuleMkLinearMap 𝔪) (Y.localizedModuleMkLinearMap 𝔪) L`.
  That map is `IsLocalizedModule 𝔪` by `Module.FinitePresentation.isLocalizedModule_mapExtendScalars`
  (using `Module.finitePresentation_of_finite` since `S` is Noetherian and `X` is finite).
  `IsLocalizedModule.comp_iff_of_bijective_left/right` strip the equivalences. (The remaining
  obstruction here is purely a defeq clash between two provably-equal `Module S`-structures on the
  `L`-linear Hom-space — the `LocalizedModule` one vs. the `ModuleCat.Algebra` one — which must be
  bridged via `LinearMap.ext`/`IsLocalizedModule.ext` rather than `∘ₗ`.)
* **Inductive step.** Take a projective presentation `0 → K → P → X → 0` with `P` projective and
  `K`, `P` finite (`Module.exists_finite_presentation`; the syzygy `K` is finite over Noetherian `S`).
  `F` preserves projectives (`localizedModuleFunctor.PreservesProjectiveObjects`) and exactness
  (`localizedModuleFunctor_map_exact`), and `Ext^{≥1}(projective, _) = 0`
  (`Ext.subsingleton_of_projective`). Localize the contravariant Ext long exact sequence
  (`Ext.contravariant_sequence_exact₁'/₃`) for the SES — localization is exact
  (`IsLocalizedModule.map_exact`) — and apply the five lemma
  (`LinearMap.bijective_of_surjective_of_bijective_of_right_exact`) to the comparison ladder, whose
  neighbouring rungs are `IsLocalizedModule` by the induction hypothesis at degree `n` for the
  finite modules `K` and `P`. Naturality of the comparison (the commuting squares) comes from
  `Ext.mapExactFunctor_comp` and `Ext.mapExactFunctor_extClass`. -/
lemma isLocalizedModule_mapExt [IsNoetherianRing S] (X Y : ModuleCat.{u} S)
    [Module.Finite S X] (n : ℕ) :
    IsLocalizedModule 𝔪
      ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S X Y n) :=
  sorry

end ModuleCat.BaseChangeExt

open ModuleCat.BaseChangeExt in
/-- Flat base change for Ext: localizing the Ext module commutes with computing Ext over the
localization. -/
theorem localizedModule_ext_subsingleton_iff {S : Type u} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) (q : PrimeSpectrum S) (i : ℕ) :
    Subsingleton (LocalizedModule q.asIdeal.primeCompl
        (Ext (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i))
      ↔ Subsingleton (Ext
          (ModuleCat.of (Localization q.asIdeal.primeCompl)
            (Localization q.asIdeal.primeCompl ⧸ I.map (algebraMap S (Localization q.asIdeal.primeCompl))))
          (ModuleCat.of (Localization q.asIdeal.primeCompl) (Localization q.asIdeal.primeCompl)) i) := by
  set 𝔪 := q.asIdeal.primeCompl with h𝔪
  haveI : IsLocalizedModule 𝔪
      ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S
        (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i) :=
    isLocalizedModule_mapExt 𝔪 _ _ i
  -- localization of the Ext module identifies with Ext over the localization
  let e1 := IsLocalizedModule.iso 𝔪
    ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S
      (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i)
  -- transport Ext along the object isomorphisms
  let e2 := extEquivOfIso (quotObjIso 𝔪 I) (ringObjIso 𝔪) i
  exact Equiv.subsingleton_congr (e1.toEquiv.trans e2)
