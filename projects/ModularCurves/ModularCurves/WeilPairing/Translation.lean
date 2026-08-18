/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TranslationBySection
import ModularCurves.WeilPairing.KMUniqueness

/-!
# Translation by a torsion section, and translation invariance of the splitting units

Infrastructure for `AP-D7`'s bilinearity in the *first* variable
(`torsionSplittingEval_add`, `WeilPairing/KMBilinear.lean`). Katz–Mazur p. 89 gets
`h(P + P') = h(P)·h(P')` from **translation invariance**: for an `N`-torsion `P'` the translation
`τ_{P'}` fixes `[N]` and therefore each open `[N]⁻¹(W i)`, so `τ_{P'}^# h_i` is again a splitting
of the same cocycle, differing from `h_i` by the pullback of one global unit of the base — and
that unit is `h(P')`. Evaluating at `P` then reads off `h(P + P') = h(P)·h(P')`.

## The three things this file supplies

* **`unitPullback`** — pulling a unit section back along `f : X ⟶ Y` between opens related only by
  an inequality `V ≤ f ⁻¹ᵁ U`, i.e. `Units.map` of `Scheme.Hom.appLE`. This is the device that
  removes the dependent-open transport the sketch feared: the transported open
  `τ ⁻¹ᵁ ([N]⁻¹ W i) = [N]⁻¹(W i)` holds only propositionally, but `appLE` absorbs the comparison
  into a `Prop` argument, so `unitPullback_congr` (a `subst` on the morphism equation followed by
  proof irrelevance) replaces every dependent rewrite. `globalTwist`
  (`WeilPairing/KMNormalisation.lean`) is the special case `f = π`, `U = ⊤`, and `sectionEval` is
  the special case `V = f ⁻¹ᵁ U` (`sectionEval_eq_unitPullback`).

* **`translateByPoint`** — the transport of `EllipticCurve.translateBy`
  (`GroupScheme/TranslationBySection.lean`, an automorphism of `E.asOver` in `Over S` clothing) to
  the `pullback E.π t` presentation of the base-changed curve, exactly as `mulByN`
  (`Picard/SelfAdjointN.lean`) transports `[N]`; the two presentations are definitionally equal but
  the statements below need them *syntactically* equal. Its three specs are
  `translateByPoint_comp_snd` (it is a morphism over `T`), `comp_translateByPoint`
  (`Q ↦ Q + P` on points, KM's `Trans(P)`) and `translateByPoint_comp_mulByN`
  (`τ_P ≫ [N] = [N]` for `N`-torsion `P`, from `[N] = 𝟙^N` in the hom-group and `constPt` being a
  monoid map).

* **`eq_mul_globalTwist_of_translate`** — the translation invariance itself, on an arbitrary
  universally `O`-connected family: if `τ` fixes each `V i` and each transition unit `F i j`, and
  if the zero-section value of `τ^# h_i` is one global unit `C`, then `τ^# h_i = h_i · π^# C`.
  Proved by feeding `τ^# h_i · (π^# C)⁻¹` — a *normalised* splitting of the same cocycle — to
  `eq_of_normalized_splitting` (`WeilPairing/KMUniqueness.lean`).

Nothing here uses `exists_torsionPoint_of_mem_kerMulByN` (`WeilPairing/KMPairing.lean`), so no
declaration below inherits that `sorryAx`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ModularCurves

/-! ## Pulling units back along `appLE` -/

section UnitPullback

variable {X Y T : Scheme.{u}}

/-- **Pullback of a unit section along `f`**, between opens related only by `V ≤ f ⁻¹ᵁ U`.

Phrasing the pullback through `Scheme.Hom.appLE` rather than `Scheme.Hom.app` is what keeps every
statement below free of dependent transports: the comparison of `V` with `f ⁻¹ᵁ U` sits in a `Prop`
argument, so two pullbacks along *equal* morphisms are equal by `subst` and proof irrelevance
(`unitPullback_congr`), no matter how the two `≤` proofs were produced. -/
noncomputable def unitPullback (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Γ(Y, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (f.appLE U V h).hom.toMonoidHom

/-- **The transport device.** Pullback along equal morphisms agrees — the inequality proofs need
not, and cannot, match, because they are produced from different data. This is what replaces the
dependent rewrite `Γ(Y, τ ⁻¹ᵁ V) = Γ(Y, V)` along `τ ≫ [N] = [N]`. -/
theorem unitPullback_congr {f f' : X ⟶ Y} (hf : f = f') (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ f' ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) :
    unitPullback f U V h a = unitPullback f' U V h' a := by
  subst hf; rfl

/-- Restricting a pulled-back unit is pulling it back to the smaller open. -/
theorem resUnit_unitPullback (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : V' ≤ V) (a : Γ(Y, U)ˣ) :
    Scheme.resUnit h' (unitPullback f U V h a) = unitPullback f U V' (h'.trans h) a :=
  Scheme.resUnit_map_appLE f h h' a

/-- Pulling back a restricted unit is pulling back from the larger open. -/
theorem unitPullback_resUnit (f : X ⟶ Y) {U U' : Y.Opens} (hU : U ≤ U') {V : X.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (a : Γ(Y, U')ˣ) :
    unitPullback f U V h (Scheme.resUnit hU a) =
      unitPullback f U' V (h.trans (f.preimage_mono hU)) a :=
  Scheme.map_appLE_resUnit f hU h a

/-- Pullbacks compose (`Scheme.Hom.appLE_comp_appLE` on units). -/
theorem unitPullback_unitPullback {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens}
    {V : Y.Opens} {V' : X.Opens} (h : V ≤ g ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ V) (a : Γ(Z, U)ˣ) :
    unitPullback f V V' h' (unitPullback g U V h a) =
      unitPullback (f ≫ g) U V' (h'.trans (f.preimage_mono h)) a := by
  apply Units.ext
  show (f.appLE V V' h').hom ((g.appLE U V h).hom (a : Γ(Z, U))) = _
  rw [show (f.appLE V V' h').hom ((g.appLE U V h).hom (a : Γ(Z, U))) =
      (g.appLE U V h ≫ f.appLE V V' h').hom (a : Γ(Z, U)) from rfl,
    Scheme.Hom.appLE_comp_appLE]
  rfl

/-- The pullback of a unit along a morphism, in the `Scheme.Hom.app` form used by the `AP-D5`
statements, is `unitPullback` at the full preimage. -/
theorem map_app_eq_unitPullback (f : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)ˣ) :
    Units.map (f.app U).hom.toMonoidHom a = unitPullback f U (f ⁻¹ᵁ U) le_rfl a := by
  apply Units.ext
  show (f.app U).hom (a : Γ(Y, U)) = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (a : Γ(Y, U))
  rw [Scheme.Hom.appLE_eq_app]

/-- Zero-section evaluation is `unitPullback` along the section, at the full preimage. -/
theorem sectionEval_eq_unitPullback (w : T ⟶ Y) (V : Y.Opens) (a : Γ(Y, V)ˣ) :
    sectionEval w V a = unitPullback w V (w ⁻¹ᵁ V) le_rfl a :=
  map_app_eq_unitPullback w V a

/-- **(KM p. 89, `(f ∘ π) ∘ P = f ∘ (πP)` on general opens)** Evaluating an `f`-pullback along a
section `w` is evaluating along the composite `w ≫ f`, restricted to `w ⁻¹ᵁ V`. The `appLE`
version of `sectionEval_pullback` (`WeilPairing/KMPatching.lean`): here `V` need not be all of
`f ⁻¹ᵁ U`, so a restriction appears. -/
theorem sectionEval_unitPullback (f : X ⟶ Y) (w : T ⟶ X) {U : Y.Opens} {V : X.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) :
    sectionEval w V (unitPullback f U V h a) =
      Scheme.resUnit (show w ⁻¹ᵁ V ≤ (w ≫ f) ⁻¹ᵁ U from w.preimage_mono h)
        (sectionEval (w ≫ f) U a) := by
  rw [sectionEval_eq_unitPullback, sectionEval_eq_unitPullback, unitPullback_unitPullback,
    resUnit_unitPullback]

/-- Evaluation along *equal* sections agrees, after restriction to a common open. The companion of
`unitPullback_congr` for the section variable: `sectionEval w V` lands on `w ⁻¹ᵁ V`, so replacing
`w` is a dependent rewrite; restricting both sides to one open of the base turns the comparison
into a `Prop` and `subst` closes it. -/
theorem resUnit_sectionEval_congr {w w' : T ⟶ Y} (hw : w = w') (V : Y.Opens) (a : Γ(Y, V)ˣ)
    {U : T.Opens} (hU : U ≤ w ⁻¹ᵁ V) (hU' : U ≤ w' ⁻¹ᵁ V) :
    Scheme.resUnit hU (sectionEval w V a) = Scheme.resUnit hU' (sectionEval w' V a) := by
  subst hw; rfl

end UnitPullback

/-! ## Translation by a section, in the `pullback E.π t` presentation -/

section Translate

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} (t : T ⟶ S)

/-- A section of the base-changed curve, as a point of the group object `E_T` of `Over T`.
`𝟙_ (Over T)` is `Over.mk (𝟙 T)` on the nose, so this is `pointEquivOverHom` with no transport. -/
noncomputable def overPoint (P : (E.baseChange t).Point (𝟙 T)) :
    𝟙_ (Over T) ⟶ (E.baseChange t).asOver :=
  (E.baseChange t).pointEquivOverHom (𝟙 T) P

/-- **Translation by a section, in the `pullback E.π t` presentation.** `τ_P = 𝟙 + P ∘ π`, the
`.left` of `EllipticCurve.translateBy` on the base-changed curve.

Presented on `pullback E.π t` rather than on `(E.baseChange t).E` for the same reason as `mulByN`
(`Picard/SelfAdjointN.lean`): the two are definitionally equal, but every statement pairing `τ_P`
with `mulByN` or with an open of `pullback E.π t` needs them *syntactically* equal. -/
noncomputable def translateByPoint (P : (E.baseChange t).Point (𝟙 T)) :
    pullback E.π t ⟶ pullback E.π t :=
  ((E.baseChange t).translateBy (overPoint E t P)).left

/-- Translation is a morphism over the base: it commutes with the structure map. -/
theorem translateByPoint_comp_snd (P : (E.baseChange t).Point (𝟙 T)) :
    translateByPoint E t P ≫ pullback.snd E.π t = pullback.snd E.π t :=
  Over.w ((E.baseChange t).translateBy (overPoint E t P))

/-- Translation on `Over T`-points: `Q ↦ Q + P`. The constant map absorbs the precomposition
(`𝟙_ (Over T)` is terminal), so `Q ≫ (𝟙 · const P) = Q · P`. -/
theorem overPoint_comp_translateBy (P Q : (E.baseChange t).Point (𝟙 T)) :
    overPoint E t Q ≫ (E.baseChange t).translateBy (overPoint E t P) = overPoint E t (Q + P) := by
  letI : CommGroup ((E.baseChange t).asOver ⟶ (E.baseChange t).asOver) := Hom.commGroup
  letI : CommGroup (Over.mk (𝟙 T) ⟶ (E.baseChange t).asOver) := Hom.commGroup
  have h1 : overPoint E t Q ≫ toUnit (E.baseChange t).asOver = 𝟙 (𝟙_ (Over T)) :=
    CartesianMonoidalCategory.toUnit_unique _ _
  have h2 : overPoint E t Q ≫ (E.baseChange t).constPt (overPoint E t P) = overPoint E t P := by
    rw [EllipticCurve.constPt, ← Category.assoc, h1]
    exact Category.id_comp _
  rw [EllipticCurve.translateBy_def, MonObj.comp_mul, Category.comp_id, h2]
  exact ((E.baseChange t).pointEquivOverHom_add (𝟙 T) Q P).symm

/-- **(KM's `Trans(P)` on points)** Composing a section with translation by `P` adds `P`:
`Q ≫ τ_P = Q + P`, as morphisms `T ⟶ E ×_S T`. -/
theorem comp_translateByPoint (P Q : (E.baseChange t).Point (𝟙 T)) :
    (Q.1 : T ⟶ pullback E.π t) ≫ translateByPoint E t P =
      ((Q + P : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t) :=
  (Over.comp_left _ _ _ _ _).symm.trans
    (congrArg CommaMorphism.left (overPoint_comp_translateBy E t P Q))

/-- The `Over T` form of `τ_P ≫ [N] = [N]`: in the hom-group `Hom(E_T, E_T)` one has
`f ≫ 𝟙^N = f^N`, and `τ_P^N = 𝟙^N · const(P)^N = [N]` because `N • P = 0` and `constPt` is a
monoid map (`GrpObj.comp_zpow` + `MonObj.comp_one`). -/
theorem translateBy_comp_mulBy (P : (E.baseChange t).Point (𝟙 T)) (N : ℕ)
    (hP : P ∈ torsionPoints E t N) :
    (E.baseChange t).translateBy (overPoint E t P) ≫ (E.baseChange t).mulBy (N : ℤ) =
      (E.baseChange t).mulBy (N : ℤ) := by
  letI : CommGroup ((E.baseChange t).asOver ⟶ (E.baseChange t).asOver) := Hom.commGroup
  letI : CommGroup (𝟙_ (Over T) ⟶ (E.baseChange t).asOver) := Hom.commGroup
  have hzpow : overPoint E t ((N : ℤ) • P) = (overPoint E t P) ^ (N : ℤ) := rfl
  have hx : (overPoint E t P) ^ (N : ℤ) = 1 := by
    rw [← hzpow, show ((N : ℤ) • P) = 0 from hP]
    rfl
  have hconst : ((E.baseChange t).constPt (overPoint E t P)) ^ (N : ℤ) = 1 := by
    rw [EllipticCurve.constPt, ← GrpObj.comp_zpow, hx, MonObj.comp_one]
  calc (E.baseChange t).translateBy (overPoint E t P) ≫ (E.baseChange t).mulBy (N : ℤ)
      = ((E.baseChange t).translateBy (overPoint E t P) ≫ 𝟙 _) ^ (N : ℤ) := by
        rw [EllipticCurve.mulBy, GrpObj.comp_zpow]
    _ = ((E.baseChange t).translateBy (overPoint E t P)) ^ (N : ℤ) := by rw [Category.comp_id]
    _ = (𝟙 (E.baseChange t).asOver) ^ (N : ℤ) *
          ((E.baseChange t).constPt (overPoint E t P)) ^ (N : ℤ) := by
        rw [EllipticCurve.translateBy_def, mul_zpow]
    _ = (E.baseChange t).mulBy (N : ℤ) := by rw [hconst]; exact _root_.mul_one _

/-- **Translation by an `N`-torsion section commutes past `[N]`**: `τ_P ≫ [N] = [N]`, because
`[N] ∘ τ_P = 𝟙 + (N • P) ∘ π` and `N • P = 0`. This is what makes `τ_P` preserve every open
`[N]⁻¹(W)`. -/
theorem translateByPoint_comp_mulByN (P : (E.baseChange t).Point (𝟙 T)) (N : ℕ)
    (hP : P ∈ torsionPoints E t N) :
    translateByPoint E t P ≫ mulByN E t N = mulByN E t N :=
  (Over.comp_left _ _ _ _ _).symm.trans
    (congrArg CommaMorphism.left (translateBy_comp_mulBy E t P N hP))

/-- The opens `[N]⁻¹(W)` are **fixed** by translation by an `N`-torsion section. An equality of
opens, hence usable as a `≤` in either direction; that is exactly what lets `unitPullback` carry
`h_i` back to its own open. -/
theorem preimage_translateByPoint_mulByN (P : (E.baseChange t).Point (𝟙 T)) (N : ℕ)
    (hP : P ∈ torsionPoints E t N) (V : (pullback E.π t).Opens) :
    translateByPoint E t P ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ V) = mulByN E t N ⁻¹ᵁ V :=
  (Scheme.Hom.comp_preimage _ _ _).symm.trans
    (congrArg (· ⁻¹ᵁ V) (translateByPoint_comp_mulByN E t P N hP))

end Translate

/-! ## Translation invariance of a normalised splitting -/

/-- Twisting numerator and denominator by the same unit leaves the ratio unchanged. Stated over
abstract elements so the normalisation runs on atoms rather than on section terms. -/
private theorem mul_inv_twist {G : Type*} [Group G] (a b w : G) :
    a * b⁻¹ = a * w⁻¹ * (b * w⁻¹)⁻¹ := by
  rw [mul_inv_rev, inv_inv, _root_.mul_assoc, ← _root_.mul_assoc w⁻¹ w, inv_mul_cancel, one_mul]

section Invariance

variable {X S T : Scheme.{u}} {p : X ⟶ S} (g : T ⟶ S) (hp : UniversallyOConnected p)
variable {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)
variable {ι : Type*} (V : ι → (pullback p g).Opens) (hV : iSup V = ⊤)
variable {F : ∀ i j, Γ(pullback p g, V i ⊓ V j)ˣ} {h : ∀ i, Γ(pullback p g, V i)ˣ}

include hp hz hV in
/-- **(KM p. 89, translation invariance)** Let `h` be a normalised splitting of a cocycle `F` over
a cover `V` of the curve, and let `τ` be an endomorphism fixing every `V i` and every `F i j`. If
the zero-section value of `τ^# h_i` is the restriction of *one* global unit `C` of the base — the
same `C` for all `i` — then

  `τ^# h_i = h_i · π^# C`.

Proof: `τ^# h_i · (π^# C)⁻¹` is again a splitting of `F` (the twists cancel in the ratio,
`resUnit_globalTwist`), and it is normalised by hypothesis, so `eq_of_normalized_splitting`
(`WeilPairing/KMUniqueness.lean`) identifies it with `h_i`.

The hypothesis `hC` is where the torsion of the translating section is spent: for `τ = τ_{P'}` the
zero-section value of `τ^# h_i` is `h_i ∘ P'`, and *that* glues to one global unit precisely
because it is `h(P')`. -/
theorem eq_mul_globalTwist_of_translate
    (hn : ∀ i, h i ∈ sectionUnits z (V i))
    (hsplit : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    {τ : pullback p g ⟶ pullback p g}
    (hτle : ∀ i, V i ≤ τ ⁻¹ᵁ V i) (hτinf : ∀ i j, V i ⊓ V j ≤ τ ⁻¹ᵁ (V i ⊓ V j))
    (hτF : ∀ i j, unitPullback τ (V i ⊓ V j) (V i ⊓ V j) (hτinf i j) (F i j) = F i j)
    {C : Γ(T, ⊤)ˣ}
    (hC : ∀ i, sectionEval z (V i) (unitPullback τ (V i) (V i) (hτle i) (h i)) =
      Scheme.resUnit (le_top : z ⁻¹ᵁ V i ≤ ⊤) C) (i : ι) :
    unitPullback τ (V i) (V i) (hτle i) (h i) =
      h i * globalTwist (pullback.snd p g) (V i) C := by
  have hres : ∀ i j, Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i)
      (unitPullback τ (V i) (V i) (hτle i) (h i)) =
      unitPullback τ (V i ⊓ V j) (V i ⊓ V j) (hτinf i j)
        (Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i)) := by
    intro i j
    rw [resUnit_unitPullback, unitPullback_resUnit]
  have hres' : ∀ i j, Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j)
      (unitPullback τ (V j) (V j) (hτle j) (h j)) =
      unitPullback τ (V i ⊓ V j) (V i ⊓ V j) (hτinf i j)
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j)) := by
    intro i j
    rw [resUnit_unitPullback, unitPullback_resUnit]
  have hn' : ∀ i, unitPullback τ (V i) (V i) (hτle i) (h i) *
      (globalTwist (pullback.snd p g) (V i) C)⁻¹ ∈ sectionUnits z (V i) := by
    intro i
    show sectionEval z (V i) _ = 1
    rw [map_mul, map_inv, sectionEval_globalTwist hz, hC i, mul_inv_cancel]
  have hsplit' : ∀ i j, F i j =
      Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i)
          (unitPullback τ (V i) (V i) (hτle i) (h i) *
            (globalTwist (pullback.snd p g) (V i) C)⁻¹) *
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j)
          (unitPullback τ (V j) (V j) (hτle j) (h j) *
            (globalTwist (pullback.snd p g) (V j) C)⁻¹))⁻¹ := by
    intro i j
    have hFAB : F i j = unitPullback τ (V i ⊓ V j) (V i ⊓ V j) (hτinf i j)
          (Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i)) *
        (unitPullback τ (V i ⊓ V j) (V i ⊓ V j) (hτinf i j)
          (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j)))⁻¹ := by
      have hx := hτF i j
      rw [hsplit i j, map_mul, map_inv] at hx
      exact (hsplit i j).trans hx.symm
    rw [map_mul, map_mul, map_inv, map_inv, resUnit_globalTwist, resUnit_globalTwist,
      hres i j, hres' i j, hFAB]
    exact mul_inv_twist _ _ _
  exact mul_inv_eq_iff_eq_mul.mp
    (eq_of_normalized_splitting g hp hz V hV hn hn' hsplit hsplit' i).symm

end Invariance

end ModularCurves
