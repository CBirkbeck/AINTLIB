/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.UnitCocycleSheaf
import ModularCurves.WeilPairing.KMSplitting

/-!
# Normalising the splitting units: `h_i ∈ K_E^×` (ticket AP-D5, the normalisation step)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 88. `WeilPairing/KMSplitting.lean`
produces units `h_i` on the members of a cover with `f_{i,j} ∘ [N] = h_i / h_j`
(`exists_pullback_transitionUnit_eq_mul_inv`); KM then *normalises* them, i.e. replaces them by
units taking the value `1` along the zero section — sections of `K_E^×` (`AP-D1`,
`WeilPairing/UnitSheaf.lean`) — which is what makes the pairing value `h_i ∘ T_P / h_i` canonical.

The argument, and why the twist must be **global on the base**: the `h_i` live on the opens
`V i = [N]⁻¹(U_i)` of the *curve*, for an arbitrary cover `{U_i}` of the curve — not on preimages
of base opens, since `κ(Q) = 𝒪(D_Q − D_0)` is fibrewise nontrivial and therefore is *not*
trivialised over the preimage of any base open. So the zero-section value of `h_i` is a unit on
`z⁻¹(V i) ⊆ S`, and these opens vary with `i`. One cannot rescale `h_i` by its own zero-section
value: that value is defined on a base open unrelated to `V i`. Instead:

1. the values agree on overlaps (`sectionEval_eq_of_mem_sectionUnits`), because the cocycle is
   normalised and `kUnitsEval`/`sectionEval` is a group homomorphism;
2. they therefore **glue to one global unit** `C ∈ Γ(S, 𝒪_S^×)` (`exists_globalUnit_restrict`) —
   the only step with content, and the one the tree did not package;
3. twisting each `h_i` by the pullback `π^# C`, which is defined on *all* of the curve, both
   normalises them and leaves every ratio `h_i / h_j` unchanged
   (`exists_normalized_splitting`).

## Main results

* `sectionEval`, `sectionUnits` — KM's `K_E^×` read on an arbitrary open `V` of the total space:
  the zero-section evaluation `Γ(Y, V)ˣ →* Γ(T, z ⁻¹ᵁ V)ˣ` and its kernel. For `V` the preimage
  of a base open this is the tree's `kUnitsEval`/`kUnits` (`AP-D1`), by
  `kUnitsEval_eq_resUnit_sectionEval` and `mem_kUnits_of_mem_sectionUnits`.
* `exists_globalUnit_restrict` — **units glue**: a family of units on an open cover agreeing on
  overlaps is the restriction of a single global unit. Proved from the sheaf axiom for `𝒪` alone
  (glue the value and the inverse, then `s · s' = 1` by separatedness), with no germs, no
  affineness and no local-ring input.
* `sectionEval_eq_of_mem_sectionUnits` — step 1: a normalised transition unit forces the
  zero-section values of the two splitting units to agree on the overlap.
* `globalTwist`, `sectionEval_globalTwist`, `resUnit_globalTwist` — step 3's twist: the pullback
  of a global base unit to an arbitrary open of the curve, its zero-section value, and its
  compatibility with restriction (which is what leaves the ratios untouched).
* `exists_normalized_splitting` — **the ticket**: given the splitting `F_{i,j} = h_i · h_j⁻¹`
  with all `F_{i,j}` normalised, there are normalised `h'_i` splitting the same cocycle.
* `exists_normalized_pullback_transitionUnit_eq_mul_inv` — **AP-D5 assembled**: the above
  composed with `exists_pullback_transitionUnit_eq_mul_inv` (`WeilPairing/KMSplitting.lean`),
  i.e. KM p. 88 in full — `f_{i,j} ∘ [N] = h_i / h_j` with every `h_i` normalised. Its covering
  hypothesis is supplied by `iSup_preimage_preimage_eq_top` from a cover of `X`.
* `eq_of_mem_sectionUnits` — `AP-D2` in this vocabulary: on preimages of base opens a
  normalised unit is unique.

## Reuse

The restriction API on units (`Scheme.resUnit`, `Scheme.resLE`, `resUnit_map_appLE`,
`resLE_appLE`, `appLE_resLE`) is *not* redefined here: it already exists in
`ForMathlib/UnitCocycleSheaf.lean`, whose docstring is about glueing invertible sheaves from
cocycles and so is invisible to a search for normalisation. `Scheme.resUnit h` is a reducible
abbreviation of `Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom`, the shape
`WeilPairing/KMSplitting.lean` states its conclusions in, so the two match on the nose.

## Degenerate cases

Nothing needs the index type to be nonempty or the `V i` themselves to cover the curve: the
hypothesis is only that the *base* opens `z ⁻¹ᵁ (V i)` cover `T`, which is what gluing needs; for
an empty index type it forces `T = ∅` and everything is vacuous.

A warning on the shape of the cover, for consumers of `KMSplitting`/`KMPairing`: the `W i` there
must be a cover of the *curve*. Instantiating them as preimages `π ⁻¹ᵁ (U i)` of a base cover
makes the trivialisation hypothesis `e i` unsatisfiable except in degenerate cases, because
`κ(Q)` restricted to a fibre is trivial only where `Q` meets the zero section; the `h_i` then do
not live over base opens, which is exactly why the normalising constant has to be glued.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ModularCurves

/-! ## `K_E^×` on an arbitrary open of the total space -/

section General

variable {Y T : Scheme.{u}}

/-- **(AP-D1 on an arbitrary open)** Zero-section evaluation of units over an open `V` of the
total space: restriction along the section `z`, landing on the base open `z ⁻¹ᵁ V`. For
`V = f ⁻¹ᵁ U` this is the tree's `kUnitsEval` (`kUnitsEval_eq_resUnit_sectionEval`). -/
noncomputable def sectionEval (z : T ⟶ Y) (V : Y.Opens) : Γ(Y, V)ˣ →* Γ(T, z ⁻¹ᵁ V)ˣ :=
  Units.map (z.app V).hom.toMonoidHom

/-- **(AP-D1 on an arbitrary open)** `K_E^×(V)`: the units on `V` taking the value `1` along the
zero section. -/
noncomputable def sectionUnits (z : T ⟶ Y) (V : Y.Opens) : Subgroup Γ(Y, V)ˣ :=
  (sectionEval z V).ker

theorem mem_sectionUnits_iff (z : T ⟶ Y) (V : Y.Opens) (u : Γ(Y, V)ˣ) :
    u ∈ sectionUnits z V ↔ sectionEval z V u = 1 := Iff.rfl

/-- Restriction of a unit pulled back from another scheme is the pullback of its restriction. -/
theorem resUnit_map_app {Y' Z : Scheme.{u}} (f : Y' ⟶ Z) {U' U : Z.Opens} (hUU : U' ≤ U)
    (a : Γ(Z, U)ˣ) :
    Scheme.resUnit (f.preimage_mono hUU) (Units.map (f.app U).hom.toMonoidHom a) =
      Units.map (f.app U').hom.toMonoidHom (Scheme.resUnit hUU a) := by
  apply Units.ext
  show Scheme.resLE (f.preimage_mono hUU) ((f.app U).hom (a : Γ(Z, U))) =
    (f.app U').hom (Scheme.resLE hUU (a : Γ(Z, U)))
  rw [show f.app U = f.appLE U (f ⁻¹ᵁ U) le_rfl from (Scheme.Hom.appLE_eq_app _).symm,
    show f.app U' = f.appLE U' (f ⁻¹ᵁ U') le_rfl from (Scheme.Hom.appLE_eq_app _).symm,
    Scheme.resLE_appLE, Scheme.appLE_resLE]

/-- Zero-section evaluation commutes with restriction to a smaller open of the total space. -/
theorem sectionEval_resUnit (z : T ⟶ Y) {V' V : Y.Opens} (hVV : V' ≤ V) (u : Γ(Y, V)ˣ) :
    sectionEval z V' (Scheme.resUnit hVV u) =
      Scheme.resUnit (z.preimage_mono hVV) (sectionEval z V u) :=
  (resUnit_map_app z hVV u).symm

/-! ## Units glue -/

/-- **Units glue.** A family of units on an open cover of a scheme agreeing on the overlaps is
the restriction of a single global unit. The value and the inverse are glued separately as
sections of `𝒪`, and separatedness turns their product into `1`; no germs, no affineness. -/
theorem exists_globalUnit_restrict {Z : Scheme.{u}} {ι : Type*} (V : ι → Z.Opens)
    (hV : iSup V = ⊤) (c : ∀ i, Γ(Z, V i)ˣ)
    (hc : ∀ i j, Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (c i) =
      Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (c j)) :
    ∃ C : Γ(Z, ⊤)ˣ, ∀ i, Scheme.resUnit (le_top : V i ≤ ⊤) C = c i := by
  have hcinv : ∀ i j, Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (c i)⁻¹ =
      Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (c j)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hc i j]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf V ⊤
    (fun _ => homOfLE le_top) (by rw [hV]) (fun i => ((c i : Γ(Z, V i))))
    (fun i j => congrArg Units.val (hc i j))
  obtain ⟨s', hs', -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf V ⊤
    (fun _ => homOfLE le_top) (by rw [hV]) (fun i => (((c i)⁻¹ : Γ(Z, V i)ˣ) : Γ(Z, V i)))
    (fun i j => congrArg Units.val (hcinv i j))
  have hmul : ∀ i, (ConcreteCategory.hom (Z.sheaf.obj.map (homOfLE (le_top : V i ≤ ⊤)).op))
      (s * s') =
      (ConcreteCategory.hom (Z.sheaf.obj.map (homOfLE (le_top : V i ≤ ⊤)).op)) 1 := by
    intro i
    rw [map_mul, map_one, hs i, hs' i]
    exact (c i).mul_inv
  have hmul' : ∀ i, (ConcreteCategory.hom (Z.sheaf.obj.map (homOfLE (le_top : V i ≤ ⊤)).op))
      (s' * s) =
      (ConcreteCategory.hom (Z.sheaf.obj.map (homOfLE (le_top : V i ≤ ⊤)).op)) 1 := by
    intro i
    rw [map_mul, map_one, hs i, hs' i]
    exact (c i).inv_mul
  have hss' : s * s' = 1 :=
    TopCat.Sheaf.eq_of_locally_eq' Z.sheaf V ⊤ (fun _ => homOfLE le_top) (by rw [hV]) _ _ hmul
  have hs's : s' * s = 1 :=
    TopCat.Sheaf.eq_of_locally_eq' Z.sheaf V ⊤ (fun _ => homOfLE le_top) (by rw [hV]) _ _ hmul'
  exact ⟨⟨s, s', hss', hs's⟩, fun i => Units.ext (hs i)⟩

/-! ## The twist by a global unit of the base -/

/-- Every open sits in the preimage of the top open; stated as a lemma so that the proof *term*
carries the preimage form, which is what the `appLE` rewrites match on. -/
theorem le_preimage_top (π : Y ⟶ T) (V : Y.Opens) : V ≤ π ⁻¹ᵁ (⊤ : T.Opens) := le_top

/-- The pullback of a global unit of the base to an open `V` of the total space. Being pulled
back from `Γ(T, ⊤)`, it is available on **every** `V` at once — which is exactly why the
normalisation is done by one global constant. -/
noncomputable def globalTwist (π : Y ⟶ T) (V : Y.Opens) (C : Γ(T, ⊤)ˣ) : Γ(Y, V)ˣ :=
  Units.map (π.appLE ⊤ V (le_preimage_top π V)).hom.toMonoidHom C

/-- The twist is compatible with restriction: its restriction to a smaller open is the twist
there. This is what makes twisting leave every ratio `h_i / h_j` unchanged. -/
theorem resUnit_globalTwist (π : Y ⟶ T) {V' V : Y.Opens} (hVV : V' ≤ V) (C : Γ(T, ⊤)ˣ) :
    Scheme.resUnit hVV (globalTwist π V C) = globalTwist π V' C :=
  Scheme.resUnit_map_appLE π (le_preimage_top π V) hVV C

/-- A section reads back what was pulled back along it, on an arbitrary open: the zero-section
value of `π^# C` is `C` restricted to `z ⁻¹ᵁ V`. -/
theorem sectionEval_globalTwist {π : Y ⟶ T} {z : T ⟶ Y} (hz : z ≫ π = 𝟙 T) (V : Y.Opens)
    (C : Γ(T, ⊤)ˣ) :
    sectionEval z V (globalTwist π V C) = Scheme.resUnit (le_top : z ⁻¹ᵁ V ≤ ⊤) C := by
  apply Units.ext
  have hcomp : π.appLE ⊤ V (le_preimage_top π V) ≫ z.app V =
      T.presheaf.map (homOfLE (le_top : z ⁻¹ᵁ V ≤ ⊤)).op := by
    rw [show z.app V = z.appLE V (z ⁻¹ᵁ V) le_rfl from (Scheme.Hom.appLE_eq_app _).symm,
      Scheme.Hom.appLE_comp_appLE]
    have hid : ∀ (φ : T ⟶ T) (_ : φ = 𝟙 T) (e : z ⁻¹ᵁ V ≤ φ ⁻¹ᵁ ⊤),
        φ.appLE ⊤ (z ⁻¹ᵁ V) e = T.presheaf.map (homOfLE (le_top : z ⁻¹ᵁ V ≤ ⊤)).op := by
      rintro φ rfl e
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact congrArg T.presheaf.map (Subsingleton.elim _ _)
    exact hid (z ≫ π) hz _
  exact congrArg (fun φ : Γ(T, ⊤) ⟶ Γ(T, z ⁻¹ᵁ V) => φ.hom (C : Γ(T, ⊤))) hcomp

/-! ## The normalisation -/

/-- Twisting numerator and denominator by the same unit leaves the ratio unchanged. -/
private theorem eq_mul_inv_twist {G : Type*} [Group G] (a b w : G) :
    a * b⁻¹ = a * w⁻¹ * (b * w⁻¹)⁻¹ := by
  rw [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc w⁻¹ w, inv_mul_cancel, one_mul]

/-- **(AP-D5 normalisation, step 1 — KM p. 88)** If the transition unit between two splitting
units is normalised, then their zero-section values agree on the overlap. -/
theorem sectionEval_eq_of_mem_sectionUnits (z : T ⟶ Y) {V₁ V₂ : Y.Opens}
    {h₁ : Γ(Y, V₁)ˣ} {h₂ : Γ(Y, V₂)ˣ} {F : Γ(Y, V₁ ⊓ V₂)ˣ}
    (hsplit : F = Scheme.resUnit (inf_le_left : V₁ ⊓ V₂ ≤ V₁) h₁ *
      (Scheme.resUnit (inf_le_right : V₁ ⊓ V₂ ≤ V₂) h₂)⁻¹)
    (hF : F ∈ sectionUnits z (V₁ ⊓ V₂)) :
    Scheme.resUnit (inf_le_left : z ⁻¹ᵁ V₁ ⊓ z ⁻¹ᵁ V₂ ≤ z ⁻¹ᵁ V₁) (sectionEval z V₁ h₁) =
      Scheme.resUnit (inf_le_right : z ⁻¹ᵁ V₁ ⊓ z ⁻¹ᵁ V₂ ≤ z ⁻¹ᵁ V₂) (sectionEval z V₂ h₂) := by
  have h1 : sectionEval z (V₁ ⊓ V₂) F = 1 := hF
  rw [hsplit, map_mul, map_inv, sectionEval_resUnit, sectionEval_resUnit,
    mul_inv_eq_one] at h1
  exact h1

/-- **(AP-D5 NORMALISATION — KM p. 88)** Let `π : Y ⟶ T` have a section `z`, let `V i` be opens
of `Y` whose zero-section traces `z ⁻¹ᵁ (V i)` cover `T`, and let units `h i` on `V i` split a
family `F i j` of transition units, `F i j = h i · (h j)⁻¹`. If every `F i j` is **normalised**
(value `1` along `z`), then the `h i` can be normalised as well: there are `h' i` in `K^×(V i)`
splitting the same family.

This is Katz–Mazur's *"we may and will normalise the `h_i`"*: the zero-section values agree on
overlaps, hence glue to one `C ∈ Γ(T, ⊤)ˣ`, and `h' i = h i · (π^# C)⁻¹`. -/
theorem exists_normalized_splitting {π : Y ⟶ T} {z : T ⟶ Y} (hz : z ≫ π = 𝟙 T)
    {ι : Type*} (V : ι → Y.Opens) (hV : ⨆ i, z ⁻¹ᵁ V i = ⊤)
    (F : ∀ i j, Γ(Y, V i ⊓ V j)ˣ) (h : ∀ i, Γ(Y, V i)ˣ)
    (hsplit : ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h i) *
      (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h j))⁻¹)
    (hF : ∀ i j, F i j ∈ sectionUnits z (V i ⊓ V j)) :
    ∃ h' : ∀ i, Γ(Y, V i)ˣ, (∀ i, h' i ∈ sectionUnits z (V i)) ∧
      ∀ i j, F i j = Scheme.resUnit (inf_le_left : V i ⊓ V j ≤ V i) (h' i) *
        (Scheme.resUnit (inf_le_right : V i ⊓ V j ≤ V j) (h' j))⁻¹ := by
  obtain ⟨C, hC⟩ := exists_globalUnit_restrict (fun i => z ⁻¹ᵁ V i) hV
    (fun i => sectionEval z (V i) (h i))
    (fun i j => sectionEval_eq_of_mem_sectionUnits z (hsplit i j) (hF i j))
  refine ⟨fun i => h i * (globalTwist π (V i) C)⁻¹, fun i => ?_, fun i j => ?_⟩
  · show sectionEval z (V i) (h i * (globalTwist π (V i) C)⁻¹) = 1
    rw [map_mul, map_inv, sectionEval_globalTwist hz, hC i, mul_inv_cancel]
  · rw [hsplit i j, map_mul, map_mul, map_inv, map_inv, resUnit_globalTwist,
      resUnit_globalTwist]
    exact eq_mul_inv_twist _ _ _

end General

/-! ## The bridge to `AP-D1`/`AP-D2`: `K_E^×` over preimages of base opens -/

section Bridge

variable {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
variable {z : T ⟶ pullback p g} (hz : z ≫ pullback.snd p g = 𝟙 T)

/-- The tree's `kUnitsEval` (`AP-D1`, indexed by base opens) is `sectionEval` on the preimage
open, restricted back down along `U ≤ z ⁻¹ᵁ (f ⁻¹ᵁ U)`. -/
theorem kUnitsEval_eq_resUnit_sectionEval (U : T.Opens)
    (u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ) :
    kUnitsEval g hz U u =
      Scheme.resUnit (le_preimage_preimage g hz U) (sectionEval z (pullback.snd p g ⁻¹ᵁ U) u) :=
  rfl

/-- **A normalised unit on the preimage of a base open lies in KM's `K_E^×`** as the tree
defines it (`kUnits`, `WeilPairing/UnitSheaf.lean`). This is what makes the `h'` produced by
`exists_normalized_splitting` eligible for the `AP-D2` uniqueness lemmas. -/
theorem mem_kUnits_of_mem_sectionUnits (U : T.Opens)
    {u : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ}
    (hu : u ∈ sectionUnits z (pullback.snd p g ⁻¹ᵁ U)) : u ∈ kUnits g hz U := by
  have h1 : sectionEval z (pullback.snd p g ⁻¹ᵁ U) u = 1 := hu
  show kUnitsEval g hz U u = 1
  rw [kUnitsEval_eq_resUnit_sectionEval, h1, map_one]

include hz in
/-- **(AP-D2 in the `sectionUnits` vocabulary)** Over a universally `O`-connected family, two
units on the preimage of a base open that are both normalised along the zero section are equal:
`H⁰(K^×) = {1}`, i.e. `eq_of_div_mem_kUnits`, read through `mem_kUnits_of_mem_sectionUnits`.

Scope: this pins the normalised unit only on opens that are *preimages of base opens*. KM's
`h_i` live on general opens `V i` of the curve, and their uniqueness needs one further gluing —
of the ratios `h_i / h'_i`, which agree on overlaps and are normalised, hence glue by
`exists_globalUnit_restrict` to a global normalised unit killed by this lemma at `U = ⊤`. That
assembly is left to the uniqueness half of the ticket (`AP-D2`, already discharged). -/
theorem eq_of_mem_sectionUnits (hp : UniversallyOConnected p) (U : T.Opens)
    {u v : Γ(pullback p g, pullback.snd p g ⁻¹ᵁ U)ˣ}
    (hu : u ∈ sectionUnits z (pullback.snd p g ⁻¹ᵁ U))
    (hv : v ∈ sectionUnits z (pullback.snd p g ⁻¹ᵁ U)) : u = v :=
  eq_of_div_mem_kUnits g hp hz U
    (Subgroup.mul_mem _ (mem_kUnits_of_mem_sectionUnits g hz U hu)
      (Subgroup.inv_mem _ (mem_kUnits_of_mem_sectionUnits g hz U hv)))

end Bridge

/-! ## AP-D5 assembled: existence and normalisation together -/

section Assembled

open AlgebraicGeometry.Scheme.Modules

variable {X Y T : Scheme.{u}}

/-- The covering hypothesis in the practical form: if the trivialising opens `W i` cover `X`,
then their `f`-preimages traced back along the section `z` cover the base. -/
theorem iSup_preimage_preimage_eq_top (f : Y ⟶ X) (z : T ⟶ Y) {ι : Sort*} {W : ι → X.Opens}
    (hW : iSup W = ⊤) : ⨆ i, z ⁻¹ᵁ (f ⁻¹ᵁ W i) = ⊤ :=
  z.iSup_preimage_eq_top (f.iSup_preimage_eq_top hW)

/-- **(AP-D5 COMPLETE — KM p. 88)** Let `M` be an `𝒪_X`-module trivialised over opens `W i`,
with `f^*M` trivialised over the top open of `Y` (for `f = [N]` and `M` representing `κ(Q)` this
is the `⊆` direction of AP-D4), and let `π : Y ⟶ T` have a section `z` whose traces
`z ⁻¹ᵁ (f ⁻¹ᵁ W i)` cover `T`. If the pulled-back transition units `f^# f_{i,j}` are normalised
along `z`, then the splitting units can be taken **normalised as well**:

  `f^# (f_{i,j}) = h_i · h_j⁻¹`  with  `h_i ∈ K^×(f ⁻¹ᵁ W i)`,

which is Katz–Mazur's `f_{i,j} ∘ [N] = h_i / h_j` with the `h_i` normalised along the zero
section. Existence is `exists_pullback_transitionUnit_eq_mul_inv`
(`WeilPairing/KMSplitting.lean`); the normalisation is `exists_normalized_splitting` above. -/
theorem exists_normalized_pullback_transitionUnit_eq_mul_inv (f : Y ⟶ X) (M : X.Modules)
    (ε : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (⊤ : Y.Opens) ≅
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (⊤ : Y.Opens)))
    {π : Y ⟶ T} {z : T ⟶ Y} (hz : z ≫ π = 𝟙 T) {ι : Type*} (W : ι → X.Opens)
    (hW : ⨆ i, z ⁻¹ᵁ (f ⁻¹ᵁ W i) = ⊤)
    (e : ∀ i, M.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, Units.map (f.app (W i ⊓ W j)).hom.toMonoidHom
        (trivializationTransitionUnit (W i ⊓ W j)
          (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (e i)
            (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
          (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (e j)
            (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))))) ∈
      sectionUnits z (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W j)) :
    ∃ h : ∀ i, Γ(Y, f ⁻¹ᵁ W i)ˣ, (∀ i, h i ∈ sectionUnits z (f ⁻¹ᵁ W i)) ∧
      ∀ i j, Units.map (f.app (W i ⊓ W j)).hom.toMonoidHom
          (trivializationTransitionUnit (W i ⊓ W j)
            (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W i) (e i)
              (Over.mk (homOfLE (inf_le_left : W i ⊓ W j ≤ W i))))
            (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (W j) (e j)
              (Over.mk (homOfLE (inf_le_right : W i ⊓ W j ≤ W j))))) =
        Scheme.resUnit (inf_le_left : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W j ≤ f ⁻¹ᵁ W i) (h i) *
          (Scheme.resUnit (inf_le_right : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W j ≤ f ⁻¹ᵁ W j) (h j))⁻¹ := by
  obtain ⟨h, hh⟩ := exists_pullback_transitionUnit_eq_mul_inv f M ε W e
  exact exists_normalized_splitting hz (fun i => f ⁻¹ᵁ W i) hW _ h hh hnorm

end Assembled

end ModularCurves
