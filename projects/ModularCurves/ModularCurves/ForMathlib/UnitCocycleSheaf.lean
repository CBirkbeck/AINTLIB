/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule

/-!
# The invertible sheaf glued from a Čech 1-cocycle of units (T-OM-A*)

**(T-E-OMEGA route R1, PART A — `/develop --decompose` 2026-07-13, STREAM-OMEGA;
decomposition: `.mathlib-quality/decomposition-omega-r1.md`.)**

From an open cover `U : ι → X.Opens` of a scheme `X` and a normalized Čech 1-cocycle of
units `u i j ∈ Γ(X, U i ⊓ U j)ˣ` (`u i i = 1`, `u i j · u j k = u i k` on triple
overlaps), we build the invertible `𝒪ₓ`-module it glues: the **compatible-families
model**, whose sections over `V` are families `b i ∈ Γ(X, V ⊓ U i)` with
`b i = u i j · b j` on double overlaps. No abstract glueing theorem is used — the sheaf
property reduces componentwise to that of `𝒪_X` (Stacks 01AJ specialized to rank one).

* `UnitCocycle`: the cover-with-cocycle data.
* `UnitCocycle.sections`: the compatible families over an open, a `Γ(X, V)`-module.
* `UnitCocycle.lineBundle`: the bundled `X.Modules` object.
* `UnitCocycle.sectionsEquivOfLE`: the chart trivialization over any `V ≤ U k` —
  consuming `u_self` and `u_cocycle`; this is the invertibility.
* `UnitCocycle.lineBundle_isInvertible`: `Scheme.Modules.IsInvertible` (the project's
  Picard-stream predicate), by the `isIso_of_bijective_app_on_basis` route of
  `Picard/IdealModule.lean`.
* `UnitCocycle.IsBasis` + torsor lemmas: bases = componentwise-unit families; the
  `Γ(X, V)ˣ`-action on bases is free, and transitive when a basis exists
  (`exists_unique_smul_eq`); with `trivSection`, bases exist over every `V ≤ U k`.
* `Scheme.exists_unit_glue`: glueing a unit over an arbitrary open from a
  restriction-compatible family of units on the affine opens below it.
* `UnitCocycle.Compat` + `Compat.sectionsEquiv`: comparison data between two cocycles
  on the same scheme and the induced section/basis transport.
* `UnitCocycle.pullbackCocycle` + basis pullback along a morphism of schemes.

Consumer: `EllipticCurve/InvariantDifferential.lean` (T-OM-B*) instantiates all of this
at the Weierstrass-atlas transition cocycle of an elliptic curve to define `ω_{E/S}`.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- Restriction of scheme sections along an inequality of opens, as a ring hom. -/
noncomputable abbrev resLE {V' V : X.Opens} (h : V' ≤ V) : Γ(X, V) →+* Γ(X, V') :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Restriction of unit sections along an inequality of opens. -/
noncomputable abbrev resUnit {V' V : X.Opens} (h : V' ≤ V) : Γ(X, V)ˣ →* Γ(X, V')ˣ :=
  Units.map (resLE h).toMonoidHom

/-- Restrictions compose (functoriality of the structure sheaf, elementwise). -/
theorem resLE_resLE {V'' V' V : X.Opens} (h' : V'' ≤ V') (h : V' ≤ V) (r : Γ(X, V)) :
    resLE h' (resLE h r) = resLE (h'.trans h) r := by
  have hcomp : X.presheaf.map (homOfLE (h'.trans h)).op =
      X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op := by
    rw [← Functor.map_comp, ← op_comp]
    rfl
  show (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom r) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom r
  rw [hcomp, CommRingCat.hom_comp, RingHom.comp_apply]

/-- **(T-OM-A1)** A normalized Čech 1-cocycle of units on an open cover of a scheme:
the glueing data of an invertible sheaf trivialized on the cover (Stacks 01AJ,
rank-one case). `u i j` is the transition from the `j`-th to the `i`-th
trivialization; normalization `u i i = 1` and the cocycle identity on triple overlaps
make the compatible-family sheaf below invertible. -/
structure UnitCocycle (X : Scheme.{u}) where
  /-- The index type of the cover. -/
  ι : Type u
  /-- The opens of the cover. -/
  U : ι → X.Opens
  /-- The opens cover `X`. -/
  covers : ∀ x : X, ∃ i, x ∈ U i
  /-- The transition units on pairwise intersections. -/
  u : ∀ i j, Γ(X, U i ⊓ U j)ˣ
  /-- Normalization on the diagonal. -/
  u_self : ∀ i, u i i = 1
  /-- The cocycle identity on triple overlaps. -/
  u_cocycle : ∀ i j k,
    resUnit (inf_le_left (b := U k)) (u i j) *
      resUnit (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (u j k) =
      resUnit (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (u i k)

namespace UnitCocycle

variable (c : UnitCocycle X)

/-- The cover of a unit cocycle has supremum `⊤`. -/
theorem iSup_eq_top : ⨆ i, c.U i = ⊤ := by
  rw [eq_top_iff]
  exact fun x _ => Opens.mem_iSup.mpr (c.covers x)

/-- **(T-OM-A1)** Compatibility of a family `b i ∈ Γ(X, V ⊓ U i)` with the cocycle:
on each double overlap, `b i = u i j · b j`. These are the sections of the glued
invertible sheaf (the components of a single section in the chart trivializations). -/
def Compatible (V : X.Opens) (b : ∀ i, Γ(X, V ⊓ c.U i)) : Prop :=
  ∀ i j, resLE (inf_le_left (b := c.U j)) (b i) =
    (resUnit (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c.u i j)).val *
      resLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (b j)

/-- **(T-OM-A1)** The sections of the glued invertible sheaf over `V`: cocycle-compatible
families. -/
def sections (V : X.Opens) : Type u :=
  {b : ∀ i, Γ(X, V ⊓ c.U i) // c.Compatible V b}

namespace sections

variable {c} {V : X.Opens}

theorem compatible_zero : c.Compatible V (fun _ => 0) := fun i j => by
  simp only [map_zero, mul_zero]

theorem compatible_add {b b' : ∀ i, Γ(X, V ⊓ c.U i)} (hb : c.Compatible V b)
    (hb' : c.Compatible V b') : c.Compatible V (b + b') := fun i j => by
  simp only [Pi.add_apply, map_add]
  rw [hb i j, hb' i j, mul_add]

theorem compatible_neg {b : ∀ i, Γ(X, V ⊓ c.U i)} (hb : c.Compatible V b) :
    c.Compatible V (-b) := fun i j => by
  simp only [Pi.neg_apply, map_neg]
  rw [hb i j, mul_neg]

theorem compatible_smul (r : Γ(X, V)) {b : ∀ i, Γ(X, V ⊓ c.U i)} (hb : c.Compatible V b) :
    c.Compatible V (fun i => resLE inf_le_left r * b i) := fun i j => by
  simp only [map_mul]
  rw [resLE_resLE, resLE_resLE, hb i j]
  ring

instance : Zero (c.sections V) := ⟨⟨fun _ => 0, compatible_zero⟩⟩

instance : Add (c.sections V) := ⟨fun b b' => ⟨b.1 + b'.1, compatible_add b.2 b'.2⟩⟩

instance : Neg (c.sections V) := ⟨fun b => ⟨-b.1, compatible_neg b.2⟩⟩

noncomputable instance : SMul Γ(X, V) (c.sections V) :=
  ⟨fun r b => ⟨fun i => resLE inf_le_left r * b.1 i, compatible_smul r b.2⟩⟩

@[simp] theorem zero_coe (i : c.ι) : ((0 : c.sections V)).1 i = 0 := rfl

@[simp] theorem add_coe (b b' : c.sections V) (i : c.ι) :
    (b + b').1 i = b.1 i + b'.1 i := rfl

@[simp] theorem neg_coe (b : c.sections V) (i : c.ι) : (-b).1 i = -(b.1 i) := rfl

@[simp] theorem smul_coe (r : Γ(X, V)) (b : c.sections V) (i : c.ι) :
    (r • b).1 i = resLE inf_le_left r * b.1 i := rfl

instance : AddCommGroup (c.sections V) where
  add_assoc a b d := Subtype.ext (by funext i; exact add_assoc _ _ _)
  zero_add a := Subtype.ext (by funext i; exact zero_add _)
  add_zero a := Subtype.ext (by funext i; exact add_zero _)
  add_comm a b := Subtype.ext (by funext i; exact add_comm _ _)
  neg_add_cancel a := Subtype.ext (by funext i; exact neg_add_cancel _)
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance : Module Γ(X, V) (c.sections V) where
  one_smul b := Subtype.ext (by funext i; simp [map_one])
  mul_smul r r' b := Subtype.ext (by funext i; simp [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (by funext i; simp)
  smul_add r b b' := Subtype.ext (by funext i; simp [mul_add])
  add_smul r r' b := Subtype.ext (by funext i; simp [map_add, add_mul])
  zero_smul b := Subtype.ext (by funext i; simp)

end sections

/-! ### T-OM-A2: the presheaf of modules -/

/-- **(T-OM-A2)** Componentwise restriction of compatible families. -/
noncomputable def sectionsMap {V' V : X.Opens} (h : V' ≤ V) :
    c.sections V → c.sections V' := by
  sorry

/-- **(T-OM-A2)** The compatible families as a presheaf of abelian groups (componentwise
restrictions of `𝒪_X`). -/
noncomputable def presheafAb (c : UnitCocycle X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := by
  sorry

/-- **(T-OM-A2)** The compatible families as a presheaf of `𝒪_X`-modules
(`PresheafOfModules.ofPresheaf` over `presheafAb`; the restrictions are semilinear). -/
noncomputable def presheafOfModules (c : UnitCocycle X) :
    _root_.PresheafOfModules (X.ringCatSheaf.obj) := by
  sorry

/-! ### T-OM-A3: the sheaf condition and the bundled module -/

/-- **(T-OM-A3)** The compatible-families presheaf is a sheaf: componentwise glueing of
`𝒪_X` plus locality of the compatibility condition (separatedness on triple overlaps). -/
theorem isSheaf_presheafAb :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥X) c.presheafAb := by
  sorry

/-- **(T-OM-A3)** ★ The invertible sheaf glued from a unit cocycle, as an `𝒪ₓ`-module. -/
noncomputable def lineBundle (c : UnitCocycle X) : X.Modules := by
  sorry

/-- **(T-OM-A3)** The sections of the line bundle over `V` are the compatible families
(the defining linear equivalence). -/
noncomputable def lineBundleSectionsEquiv (V : X.Opens) :
    Γ(c.lineBundle, V) ≃ₗ[Γ(X, V)] c.sections V := by
  sorry

/-! ### T-OM-A4: the chart trivialization -/

/-- **(T-OM-A4)** The chart section of the `k`-th trivialization over `V ≤ U k`:
the compatible family `(u i k)|_{V ⊓ U i}` — the coordinates, in every chart, of the
`k`-th chart's canonical basis vector. -/
noncomputable def trivSection (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.sections V := by
  sorry

/-- **(T-OM-A4)** Over `V ≤ U k`, evaluation of the `k`-th component is a linear
equivalence onto `Γ(X, V)` — the chart trivialization of the glued sheaf. Inverse:
`g ↦ g • trivSection k`. Consumes `u_self` (right inverse) and `u_cocycle`
(compatibility of the inverse family). -/
noncomputable def sectionsEquivOfLE (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.sections V ≃ₗ[Γ(X, V)] Γ(X, V) := by
  sorry

/-- **(T-OM-A4)** The trivialization is natural in `V` (compatible with restriction). -/
theorem sectionsEquivOfLE_natural (k : c.ι) {V' V : X.Opens} (hV' : V' ≤ V)
    (hV : V ≤ c.U k) (b : c.sections V) :
    c.sectionsEquivOfLE k (hV'.trans hV) (c.sectionsMap hV' b) =
      resLE hV' (c.sectionsEquivOfLE k hV b) := by
  sorry

/-- **(T-OM-A4)** The trivialization sends the chart section to `1`. -/
theorem sectionsEquivOfLE_trivSection (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.sectionsEquivOfLE k hV (c.trivSection k hV) = 1 := by
  sorry

/-! ### T-OM-A4b: invertibility (the Picard-stream predicate) -/

open AlgebraicGeometry.Scheme.Modules in
/-- **(T-OM-A4b)** ★ The glued line bundle is an invertible `𝒪ₓ`-module in the sense of
the Picard stream (`Scheme.Modules.IsInvertible`): the cover `U` trivializes it, by the
`isIso_of_bijective_app_on_basis` route with the bijectivity supplied by
`sectionsEquivOfLE` at every open below a chart. -/
theorem lineBundle_isInvertible : IsInvertible c.lineBundle := by
  sorry

/-! ### T-OM-A5: bases and the torsor structure -/

/-- **(T-OM-A5)** A section is a basis if it is a unit in every chart. For sections of an
invertible sheaf this is the correct global notion of "nowhere-vanishing generator"; over
`V ≤ U k` it coincides with "the trivialization sends it to a unit"
(`isBasis_iff_isUnit`). -/
def IsBasis {V : X.Opens} (b : c.sections V) : Prop :=
  ∀ i, IsUnit (b.1 i)

/-- **(T-OM-A5)** The chart section is a basis. -/
theorem isBasis_trivSection (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.IsBasis (c.trivSection k hV) := by
  sorry

/-- **(T-OM-A5)** Unit scaling preserves and reflects bases. -/
theorem isBasis_smul_iff {V : X.Opens} (g : Γ(X, V)ˣ) (b : c.sections V) :
    c.IsBasis (g.val • b) ↔ c.IsBasis b := by
  sorry

/-- **(T-OM-A5)** Over `V ≤ U k`, a section is a basis iff its trivialization is a unit. -/
theorem isBasis_iff_isUnit (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) (b : c.sections V) :
    c.IsBasis b ↔ IsUnit (c.sectionsEquivOfLE k hV b) := by
  sorry

/-- **(T-OM-A5)** ★ The torsor property: any two sections with the first a basis differ
by a unique scalar — the ratios in each chart agree on overlaps and glue. This is the
`𝔾ₘ`-torsor trivialization of the board ("ω3 = T-A4's trivialization"): the scalar is a
unit iff the second section is a basis (`isBasis_smul_iff` + uniqueness). -/
theorem exists_unique_smul_eq {V : X.Opens} {b : c.sections V} (hb : c.IsBasis b)
    (b' : c.sections V) : ∃! g : Γ(X, V), g • b = b' := by
  sorry

/-- **(T-OM-A5)** The unit action on bases is free. -/
theorem smul_left_injective {V : X.Opens} {b : c.sections V} (hb : c.IsBasis b)
    {g g' : Γ(X, V)} (h : g • b = g' • b) : g = g' := by
  sorry

/-! ### T-OM-A6: glueing units over an open from affine-local data -/

end UnitCocycle

/-- **(T-OM-A6)** A restriction-compatible family of units on the affine opens below `W`
glues to a unique unit on `W`: affine opens form a basis, the underlying sections glue by
the sheaf property, and the glued section is a unit because it is one on a cover
(`RingedSpace.isUnit_of_isUnit_germ`). -/
theorem exists_unit_glue (X : Scheme.{u}) (W : X.Opens)
    (data : ∀ V : X.affineOpens, V.1 ≤ W → Γ(X, V.1)ˣ)
    (compat : ∀ (V V' : X.affineOpens) (hV : V.1 ≤ W) (h : V'.1 ≤ V.1),
      resUnit h (data V hV) = data V' (h.trans hV)) :
    ∃! g : Γ(X, W)ˣ, ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      resUnit hV g = data V hV := by
  sorry

namespace UnitCocycle

variable (c : UnitCocycle X)

/-! ### T-OM-A7: comparison of two cocycles and section transport -/

/-- **(T-OM-A7)** Comparison data between two unit cocycles on the same scheme: units
`w i j` on the mixed overlaps intertwining the two transition systems. This is a
cochain exhibiting the two glued sheaves as isomorphic (the direction of "cohomologous
cocycles have isomorphic bundles" that the ω-base-change needs). -/
structure Compat (c' : UnitCocycle X) where
  /-- The comparison units on mixed overlaps. -/
  w : ∀ (i : c.ι) (j : c'.ι), Γ(X, c.U i ⊓ c'.U j)ˣ
  /-- Left compatibility: `u i i' · w i' j = w i j` on `U i ⊓ U i' ⊓ U' j`. -/
  left : ∀ (i i' : c.ι) (j : c'.ι),
    resUnit (inf_le_left (b := c'.U j)) (c.u i i') *
      resUnit (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (w i' j) =
      resUnit (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w i j)
  /-- Right compatibility: `w i j · u' j j' = w i j'` on `U i ⊓ U' j ⊓ U' j'`. -/
  right : ∀ (i : c.ι) (j j' : c'.ι),
    resUnit (inf_le_left (b := c'.U j')) (w i j) *
      resUnit (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c'.u j j') =
      resUnit (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w i j')

/-- **(T-OM-A7)** Comparison data transports sections: the `i`-component of the image is
glued (componentwise, by the sheaf property of `𝒪_X`) from `w i j · b' j` over the cover
of `V ⊓ U i` by the `V ⊓ U i ⊓ U' j`. -/
noncomputable def Compat.sectionsEquiv {c : UnitCocycle X} {c' : UnitCocycle X}
    (κ : c.Compat c') (V : X.Opens) : c'.sections V ≃ₗ[Γ(X, V)] c.sections V := by
  sorry

/-- **(T-OM-A7)** Comparison transport preserves bases. -/
theorem Compat.isBasis_sectionsEquiv {c : UnitCocycle X} {c' : UnitCocycle X}
    (κ : c.Compat c') {V : X.Opens} (b : c'.sections V) :
    c.IsBasis (κ.sectionsEquiv V b) ↔ c'.IsBasis b := by
  sorry

/-! ### T-OM-A7b: pullback of a cocycle along a morphism of schemes -/

/-- **(T-OM-A7b)** The pullback cocycle along `f : Y ⟶ X`: preimage cover, transition
units mapped by `f`'s section maps on preimages. -/
noncomputable def pullbackCocycle (c : UnitCocycle X) (f : Y ⟶ X) : UnitCocycle Y := by
  sorry

/-- **(T-OM-A7b)** Componentwise pullback of sections along `f`. -/
noncomputable def sectionsPullback (f : Y ⟶ X) {V : X.Opens} (b : c.sections V) :
    (c.pullbackCocycle f).sections (f ⁻¹ᵁ V) := by
  sorry

/-- **(T-OM-A7b)** Pullback of a basis is a basis (ring maps preserve units). -/
theorem isBasis_sectionsPullback (f : Y ⟶ X) {V : X.Opens} {b : c.sections V}
    (hb : c.IsBasis b) : (c.pullbackCocycle f).IsBasis (c.sectionsPullback f b) := by
  sorry

end UnitCocycle

end AlgebraicGeometry.Scheme
