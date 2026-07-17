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

@[simp] theorem resUnit_val {V' V : X.Opens} (h : V' ≤ V) (g : Γ(X, V)ˣ) :
    (resUnit h g).val = resLE h g.val :=
  rfl

/-- Restriction along a reflexive inequality is the identity. -/
@[simp] theorem resLE_rfl {V : X.Opens} (h : V ≤ V) (r : Γ(X, V)) : resLE h r = r := by
  have harr : (homOfLE h).op = 𝟙 (Opposite.op V) := by
    rw [show homOfLE h = 𝟙 V from Subsingleton.elim _ _, op_id]
  show (X.presheaf.map (homOfLE h).op).hom r = r
  rw [harr, CategoryTheory.Functor.map_id]
  rfl

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

/-- Unit restrictions compose. -/
theorem resUnit_resUnit {V'' V' V : X.Opens} (h' : V'' ≤ V') (h : V' ≤ V) (g : Γ(X, V)ˣ) :
    resUnit h' (resUnit h g) = resUnit (h'.trans h) g :=
  Units.ext (by simp [resLE_resLE])

/-- Restrictions compose (ring-hom level). -/
theorem resLE_comp {V'' V' V : X.Opens} (h' : V'' ≤ V') (h : V' ≤ V) :
    (resLE (X := X) h').comp (resLE h) = resLE (h'.trans h) :=
  RingHom.ext fun r => resLE_resLE h' h r

/-- The inverse of a restricted unit times the restricted value is one. -/
theorem inv_resUnit_mul_resLE {V' V : X.Opens} (h : V' ≤ V) (g : Γ(X, V)ˣ) :
    ((resUnit h g)⁻¹).val * resLE h g.val = 1 :=
  Units.inv_mul _

/-- The restricted value times the inverse of the restricted unit is one. -/
theorem resLE_mul_inv_resUnit {V' V : X.Opens} (h : V' ≤ V) (g : Γ(X, V)ˣ) :
    resLE h g.val * ((resUnit h g)⁻¹).val = 1 :=
  Units.mul_inv (resUnit h g)

/-- Restriction of the value of a restricted unit. -/
theorem resLE_resUnit_val {V'' V' V : X.Opens} (h' : V'' ≤ V') (h : V' ≤ V)
    (g : Γ(X, V)ˣ) : resLE h' ((resUnit h g).val) = (resUnit (h'.trans h) g).val := by
  simp [resLE_resLE]

/-- Restriction of the value of the inverse of a restricted unit. -/
theorem resLE_inv_resUnit_val {V'' V' V : X.Opens} (h' : V'' ≤ V') (h : V' ≤ V)
    (g : Γ(X, V)ˣ) :
    resLE h' (((resUnit h g)⁻¹).val) = ((resUnit (h'.trans h) g)⁻¹).val := by
  have hrfl : (resUnit h' ((resUnit h g)⁻¹)).val = resLE h' (((resUnit h g)⁻¹).val) := rfl
  rw [← hrfl, map_inv, resUnit_resUnit]

/-- Restricting the pullback of a section is pulling back to the smaller open. -/
theorem resLE_appLE {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W) (r : Γ(X, U)) :
    resLE h' ((f.appLE U W h).hom r) = (f.appLE U W' (h'.trans h)).hom r := by
  rw [show resLE h' ((f.appLE U W h).hom r) =
    (f.appLE U W h ≫ Y.presheaf.map (homOfLE h').op).hom r from rfl,
    Scheme.Hom.appLE_map]

/-- Pulling back a restricted section is pulling back from the larger open. -/
theorem appLE_resLE {Y X : Scheme.{u}} (f : Y ⟶ X) {U U' : X.Opens} (hU : U ≤ U')
    {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (r : Γ(X, U')) :
    (f.appLE U W h).hom (resLE hU r) =
      (f.appLE U' W (h.trans ((Opens.map f.base).map (homOfLE hU)).le)).hom r := by
  rw [show (f.appLE U W h).hom (resLE hU r) =
    (X.presheaf.map (homOfLE hU).op ≫ f.appLE U W h).hom r from rfl,
    Scheme.Hom.map_appLE]

/-- Restricting a pulled-back unit is pulling back to the smaller open. -/
theorem resUnit_map_appLE {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W) (g : Γ(X, U)ˣ) :
    resUnit h' (Units.map ((f.appLE U W h).hom).toMonoidHom g) =
      Units.map ((f.appLE U W' (h'.trans h)).hom).toMonoidHom g :=
  Units.ext (by simpa using resLE_appLE f h h' g.val)

/-- Pulling back a restricted unit is pulling back from the larger open. -/
theorem map_appLE_resUnit {Y X : Scheme.{u}} (f : Y ⟶ X) {U U' : X.Opens} (hU : U ≤ U')
    {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (g : Γ(X, U')ˣ) :
    Units.map ((f.appLE U W h).hom).toMonoidHom (resUnit hU g) =
      Units.map ((f.appLE U' W
        (h.trans ((Opens.map f.base).map (homOfLE hU)).le)).hom).toMonoidHom g :=
  Units.ext (by simpa using appLE_resLE f hU h g.val)

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

/-- **(T-OM-A0′)** The `n`-th power of a unit cocycle (same cover, transition units
raised to the `n`): the carrier of `ω^{⊗n}`-style twists. -/
@[simps]
noncomputable def zpow (n : ℤ) : UnitCocycle X where
  ι := c.ι
  U := c.U
  covers := c.covers
  u i j := (c.u i j) ^ n
  u_self i := by rw [c.u_self, one_zpow]
  u_cocycle i j k := by
    rw [map_zpow, map_zpow, map_zpow, ← mul_zpow, c.u_cocycle]


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

/-- **(T-OM-A2)** Compatibility is stable under componentwise restriction. -/
theorem Compatible.res {c : UnitCocycle X} {V' V : X.Opens} (h : V' ≤ V)
    {b : ∀ i, Γ(X, V ⊓ c.U i)} (hb : c.Compatible V b) :
    c.Compatible V' (fun i => resLE (inf_le_inf_right (c.U i) h) (b i)) := fun i j => by
  have hij := congrArg
    (⇑(resLE (X := X) (inf_le_inf_right (c.U j) (inf_le_inf_right (c.U i) h)))) (hb i j)
  simp only [map_mul, resUnit_val, resLE_resLE] at hij ⊢
  exact hij

/-- **(T-OM-A2)** Componentwise restriction of compatible families. -/
noncomputable def sectionsMap {V' V : X.Opens} (h : V' ≤ V) :
    c.sections V → c.sections V' := fun b =>
  ⟨fun i => resLE (inf_le_inf_right (c.U i) h) (b.1 i), Compatible.res h b.2⟩

@[simp] theorem sectionsMap_coe {V' V : X.Opens} (h : V' ≤ V) (b : c.sections V)
    (i : c.ι) :
    (c.sectionsMap h b).1 i = resLE (inf_le_inf_right (c.U i) h) (b.1 i) :=
  rfl

/-- **(T-OM-A2)** The compatible families as a presheaf of abelian groups (componentwise
restrictions of `𝒪_X`). -/
noncomputable def presheafAb (c : UnitCocycle X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (c.sections V.unop)
  map {V V'} i := AddCommGrpCat.ofHom
    { toFun := c.sectionsMap (leOfHom i.unop)
      map_zero' := Subtype.ext (by
        funext k
        exact map_zero (resLE (inf_le_inf_right (c.U k) (leOfHom i.unop))))
      map_add' := fun b b' => Subtype.ext (by
        funext k
        exact map_add (resLE (inf_le_inf_right (c.U k) (leOfHom i.unop))) _ _) }
  map_id V := by
    ext b
    refine Subtype.ext (funext fun k => ?_)
    show resLE _ (b.1 k) = b.1 k
    exact resLE_rfl _ _
  map_comp {V V' V''} i j := by
    ext b
    refine Subtype.ext (funext fun k => ?_)
    show resLE _ (b.1 k) = resLE _ (resLE _ (b.1 k))
    rw [resLE_resLE]

/-- The sections of the compatible-families presheaf carry the module structure of
`sections` (instance bridge for `PresheafOfModules.ofPresheaf`). -/
noncomputable instance (c : UnitCocycle X) (V : (Opens X)ᵒᵖ) :
    Module ((X.ringCatSheaf.obj).obj V) ((c.presheafAb).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (c.sections V.unop))

/-- **(T-OM-A2)** The compatible families as a presheaf of `𝒪_X`-modules
(`PresheafOfModules.ofPresheaf` over `presheafAb`; the restrictions are semilinear). -/
noncomputable def presheafOfModules (c : UnitCocycle X) :
    _root_.PresheafOfModules (X.ringCatSheaf.obj) :=
  PresheafOfModules.ofPresheaf (c.presheafAb) (fun {V V'} i r m => by
    refine Subtype.ext (funext fun k => ?_)
    show resLE (inf_le_inf_right (c.U k) (leOfHom i.unop))
        (resLE inf_le_left r * m.1 k) =
      resLE inf_le_left (((X.ringCatSheaf.obj).map i) r) *
        resLE (inf_le_inf_right (c.U k) (leOfHom i.unop)) (m.1 k)
    rw [map_mul, resLE_resLE]
    show _ * _ = resLE inf_le_left (((X.ringCatSheaf.obj).map i).hom r) * _
    rw [show (((X.ringCatSheaf.obj).map i).hom r) = resLE (leOfHom i.unop) r from rfl,
      resLE_resLE])

/-! ### T-OM-A3: the sheaf condition and the bundled module -/

/-- **(T-OM-A3)** The compatible-families presheaf is a sheaf: componentwise glueing of
`𝒪_X` plus locality of the compatibility condition (separatedness on triple overlaps). -/
theorem isSheaf_presheafAb :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥X) c.presheafAb := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{u})
    (F := c.presheafAb)).mpr
  intro ι' Vl sf hcompat
  -- componentwise compatibility of the underlying `𝒪_X`-sections
  have hcpt : ∀ i : c.ι, TopCat.Presheaf.IsCompatible X.sheaf.1
      (fun l => Vl l ⊓ c.U i) (fun l => (sf l).1 i) := by
    intro i l m
    have h0 : resLE (inf_le_inf_right (c.U i) (inf_le_left (b := Vl m))) ((sf l).1 i) =
        resLE (inf_le_inf_right (c.U i) (inf_le_right (a := Vl l))) ((sf m).1 i) :=
      congrArg (fun s : c.sections (Vl l ⊓ Vl m) => s.1 i) (hcompat l m)
    have h1 := congrArg (⇑(resLE (X := X)
      (le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
        (inf_le_left.trans inf_le_right) :
        (Vl l ⊓ c.U i) ⊓ (Vl m ⊓ c.U i) ≤ (Vl l ⊓ Vl m) ⊓ c.U i))) h0
    simp only [resLE_resLE] at h1
    show resLE (Opens.infLELeft (Vl l ⊓ c.U i) (Vl m ⊓ c.U i)).le ((sf l).1 i) =
      resLE (Opens.infLERight (Vl l ⊓ c.U i) (Vl m ⊓ c.U i)).le ((sf m).1 i)
    exact h1
  -- glue each component
  choose b hb hbuniq using fun i : c.ι =>
    TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun l => Vl l ⊓ c.U i) (iSup Vl ⊓ c.U i)
      (fun l => homOfLE (inf_le_inf_right (c.U i) (le_iSup Vl l)))
      (le_of_eq (by rw [iSup_inf_eq])) (fun l => (sf l).1 i) (hcpt i)
  -- the glued family is compatible (separatedness over the cover)
  have hbcomp : c.Compatible (iSup Vl) b := by
    intro i j
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun l => Vl l ⊓ c.U i ⊓ c.U j) (iSup Vl ⊓ c.U i ⊓ c.U j)
      (fun l => homOfLE (inf_le_inf_right (c.U j) (inf_le_inf_right (c.U i) (le_iSup Vl l))))
      (le_of_eq (by rw [iSup_inf_eq, iSup_inf_eq])) _ _ (fun l => ?_)
    have hbi : resLE (inf_le_left (b := c.U j))
        (resLE (inf_le_inf_right (c.U i) (le_iSup Vl l)) (b i)) =
        resLE (inf_le_left (b := c.U j)) ((sf l).1 i) :=
      congrArg (⇑(resLE (X := X) (inf_le_left (b := c.U j)))) (hb i l)
    have hbj : resLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (resLE (inf_le_inf_right (c.U j) (le_iSup Vl l)) (b j)) =
        resLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ((sf l).1 j) :=
      congrArg (⇑(resLE (X := X)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          Vl l ⊓ c.U i ⊓ c.U j ≤ Vl l ⊓ c.U j))) (hb j l)
    simp only [resLE_resLE] at hbi hbj
    show resLE (inf_le_inf_right (c.U j) (inf_le_inf_right (c.U i) (le_iSup Vl l)))
        (resLE inf_le_left (b i)) =
      resLE (inf_le_inf_right (c.U j) (inf_le_inf_right (c.U i) (le_iSup Vl l)))
        ((resUnit (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c.u i j)).val *
          resLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (b j))
    rw [map_mul]
    simp only [resUnit_val, resLE_resLE]
    rw [hbi, hbj]
    have hsf := (sf l).2 i j
    simp only [resUnit_val] at hsf
    exact hsf
  -- the amalgamation
  refine ⟨⟨b, hbcomp⟩, fun l => ?_, fun s' hs' => ?_⟩
  · refine Subtype.ext (funext fun i => ?_)
    show resLE (inf_le_inf_right (c.U i) (le_iSup Vl l)) (b i) = (sf l).1 i
    exact hb i l
  · refine Subtype.ext (funext fun i => ?_)
    show s'.1 i = b i
    refine hbuniq i _ (fun l => ?_)
    show resLE (inf_le_inf_right (c.U i) (le_iSup Vl l)) (s'.1 i) = (sf l).1 i
    exact congrArg (fun s : c.sections (Vl l) => s.1 i) (hs' l)

/-- **(T-OM-A3)** ★ The invertible sheaf glued from a unit cocycle, as an `𝒪ₓ`-module. -/
noncomputable def lineBundle (c : UnitCocycle X) : X.Modules where
  val := c.presheafOfModules
  isSheaf := c.isSheaf_presheafAb

/-- **(T-OM-A3)** The sections of the line bundle over `V` are the compatible families
(the defining linear equivalence). -/
noncomputable def lineBundleSectionsEquiv (V : X.Opens) :
    Γ(c.lineBundle, V) ≃ₗ[Γ(X, V)] c.sections V where
  toFun s := s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### T-OM-A4: the chart trivialization -/

/-- **(T-OM-A4)** The chart section of the `k`-th trivialization over `V ≤ U k`:
the compatible family `(u i k)|_{V ⊓ U i}` — the coordinates, in every chart, of the
`k`-th chart's canonical basis vector. -/
noncomputable def trivSection (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.sections V :=
  ⟨fun i => (resUnit (le_inf inf_le_right (inf_le_left.trans hV)) (c.u i k)).val,
   fun i j => by
    have h0 := congrArg Units.val
      (congrArg (resUnit (le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (inf_le_left.trans (inf_le_left.trans hV)) :
        V ⊓ c.U i ⊓ c.U j ≤ (c.U i ⊓ c.U j) ⊓ c.U k)) (c.u_cocycle i j k))
    simp only [map_mul, Units.val_mul, resUnit_val, resLE_resLE] at h0 ⊢
    exact h0.symm⟩

@[simp] theorem trivSection_coe (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) (i : c.ι) :
    (c.trivSection k hV).1 i =
      (resUnit (le_inf inf_le_right (inf_le_left.trans hV)) (c.u i k)).val :=
  rfl

/-- **(T-OM-A4)** Over `V ≤ U k`, evaluation of the `k`-th component is a linear
equivalence onto `Γ(X, V)` — the chart trivialization of the glued sheaf. Inverse:
`g ↦ g • trivSection k`. Consumes `u_self` (right inverse) and `u_cocycle`
(compatibility of the inverse family). -/
noncomputable def sectionsEquivOfLE (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.sections V ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun b := resLE (le_inf le_rfl hV) (b.1 k)
  map_add' b b' := map_add _ _ _
  map_smul' r b := by
    simp only [sections.smul_coe, map_mul, resLE_resLE, resLE_rfl, RingHom.id_apply,
      smul_eq_mul]
  invFun g := g • c.trivSection k hV
  left_inv b := by
    refine Subtype.ext (funext fun i => ?_)
    have hbik := congrArg
      (⇑(resLE (X := X) (le_inf le_rfl (inf_le_left.trans hV) :
        V ⊓ c.U i ≤ V ⊓ c.U i ⊓ c.U k))) (b.2 i k)
    simp only [resUnit_val, map_mul, resLE_resLE, resLE_rfl] at hbik
    show resLE inf_le_left (resLE (le_inf le_rfl hV) (b.1 k)) *
      (resUnit (le_inf inf_le_right (inf_le_left.trans hV)) (c.u i k)).val = b.1 i
    simp only [resUnit_val, resLE_resLE]
    rw [mul_comm]
    exact hbik.symm
  right_inv g := by
    show resLE (le_inf le_rfl hV) (resLE inf_le_left g *
      (resUnit (le_inf inf_le_right (inf_le_left.trans hV)) (c.u k k)).val) = g
    rw [c.u_self k]
    simp only [map_one, Units.val_one, mul_one, resLE_resLE, resLE_rfl]

/-- **(T-OM-A4)** The trivialization is natural in `V` (compatible with restriction). -/
theorem sectionsEquivOfLE_natural (k : c.ι) {V' V : X.Opens} (hV' : V' ≤ V)
    (hV : V ≤ c.U k) (b : c.sections V) :
    c.sectionsEquivOfLE k (hV'.trans hV) (c.sectionsMap hV' b) =
      resLE hV' (c.sectionsEquivOfLE k hV b) := by
  show resLE (le_inf le_rfl (hV'.trans hV))
      (resLE (inf_le_inf_right (c.U k) hV') (b.1 k)) =
    resLE hV' (resLE (le_inf le_rfl hV) (b.1 k))
  simp only [resLE_resLE]

/-- **(T-OM-A4)** The trivialization sends the chart section to `1`. -/
theorem sectionsEquivOfLE_trivSection (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.sectionsEquivOfLE k hV (c.trivSection k hV) = 1 := by
  show resLE (le_inf le_rfl hV)
    (resUnit (le_inf inf_le_right (inf_le_left.trans hV)) (c.u k k)).val = 1
  rw [c.u_self k]
  simp only [map_one, Units.val_one]

/-! ### T-OM-A4b: invertibility (the Picard-stream predicate) -/

/-- **(T-OM-A4b)** Restriction distributes over the scalar action of sections. -/
theorem sectionsMap_smul {V' V : X.Opens} (h : V' ≤ V) (r : Γ(X, V)) (b : c.sections V) :
    c.sectionsMap h (r • b) = resLE h r • c.sectionsMap h b :=
  Subtype.ext (funext fun i => by
    show resLE _ (resLE inf_le_left r * b.1 i) =
      resLE inf_le_left (resLE h r) * resLE _ (b.1 i)
    rw [map_mul]
    simp only [resLE_resLE])

/-- **(T-OM-A4b)** The chart section is natural under restriction. -/
theorem sectionsMap_trivSection (k : c.ι) {V' V : X.Opens} (h' : V' ≤ V)
    (hV : V ≤ c.U k) :
    c.sectionsMap h' (c.trivSection k hV) = c.trivSection k (h'.trans hV) :=
  Subtype.ext (funext fun i => by
    show resLE _ ((resUnit _ (c.u i k)).val) = (resUnit _ (c.u i k)).val
    rw [resLE_resUnit_val])

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-A4b)** Multiplication into the chart section: a morphism from the structure
sheaf of the chart to the restriction of the line bundle (the trivializing map). -/
noncomputable def trivHom (k : c.ι) :
    Modules.unitObj ↑(c.U k) ⟶ (Modules.restrictFunctor (c.U k).ι).obj c.lineBundle :=
  ⟨{ app := fun W => ModuleCat.ofHom
      (Y := ((Modules.restrictFunctor (c.U k).ι).obj c.lineBundle).val.obj W)
      { toFun := fun g => (((c.U k).ι.appIso W.unop).inv.hom g) •
          c.trivSection k ((c.U k).ι_image_le W.unop)
        map_add' := fun g g' => by
          erw [map_add, add_smul]
        map_smul' := fun r g => by
          erw [map_mul, mul_smul]
          try rfl }
     naturality := fun {W W'} i => by
      refine ModuleCat.hom_ext (LinearMap.ext fun g => ?_)
      have h0 := congrArg (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) g)
        ((c.U k).ι.appIso_inv_naturality i)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h0
      have harr : (c.U k).ι.opensFunctor.op.map i =
          (homOfLE ((c.U k).ι.opensFunctor.map i.unop).le).op := by
        rw [show (c.U k).ι.opensFunctor.op.map i =
          ((c.U k).ι.opensFunctor.map i.unop).op from rfl]
        exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
      rw [harr] at h0
      show (((c.U k).ι.appIso W'.unop).inv.hom
          ((↑(c.U k) : Scheme.{u}).presheaf.map i g)) •
          c.trivSection k ((c.U k).ι_image_le W'.unop) =
        c.sectionsMap ((c.U k).ι.opensFunctor.map i.unop).le
          ((((c.U k).ι.appIso W.unop).inv.hom g) •
            c.trivSection k ((c.U k).ι_image_le W.unop))
      rw [c.sectionsMap_smul, c.sectionsMap_trivSection, h0] }⟩

/-- **(T-OM-A4b)** The trivializing map is bijective on every open of the chart:
it is the composition of the section iso of the open immersion with the inverse of the
chart trivialization. -/
theorem bijective_trivHom_app (k : c.ι)
    (W : (TopologicalSpace.Opens ↥(c.U k))ᵒᵖ) :
    Function.Bijective ((c.trivHom k).val.app W).hom := by
  have hfun : ⇑((c.trivHom k).val.app W).hom =
      (⇑(c.sectionsEquivOfLE k ((c.U k).ι_image_le W.unop)).symm) ∘
        (⇑(((c.U k).ι.appIso W.unop).inv.hom)) :=
    rfl
  rw [hfun]
  exact (c.sectionsEquivOfLE k ((c.U k).ι_image_le W.unop)).symm.bijective.comp
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)

/-- **(T-OM-A4b)** ★ The glued line bundle is an invertible `𝒪ₓ`-module in the sense of
the Picard stream (`Scheme.Modules.IsInvertible`): the cover `U` trivializes it, by the
`isIso_of_bijective_app_on_basis` route with the bijectivity supplied by
`sectionsEquivOfLE` at every open below a chart. -/
theorem lineBundle_isInvertible : Modules.IsInvertible c.lineBundle := by
  refine ⟨c.ι, c.U, c.iSup_eq_top, fun k => ?_⟩
  haveI : IsIso (c.trivHom k) := by
    refine Modules.isIso_of_bijective_app_on_basis _ Set.univ
      (fun x U hxU => ⟨U, trivial, hxU, le_rfl⟩) ?_
    intro W _
    exact c.bijective_trivHom_app k (Opposite.op W)
  exact ⟨(Modules.restrictFunctorIsoPullback (c.U k).ι).symm.app c.lineBundle ≪≫
    (asIso (c.trivHom k)).symm⟩

/-! ### T-OM-A5: bases and the torsor structure -/

/-- **(T-OM-A5)** A section is a basis if it is a unit in every chart. For sections of an
invertible sheaf this is the correct global notion of "nowhere-vanishing generator"; over
`V ≤ U k` it coincides with "the trivialization sends it to a unit"
(`isBasis_iff_isUnit`). -/
def IsBasis {V : X.Opens} (b : c.sections V) : Prop :=
  ∀ i, IsUnit (b.1 i)

/-- **(T-OM-A5)** The chart section is a basis. -/
theorem isBasis_trivSection (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) :
    c.IsBasis (c.trivSection k hV) := fun i =>
  (resUnit (le_inf inf_le_right (inf_le_left.trans hV)) (c.u i k)).isUnit

/-- **(T-OM-A5)** Restriction preserves bases. -/
theorem IsBasis.sectionsMap {V' V : X.Opens} (h : V' ≤ V) {b : c.sections V}
    (hb : c.IsBasis b) : c.IsBasis (c.sectionsMap h b) := fun i =>
  (hb i).map (resLE (inf_le_inf_right (c.U i) h))

/-- **(T-OM-A5)** Unit scaling preserves and reflects bases. -/
theorem isBasis_smul_iff {V : X.Opens} (g : Γ(X, V)ˣ) (b : c.sections V) :
    c.IsBasis (g.val • b) ↔ c.IsBasis b := by
  have hres : ∀ i : c.ι, IsUnit (resLE (inf_le_left (b := c.U i)) g.val) := fun i => by
    rw [← resUnit_val inf_le_left g]
    exact (resUnit inf_le_left g).isUnit
  constructor
  · intro h i
    have := h i
    rw [sections.smul_coe, IsUnit.mul_iff] at this
    exact this.2
  · intro h i
    rw [sections.smul_coe, IsUnit.mul_iff]
    exact ⟨hres i, h i⟩

/-- **(T-OM-A5)** Over `V ≤ U k`, a section is a basis iff its trivialization is a unit. -/
theorem isBasis_iff_isUnit (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) (b : c.sections V) :
    c.IsBasis b ↔ IsUnit (c.sectionsEquivOfLE k hV b) := by
  constructor
  · intro h
    exact (h k).map (resLE (le_inf le_rfl hV))
  · intro h i
    -- recover the k-component's unitness from its transport
    have hk : IsUnit (b.1 k) := by
      have h' := h.map (resLE (X := X) (inf_le_left (b := c.U k)))
      rw [show resLE inf_le_left (c.sectionsEquivOfLE k hV b) =
        resLE inf_le_left (resLE (le_inf le_rfl hV) (b.1 k)) from rfl,
        resLE_resLE, resLE_rfl] at h'
      exact h'
    -- the i-component is a unit multiple of the (restricted) k-component
    have hbik := congrArg
      (⇑(resLE (X := X) (le_inf le_rfl (inf_le_left.trans hV) :
        V ⊓ c.U i ≤ V ⊓ c.U i ⊓ c.U k))) (b.2 i k)
    simp only [resUnit_val, map_mul, resLE_resLE, resLE_rfl] at hbik
    rw [hbik, IsUnit.mul_iff]
    constructor
    · rw [← resUnit_val]
      exact (resUnit _ (c.u i k)).isUnit
    · exact hk.map _
  -- (the `rfl`-show unfolds the equivalence's `toFun`)

/-- **(T-OM-A5)** The unit action on bases is free. -/
theorem smul_left_injective {V : X.Opens} {b : c.sections V} (hb : c.IsBasis b)
    {g g' : Γ(X, V)} (h : g • b = g' • b) : g = g' := by
  have hcover : V ≤ iSup (fun i : c.ι => V ⊓ c.U i) := by
    intro x hxV
    obtain ⟨i, hxi⟩ := c.covers x
    exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i : c.ι => V ⊓ c.U i) V
    (fun i => homOfLE inf_le_left) hcover g g' (fun i => ?_)
  have hcomp := congrArg (fun s : c.sections V => s.1 i) h
  simp only [sections.smul_coe] at hcomp
  exact (hb i).mul_left_cancel (by
    rw [mul_comm (b.1 i) _, mul_comm (b.1 i) _]
    exact hcomp)

/-- **(T-OM-A5)** ★ The torsor property: any two sections with the first a basis differ
by a unique scalar — the ratios in each chart agree on overlaps and glue. This is the
`𝔾ₘ`-torsor trivialization of the board ("ω3 = T-A4's trivialization"): the scalar is a
unit iff the second section is a basis (`isBasis_smul_iff` + uniqueness). -/
theorem exists_unique_smul_eq {V : X.Opens} {b : c.sections V} (hb : c.IsBasis b)
    (b' : c.sections V) : ∃! g : Γ(X, V), g • b = b' := by
  classical
  -- the chartwise inverse identity
  have hIB : ∀ i : c.ι, ((hb i).unit⁻¹).val * b.1 i = 1 := fun i => (hb i).val_inv_mul
  -- the chartwise ratios
  set r : ∀ i : c.ι, Γ(X, V ⊓ c.U i) :=
    fun i => ((hb i).unit⁻¹).val * b'.1 i with hr
  have hrb : ∀ i : c.ι, r i * b.1 i = b'.1 i := fun i => by
    calc r i * b.1 i = (((hb i).unit⁻¹).val * b.1 i) * b'.1 i := by rw [hr]; ring
      _ = b'.1 i := by rw [hIB i, one_mul]
  -- the cover of `V` by the chart pieces
  have hcover : V ≤ iSup (fun i : c.ι => V ⊓ c.U i) := by
    intro x hxV
    obtain ⟨i, hxi⟩ := c.covers x
    exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩
  -- the ratios agree on overlaps: the transition units cancel
  have hcpt : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i : c.ι => V ⊓ c.U i) r := by
    intro i j
    show resLE (Opens.infLELeft (V ⊓ c.U i) (V ⊓ c.U j)).le (r i) =
      resLE (Opens.infLERight (V ⊓ c.U i) (V ⊓ c.U j)).le (r j)
    have hle : (V ⊓ c.U i) ⊓ (V ⊓ c.U j) ≤ V ⊓ c.U i ⊓ c.U j :=
      le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)
    have hbeq := congrArg (⇑(resLE (X := X) hle)) (b.2 i j)
    have hbeq' := congrArg (⇑(resLE (X := X) hle)) (b'.2 i j)
    simp only [resUnit_val, map_mul, resLE_resLE] at hbeq hbeq'
    -- abbreviations (all restrictions land in `(V ⊓ U i) ⊓ (V ⊓ U j)`)
    set hL := (Opens.infLELeft (V ⊓ c.U i) (V ⊓ c.U j)).le
    set hR := (Opens.infLERight (V ⊓ c.U i) (V ⊓ c.U j)).le
    have hA : IsUnit (resLE hL (b.1 i)) := (hb i).map _
    have hIA : resLE hL ((hb i).unit⁻¹).val * resLE hL (b.1 i) = 1 := by
      rw [← map_mul, hIB i, map_one]
    have hJB : resLE hR ((hb j).unit⁻¹).val * resLE hR (b.1 j) = 1 := by
      rw [← map_mul, hIB j, map_one]
    -- the two compatibility equations, in the collapsed form
    have hbi : resLE hL (b.1 i) = resLE (hle.trans
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (c.u i j).val *
        resLE hR (b.1 j) := by
      simpa only [resLE_resLE] using hbeq
    have hbi' : resLE hL (b'.1 i) = resLE (hle.trans
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (c.u i j).val *
        resLE hR (b'.1 j) := by
      simpa only [resLE_resLE] using hbeq'
    refine hA.mul_right_cancel ?_
    calc resLE hL (r i) * resLE hL (b.1 i)
        = (resLE hL ((hb i).unit⁻¹).val * resLE hL (b.1 i)) * resLE hL (b'.1 i) := by
          simp only [hr, map_mul]; ring
      _ = resLE hL (b'.1 i) := by rw [hIA, one_mul]
      _ = resLE (hle.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
            (c.u i j).val * resLE hR (b'.1 j) := hbi'
      _ = (resLE hR ((hb j).unit⁻¹).val * resLE hR (b.1 j)) *
            (resLE (hle.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
              (c.u i j).val * resLE hR (b'.1 j)) := by rw [hJB, one_mul]
      _ = resLE hR (r j) * (resLE (hle.trans
            (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (c.u i j).val *
            resLE hR (b.1 j)) := by simp only [hr, map_mul]; ring
      _ = resLE hR (r j) * resLE hL (b.1 i) := by rw [← hbi]
  -- glue the ratios
  obtain ⟨g, hg, hguniq⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf
    (fun i : c.ι => V ⊓ c.U i) V (fun i => homOfLE inf_le_left) hcover r hcpt
  refine ⟨g, ?_, ?_⟩
  · refine Subtype.ext (funext fun i => ?_)
    show resLE inf_le_left g * b.1 i = b'.1 i
    rw [show resLE (inf_le_left (b := c.U i)) g = r i from hg i]
    exact hrb i
  · intro g' hg'
    refine hguniq g' (fun i => ?_)
    show resLE inf_le_left g' = r i
    have hcomp := congrArg (fun s : c.sections V => s.1 i) hg'
    simp only [sections.smul_coe] at hcomp
    refine (hb i).mul_left_cancel ?_
    rw [mul_comm (b.1 i) _, mul_comm (b.1 i) _, hcomp, ← hrb i]

/-! ### T-OM-A6: glueing units over an open from affine-local data -/

end UnitCocycle

/-- The underlying sections of a restriction-compatible family of units agree after
restriction to a common smaller affine open. -/
private theorem unit_glue_res {X : Scheme.{u}} {W : X.Opens}
    (data : ∀ V : X.affineOpens, V.1 ≤ W → Γ(X, V.1)ˣ)
    (compat : ∀ (V V' : X.affineOpens) (hV : V.1 ≤ W) (h : V'.1 ≤ V.1),
      resUnit h (data V hV) = data V' (h.trans hV))
    {V V' : X.affineOpens} (hV : V.1 ≤ W) (h : V'.1 ≤ V.1) :
    resLE h (data V hV).val = (data V' (h.trans hV)).val := by
  have := congrArg Units.val (compat V V' hV h)
  simpa using this

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
  classical
  -- the affine cover of `W`
  set κ := {V : X.affineOpens // V.1 ≤ W} with hκ
  set 𝒰 : κ → X.Opens := fun p => p.1.1 with h𝒰
  have hcover : W ≤ iSup 𝒰 := by
    intro x hxW
    obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, hVW⟩, hxV⟩
  -- covering an intersection of two affine opens below `W` by affines
  have hcoverInf : ∀ p q : κ, 𝒰 p ⊓ 𝒰 q ≤
      iSup (fun r : {V : X.affineOpens // V.1 ≤ 𝒰 p ⊓ 𝒰 q} => r.1.1) := by
    intro p q x hx
    obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, hVW⟩, hxV⟩
  -- the underlying sections are pairwise compatible
  have hpair : TopCat.Presheaf.IsCompatible X.sheaf.1 𝒰 (fun p => (data p.1 p.2).val) := by
    intro p q
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun r : {V : X.affineOpens // V.1 ≤ 𝒰 p ⊓ 𝒰 q} => r.1.1) (𝒰 p ⊓ 𝒰 q)
      (fun r => homOfLE r.2) (hcoverInf p q) _ _ (fun r => ?_)
    show resLE r.2 (resLE inf_le_left (data p.1 p.2).val) =
      resLE r.2 (resLE inf_le_right (data q.1 q.2).val)
    rw [resLE_resLE, resLE_resLE,
      unit_glue_res data compat p.2 (r.2.trans inf_le_left),
      unit_glue_res data compat q.2 (r.2.trans inf_le_right)]
  -- glue the underlying section
  obtain ⟨g₀, hg₀, hg₀uniq⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf 𝒰 W
    (fun p => homOfLE p.2) hcover (fun p => (data p.1 p.2).val) hpair
  have hg₀' : ∀ (V : X.affineOpens) (hV : V.1 ≤ W), resLE hV g₀ = (data V hV).val :=
    fun V hV => hg₀ ⟨V, hV⟩
  -- the glued section is a unit (it is one near every point)
  have hunit : IsUnit g₀ := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hxW
    obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    have hgerm : X.presheaf.germ W x hxW g₀ =
        X.presheaf.germ V x hxV (resLE hVW g₀) := by
      rw [show resLE hVW g₀ = (X.presheaf.map (homOfLE hVW).op).hom g₀ from rfl]
      exact (X.presheaf.germ_res_apply (homOfLE hVW) x hxV g₀).symm
    rw [hgerm, hg₀' ⟨V, hVaff⟩ hVW]
    exact ((data ⟨V, hVaff⟩ hVW).isUnit).map _
  refine ⟨hunit.unit, fun V hV => ?_, fun g' hg' => ?_⟩
  · refine Units.ext ?_
    rw [resUnit_val, IsUnit.unit_spec]
    exact hg₀' V hV
  · refine Units.ext ?_
    rw [IsUnit.unit_spec]
    refine hg₀uniq g'.val (fun p => ?_)
    show resLE p.2 g'.val = (data p.1 p.2).val
    have := congrArg Units.val (hg' p.1 p.2)
    simpa using this

/-- **(T-OM-A6)** Units of the section ring agreeing on a covering family of subopens
are equal (separation). -/
theorem unit_ext_of_res_cover (X : Scheme.{u}) {W : X.Opens} {g g' : Γ(X, W)ˣ}
    {ι' : Type u} (𝒰 : ι' → X.Opens) (h𝒰 : ∀ l, 𝒰 l ≤ W) (hcover : W ≤ iSup 𝒰)
    (h : ∀ l, resUnit (h𝒰 l) g = resUnit (h𝒰 l) g') : g = g' := by
  refine Units.ext (TopCat.Sheaf.eq_of_locally_eq' X.sheaf 𝒰 W (fun l => homOfLE (h𝒰 l))
    hcover g.val g'.val (fun l => ?_))
  show resLE (h𝒰 l) g.val = resLE (h𝒰 l) g'.val
  have := congrArg Units.val (h l)
  simpa using this

/-- **(T-OM-A6)** Units of the section ring agreeing on all affine opens below `W`
are equal (separation over the affine basis). -/
theorem unit_ext_of_affine_res (X : Scheme.{u}) {W : X.Opens} {g g' : Γ(X, W)ˣ}
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W), resUnit hV g = resUnit hV g') : g = g' := by
  have hcover : W ≤ iSup (fun p : {V : X.affineOpens // V.1 ≤ W} => p.1.1) := by
    intro x hxW
    obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, hVW⟩, hxV⟩
  refine Units.ext (TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun p : {V : X.affineOpens // V.1 ≤ W} => p.1.1) W (fun p => homOfLE p.2) hcover
    g.val g'.val (fun p => ?_))
  show resLE p.2 g.val = resLE p.2 g'.val
  have := congrArg Units.val (h p.1 p.2)
  simpa using this

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

namespace Compat

variable {c} {c' : UnitCocycle X} (κ : c.Compat c')

/-- **(T-OM-A7)** The inverse comparison data: inverted units on the swapped overlaps. -/
noncomputable def symm : c'.Compat c where
  w j i := resUnit (show c'.U j ⊓ c.U i ≤ c.U i ⊓ c'.U j by order) (κ.w i j)⁻¹
  left j j' i := by
    have h := congrArg (resUnit
      (show c'.U j ⊓ c'.U j' ⊓ c.U i ≤ c.U i ⊓ c'.U j ⊓ c'.U j' by order))
      (κ.right i j j')
    simp only [map_mul, map_inv, resUnit_resUnit] at h ⊢
    rw [← h]
    group
  right j i i' := by
    have h := congrArg (resUnit
      (show c'.U j ⊓ c.U i ⊓ c.U i' ≤ c.U i ⊓ c.U i' ⊓ c'.U j by order))
      (κ.left i i' j)
    simp only [map_mul, map_inv, resUnit_resUnit] at h ⊢
    rw [← h]
    group

variable {V : X.Opens}

/-- The value-level `right` law on an arbitrary open below a mixed triple overlap. -/
private theorem right_val {T : X.Opens} (i : c.ι) (j j' : c'.ι)
    (hT : T ≤ c.U i ⊓ c'.U j ⊓ c'.U j') :
    resLE (hT.trans (by order)) (κ.w i j).val *
      resLE (hT.trans (by order)) (c'.u j j').val =
      resLE (hT.trans (by order)) (κ.w i j').val := by
  have h := congrArg Units.val (congrArg (resUnit hT) (κ.right i j j'))
  simpa only [map_mul, Units.val_mul, resUnit_val, resLE_resLE] using h

/-- The value-level `left` law on an arbitrary open below a mixed triple overlap. -/
private theorem left_val {T : X.Opens} (i i' : c.ι) (j : c'.ι)
    (hT : T ≤ c.U i ⊓ c.U i' ⊓ c'.U j) :
    resLE (hT.trans (by order)) (c.u i i').val *
      resLE (hT.trans (by order)) (κ.w i' j).val =
      resLE (hT.trans (by order)) (κ.w i j).val := by
  have h := congrArg Units.val (congrArg (resUnit hT) (κ.left i i' j))
  simpa only [map_mul, Units.val_mul, resUnit_val, resLE_resLE] using h

/-- The value-level compatibility of a section on an arbitrary open below a
double overlap. -/
private theorem sections_compat_val {cc : UnitCocycle X} (b : cc.sections V)
    (i j : cc.ι) {T : X.Opens} (hT : T ≤ V ⊓ cc.U i ⊓ cc.U j) :
    resLE (hT.trans (by order)) (b.1 i) =
      resLE (hT.trans (by order)) (cc.u i j).val *
        resLE (hT.trans (by order)) (b.1 j) := by
  have h := congrArg (⇑(resLE (X := X) hT)) (b.2 i j)
  simpa only [map_mul, resUnit_val, resLE_resLE] using h

/-- **(T-OM-A7)** The transported component: glued from `w i j · b' j` over the
`c'`-cover of `V ⊓ U i`, packaged with its defining local description. -/
private noncomputable def transportAux (b' : c'.sections V) (i : c.ι) :
    { s : Γ(X, V ⊓ c.U i) // ∀ j : c'.ι,
        resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order) s =
          resLE (show V ⊓ c.U i ⊓ c'.U j ≤ c.U i ⊓ c'.U j by order) (κ.w i j).val *
          resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c'.U j by order) (b'.1 j) } := by
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.sheaf
    (fun j : c'.ι => V ⊓ c.U i ⊓ c'.U j) (V ⊓ c.U i)
    (fun j => homOfLE (by order)) (by
      intro x hx
      obtain ⟨j, hxj⟩ := c'.covers x
      exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩)
    (fun j => resLE (show V ⊓ c.U i ⊓ c'.U j ≤ c.U i ⊓ c'.U j by order) (κ.w i j).val *
      resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c'.U j by order) (b'.1 j)) (by
      intro j j'
      show resLE (Opens.infLELeft _ _).le _ = resLE (Opens.infLERight _ _).le _
      simp only [map_mul, resLE_resLE]
      rw [sections_compat_val b' j j'
          (show (V ⊓ c.U i ⊓ c'.U j) ⊓ (V ⊓ c.U i ⊓ c'.U j') ≤ V ⊓ c'.U j ⊓ c'.U j'
            by order),
        ← κ.right_val i j j'
          (show (V ⊓ c.U i ⊓ c'.U j) ⊓ (V ⊓ c.U i ⊓ c'.U j') ≤ c.U i ⊓ c'.U j ⊓ c'.U j'
            by order)]
      ring)
  exact ⟨hglue.choose, fun j => (hglue.choose_spec.1 j :)⟩

/-- **(T-OM-A7)** Comparison data transports sections: the `i`-component of the image
is glued from `w i j · b' j` over the `c'`-cover of `V ⊓ U i`. -/
noncomputable def transportFun (b' : c'.sections V) : c.sections V :=
  ⟨fun i => (κ.transportAux b' i).1, by
    intro i i'
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun j : c'.ι => V ⊓ c.U i ⊓ c.U i' ⊓ c'.U j) (V ⊓ c.U i ⊓ c.U i')
      (fun j => homOfLE (by order)) (by
        intro x hx
        obtain ⟨j, hxj⟩ := c'.covers x
        exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩) _ _ (fun j => ?_)
    have hsi := congrArg (⇑(resLE (X := X)
      (show V ⊓ c.U i ⊓ c.U i' ⊓ c'.U j ≤ V ⊓ c.U i ⊓ c'.U j by order)))
      ((κ.transportAux b' i).2 j)
    have hsi' := congrArg (⇑(resLE (X := X)
      (show V ⊓ c.U i ⊓ c.U i' ⊓ c'.U j ≤ V ⊓ c.U i' ⊓ c'.U j by order)))
      ((κ.transportAux b' i').2 j)
    show resLE (show V ⊓ c.U i ⊓ c.U i' ⊓ c'.U j ≤ V ⊓ c.U i ⊓ c.U i' by order)
        (resLE (inf_le_left (b := c.U i')) ((κ.transportAux b' i).1)) =
      resLE (show V ⊓ c.U i ⊓ c.U i' ⊓ c'.U j ≤ V ⊓ c.U i ⊓ c.U i' by order)
        ((resUnit (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c.u i i')).val *
          resLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
            ((κ.transportAux b' i').1))
    simp only [map_mul, resUnit_val, resLE_resLE] at hsi hsi' ⊢
    rw [hsi, hsi', ← mul_assoc, κ.left_val i i' j (by order)]⟩

@[simp] theorem transportFun_res (b' : c'.sections V) (i : c.ι) (j : c'.ι) :
    resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order) ((κ.transportFun b').1 i) =
      resLE (show V ⊓ c.U i ⊓ c'.U j ≤ c.U i ⊓ c'.U j by order) (κ.w i j).val *
      resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c'.U j by order) (b'.1 j) :=
  (κ.transportAux b' i).2 j

/-- Two sections agreeing under all the local descriptions agree (separation). -/
private theorem sections_ext {cc : UnitCocycle X} (s t : cc.sections V)
    (h : ∀ (i : cc.ι) (W : X.Opens) (hW : W ≤ V ⊓ cc.U i),
      resLE hW (s.1 i) = resLE hW (t.1 i)) : s = t :=
  Subtype.ext (funext fun i => by
    simpa using h i (V ⊓ cc.U i) le_rfl)

/-- **(T-OM-A7)** Comparison data transports sections: the linear equivalence. -/
noncomputable def sectionsEquiv (V : X.Opens) :
    c'.sections V ≃ₗ[Γ(X, V)] c.sections V where
  toFun := κ.transportFun
  map_add' b₁ b₂ := by
    refine Subtype.ext (funext fun i => ?_)
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun j : c'.ι => V ⊓ c.U i ⊓ c'.U j) (V ⊓ c.U i)
      (fun j => homOfLE (by order)) (by
        intro x hx
        obtain ⟨j, hxj⟩ := c'.covers x
        exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩) _ _ (fun j => ?_)
    show resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order)
        ((κ.transportFun (b₁ + b₂)).1 i) =
      resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order)
        ((κ.transportFun b₁ + κ.transportFun b₂).1 i)
    rw [show (κ.transportFun b₁ + κ.transportFun b₂).1 i =
      (κ.transportFun b₁).1 i + (κ.transportFun b₂).1 i from rfl, map_add,
      κ.transportFun_res, κ.transportFun_res, κ.transportFun_res,
      show (b₁ + b₂).1 j = b₁.1 j + b₂.1 j from rfl, map_add, mul_add]
  map_smul' r b' := by
    refine Subtype.ext (funext fun i => ?_)
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun j : c'.ι => V ⊓ c.U i ⊓ c'.U j) (V ⊓ c.U i)
      (fun j => homOfLE (by order)) (by
        intro x hx
        obtain ⟨j, hxj⟩ := c'.covers x
        exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩) _ _ (fun j => ?_)
    show resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order)
        ((κ.transportFun (r • b')).1 i) =
      resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order)
        (((r : Γ(X, V)) • κ.transportFun b').1 i)
    rw [show ((r : Γ(X, V)) • κ.transportFun b').1 i =
      resLE inf_le_left r * (κ.transportFun b').1 i from rfl, map_mul,
      κ.transportFun_res, κ.transportFun_res,
      show (r • b').1 j = resLE inf_le_left r * b'.1 j from rfl, map_mul]
    simp only [resLE_resLE]
    ring
  invFun := κ.symm.transportFun
  left_inv b' := by
    refine Subtype.ext (funext fun j => ?_)
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun i : c.ι => V ⊓ c'.U j ⊓ c.U i) (V ⊓ c'.U j)
      (fun i => homOfLE (by order)) (by
        intro x hx
        obtain ⟨i, hxi⟩ := c.covers x
        exact Opens.mem_iSup.mpr ⟨i, hx, hxi⟩) _ _ (fun i => ?_)
    show resLE (show V ⊓ c'.U j ⊓ c.U i ≤ V ⊓ c'.U j by order)
        ((κ.symm.transportFun (κ.transportFun b')).1 j) =
      resLE (show V ⊓ c'.U j ⊓ c.U i ≤ V ⊓ c'.U j by order) (b'.1 j)
    rw [κ.symm.transportFun_res (κ.transportFun b') j i]
    have h2 := congrArg (⇑(resLE (X := X)
      (show V ⊓ c'.U j ⊓ c.U i ≤ V ⊓ c.U i ⊓ c'.U j by order)))
      (κ.transportFun_res b' i j)
    simp only [map_mul, resLE_resLE] at h2
    rw [show κ.symm.w j i = resUnit
      (show c'.U j ⊓ c.U i ≤ c.U i ⊓ c'.U j by order) (κ.w i j)⁻¹ from rfl]
    rw [resLE_resUnit_val, map_inv, h2, ← mul_assoc, inv_resUnit_mul_resLE, one_mul]
  right_inv b := by
    refine Subtype.ext (funext fun i => ?_)
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun j : c'.ι => V ⊓ c.U i ⊓ c'.U j) (V ⊓ c.U i)
      (fun j => homOfLE (by order)) (by
        intro x hx
        obtain ⟨j, hxj⟩ := c'.covers x
        exact Opens.mem_iSup.mpr ⟨j, hx, hxj⟩) _ _ (fun j => ?_)
    show resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order)
        ((κ.transportFun (κ.symm.transportFun b)).1 i) =
      resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order) (b.1 i)
    rw [κ.transportFun_res (κ.symm.transportFun b) i j]
    have h2 := congrArg (⇑(resLE (X := X)
      (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c'.U j ⊓ c.U i by order)))
      (κ.symm.transportFun_res b j i)
    simp only [map_mul, resLE_resLE] at h2
    rw [h2]
    rw [show κ.symm.w j i = resUnit
      (show c'.U j ⊓ c.U i ≤ c.U i ⊓ c'.U j by order) (κ.w i j)⁻¹ from rfl]
    rw [resLE_resUnit_val, map_inv, ← mul_assoc,
      resLE_mul_inv_resUnit, one_mul]

/-- **(T-OM-A7)** One direction of basis preservation: transport of a basis is a basis
(each transported component is locally a unit multiple of a unit, and a section that is
locally a unit is a unit). -/
theorem isBasis_transportFun {b' : c'.sections V} (hb' : c'.IsBasis b') :
    c.IsBasis (κ.transportFun b') := by
  intro i
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  obtain ⟨j, hxj⟩ := c'.covers x
  have hres := κ.transportFun_res b' i j
  have hxij : x ∈ V ⊓ c.U i ⊓ c'.U j := ⟨hx, hxj⟩
  have hgerm : X.presheaf.germ (V ⊓ c.U i) x hx ((κ.transportFun b').1 i) =
      X.presheaf.germ (V ⊓ c.U i ⊓ c'.U j) x hxij
        (resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c.U i by order)
          ((κ.transportFun b').1 i)) :=
    (X.presheaf.germ_res_apply (homOfLE (by order)) x hxij _).symm
  rw [hgerm, hres, map_mul]
  refine IsUnit.mul ?_ ?_
  · exact ((resUnit (show V ⊓ c.U i ⊓ c'.U j ≤ c.U i ⊓ c'.U j by order)
      (κ.w i j)).isUnit).map _
  · exact ((hb' j).map (resLE (show V ⊓ c.U i ⊓ c'.U j ≤ V ⊓ c'.U j by order))).map _

/-- **(T-OM-A7)** Comparison transport preserves bases. -/
theorem isBasis_sectionsEquiv {V : X.Opens} (b : c'.sections V) :
    c.IsBasis (κ.sectionsEquiv V b) ↔ c'.IsBasis b := by
  constructor
  · intro h
    have := κ.symm.isBasis_transportFun (b' := κ.sectionsEquiv V b) h
    rwa [show κ.symm.transportFun (κ.sectionsEquiv V b) = b from
      (κ.sectionsEquiv V).left_inv b] at this
  · intro h
    exact κ.isBasis_transportFun h

end Compat

/-! ### T-OM-A7b: pullback of a cocycle along a morphism of schemes -/

/-- **(T-OM-A7b)** The pullback cocycle along `f : Y ⟶ X`: preimage cover, transition
units mapped by `f`'s section maps on preimages. -/
noncomputable def pullbackCocycle (c : UnitCocycle X) (f : Y ⟶ X) : UnitCocycle Y where
  ι := c.ι
  U i := f ⁻¹ᵁ c.U i
  covers y := (c.covers (f.base y)).imp fun _ hi => hi
  u i j := Units.map ((f.appLE (c.U i ⊓ c.U j) (f ⁻¹ᵁ c.U i ⊓ f ⁻¹ᵁ c.U j)
    (fun _ hy => ⟨hy.1, hy.2⟩)).hom).toMonoidHom (c.u i j)
  u_self i := by
    rw [c.u_self i]
    exact map_one _
  u_cocycle i j k := by
    refine Units.ext ?_
    have hX := congrArg Units.val (c.u_cocycle i j k)
    simp only [Units.val_mul, resUnit_val] at hX
    have hY := congrArg ((f.appLE (c.U i ⊓ c.U j ⊓ c.U k)
      ((f ⁻¹ᵁ c.U i ⊓ f ⁻¹ᵁ c.U j) ⊓ f ⁻¹ᵁ c.U k)
      (fun _ hy => ⟨⟨hy.1.1, hy.1.2⟩, hy.2⟩)).hom) hX
    rw [map_mul] at hY
    simp only [Units.val_mul, resUnit_val, Units.coe_map, MonoidHom.coe_coe]
    simp only [appLE_resLE] at hY
    erw [resLE_appLE, resLE_appLE, resLE_appLE]
    exact hY
  -- (the `resLE_appLE`/`appLE_resLE` collapses land on the same pullback maps,
  --  which agree by proof irrelevance of the openness inequalities)

@[simp] theorem pullbackCocycle_u (f : Y ⟶ X) (i j : c.ι) :
    (c.pullbackCocycle f).u i j =
      Units.map ((f.appLE (c.U i ⊓ c.U j) (f ⁻¹ᵁ c.U i ⊓ f ⁻¹ᵁ c.U j)
        (fun _ hy => ⟨hy.1, hy.2⟩)).hom).toMonoidHom (c.u i j) :=
  rfl

/-- Restrictions of the pulled-back transition units are pullbacks of the units. -/
theorem pullbackCocycle_resUnit (f : Y ⟶ X) (i j : c.ι) {W' : Y.Opens}
    (h : W' ≤ (c.pullbackCocycle f).U i ⊓ (c.pullbackCocycle f).U j) :
    resUnit h ((c.pullbackCocycle f).u i j) =
      Units.map ((f.appLE (c.U i ⊓ c.U j) W'
        (fun _ hy => ⟨(h hy).1, (h hy).2⟩)).hom).toMonoidHom (c.u i j) := by
  refine Units.ext ?_
  show resLE h (((c.pullbackCocycle f).u i j).val) =
    (f.appLE (c.U i ⊓ c.U j) W' (fun _ hy => ⟨(h hy).1, (h hy).2⟩)).hom (c.u i j).val
  rw [show (((c.pullbackCocycle f).u i j).val) =
    (f.appLE (c.U i ⊓ c.U j) (f ⁻¹ᵁ c.U i ⊓ f ⁻¹ᵁ c.U j)
      (fun _ hy => ⟨hy.1, hy.2⟩)).hom (c.u i j).val from rfl]
  erw [resLE_appLE]

/-- **(T-OM-A7b)** Componentwise pullback of sections along `f`. -/
noncomputable def sectionsPullback (f : Y ⟶ X) {V : X.Opens} (b : c.sections V) :
    (c.pullbackCocycle f).sections (f ⁻¹ᵁ V) :=
  ⟨fun i => (f.appLE (V ⊓ c.U i) (f ⁻¹ᵁ V ⊓ f ⁻¹ᵁ c.U i)
      (fun _ hy => ⟨hy.1, hy.2⟩)).hom (b.1 i), by
    intro i j
    have hX := b.2 i j
    simp only [resUnit_val] at hX
    have hY := congrArg ((f.appLE (V ⊓ c.U i ⊓ c.U j)
      ((f ⁻¹ᵁ V ⊓ f ⁻¹ᵁ c.U i) ⊓ f ⁻¹ᵁ c.U j)
      (fun _ hy => ⟨⟨hy.1.1, hy.1.2⟩, hy.2⟩)).hom) hX
    rw [map_mul] at hY
    simp only [pullbackCocycle_u, resUnit_val, Units.coe_map, MonoidHom.coe_coe]
    simp only [appLE_resLE] at hY
    erw [resLE_appLE, resLE_appLE, resLE_appLE]
    exact hY⟩

/-- **(T-OM-A7b)** Pullback of a basis is a basis (ring maps preserve units). -/
theorem isBasis_sectionsPullback (f : Y ⟶ X) {V : X.Opens} {b : c.sections V}
    (hb : c.IsBasis b) : (c.pullbackCocycle f).IsBasis (c.sectionsPullback f b) :=
  fun i => (hb i).map _

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-A7b)** Pullback of sections is semilinear over the section comparison. -/
theorem sectionsPullback_smul (f : Y ⟶ X) {V : X.Opens} (r : Γ(X, V)) (b : c.sections V) :
    c.sectionsPullback f (r • b) =
      ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom r) • c.sectionsPullback f b := by
  refine Subtype.ext (funext fun i => ?_)
  show (f.appLE (V ⊓ c.U i) (f ⁻¹ᵁ V ⊓ (c.pullbackCocycle f).U i)
      (fun _ hy => ⟨hy.1, hy.2⟩)).hom (resLE inf_le_left r * b.1 i) =
    resLE inf_le_left ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom r) *
      (f.appLE (V ⊓ c.U i) (f ⁻¹ᵁ V ⊓ (c.pullbackCocycle f).U i)
        (fun _ hy => ⟨hy.1, hy.2⟩)).hom (b.1 i)
  rw [map_mul]
  congr 1
  rw [appLE_resLE, resLE_appLE]

end UnitCocycle

end AlgebraicGeometry.Scheme
