/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModuleMul
import ModularCurves.EllipticCurve.MulByHomDegree
import ModularCurves.EllipticCurve.SectionCoordinates
import ModularCurves.EllipticCurve.AffineSectionSpecPoints
import ModularCurves.EllipticCurve.PoleSheafModel
import ModularCurves.LevelStructure.CartierDivisor
import HasseWeil.Pic0.TheoremOfSquareDivisorForm

/-!
# The theorem of the square as a module triviality over a field (T10-asm)

Over a field `k`, for an elliptic Weierstrass curve `W` and points `P`, `Q` of `W`, the ideal
modules of the four sections `P`, `Q`, `P + Q`, `0` of the projective model satisfy

  `I(P) ⊗_{𝒪} I(Q) ≅ I(P+Q) ⊗_{𝒪} I(0)`.

This is the field-level shadow of the relative theorem of the square
(`Picard/SelfAdjointN.lean`, leaf (i)), and the target of Blocker 3 of the Katz–Mazur route.

## The two halves of the bridge, and how they compose

* `Picard/IdealModuleMul.lean` turns a *sum of divisors* into a *tensor product*: given one
  affine cover with nonzerodivisor generators, `I(J₁) ⊗ I(J₂) ≅ I(J₁ · J₂)`.
* `Picard/PrincipalIdealModuleIso.lean` turns a *principal divisor* into an *isomorphism*: given
  local numerators and denominators satisfying the cocycle identity, `I(J₂) ≅ I(J₁)`.

`SquareChartData JP JQ JR JO` is exactly the data that feeds both at once: one affine cover, a
nonzerodivisor generator for each of the four ideal sheaves, and the cocycle identity for the
ratio `(genP · genQ) / (genR · genO)`. `nonempty_tensorObj_idealModule_iso_of_squareChartData`
composes

  `I(JP) ⊗ I(JQ) ≅ I(JP·JQ) ≅ I(JR·JO) ≅ I(JR) ⊗ I(JO)`,

the middle isomorphism being multiplication by the rational function the cocycle presents.
Nothing about curves, fields or smoothness is used: it holds on an arbitrary scheme.

`squareChartDataOfRatio` is the convenient constructor on an *integral* scheme: there the
cocycle identity is implied by a single equation `genP·genQ = g · (genR·genO)` in the function
field, because `Γ(C, U) ↪ K(C)` for every nonempty open (`Scheme.germToFunctionField_injective`).
This is the shape in which a rational function with a prescribed divisor is actually met.

`exists_affineOpen_span_nzd_four` builds the *cover* half of a chart datum out of pointwise
local principality, and `nonempty_squareChartData_diagonal` builds the whole datum whenever the
two sides carry the same pair of divisors (ratio `1`).

## The generators may be chosen before the function

`nonempty_squareChartData_of_span_ratio` and its pointwise form
`nonempty_squareChartData_of_ideal_ratio` remove what looked like the main obstruction. Local
generators of the four ideal sheaves are only well defined up to a unit per chart, but that unit
is *pinned* by any ideal identity `⟨den⟩ · (D_P · D_Q) = ⟨num⟩ · (D_R · D_O)` one already has
(`ModularCurves.exists_unit_mul_of_span_singleton_eq`: two generators of one principal ideal, one
of them a nonzerodivisor, differ by a unit) and can be absorbed into a single generator. So the
geometric input needed is an *ideal-sheaf identity chart by chart*, not a coherent system of
generators.

## Status

`hloc_off_chartZ` — the local Cartier data at the *single* point of `projModel W` off the affine
`Z`-chart, i.e. the chart at infinity — is the one remaining leaf. Everything else is proved, and
`exists_squareChartData_projModel` is assembled from it. Proved here:

* the whole composition, on an arbitrary scheme
  (`nonempty_tensorObj_idealModule_iso_of_squareChartData`);
* the reduction of the cocycle to one equation in the function field
  (`cocycle_of_germToFunctionField_ratio`, `squareChartDataOfRatio`);
* the passage from a chartwise **ideal identity** to a chart datum
  (`nonempty_squareChartData_of_span_ratio`, `nonempty_squareChartData_of_ideal_ratio`);
* the common-refinement step (`exists_affineOpen_span_nzd_four`) and the local principality of
  every section ideal sheaf of the model (`exists_affineOpen_ker_pointSection_span_nzd`);
* the degenerate cases `P = 0` and `Q = 0` of the leaf itself
  (`nonempty_squareChartData_projModel_zero_left` / `_zero_right`);
* the affine-chart ideal identity in exactly the shape the reduction consumes — the chord
  (`chordIdealIdentity`, mathlib's `XYIdeal_mul_XYIdeal`) and the vertical
  (`verticalIdealIdentity`, mathlib's `XYIdeal_neg_mul`), assembled over *all* pairs of points
  into the single existential `exists_affine_ideal_identity` (item 1c of the leaf);
* **the points-to-ideals dictionary on the affine `Z`-chart** (item 1a of the leaf):
  `ker_ideal_pointSection_chartZ` / `ker_ideal_pointSection_chartZ'` identify the section ideal
  sheaf `I(P)` on the `Z`-chart with mathlib's `affineIdeal` (`XYIdeal` at an affine point, `⊤` at
  `0`), transported along `chartZSectionsRingEquiv`; the route is mathlib's `quotientXYIdealEquiv`
  (`ker_eq_XYIdeal`), the chart evaluation `affineChartHom` (`ker_affineChartHom`), the
  general `fromSpec` computation `ker_ideal_of_fromSpec_factor`, and `pointSection_some`;
* the resulting `hloc` clause at every point of the `Z`-chart (`hloc_chartZ`), for the explicit
  chord-over-vertical rational function `chartZFunction`;
* the triviality of a section ideal sheaf away from its section
  (`ker_ideal_eq_top_of_preimage_eq_bot`);
* the transport of the HasseWeil divisor witness into `(projModel W).functionField`
  (`exists_functionField_projectiveDivisorOf_kappa`).

## Note on the two `idealModule`s

The tree carries two unrelated constructions called `idealModule`:
`AlgebraicGeometry.Scheme.Modules.idealModule (J : C.IdealSheafData)` (used here and by both
halves of the bridge) and `ModularCurves.idealModule (f : X ⟶ Y)`, the kernel of
`𝒪_Y ⟶ f_*𝒪_X` (used by `EllipticCurve/PoleSheafModel.lean`). The chart trivialisations at
`PoleSheafModel.lean:409-431` are for the *second*; the ideal *sheaf* computations they rest on
(`projModelZero_ker_ideal_chartZ`, `projModelZero_ker_ideal_sectionNeighborhood`,
`projModelSectionRoot_mem_nonZeroDivisors`) are about `(projModelZero W).ker` and so do feed the
first.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite HasseWeil.Curves

namespace ModularCurves

/-- **Two generators of one principal ideal differ by a unit**, as soon as one of them is a
nonzerodivisor: `span {a} = span {b}` gives `b = c * a` and `a = d * b`, hence `(d * c - 1) * a = 0`
and therefore `d * c = 1`.

This is the algebraic reason why the "generators are only well defined up to a unit per chart"
obstruction is harmless: the unit is *determined* by any ideal identity one already has, and can be
absorbed into one of the generators. -/
theorem exists_unit_mul_of_span_singleton_eq {A : Type*} [CommRing A] {a b : A}
    (ha : a ∈ nonZeroDivisors A) (h : Ideal.span {a} = Ideal.span ({b} : Set A)) :
    ∃ u : Aˣ, b = (u : A) * a := by
  have hb : b ∈ Ideal.span ({a} : Set A) := by
    rw [h]; exact Ideal.mem_span_singleton_self b
  have ha' : a ∈ Ideal.span ({b} : Set A) := by
    rw [← h]; exact Ideal.mem_span_singleton_self a
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp ha'
  have hdc : d * c = 1 := by
    refine sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp ha _ ?_)
    calc (d * c - 1) * a = d * (c * a) - a := by ring
      _ = 0 := by rw [hc, hd, sub_self]
  exact ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, hc.symm⟩

end ModularCurves

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}}

/-! ## The scheme-level composition -/

/-- The ideal of a product of ideal sheaves on an affine open where both factors are principal.
(`Scheme.IdealSheafData.ideal_mul` computes the ideal of a product chart by chart, and
`Ideal.span_singleton_mul_span_singleton` multiplies the two principal ideals.) -/
theorem ideal_mul_eq_span_singleton_mul {J₁ J₂ : C.IdealSheafData} (U : C.affineOpens)
    {a b : Γ(C, U.1)} (h₁ : J₁.ideal U = Ideal.span {a}) (h₂ : J₂.ideal U = Ideal.span {b}) :
    (J₁ * J₂).ideal U = Ideal.span {a * b} := by
  rw [show (J₁ * J₂).ideal U = J₁.ideal U * J₂.ideal U from by
    rw [Scheme.IdealSheafData.ideal_mul]; rfl, h₁, h₂,
    Ideal.span_singleton_mul_span_singleton]

/-- **The local data of a theorem-of-the-square identity** `D_P + D_Q ∼ D_R + D_O`.

One affine cover, a nonzerodivisor generator for each of the four ideal sheaves on each chart,
and the cocycle identity saying that the local ratios `(genP i · genQ i) / (genR i · genO i)`
are one and the same rational function — cross-multiplied, so that no total quotient sheaf has
to be constructed. This is `PrincipalDivisorData` for the two product ideal sheaves, packaged
so that `ProductDivisorData` can be read off the same cover. -/
structure SquareChartData (JP JQ JR JO : C.IdealSheafData) where
  /-- The index type of the trivialising affine cover. -/
  Idx : Type u
  /-- The trivialising affine cover. -/
  chart : Idx → C.affineOpens
  /-- The charts cover the scheme. -/
  chart_cover : ⨆ i, (chart i).1 = ⊤
  /-- The local equation of `D_P` on `chart i`. -/
  genP : ∀ i, Γ(C, (chart i).1)
  /-- The local equation of `D_Q` on `chart i`. -/
  genQ : ∀ i, Γ(C, (chart i).1)
  /-- The local equation of `D_R` on `chart i`. -/
  genR : ∀ i, Γ(C, (chart i).1)
  /-- The local equation of `D_O` on `chart i`. -/
  genO : ∀ i, Γ(C, (chart i).1)
  /-- `genP i` generates `JP` on `chart i`. -/
  span_genP : ∀ i, JP.ideal (chart i) = Ideal.span {genP i}
  /-- `genQ i` generates `JQ` on `chart i`. -/
  span_genQ : ∀ i, JQ.ideal (chart i) = Ideal.span {genQ i}
  /-- `genR i` generates `JR` on `chart i`. -/
  span_genR : ∀ i, JR.ideal (chart i) = Ideal.span {genR i}
  /-- `genO i` generates `JO` on `chart i`. -/
  span_genO : ∀ i, JO.ideal (chart i) = Ideal.span {genO i}
  /-- `genP i` is a nonzerodivisor, i.e. `D_P` is Cartier. -/
  genP_nzd : ∀ i, genP i ∈ nonZeroDivisors Γ(C, (chart i).1)
  /-- `genQ i` is a nonzerodivisor, i.e. `D_Q` is Cartier. -/
  genQ_nzd : ∀ i, genQ i ∈ nonZeroDivisors Γ(C, (chart i).1)
  /-- `genR i` is a nonzerodivisor, i.e. `D_R` is Cartier. -/
  genR_nzd : ∀ i, genR i ∈ nonZeroDivisors Γ(C, (chart i).1)
  /-- `genO i` is a nonzerodivisor, i.e. `D_O` is Cartier. -/
  genO_nzd : ∀ i, genO i ∈ nonZeroDivisors Γ(C, (chart i).1)
  /-- The local ratios agree on overlaps. -/
  cocycle : ∀ i j,
    ((genP i * genQ i) |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_left⟫) *
        ((genR j * genO j) |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_right⟫) =
      ((genP j * genQ j) |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_right⟫) *
        ((genR i * genO i) |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_left⟫)

namespace SquareChartData

variable {JP JQ JR JO : C.IdealSheafData} (D : SquareChartData JP JQ JR JO)

/-- The underlying principal-divisor data of the ratio
`(genP · genQ) / (genR · genO)`, presenting `D_P + D_Q − D_R − D_O` as a principal divisor. -/
def toPrincipalDivisorData : PrincipalDivisorData (JP * JQ) (JR * JO) where
  Idx := D.Idx
  chart := D.chart
  chart_cover := D.chart_cover
  num i := D.genP i * D.genQ i
  den i := D.genR i * D.genO i
  span_num i := ideal_mul_eq_span_singleton_mul _ (D.span_genP i) (D.span_genQ i)
  span_den i := ideal_mul_eq_span_singleton_mul _ (D.span_genR i) (D.span_genO i)
  num_nzd i := mul_mem (D.genP_nzd i) (D.genQ_nzd i)
  den_nzd i := mul_mem (D.genR_nzd i) (D.genO_nzd i)
  cocycle := D.cocycle

/-- Exchanging the two divisors on the right-hand side of the identity. Only the *product*
`genR · genO` enters the cocycle, so this is commutativity of multiplication. -/
def swapRight : SquareChartData JP JQ JO JR where
  Idx := D.Idx
  chart := D.chart
  chart_cover := D.chart_cover
  genP := D.genP
  genQ := D.genQ
  genR := D.genO
  genO := D.genR
  span_genP := D.span_genP
  span_genQ := D.span_genQ
  span_genR := D.span_genO
  span_genO := D.span_genR
  genP_nzd := D.genP_nzd
  genQ_nzd := D.genQ_nzd
  genR_nzd := D.genO_nzd
  genO_nzd := D.genR_nzd
  cocycle i j := by
    rw [show D.genO j * D.genR j = D.genR j * D.genO j from mul_comm _ _,
      show D.genO i * D.genR i = D.genR i * D.genO i from mul_comm _ _]
    exact D.cocycle i j

end SquareChartData

/-- **(T10-asm, scheme level) The theorem of the square from its local data.**

The composition of the two halves of the bridge:

  `I(JP) ⊗ I(JQ) ≅ I(JP · JQ) ≅ I(JR · JO) ≅ I(JR) ⊗ I(JO)`,

the outer isomorphisms by `nonempty_tensorObj_idealModule_iso_mul` (a product of ideal sheaves
is the tensor product of the ideal modules) and the middle one by
`nonempty_idealModule_iso_of_principalDivisorData` (multiplication by the rational function that
the cocycle identity presents). No hypothesis on `C` is used. -/
theorem nonempty_tensorObj_idealModule_iso_of_squareChartData {JP JQ JR JO : C.IdealSheafData}
    (D : SquareChartData JP JQ JR JO) :
    Nonempty (tensorObj (idealModule JP) (idealModule JQ) ≅
      tensorObj (idealModule JR) (idealModule JO)) := by
  obtain ⟨ePQ⟩ := nonempty_tensorObj_idealModule_iso_mul (JA := JP) (JB := JQ) D.chart
    D.chart_cover D.genP D.genQ D.span_genP D.span_genQ D.genP_nzd D.genQ_nzd
  obtain ⟨eRO⟩ := nonempty_tensorObj_idealModule_iso_mul (JA := JR) (JB := JO) D.chart
    D.chart_cover D.genR D.genO D.span_genR D.span_genO D.genR_nzd D.genO_nzd
  exact ⟨ePQ ≪≫ (nonempty_idealModule_iso_of_principalDivisorData
    D.toPrincipalDivisorData).some.symm ≪≫ eRO.symm⟩

/-! ## The cocycle from a single ratio in the function field -/

/-- On an irreducible space two nonempty opens meet. -/
theorem nonempty_inf_of_nonempty [IrreducibleSpace ↥C] {U V : C.Opens}
    (hU : Nonempty ↥U.toScheme) (hV : Nonempty ↥V.toScheme) :
    Nonempty ↥(U ⊓ V : C.Opens).toScheme := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hy⟩ := hV
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (X := ↥C) U.2 V.2 ⟨x, hx⟩ ⟨y, hy⟩
  exact ⟨⟨z, hz⟩⟩

/-- The map to the function field is compatible with restriction: both are the germ at the
generic point. -/
theorem germToFunctionField_restrict [IsIntegral C] {U V : C.Opens} (h : V ≤ U)
    [Nonempty ↥U.toScheme] [Nonempty ↥V.toScheme] (s : Γ(C, U)) :
    C.germToFunctionField V (s |_ₗ V ⟪h⟫) = C.germToFunctionField U s :=
  C.presheaf.germ_res_apply (homOfLE h) _ _ s

/-- **The cocycle identity is a single equation in the function field.** On an integral scheme,
if the local numerators and denominators have one and the same ratio `g ∈ K(C)`, then they
satisfy the cross-multiplied cocycle identity on every overlap: the overlap is a nonempty open
(irreducibility), and its sections inject into `K(C)`. -/
theorem cocycle_of_germToFunctionField_ratio [IsIntegral C] {Idx : Type u}
    (chart : Idx → C.affineOpens) (hne : ∀ i, Nonempty ↥(chart i).1.toScheme)
    (numer denom : ∀ i, Γ(C, (chart i).1)) (g : C.functionField)
    (hratio : ∀ i, C.germToFunctionField (chart i).1 (numer i) =
      g * C.germToFunctionField (chart i).1 (denom i)) (i j : Idx) :
    (numer i |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_left⟫) *
        (denom j |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_right⟫) =
      (numer j |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_right⟫) *
        (denom i |_ₗ (chart i).1 ⊓ (chart j).1 ⟪inf_le_left⟫) := by
  haveI := hne i
  haveI := hne j
  haveI : Nonempty ↥((chart i).1 ⊓ (chart j).1 : C.Opens).toScheme :=
    nonempty_inf_of_nonempty (hne i) (hne j)
  refine C.germToFunctionField_injective ((chart i).1 ⊓ (chart j).1) ?_
  rw [map_mul, map_mul, germToFunctionField_restrict, germToFunctionField_restrict,
    germToFunctionField_restrict, germToFunctionField_restrict, hratio i, hratio j]
  ring

/-- **The integral-scheme constructor for `SquareChartData`.** On an integral scheme the cocycle
identity reduces to one equation `genP · genQ = g · (genR · genO)` in the function field — the
form in which "a rational function with divisor `D_P + D_Q − D_R − D_O`" is actually met. -/
def squareChartDataOfRatio [IsIntegral C] {JP JQ JR JO : C.IdealSheafData} {Idx : Type u}
    (chart : Idx → C.affineOpens) (chart_cover : ⨆ i, (chart i).1 = ⊤)
    (hne : ∀ i, Nonempty ↥(chart i).1.toScheme)
    (genP genQ genR genO : ∀ i, Γ(C, (chart i).1))
    (span_genP : ∀ i, JP.ideal (chart i) = Ideal.span {genP i})
    (span_genQ : ∀ i, JQ.ideal (chart i) = Ideal.span {genQ i})
    (span_genR : ∀ i, JR.ideal (chart i) = Ideal.span {genR i})
    (span_genO : ∀ i, JO.ideal (chart i) = Ideal.span {genO i})
    (genP_nzd : ∀ i, genP i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (genQ_nzd : ∀ i, genQ i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (genR_nzd : ∀ i, genR i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (genO_nzd : ∀ i, genO i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (g : C.functionField)
    (hratio : ∀ i, C.germToFunctionField (chart i).1 (genP i * genQ i) =
      g * C.germToFunctionField (chart i).1 (genR i * genO i)) :
    SquareChartData JP JQ JR JO where
  Idx := Idx
  chart := chart
  chart_cover := chart_cover
  genP := genP
  genQ := genQ
  genR := genR
  genO := genO
  span_genP := span_genP
  span_genQ := span_genQ
  span_genR := span_genR
  span_genO := span_genO
  genP_nzd := genP_nzd
  genQ_nzd := genQ_nzd
  genR_nzd := genR_nzd
  genO_nzd := genO_nzd
  cocycle := cocycle_of_germToFunctionField_ratio chart hne
    (fun i => genP i * genQ i) (fun i => genR i * genO i) g hratio

/-! ## The chart datum from a chartwise ideal identity -/

/-- **The chart datum from a chartwise ideal identity (T10-asm-chart, reduction step).**

The generators of the four ideal sheaves need *not* be produced together with the rational
function. It is enough to have, on each chart of one cover:

* *any* nonzerodivisor generators `genP, genQ, genR, genO` of the four ideal sheaves;
* a local numerator/denominator pair `num, den` presenting one and the same global ratio
  `g ∈ K(C)` (`hratio`);
* the **ideal identity** `den · (D_P + D_Q) = num · (D_R + D_O)` on that chart (`hspan`).

The unit ambiguity in the generators then cancels *automatically*: `hspan` says the two products
`den · genP · genQ` and `num · genR · genO` generate the same principal ideal, and the first is a
nonzerodivisor, so they differ by a unit `u` (`ModularCurves.exists_unit_mul_of_span_singleton_eq`);
absorbing `u` into `genP` makes the ratios equal to `g` on the nose, and
`squareChartDataOfRatio` does the rest. -/
theorem nonempty_squareChartData_of_span_ratio [IsIntegral C] {JP JQ JR JO : C.IdealSheafData}
    {Idx : Type u} (chart : Idx → C.affineOpens) (chart_cover : ⨆ i, (chart i).1 = ⊤)
    (hne : ∀ i, Nonempty ↥(chart i).1.toScheme)
    (genP genQ genR genO num den : ∀ i, Γ(C, (chart i).1))
    (span_genP : ∀ i, JP.ideal (chart i) = Ideal.span {genP i})
    (span_genQ : ∀ i, JQ.ideal (chart i) = Ideal.span {genQ i})
    (span_genR : ∀ i, JR.ideal (chart i) = Ideal.span {genR i})
    (span_genO : ∀ i, JO.ideal (chart i) = Ideal.span {genO i})
    (genP_nzd : ∀ i, genP i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (genQ_nzd : ∀ i, genQ i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (genR_nzd : ∀ i, genR i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (genO_nzd : ∀ i, genO i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (den_nzd : ∀ i, den i ∈ nonZeroDivisors Γ(C, (chart i).1))
    (g : C.functionField)
    (hratio : ∀ i, C.germToFunctionField (chart i).1 (num i) =
      g * C.germToFunctionField (chart i).1 (den i))
    (hspan : ∀ i, Ideal.span {den i * (genP i * genQ i)} =
      Ideal.span {num i * (genR i * genO i)}) :
    Nonempty (SquareChartData JP JQ JR JO) := by
  choose u hu using fun i => ModularCurves.exists_unit_mul_of_span_singleton_eq
    (mul_mem (den_nzd i) (mul_mem (genP_nzd i) (genQ_nzd i))) (hspan i)
  refine ⟨squareChartDataOfRatio chart chart_cover hne
    (fun i => (u i : Γ(C, (chart i).1)) * genP i) genQ genR genO
    (fun i => (span_genP i).trans
      (Ideal.span_singleton_mul_left_unit (u i).isUnit (genP i)).symm)
    span_genQ span_genR span_genO
    (fun i => mul_mem (u i).isUnit.mem_nonZeroDivisors (genP_nzd i))
    genQ_nzd genR_nzd genO_nzd g fun i => ?_⟩
  haveI := hne i
  have hden : C.germToFunctionField (chart i).1 (den i) ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero (den_nzd i)
      (C.germToFunctionField_injective (chart i).1 (h0.trans (map_zero _).symm))
  have h1 : C.germToFunctionField (chart i).1 (num i) *
        (C.germToFunctionField (chart i).1 (genR i) * C.germToFunctionField (chart i).1 (genO i)) =
      C.germToFunctionField (chart i).1 (u i : Γ(C, (chart i).1)) *
        (C.germToFunctionField (chart i).1 (den i) *
          (C.germToFunctionField (chart i).1 (genP i) *
            C.germToFunctionField (chart i).1 (genQ i))) := by
    simpa only [map_mul] using congrArg (C.germToFunctionField (chart i).1) (hu i)
  rw [hratio i] at h1
  refine mul_left_cancel₀ hden ?_
  simp only [map_mul]
  linear_combination -h1

/-! ## Common refinement of four locally principal ideal sheaves -/

/-- **Common refinement.** Four ideal sheaves that are locally principal on nonzerodivisors are
simultaneously so on one affine neighbourhood of every point: shrink to a basis affine inside
the intersection of the four given charts and restrict the generators
(`ideal_eq_span_restrict_of_affine` for the generation,
`restrict_gen_nonZeroDivisors_and_surjective` for the nonzerodivisor property).

This is the *cover* half of a theorem-of-the-square chart datum. It deliberately does not
supply the cocycle, and cannot: generators chosen independently on each chart differ from a
coherent choice by a unit, and those units do not cancel. Cover and generators must be produced
together with the rational function. -/
theorem exists_affineOpen_span_nzd_four {J₁ J₂ J₃ J₄ : C.IdealSheafData}
    (h₁ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₁.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₂ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₂.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₃ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₃.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₄ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₄.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1)) (c : ↥C) :
    ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g₁ g₂ g₃ g₄ : Γ(C, V.1),
      ((J₁.ideal V = Ideal.span {g₁} ∧ g₁ ∈ nonZeroDivisors Γ(C, V.1)) ∧
        (J₂.ideal V = Ideal.span {g₂} ∧ g₂ ∈ nonZeroDivisors Γ(C, V.1))) ∧
      ((J₃.ideal V = Ideal.span {g₃} ∧ g₃ ∈ nonZeroDivisors Γ(C, V.1)) ∧
        (J₄.ideal V = Ideal.span {g₄} ∧ g₄ ∈ nonZeroDivisors Γ(C, V.1))) := by
  obtain ⟨V₁, hc₁, g₁, hs₁, hn₁⟩ := h₁ c
  obtain ⟨V₂, hc₂, g₂, hs₂, hn₂⟩ := h₂ c
  obtain ⟨V₃, hc₃, g₃, hs₃, hn₃⟩ := h₃ c
  obtain ⟨V₄, hc₄, g₄, hs₄, hn₄⟩ := h₄ c
  obtain ⟨-, ⟨W, hW, rfl⟩, hcW, hsub⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open
      (show c ∈ ((V₁.1 ⊓ V₂.1 ⊓ V₃.1 ⊓ V₄.1 : C.Opens) : Set ↥C) from
        ⟨⟨⟨hc₁, hc₂⟩, hc₃⟩, hc₄⟩) (V₁.1 ⊓ V₂.1 ⊓ V₃.1 ⊓ V₄.1).2
  have hW₁ : W ≤ V₁.1 := fun a ha => (hsub ha).1.1.1
  have hW₂ : W ≤ V₂.1 := fun a ha => (hsub ha).1.1.2
  have hW₃ : W ≤ V₃.1 := fun a ha => (hsub ha).1.2
  have hW₄ : W ≤ V₄.1 := fun a ha => (hsub ha).2
  exact ⟨⟨W, hW⟩, hcW, _, _, _, _,
    ⟨⟨ideal_eq_span_restrict_of_affine V₁ g₁ hs₁ hn₁ ⟨W, hW⟩ hW₁,
        (restrict_gen_nonZeroDivisors_and_surjective V₁ g₁ hs₁ hn₁ hW₁).1⟩,
      ⟨ideal_eq_span_restrict_of_affine V₂ g₂ hs₂ hn₂ ⟨W, hW⟩ hW₂,
        (restrict_gen_nonZeroDivisors_and_surjective V₂ g₂ hs₂ hn₂ hW₂).1⟩⟩,
    ⟨⟨ideal_eq_span_restrict_of_affine V₃ g₃ hs₃ hn₃ ⟨W, hW⟩ hW₃,
        (restrict_gen_nonZeroDivisors_and_surjective V₃ g₃ hs₃ hn₃ hW₃).1⟩,
      ⟨ideal_eq_span_restrict_of_affine V₄ g₄ hs₄ hn₄ ⟨W, hW⟩ hW₄,
        (restrict_gen_nonZeroDivisors_and_surjective V₄ g₄ hs₄ hn₄ hW₄).1⟩⟩⟩

/-- **The chart datum from an ideal-sheaf identity (T10-asm-chart, pointwise form).**

This is the shape in which the geometry actually supplies a theorem-of-the-square identity:

* each of the four ideal sheaves is locally principal on a nonzerodivisor (`hP`–`hO`); for the
  section ideal sheaves of a smooth proper relative curve this is exactly
  `ModularCurves.exists_affineOpen_ker_pointSection_span_nzd`;
* around every point there is *one* affine chart carrying a numerator/denominator presentation
  `num / den = g` of one fixed rational function `g`, together with the **ideal identity**
  `⟨den⟩ · (D_P · D_Q) = ⟨num⟩ · (D_R · D_O)` on that chart (`hloc`). No generators are asked for
  here, and no compatibility between charts: the identity is between ideals.

The two inputs live on unrelated charts. They are refined onto a common affine neighbourhood — the
generators survive by `ideal_eq_span_restrict_of_affine`, the ideal identity by `Ideal.map_mul`
together with `Scheme.IdealSheafData.map_ideal`, and `den` stays a nonzerodivisor because a
nonempty open of an integral scheme has a domain of sections — and then
`nonempty_squareChartData_of_span_ratio` absorbs the residual unit.

So the only genuinely geometric input left is `hloc`: **a local Cartier presentation of the
divisor `D_P + D_Q − D_R − D_O` as `div(g)`**, chart by chart. -/
theorem nonempty_squareChartData_of_ideal_ratio [IsIntegral C] {JP JQ JR JO : C.IdealSheafData}
    (hP : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JP.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hQ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JQ.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hR : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JR.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hO : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JO.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (g : C.functionField)
    (hloc : ∀ c : ↥C, ∃ (V : C.affineOpens) (hc : c ∈ V.1) (num den : Γ(C, V.1)),
      den ∈ nonZeroDivisors Γ(C, V.1) ∧
      @Scheme.germToFunctionField C _ V.1 ⟨⟨c, hc⟩⟩ num =
        g * @Scheme.germToFunctionField C _ V.1 ⟨⟨c, hc⟩⟩ den ∧
      Ideal.span {den} * (JP.ideal V * JQ.ideal V) =
        Ideal.span {num} * (JR.ideal V * JO.ideal V)) :
    Nonempty (SquareChartData JP JQ JR JO) := by
  choose V₀ hc₀ num den den_nzd hratio₀ hideal₀ using hloc
  choose V hcV g₁ g₂ g₃ g₄ hg using fun c => exists_affineOpen_span_nzd_four hP hQ hR hO c
  -- a common affine refinement of the two charts, around each point
  have hbasis : ∀ c : ↥C, ∃ Wc : C.affineOpens, c ∈ Wc.1 ∧ Wc.1 ≤ (V c).1 ∧ Wc.1 ≤ (V₀ c).1 := by
    intro c
    obtain ⟨-, ⟨Wc, hWc, rfl⟩, hcWc, hsub⟩ :=
      C.isBasis_affineOpens.exists_subset_of_mem_open
        (show c ∈ (((V c).1 ⊓ (V₀ c).1 : C.Opens) : Set ↥C) from ⟨hcV c, hc₀ c⟩)
        ((V c).1 ⊓ (V₀ c).1).2
    exact ⟨⟨Wc, hWc⟩, hcWc, fun a ha => (hsub ha).1, fun a ha => (hsub ha).2⟩
  choose W hcW hWV hWV₀ using hbasis
  have hneW : ∀ c : ↥C, Nonempty ↥(W c).1.toScheme := fun c => ⟨⟨c, hcW c⟩⟩
  refine nonempty_squareChartData_of_span_ratio W ?_ hneW
    (fun c => g₁ c |_ₗ (W c).1 ⟪hWV c⟫) (fun c => g₂ c |_ₗ (W c).1 ⟪hWV c⟫)
    (fun c => g₃ c |_ₗ (W c).1 ⟪hWV c⟫) (fun c => g₄ c |_ₗ (W c).1 ⟪hWV c⟫)
    (fun c => num c |_ₗ (W c).1 ⟪hWV₀ c⟫) (fun c => den c |_ₗ (W c).1 ⟪hWV₀ c⟫)
    (fun c => ideal_eq_span_restrict_of_affine (V c) (g₁ c) (hg c).1.1.1 (hg c).1.1.2 (W c) (hWV c))
    (fun c => ideal_eq_span_restrict_of_affine (V c) (g₂ c) (hg c).1.2.1 (hg c).1.2.2 (W c) (hWV c))
    (fun c => ideal_eq_span_restrict_of_affine (V c) (g₃ c) (hg c).2.1.1 (hg c).2.1.2 (W c) (hWV c))
    (fun c => ideal_eq_span_restrict_of_affine (V c) (g₄ c) (hg c).2.2.1 (hg c).2.2.2 (W c) (hWV c))
    (fun c => (restrict_gen_nonZeroDivisors_and_surjective (V c) (g₁ c) (hg c).1.1.1
      (hg c).1.1.2 (hWV c)).1)
    (fun c => (restrict_gen_nonZeroDivisors_and_surjective (V c) (g₂ c) (hg c).1.2.1
      (hg c).1.2.2 (hWV c)).1)
    (fun c => (restrict_gen_nonZeroDivisors_and_surjective (V c) (g₃ c) (hg c).2.1.1
      (hg c).2.1.2 (hWV c)).1)
    (fun c => (restrict_gen_nonZeroDivisors_and_surjective (V c) (g₄ c) (hg c).2.2.1
      (hg c).2.2.2 (hWV c)).1)
    (fun c => ?_) g (fun c => ?_) (fun c => ?_)
  · exact eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hcW x⟩
  · -- `den` stays a nonzerodivisor: its germ is unchanged, and `Γ(C, W c)` is a domain
    haveI := hneW c
    haveI : Nonempty ↥(V₀ c).1.toScheme := ⟨⟨c, hc₀ c⟩⟩
    haveI : IsDomain Γ(C, (W c).1) := IsIntegral.component_integral (X := C) (W c).1
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    refine nonZeroDivisors.ne_zero (den_nzd c) (C.germToFunctionField_injective (V₀ c).1 ?_)
    rw [← germToFunctionField_restrict (hWV₀ c) (den c), h0, map_zero, map_zero]
  · haveI := hneW c
    haveI : Nonempty ↥(V₀ c).1.toScheme := ⟨⟨c, hc₀ c⟩⟩
    rw [germToFunctionField_restrict (hWV₀ c) (num c),
      germToFunctionField_restrict (hWV₀ c) (den c)]
    exact hratio₀ c
  · -- the ideal identity restricts along `W c ≤ V₀ c`
    set φ := (C.presheaf.map (homOfLE (hWV₀ c)).op).hom with hφ
    have hPW : Ideal.map φ (JP.ideal (V₀ c)) = JP.ideal (W c) := JP.map_ideal (hWV₀ c)
    have hQW : Ideal.map φ (JQ.ideal (V₀ c)) = JQ.ideal (W c) := JQ.map_ideal (hWV₀ c)
    have hRW : Ideal.map φ (JR.ideal (V₀ c)) = JR.ideal (W c) := JR.map_ideal (hWV₀ c)
    have hOW : Ideal.map φ (JO.ideal (V₀ c)) = JO.ideal (W c) := JO.map_ideal (hWV₀ c)
    have hmap := congrArg (Ideal.map φ) (hideal₀ c)
    rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_mul, Ideal.map_mul, Ideal.map_span,
      Ideal.map_span, Set.image_singleton, Set.image_singleton, hPW, hQW, hRW, hOW,
      ideal_eq_span_restrict_of_affine (V c) (g₁ c) (hg c).1.1.1 (hg c).1.1.2 (W c) (hWV c),
      ideal_eq_span_restrict_of_affine (V c) (g₂ c) (hg c).1.2.1 (hg c).1.2.2 (W c) (hWV c),
      ideal_eq_span_restrict_of_affine (V c) (g₃ c) (hg c).2.1.1 (hg c).2.1.2 (W c) (hWV c),
      ideal_eq_span_restrict_of_affine (V c) (g₄ c) (hg c).2.2.1 (hg c).2.2.2 (W c) (hWV c),
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton] at hmap
    exact hmap

/-- **The degenerate chart datum.** When the two sides of the identity carry the same pair of
divisors, the constant ratio `1` works and the cocycle is commutativity of multiplication. The
only input is that both ideal sheaves are locally principal on nonzerodivisors; the common cover
comes from `exists_affineOpen_span_nzd_four`, indexed by the points of `C`.

This is what discharges the degenerate cases `Q = 0` and `P = 0` of the theorem of the square. -/
theorem nonempty_squareChartData_diagonal {JP JQ : C.IdealSheafData}
    (hP : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JP.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hQ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JQ.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1)) :
    Nonempty (SquareChartData JP JQ JP JQ) := by
  choose V hcV g₁ g₂ g₃ g₄ hg using fun c => exists_affineOpen_span_nzd_four hP hQ hP hQ c
  refine ⟨{ Idx := ↥C
            chart := V
            chart_cover := ?_
            genP := g₁
            genQ := g₂
            genR := g₁
            genO := g₂
            span_genP := fun c => (hg c).1.1.1
            span_genQ := fun c => (hg c).1.2.1
            span_genR := fun c => (hg c).1.1.1
            span_genO := fun c => (hg c).1.2.1
            genP_nzd := fun c => (hg c).1.1.2
            genQ_nzd := fun c => (hg c).1.2.2
            genR_nzd := fun c => (hg c).1.1.2
            genO_nzd := fun c => (hg c).1.2.2
            cocycle := fun i j => mul_comm _ _ }⟩
  exact eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hcV x⟩

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

open AlgebraicGeometry.Scheme.Modules

/-! ## The field-level bridge -/

variable {k : Type u} [Field k] [DecidableEq k]

/-- **The section of the projective model attached to a point.** `projModelPointsEquiv` is the
dictionary between the `k`-points of `projModel W` and mathlib's `W.toAffine.Point` (note
`W.baseChange k = W`); `pointSection` is its inverse, forgotten down to the underlying morphism
`Spec k ⟶ projModel W`. It is the `sec` of the theorem-of-the-square statement. -/
noncomputable def pointSection (W : WeierstrassCurve k) [W.IsElliptic] (P : W.toAffine.Point) :
    Spec (CommRingCat.of k) ⟶ projModel W :=
  ((projModelPointsEquiv W k).symm P).1

omit [DecidableEq k] in
/-- The section attached to `0` is the zero section, precomposed with the identity map of the
base written as `Spec` of the identity algebra map. -/
theorem pointSection_zero (W : WeierstrassCurve k) [W.IsElliptic] :
    pointSection W 0 =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ projModelZero W := by
  have h := (projModelPointsEquiv W k).symm_apply_eq.mpr
    (projModelPointsEquiv_zero W k).symm
  exact congrArg Subtype.val h

omit [DecidableEq k] in
/-- The section attached to `0` **is** the zero section: the base morphism `Spec` of the
identity algebra map `k → k` is the identity. -/
@[simp] theorem pointSection_zero' (W : WeierstrassCurve k) [W.IsElliptic] :
    pointSection W 0 = projModelZero W := by
  rw [pointSection_zero,
    show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl, Spec.map_id,
    Category.id_comp]

omit [DecidableEq k] in
/-- `pointSection` really is a section of the structure morphism of the projective model. -/
theorem pointSection_projModelπ (W : WeierstrassCurve k) [W.IsElliptic]
    (P : W.toAffine.Point) :
    pointSection W P ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)) := by
  have h : pointSection W P ≫ projModelπ W =
    Spec.map (CommRingCat.ofHom (algebraMap k k)) := ((projModelPointsEquiv W k).symm P).2
  rw [h, show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl, Spec.map_id]

omit [DecidableEq k] in
/-- **Every section ideal sheaf of the projective model is locally principal on a
nonzerodivisor.** This is `exists_affineOpen_ker_principal_nonZeroDivisor` (T-D22 = HB-REGIMM,
KM 1.2.2) for the smooth proper relative curve `projModelπ W`; it is the *cover* input of a
theorem-of-the-square chart datum. -/
theorem exists_affineOpen_ker_pointSection_span_nzd (W : WeierstrassCurve k) [W.IsElliptic]
    (P : W.toAffine.Point) (c : ↥(projModel W)) :
    ∃ V : (projModel W).affineOpens, c ∈ V.1 ∧ ∃ g : Γ(projModel W, V.1),
      (Scheme.Hom.ker (pointSection W P)).ideal V = Ideal.span {g} ∧
        g ∈ nonZeroDivisors Γ(projModel W, V.1) := by
  haveI := projModelπ_isProper W
  exact RelEffCartierDiv.exists_affineOpen_ker_principal_nonZeroDivisor (projModelπ W)
    (projModel_smooth W) (pointSection W P) (pointSection_projModelπ W P) c

omit [DecidableEq k] in
/-- The zero-section case of `exists_affineOpen_ker_pointSection_span_nzd`. -/
theorem exists_affineOpen_ker_projModelZero_span_nzd (W : WeierstrassCurve k) [W.IsElliptic]
    (c : ↥(projModel W)) :
    ∃ V : (projModel W).affineOpens, c ∈ V.1 ∧ ∃ g : Γ(projModel W, V.1),
      (Scheme.Hom.ker (projModelZero W)).ideal V = Ideal.span {g} ∧
        g ∈ nonZeroDivisors Γ(projModel W, V.1) := by
  haveI := projModelπ_isProper W
  exact RelEffCartierDiv.exists_affineOpen_ker_principal_nonZeroDivisor (projModelπ W)
    (projModel_smooth W) (projModelZero W) (projModelZero_projModelπ W) c

/-- **The degenerate case `Q = 0` of the leaf, proved.** Both sides carry the same pair of
divisors, so the chart datum is the diagonal one of
`nonempty_squareChartData_diagonal` with constant ratio `1`. -/
theorem nonempty_squareChartData_projModel_zero_right (W : WeierstrassCurve k) [W.IsElliptic]
    (P : W.toAffine.Point) :
    Nonempty (SquareChartData (Scheme.Hom.ker (pointSection W P))
      (Scheme.Hom.ker (pointSection W 0)) (Scheme.Hom.ker (pointSection W (P + 0)))
      (Scheme.Hom.ker (projModelZero W))) := by
  rw [add_zero, pointSection_zero']
  exact nonempty_squareChartData_diagonal (exists_affineOpen_ker_pointSection_span_nzd W P)
    (exists_affineOpen_ker_projModelZero_span_nzd W)

/-- **The degenerate case `P = 0` of the leaf, proved.** -/
theorem nonempty_squareChartData_projModel_zero_left (W : WeierstrassCurve k) [W.IsElliptic]
    (Q : W.toAffine.Point) :
    Nonempty (SquareChartData (Scheme.Hom.ker (pointSection W 0))
      (Scheme.Hom.ker (pointSection W Q)) (Scheme.Hom.ker (pointSection W (0 + Q)))
      (Scheme.Hom.ker (projModelZero W))) := by
  rw [zero_add, pointSection_zero']
  exact ⟨(nonempty_squareChartData_diagonal
    (exists_affineOpen_ker_projModelZero_span_nzd W)
    (exists_affineOpen_ker_pointSection_span_nzd W Q)).some.swapRight⟩

/-- **The field input, transported onto the scheme model.** The theorem of the square in divisor
form (`HasseWeil.Pic0.RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv`, Silverman III.3.5,
proved unconditionally in every characteristic) produces a nonzero element of
`W.toAffine.FunctionField`; `EllipticCurve.projModelFunctionFieldEquiv` moves it to
`(projModel W).functionField`, which is where `squareChartDataOfRatio` consumes it.

The `[IsIntegrallyClosed W.toAffine.CoordinateRing]` hypothesis is inherited from
`Curves.miller_hypothesis_holds_allChar`, which `kappaDivisor_add_linEquiv` routes through. It is
*not* discharged here: it is a genuine hypothesis of this lemma. (It is a theorem about smooth
affine curves over a field, so it is expected to be dischargeable, but HasseWeil does not do so
today.) -/
theorem exists_functionField_projectiveDivisorOf_kappa (W : WeierstrassCurve k) [W.IsElliptic]
    [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve k).CoordinateRing]
    (P Q : W.toAffine.Point) :
    ∃ F : (projModel W).functionField, F ≠ 0 ∧
      (⟨W.toAffine⟩ : SmoothPlaneCurve k).projectiveDivisorOf
          (EllipticCurve.projModelFunctionFieldEquiv W F) =
        kappaDivisor W.toAffine (P + Q) -
          (kappaDivisor W.toAffine P + kappaDivisor W.toAffine Q) := by
  obtain ⟨f, hf, hdiv⟩ :=
    HasseWeil.Pic0.RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv W.toAffine P Q
  refine ⟨(EllipticCurve.projModelFunctionFieldEquiv W).symm f, ?_, ?_⟩
  · intro h
    exact hf ((EllipticCurve.projModelFunctionFieldEquiv W).symm.injective
      (h.trans (map_zero (EllipticCurve.projModelFunctionFieldEquiv W).symm).symm))
  · rwa [(EllipticCurve.projModelFunctionFieldEquiv W).apply_symm_apply]

/-- **A section ideal sheaf is the unit ideal on any chart the section misses.** If `f ⁻¹ᵁ V` is
empty then `Γ(X, f ⁻¹ᵁ V)` is trivial, so `f.app V` kills everything.

This is the computation behind `projModelZero_ker_ideal_chartZ`, isolated for a general section:
it is what makes three of the four ideal sheaves *trivial* on a chart, which is why the chart
datum around a point only ever has to see the divisors passing through that point. -/
theorem ker_ideal_eq_top_of_preimage_eq_bot {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (V : Y.affineOpens) (h : f ⁻¹ᵁ V.1 = ⊥) :
    (Scheme.Hom.ker f).ideal V = ⊤ := by
  rw [Scheme.Hom.ker_apply]
  haveI : Subsingleton Γ(X, f ⁻¹ᵁ V.1) := by rw [h]; infer_instance
  exact (Ideal.eq_top_iff_one _).mpr (RingHom.mem_ker.mpr (Subsingleton.elim _ _))

/-! ## The affine-chart ideal identity (the chord and the vertical, from mathlib)

On the affine `Z`-chart the point at infinity is absent, so `I(O)` is the unit ideal and the
identity `⟨den⟩ · (I(P) · I(Q)) = ⟨num⟩ · (I(P+Q) · I(O))` asked for by
`nonempty_squareChartData_of_ideal_ratio` is *exactly* mathlib's ideal computation for the
Weierstrass group law: `num` is the chord `ℓ`, `den` is the vertical `x − x₃`, and `g = ℓ/v`. -/

open Polynomial WeierstrassCurve.Affine.CoordinateRing in
/-- **The chord identity on the affine chart.** For `P = (x₁, y₁)` and `Q = (x₂, y₂)` with
`Q ≠ -P`, writing `x₃ = addX`, `y₃ = addY` for the coordinates of `R = P + Q` and `ℓ` for the
chord through `P` and `Q`,

  `⟨x − x₃⟩ · (I(P) · I(Q)) = ⟨ℓ⟩ · (I(R) · ⊤)`

in `W.CoordinateRing`. This is `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal`
(`XIdeal = ⟨XClass⟩`, `YIdeal = ⟨YClass⟩`) with the unit ideal `⊤ = I(O)|_{affine}` inserted; it is
the `hloc` input of `nonempty_squareChartData_of_ideal_ratio` on every chart contained in the
affine `Z`-chart, with `den = XClass x₃` (the vertical) and `num = YClass ℓ` (the chord). -/
theorem chordIdealIdentity {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    Ideal.span {XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)} *
        (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      Ideal.span {YClass W (WeierstrassCurve.Affine.linePolynomial x₁ y₁ <|
          W.slope x₁ x₂ y₁ y₂)} *
        (XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) * (⊤ : Ideal W.CoordinateRing)) := by
  rw [Ideal.mul_top]
  exact XYIdeal_mul_XYIdeal h₁ h₂ hxy

open Polynomial WeierstrassCurve.Affine.CoordinateRing in
/-- **The vertical identity on the affine chart**, i.e. the degenerate case `Q = -P` of
`chordIdealIdentity`. There `R = P + Q = 0`, so on the affine chart *both* right-hand ideals are
the unit ideal and

  `⟨1⟩ · (I(P) · I(-P)) = ⟨x − x₁⟩ · (⊤ · ⊤)`,

i.e. `den = 1`, `num = XClass x₁` and `g = x − x₁`: the vertical line through `P`, whose divisor
is `(P) + (-P) − 2(O)`. This is
`WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul`. -/
theorem verticalIdealIdentity {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    Ideal.span {(1 : W.CoordinateRing)} *
        (XYIdeal W x (C y) * XYIdeal W x (C <| W.negY x y)) =
      Ideal.span {XClass W x} * ((⊤ : Ideal W.CoordinateRing) * (⊤ : Ideal W.CoordinateRing)) := by
  rw [Ideal.span_singleton_one, Ideal.top_mul, Ideal.mul_top, Ideal.mul_top, mul_comm]
  exact XYIdeal_neg_mul h

/-! ## The `Z`-chart ideal dictionary (T10-asm-chart, item 1a)

The section ideal sheaf of an affine point of `W`, read on the affine `Z`-chart of `projModel W`,
**is** mathlib's `XYIdeal`. This is what turns `chordIdealIdentity` / `verticalIdealIdentity` into
the `hloc` input of `nonempty_squareChartData_projModel_of_local` on every chart contained in the
`Z`-chart.

The chain is: the evaluation `affineChartHom` of the `Z`-chart ring at `[p : q : 1]` has kernel
`XYIdeal` (`ker_affineChartHom`, from mathlib's `quotientXYIdealEquiv`); the affine-point section
factors as `Spec` of that evaluation followed by `fromSpec` of the chart
(`projModelAffineSection_eq_fromSpec`), so the section's kernel ideal sheaf on the chart is that
same kernel (`ker_ideal_of_fromSpec_factor`); and `pointSection W (some x y h)` *is* the
affine-point section (`pointSection_some`). -/

section ChartZDictionary

open Polynomial WeierstrassCurve.Affine.CoordinateRing HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The kernel of an evaluation of the affine coordinate ring is `XYIdeal`.** If a ring map
`ε : R[W] → R` retracts the base ring and kills `X - p` and `Y - q`, then its kernel is exactly
`XYIdeal W p (C q)`: the containment `⊇` is by definition, and `⊆` because
`R[W] / XYIdeal ≃ₐ[R] R` (mathlib's `quotientXYIdealEquiv`), so any `a` in the kernel differs
from the constant `ε a = 0` by an element of `XYIdeal`. -/
theorem ker_eq_XYIdeal {A : Type*} [CommRing A] {W : WeierstrassCurve.Affine A} {p q : A}
    (h : W.Equation p q) (ε : W.CoordinateRing →+* A)
    (hC : ∀ r : A, ε (algebraMap A W.CoordinateRing r) = r)
    (hx : ε (XClass W p) = 0) (hy : ε (YClass W (C q)) = 0) :
    RingHom.ker ε = XYIdeal W p (C q) := by
  have hle : XYIdeal W p (C q) ≤ RingHom.ker ε := by
    rw [XYIdeal, Ideal.span_le]
    rintro a (rfl | rfl)
    · exact hx
    · exact hy
  refine le_antisymm (fun a ha => ?_) hle
  set e := quotientXYIdealEquiv (W' := W) (x := p) (y := C q) h with he
  set r : A := e (Ideal.Quotient.mk (XYIdeal W p (C q)) a) with hr
  have hcomm : e (Ideal.Quotient.mk (XYIdeal W p (C q)) (algebraMap A W.CoordinateRing r)) = r :=
    e.commutes r
  have hzero : Ideal.Quotient.mk (XYIdeal W p (C q)) (a - algebraMap A W.CoordinateRing r) = 0 := by
    refine e.injective ?_
    rw [map_sub, map_sub, hcomm, ← hr, sub_self, map_zero]
  have hmem : a - algebraMap A W.CoordinateRing r ∈ XYIdeal W p (C q) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hr0 : r = 0 := by
    have hker := hle hmem
    rw [RingHom.mem_ker, map_sub, hC, RingHom.mem_ker.mp ha, zero_sub, neg_eq_zero] at hker
    exact hker
  rw [hr0, map_zero, sub_zero] at hmem
  exact hmem

variable {R : Type u} [CommRing R]

/-- `X - p` is the coordinate `x` minus the constant `p`. -/
theorem XClass_eq_coordX_sub (W : WeierstrassCurve R) (p : R) :
    XClass W.toAffine p = coordX W - algebraMap R W.toAffine.CoordinateRing p := by
  rw [XClass, coordX]
  show AdjoinRoot.mk _ _ = AdjoinRoot.mk _ _ - AdjoinRoot.mk _ _
  rw [← map_sub]
  congr 1
  rw [map_sub]
  rfl

/-- `Y - q` is the coordinate `y` minus the constant `q`. -/
theorem YClass_eq_coordY_sub (W : WeierstrassCurve R) (q : R) :
    YClass W.toAffine (C q) = coordY W - algebraMap R W.toAffine.CoordinateRing q := by
  rw [YClass, coordY]
  show AdjoinRoot.mk _ _ = AdjoinRoot.mk _ _ - AdjoinRoot.mk _ _
  rw [← map_sub]
  congr 1

/-- The affine-point chart evaluation on a chart coordinate `Xⱼ/Z` is `Xⱼ` at `[p : q : 1]`. -/
theorem affineChartHom_isLocalizationElem (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (j : Fin 3) :
    affineChartHom W p q h (Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W j)) =
      MvPolynomial.eval ![p, q, 1] (MvPolynomial.X j) := by
  rw [show Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
      (mk_X_mem_quotientGrading_one W j) =
    Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) 1
      (((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) ^ 1)
      (by simpa using SetLike.pow_mem_graded 1 (mk_X_mem_quotientGrading_one W j)) from rfl]
  rw [affineChartHom_mk, map_pow, pow_one]
  rw [show (quotientGradingHom (projIdeal W)) (MvPolynomial.X j) =
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X j) from rfl]
  rw [projModelAffineEval_mk]

/-- The affine-point chart evaluation retracts the base ring. -/
theorem affineChartHom_fromZero (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (r : R) :
    affineChartHom W p q h ((fromZeroRingHom (quotientGrading (projIdeal W))
      (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r)) = r :=
  RingHom.congr_fun (affineChartHom_comp_algebraMap W p q h) r

/-- **The `Z`-chart ideal dictionary, ring form.** The kernel of the chart evaluation at the
affine point `(p, q)` is mathlib's `XYIdeal W p (C q)`, pulled back along the identification of
the `Z`-chart ring with the affine coordinate ring. -/
theorem ker_affineChartHom (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    RingHom.ker (affineChartHom W p q h) =
      Ideal.comap (chartZRingEquiv W : _ →+* W.toAffine.CoordinateRing)
        (XYIdeal W.toAffine p (C q)) := by
  set ε : W.toAffine.CoordinateRing →+* R :=
    (affineChartHom W p q h).comp ((chartZRingEquiv W).symm : _ →+* _) with hε
  have hC : ∀ r : R, ε (algebraMap R W.toAffine.CoordinateRing r) = r := by
    intro r
    have hsym : (chartZRingEquiv W).symm (algebraMap R W.toAffine.CoordinateRing r) =
        (fromZeroRingHom (quotientGrading (projIdeal W))
          (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
            ((algebraMapGradeZero (projIdeal W)) r) :=
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_fromZero W r).symm
    show affineChartHom W p q h ((chartZRingEquiv W).symm _) = r
    rw [hsym, affineChartHom_fromZero]
  have hx : ε (XClass W.toAffine p) = 0 := by
    have hsym : (chartZRingEquiv W).symm (coordX W) =
        Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
          (mk_X_mem_quotientGrading_one W 0) :=
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_x W).symm
    rw [XClass_eq_coordX_sub, map_sub, hC]
    show affineChartHom W p q h ((chartZRingEquiv W).symm (coordX W)) - p = 0
    rw [hsym, affineChartHom_isLocalizationElem]
    simp
  have hy : ε (YClass W.toAffine (C q)) = 0 := by
    have hsym : (chartZRingEquiv W).symm (coordY W) =
        Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
          (mk_X_mem_quotientGrading_one W 1) :=
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_y W).symm
    rw [YClass_eq_coordY_sub, map_sub, hC]
    show affineChartHom W p q h ((chartZRingEquiv W).symm (coordY W)) - q = 0
    rw [hsym, affineChartHom_isLocalizationElem]
    simp
  have hker := ker_eq_XYIdeal h ε hC hx hy
  have hcomp : ε.comp (chartZRingEquiv W : _ →+* W.toAffine.CoordinateRing) =
      affineChartHom W p q h := by
    refine RingHom.ext fun a => ?_
    show affineChartHom W p q h ((chartZRingEquiv W).symm (chartZRingEquiv W a)) = _
    rw [RingEquiv.symm_apply_apply]
  rw [← hker, ← hcomp, ← RingHom.comap_ker]

/-- The affine-point section in `fromSpec` chart coordinates: `Spec` of the chart evaluation,
composed with the canonical `fromSpec` of the affine `Z`-chart. (The `Y`-chart analogue for the
zero section is `projModelZero_eq_fromSpec`.) -/
theorem projModelAffineSection_eq_fromSpec (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineSection W p q h =
      Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
        CommRingCat.ofHom (affineChartHom W p q h)) ≫
      (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).fromSpec := by
  rw [← spec_affineChartHom_awayι W p q h, Proj_fromSpec_awayToSection_awayι, Spec.map_comp,
    Category.assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    show Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≫
        (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
        CommRingCat.ofHom (affineChartHom W p q h) =
        CommRingCat.ofHom (affineChartHom W p q h) from by
      rw [← Category.assoc, show Proj.awayToSection (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
        (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).hom from rfl,
        Iso.hom_inv_id, Category.id_comp]]

/-- **A section that factors through `fromSpec` has the evident kernel ideal sheaf.** If
`f : Spec A ⟶ X` factors as `Spec` of a ring map `φ : Γ(X, U) ⟶ A` followed by `fromSpec` of an
affine open `U`, then `(ker f).ideal U = ker φ`. (The `appLE` at the top open is `φ` up to the
`Γ`-`Spec` identification, by `IsAffineOpen.SpecMap_appLE_fromSpec` and faithfulness of `Spec`.) -/
theorem ker_ideal_of_fromSpec_factor {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {A : CommRingCat.{u}} (φ : Γ(X, U) ⟶ A) (f : Spec A ⟶ X) [QuasiCompact f]
    (hfac : f = Spec.map φ ≫ hU.fromSpec) :
    (Scheme.Hom.ker f).ideal ⟨U, hU⟩ = RingHom.ker φ.hom := by
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    rw [hfac]
    show Spec.map φ ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) = ⊤
    rw [hU.fromSpec_preimage_self]
    rfl
  have hi : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ U := le_of_eq hpre.symm
  have hkerApp : RingHom.ker ((f.app U)).hom = RingHom.ker ((f.appLE U ⊤ hi)).hom := by
    haveI : IsIso (homOfLE hi) :=
      ⟨homOfLE (le_of_eq hpre), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    have hinj : Function.Injective (((Spec A).presheaf.map (homOfLE hi).op)).hom :=
      (ConcreteCategory.bijective_of_isIso ((Spec A).presheaf.map (homOfLE hi).op)).1
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show ((f.app U)).hom a = 0 ↔
      (((Spec A).presheaf.map (homOfLE hi).op)).hom (((f.app U)).hom a) = 0
    exact ⟨fun ha => by rw [ha, map_zero], fun ha => hinj (by rw [ha, map_zero])⟩
  have happ : f.appLE U ⊤ hi = φ ≫ (Scheme.ΓSpecIso A).inv := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp]
    have h1 := hU.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec A)) hi
    have h2 : (isAffineOpen_top (Spec A)).fromSpec = Spec.map (Scheme.ΓSpecIso A).inv := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    rw [h2] at h1
    rw [← cancel_mono hU.fromSpec]
    refine h1.trans ?_
    rw [Category.assoc, ← hfac]
  have hinj2 : Function.Injective (((Scheme.ΓSpecIso A).inv)).hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1
  rw [Scheme.Hom.ker_apply, hkerApp, happ, CommRingCat.hom_comp, ← RingHom.comap_ker]
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  exact ⟨fun hh => hinj2 (by rw [hh, map_zero]), fun hh => by rw [hh, map_zero]⟩

/-- **(1a) The `Z`-chart ideal dictionary, sheaf form.** The section ideal sheaf of the
affine-point section `[p : q : 1]`, read on the affine `Z`-chart, is mathlib's
`XYIdeal W p (C q)` transported along `chartZSectionsRingEquiv`. -/
theorem ker_ideal_projModelAffineSection_chartZ (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    (Scheme.Hom.ker (projModelAffineSection W p q h)).ideal (projModelZChart W) =
      Ideal.comap (chartZSectionsRingEquiv W : _ →+* W.toAffine.CoordinateRing)
        (XYIdeal W.toAffine p (C q)) := by
  have hker := ker_ideal_of_fromSpec_factor
    (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos)
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
      CommRingCat.ofHom (affineChartHom W p q h))
    (projModelAffineSection W p q h) (projModelAffineSection_eq_fromSpec W p q h)
  refine hker.trans ?_
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, ker_affineChartHom,
    Ideal.comap_comap]
  rfl

omit [DecidableEq k] in
/-- **(1a, the section identification)** The section of the projective model attached to the
affine point `some x y` is the affine-point section `[x : y : 1]`: both are `Z`-chart points with
the same dehomogenised coordinates, and `projModelPointsEquiv` is injective. -/
theorem pointSection_some (W : WeierstrassCurve k) [W.IsElliptic] (x y : k)
    (h : W.toAffine.Nonsingular x y) :
    pointSection W (WeierstrassCurve.Affine.Point.some x y h) =
      projModelAffineSection W x y h.left := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl, Spec.map_id]
  have hsec : (affineSectionSpecPoint W k x y h.left).1 = projModelAffineSection W x y h.left := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ projModelAffineSection W x y h.left = _
    rw [hid, Category.id_comp]
  have hkey := projModelPointsEquiv_affineSectionSpecPoint W (K := k) x y h.left h
  have hsym : ((projModelPointsEquiv W k).symm) (WeierstrassCurve.Affine.Point.some x y h) =
      affineSectionSpecPoint W k x y h.left :=
    (projModelPointsEquiv W k).symm_apply_eq.mpr hkey.symm
  exact (congrArg Subtype.val hsym).trans hsec

omit [DecidableEq k] in
/-- **(1a, PROVED) The points-to-ideals dictionary on the `Z`-chart.** For an affine point
`P = some x y` of `W`, the ideal of the section ideal sheaf `I(P)` on the affine `Z`-chart is
mathlib's `XYIdeal W x (C y)`, transported along the identification `chartZSectionsRingEquiv` of
the `Z`-chart sections with the affine coordinate ring.

Together with `projModelZero_ker_ideal_chartZ` (`I(0)|_{Z-chart} = ⊤`) this is exactly the
translation that turns `chordIdealIdentity` / `verticalIdealIdentity` into the `hloc` input of
`nonempty_squareChartData_projModel_of_local` on charts inside the `Z`-chart. -/
theorem ker_ideal_pointSection_chartZ (W : WeierstrassCurve k) [W.IsElliptic] (x y : k)
    (h : W.toAffine.Nonsingular x y) :
    (Scheme.Hom.ker (pointSection W (WeierstrassCurve.Affine.Point.some x y h))).ideal
        (projModelZChart W) =
      Ideal.comap (chartZSectionsRingEquiv W : _ →+* W.toAffine.CoordinateRing)
        (XYIdeal W.toAffine x (C y)) := by
  rw [pointSection_some]
  exact ker_ideal_projModelAffineSection_chartZ W x y h.left

end ChartZDictionary

/-! ## The affine ideal identity for an arbitrary pair of points, and its `Z`-chart transport
(T10-asm-chart, items 1c and 1a assembled)

`affineIdeal W P` packages the two cases of the section ideal on the affine part — `XYIdeal` at an
affine point, the unit ideal at `0`. In these terms the *whole* case analysis of the theorem of the
square on the affine chart is one existential, `exists_affine_ideal_identity`: the chord, the
vertical, and the two `P = 0` / `Q = 0` cases with ratio `1`.

`ideal_identity_chartZ` transports it to the `Z`-chart of the projective model along
`chartZSectionsRingEquiv` (using the dictionary `ker_ideal_pointSection_chartZ'`), and
`hloc_chartZ` packages the result as the `hloc` clause of
`nonempty_squareChartData_projModel_of_local` at every point of the `Z`-chart, for the rational
function `chartZFunction W num den = num / den`. -/

section ChartZLocal

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

/-- **The affine ideal of a point of a Weierstrass curve**: mathlib's `XYIdeal` at an affine
point, and the unit ideal at the point at infinity (which is invisible on the affine chart). -/
noncomputable def affineIdeal {A : Type*} [CommRing A] (W : WeierstrassCurve.Affine A) :
    W.Point → Ideal W.CoordinateRing
  | 0 => ⊤
  | .some x y _ => XYIdeal W x (C y)

@[simp] theorem affineIdeal_zero {A : Type*} [CommRing A] (W : WeierstrassCurve.Affine A) :
    affineIdeal W 0 = ⊤ := rfl

@[simp] theorem affineIdeal_some {A : Type*} [CommRing A] (W : WeierstrassCurve.Affine A)
    {x y : A} (h : W.Nonsingular x y) : affineIdeal W (.some x y h) = XYIdeal W x (C y) := rfl

/-- **(1c, PROVED) The affine ideal identity for an arbitrary pair of points.** For all `P`, `Q`
there are nonzero `num`, `den` in the affine coordinate ring with

  `⟨den⟩ · (I(P) · I(Q)) = ⟨num⟩ · (I(P+Q) · I(0))`,

uniformly in the four cases: `P = 0` and `Q = 0` are the ratio `1`; `Q = -P` is the vertical
(`den = 1`, `num = X - x₁`, `verticalIdealIdentity`); everything else — including `P = Q`, the
tangent — is the chord (`den = X - x₃`, `num = ℓ`, `chordIdealIdentity`).

This is the case split of the theorem of the square, done once, on the affine chart. -/
theorem exists_affine_ideal_identity (W : WeierstrassCurve.Affine k) (P Q : W.Point) :
    ∃ num den : W.CoordinateRing, num ≠ 0 ∧ den ≠ 0 ∧
      Ideal.span {den} * (affineIdeal W P * affineIdeal W Q) =
        Ideal.span {num} * (affineIdeal W (P + Q) * affineIdeal W 0) := by
  match P, Q with
  | 0, Q =>
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    rw [zero_add, affineIdeal_zero, Ideal.top_mul, Ideal.mul_top]
  | .some x y h, 0 =>
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    rw [add_zero, affineIdeal_zero, Ideal.mul_top]
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · refine ⟨XClass W x₁, 1, XClass_ne_zero x₁, one_ne_zero, ?_⟩
      have hadd : (Point.some x₁ y₁ h₁ : W.Point) + Point.some x₂ y₂ h₂ = 0 :=
        Point.add_of_Y_eq hxy.1 hxy.2
      rw [hadd, affineIdeal_zero, affineIdeal_some, affineIdeal_some,
        Ideal.span_singleton_one, Ideal.top_mul, Ideal.mul_top, Ideal.mul_top, hxy.1, hxy.2]
      exact XYIdeal_neg_mul h₂
    · have hadd : (Point.some x₁ y₁ h₁ : W.Point) + Point.some x₂ y₂ h₂ =
          Point.some _ _ (nonsingular_add h₁ h₂ hxy) := Point.add_some hxy
      refine ⟨YClass W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)),
        XClass W (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)),
        YClass_ne_zero _, XClass_ne_zero _, ?_⟩
      rw [hadd, affineIdeal_zero, affineIdeal_some, affineIdeal_some, affineIdeal_some]
      exact chordIdealIdentity h₁.left h₂.left hxy

/-- Pushing an ideal forward along the inverse of a ring equivalence is pulling it back. -/
theorem ideal_map_symm_eq_comap {A B : Type*} [CommRing A] [CommRing B] (f : A ≃+* B)
    (I : Ideal B) : Ideal.map (f.symm : B →+* A) I = Ideal.comap (f : A →+* B) I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) fun a ha => ?_
  · show (f : A →+* B) ((f.symm : B →+* A) b) ∈ I
    rw [show (f : A →+* B) ((f.symm : B →+* A) b) = b from f.apply_symm_apply b]
    exact hb
  · have hb : (f : A →+* B) a ∈ I := ha
    have hmem := Ideal.mem_map_of_mem (f.symm : B →+* A) hb
    rwa [show (f.symm : B →+* A) ((f : A →+* B) a) = a from f.symm_apply_apply a] at hmem

omit [DecidableEq k] in
/-- The affine `Z`-chart of the projective model is nonempty: its ring of sections is the affine
coordinate ring, which is nontrivial. -/
theorem nonempty_projModelZChart (W : WeierstrassCurve k) :
    Nonempty ↥(projModelZChart W).1.toScheme := by
  haveI : Nontrivial Γ(projModel W, (projModelZChart W).1) :=
    (chartZSectionsRingEquiv W).toEquiv.nontrivial
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum Γ(projModel W, (projModelZChart W).1)))
  have hmem : ((projModelZChart W).2.fromSpec) p ∈
      Set.range ⇑((projModelZChart W).2.fromSpec) := ⟨p, rfl⟩
  rw [(projModelZChart W).2.range_fromSpec] at hmem
  exact ⟨⟨_, hmem⟩⟩

omit [DecidableEq k] in
/-- **(1a, uniform form)** The section ideal sheaf of *any* point of `W` on the affine `Z`-chart is
`affineIdeal`, transported along `chartZSectionsRingEquiv`. At `0` this is
`projModelZero_ker_ideal_chartZ`; at an affine point it is `ker_ideal_pointSection_chartZ`. -/
theorem ker_ideal_pointSection_chartZ' (W : WeierstrassCurve k) [W.IsElliptic]
    (P : W.toAffine.Point) :
    (Scheme.Hom.ker (pointSection W P)).ideal (projModelZChart W) =
      Ideal.comap (chartZSectionsRingEquiv W : _ →+* W.toAffine.CoordinateRing)
        (affineIdeal W.toAffine P) := by
  match P with
  | 0 =>
    rw [pointSection_zero', projModelZero_ker_ideal_chartZ, affineIdeal_zero,
      Ideal.comap_top, Ideal.span_singleton_one]
  | .some x y h => exact ker_ideal_pointSection_chartZ W x y h

/-- **The affine ideal identity, transported to the `Z`-chart of the projective model.** -/
theorem ideal_identity_chartZ (W : WeierstrassCurve k) [W.IsElliptic] (P Q : W.toAffine.Point)
    (num den : W.toAffine.CoordinateRing)
    (hid : Ideal.span {den} * (affineIdeal W.toAffine P * affineIdeal W.toAffine Q) =
      Ideal.span {num} * (affineIdeal W.toAffine (P + Q) * affineIdeal W.toAffine 0)) :
    Ideal.span {(chartZSectionsRingEquiv W).symm den} *
        ((Scheme.Hom.ker (pointSection W P)).ideal (projModelZChart W) *
          (Scheme.Hom.ker (pointSection W Q)).ideal (projModelZChart W)) =
      Ideal.span {(chartZSectionsRingEquiv W).symm num} *
        ((Scheme.Hom.ker (pointSection W (P + Q))).ideal (projModelZChart W) *
          (Scheme.Hom.ker (projModelZero W)).ideal (projModelZChart W)) := by
  have hmapI : ∀ S : W.toAffine.Point,
      Ideal.map ((chartZSectionsRingEquiv W).symm : _ →+* Γ(projModel W, (projModelZChart W).1))
          (affineIdeal W.toAffine S) =
        (Scheme.Hom.ker (pointSection W S)).ideal (projModelZChart W) := by
    intro S
    rw [ker_ideal_pointSection_chartZ' W S, ideal_map_symm_eq_comap]
  have hspan : ∀ a : W.toAffine.CoordinateRing,
      Ideal.map ((chartZSectionsRingEquiv W).symm : _ →+* Γ(projModel W, (projModelZChart W).1))
          (Ideal.span {a}) = Ideal.span {(chartZSectionsRingEquiv W).symm a} := by
    intro a
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hmap := congrArg (Ideal.map
    ((chartZSectionsRingEquiv W).symm : _ →+* Γ(projModel W, (projModelZChart W).1))) hid
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_mul, Ideal.map_mul] at hmap
  simp only [hmapI, hspan, pointSection_zero'] at hmap
  exact hmap

omit [DecidableEq k] in
/-- A nonzero element of the affine coordinate ring gives a nonzero `Z`-chart section. -/
theorem chartZSection_ne_zero (W : WeierstrassCurve k) {a : W.toAffine.CoordinateRing}
    (ha : a ≠ 0) : (chartZSectionsRingEquiv W).symm a ≠ 0 := fun h => ha (by
  have hh := congrArg (chartZSectionsRingEquiv W) h
  rwa [RingEquiv.apply_symm_apply, map_zero] at hh)

/-- **The rational function `num / den`, read on the affine `Z`-chart.** This is the `g` of
`nonempty_squareChartData_projModel_of_local`: the chord over the vertical. -/
noncomputable def chartZFunction (W : WeierstrassCurve k) [W.IsElliptic]
    (num den : W.toAffine.CoordinateRing) : (projModel W).functionField :=
  @Scheme.germToFunctionField (projModel W) _ (projModelZChart W).1
      (nonempty_projModelZChart W) ((chartZSectionsRingEquiv W).symm num) *
    (@Scheme.germToFunctionField (projModel W) _ (projModelZChart W).1
      (nonempty_projModelZChart W) ((chartZSectionsRingEquiv W).symm den))⁻¹

/-- **(PROVED) The `Z`-chart clause of `hloc`.** At every point of the affine `Z`-chart the local
Cartier data of `nonempty_squareChartData_projModel_of_local` is supplied by the chart itself, with
`num`, `den` the transported affine numerator and denominator and `g = chartZFunction W num den`.
The nonzerodivisor condition is `den ≠ 0` in the domain `Γ(projModel W, Z-chart)`, the germ identity
is the definition of `g`, and the ideal identity is `ideal_identity_chartZ`. -/
theorem hloc_chartZ (W : WeierstrassCurve k) [W.IsElliptic] (P Q : W.toAffine.Point)
    (num den : W.toAffine.CoordinateRing) (hden : den ≠ 0)
    (hid : Ideal.span {den} * (affineIdeal W.toAffine P * affineIdeal W.toAffine Q) =
      Ideal.span {num} * (affineIdeal W.toAffine (P + Q) * affineIdeal W.toAffine 0))
    (c : ↥(projModel W)) (hc : c ∈ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        chartZFunction W num den *
          @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} * ((Scheme.Hom.ker (pointSection W P)).ideal V *
          (Scheme.Hom.ker (pointSection W Q)).ideal V) =
        Ideal.span {num'} * ((Scheme.Hom.ker (pointSection W (P + Q))).ideal V *
          (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  haveI := nonempty_projModelZChart W
  haveI : IsDomain Γ(projModel W, (projModelZChart W).1) :=
    IsIntegral.component_integral (X := projModel W) (projModelZChart W).1
  have hden' : (chartZSectionsRingEquiv W).symm den ≠ 0 := chartZSection_ne_zero W hden
  have hgerm : @Scheme.germToFunctionField (projModel W) _ (projModelZChart W).1
      (nonempty_projModelZChart W) ((chartZSectionsRingEquiv W).symm den) ≠ 0 := fun h =>
    hden' (@Scheme.germToFunctionField_injective (projModel W) _ (projModelZChart W).1
      (nonempty_projModelZChart W) _ 0 (by rw [h, map_zero]))
  refine ⟨projModelZChart W, hc, (chartZSectionsRingEquiv W).symm num,
    (chartZSectionsRingEquiv W).symm den, mem_nonZeroDivisors_of_ne_zero hden', ?_,
    ideal_identity_chartZ W P Q num den hid⟩
  show _ = (_ * _) * _
  rw [mul_assoc, inv_mul_cancel₀ hgerm, mul_one]

end ChartZLocal

/-- **The leaf, reduced to a purely local Cartier statement (T10-asm-chart, entry point).**

Every structural ingredient of `exists_squareChartData_projModel` is discharged here: the four
section ideal sheaves are locally principal on nonzerodivisors
(`exists_affineOpen_ker_pointSection_span_nzd` / `exists_affineOpen_ker_projModelZero_span_nzd`),
and `nonempty_squareChartData_of_ideal_ratio` refines the charts, restricts the ideals, and
absorbs the unit ambiguity in the generators.

What is left is exactly `hloc`: around every point of `projModel W`, one affine chart carrying a
numerator/denominator presentation of one fixed rational function `g` together with the ideal
identity `⟨den⟩ · (I(P) · I(Q)) = ⟨num⟩ · (I(P+Q) · I(0))`. On charts inside the affine
`Z`-chart that identity is `chordIdealIdentity` / `verticalIdealIdentity` (mathlib's
`XYIdeal_mul_XYIdeal` / `XYIdeal_neg_mul`), transported along `chartZSectionsRingEquiv`; the only
other point of `projModel W` is the point at infinity, where three of the four ideals are the unit
ideal by `ker_ideal_eq_top_of_preimage_eq_bot` and the fourth is `⟨projModelSectionRoot W⟩`. -/
theorem nonempty_squareChartData_projModel_of_local (W : WeierstrassCurve k) [W.IsElliptic]
    (P Q : W.toAffine.Point) (g : (projModel W).functionField)
    (hloc : ∀ c : ↥(projModel W), ∃ (V : (projModel W).affineOpens) (hc : c ∈ V.1)
      (num den : Γ(projModel W, V.1)), den ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hc⟩⟩ num =
        g * @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hc⟩⟩ den ∧
      Ideal.span {den} * ((Scheme.Hom.ker (pointSection W P)).ideal V *
          (Scheme.Hom.ker (pointSection W Q)).ideal V) =
        Ideal.span {num} * ((Scheme.Hom.ker (pointSection W (P + Q))).ideal V *
          (Scheme.Hom.ker (projModelZero W)).ideal V)) :
    Nonempty (SquareChartData (Scheme.Hom.ker (pointSection W P))
      (Scheme.Hom.ker (pointSection W Q)) (Scheme.Hom.ker (pointSection W (P + Q)))
      (Scheme.Hom.ker (projModelZero W))) :=
  nonempty_squareChartData_of_ideal_ratio
    (exists_affineOpen_ker_pointSection_span_nzd W P)
    (exists_affineOpen_ker_pointSection_span_nzd W Q)
    (exists_affineOpen_ker_pointSection_span_nzd W (P + Q))
    (exists_affineOpen_ker_projModelZero_span_nzd W) g hloc

/-! ## The chart at infinity (T10-asm-chart, item 1b)

`projModelZChart_sup_sectionNeighborhood_eq_top` covers `projModel W` by the affine `Z`-chart and
the section neighbourhood `D(v)` inside the `Y`-chart `AdjoinRoot (infChartCubic W)`, whose
coordinates are `s = X/Y` (`AdjoinRoot.root`, the uniformiser at `O`) and `t = Z/Y`
(`infChartTElem`), related by `t · w = s³` with `w := v − a₂s²` (`tel_mul_infChartW`). The only
point of the model off the `Z`-chart is `[0 : 1 : 0]`, and around it the clause of
`nonempty_squareChartData_projModel_of_local` is supplied by the chart

  `V := D(v · Nn · Dd) ⊆ D(v)`  (`infChartOpen`),

where `Nn`, `Dd` are a numerator and a denominator, both `≡ 1 (mod (s, t))`, of the rational
function `g · sⁿ` — so that `g · sⁿ` is a *unit* on `V`. Since `V` also avoids `P`, `Q` and `P + Q`,
the four ideals restrict to `I(P)|V = I(Q)|V = ⊤`, `I(P+Q)|V · I(0)|V = ⟨sⁿ⟩`, and the whole clause
collapses to `num' = 1`, `den' = sⁿ · (g·sⁿ)⁻¹` (`hloc_off_chartZ_aux`).

The dictionary that computes `g` at infinity is `OverlapRel`: `OverlapRel W b a j` says that the
`Y`-chart element `b` *is* the `Z`-chart element `a` times `tʲ` in the overlap localization. It
transports to the function field (`germY_eq_germZ_mul`, through
`overlap_sections_equation_of_loc`), and it is also exactly what proves *avoidance*
(`ker_ideal_pointSection_infChartOpen_eq_top`): if the cutter `v · Nn · Dd` factors through an `a`
vanishing at an affine point, then that point misses `V`, so the section ideal there is `⊤`.

For the chord `g = ℓ/(x − x₃)` this is `n = 1`, `Nn = (1 − ℓs − μt)·w`, `Dd = w − x₃s²`; for the
vertical `g = x − x₁` it is `n = 2`, `Nn = w − x₁s²`, `Dd = 1`. In both cases `Nn · Dd` restricts on
the overlap to `x⁵·num·den` resp. `x⁴·num` times a power of `t`, which is the avoidance input.

**Two logged dead ends.** `WeilPairing/LineVertical.lean` is *not* about the chord and the vertical
(no `linePolynomial`, no `slope`, no `addX`), and the `ProjIsPrincipal` /
`kappaDivisor_add_linEquiv` route is unsound over non-closed fields — see the
`exists_functionField_projectiveDivisorOf_kappa` note above. -/

section InfinityChart

open WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- `w := v - a₂ s²`, the companion of the section unit with `t · w = s³`. -/
noncomputable def infChartW (W : WeierstrassCurve R) : AdjoinRoot (infChartCubic W) :=
  sectionUnitElem W -
    algebraMap (Polynomial R) _ (Polynomial.C W.a₂) * AdjoinRoot.root (infChartCubic W) ^ 2

theorem tel_mul_infChartW (W : WeierstrassCurve R) :
    infChartTElem W * infChartW W = AdjoinRoot.root (infChartCubic W) ^ 3 := by
  have h := tel_mul_sectionUnitElem W
  unfold infChartW infChartTElem
  have hterm : algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))
      (Polynomial.C W.a₂ * Polynomial.X) =
      algebraMap (Polynomial R) _ (Polynomial.C W.a₂) *
        algebraMap (Polynomial R) _ Polynomial.X := by
    rw [map_mul]
  rw [hterm] at h
  linear_combination h

/-- A constant of the base ring, in the infinity chart. -/
noncomputable abbrev infChartConst (W : WeierstrassCurve R) (a : R) :
    AdjoinRoot (infChartCubic W) :=
  algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) (Polynomial.C a)

/-! ### The overlap dictionary `OverlapRel` -/

section OverlapDict

/-- `t` is invertible in the overlap localization. -/
theorem isUnit_algebraMap_infChartTElem (W : WeierstrassCurve R) :
    IsUnit (algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
      (infChartTElem W)) :=
  IsLocalization.map_units (M := Submonoid.powers (infChartTElem W)) _
    ⟨infChartTElem W, ⟨1, pow_one _⟩⟩

/-- The overlap relation `b = a · tʲ`: the `Y`-chart element `b` is the `Z`-chart element `a`
times `tʲ` in the overlap localization. -/
def OverlapRel (W : WeierstrassCurve R) (b : AdjoinRoot (infChartCubic W))
    (a : W.toAffine.CoordinateRing) (j : ℕ) : Prop :=
  algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W)) b =
    overlapMap W a *
      algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) ^ j

theorem OverlapRel.mul {W : WeierstrassCurve R} {b₁ b₂ : AdjoinRoot (infChartCubic W)}
    {a₁ a₂ : W.toAffine.CoordinateRing} {j₁ j₂ : ℕ}
    (h₁ : OverlapRel W b₁ a₁ j₁) (h₂ : OverlapRel W b₂ a₂ j₂) :
    OverlapRel W (b₁ * b₂) (a₁ * a₂) (j₁ + j₂) := by
  unfold OverlapRel at h₁ h₂ ⊢
  rw [map_mul, h₁, h₂, map_mul, pow_add]
  ring

theorem OverlapRel.sub {W : WeierstrassCurve R} {b₁ b₂ : AdjoinRoot (infChartCubic W)}
    {a₁ a₂ : W.toAffine.CoordinateRing} {j : ℕ}
    (h₁ : OverlapRel W b₁ a₁ j) (h₂ : OverlapRel W b₂ a₂ j) :
    OverlapRel W (b₁ - b₂) (a₁ - a₂) j := by
  unfold OverlapRel at h₁ h₂ ⊢
  rw [map_sub, h₁, h₂, map_sub]
  ring

theorem OverlapRel.add {W : WeierstrassCurve R} {b₁ b₂ : AdjoinRoot (infChartCubic W)}
    {a₁ a₂ : W.toAffine.CoordinateRing} {j : ℕ}
    (h₁ : OverlapRel W b₁ a₁ j) (h₂ : OverlapRel W b₂ a₂ j) :
    OverlapRel W (b₁ + b₂) (a₁ + a₂) j := by
  unfold OverlapRel at h₁ h₂ ⊢
  rw [map_add, h₁, h₂, map_add]
  ring

theorem OverlapRel.pow {W : WeierstrassCurve R} {b : AdjoinRoot (infChartCubic W)}
    {a : W.toAffine.CoordinateRing} {j : ℕ} (h : OverlapRel W b a j) (n : ℕ) :
    OverlapRel W (b ^ n) (a ^ n) (j * n) := by
  unfold OverlapRel at h ⊢
  rw [map_pow, h, map_pow]
  ring

theorem overlapRel_const (W : WeierstrassCurve R) (a : R) :
    OverlapRel W (infChartConst W a) (algebraMap R W.toAffine.CoordinateRing a) 0 := by
  unfold OverlapRel
  rw [pow_zero, mul_one]
  show _ = overlapMap W (AdjoinRoot.mk _ (Polynomial.C (Polynomial.C a)))
  rw [show AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (Polynomial.C a)) =
    AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a) from rfl]
  unfold overlapMap
  rw [AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

theorem overlapRel_root (W : WeierstrassCurve R) :
    OverlapRel W (AdjoinRoot.root (infChartCubic W)) (coordX W) 1 := by
  unfold OverlapRel
  rw [pow_one, overlapMap_coordX]
  unfold overlapXElem
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

theorem overlapRel_one (W : WeierstrassCurve R) :
    OverlapRel W 1 (coordY W) 1 := by
  unfold OverlapRel
  rw [pow_one, overlapMap_coordY]
  unfold overlapInvT
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

theorem OverlapRel.cancel {W : WeierstrassCurve R} {b : AdjoinRoot (infChartCubic W)}
    {a : W.toAffine.CoordinateRing} {j : ℕ}
    (h : OverlapRel W (infChartTElem W * b) a (j + 1)) : OverlapRel W b a j := by
  unfold OverlapRel at h ⊢
  obtain ⟨u, hu⟩ := isUnit_algebraMap_infChartTElem W
  rw [map_mul, ← hu] at h
  refine (Units.mul_right_inj u).mp ?_
  rw [h, ← hu]
  ring

theorem overlapRel_infChartW (W : WeierstrassCurve R) :
    OverlapRel W (infChartW W) (coordX W ^ 3) 2 := by
  refine OverlapRel.cancel ?_
  rw [tel_mul_infChartW W]
  simpa using (overlapRel_root W).pow 3

theorem overlapRel_sectionUnitElem (W : WeierstrassCurve R) :
    OverlapRel W (sectionUnitElem W)
      (coordX W ^ 3 + algebraMap R W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) 2 := by
  have hsplit : sectionUnitElem W =
      infChartW W + infChartConst W W.a₂ * AdjoinRoot.root (infChartCubic W) ^ 2 := by
    unfold infChartW
    ring
  rw [hsplit]
  refine OverlapRel.add (overlapRel_infChartW W) ?_
  simpa using (overlapRel_const W W.a₂).mul ((overlapRel_root W).pow 2)

end OverlapDict

section InfinityGerm


omit [DecidableEq k] in
/-- The `Y`-chart of the projective model is nonempty: the zero section lands in it. -/
theorem nonempty_projModelYChart (W : WeierstrassCurve k) :
    Nonempty ↥(projModelYChart W).1.toScheme := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum k))
  have hmem : p ∈ projModelZero W ⁻¹ᵁ ((projModelYChart W : (projModel W).Opens)) := by
    rw [projModelZero_preimage_yChart W]
    trivial
  exact ⟨⟨_, hmem⟩⟩

omit [DecidableEq k] in
theorem nonempty_projModelOverlap (W : WeierstrassCurve k) :
    Nonempty ↥(Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).toScheme := by
  have h := AlgebraicGeometry.Scheme.Modules.nonempty_inf_of_nonempty
    (C := projModel W) (U := (projModelYChart W).1) (V := (projModelZChart W).1)
    (nonempty_projModelYChart W) (nonempty_projModelZChart W)
  rw [show ((projModelYChart W).1 ⊓ (projModelZChart W).1 : (projModel W).Opens) =
    Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) from
    (Proj.basicOpen_mul _ _ _).symm] at h
  exact h

/-- The germ in the function field of a `Y`-chart element. -/
noncomputable def germY (W : WeierstrassCurve k) :
    AdjoinRoot (infChartCubic W) →+* (projModel W).functionField :=
  (@Scheme.germToFunctionField (projModel W) _ (projModelYChart W).1
      (nonempty_projModelYChart W)).hom.comp
    (chartYSectionsRingEquiv W).symm.toRingHom

/-- The germ in the function field of a `Z`-chart element. -/
noncomputable def germZ (W : WeierstrassCurve k) :
    W.toAffine.CoordinateRing →+* (projModel W).functionField :=
  (@Scheme.germToFunctionField (projModel W) _ (projModelZChart W).1
      (nonempty_projModelZChart W)).hom.comp
    (chartZSectionsRingEquiv W).symm.toRingHom

omit [DecidableEq k] in
theorem germY_injective (W : WeierstrassCurve k) : Function.Injective (germY W) :=
  (@Scheme.germToFunctionField_injective (projModel W) _ (projModelYChart W).1
    (nonempty_projModelYChart W)).comp (chartYSectionsRingEquiv W).symm.injective

omit [DecidableEq k] in
theorem germZ_injective (W : WeierstrassCurve k) : Function.Injective (germZ W) :=
  (@Scheme.germToFunctionField_injective (projModel W) _ (projModelZChart W).1
    (nonempty_projModelZChart W)).comp (chartZSectionsRingEquiv W).symm.injective

omit [DecidableEq k] in
/-- **The overlap dictionary in the function field.** -/
theorem germY_eq_germZ_mul (W : WeierstrassCurve k) {b : AdjoinRoot (infChartCubic W)}
    {a : W.toAffine.CoordinateRing} {j : ℕ} (h : OverlapRel W b a j) :
    germY W b = germZ W a * germY W (infChartTElem W) ^ j := by
  haveI := nonempty_projModelOverlap W
  haveI := nonempty_projModelYChart W
  haveI := nonempty_projModelZChart W
  have hsec := overlap_sections_equation_of_loc W a b (infChartTElem W) j h
  have hle1 : Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≤ (projModelYChart W).1 :=
    Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ⟨_, rfl⟩
  have hle2 : Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≤ (projModelZChart W).1 :=
    Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      ⟨_, mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))⟩
  have hgerm := congrArg (@Scheme.germToFunctionField (projModel W) _ _
    (nonempty_projModelOverlap W)) hsec
  rw [map_mul, map_pow] at hgerm
  rw [show germY W b = @Scheme.germToFunctionField (projModel W) _ (projModelYChart W).1
      (nonempty_projModelYChart W) ((chartYSectionsRingEquiv W).symm b) from rfl,
    show germZ W a = @Scheme.germToFunctionField (projModel W) _ (projModelZChart W).1
      (nonempty_projModelZChart W) ((chartZSectionsRingEquiv W).symm a) from rfl,
    show germY W (infChartTElem W) = @Scheme.germToFunctionField (projModel W) _
      (projModelYChart W).1 (nonempty_projModelYChart W)
      ((chartYSectionsRingEquiv W).symm (infChartTElem W)) from rfl,
    ← AlgebraicGeometry.Scheme.Modules.germToFunctionField_restrict hle1
      ((chartYSectionsRingEquiv W).symm b),
    ← AlgebraicGeometry.Scheme.Modules.germToFunctionField_restrict hle2
      ((chartZSectionsRingEquiv W).symm a),
    ← AlgebraicGeometry.Scheme.Modules.germToFunctionField_restrict hle1
      ((chartYSectionsRingEquiv W).symm (infChartTElem W))]
  exact hgerm

end InfinityGerm

/-! ### The chart `D(v · F)`, its four ideals, and the generic clause -/

section InfinityOpen

/-- Membership in a basic open of an affine open, read on the chart prime. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : ↥X) (hx : x ∈ U) (f : Γ(X, U)) :
    x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  refine Iff.symm ?_
  rw [← PrimeSpectrum.mem_basicOpen]
  change hU.isoSpec.hom ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen f ↔ _
  rw [← hU.fromSpec_preimage_basicOpen]
  change hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ x ∈ X.basicOpen f
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩]

/-- Restriction is transitive. -/
theorem presheaf_map_map {X : Scheme.{u}} {U V T : X.Opens} (h₁ : V ≤ U) (h₂ : T ≤ V)
    (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom a) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- **The chart at infinity cut out by `F`**: the basic open `D(v · F)` of the `Y`-chart. -/
noncomputable def infChartOpen (W : WeierstrassCurve R) (F : AdjoinRoot (infChartCubic W)) :
    (projModel W).affineOpens :=
  (projModel W).affineBasicOpen (U := projModelYChart W)
    ((chartYSectionsRingEquiv W).symm (sectionUnitElem W * F))

theorem infChartOpen_le_chartY (W : WeierstrassCurve R) (F : AdjoinRoot (infChartCubic W)) :
    (infChartOpen W F).1 ≤ (projModelYChart W).1 :=
  (projModel W).basicOpen_le _

theorem infChartOpen_le_sectionNeighborhood (W : WeierstrassCurve R)
    (F : AdjoinRoot (infChartCubic W)) :
    (infChartOpen W F).1 ≤ (projModelSectionNeighborhood W).1 := by
  show (projModel W).basicOpen ((chartYSectionsRingEquiv W).symm (sectionUnitElem W * F)) ≤
    (projModel W).basicOpen (projModelSectionUnitSection W)
  rw [map_mul, Scheme.basicOpen_mul]
  exact inf_le_left

/-- Restriction of a `Y`-chart element to the chart at infinity. -/
noncomputable def infChartRes (W : WeierstrassCurve R) (F : AdjoinRoot (infChartCubic W)) :
    AdjoinRoot (infChartCubic W) →+* Γ(projModel W, (infChartOpen W F).1) :=
  ((projModel W).presheaf.map (homOfLE (infChartOpen_le_chartY W F)).op).hom.comp
    (chartYSectionsRingEquiv W).symm.toRingHom

omit [DecidableEq k] in
/-- The point at infinity lies in every chart `D(v · F)` with `F ≡ 1 mod (s, t)`. -/
theorem mem_infChartOpen (W : WeierstrassCurve k)
    (F : AdjoinRoot (infChartCubic W))
    (hF : F - 1 ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W})
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    c ∈ (infChartOpen W F).1 := by
  have hcY : c ∈ (projModelYChart W).1 := by
    have hcover : (projModelYChart W : (projModel W).Opens) ⊔
        (projModelZChart W : (projModel W).Opens) = ⊤ :=
      basicOpen_X1_sup_basicOpen_X2_eq_top W
    have hmem : c ∈ (projModelYChart W : (projModel W).Opens) ⊔
        (projModelZChart W : (projModel W).Opens) := by rw [hcover]; trivial
    rcases (TopologicalSpace.Opens.mem_sup).mp hmem with h | h
    · exact h
    · exact absurd h hc
  let q := (projModelYChart W).2.primeIdealOf ⟨c, hcY⟩
  let P : Ideal (AdjoinRoot (infChartCubic W)) := Ideal.map (chartYSectionsRingEquiv W) q.asIdeal
  letI : P.IsPrime := Ideal.map_isPrime_of_equiv (chartYSectionsRingEquiv W)
  have htq : (chartYSectionsRingEquiv W).symm (infChartTElem W) ∈ q.asIdeal := by
    by_contra htq
    exact hc ((mem_projModelZChart_iff_not_mem_infChartTElem W c hcY).mpr htq)
  have htP : infChartTElem W ∈ P := by
    have hmap := Ideal.mem_map_of_mem (chartYSectionsRingEquiv W) htq
    simpa only [RingEquiv.apply_symm_apply] using hmap
  have hsP : AdjoinRoot.root (infChartCubic W) ∈ P := root_mem_of_tel_mem W P htP
  have hspan : Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} ≤ P := by
    refine Ideal.span_le.mpr ?_
    rintro a (rfl | rfl)
    · exact hsP
    · exact htP
  have hvP : sectionUnitElem W - 1 ∈ P := hspan (sectionUnitElem_sub_one_mem W)
  have hFP : F - 1 ∈ P := hspan hF
  have hprod : sectionUnitElem W * F - 1 ∈ P := by
    have hrw : sectionUnitElem W * F - 1 = (sectionUnitElem W - 1) * F + (F - 1) := by ring
    rw [hrw]
    exact P.add_mem (P.mul_mem_right _ hvP) hFP
  have hnot : sectionUnitElem W * F ∉ P := by
    intro hmem
    have h1 : (1 : AdjoinRoot (infChartCubic W)) ∈ P := by
      simpa only [sub_sub_cancel] using P.sub_mem hmem hprod
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hq : (chartYSectionsRingEquiv W).symm (sectionUnitElem W * F) ∉ q.asIdeal := by
    intro hmemq
    refine hnot ?_
    have hmap := Ideal.mem_map_of_mem (chartYSectionsRingEquiv W) hmemq
    simpa only [RingEquiv.apply_symm_apply] using hmap
  exact (mem_basicOpen_iff_notMem_primeIdealOf (projModelYChart W).2 c hcY _).mpr hq

/-- On the chart at infinity the zero-section ideal is generated by `s`. -/
theorem projModelZero_ker_ideal_infChartOpen (W : WeierstrassCurve R)
    (F : AdjoinRoot (infChartCubic W)) :
    (projModelZero W).ker.ideal (infChartOpen W F) =
      Ideal.span {infChartRes W F (AdjoinRoot.root (infChartCubic W))} := by
  have hle : infChartOpen W F ≤ projModelSectionNeighborhood W :=
    infChartOpen_le_sectionNeighborhood W F
  have hmap := (projModelZero W).ker.map_ideal hle
  have hres : ((projModel W).presheaf.map (homOfLE hle).op).hom (projModelSectionRoot W) =
      infChartRes W F (AdjoinRoot.root (infChartCubic W)) :=
    presheaf_map_map _ _ _
  rw [← hmap, projModelZero_ker_ideal_sectionNeighborhood W, Ideal.map_span,
    Set.image_singleton]
  exact congrArg (fun z => Ideal.span ({z} : Set Γ(projModel W, (infChartOpen W F).1))) hres

omit [DecidableEq k] in
/-- **Avoidance.** If, on the chart overlap, the cutter `v · F` of the chart at infinity is the
`Z`-chart element `a` times a power of `t`, and `a` vanishes at the affine point `(x, y)`, then
that point misses the chart, so its section ideal there is the unit ideal. -/
theorem ker_ideal_pointSection_infChartOpen_eq_top (W : WeierstrassCurve k) [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (F : AdjoinRoot (infChartCubic W)) {a : W.toAffine.CoordinateRing} {m : ℕ}
    (hrel : OverlapRel W (sectionUnitElem W * F) a m)
    (ha : a ∈ WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)) :
    (Scheme.Hom.ker (pointSection W (WeierstrassCurve.Affine.Point.some x y h))).ideal
      (infChartOpen W F) = ⊤ := by
  set f := pointSection W (WeierstrassCurve.Affine.Point.some x y h) with hf
  refine ker_ideal_eq_top_of_preimage_eq_bot f _ ?_
  have hZ : f ⁻¹ᵁ (projModelZChart W).1 = ⊤ := by
    rw [hf, pointSection_some W x y h, projModelAffineSection_eq_fromSpec W x y h.left]
    show Spec.map _ ⁻¹ᵁ ((projModelZChart W).2.fromSpec ⁻¹ᵁ (projModelZChart W).1) = ⊤
    rw [(projModelZChart W).2.fromSpec_preimage_self]
    rfl
  have hker : (f.app (projModelZChart W).1).hom ((chartZSectionsRingEquiv W).symm a) = 0 := by
    have hid := ker_ideal_pointSection_chartZ W x y h
    rw [Scheme.Hom.ker_apply] at hid
    have hmem : (chartZSectionsRingEquiv W).symm a ∈
        RingHom.ker (f.app (projModelZChart W).1).hom := by
      rw [hf, hid, Ideal.mem_comap]
      show (chartZSectionsRingEquiv W) ((chartZSectionsRingEquiv W).symm a) ∈ _
      rw [RingEquiv.apply_symm_apply]
      exact ha
    exact hmem
  have hle1 : Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≤ (projModelYChart W).1 :=
    Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ⟨_, rfl⟩
  have hle2 : Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≤ (projModelZChart W).1 :=
    Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      ⟨_, mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))⟩
  have hsec0 := overlap_sections_equation_of_loc W a (sectionUnitElem W * F) (infChartTElem W) m
    hrel
  have hsec : ((projModel W).presheaf.map (homOfLE hle1).op).hom
        ((chartYSectionsRingEquiv W).symm (sectionUnitElem W * F)) =
      ((projModel W).presheaf.map (homOfLE hle2).op).hom
          ((chartZSectionsRingEquiv W).symm a) *
        ((projModel W).presheaf.map (homOfLE hle1).op).hom
          ((chartYSectionsRingEquiv W).symm (infChartTElem W)) ^ m := hsec0
  have hBY : (projModel W).basicOpen (((projModel W).presheaf.map (homOfLE hle1).op).hom
      ((chartYSectionsRingEquiv W).symm (sectionUnitElem W * F))) =
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ⊓ (infChartOpen W F).1 :=
    Scheme.basicOpen_res (projModel W)
      ((chartYSectionsRingEquiv W).symm (sectionUnitElem W * F)) (homOfLE hle1).op
  have hBZ : (projModel W).basicOpen (((projModel W).presheaf.map (homOfLE hle2).op).hom
      ((chartZSectionsRingEquiv W).symm a)) =
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ⊓
        (projModel W).basicOpen ((chartZSectionsRingEquiv W).symm a) :=
    Scheme.basicOpen_res (projModel W) ((chartZSectionsRingEquiv W).symm a) (homOfLE hle2).op
  have hle : (infChartOpen W F).1 ⊓ (projModelZChart W).1 ≤
      (projModel W).basicOpen ((chartZSectionsRingEquiv W).symm a) := by
    have hOv : Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
        (projModelYChart W).1 ⊓ (projModelZChart W).1 := Proj.basicOpen_mul _ _ _
    calc (infChartOpen W F).1 ⊓ (projModelZChart W).1
        ≤ Proj.basicOpen (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
              (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ⊓ (infChartOpen W F).1 := by
          rw [hOv]
          exact le_inf (le_inf (inf_le_left.trans (infChartOpen_le_chartY W F)) inf_le_right)
            inf_le_left
      _ = (projModel W).basicOpen (((projModel W).presheaf.map (homOfLE hle1).op).hom
            ((chartYSectionsRingEquiv W).symm (sectionUnitElem W * F))) := hBY.symm
      _ ≤ (projModel W).basicOpen (((projModel W).presheaf.map (homOfLE hle2).op).hom
            ((chartZSectionsRingEquiv W).symm a)) := by
          rw [hsec, Scheme.basicOpen_mul]
          exact inf_le_left
      _ ≤ (projModel W).basicOpen ((chartZSectionsRingEquiv W).symm a) := by
          rw [hBZ]; exact inf_le_right
  rw [_root_.eq_bot_iff]
  intro z hz
  have hzZ : z ∈ f ⁻¹ᵁ (projModelZChart W).1 := by rw [hZ]; trivial
  have hmem : z ∈ f ⁻¹ᵁ ((projModel W).basicOpen ((chartZSectionsRingEquiv W).symm a)) :=
    hle ⟨hz, hzZ⟩
  rw [Scheme.preimage_basicOpen] at hmem
  have hzero : (f.app (projModelZChart W).1) ((chartZSectionsRingEquiv W).symm a) = 0 := hker
  rw [hzero, Scheme.basicOpen_zero] at hmem
  exact hmem

/-- The cutter of the chart at infinity is a unit there. -/
theorem isUnit_infChartRes_cutter (W : WeierstrassCurve R) (F : AdjoinRoot (infChartCubic W)) :
    IsUnit (infChartRes W F (sectionUnitElem W * F)) :=
  AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen (projModel W).toRingedSpace _

theorem isUnit_infChartRes_of_dvd (W : WeierstrassCurve R) (F b : AdjoinRoot (infChartCubic W))
    (hdvd : b ∣ sectionUnitElem W * F) : IsUnit (infChartRes W F b) := by
  obtain ⟨e, he⟩ := hdvd
  have hu := isUnit_infChartRes_cutter W F
  rw [he, map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

omit [DecidableEq k] in
theorem germToFunctionField_infChartRes (W : WeierstrassCurve k)
    (F : AdjoinRoot (infChartCubic W)) [hne : Nonempty ↥(infChartOpen W F).1]
    (b : AdjoinRoot (infChartCubic W)) :
    @Scheme.germToFunctionField (projModel W) _ (infChartOpen W F).1 hne (infChartRes W F b) =
      germY W b := by
  haveI := nonempty_projModelYChart W
  haveI : Nonempty ↥(infChartOpen W F).1.toScheme := hne
  exact AlgebraicGeometry.Scheme.Modules.germToFunctionField_restrict
    (infChartOpen_le_chartY W F) ((chartYSectionsRingEquiv W).symm b)

/-- **The generic clause at infinity.**  `Nn`, `Dd` are the numerator and denominator of
`g · sⁿ` in the `Y`-chart; the chart is `D(v · Nn · Dd)`. -/
theorem hloc_off_chartZ_aux (W : WeierstrassCurve k) [W.IsElliptic] (P Q : W.toAffine.Point)
    (g : (projModel W).functionField) (n : ℕ) (Nn Dd : AdjoinRoot (infChartCubic W))
    (hNn : Nn - 1 ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W})
    (hDd : Dd - 1 ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W})
    (hkey : g * germY W (AdjoinRoot.root (infChartCubic W)) ^ n * germY W Dd = germY W Nn)
    (hIP : (Scheme.Hom.ker (pointSection W P)).ideal (infChartOpen W (Nn * Dd)) = ⊤)
    (hIQ : (Scheme.Hom.ker (pointSection W Q)).ideal (infChartOpen W (Nn * Dd)) = ⊤)
    (hIR : (Scheme.Hom.ker (pointSection W (P + Q))).ideal (infChartOpen W (Nn * Dd)) *
        Ideal.span {infChartRes W (Nn * Dd) (AdjoinRoot.root (infChartCubic W))} =
      Ideal.span {infChartRes W (Nn * Dd) (AdjoinRoot.root (infChartCubic W)) ^ n})
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        g * @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} * ((Scheme.Hom.ker (pointSection W P)).ideal V *
          (Scheme.Hom.ker (pointSection W Q)).ideal V) =
        Ideal.span {num'} * ((Scheme.Hom.ker (pointSection W (P + Q))).ideal V *
          (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  have hprod : Nn * Dd - 1 ∈
      Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} := by
    have hrw : Nn * Dd - 1 = (Nn - 1) * Dd + (Dd - 1) := by ring
    rw [hrw]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hNn) hDd
  have hcv : c ∈ (infChartOpen W (Nn * Dd)).1 := mem_infChartOpen W (Nn * Dd) hprod c hc
  haveI hne : Nonempty ↥(infChartOpen W (Nn * Dd)).1 := ⟨⟨c, hcv⟩⟩
  haveI hne' : Nonempty ↥(infChartOpen W (Nn * Dd)).1.toScheme := ⟨⟨c, hcv⟩⟩
  haveI : IsDomain Γ(projModel W, (infChartOpen W (Nn * Dd)).1) :=
    IsIntegral.component_integral (X := projModel W) (infChartOpen W (Nn * Dd)).1
  set sV := infChartRes W (Nn * Dd) (AdjoinRoot.root (infChartCubic W)) with hsV
  have hNnU : IsUnit (infChartRes W (Nn * Dd) Nn) :=
    isUnit_infChartRes_of_dvd W (Nn * Dd) Nn ⟨sectionUnitElem W * Dd, by ring⟩
  obtain ⟨X, hX⟩ := isUnit_iff_exists_inv.mp hNnU
  refine ⟨infChartOpen W (Nn * Dd), hcv, 1, sV ^ n * (infChartRes W (Nn * Dd) Dd * X),
    ?_, ?_, ?_⟩
  · -- nonzerodivisor
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    have hg : g * @Scheme.germToFunctionField (projModel W) _ (infChartOpen W (Nn * Dd)).1 hne
        (sV ^ n * (infChartRes W (Nn * Dd) Dd * X)) = 1 := by
      rw [map_mul, map_pow, map_mul, hsV, germToFunctionField_infChartRes,
        germToFunctionField_infChartRes]
      calc g * (germY W (AdjoinRoot.root (infChartCubic W)) ^ n *
            (germY W Dd * @Scheme.germToFunctionField (projModel W) _ _ hne X))
          = (g * germY W (AdjoinRoot.root (infChartCubic W)) ^ n * germY W Dd) *
            @Scheme.germToFunctionField (projModel W) _ _ hne X := by ring
        _ = germY W Nn * @Scheme.germToFunctionField (projModel W) _ _ hne X := by rw [hkey]
        _ = 1 := by
            rw [← germToFunctionField_infChartRes W (Nn * Dd) Nn, ← map_mul, hX, map_one]
    rw [h0, map_zero, mul_zero] at hg
    exact zero_ne_one hg
  · -- germ identity
    rw [map_one, map_mul, map_pow, map_mul, hsV, germToFunctionField_infChartRes,
      germToFunctionField_infChartRes]
    calc (1 : (projModel W).functionField)
        = germY W Nn * @Scheme.germToFunctionField (projModel W) _ _ ⟨⟨c, hcv⟩⟩ X := by
          rw [← germToFunctionField_infChartRes W (Nn * Dd) Nn, ← map_mul, hX, map_one]
      _ = (g * germY W (AdjoinRoot.root (infChartCubic W)) ^ n * germY W Dd) *
            @Scheme.germToFunctionField (projModel W) _ _ ⟨⟨c, hcv⟩⟩ X := by rw [hkey]
      _ = g * (germY W (AdjoinRoot.root (infChartCubic W)) ^ n *
            (germY W Dd * @Scheme.germToFunctionField (projModel W) _ _ ⟨⟨c, hcv⟩⟩ X)) := by ring
  · -- ideal identity
    have hDdU : IsUnit (infChartRes W (Nn * Dd) Dd) :=
      isUnit_infChartRes_of_dvd W (Nn * Dd) Dd ⟨sectionUnitElem W * Nn, by ring⟩
    have hXU : IsUnit X := isUnit_iff_exists_inv'.mpr ⟨infChartRes W (Nn * Dd) Nn, hX⟩
    rw [hIP, hIQ, projModelZero_ker_ideal_infChartOpen W (Nn * Dd), ← hsV,
      Ideal.span_singleton_one]
    simp only [Ideal.top_mul, Ideal.mul_top]
    rw [hIR, Ideal.span_singleton_mul_right_unit (hDdU.mul hXU) (sV ^ n)]

end InfinityOpen

/-! ### The chord and the vertical -/

section InfinityCases

open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

theorem overlapRel_tElem (W : WeierstrassCurve R) : OverlapRel W (infChartTElem W) 1 1 := by
  unfold OverlapRel
  rw [map_one, one_mul, pow_one]

theorem mul_sub_one_mem {A : Type*} [CommRing A] {I : Ideal A} {a b : A}
    (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) : a * b - 1 ∈ I := by
  have hrw : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [hrw]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb

theorem root_mem_infSpan (W : WeierstrassCurve R) :
    AdjoinRoot.root (infChartCubic W) ∈
      Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem tElem_mem_infSpan (W : WeierstrassCurve R) :
    infChartTElem W ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem infChartW_sub_one_mem (W : WeierstrassCurve R) :
    infChartW W - 1 ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} := by
  have hrw : infChartW W - 1 = (sectionUnitElem W - 1) -
      (infChartConst W W.a₂ * AdjoinRoot.root (infChartCubic W)) *
        AdjoinRoot.root (infChartCubic W) := by
    unfold infChartW
    ring
  rw [hrw]
  exact Ideal.sub_mem _ (sectionUnitElem_sub_one_mem W)
    (Ideal.mul_mem_left _ _ (root_mem_infSpan W))

theorem YClass_eq_coordY_sub_of (W : WeierstrassCurve R) (p : Polynomial R) :
    YClass W.toAffine p = coordY W - AdjoinRoot.of W.toAffine.polynomial p := by
  show AdjoinRoot.mk _ (Polynomial.X - Polynomial.C p) =
    AdjoinRoot.mk _ Polynomial.X - AdjoinRoot.mk _ (Polynomial.C p)
  rw [map_sub]

theorem of_linePolynomial (W : WeierstrassCurve R) (x₁ y₁ l : R) :
    AdjoinRoot.of W.toAffine.polynomial (linePolynomial x₁ y₁ l) =
      algebraMap R W.toAffine.CoordinateRing l *
        (coordX W - algebraMap R W.toAffine.CoordinateRing x₁) +
      algebraMap R W.toAffine.CoordinateRing y₁ := by
  rw [linePolynomial, map_add, map_mul, map_sub]
  rfl


omit [DecidableEq k] in
theorem nontrivial_adjoinRoot_infChartCubic (W : WeierstrassCurve k) :
    Nontrivial (AdjoinRoot (infChartCubic W)) := by
  haveI := nonempty_projModelYChart W
  haveI : IsDomain Γ(projModel W, (projModelYChart W).1) :=
    IsIntegral.component_integral (X := projModel W) (projModelYChart W).1
  exact (chartYSectionsRingEquiv W).symm.toEquiv.nontrivial

omit [DecidableEq k] in
theorem germY_root_ne_zero (W : WeierstrassCurve k) :
    germY W (AdjoinRoot.root (infChartCubic W)) ≠ 0 := by
  haveI := nontrivial_adjoinRoot_infChartCubic W
  intro h
  have hroot : AdjoinRoot.root (infChartCubic W) = 0 :=
    germY_injective W (by rw [h, map_zero])
  have h1 : (1 : AdjoinRoot (infChartCubic W)) = 0 :=
    mem_nonZeroDivisors_iff_right.mp (infChart_root_mem_nonZeroDivisors W) 1
      (by rw [hroot, mul_zero])
  exact one_ne_zero h1

omit [DecidableEq k] in
theorem germZ_ne_zero (W : WeierstrassCurve k) {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    germZ W a ≠ 0 := fun h => ha (germZ_injective W (by rw [h, map_zero]))

omit [DecidableEq k] in
theorem chartZFunction_eq_germZ (W : WeierstrassCurve k) [W.IsElliptic]
    (num den : W.toAffine.CoordinateRing) :
    chartZFunction W num den = germZ W num * (germZ W den)⁻¹ := rfl

/-- The `Y`-chart identity `(s - x₀ t) · w = s · (w - x₀ s²)`, from `t · w = s³`. -/
theorem denInf_mul_infChartW (W : WeierstrassCurve R) (x₀ : R) :
    (AdjoinRoot.root (infChartCubic W) - infChartConst W x₀ * infChartTElem W) * infChartW W =
      AdjoinRoot.root (infChartCubic W) *
        (infChartW W - infChartConst W x₀ * AdjoinRoot.root (infChartCubic W) ^ 2) := by
  have h := tel_mul_infChartW W
  linear_combination (-(infChartConst W x₀)) * h

/-- `1 − l·s − μ·t`, the chord numerator read in the `Y`-chart. -/
noncomputable def chordNumInf (W : WeierstrassCurve R) (l mu : R) :
    AdjoinRoot (infChartCubic W) :=
  1 - infChartConst W l * AdjoinRoot.root (infChartCubic W) - infChartConst W mu * infChartTElem W

/-- `s − x₀·t`, the vertical numerator read in the `Y`-chart. -/
noncomputable def vertNumInf (W : WeierstrassCurve R) (x₀ : R) : AdjoinRoot (infChartCubic W) :=
  AdjoinRoot.root (infChartCubic W) - infChartConst W x₀ * infChartTElem W

/-- `(1 − l·s − μ·t)·w`. -/
noncomputable def chordNn (W : WeierstrassCurve R) (l mu : R) : AdjoinRoot (infChartCubic W) :=
  chordNumInf W l mu * infChartW W

/-- `w − x₀·s²`. -/
noncomputable def chordDd (W : WeierstrassCurve R) (x₀ : R) : AdjoinRoot (infChartCubic W) :=
  infChartW W - infChartConst W x₀ * AdjoinRoot.root (infChartCubic W) ^ 2

theorem overlapRel_one' (W : WeierstrassCurve R) : OverlapRel W 1 1 0 := by
  unfold OverlapRel
  rw [map_one, map_one, pow_zero, mul_one]

theorem overlapRel_chordNumInf (W : WeierstrassCurve R) (l mu : R) :
    OverlapRel W (chordNumInf W l mu)
      (coordY W - (algebraMap R W.toAffine.CoordinateRing l * coordX W +
        algebraMap R W.toAffine.CoordinateRing mu)) 1 := by
  have hA : OverlapRel W (infChartConst W l * AdjoinRoot.root (infChartCubic W))
      (algebraMap R W.toAffine.CoordinateRing l * coordX W) 1 :=
    (overlapRel_const W l).mul (overlapRel_root W)
  have hB : OverlapRel W (infChartConst W mu * infChartTElem W)
      (algebraMap R W.toAffine.CoordinateRing mu * 1) 1 :=
    (overlapRel_const W mu).mul (overlapRel_tElem W)
  have h := ((overlapRel_one W).sub hA).sub hB
  have heq : coordY W - algebraMap R W.toAffine.CoordinateRing l * coordX W -
      algebraMap R W.toAffine.CoordinateRing mu * 1 =
      coordY W - (algebraMap R W.toAffine.CoordinateRing l * coordX W +
        algebraMap R W.toAffine.CoordinateRing mu) := by ring
  exact heq ▸ h

theorem overlapRel_vertNumInf (W : WeierstrassCurve R) (x₀ : R) :
    OverlapRel W (vertNumInf W x₀)
      (coordX W - algebraMap R W.toAffine.CoordinateRing x₀) 1 := by
  have hB : OverlapRel W (infChartConst W x₀ * infChartTElem W)
      (algebraMap R W.toAffine.CoordinateRing x₀ * 1) 1 :=
    (overlapRel_const W x₀).mul (overlapRel_tElem W)
  have h := (overlapRel_root W).sub hB
  have heq : coordX W - algebraMap R W.toAffine.CoordinateRing x₀ * 1 =
      coordX W - algebraMap R W.toAffine.CoordinateRing x₀ := by ring
  exact heq ▸ h

theorem overlapRel_chordDd (W : WeierstrassCurve R) (x₀ : R) :
    OverlapRel W (chordDd W x₀)
      (coordX W ^ 2 * (coordX W - algebraMap R W.toAffine.CoordinateRing x₀)) 2 := by
  have hB : OverlapRel W
      (infChartConst W x₀ * AdjoinRoot.root (infChartCubic W) ^ 2)
      (algebraMap R W.toAffine.CoordinateRing x₀ * coordX W ^ 2) 2 :=
    (overlapRel_const W x₀).mul ((overlapRel_root W).pow 2)
  have h := (overlapRel_infChartW W).sub hB
  have heq : coordX W ^ 3 - algebraMap R W.toAffine.CoordinateRing x₀ * coordX W ^ 2 =
      coordX W ^ 2 * (coordX W - algebraMap R W.toAffine.CoordinateRing x₀) := by ring
  exact heq ▸ h

theorem overlapRel_chordNn (W : WeierstrassCurve R) (l mu : R) :
    OverlapRel W (chordNn W l mu)
      ((coordY W - (algebraMap R W.toAffine.CoordinateRing l * coordX W +
        algebraMap R W.toAffine.CoordinateRing mu)) * coordX W ^ 3) 3 :=
  (overlapRel_chordNumInf W l mu).mul (overlapRel_infChartW W)

theorem chordNumInf_sub_one_mem (W : WeierstrassCurve R) (l mu : R) :
    chordNumInf W l mu - 1 ∈
      Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} := by
  have hrw : chordNumInf W l mu - 1 =
      -(infChartConst W l * AdjoinRoot.root (infChartCubic W)) -
        infChartConst W mu * infChartTElem W := by
    unfold chordNumInf; ring
  rw [hrw]
  exact Ideal.sub_mem _ (neg_mem (Ideal.mul_mem_left _ _ (root_mem_infSpan W)))
    (Ideal.mul_mem_left _ _ (tElem_mem_infSpan W))

theorem chordNn_sub_one_mem (W : WeierstrassCurve R) (l mu : R) :
    chordNn W l mu - 1 ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} :=
  mul_sub_one_mem (chordNumInf_sub_one_mem W l mu) (infChartW_sub_one_mem W)

theorem chordDd_sub_one_mem (W : WeierstrassCurve R) (x₀ : R) :
    chordDd W x₀ - 1 ∈ Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} := by
  have hrw : chordDd W x₀ - 1 = (infChartW W - 1) -
      (infChartConst W x₀ * AdjoinRoot.root (infChartCubic W)) *
        AdjoinRoot.root (infChartCubic W) := by
    unfold chordDd; ring
  rw [hrw]
  exact Ideal.sub_mem _ (infChartW_sub_one_mem W)
    (Ideal.mul_mem_left _ _ (root_mem_infSpan W))

omit [DecidableEq k] in
theorem germY_vertNumInf_mul (W : WeierstrassCurve k) (x₀ : k) :
    germY W (vertNumInf W x₀) * germY W (infChartW W) =
      germY W (AdjoinRoot.root (infChartCubic W)) * germY W (chordDd W x₀) := by
  rw [← map_mul, ← map_mul]
  exact congrArg (germY W) (denInf_mul_infChartW W x₀)

omit [DecidableEq k] in
theorem germY_tElem_mul_infChartW (W : WeierstrassCurve k) :
    germY W (infChartTElem W) * germY W (infChartW W) =
      germY W (AdjoinRoot.root (infChartCubic W)) ^ 3 := by
  rw [← map_mul, tel_mul_infChartW, map_pow]

/-- **The clause at infinity, chord shape.** -/
theorem hloc_off_chartZ_chordShape (W : WeierstrassCurve k) [W.IsElliptic]
    {x₁ y₁ x₂ y₂ x₃ y₃ l mu : k} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (h₃ : W.toAffine.Nonsingular x₃ y₃)
    (hadd : (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₂ y₂ h₂ =
      Point.some x₃ y₃ h₃)
    (num den : W.toAffine.CoordinateRing)
    (hnumdef : num = coordY W - (algebraMap k W.toAffine.CoordinateRing l * coordX W +
      algebraMap k W.toAffine.CoordinateRing mu))
    (hdendef : den = coordX W - algebraMap k W.toAffine.CoordinateRing x₃)
    (hden0 : den ≠ 0)
    (hnum1 : num ∈ XYIdeal W.toAffine x₁ (C y₁))
    (hnum2 : num ∈ XYIdeal W.toAffine x₂ (C y₂))
    (hden3 : den ∈ XYIdeal W.toAffine x₃ (C y₃))
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        chartZFunction W num den *
          @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} *
          ((Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal V *
            (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal V) =
        Ideal.span {num'} *
          ((Scheme.Hom.ker (pointSection W ((Point.some x₁ y₁ h₁ : W.toAffine.Point) +
              Point.some x₂ y₂ h₂))).ideal V *
            (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  -- the overlap factorisation of the cutter `v · Nn · Dd`
  have hcut : OverlapRel W (sectionUnitElem W * (chordNn W l mu * chordDd W x₃))
      ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((num * coordX W ^ 3) * (coordX W ^ 2 * den))) 7 := by
    have h := (overlapRel_sectionUnitElem W).mul
      ((overlapRel_chordNn W l mu).mul (overlapRel_chordDd W x₃))
    rw [hnumdef, hdendef]
    exact h
  have hIP : (Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal
      (infChartOpen W (chordNn W l mu * chordDd W x₃)) = ⊤ := by
    refine ker_ideal_pointSection_infChartOpen_eq_top W h₁ _ hcut ?_
    have hfac : (coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((num * coordX W ^ 3) * (coordX W ^ 2 * den)) =
        ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
          (coordX W ^ 3 * (coordX W ^ 2 * den))) * num := by ring
    rw [hfac]
    exact Ideal.mul_mem_left _ _ hnum1
  have hIQ : (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal
      (infChartOpen W (chordNn W l mu * chordDd W x₃)) = ⊤ := by
    refine ker_ideal_pointSection_infChartOpen_eq_top W h₂ _ hcut ?_
    have hfac : (coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((num * coordX W ^ 3) * (coordX W ^ 2 * den)) =
        ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
          (coordX W ^ 3 * (coordX W ^ 2 * den))) * num := by ring
    rw [hfac]
    exact Ideal.mul_mem_left _ _ hnum2
  have hIR : (Scheme.Hom.ker (pointSection W ((Point.some x₁ y₁ h₁ : W.toAffine.Point) +
      Point.some x₂ y₂ h₂))).ideal (infChartOpen W (chordNn W l mu * chordDd W x₃)) = ⊤ := by
    rw [hadd]
    refine ker_ideal_pointSection_infChartOpen_eq_top W h₃ _ hcut ?_
    have hfac : (coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((num * coordX W ^ 3) * (coordX W ^ 2 * den)) =
        ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
          ((num * coordX W ^ 3) * coordX W ^ 2)) * den := by ring
    rw [hfac]
    exact Ideal.mul_mem_left _ _ hden3
  -- the key identity in the function field
  have hnumI : germY W (chordNumInf W l mu) = germZ W num * germY W (infChartTElem W) := by
    have h := germY_eq_germZ_mul W (overlapRel_chordNumInf W l mu)
    rw [pow_one] at h
    rw [h, hnumdef]
  have hdenI : germY W (vertNumInf W x₃) = germZ W den * germY W (infChartTElem W) := by
    have h := germY_eq_germZ_mul W (overlapRel_vertNumInf W x₃)
    rw [pow_one] at h
    rw [h, hdendef]
  have hden0' : germZ W den ≠ 0 := germZ_ne_zero W hden0
  have hkey : chartZFunction W num den *
      germY W (AdjoinRoot.root (infChartCubic W)) ^ 1 * germY W (chordDd W x₃) =
      germY W (chordNn W l mu) := by
    calc chartZFunction W num den *
          germY W (AdjoinRoot.root (infChartCubic W)) ^ 1 * germY W (chordDd W x₃)
        = germZ W num * (germZ W den)⁻¹ *
            (germY W (AdjoinRoot.root (infChartCubic W)) * germY W (chordDd W x₃)) := by
          rw [chartZFunction_eq_germZ, pow_one]; ring
      _ = germZ W num * (germZ W den)⁻¹ *
            (germY W (vertNumInf W x₃) * germY W (infChartW W)) := by
          rw [germY_vertNumInf_mul W x₃]
      _ = germZ W num * (germZ W den)⁻¹ *
            (germZ W den * germY W (infChartTElem W) * germY W (infChartW W)) := by rw [hdenI]
      _ = germZ W num * (germY W (infChartTElem W) * germY W (infChartW W)) := by
          rw [show germZ W num * (germZ W den)⁻¹ *
              (germZ W den * germY W (infChartTElem W) * germY W (infChartW W)) =
            germZ W num * ((germZ W den)⁻¹ * germZ W den) *
              (germY W (infChartTElem W) * germY W (infChartW W)) from by ring,
            inv_mul_cancel₀ hden0', mul_one]
      _ = germY W (chordNumInf W l mu) * germY W (infChartW W) := by rw [hnumI]; ring
      _ = germY W (chordNn W l mu) := by rw [chordNn, map_mul]
  refine hloc_off_chartZ_aux W (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂)
    (chartZFunction W num den) 1 (chordNn W l mu) (chordDd W x₃)
    (chordNn_sub_one_mem W l mu) (chordDd_sub_one_mem W x₃) hkey hIP hIQ ?_ c hc
  rw [hIR, Ideal.top_mul, pow_one]

/-- **The clause at infinity, vertical shape.** -/
theorem hloc_off_chartZ_vertShape (W : WeierstrassCurve k) [W.IsElliptic]
    {x₁ y₁ x₂ y₂ : k} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hadd : (Point.some x₁ y₁ h₁ : W.toAffine.Point) + Point.some x₂ y₂ h₂ = 0)
    (num : W.toAffine.CoordinateRing)
    (hnumdef : num = coordX W - algebraMap k W.toAffine.CoordinateRing x₁)
    (hnum1 : num ∈ XYIdeal W.toAffine x₁ (C y₁))
    (hnum2 : num ∈ XYIdeal W.toAffine x₂ (C y₂))
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        chartZFunction W num 1 *
          @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} *
          ((Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal V *
            (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal V) =
        Ideal.span {num'} *
          ((Scheme.Hom.ker (pointSection W ((Point.some x₁ y₁ h₁ : W.toAffine.Point) +
              Point.some x₂ y₂ h₂))).ideal V *
            (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  have hcut : OverlapRel W (sectionUnitElem W * (chordDd W x₁ * 1))
      ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((coordX W ^ 2 * num) * 1)) 4 := by
    have h := (overlapRel_sectionUnitElem W).mul
      ((overlapRel_chordDd W x₁).mul (overlapRel_one' W))
    rw [hnumdef]
    exact h
  have hIP : (Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal
      (infChartOpen W (chordDd W x₁ * 1)) = ⊤ := by
    refine ker_ideal_pointSection_infChartOpen_eq_top W h₁ _ hcut ?_
    have hfac : (coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((coordX W ^ 2 * num) * 1) =
        ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
          coordX W ^ 2) * num := by ring
    rw [hfac]
    exact Ideal.mul_mem_left _ _ hnum1
  have hIQ : (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal
      (infChartOpen W (chordDd W x₁ * 1)) = ⊤ := by
    refine ker_ideal_pointSection_infChartOpen_eq_top W h₂ _ hcut ?_
    have hfac : (coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
        ((coordX W ^ 2 * num) * 1) =
        ((coordX W ^ 3 + algebraMap k W.toAffine.CoordinateRing W.a₂ * coordX W ^ 2) *
          coordX W ^ 2) * num := by ring
    rw [hfac]
    exact Ideal.mul_mem_left _ _ hnum2
  have hnumI : germY W (vertNumInf W x₁) = germZ W num * germY W (infChartTElem W) := by
    have h := germY_eq_germZ_mul W (overlapRel_vertNumInf W x₁)
    rw [pow_one] at h
    rw [h, hnumdef]
  have hgz : chartZFunction W num 1 = germZ W num := by
    rw [chartZFunction_eq_germZ, map_one, inv_one, mul_one]
  have hkey : chartZFunction W num 1 *
      germY W (AdjoinRoot.root (infChartCubic W)) ^ 2 * germY W 1 = germY W (chordDd W x₁) := by
    refine mul_left_cancel₀ (germY_root_ne_zero W) ?_
    calc germY W (AdjoinRoot.root (infChartCubic W)) *
          (chartZFunction W num 1 * germY W (AdjoinRoot.root (infChartCubic W)) ^ 2 * germY W 1)
        = germZ W num * (germY W (AdjoinRoot.root (infChartCubic W)) ^ 3) := by
          rw [hgz, map_one]; ring
      _ = germZ W num * (germY W (infChartTElem W) * germY W (infChartW W)) := by
          rw [germY_tElem_mul_infChartW W]
      _ = germY W (vertNumInf W x₁) * germY W (infChartW W) := by rw [hnumI]; ring
      _ = germY W (AdjoinRoot.root (infChartCubic W)) * germY W (chordDd W x₁) :=
          germY_vertNumInf_mul W x₁
  refine hloc_off_chartZ_aux W (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂)
    (chartZFunction W num 1) 2 (chordDd W x₁) 1
    (chordDd_sub_one_mem W x₁) (by rw [sub_self]; exact Ideal.zero_mem _) hkey hIP hIQ ?_ c hc
  rw [hadd, pointSection_zero', projModelZero_ker_ideal_infChartOpen W (chordDd W x₁ * 1),
    Ideal.span_singleton_mul_span_singleton, ← pow_two]

/-- The chord identity on the affine chart, in the `affineIdeal` packaging. -/
theorem affine_ideal_identity_chord (W : WeierstrassCurve.Affine k) {x₁ y₁ x₂ y₂ : k}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    Ideal.span {XClass W (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} *
        (affineIdeal W (Point.some x₁ y₁ h₁) * affineIdeal W (Point.some x₂ y₂ h₂)) =
      Ideal.span {YClass W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))} *
        (affineIdeal W ((Point.some x₁ y₁ h₁ : W.Point) + Point.some x₂ y₂ h₂) *
          affineIdeal W 0) := by
  have hadd : (Point.some x₁ y₁ h₁ : W.Point) + Point.some x₂ y₂ h₂ =
      Point.some _ _ (nonsingular_add h₁ h₂ hxy) := Point.add_some hxy
  rw [hadd, affineIdeal_zero, affineIdeal_some, affineIdeal_some, affineIdeal_some]
  exact chordIdealIdentity h₁.left h₂.left hxy

/-- The vertical identity on the affine chart, in the `affineIdeal` packaging. -/
theorem affine_ideal_identity_vertical (W : WeierstrassCurve.Affine k) {x₁ y₁ x₂ y₂ : k}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) :
    Ideal.span {(1 : W.CoordinateRing)} *
        (affineIdeal W (Point.some x₁ y₁ h₁) * affineIdeal W (Point.some x₂ y₂ h₂)) =
      Ideal.span {XClass W x₁} *
        (affineIdeal W ((Point.some x₁ y₁ h₁ : W.Point) + Point.some x₂ y₂ h₂) *
          affineIdeal W 0) := by
  have hadd : (Point.some x₁ y₁ h₁ : W.Point) + Point.some x₂ y₂ h₂ = 0 :=
    Point.add_of_Y_eq hxy.1 hxy.2
  rw [hadd, affineIdeal_zero, affineIdeal_some, affineIdeal_some,
    Ideal.span_singleton_one, Ideal.top_mul, Ideal.mul_top, Ideal.mul_top, hxy.1, hxy.2]
  exact XYIdeal_neg_mul h₂

/-- **(1b, chord)** The clause at infinity for the chord. -/
theorem hloc_off_chartZ_chord (W : WeierstrassCurve k) [W.IsElliptic] {x₁ y₁ x₂ y₂ : k}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        chartZFunction W
            (YClass W.toAffine (linePolynomial x₁ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)))
            (XClass W.toAffine (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))) *
          @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} *
          ((Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal V *
            (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal V) =
        Ideal.span {num'} *
          ((Scheme.Hom.ker (pointSection W ((Point.some x₁ y₁ h₁ : W.toAffine.Point) +
              Point.some x₂ y₂ h₂))).ideal V *
            (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  refine hloc_off_chartZ_chordShape W h₁ h₂ (nonsingular_add h₁ h₂ hxy) (Point.add_some hxy)
    _ _ (l := W.toAffine.slope x₁ x₂ y₁ y₂)
    (mu := y₁ - W.toAffine.slope x₁ x₂ y₁ y₂ * x₁) ?_ ?_ (XClass_ne_zero _) ?_ ?_ ?_ c hc
  · rw [YClass_eq_coordY_sub_of, of_linePolynomial, map_sub, map_mul]
    ring
  · exact XClass_eq_coordX_sub W _
  · rw [XYIdeal_eq₁ x₁ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · rw [XYIdeal_eq₂ h₁.left h₂.left hxy]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · exact Ideal.subset_span (Set.mem_insert _ _)

/-- **(1b, vertical)** The clause at infinity for the vertical. -/
theorem hloc_off_chartZ_vertical (W : WeierstrassCurve k) [W.IsElliptic] {x₁ y₁ x₂ y₂ : k}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        chartZFunction W (XClass W.toAffine x₁) 1 *
          @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} *
          ((Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal V *
            (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal V) =
        Ideal.span {num'} *
          ((Scheme.Hom.ker (pointSection W ((Point.some x₁ y₁ h₁ : W.toAffine.Point) +
              Point.some x₂ y₂ h₂))).ideal V *
            (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  refine hloc_off_chartZ_vertShape W h₁ h₂ (Point.add_of_Y_eq hxy.1 hxy.2) _ ?_ ?_ ?_ c hc
  · exact XClass_eq_coordX_sub W x₁
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · rw [hxy.1]
    exact Ideal.subset_span (Set.mem_insert _ _)

/-- **(1b, PROVED) The clause at infinity.**
`hloc_chartZ` handles every point of the affine `Z`-chart; this handles the one remaining point
`[0 : 1 : 0]`, for a pair of affine points `P`, `Q`.

Unlike `hloc_chartZ` this needs the *shape* of `num`, `den` and not merely the affine ideal
identity they satisfy: the construction at infinity reads `num` and `den` off the chart overlap, so
it has to know that they are the chord `ℓ` over the vertical `x − x₃`, or (when `Q = −P`) the
vertical `x − x₁` over `1`. The hypothesis `hshape` records exactly the disjunction produced by the
case split of `exists_affine_ideal_identity`, and `exists_squareChartData_projModel` supplies it by
performing that same case split at the call site. -/
theorem hloc_off_chartZ (W : WeierstrassCurve k) [W.IsElliptic] {x₁ y₁ x₂ y₂ : k}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (num den : W.toAffine.CoordinateRing)
    (hshape : (¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) ∧
        num = YClass W.toAffine (linePolynomial x₁ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) ∧
        den = XClass W.toAffine (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))) ∨
      ((x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) ∧ num = XClass W.toAffine x₁ ∧ den = 1))
    (c : ↥(projModel W)) (hc : c ∉ (projModelZChart W).1) :
    ∃ (V : (projModel W).affineOpens) (hcv : c ∈ V.1) (num' den' : Γ(projModel W, V.1)),
      den' ∈ nonZeroDivisors Γ(projModel W, V.1) ∧
      @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ num' =
        chartZFunction W num den *
          @Scheme.germToFunctionField (projModel W) _ V.1 ⟨⟨c, hcv⟩⟩ den' ∧
      Ideal.span {den'} *
          ((Scheme.Hom.ker (pointSection W (Point.some x₁ y₁ h₁))).ideal V *
            (Scheme.Hom.ker (pointSection W (Point.some x₂ y₂ h₂))).ideal V) =
        Ideal.span {num'} *
          ((Scheme.Hom.ker (pointSection W ((Point.some x₁ y₁ h₁ : W.toAffine.Point) +
              Point.some x₂ y₂ h₂))).ideal V *
            (Scheme.Hom.ker (projModelZero W)).ideal V) := by
  rcases hshape with ⟨hxy, rfl, rfl⟩ | ⟨hxy, rfl, rfl⟩
  · exact hloc_off_chartZ_chord W h₁ h₂ hxy c hc
  · exact hloc_off_chartZ_vertical W h₁ h₂ hxy c hc

end InfinityCases

end InfinityChart

open WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing in
/-- **THE LEAF (T10-asm-chart): read the local numerator and denominator of the
theorem-of-the-square function off the Weierstrass charts.**

Produce an affine cover of `projModel W` by nonempty charts, together with nonzerodivisor
generators of the four section ideal sheaves on each chart whose ratios
`(genP · genQ) / (genR · genO)` are one and the same rational function — the input of
`squareChartDataOfRatio`, whose output this file's composition turns into the theorem of the
square. This *is* the theorem of the square on the projective model, in local form.

**Status: proved.** The proof below is the complete assembly. The case split of
`exists_affine_ideal_identity` (1c) is performed here rather than inside it, because the chart at
infinity needs the *shape* of `num`, `den` and not only the ideal identity:

* `P = 0` and `Q = 0` are the degenerate cases `nonempty_squareChartData_projModel_zero_left` /
  `_zero_right` (both sides carry the same pair of divisors, ratio `1`);
* for two affine points the identity on the affine chart is `affine_ideal_identity_vertical`
  (`num = x − x₁`, `den = 1`) or `affine_ideal_identity_chord` (`num = ℓ`, `den = x − x₃`), and
  `chartZFunction W num den` is the resulting rational function — the classical
  chord-over-vertical;
* `hloc_chartZ` (1a) supplies the local Cartier data at every point of the affine `Z`-chart,
  through the dictionary `ker_ideal_pointSection_chartZ'` (mathlib's `XYIdeal`, transported along
  `chartZSectionsRingEquiv`);
* `hloc_off_chartZ_vertical` / `hloc_off_chartZ_chord` (1b) supply it at the one point off the
  `Z`-chart, `[0 : 1 : 0]`; see the section "The chart at infinity" above.

**Why the available divisor input does not help.**
`exists_functionField_projectiveDivisorOf_kappa` above delivers a nonzero `F` with
`projectiveDivisorOf F = (P+Q) + (0) − (P) − (Q)`, but HasseWeil's `projectiveDivisorOf`
records orders only at `k`-**rational** affine points (`SmoothPlaneCurve.SmoothPoint` is a
pair of elements of `k`) together with the place at infinity. Over a non-algebraically-closed
`k` that pins `F` only up to a factor whose divisor is supported on closed points of degree
`> 1`, and such factors exist: if `S`, `U` are quadratic points of `E` with the same trace
`S + S̄ = U + Ū = T ≠ 0`, then `(S)+(S̄) − (U)−(Ū)` is principal and invisible to
`projectiveDivisorOf`. So `F` may have extra zeros and poles, which the ideal-sheaf identity
does not tolerate; feeding `F` straight into `squareChartDataOfRatio` is *not* sound.
(The classical witness `f = v / ℓ`, vertical over chord, does have divisor exactly
`(P+Q) + (0) − (P) − (Q)` at every closed point — the statement is true, it is the *input*
that is too weak.) That is why this leaf is stated *without* the divisor witness as a hypothesis,
and why the route above is the explicit chord-and-vertical one. -/
theorem exists_squareChartData_projModel (W : WeierstrassCurve k) [W.IsElliptic]
    (P Q : W.toAffine.Point) :
    Nonempty (SquareChartData (Scheme.Hom.ker (pointSection W P))
      (Scheme.Hom.ker (pointSection W Q)) (Scheme.Hom.ker (pointSection W (P + Q)))
      (Scheme.Hom.ker (projModelZero W))) := by
  match P, Q with
  | 0, Q => exact nonempty_squareChartData_projModel_zero_left W Q
  | .some x y h, 0 => exact nonempty_squareChartData_projModel_zero_right W _
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · refine nonempty_squareChartData_projModel_of_local W _ _
        (chartZFunction W (XClass W.toAffine x₁) 1) fun c => ?_
      by_cases hc : c ∈ (projModelZChart W).1
      · exact hloc_chartZ W _ _ _ 1 one_ne_zero
          (affine_ideal_identity_vertical W.toAffine h₁ h₂ hxy) c hc
      · exact hloc_off_chartZ_vertical W h₁ h₂ hxy c hc
    · refine nonempty_squareChartData_projModel_of_local W _ _
        (chartZFunction W
          (YClass W.toAffine (linePolynomial x₁ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)))
          (XClass W.toAffine (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))))
        fun c => ?_
      by_cases hc : c ∈ (projModelZChart W).1
      · exact hloc_chartZ W _ _ _ _ (XClass_ne_zero _)
          (affine_ideal_identity_chord W.toAffine h₁ h₂ hxy) c hc
      · exact hloc_off_chartZ_chord W h₁ h₂ hxy c hc

/-- **(T10-asm) The theorem of the square as a module triviality over a field.**

For an elliptic Weierstrass curve `W` over a field `k` and points `P`, `Q`, the ideal modules of
the sections of the projective model attached to `P`, `Q`, `P + Q` and `0` satisfy

  `I(P) ⊗_{𝒪} I(Q) ≅ I(P+Q) ⊗_{𝒪} I(0)`.

No hypothesis beyond `W.IsElliptic` is needed: the composition
(`nonempty_tensorObj_idealModule_iso_of_squareChartData`) is unconditional, and the local input
`exists_squareChartData_projModel` is stated on the bare curve. In particular
`IsIntegrallyClosed` is *not* assumed here — it is a hypothesis only of the weaker divisor-form
input `exists_functionField_projectiveDivisorOf_kappa`. -/
theorem nonempty_tensorObj_idealModule_add_field (W : WeierstrassCurve k) [W.IsElliptic]
    (P Q : W.toAffine.Point) :
    Nonempty (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker (pointSection W P)))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (pointSection W Q))) ≅
        tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker (pointSection W (P + Q))))
          (Scheme.Modules.idealModule (Scheme.Hom.ker (projModelZero W)))) :=
  nonempty_tensorObj_idealModule_iso_of_squareChartData
    (exists_squareChartData_projModel W P Q).some

end ModularCurves
