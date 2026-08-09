/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModuleMul
import ModularCurves.EllipticCurve.MulByHomDegree
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

## Status

`exists_squareChartData_projModel` — the local reading of the theorem-of-the-square function on
the Weierstrass charts — is the one remaining leaf; see its docstring for exactly what is
missing and why the divisor input available today does not suffice. Proved here:

* the whole composition, on an arbitrary scheme
  (`nonempty_tensorObj_idealModule_iso_of_squareChartData`);
* the reduction of the cocycle to one equation in the function field
  (`cocycle_of_germToFunctionField_ratio`, `squareChartDataOfRatio`);
* the common-refinement step (`exists_affineOpen_span_nzd_four`) and the local principality of
  every section ideal sheaf of the model (`exists_affineOpen_ker_pointSection_span_nzd`);
* the degenerate cases `P = 0` and `Q = 0` of the leaf itself
  (`nonempty_squareChartData_projModel_zero_left` / `_zero_right`);
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

/-- **THE REMAINING LEAF (T10-asm-chart): read the local numerator and denominator of the
theorem-of-the-square function off the Weierstrass charts.**

Produce an affine cover of `projModel W` by nonempty charts, together with nonzerodivisor
generators of the four section ideal sheaves on each chart whose ratios
`(genP · genQ) / (genR · genO)` are one and the same rational function — the input of
`squareChartDataOfRatio`, whose output this file's composition turns into the theorem of the
square. This *is* the theorem of the square on the projective model, in local form.

Two things are missing, and neither is repackaging:

1. **The ideal-sheaf dictionary.** Nothing in the tree computes an *explicit* generator of
   `Scheme.Hom.ker (pointSection W P)` for a general point `P`. Only the zero section is done,
   on its two charts, by `projModelZero_ker_ideal_chartZ` /
   `projModelZero_ker_ideal_sectionNeighborhood` / `projModelSectionRoot_mem_nonZeroDivisors`
   (`EllipticCurve/PoleSheafModel.lean`). The points dictionary `projModelPointsEquiv` is a
   bijection of *points*, not of ideals, so it does not identify
   `Scheme.Hom.ker (pointSection W P)` with mathlib's `XYIdeal x y` on the affine chart.
   `exists_affineOpen_ker_pointSection_span_nzd` (above) does give a *pointwise* principal
   chart for each of the four ideals, and `exists_affineOpen_span_nzd_four` refines the four
   onto one common chart — but generators produced that way are only unique up to a unit on
   each chart, and those units do not cancel in the cocycle. So the cover and the four
   generators have to be produced *together with* the rational function, not before it. (When
   the ratio is `1` no choice is needed, which is why `nonempty_squareChartData_diagonal`
   already settles the degenerate cases `P = 0` and `Q = 0`.)

2. **The available divisor input is strictly weaker than what is needed.**
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
   that is too weak.) Closing this leaf therefore needs either the explicit chord-and-vertical
   function read on the two Weierstrass charts, or a strengthening of
   `HasseWeil.Curves.MillerHypothesis` from rational points to all closed points.

For that reason this leaf is deliberately stated *without* the divisor witness as a hypothesis:
taking the weak witness as an input would make the statement false. -/
theorem exists_squareChartData_projModel (W : WeierstrassCurve k) [W.IsElliptic]
    (P Q : W.toAffine.Point) :
    Nonempty (SquareChartData (Scheme.Hom.ker (pointSection W P))
      (Scheme.Hom.ker (pointSection W Q)) (Scheme.Hom.ker (pointSection W (P + Q)))
      (Scheme.Hom.ker (projModelZero W))) := by
  sorry

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
    Nonempty (tensorObj (idealModule (Scheme.Hom.ker (pointSection W P)))
          (idealModule (Scheme.Hom.ker (pointSection W Q))) ≅
        tensorObj (idealModule (Scheme.Hom.ker (pointSection W (P + Q))))
          (idealModule (Scheme.Hom.ker (projModelZero W)))) :=
  nonempty_tensorObj_idealModule_iso_of_squareChartData
    (exists_squareChartData_projModel W P Q).some

end ModularCurves
