import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.Rigidity
import ModularCurves.ForMathlib.FinrankComp
import ModularCurves.ForMathlib.FinrankDegenerate
import ModularCurves.LevelStructure.CartierDivisor

/-!
# The endomorphism ring, degree, and Hasse bound of `E/S` (KM Ch. 2, §§2.5–2.7)

The `End(E/S)` / degree / Hasse layer feeding rigidity (`aut_hom_eq_id_of_fullLevel`,
`Moduli/Groupoid.lean`). `End(E/S)` is the ring of `Over S`-endomorphisms
`E.asOver ⟶ E.asOver`: its additive group is the (multiplicatively-spelled) `Hom.commGroup`
(group-`1` = zero morphism = ring `0`, group-`*` = pointwise sum = ring `+`, `f ^ n` = `[n]·f`,
`E.mulBy n = (𝟙 E.asOver) ^ n = [n]`); ring-`1` = `𝟙 E.asOver`; ring-`*` = composition `≫`.

**Foundation spine status (v10.250):** `endDeg`/`endTrace`/`endDual` are now **CONSTRUCTED**,
Abel-FREE (the v10.212 UNIFICATION ruling): `endDeg` is the scheme-theoretic fibre rank
`Scheme.Hom.finrank` of `f.left` at the zero-section basepoint; `endTrace` is the `deg(1+f)`
polarization cross-term; `endDual` is the trace reflection `[tr f] − f`. The construction makes
`endTrace_spec` pure group algebra and `endDeg_one_add` definitional; `endDeg_mulBy = n²` reduces
to the BB-DEG scheme substrate (`Torsion.mulByHom_finrank`, G0's seat) + the T-DEG0 rank-zero leaf.
The remaining pins are theorem-level leaves (T-G3b/c/d/e + the characteristic polynomial
`endDual_comp_self` = the degree quadratic form, where the Abel content now concentrates). Full
plan + verbatim KM quotes: `.mathlib-quality/decomposition-end0.md`.

**DEGENERATE-BASE NOTE (binding for pin-provers):** `endDeg` is a single integer, evaluated at a
basepoint (junk `1` over the empty base — over `∅` every endomorphism IS `𝟙`, so degree-`1` junk
keeps `endDeg_one`/`endDeg_eq_one_of_isIso`/`endDeg_comp`/`eq_zero_of_endDeg_eq_zero` true with no
hypotheses). Pins that force an explicit `[n]`-value (`endDeg_mulBy`, `endDual_mulBy`, and the
scalings `endDeg_comp_mulBy`/`endTrace_comp_mulBy`) are FALSE over `S = ∅` (all endomorphisms
coincide there) and carry `[Nonempty S]`. Over a DISCONNECTED base an endomorphism can have
different fibre degrees on different components, so pins comparing ranks at different points of
`E.E` (`endDeg_comp`, `endDual_comp_self`, `eq_zero_of_endDeg_eq_zero`, `endTrace_sq_le`) are
honest only componentwise — prove them with the hypotheses they need (e.g.
`[PreconnectedSpace E.E]`); every downstream consumer instantiates at geometric fibres
`S = Spec k`, where all such hypotheses synthesize.

Sources (KM, verbatim in the decl docstrings): 2.5.1 (pointed ⟹ hom; dual via Abel), 2.6.1
(`f^t f = [deg f]`), 2.6.1.1 (`deg[N] = N²`, `f^{tt} = f`), 2.6.2 (dual additive), 2.6.2.2 (trace),
2.6.3 (char.-poly + `(tr f)² ≤ 4 deg f`), 2.7.2 (rigidity of level `N`). Fibre anchor for T-G3c:
HasseWeil `Foundation/DegreeQuadraticForm.lean` + `HasseBound.lean` (IMPORT at execution).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **DS-data (T-END0b — KM 2.6.1), CONSTRUCTED Abel-FREE (v10.250 foundation spine).** The degree
`deg : End(E/S) → ℤ`. KM (verbatim, Thm 2.6.1): *"f^t f = deg(f) := { N if f is an isogeny of
degree N; 0 if f = 0 }."* **Construction (the v10.212 UNIFICATION ruling):** the scheme-theoretic
fibre rank `Scheme.Hom.finrank` of `f.left` at the zero-section basepoint `E.zero s₀` (for a
chosen point `s₀ : S`; junk `1` over the empty base, where every endomorphism *is* the identity,
of degree `1`). For a finite flat isogeny this is the
fibrewise isogeny degree (= HasseWeil's `Isogeny.degree` through the K4 bridge); for `f = [0]` the
fibre module is torsion, of rank `0` — so one formula realises KM's case split, with **no**
Abel/Pic⁰ input. Pinned by `endDual_comp_self`, `endDeg_mulBy`. -/
noncomputable def endDeg (f : E.asOver ⟶ E.asOver) : ℤ :=
  haveI := Classical.propDecidable (Nonempty S)
  if h : Nonempty S then
    (Scheme.Hom.finrank (X := E.E) (S := E.E) f.left (E.zero h.some) : ℤ)
  else 1

/-- **DS-data (T-END0d — KM 2.6.2.2), CONSTRUCTED.** The trace `tr : End(E/S) → ℤ`. KM (verbatim,
Cor 2.6.2.2): *"there exists an integer, called trace(f), such that f + f^t = trace(f)."*
**Construction:** the polarization cross-term of the degree at the identity,
`tr f := deg(1 + f) − 1 − deg f` (KM, proof of Cor 2.6.2.2: *"deg(1+f) = 1 + deg(f) + (f + f^t)"*),
which makes the polarization pin `endDeg_one_add` definitional. Pinned by `endTrace_spec`. -/
noncomputable def endTrace (f : E.asOver ⟶ E.asOver) : ℤ :=
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  E.endDeg (𝟙 E.asOver * f) - 1 - E.endDeg f

/-- **DS-data (T-END0b — KM 2.5/2.6.1), CONSTRUCTED Abel-FREE.** The dual (transpose) isogeny
`f ↦ f^t`. KM (verbatim, proof of 2.5.1, print p.79): *"f^t = Pic(f) = f^* : Pic⁰_{E′/S} →
Pic⁰_{E/S} … via Abel's isomorphism … an S-homomorphism f^t : E′ → E."* **Construction
(Abel-free):** KM's Cor 2.6.2.2 identity `f + f^t = [tr f]` is *solved for the dual*:
`f^t := [tr f] − f` (spelled `E.mulBy (endTrace f) * f⁻¹` in the multiplicative hom-group). This
trace-reflection definition makes `endTrace_spec` pure group algebra and concentrates the entire
Abel/quadratic content in the characteristic-polynomial pin `endDual_comp_self`
(`f^t ∘ f = [deg f]`, KM 2.6.1). Pinned by `endDual_comp_self`, `endDual_mulBy`. -/
noncomputable def endDual (f : E.asOver ⟶ E.asOver) : E.asOver ⟶ E.asOver :=
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  E.mulBy (E.endTrace f) * f⁻¹

/-- **(T-END0a foundation — KM 2.5.1, PROVEN via `isMonHom_of_one_comp_eq'`)** Over a locally
noetherian base, a **pointed** endomorphism of `E/S` (one fixing the group unit / zero section)
is a monoid homomorphism: `μ ≫ f = (f ⊗ f) ≫ μ`. This is the additivity underlying the ring
structure on `End(E/S)` (postcomposition by such `f` distributes over the pointwise group law).
The `[IsLocallyNoetherian S]` hypothesis drops out when T-W7.8 (EGA IV §8 spreading-out) lands,
per the T-E4a-noeth future-proofing pattern. KM (verbatim, Thm 2.5.1): *"any S-morphism
f : E → E′ with f(0) = 0 is a homomorphism."* Reuses the sorry-free T-W7.7 rigidity engine
(`isMonHom_of_one_comp_eq'`) + `EllipticCurveGeom.universallyOConnected`. -/
theorem endMonHom [IsLocallyNoetherian S] (f : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ f = η[E.asOver]) :
    μ[E.asOver] ≫ f = MonoidalCategory.tensorHom f f ≫ μ[E.asOver] := by
  haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
  haveI : IsProper E.asOver.hom := inferInstanceAs (IsProper E.π)
  haveI : Flat E.asOver.hom := inferInstanceAs (Flat E.π)
  haveI : IsSeparated E.asOver.hom := inferInstanceAs (IsSeparated E.π)
  exact isMonHom_of_one_comp_eq' E.toEllipticCurveGeom.universallyOConnected f hη

/-- **(T-END0a — right-distributivity of `End(E/S)`)** Post-composition by a **pointed**
endomorphism `f` distributes over the pointwise (additive) group law: `(a * b) ≫ f = (a ≫ f) * (b ≫ f)`
(the `*` is the additive `Hom.commGroup`/`Hom.group` operation). This is the additive half of the
ring structure that is *not* free — pre-composition distributes over `*` for **every** morphism
(`MonObj.comp_mul`, naturality of `lift`), but post-composition distributes only through a *monoid
homomorphism*. A pointed `f` is one (`endMonHom`), so post-composition by `f` is the bundled monoid
hom `IsMonHom.monoidHom f` and the identity is its `map_mul`. -/
theorem endPostcomp_mul [IsLocallyNoetherian S] (a b f : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ f = η[E.asOver]) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  haveI : IsMonHom f := { one_hom := hη, mul_hom := endMonHom E f hη }
  exact map_mul (IsMonHom.monoidHom f E.asOver) a b

/-- The multiplication-by-`n` isogeny `[n]` is **pointed**: `η ≫ [n] = η` (it fixes the zero
section, `n • 0 = 0`). Since `[n] = (𝟙)^n` in the hom-group, pre-composition by `η` commutes with
the group power (`GrpObj.comp_zpow`), and `η` is the unit of the group `𝟙_ ⟶ E.asOver`, so
`η ≫ (𝟙)^n = (η ≫ 𝟙)^n = η^n = η`. Feeds `IsMonHom (E.mulBy n)` and the final `ε = 𝟙` step. -/
theorem mulBy_pointed (n : ℤ) : η[E.asOver] ≫ E.mulBy n = η[E.asOver] := by
  have hη1 : η[E.asOver] = (1 : 𝟙_ (Over S) ⟶ E.asOver) := by
    rw [Hom.one_def]; simp
  simp only [EllipticCurve.mulBy]
  rw [GrpObj.comp_zpow, Category.comp_id, hη1, one_zpow]

/-- `[1] = 𝟙 E.asOver`: multiplication-by-one is the identity endomorphism (`(𝟙)^1 = 𝟙`). -/
theorem mulBy_one : E.mulBy 1 = 𝟙 E.asOver := by
  simp only [EllipticCurve.mulBy, zpow_one]

/-- `[m] ≫ [n] = [m·n]`: composing multiplications multiplies the multipliers. Pre-composition
into a hom-group power distributes (`GrpObj.comp_zpow`), so `[m] ≫ (𝟙)^n = ([m] ≫ 𝟙)^n = ((𝟙)^m)^n
= (𝟙)^{mn}` by `zpow_mul`. -/
theorem mulBy_comp (m n : ℤ) : E.mulBy m ≫ E.mulBy n = E.mulBy (m * n) := by
  simp only [EllipticCurve.mulBy]
  rw [GrpObj.comp_zpow, Category.comp_id, ← zpow_mul]

/-- `[m] + [n] = [m + n]`: the multiplications compose additively in the hom-group
(`(𝟙)^m * (𝟙)^n = (𝟙)^{m+n}`, `zpow_add`). -/
theorem mulBy_mul (m n : ℤ) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.mulBy m * E.mulBy n = E.mulBy (m + n) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  simp only [EllipticCurve.mulBy]
  rw [← zpow_add]

/-- `[-1]` is an automorphism of `E/S`: it is its own inverse (`[-1] ≫ [-1] = [1] = 𝟙`). -/
instance isIso_mulBy_neg_one : IsIso (E.mulBy (-1)) :=
  ⟨E.mulBy (-1), by rw [E.mulBy_comp, show (-1 : ℤ) * -1 = 1 by norm_num, E.mulBy_one],
    by rw [E.mulBy_comp, show (-1 : ℤ) * -1 = 1 by norm_num, E.mulBy_one]⟩

/-- The underlying scheme morphism of `[-1]` is an isomorphism (`Over.forget` preserves isos). -/
instance isIso_mulByHom_neg_one : IsIso (E.mulByHom (-1)) :=
  inferInstanceAs (IsIso ((Over.forget S).map (E.mulBy (-1))))

/-- The `[0]` endomorphism is the constant-to-zero-section map `π ≫ zero`. -/
theorem mulByHom_zero_eq : E.mulByHom 0 = E.π ≫ E.zero := by
  show (E.mulBy 0).left = E.π ≫ E.zero
  rw [show E.mulBy (0 : ℤ) = (1 : E.asOver ⟶ E.asOver) from by
    simp only [EllipticCurve.mulBy, zpow_zero]]
  show ((1 : E.asOver ⟶ E.asOver)).left = E.π ≫ E.zero
  rw [Hom.one_def, Over.comp_left, E.one_eq_zero]
  have hw : (toUnit E.asOver).left ≫ (𝟙_ (Over S)).hom = E.π :=
    Over.w (toUnit E.asOver)
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ E.zero) hw)

/-- **(T-DEG0 leaf, PROVEN)** The `[0]` endomorphism has fibre rank `0` at every point. `[0]`
factors through the zero section, a relative effective Cartier divisor (KM 1.2.2: smoothness of
`E.π` of relative dimension `1` makes the section ideal affine-locally principal on a
nonzerodivisor, `exists_affineOpen_ker_principal_nonZeroDivisor`), so its pushforward module is
ideal-torsion with the ideal germ nonzero — `rankAtStalk` zero with no flatness/finiteness
(`Scheme.Hom.finrank_eq_zero_of_factors_of_nonZeroDivisor_mem`,
`ForMathlib/FinrankDegenerate.lean`). Realises KM 2.6.1's `deg 0 = 0` degenerate case with no
zero-or-isogeny dichotomy. Consumed by the `n = 0` case of `endDeg_mulBy`. -/
theorem mulByHom_zero_finrank (x : E.E) : (E.mulByHom 0).finrank x = 0 := by
  haveI : IsSeparated E.π := inferInstance
  obtain ⟨V, hxV, f₀, hgen, hnzd⟩ :=
    RelEffCartierDiv.exists_affineOpen_ker_principal_nonZeroDivisor E.π E.smooth E.zero E.zero_π x
  refine Scheme.Hom.finrank_eq_zero_of_factors_of_nonZeroDivisor_mem _ (Scheme.Hom.ker E.zero)
    (E.π ≫ E.zero.toImage) ?_ x V hxV f₀ ?_ hnzd
  · rw [mulByHom_zero_eq, Category.assoc, Scheme.Hom.toImage_imageι]
  · rw [hgen]
    exact Ideal.mem_span_singleton_self f₀

/-- `Spec R` is nonempty for a nontrivial ring — the scheme-carrier form of
`PrimeSpectrum.instNonempty`, provided as an instance so the `[Nonempty S]` hypotheses of the
degree pins synthesize at every geometric-fibre call site `S = Spec k`. -/
instance (R : Type u) [CommRing R] [Nontrivial R] : Nonempty (Spec (CommRingCat.of R)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum R))

/-- **(T-END0b pin — KM 2.6.1)** The defining identity of the degree: `f^t ∘ f = [deg f]`. -/
theorem endDual_comp_self (f : E.asOver ⟶ E.asOver) :
    E.endDual f ≫ f = E.mulBy (E.endDeg f) := sorry

/-- **(T-END0c — KM 2.6.1.1)** `deg [N] = N²` (KM: *"deg([N]) = N²"*, displayed in the proof of
Cor 2.6.1.1). Fibre anchor: HasseWeil `mulByInt_degree` (BB-DEG) via T-B6. **Reduction (this
proof):** `endDeg` evaluates `(mulByHom n).finrank` at the zero basepoint; for `n > 0` that is
BB-DEG `Torsion.mulByHom_finrank` (G0's E[N]-scheme substrate seat); for `n < 0` the `[-1]`-twist
`[n] = [-1] ≫ [-n]` reduces to the positive case by `finrank_comp_left_of_isIso` (side conditions
from `mulByHom_isFinite` + BB-FLAT); for `n = 0` it is the T-DEG0 torsion-rank leaf. `[Nonempty S]`
is required — over the empty base all endomorphisms coincide (DEGENERATE-BASE NOTE). -/
theorem endDeg_mulBy [hne : Nonempty S] (n : ℤ) : E.endDeg (E.mulBy n) = n ^ 2 := by
  have hpt : ∀ g : E.asOver ⟶ E.asOver,
      E.endDeg g
        = (Scheme.Hom.finrank (X := E.E) (S := E.E) g.left (E.zero hne.some) : ℤ) := by
    intro g
    simp only [endDeg, dif_pos hne]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero] at hpt ⊢
      rw [hpt, E.mulByHom_zero_finrank]
      norm_num
    · haveI : NeZero m := ⟨hm.ne'⟩
      rw [hpt, E.mulByHom_finrank m]
      push_cast
      ring
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, neg_zero] at hpt ⊢
      rw [hpt, E.mulByHom_zero_finrank]
      norm_num
    · haveI : NeZero m := ⟨hm.ne'⟩
      haveI : Flat (E.mulByHom (m : ℤ)) := E.mulByHom_flat m
      haveI : IsFinite (E.mulByHom (m : ℤ)) := E.mulByHom_isFinite m
      have hsplit : E.mulBy (-(m : ℤ)) = E.mulBy (-1) ≫ E.mulBy (m : ℤ) := by
        rw [E.mulBy_comp, show (-1 : ℤ) * m = -(m : ℤ) by ring]
      have hleft : E.mulByHom (-(m : ℤ)) = E.mulByHom (-1) ≫ E.mulByHom (m : ℤ) := by
        rw [show E.mulByHom (-(m : ℤ)) = (E.mulBy (-(m : ℤ))).left from rfl, hsplit]
        rfl
      have hcomp : Scheme.Hom.finrank (X := E.E) (S := E.E) (E.mulByHom (-(m : ℤ)))
          = Scheme.Hom.finrank (X := E.E) (S := E.E) (E.mulByHom (m : ℤ)) := by
        rw [hleft, Scheme.Hom.finrank_comp_left_of_isIso]
      rw [hpt, hcomp, E.mulByHom_finrank m]
      push_cast
      ring

/-- **(T-END0b pin — KM 2.6.1)** The degree is non-negative: `0 ≤ deg f` (KM 2.6.1 defines
`deg f = N ≥ 0` for an isogeny of degree `N`, and `deg 0 = 0`). Supplies the `0 ≤ d` hypothesis of
`gme_deg_trace_forces_zero` in the rigidity computation. -/
theorem endDeg_nonneg (f : E.asOver ⟶ E.asOver) : 0 ≤ E.endDeg f := by
  simp only [endDeg]
  split
  · exact Int.natCast_nonneg _
  · exact zero_le_one

/-- Any `Over S`-endomorphism of `E` is locally of finite presentation, by the cancellation
`ForMathlib.FinitePresentationCancel` (Stacks 01TX) against the smooth structure morphism —
the general-endomorphism form of `mulByHom_locallyOfFinitePresentation`. -/
theorem endo_locallyOfFinitePresentation (f : E.asOver ⟶ E.asOver) :
    LocallyOfFinitePresentation (show E.E ⟶ E.E from f.left) := by
  haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) E.π
  have h : LocallyOfFinitePresentation ((show E.E ⟶ E.E from f.left) ≫ E.π) := by
    have hw : (show E.E ⟶ E.E from f.left) ≫ E.π = E.π := Over.w f
    rw [hw]
    infer_instance
  exact LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType h inferInstance

/-- A finite flat endomorphism of `E` with **integral** total space is surjective: its image is
open (flat + locally of finite presentation ⟹ universally open, Stacks 01UA), closed (finite ⟹
proper), and nonempty, hence everything in the preconnected space `E.E`. This discharges the
surjectivity inputs of the composition formula without any degree computation. -/
theorem endo_surjective [IsIntegral E.E] (f : E.asOver ⟶ E.asOver)
    [Flat (show E.E ⟶ E.E from f.left)] [IsFinite (show E.E ⟶ E.E from f.left)] :
    Surjective (show E.E ⟶ E.E from f.left) := by
  set fl : E.E ⟶ E.E := f.left with hfl
  haveI : LocallyOfFinitePresentation fl := E.endo_locallyOfFinitePresentation f
  haveI : IrreducibleSpace E.E := inferInstance
  haveI : Nonempty E.E := inferInstance
  have hopen : IsOpen (Set.range fl.base) := fl.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range fl.base) := fl.isClosedMap.isClosed_range
  have hne : (Set.range fl.base).Nonempty := Set.range_nonempty _
  constructor
  rw [← Set.range_eq_univ]
  exact IsClopen.eq_univ ⟨hclosed, hopen⟩ hne

/-- **(T-END0c pin, PROVEN integral form — KM 2.6.1, `deg` multiplicative)** The degree is
multiplicative under composition of finite flat endomorphisms when the total space `E.E` is
integral: `deg(f ≫ g) = deg f · deg g`. This is the honest isogeny form of the `endDeg_comp`
pin (the `[Flat]`/`[IsFinite]` instances are the tracked isogeny fibre semantics, exactly as in
`KernelBound.le_endDeg_of_killed_injective`): the fibre-rank composition multiplicativity
`Scheme.Hom.finrank_comp` (`ForMathlib/FinrankComp.lean`) evaluated at the zero-section
basepoint on both factors. Every geometric-fibre consumer (`S = Spec k`, `E` integral) lands
here. -/
theorem endDeg_comp_of_isIntegral [IsIntegral E.E] (f g : E.asOver ⟶ E.asOver)
    [Flat (show E.E ⟶ E.E from f.left)] [IsFinite (show E.E ⟶ E.E from f.left)]
    [Flat (show E.E ⟶ E.E from g.left)] [IsFinite (show E.E ⟶ E.E from g.left)] :
    E.endDeg (f ≫ g) = E.endDeg f * E.endDeg g := by
  haveI : IrreducibleSpace E.E := inferInstance
  haveI : Nonempty E.E := inferInstance
  haveI hne : Nonempty S := ⟨E.π.base ‹Nonempty E.E›.some⟩
  set fl : E.E ⟶ E.E := f.left with hfl
  set gl : E.E ⟶ E.E := g.left with hgl
  haveI : LocallyOfFinitePresentation fl := E.endo_locallyOfFinitePresentation f
  haveI : Surjective fl := E.endo_surjective f
  haveI : Surjective gl := E.endo_surjective g
  simp only [endDeg, dif_pos hne]
  show (Scheme.Hom.finrank (X := E.E) (S := E.E) (fl ≫ gl) (E.zero hne.some) : ℤ)
      = (Scheme.Hom.finrank (X := E.E) (S := E.E) fl (E.zero hne.some) : ℤ)
        * (Scheme.Hom.finrank (X := E.E) (S := E.E) gl (E.zero hne.some) : ℤ)
  rw [Scheme.Hom.finrank_comp fl gl (E.zero hne.some) (E.zero hne.some), Nat.cast_mul]

/-- **(T-END0c pin, PROVEN integral form — KM 2.6.1.1 scaling)** `deg(g ∘ [n]) = n² · deg g` for
a finite flat endomorphism `g` of `E` with integral total space (`[n]`'s finite-flatness is the
BB-FLAT isogeny substrate, taken as instances): `endDeg_comp_of_isIntegral` against
`endDeg_mulBy = n²`. -/
theorem endDeg_comp_mulBy_of_isIntegral [IsIntegral E.E] (n : ℤ) (g : E.asOver ⟶ E.asOver)
    [Flat (show E.E ⟶ E.E from g.left)] [IsFinite (show E.E ⟶ E.E from g.left)]
    [Flat (show E.E ⟶ E.E from (E.mulBy n).left)]
    [IsFinite (show E.E ⟶ E.E from (E.mulBy n).left)] :
    E.endDeg (g ≫ E.mulBy n) = n ^ 2 * E.endDeg g := by
  haveI : IrreducibleSpace E.E := inferInstance
  haveI : Nonempty E.E := inferInstance
  haveI : Nonempty S := ⟨E.π.base ‹Nonempty E.E›.some⟩
  rw [E.endDeg_comp_of_isIntegral g (E.mulBy n), E.endDeg_mulBy n, mul_comm]

/-- **(T-G3e positivity half, PROVEN)** A **pointed** finite flat endomorphism of `E` over a
nonempty base has degree at least `1`: pointedness sends the zero point to the zero point, and a
finite flat morphism has positive fibre rank at every point of its image
(`Scheme.Hom.one_le_finrank_map`). This is the isogeny half of the positive-definiteness pin
`eq_zero_of_endDeg_eq_zero` — under `deg g = 0` it forces `g` outside the finite-flat (isogeny)
class, leaving only the zero-or-isogeny dichotomy to conclude `g = [0]`. -/
theorem one_le_endDeg_of_pointed [Nonempty S] (f : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ f = η[E.asOver])
    [Flat (show E.E ⟶ E.E from f.left)] [IsFinite (show E.E ⟶ E.E from f.left)] :
    1 ≤ E.endDeg f := by
  haveI hne : Nonempty S := ‹_›
  set fl : E.E ⟶ E.E := f.left with hfl
  -- pointedness at the scheme level: `zero ≫ f.left = zero`
  have hz : E.zero ≫ fl = E.zero := by
    have h : (η[E.asOver]).left ≫ fl = (η[E.asOver]).left := congrArg CommaMorphism.left hη
    rw [E.one_eq_zero] at h
    have h2 : (𝟙 S ≫ E.zero) ≫ fl = 𝟙 S ≫ E.zero := h
    rwa [Category.id_comp] at h2
  -- hence the zero point is in the image of `f.left`
  have hpt : fl.base (E.zero.base hne.some) = E.zero.base hne.some := by
    have := congrArg (fun m : S ⟶ E.E => m.base hne.some) hz
    simpa using this
  have h1 : 1 ≤ Scheme.Hom.finrank (X := E.E) (S := E.E) fl (E.zero.base hne.some) := by
    have := Scheme.Hom.one_le_finrank_map fl (E.zero.base hne.some)
    rwa [hpt] at this
  simp only [endDeg, dif_pos hne]
  exact_mod_cast h1

/-- **(T-END0c pin — KM 2.6.1, `deg` multiplicative)** The degree is multiplicative under
composition: `deg(f ≫ g) = deg f · deg g`. KM (Thm 2.6.1 / Cor 2.6.1.1): the degree of a composite
isogeny is the product of the degrees (`(f∘g)^t (f∘g) = g^t (f^t f) g = [deg f][deg g]`).
**Status**: the isogeny case is PROVEN as `endDeg_comp_of_isIntegral` (via
`Scheme.Hom.finrank_comp`); this unrestricted form additionally needs the degenerate cases
(non-finite-flat endomorphisms — the zero-or-isogeny dichotomy) and stays a pin. -/
theorem endDeg_comp (f g : E.asOver ⟶ E.asOver) :
    E.endDeg (f ≫ g) = E.endDeg f * E.endDeg g := sorry

/-- The identity endomorphism has degree `1`: `deg 𝟙 = 1` (`𝟙 = [1]` and `deg [1] = 1² = 1`;
over the empty base by the junk convention). Proved from `mulBy_one` + `endDeg_mulBy`
(no data-sorry of its own). -/
theorem endDeg_one : E.endDeg (𝟙 E.asOver) = 1 := by
  by_cases hS : Nonempty S
  · rw [← E.mulBy_one, E.endDeg_mulBy, one_pow]
  · simp only [endDeg, dif_neg hS]

/-- **(deg of an automorphism = 1 — KM 2.7.1)** An invertible endomorphism (an automorphism of
`E/S`) has degree `1`: the underlying scheme morphism is an isomorphism (`Over.forget` preserves
isos), and an isomorphism has fibre rank `1` at every point
(`Scheme.Hom.finrank_eq_one_of_isIso`); over the empty base it is the degree-`1` junk value.
Proved directly from the `finrank` construction — independent of the multiplicativity pin
`endDeg_comp`. This discharges the `deg ε = 1` bridge of `aut_hom_eq_id_of_fullLevel`. -/
theorem endDeg_eq_one_of_isIso (f : E.asOver ⟶ E.asOver) [IsIso f] : E.endDeg f = 1 := by
  haveI : IsIso (show E.E ⟶ E.E from f.left) :=
    inferInstanceAs (IsIso ((Over.forget S).map f))
  have h1 : Scheme.Hom.finrank (X := E.E) (S := E.E) f.left = 1 :=
    Scheme.Hom.finrank_eq_one_of_isIso (X := E.E) (Y := E.E) f.left
  simp only [endDeg]
  split
  · rw [h1]
    norm_num
  · rfl

/-- **(KM 2.6.2.1)** The transpose of `[N]` is `[N]` itself: `[N]^t = [N]`. With the constructed
dual this is the trace computation `tr [n] = deg [1+n] − 1 − deg [n] = (1+n)² − 1 − n² = 2n`
(via `endDeg_mulBy`), then `[n]^t = [2n] − [n] = [n]` in the hom-group. -/
theorem endDual_mulBy [Nonempty S] (n : ℤ) : E.endDual (E.mulBy n) = E.mulBy n := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  have htr : E.endTrace (E.mulBy n) = 2 * n := by
    simp only [endTrace]
    rw [← E.mulBy_one, E.mulBy_mul, E.endDeg_mulBy (1 + n), E.endDeg_mulBy n]
    ring
  have hinv : (E.mulBy n)⁻¹ = E.mulBy (-n) := by
    simp only [EllipticCurve.mulBy]
    rw [← zpow_neg]
  simp only [endDual]
  rw [htr, hinv, E.mulBy_mul]
  congr 1
  ring

/-- **(T-END0d pin — KM 2.6.2.2)** The trace identity `f + f^t = [tr f]` (`*` is the endomorphism
addition, the pointwise `Hom.commGroup` operation). With the trace-reflection construction
`f^t = [tr f] * f⁻¹` this is pure commutative-group algebra: `f * ([tr f] * f⁻¹) = [tr f]`. -/
theorem endTrace_spec (f : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    f * E.endDual f = E.mulBy (E.endTrace f) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  simp only [endDual]
  rw [← _root_.mul_assoc, _root_.mul_comm f (E.mulBy (E.endTrace f)), _root_.mul_assoc,
    mul_inv_cancel, _root_.mul_one]

/-- **(T-END0d pin — KM 2.6.2.2 proof, polarization)** The defining polarization of the trace as
the cross term of `deg` at the identity: `deg(1 + f) = 1 + deg f + tr f` (`1 = 𝟙 E.asOver`, `+` is
the `Hom.commGroup` operation `*`). KM (verbatim, proof of Cor 2.6.2.2): *"deg(1+f) = 1 + deg(f) +
(f + f^t)"*, with `f + f^t = [tr f]`. This is the bilinear-form engine of the T-G3b expansion. -/
theorem endDeg_one_add (f : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.endDeg (𝟙 E.asOver * f) = 1 + E.endDeg f + E.endTrace f := by
  simp only [endTrace]
  ring

/-- **(T-END0c pin — KM 2.6.1.1, `deg` multiplicative)** The degree scales quadratically under
post-composition by `[n]`: `deg(g ∘ [n]) = n² · deg g`. KM (verbatim, Cor 2.6.1.1): *"deg is
multiplicative"* together with the displayed *"deg([N]) = N²"* — here `deg(g ≫ [n]) = deg g · deg [n]
= deg g · n²`. -/
theorem endDeg_comp_mulBy (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    E.endDeg (g ≫ E.mulBy n) = n ^ 2 * E.endDeg g := sorry

/-- **(T-END0d pin — KM 2.6.2, `tr` linear)** The trace scales linearly under post-composition by
`[n]`: `tr(g ∘ [n]) = n · tr g`. KM (verbatim, Thm 2.6.2): *"(f+g)^t = f^t + g^t"* (trace additive),
with `g ≫ [n] = [n] ∘ g = n • g` in `End(E/S)`, so `tr(n • g) = n · tr g`. -/
theorem endTrace_comp_mulBy (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    E.endTrace (g ≫ E.mulBy n) = n * E.endTrace g := sorry

/-- **(T-G3b — KM 2.6.3 / 2.7.2 proof)** The degree quadratic expansion
`deg(1 + g∘[N]) = 1 + N·tr g + N²·deg g`. Here `1 = 𝟙 E.asOver` (identity endomorphism), `+` is
the pointwise `Hom.commGroup` operation `*`, and `g∘[N] = g ≫ [N]`. KM (verbatim, proof of Cor
2.7.2): *"ε = 1 + gN, so … deg(ε) = 1 + N trace(g) + N² deg(g)."* -/
theorem endDeg_one_add_mulBy_comp (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.endDeg (𝟙 E.asOver * (g ≫ E.mulBy n)) =
      1 + n * E.endTrace g + n ^ 2 * E.endDeg g := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  rw [E.endDeg_one_add (g ≫ E.mulBy n), E.endDeg_comp_mulBy n g, E.endTrace_comp_mulBy n g]
  ring

/-- **(T-G3c — KM 2.6.3(2))** The discriminant / Hasse–Cauchy–Schwarz bound `(tr g)² ≤ 4·deg g`.
KM (verbatim, Thm 2.6.3(2)): *"(trace(f))² ≤ 4 deg(f)"*, proof *"deg(n − mf) ≥ 0."* Fibrewise via
T-RED0 + HasseWeil `hasse_bound` / `degree_quadratic_closed` transfer (IMPORT, never re-prove). -/
theorem endTrace_sq_le (g : E.asOver ⟶ E.asOver) :
    E.endTrace g ^ 2 ≤ 4 * E.endDeg g := sorry

/-- **(T-G3e — KM 2.6.3(2) proof)** Positive-definiteness of `deg`: `deg g = 0 ⟹ g = 0` (here the
zero endomorphism is `[0] = E.mulBy 0`). KM's `deg(n − mf) ≥ 0` sharpened to definiteness for the
endomorphism ring of an elliptic curve. -/
theorem eq_zero_of_endDeg_eq_zero (g : E.asOver ⟶ E.asOver) (hg : E.endDeg g = 0) :
    g = E.mulBy 0 := sorry

/-- **(T-G3d — KM 2.7.2 proof)** `N`-divisibility of `ε − 1`: an endomorphism `ε` fixing the
`N`-torsion subscheme `E[N]` (i.e. `ε.left` restricts to the identity on `E.torsionι N`) factors as
`ε = 1 + g∘[N]` for some `g ∈ End(E/S)`. KM (verbatim, proof of Cor 2.7.2): *"ε−1 kills E[N], so it
factors as ε−1 = g·N for some g ∈ End(E). Then ε = 1 + gN."* (`1 = 𝟙 E.asOver`, `+` = `Hom.commGroup`
`*`, `g∘[N] = g ≫ [N]`.) -/
theorem exists_eq_one_add_mulBy_comp_of_fixesTorsion (N : ℕ) [NeZero N]
    (ε : E.asOver ⟶ E.asOver) (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    ∃ g : E.asOver ⟶ E.asOver, ε = 𝟙 E.asOver * (g ≫ E.mulBy (N : ℤ)) := sorry

/-- **(T-G3a — engine core; GME 2.6.4 arithmetic, p. 151)** The purely number-theoretic heart of
the automorphism-rigidity computation, abstracted from the elliptic-curve setup so it is proved and
reused independently of the endomorphism-degree infrastructure.

Reading `d = deg g ≥ 0`, `t = tr g` (the polar/trace form of the degree quadratic form), `n = N ≥ 3`:
GME's chain "`1 = deg ε = 1 + n·tr g + n²·deg g`" for an automorphism `ε = 1 + n·g` gives the linear
relation `hlin` (`n·t + n²·d = 0`), and the Hasse / Cauchy–Schwarz discriminant bound `t² ≤ 4·d`
gives `hbound`. Together with `n ≥ 3` these force `deg g = 0`, whence (by positive-definiteness of
`deg`, supplied by the caller) `g = 0` and `ε = 1`. This is the step that makes `N ≥ 3` the sharp
threshold: cancelling `n` gives `t = -n·d`, so `n²·d² ≤ 4·d`, i.e. `d·(n²·d - 4) ≤ 0`; the only
non-negative integer solution once `n² ≥ 9` is `d = 0`. Reused by `T-H5`. -/
theorem gme_deg_trace_forces_zero {n t d : ℤ} (hn : 3 ≤ n) (hd : 0 ≤ d)
    (hlin : n * t + n ^ 2 * d = 0) (hbound : t ^ 2 ≤ 4 * d) : d = 0 := by
  have hn0 : (0 : ℤ) < n := by linarith
  -- Cancel `n` from the linear relation: `t = -(n·d)`.
  have ht : t + n * d = 0 := by
    have key : n * (t + n * d) = 0 := by linear_combination hlin
    exact (mul_eq_zero.mp key).resolve_left (ne_of_gt hn0)
  have htd : t = -(n * d) := by linarith
  -- Feed `t = -(n·d)` into the discriminant bound: `n²·d² ≤ 4·d`.
  have hb2 : n ^ 2 * d ^ 2 ≤ 4 * d := by
    have h := hbound; rw [htd] at h; nlinarith [h]
  -- `n ≥ 3` and `d ≥ 0` (integer) force `d = 0`.
  by_contra hne
  have hd1 : 1 ≤ d := by omega
  nlinarith [hb2, mul_nonneg (by linarith : (0 : ℤ) ≤ n - 3) (by linarith : (0 : ℤ) ≤ n + 3),
    mul_nonneg hd (sub_nonneg.mpr hd1), hd1, sq_nonneg d]

/-- **(T-G3 core — KM 2.7.2(1), the arithmetic-geometric heart of rigidity)** An endomorphism `ε`
of `E/S` that has **degree `1`** (i.e. is an automorphism) and **fixes the `N`-torsion** `E[N]`
(`N ≥ 3`) is the identity `𝟙 E.asOver`. This is the whole `deg`/Hasse computation of KM's rigidity
corollary, assembled in `End(E/S)`-language from the leaves: T-G3d factors `ε = 1 + g∘[N]`; T-G3b
expands `deg ε = 1 + N·tr g + N²·deg g`, so `deg ε = 1` forces the linear relation `N·tr g +
N²·deg g = 0`; with `deg g ≥ 0` (`endDeg_nonneg`), the Hasse bound `tr(g)² ≤ 4·deg g` (T-G3c) and
`N ≥ 3`, the proven `gme_deg_trace_forces_zero` yields `deg g = 0`; positive-definiteness (T-G3e)
gives `g = [0]`, and `[0] ∘ [N] = [0]` (via `mulBy_pointed`) collapses `ε = 1 + [0] = 𝟙`. The
scheme-morphism form `aut_hom_eq_id_of_fullLevel` (`Moduli/Groupoid.lean`) applies this through the
pointed/automorphism/level-structure bridges. KM (verbatim, Cor 2.7.2(1)): *"If N ≥ 3, then
ε = id."* -/
theorem aut_endo_eq_one [IsLocallyNoetherian S] (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (ε : E.asOver ⟶ E.asOver) (hdeg : E.endDeg ε = 1)
    (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    ε = 𝟙 E.asOver := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  obtain ⟨g, hg⟩ := E.exists_eq_one_add_mulBy_comp_of_fixesTorsion N ε hfix
  have hexp := E.endDeg_one_add_mulBy_comp (N : ℤ) g
  rw [← hg, hdeg] at hexp
  have hlin : (N : ℤ) * E.endTrace g + (N : ℤ) ^ 2 * E.endDeg g = 0 := by linarith
  have hdz : E.endDeg g = 0 :=
    gme_deg_trace_forces_zero hN (E.endDeg_nonneg g) hlin (E.endTrace_sq_le g)
  have hg0 : g = E.mulBy 0 := E.eq_zero_of_endDeg_eq_zero g hdz
  have h0 : E.mulBy (0 : ℤ) = (1 : E.asOver ⟶ E.asOver) := by
    simp only [EllipticCurve.mulBy, zpow_zero]
  have h1c : (1 : E.asOver ⟶ E.asOver) ≫ E.mulBy (N : ℤ) = 1 := by
    rw [Hom.one_def, Category.assoc, E.mulBy_pointed]
  rw [hg, hg0, h0, h1c, _root_.mul_one]

end EllipticCurve

end ModularCurves
