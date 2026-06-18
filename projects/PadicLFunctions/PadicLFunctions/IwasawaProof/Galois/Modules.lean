import PadicLFunctions.Iwasawa.PlusPart
import PadicLFunctions.Iwasawa.StructureTheory.Isotypic
import Mathlib.Algebra.Exact.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Galois Λ(𝒢⁺)-modules for the Iwasawa Main Conjecture  (S13-G, G-DEF)

The Galois-theoretic side of the Iwasawa Main Conjecture (RJW arXiv:2309.15692 §13.2).
Over the cyclotomic tower `F_∞⁺ = ℚ(μ_{p^∞})⁺` with `𝒢⁺ = Gal(F_∞⁺/ℚ)`, the protagonists are
the `Λ(𝒢⁺)`-modules

* `𝒳⁺_∞ = Gal(𝓜⁺_∞/F⁺_∞)`, `𝓜⁺_∞` = maximal abelian pro-`p` extension unramified outside `p`;
* `𝒴⁺_∞ = Gal(𝓛⁺_∞/F⁺_∞)`, `𝓛⁺_∞` = maximal *unramified* abelian pro-`p` extension;
* `Gal(𝓜⁺_∞/𝓛⁺_∞)`,

fitting into the fundamental-Galois-theory short exact sequence (TeX 3806)
`0 → Gal(𝓜⁺_∞/𝓛⁺_∞) → 𝒳⁺_∞ → 𝒴⁺_∞ → 0`.

These infinite Galois groups are not yet constructed in mathlib; following the plan
(`.mathlib-quality/plan-G.md`), `IwasawaGaloisData` **bundles** them as `Λ(𝒢⁺)`-modules
together with that short exact sequence and the finiteness of `𝒳⁺_∞`.  The *class-field-theory*
content is **not** here — the unit/Galois bridge (CFTunits1) is derived from the general
`ClassFieldTheory` interface (tickets G2-*).  `Λ(𝒢⁺)` is the project's completed group algebra
`PadicMeasure p (GPlus p)` (matching §12 and `zetaIdealPlus`).

## Main declarations

* `Iwasawa.Galois.LambdaGPlus p` (notation): the algebra `Λ(𝒢⁺) = PadicMeasure p (GPlus p)`.
* `Iwasawa.Galois.IwasawaGaloisData`: the bundled Galois SES `0 → MmodL → 𝒳⁺ → 𝒴⁺ → 0` of
  `Λ(𝒢⁺)`-modules, with `𝒳⁺` finitely generated over `Λ(𝒢⁺)`.
-/

noncomputable section

namespace Iwasawa.Galois

open PadicMeasure Function

variable (p : ℕ) [Fact p.Prime]

/-- The **plus-part group Iwasawa algebra** `Λ(𝒢⁺) = ℤ_p⟦𝒢⁺⟧`, realised as the project's
completed measure algebra `PadicMeasure p (GPlus p)` (`𝒢⁺ = ℤ_p^× / ⟨-1⟩`).  This is the
coefficient ring of the Galois Iwasawa modules and the target of `zetaIdealPlus`. -/
abbrev LambdaGPlus : Type _ := PadicMeasure p (PadicMeasure.GPlus p)

variable (XPlus YPlus MmodL : Type*)
  [AddCommGroup XPlus] [Module (LambdaGPlus p) XPlus]
  [AddCommGroup YPlus] [Module (LambdaGPlus p) YPlus]
  [AddCommGroup MmodL] [Module (LambdaGPlus p) MmodL]

/-- **Bundled Galois data for the Iwasawa Main Conjecture** (RJW TeX 3687–3808).  For the
`Λ(𝒢⁺)`-modules `𝒳⁺_∞` (`= XPlus`), `𝒴⁺_∞` (`= YPlus`) and `Gal(𝓜⁺_∞/𝓛⁺_∞)` (`= MmodL`), this
records the **fundamental-Galois-theory short exact sequence**
`0 → Gal(𝓜⁺_∞/𝓛⁺_∞) → 𝒳⁺_∞ → 𝒴⁺_∞ → 0` (since `𝓛⁺_∞ ⊆ 𝓜⁺_∞` and `𝒴⁺_∞ = 𝒳⁺_∞/Gal(𝓜⁺_∞/𝓛⁺_∞)`)
together with the finite generation of `𝒳⁺_∞` over `Λ(𝒢⁺)`.

The CFT content is **not** here: the maps `galι`, `galπ` are the inclusion/restriction of Galois
groups (Galois theory), and CFTunits1 — which connects these to units — is *derived* from the
general `ClassFieldTheory` interface (G2). -/
structure IwasawaGaloisData where
  /-- the inclusion `Gal(𝓜⁺_∞/𝓛⁺_∞) ↪ 𝒳⁺_∞`. -/
  galι : MmodL →ₗ[LambdaGPlus p] XPlus
  /-- the restriction `𝒳⁺_∞ ↠ 𝒴⁺_∞`. -/
  galπ : XPlus →ₗ[LambdaGPlus p] YPlus
  /-- `galι` is injective. -/
  galι_injective : Injective galι
  /-- `galπ` is surjective. -/
  galπ_surjective : Surjective galπ
  /-- exactness in the middle: `range galι = ker galπ`. -/
  gal_exact : Exact galι galπ
  /-- `𝒳⁺_∞` is finitely generated over `Λ(𝒢⁺)`. -/
  XPlus_finite : Module.Finite (LambdaGPlus p) XPlus

/-! ## G1 — the finite-level class-group modules `𝒴⁺_n` -/

open NumberField

/-- The **real cyclotomic field** `F_n⁺` at level `n`: the maximal totally real subfield of
`ℚ(μ_{p^n})`.  Realised via mathlib's `CyclotomicField (p^n) ℚ` (which carries the `NumberField`
and class-group API for every `n`), so the whole *tower* is available — unlike the project's
`FglobalPlus` (an `IntermediateField ℚ ℂ_[p]`, used unit-side), which lacks a `NumberField`
instance.  The two representations are identified later, where units meet Galois modules (G4). -/
abbrev RealCyclotomic (n : ℕ) : Type _ :=
  NumberField.maximalRealSubfield (CyclotomicField (p ^ n) ℚ)

/-- **`𝒴⁺_n = ℤ_p ⊗ Cl(F_n⁺)`** (RJW eq Y_n^+, TeX 3819): the `p`-part of the ideal class group
of the real cyclotomic field at level `n`, as a `ℤ_p`-module (`Cl` is finite, so `ℤ_p ⊗ -` is its
`p`-primary part).  By unramified class field theory (Hilbert 94, reused from `FltRegular`) this is
`Gal(𝓛⁺_n/F_n⁺)`; the inverse limit over `n` is `𝒴⁺_∞`. -/
def YPlusFin (n : ℕ) : Type _ :=
  TensorProduct ℤ ℤ_[p] (Additive (ClassGroup (𝓞 (RealCyclotomic p n))))

namespace YPlusFin

instance (n : ℕ) : AddCommGroup (YPlusFin p n) :=
  inferInstanceAs (AddCommGroup (TensorProduct ℤ ℤ_[p] _))

instance (n : ℕ) : Module ℤ_[p] (YPlusFin p n) :=
  inferInstanceAs (Module ℤ_[p] (TensorProduct ℤ ℤ_[p] _))

/-- `𝒴⁺_n` is a finite `ℤ_p`-module: `Cl(F_n⁺)` is finite, so the base change is finitely
generated over `ℤ_p`. -/
instance (n : ℕ) : Module.Finite ℤ_[p] (YPlusFin p n) := by
  have : Module.Finite ℤ (Additive (ClassGroup (𝓞 (RealCyclotomic p n)))) :=
    Module.Finite.of_finite
  exact inferInstanceAs (Module.Finite ℤ_[p] (TensorProduct ℤ ℤ_[p] _))

end YPlusFin

end Iwasawa.Galois
