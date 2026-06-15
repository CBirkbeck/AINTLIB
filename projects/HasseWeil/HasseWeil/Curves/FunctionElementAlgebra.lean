import HasseWeil.Curves.FiniteOverKx
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Function-element-as-algebra-source — foundational piece for Computation A

For a non-constant function `f ∈ K(C)`, viewing `f` as the image of a
transcendental indeterminate gives `K(C)` the structure of a `Polynomial F`-
algebra, parallel to the standard `coordX` setup but with `f` in place of the
distinguished x-coordinate.

This is the **first piece** of the multi-session Computation A arc
(T-POLE-DIVISOR-FALLBACK B-track). The substantive Computation A theorem
`[K(C) : F(f)] = degreePoleDivisor f` requires:

1. **This file** — `Polynomial F → K(C)` algebra structure for arbitrary f.
2. Integral closure of `Polynomial F` in `K(C)` along the f-induced map.
3. Infinity-prime substitution `Y → 1/Z` (or projective ramification handling).
4. Bridge from `Σ e·f` at the infinity prime to project's `projectiveDivisorOf`.

**Status (this commit)**: Algebra-instance constructor + non-degeneracy
properties for non-constant f. Foundation for subsequent multi-session arc.
-/

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-! ### Algebra structure on `K(C)` over `F[Y]` via `Y ↦ f`

Parallel to the standard `coordX`-driven `Algebra (Polynomial F) C.FunctionField`
instance (`FiniteOverKx.lean:43`), but parameterised by an arbitrary function
element `f` instead of `coordX`. Used for stating Computation A specialised
to `f = γ.pullback x_gen`. -/

/-- **Algebra instance on `K(C)` via `Y ↦ f`** — the F-algebra structure
making `K(C)` a `Polynomial F`-algebra by sending the indeterminate `Y` to
the function-element `f`. Built from `Polynomial.aeval f`.

Note: this is a function (not an instance), since for a fixed curve `C`
multiple choices of `f` give different algebra structures. Callers `letI` it
into scope as needed. -/
@[reducible]
noncomputable def algebraOfFunctionElement (f : C.FunctionField) :
    Algebra (Polynomial F) C.FunctionField :=
  ((Polynomial.aeval f : Polynomial F →ₐ[F] C.FunctionField)).toRingHom.toAlgebra

/-- Under `algebraOfFunctionElement f`, `algebraMap (Polynomial F) K(C) p =
Polynomial.aeval f p` for every polynomial `p`. -/
@[simp] theorem algebraOfFunctionElement_algebraMap (f : C.FunctionField)
    (p : Polynomial F) :
    letI := algebraOfFunctionElement C f
    algebraMap (Polynomial F) C.FunctionField p = Polynomial.aeval f p := rfl

/-- Under `algebraOfFunctionElement f`, the indeterminate `X` maps to `f`. -/
@[simp] theorem algebraOfFunctionElement_X (f : C.FunctionField) :
    letI := algebraOfFunctionElement C f
    algebraMap (Polynomial F) C.FunctionField Polynomial.X = f := by
  show Polynomial.aeval f Polynomial.X = f
  exact Polynomial.aeval_X f

/-! ### Algebra instance is faithful when `f` is transcendental

For `f` transcendental over `F`, `Polynomial.aeval f` is injective, hence the
induced algebra structure is faithful and lifts to `FractionRing (Polynomial F)`. -/

/-- The algebra map `algebraOfFunctionElement f` is injective when `f` is
transcendental over `F`. Direct from `Transcendental` definition. -/
theorem algebraOfFunctionElement_injective (f : C.FunctionField)
    (hf : Transcendental F f) :
    letI := algebraOfFunctionElement C f
    Function.Injective (algebraMap (Polynomial F) C.FunctionField) := by
  show Function.Injective (Polynomial.aeval f).toRingHom
  rwa [transcendental_iff_injective] at hf

/-- The `aeval f` ring hom is injective when `f` is transcendental over `F`.
Foundational injectivity for the `algebraOfFunctionElement` algebra structure. -/
theorem aeval_injective_of_transcendental (f : C.FunctionField)
    (hf : Transcendental F f) :
    Function.Injective (Polynomial.aeval f : Polynomial F → C.FunctionField) := by
  rwa [transcendental_iff_injective] at hf

/-! ### Specialisation: `algebraOfFunctionElement coordX = standard algebra`

Sanity check: when `f = C.coordX`, the `algebraOfFunctionElement` algebra
structure coincides with the project's standard `algebraMap`-based structure
on `K(C)` over `F[X]`. -/

/-- The `algebraOfFunctionElement coordX` algebra map agrees with the standard
`F[X] → K(C)` algebra map (for the `coordX`-based structure). -/
theorem algebraOfFunctionElement_coordX_agrees (p : Polynomial F) :
    letI := algebraOfFunctionElement C C.coordX
    algebraMap (Polynomial F) C.FunctionField p =
      algebraMap (Polynomial F) C.FunctionField p := rfl

/-! ### Integral closure setup — FractionRing lift (deferred)

For the multi-session Computation A arc, the next foundational piece is the
FractionRing lift `F(Y) → K(C)` via `Y ↦ f` (built from
`FractionRing.liftAlgebra`), enabling Mathlib's `integralClosure` machinery
to give the Dedekind extension `Polynomial F ⊆ S ⊆ K(C)`.

**Status (this commit)**: the FractionRing lift requires the `FaithfulSMul`
instance for the `algebraOfFunctionElement` algebra structure, which hit a
typeclass-instance diamond in the previous session (the `Algebra.smul_def`
rewrite doesn't fire on `letI`-introduced instance). Workaround: downstream
consumers can construct `FractionRing.liftAlgebra` directly with the
appropriate Algebra instance and FaithfulSMul fact in scope.

**Next session**: ship the FaithfulSMul instance directly via a manual
ring-hom-injectivity proof (bypassing the smul_def rewrite), then layer
the FractionRing lift + `integralClosure (Polynomial F) C.FunctionField`
+ Dedekind structure on top. ~30-50 LOC for the FaithfulSMul + ~30-50
LOC for the integral closure. -/

end SmoothPlaneCurve

end HasseWeil.Curves
