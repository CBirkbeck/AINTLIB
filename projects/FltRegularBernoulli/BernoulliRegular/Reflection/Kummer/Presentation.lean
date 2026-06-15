module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import BernoulliRegular.HilbertClassField

/-!
# Kummer presentation of `ComponentUnramifiedCyclicDegreePExtension`

For `K = ℚ(ζ_p)` containing the primitive `p`-th roots of unity, Kummer
theory presents every cyclic Galois extension `E/K` of degree `p` in the
form `E = K(α)` for some `α ∈ E` with `α^p ∈ K`.  Equivalently, `E` is
the splitting field over `K` of a polynomial `X^p - C γ` with `γ ∈ K`,
chosen as `γ = α^p` (viewed in `K` via the algebra map).

This file packages this presentation as the structure
`KummerPresentation`, derived from a
`ComponentUnramifiedCyclicDegreePExtension` via mathlib's
`exists_root_adjoin_eq_top_of_isCyclic`.  The construction is the
**first refined atomic predicate** in the Kummer-presentation pipeline
described in `KummerCharacterUnitLift.lean`:

> Step 1. Kummer presentation: `E = K(γ_χ^{1/p})` for some `γ_χ ∈ Kˣ`.

Subsequent steps (unit lift via unramifiedness, χ-eigenspace alignment,
injectivity) are tracked separately and consume the data delivered by
this file.

## Main definitions

* `BernoulliRegular.KummerPresentation`: data of `(γ, α)` with
  `γ ∈ K`, `α ∈ E`, `α^p = algebraMap γ`, and `K⟮α⟯ = ⊤`.
* `BernoulliRegular.ComponentUnramifiedCyclicDegreePExtension.kummerPresentation`:
  the extraction of a `KummerPresentation` from the extension data, using
  mathlib's `exists_root_adjoin_eq_top_of_isCyclic`.
* `BernoulliRegular.KummerPresentation.algEquivSplittingField`:
  the algebra equivalence `E ≃ₐ[K] SplittingField (X^p - C γ)`.
* `BernoulliRegular.KummerPresentation.gen_ne_zero`: the chosen `γ` is
  nonzero, so it lies in `Kˣ` (recorded as a unit via `genUnit`).

## References

* Mathlib, `Mathlib/FieldTheory/KummerExtension.lean`
  (`exists_root_adjoin_eq_top_of_isCyclic`, `isCyclic_tfae`).
* Washington, *Introduction to Cyclotomic Fields*, §10.2.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial

namespace BernoulliRegular

universe u v

set_option linter.unusedSectionVars false

section KummerPresentation

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Kummer presentation of a cyclic degree-`p` extension.**

Data witnessing that an extension `E/K` is the Kummer extension
`K(α)` for some `α : E` with `α^p ∈ K`.  Equivalently, `E` is the
splitting field of `X^p - C γ` over `K`, where `γ = α^p` viewed in `K`.

The fields are:

* `gen` — the element `γ ∈ K` whose `p`-th root generates `E/K`;
* `root` — a chosen `p`-th root `α ∈ E` of `γ`;
* `root_pow_eq` — the equation `α^p = algebraMap K E γ`;
* `adjoin_root_eq_top` — the simple-adjoin equation `K⟮α⟯ = ⊤` in `E`.
-/
structure KummerPresentation
    {χ : MulChar (ZMod p)ˣ ℚ}
    {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
    (Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp) where
  /-- The chosen `γ ∈ K` whose `p`-th root generates the extension. -/
  gen : K
  /-- The chosen `p`-th root `α ∈ E` of `γ`. -/
  root : Ext.E
  /-- `α^p = γ` (in `E`, after embedding `γ` via the algebra map). -/
  root_pow_eq : root ^ p = algebraMap K Ext.E gen
  /-- `K⟮α⟯ = ⊤` in `E`: `α` is a primitive element. -/
  adjoin_root_eq_top : (IntermediateField.adjoin K {root} : IntermediateField K Ext.E) = ⊤

namespace KummerPresentation

variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
variable {Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp}

/-- The chosen `γ` is nonzero: it is the `p`-th power of `α`, and `α` cannot
be zero, since otherwise `K⟮α⟯ = K ≠ E` (degree `p > 1`). -/
theorem gen_ne_zero (P : KummerPresentation Ext) : P.gen ≠ 0 := by
  -- If γ = 0 then α^p = 0, hence α = 0; then K⟮α⟯ = K, contradicting
  -- finrank K E = p > 1.
  intro hγ
  -- α^p = algebraMap K E 0 = 0
  have h1 : P.root ^ p = 0 := by
    rw [P.root_pow_eq, hγ, map_zero]
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hα : P.root = 0 := by
    have h2 : P.root ^ p = (0 : Ext.E) := h1
    exact (pow_eq_zero_iff (M₀ := Ext.E) (a := P.root) hp_pos.ne').mp h2
  -- K⟮0⟯ = ⊥
  have hbot : (IntermediateField.adjoin K {P.root} : IntermediateField K Ext.E) = ⊥ := by
    rw [hα]
    -- `K⟮0⟯ = ⊥`
    exact IntermediateField.adjoin_zero
  -- Combining with adjoin_root_eq_top gives ⊥ = ⊤
  have htb : (⊥ : IntermediateField K Ext.E) = (⊤ : IntermediateField K Ext.E) := by
    rw [← hbot, P.adjoin_root_eq_top]
  -- finrank K E = 1 from ⊥ = ⊤
  have hfr : Module.finrank K Ext.E = 1 := by
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at htb
    exact htb
  rw [Ext.degree_eq_p] at hfr
  exact (Fact.out : p.Prime).one_lt.ne' hfr

/-- The chosen `γ` viewed as a unit in `K`. -/
def genUnit (P : KummerPresentation Ext) : Kˣ :=
  Units.mk0 P.gen P.gen_ne_zero

@[simp] lemma genUnit_val (P : KummerPresentation Ext) : (P.genUnit : K) = P.gen := rfl

/-- **The polynomial `X^p - C γ` is irreducible over `K`.**

This follows from `irreducible_X_pow_sub_C_of_root_adjoin_eq_top`: `α` is a
root of `X^p - C γ`, generates `E/K` as a simple extension, and
`finrank K E = p`. -/
theorem irreducible_X_pow_sub_C (P : KummerPresentation Ext) :
    Irreducible (X ^ p - Polynomial.C P.gen) := by
  -- Apply the mathlib lemma with `n := finrank K E = p`.
  have hfr : Module.finrank K Ext.E = p := Ext.degree_eq_p
  have ha : P.root ^ Module.finrank K Ext.E = algebraMap K Ext.E P.gen := by
    rw [hfr]; exact P.root_pow_eq
  have hα : (IntermediateField.adjoin K {P.root} : IntermediateField K Ext.E) = ⊤ :=
    P.adjoin_root_eq_top
  have h := irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    (K := K) (L := Ext.E) (a := P.gen) (α := P.root) ha hα
  -- Rewrite `finrank K E = p` to match the polynomial.
  rw [hfr] at h
  exact h

/-- **`E/K` is a splitting field of `X^p - C γ`.** -/
theorem isSplittingField_X_pow_sub_C (P : KummerPresentation Ext) :
    IsSplittingField K Ext.E (X ^ p - Polynomial.C P.gen) := by
  -- We need primitive p-th roots of unity in K.
  have hζ : (primitiveRoots p K).Nonempty := by
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    refine ⟨IsCyclotomicExtension.zeta p ℚ K, ?_⟩
    rw [mem_primitiveRoots hp_pos]
    exact IsCyclotomicExtension.zeta_spec p ℚ K
  -- Convert to the `finrank K E`-form expected by the mathlib lemma.
  have hK : (primitiveRoots (Module.finrank K Ext.E) K).Nonempty := by
    rw [Ext.degree_eq_p]; exact hζ
  have hfr : Module.finrank K Ext.E = p := Ext.degree_eq_p
  have ha : P.root ^ Module.finrank K Ext.E = algebraMap K Ext.E P.gen := by
    rw [hfr]; exact P.root_pow_eq
  have hα : (IntermediateField.adjoin K {P.root} : IntermediateField K Ext.E) = ⊤ :=
    P.adjoin_root_eq_top
  have h := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    (K := K) (L := Ext.E) hK (a := P.gen) (α := P.root) ha hα
  rw [hfr] at h
  exact h

/-- **The algebra equivalence `E ≃ₐ[K] SplittingField (X^p - C γ)`.**

This is the standard Kummer presentation: `E` is unique up to `K`-algebra
equivalence as the splitting field of the Kummer polynomial. -/
def algEquivSplittingField (P : KummerPresentation Ext) :
    Ext.E ≃ₐ[K] SplittingField (X ^ p - Polynomial.C P.gen) :=
  haveI := P.isSplittingField_X_pow_sub_C
  IsSplittingField.algEquiv Ext.E (X ^ p - Polynomial.C P.gen)

end KummerPresentation

/-- **The Kummer presentation theorem.**

For `K = ℚ(ζ_p)` (which contains the primitive `p`-th roots of unity), every
unramified cyclic degree-`p` extension `E/K` is presented as `K(α)` for some
`α ∈ E` with `α^p ∈ K`.  Equivalently, there exists `γ ∈ K` such that `E`
is the splitting field of `X^p - C γ` over `K`.

This is the constructor producing a `KummerPresentation` from the extension
data, via mathlib's `exists_root_adjoin_eq_top_of_isCyclic`. -/
def ComponentUnramifiedCyclicDegreePExtension.kummerPresentation
    {χ : MulChar (ZMod p)ˣ ℚ}
    {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
    (Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp) :
    KummerPresentation Ext := by
  -- Equip the extension with its non-instance cyclic-Galois data.
  haveI : IsCyclic (Ext.E ≃ₐ[K] Ext.E) := Ext.cyclic
  -- Prepare the cyclic-Kummer hypothesis: K contains primitive `finrank`-th
  -- roots of unity, since `finrank K E = p` and `K = ℚ(ζ_p)`.
  classical
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hζ : (primitiveRoots p K).Nonempty := by
    refine ⟨IsCyclotomicExtension.zeta p ℚ K, ?_⟩
    rw [mem_primitiveRoots hp_pos]
    exact IsCyclotomicExtension.zeta_spec p ℚ K
  have hK : (primitiveRoots (Module.finrank K Ext.E) K).Nonempty := by
    rw [Ext.degree_eq_p]; exact hζ
  -- Apply mathlib's existence lemma.  Use `Exists.choose` to extract the data
  -- (we are constructing data, not a proposition, so `obtain`/`rcases` cannot
  -- destruct `∃` here).
  have hex := exists_root_adjoin_eq_top_of_isCyclic K Ext.E hK
  let α : Ext.E := hex.choose
  have hα_spec :
      α ^ Module.finrank K Ext.E ∈ Set.range (algebraMap K Ext.E) ∧
      (IntermediateField.adjoin K {α} : IntermediateField K Ext.E) = ⊤ := hex.choose_spec
  let γ : K := hα_spec.1.choose
  have hγ : algebraMap K Ext.E γ = α ^ Module.finrank K Ext.E := hα_spec.1.choose_spec
  refine
    { gen := γ
      root := α
      root_pow_eq := ?_
      adjoin_root_eq_top := hα_spec.2 }
  -- α ^ (finrank K E) = algebraMap γ, and finrank K E = p.
  have hpfr : α ^ p = α ^ Module.finrank K Ext.E := by
    congr 1; exact Ext.degree_eq_p.symm
  rw [hpfr]
  exact hγ.symm

end KummerPresentation

end BernoulliRegular

end
