module

public import Mathlib.Tactic

/-!
# Component-level reflection target

This file isolates the readable form of the reflection argument, without
connecting it to component-extension yet.

## Intended notation

The later mathematical object is the cyclotomic field `K = ℚ(ζ_p)`, with `p`
an odd prime.  This file only formalizes the index manipulation and therefore
assumes `Odd p` where parity is needed, rather than carrying primality.

`C` denotes the ideal class group `Cl(𝒪_K)`.

Following Washington notation, `A` denotes the `p`-Sylow subgroup, equivalently
the `p`-primary part, of `C`.  This is enough for the reflection obstruction:
regularity and degree-`p` unramified extensions only see the `p`-primary part of
the class group, and the prime-to-`p` part cannot contribute a degree-`p`
quotient.  Since `C` is abelian, this `p`-primary subgroup is canonical and is
preserved by the Galois action.

`Δ` denotes `Gal(K/ℚ) ≃ (ZMod p)ˣ`.  The notation `A_i` means the `i`-th
`Δ`-component of `A`: the component on which an element `a ∈ (ZMod p)ˣ` acts by
the character `a ↦ a^i`.

Set

```text
V = A / A^p
```

in Washington's multiplicative class-group notation; additively this is
`A / pA`.  This `V` is the elementary `F_p`-vector space actually used by the
formal reflection data.  Write `V_i` for the `i`-th `Δ`-component of `V`, or
equivalently the elementary image of `A_i` in `V`.

Equivalently, one may work dually with the `p`-torsion group `A[p]`.  For a
finite abelian `p`-group component, `A_i ≠ 0`, `V_i ≠ 0`, and `A_i[p] ≠ 0` are
equivalent.  Thus no information relevant to a regularity contradiction is lost
by using only `V`.  Since `|Δ| = p - 1` is prime to `p`, the resulting
`F_p[Δ]` representation is semisimple.

In this scratch file we do not construct the eigenspaces; instead,
`componentNontrivial i` is an abstract predicate meaning that the Washington
component `A_i` is nonzero, equivalently that `V_i` is nonzero.

`IsReflectionComponentIndex p i` means `0 < i < p`, so the boundary components
are excluded.  With the current indexing convention, reflection sends the
`i`-component to the `(p - i)`-component, written
`reflectedComponentIndex p i`.

The intended component-level statement is:

```text
If V_i is nontrivial, then V_{p-i} is nontrivial.
```

Using the equivalence above, this can also be read in Washington notation as:
if `A_i` is nontrivial, then `A_{p-i}` is nontrivial.

For odd `p`, this immediately gives an odd nontrivial component from any
nontrivial component:

* if `i` is odd, we are already on the Herbrand side;
* if `i` is even, then `p - i` is odd, and reflection moves nontriviality there.

Later work should connect `ComponentReflectionData` to the actual
`Δ`-component decomposition of `A` and `V = A / A^p`, with only the elementary
quotient `V` used in the reflection input, and then derive the class-number
bridge used by `Main.lean`.
-/

@[expose] public section

namespace BernoulliRegular

/-- Valid indices for the non-boundary components: `0 < i < p`. -/
def IsReflectionComponentIndex (p i : ℕ) : Prop :=
  0 < i ∧ i < p

/-- The reflected index in the usual reflection pairing. -/
def reflectedComponentIndex (p i : ℕ) : ℕ :=
  p - i

theorem reflectedComponentIndex_isIndex
    {p i : ℕ} (hi : IsReflectionComponentIndex p i) :
    IsReflectionComponentIndex p (reflectedComponentIndex p i) := by
  dsimp [IsReflectionComponentIndex, reflectedComponentIndex] at hi ⊢
  omega

theorem reflectedComponentIndex_odd_of_even
    {p i : ℕ} (hp_odd : Odd p) (hi : IsReflectionComponentIndex p i)
    (hi_even : Even i) :
    Odd (reflectedComponentIndex p i) := by
  simpa [reflectedComponentIndex] using
    Nat.Odd.sub_even (Nat.le_of_lt hi.2) hp_odd hi_even

/-- The clean component-level reflection statement.

The predicate `componentNontrivial i` means "the Washington component `A_i` is
nontrivial", equivalently "`V_i` is nontrivial" for `V = A / A^p`.  The field
`reflected_nontrivial` is exactly the reflection principle: nontriviality
transfers from `i` to `p - i` on the elementary components. -/
structure ComponentReflectionData (p : ℕ) where
  componentNontrivial : ℕ → Prop
  reflected_nontrivial :
    ∀ {i : ℕ}, IsReflectionComponentIndex p i →
      componentNontrivial i → componentNontrivial (reflectedComponentIndex p i)

namespace ComponentReflectionData

/-- If any valid component is nontrivial, reflection supplies a nontrivial odd
component.  This is the precise odd/even split:

* odd `i`: use the original component;
* even `i`: use the reflected component `p - i`, which is odd because `p` is
  odd. -/
theorem exists_odd_nontrivial_of_nontrivial
    {p i : ℕ} (R : ComponentReflectionData p)
    (hp_odd : Odd p) (hi : IsReflectionComponentIndex p i)
    (h_nontrivial : R.componentNontrivial i) :
    ∃ j, IsReflectionComponentIndex p j ∧ Odd j ∧ R.componentNontrivial j := by
  rcases Nat.even_or_odd i with hi_even | hi_odd
  · refine ⟨reflectedComponentIndex p i, ?_, ?_, ?_⟩
    · exact reflectedComponentIndex_isIndex hi
    · exact reflectedComponentIndex_odd_of_even hp_odd hi hi_even
    · exact R.reflected_nontrivial hi h_nontrivial
  · exact ⟨i, hi, hi_odd, h_nontrivial⟩

end ComponentReflectionData

end BernoulliRegular

end
