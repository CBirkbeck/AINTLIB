import BernoulliRegular.Thaine.AuxiliaryPrimes
import BernoulliRegular.Thaine.AuxiliaryUnits

/-!
# T-THAINE-3: Kolyvagin derivative classes (parametric structure)

The Kolyvagin derivative `D_τ κ` of a cyclotomic Euler-system class `κ`
along a squarefree product τ = ℓ₁ ⋯ ℓ_n of Thaine-auxiliary primes.
The construction is parametric: given an Euler system `κ` (a coherent
family of cyclotomic units in extensions K(ζ_{τ})) and the auxiliary-prime
data, the derivative class `D_τ κ ∈ E_K ⊗ ℤ/p^n ℤ` satisfies the descent
identities required for Thaine's annihilator descent.

This file ships the **type-level interface** (the structure that
T-THAINE-4's annihilator descent consumes). The substantive Kolyvagin
construction (the actual definition of `D_τ κ` modulo p^n, and the
descent identities) is research-grade Lean and lives in the body of
the substantive content of T-THAINE-3 — to be filled in a refinement.

## References

* [Wash97 2nd ed §15.2] Kolyvagin's lemma.
* [Rubin00] *Euler Systems*, Chapter 4 (the derivative classes).
* Greither, *Annales Inst. Fourier* 42 (1992).
-/

@[expose] public section

namespace BernoulliRegular

namespace Thaine

/-- **`KolyvaginDerivativeData p n`** — the type-level data carrying a
Kolyvagin derivative class at level `n` for the prime `p`. The
substantive content (cyclotomic Euler system, derivative formula,
descent identities) is parametric on this structure.

Filling this is the substantive content of the T-THAINE-3 epic
(Kolyvagin's construction + descent identities, ~300–500 lines of
formalization following [Rubin00 §4]). -/
structure KolyvaginDerivativeData (p n : ℕ) where
  /-- The set of squarefree products of Thaine-auxiliary primes used
  in the descent. -/
  squarefree_products : Set ℕ
  /-- For each squarefree product τ in the set, a marker that the
  derivative class `D_τ` is defined and satisfies the descent
  identities. (Type-level placeholder; the substantive content is
  in the refinement.) -/
  derivative_defined : ∀ τ ∈ squarefree_products, True
  /-- The descent-compatibility marker: derivative classes at
  different levels are compatible. (Type-level placeholder.) -/
  descent_compatible : ∀ τ τ', τ ∈ squarefree_products → τ' ∈ squarefree_products →
    τ ∣ τ' → True

/-- **Existence stub for the FLT37 setting**: at level n = 1 with the
single auxiliary prime ℓ = 149 (i.e., `squarefree_products = {1, 149}`),
`KolyvaginDerivativeData 37 1` is constructible. The substantive content
(derivative formulas) is deferred. -/
def kolyvaginDerivativeData_thirtyseven_one : KolyvaginDerivativeData 37 1 where
  squarefree_products := {1, 149}
  derivative_defined := fun _ _ => trivial
  descent_compatible := fun _ _ _ _ _ => trivial

end Thaine

end BernoulliRegular
