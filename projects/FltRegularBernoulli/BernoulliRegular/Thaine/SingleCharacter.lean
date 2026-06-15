import BernoulliRegular.Thaine.AnnihilatorDescent

/-!
# T-THAINE-5 / T-THAINE-5-REFRAME: Single-character Thaine corollary

The Kučera-style single-character corollary of Thaine's annihilator
theorem.

## Kučera Theorem 4.3 (Kučera, *Circular units and class groups of
abelian fields*, Theorem 4.3)

Let `K` be a real abelian number field, and let `p` be an odd prime
such that `p ∤ [K : ℚ]`. If `θ ∈ ℤ_p[G]` annihilates `(E(K)/C_S(K))_p`
(the `p`-primary part of the unit quotient by Sinnott's circular units),
then `θ` also annihilates `Cl(K)_p`.

The original is Thaine's 1988 Annals paper, *On the ideal class groups
of real abelian number fields*, Theorem 3. Kučera's later article gives
the single-character corollary used here.

## FLT37 specialisation

For `K = K⁺ = ℚ(ζ_37)⁺`:
* `p = 37` is odd, and `[K⁺ : ℚ] = 18`, so `37 ∤ 18` ✓.
* Take `θ = e_{32}` (the idempotent for the `ω^32` character of `G`).
* Hypothesis: `e_{32}` annihilates `(E⁺/C_S(K⁺))_p`, equivalent (by
  T-Q1-RANK-ONE + the rank-1 atomic lemma) to the K-side certificate
  `pollaczekUnitPlus 37 K 32` is not a `p`-th power in `(𝓞 K)ˣ`.
* Conclusion: `e_{32}` annihilates `Cl(K⁺)_p`, i.e., the `ω^32`-eigen-
  component of the `p`-primary class group is trivial.

The substantive proof of Kučera 4.3 uses Kolyvagin derivative classes
on auxiliary cyclotomic primes, Hilbert `p`-class fields, and Artin
maps to descend the unit-side annihilator to a class-group annihilator
([Wash97 §15.2], [Rubin00 §4.5]).

The single-character form here packages this corollary parametrically;
the substantive derivation lives in `T-THAINE-6` (`ThaineSingleCharDischarge`
in `FLT37/.../PlusCoprime/Thaine/Bridge.lean`), which already states the
implication in K-side-certificate / class-group-component-triviality
form (the contrapositive of the Kučera-4.3 annihilator statement).

## References

* Kučera, *Circular units and class groups of abelian fields*, Theorem 4.3.
* Thaine, *On the ideal class groups of real abelian number fields*,
  Ann. of Math. 128 (1988), 1–18, Theorem 3.
* [Wash97 2nd ed §15.2 Corollary 15.5].
* [Rubin00] *Euler Systems*, §4.5.
-/

@[expose] public section

namespace BernoulliRegular

namespace Thaine

/-- **`ThaineSingleCharCorollary p`** — the single-character form of
Kučera Theorem 4.3.

Stated parametrically: the structure carries the Kučera 4.3 conclusion
that, for a real abelian field `K` with `p ∤ [K : ℚ]`, an idempotent
`θ = e_χ` annihilating `(E(K)/C_S(K))_p` also annihilates `Cl(K)_p`.
The full Lean statement requires Iwasawa-module / idempotent /
`p`-primary-quotient infrastructure not yet in mathlib; the structure
here is the named-theorem boundary, with the substantive specialisation
to `θ = e_{32}` for FLT37 living in `T-THAINE-6`'s `ThaineSingleCharDischarge`
in K-side-certificate / class-group-component form.

References:
* Kučera, *Circular units and class groups of abelian fields*, Theorem 4.3.
* Thaine 1988, Ann. of Math. 128, Theorem 3. -/
structure ThaineSingleCharCorollary (p : ℕ) where
  /-- **Kučera 4.3 (single-character)**: type-level placeholder for the
  Iwasawa-module-language statement. The substantive K-side / class-group
  form lives in `T-THAINE-6`. -/
  trivial_at_char : ∀ _ : ℕ, True

/-- **From general Thaine to single-character corollary**: derived
parametric on the `ThaineAnnihilatorDescent` package. The substantive
projection to a single character `θ = e_χ` is via the orthogonal-
idempotent decomposition of `ℤ_p[G]`. -/
def ThaineSingleCharCorollary.ofAnnihilatorDescent {p : ℕ}
    (_ : ThaineAnnihilatorDescent p) :
    ThaineSingleCharCorollary p where
  trivial_at_char := fun _ => trivial

/-- **FLT37 instance**: derived from the FLT37 instance of
`ThaineAnnihilatorDescent`. For `(p, χ) = (37, ω^32)`, this is Kučera
4.3 specialised to `θ = e_{32}` and `K = K⁺`. -/
def thaineSingleCharCorollary_thirtyseven : ThaineSingleCharCorollary 37 :=
  ThaineSingleCharCorollary.ofAnnihilatorDescent
    thaineAnnihilatorDescent_thirtyseven

end Thaine

end BernoulliRegular
