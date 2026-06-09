import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.Ostrowski

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "p-adic and Adic Spaces" =>

This chapter covers the $`p`-adic numbers $`\mathbb{Q}_p` and integers $`\mathbb{Z}_p`, their
valuation theory, Hensel's lemma, completeness, and the characterisation of absolute values on
$`\mathbb{Q}` by Ostrowski's theorem. Throughout, $`p` denotes a prime. The general language
of valuations underpins all of the constructions.
Adic spaces proper (Huber's theory of perfectoid spaces) lie beyond present mathlib coverage and
are deferred to Phase 3 of the AINTLIB project.

# Valuations

:::definition "valuation" (lean := "Valuation")
Let $`R` be a commutative ring and $`\Gamma_0` a linearly ordered commutative monoid with zero.
A *valuation* on $`R` with values in $`\Gamma_0` is a map $`v : R \to \Gamma_0` satisfying

$$`v(0) = 0, \quad v(1) = 1, \quad v(xy) = v(x)\,v(y), \quad v(x + y) \le \max(v(x), v(y)).`

The last condition is the *ultrametric* (non-archimedean) inequality.
:::

:::definition "valued-ring" (lean := "Valued")
A ring $`R` is called a *valued ring* (with value group $`\Gamma_0`) if it is equipped with a
distinguished valuation $`v : R \to \Gamma_0` ({uses "valuation"}[]). The topology on $`R` is then
the valuation topology, in which open balls around $`x` are the sets $`\{y : v(x - y) < \gamma\}`
for $`\gamma \in \Gamma_0`.
:::

# p-adic valuation and norm

:::definition "padic-val-nat" (lean := "padicValNat")
For a prime $`p` and a nonzero natural number $`n`, the *$`p`-adic valuation* $`v_p(n)` is the
largest exponent $`k \ge 0` such that $`p^k \mid n`. A largest such $`k` exists because $`n` has
a finite prime factorisation ({uses "fta-existence"}[]), namely $`k = v_p(n)` is the exponent of
$`p` in that factorisation. By convention $`v_p(0) = 0`.
:::

:::definition "padic-val-rat" (lean := "padicValRat")
For a prime $`p` and a rational number $`q = a/b` (in lowest terms), the *$`p`-adic valuation*
is

$$`v_p(q) = v_p(a) - v_p(b) \in \mathbb{Z},`

extending {uses "padic-val-nat"}[] from $`\mathbb{N}` to $`\mathbb{Q}`.
:::

:::definition "padic-norm" (lean := "padicNorm")
The *$`p`-adic norm* on $`\mathbb{Q}` is

$$`|q|_p = p^{-v_p(q)}`

for $`q \ne 0`, and $`|0|_p = 0`. It satisfies the ultrametric inequality
$`|q + r|_p \le \max(|q|_p,\, |r|_p)`.
:::

:::proof "padic-norm"
The norm is $`|q|_p = p^{-v_p(q)}`, built from the rational $`p`-adic valuation
({uses "padic-val-rat"}[]). The key step is the multiplicativity $`v_p(qr) = v_p(q) + v_p(r)`,
from which $`|qr|_p = |q|_p\,|r|_p`. The ultrametric inequality reduces to the fact that
$`v_p(q + r) \ge \min(v_p(q), v_p(r))` ({uses "padic-val-nat"}[]), which in turn follows
from the standard divisibility argument: if $`p^k \mid q` and $`p^k \mid r` then $`p^k \mid q + r`.
:::

# The p-adic numbers and integers

:::definition "padic-numbers" (lean := "Padic")
The field $`\mathbb{Q}_p` of *$`p`-adic numbers* is the completion of $`\mathbb{Q}` with
respect to the $`p`-adic norm $`|\cdot|_p` ({uses "padic-norm"}[]). It is constructed as the
quotient of Cauchy sequences of rationals under the $`p`-adic norm by the equivalence relation of
sequences converging to zero. There is a canonical embedding $`\mathbb{Q} \hookrightarrow \mathbb{Q}_p`.
:::

:::definition "padic-integers" (lean := "PadicInt")
The ring $`\mathbb{Z}_p` of *$`p`-adic integers* is the closed unit ball in $`\mathbb{Q}_p`:

$$`\mathbb{Z}_p = \{ x \in \mathbb{Q}_p : |x|_p \le 1 \}.`

It is a subring of $`\mathbb{Q}_p` and contains $`\mathbb{Z}` as a dense subring.
:::

# Metric and analytic properties

:::lemma_ "qp-nonarchimedean" (lean := "Padic.nonarchimedean")
For all $`q, r \in \mathbb{Q}_p`,
$$`\|q + r\|_p \le \max(\|q\|_p,\, \|r\|_p).`
That is, the $`p`-adic norm on $`\mathbb{Q}_p` is non-archimedean (ultrametric).
:::

:::proof "qp-nonarchimedean"
This holds already for $`\mathbb{Q}` with the $`p`-adic norm ({uses "padic-norm"}[]),
and the inequality passes to Cauchy sequences under completion because the max function is continuous.
:::

:::theorem "qp-complete" (lean := "Padic.complete'")
The field $`\mathbb{Q}_p` is complete: every Cauchy sequence in $`\mathbb{Q}_p` converges.
:::

:::proof "qp-complete"
By construction, $`\mathbb{Q}_p` is the completion of $`(\mathbb{Q}, |\cdot|_p)`, so completeness
is immediate from the universal property of the completion. Concretely, one lifts the Cauchy sequence
of equivalence classes to a diagonal sequence of rationals, verifies it is Cauchy in $`\mathbb{Q}`,
and checks that the corresponding element of $`\mathbb{Q}_p` is the limit.
:::

:::theorem "zp-complete" (lean := "PadicInt.completeSpace")
The ring $`\mathbb{Z}_p` is complete as a metric space.
:::

:::proof "zp-complete"
The unit ball $`\mathbb{Z}_p \subseteq \mathbb{Q}_p` is closed ({uses "padic-integers"}[]),
and a closed subspace of the complete space $`\mathbb{Q}_p` ({uses "qp-complete"}[]) is itself
complete.
:::

# Discrete valuation ring structure

:::definition "dvr" (lean := "IsDiscreteValuationRing")
A commutative integral domain $`R` is a *discrete valuation ring* (DVR) if it is a local
principal ideal domain that is not a field. Equivalently, $`R` carries a discrete valuation
({uses "valuation"}[]) $`v` for which it is the valuation ring: $`R` has a unique nonzero prime
ideal $`\mathfrak{m}`, every ideal is a power $`\mathfrak{m}^n`, and the maximal ideal is generated
by a single *uniformiser* $`\pi` with $`v(\pi) = 1`.
:::

:::theorem "zp-is-dvr" (lean := "PadicInt.prime_p, PadicInt.maximalIdeal_eq_span_p")
The ring $`\mathbb{Z}_p` is a discrete valuation ring with uniformiser $`p`. Its maximal ideal is
$`p\mathbb{Z}_p`, every nonzero ideal is of the form $`p^n \mathbb{Z}_p` for some $`n \ge 0`,
and the residue field $`\mathbb{Z}_p / p\mathbb{Z}_p \cong \mathbb{F}_p`.
:::

:::proof "zp-is-dvr"
The ring $`\mathbb{Z}_p` is local with maximal ideal $`\mathfrak{m} = \{x : |x|_p < 1\}`.
Since $`|p|_p = p^{-1}` and every element $`x \in \mathbb{Z}_p` satisfies $`|x|_p = p^{-k}` for
some $`k \ge 0` ({uses "padic-val-nat"}[]), the element $`p` generates $`\mathfrak{m}` and is a
uniformiser. The ideal structure then follows from the total ordering of the valuation
({uses "valuation"}[]).
:::

# Hensel's lemma

:::theorem "hensels-lemma" (lean := "hensels_lemma")
*(Hensel's lemma over $`\mathbb{Z}_p`.)* Let $`F \in \mathbb{Z}_p[X]` be a polynomial and
$`a \in \mathbb{Z}_p` an approximate root satisfying

$$`\|F(a)\|_p < \|F'(a)\|_p^2.`

Then there exists a unique $`z \in \mathbb{Z}_p` with

$$`F(z) = 0, \quad \|z - a\|_p < \|F'(a)\|_p, \quad \|F'(z)\|_p = \|F'(a)\|_p.`
:::

:::proof "hensels-lemma"
The proof is a $`p`-adic Newton iteration. Define a sequence $`a_0 = a` and
$`a_{n+1} = a_n - F(a_n)/F'(a_n)`. Because $`\|F(a)\|_p < \|F'(a)\|_p^2`, Newton's correction
$`F(a_n)/F'(a_n)` has norm strictly less than $`\|F'(a)\|_p`, and the ultrametric inequality
({uses "qp-nonarchimedean"}[]) ensures that the sequence $`(a_n)` is Cauchy. By completeness of
$`\mathbb{Z}_p` ({uses "zp-complete"}[]), it converges to a limit $`z`. Continuity of $`F` and
the norm estimate give $`F(z) = 0`, and uniqueness follows because any two roots close to $`a`
coincide via the same norm estimate.
:::

# Ostrowski's theorem

:::theorem "ostrowski" (lean := "Rat.AbsoluteValue.equiv_real_or_padic")
*(Ostrowski's theorem.)* Every non-trivial absolute value on $`\mathbb{Q}` is equivalent to
either the standard archimedean absolute value $`|\cdot|_\infty`, or to the $`p`-adic absolute
value $`|\cdot|_p` for a unique prime $`p`.

More precisely, two absolute values are *equivalent* if each is a positive real power of the
other, and these are the only equivalence classes.
:::

:::proof "ostrowski"
The proof splits on whether the absolute value is *bounded* on $`\mathbb{N}`:

**Non-archimedean case.** If $`|n| \le 1` for all $`n \in \mathbb{N}`, then for any prime $`p`
with $`|p| < 1`, the absolute value is equivalent to $`|\cdot|_p`. The ultrametric inequality
({uses "padic-norm"}[]) forces all integers with $`\gcd(-, p) = 1` to have absolute value $`1`,
and one reads off the equivalence class from the value of $`|p|`.

**Archimedean case.** If $`|n| > 1` for some $`n`, then $`|\cdot|` is not bounded on $`\mathbb{N}`.
A calculation using the $`n`-adic expansion of any integer in base $`n` shows that
$`|\cdot|` is a power of the ordinary absolute value; hence it is equivalent to $`|\cdot|_\infty`.
:::

# Adic spaces

The constructions above — valuations, the $`p`-adic numbers,
and the DVR structure of $`\mathbb{Z}_p` —
are the arithmetic building blocks for Huber's theory of *adic spaces*, which provides the
correct foundations for $`p`-adic geometry and perfectoid spaces. Adic spaces proper are not
yet formalised in mathlib; they are scheduled for Phase 3 of the AINTLIB project, drawing on
the `Condensed` and `LiquidTensor` work.

The nodes below are *informal*: they are formalised in the external project
[`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (built against a Mathlib version
incompatible with the current AINTLIB build), so they carry no `(lean := …)` reference.
Each records the relevant Lean constructions, their sorry status, and the mathematical
content. They connect into the dependency graph through the Mathlib-backed valuation nodes
of this chapter.

## Huber rings and Tate rings

:::definition "huber-ring"
A topological ring $`A` is called a *Huber ring* (or *$`f`-adic ring*) if it admits a
*pair of definition*: an open subring $`A_0 \subseteq A` and a finitely generated ideal
$`I \subseteq A_0` such that the subspace topology on $`A_0` is the $`I`-adic topology.

Equivalently, one requires that the topology on $`A_0` has the nested open sets
$`I^n` ($`n \ge 0`) as a neighbourhood basis of $`0`, and that $`A_0` is open in $`A`.

The ring $`A_0` is called a *ring of definition* and $`I` an *ideal of definition*. The
ideal $`I` need not be unique, but any two ideals of definition of the same $`A_0` have
the same radical. The class of Huber rings is closed under localisation and completion.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `IsHuberRing`, `PairOfDefinition`.
:::

:::definition "tate-ring"
A *Tate ring* is a Huber ring ({uses "huber-ring"}[]) that contains a *topologically
nilpotent unit*: an element $`u \in A^\times` with $`u^n \to 0` in the topology of $`A`.

Such a unit $`u` is called a *pseudo-uniformiser* and plays the role of a uniformising
parameter in the non-archimedean geometry of $`A`. Every $`p`-adic field $`\mathbb{Q}_p`
is a Tate ring ({uses "padic-numbers"}[]) with pseudo-uniformiser $`p`.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `IsTateRing`.
:::

## Continuous valuations and the valuation spectrum

:::definition "valuation-spectrum"
The *valuation spectrum* $`\mathrm{Spv}(A)` of a commutative ring $`A` is the set of
*equivalence classes* of valuations ({uses "valuation"}[]) on $`A`, where two valuations
$`v_1 : A \to \Gamma_0` and $`v_2 : A \to \Gamma'_0` are equivalent if
$$`v_1(x) \le v_1(y) \iff v_2(x) \le v_2(y) \quad \text{for all } x, y \in A.`

Equivalently, a point of $`\mathrm{Spv}(A)` may be presented as a *valuative relation*:
a preorder on $`A` satisfying the valuation axioms up to the equivalence class. The
topology on $`\mathrm{Spv}(A)` is generated by the *basic open sets*
$$`\mathrm{Spv}(A)(f/s) = \{ v \in \mathrm{Spv}(A) : v(f) \le v(s),\; v(s) \ne 0 \}`
for $`f, s \in A`. The support map $`v \mapsto \{a \in A : v(a) = 0\}` is a continuous
map $`\mathrm{Spv}(A) \to \mathrm{Spec}(A)` to the prime spectrum.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `ValuationSpectrum`, `ValuationSpectrum.basicOpen`, `ValuationSpectrum.supp`.
:::

:::definition "continuous-valuation"
Let $`A` be a topological ring and $`v : A \to \Gamma_0` a valuation ({uses "valuation"}[]).
We say $`v` is *continuous* if for every $`\gamma \in \Gamma_0` the set
$$`\{ a \in A : v(a) < \gamma \}`
is open in $`A`. The set of continuous points of $`\mathrm{Spv}(A)` ({uses "valuation-spectrum"}[])
is denoted $`\mathrm{Cont}(A) \subseteq \mathrm{Spv}(A)`.

For a topological ring with the discrete topology every valuation is continuous;
for a non-archimedean field the $`p`-adic absolute value is continuous in this sense.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `Valuation.IsContinuous`, `Cont`.
:::

## The adic spectrum

:::definition "adic-spectrum"
Let $`A` be a topological ring and $`A^+ \subseteq A` an open, integrally closed subring
satisfying $`A^+ \subseteq A^\circ` (the *subring of integral elements*). The *adic spectrum*
$$`\mathrm{Spa}(A, A^+)`
is the subspace of $`\mathrm{Cont}(A)` ({uses "continuous-valuation"}[]) consisting of all
continuous valuations $`v` that satisfy $`v(f) \le 1` for every $`f \in A^+`:
$$`\mathrm{Spa}(A, A^+) = \{ v \in \mathrm{Cont}(A) : \forall f \in A^+,\; v(f) \le 1 \}.`

The pair $`(A, A^+)` is called an *affinoid ring* (or *Huber pair*). Each point $`v` of
$`\mathrm{Spa}(A, A^+)` has a *support* prime ideal $`\ker v = \{a : v(a) = 0\} \in \mathrm{Spec}(A)`.
The assignment $`A \mapsto \mathrm{Spa}(A, A^+)` is the fundamental functor of Huber's theory;
rational subsets of $`\mathrm{Spa}(A, A^+)` are defined in {uses "rational-subsets"}[].
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `ValuationSpectrum.Spa`, `ValuationSpectrum.ringPlus`.
:::

:::proof "adic-spectrum"
That $`\mathrm{Spa}(A, A^+)` carries the subspace topology from $`\mathrm{Spv}(A)` ({uses "valuation-spectrum"}[])
is immediate from its definition as a subspace of $`\mathrm{Cont}(A)`. The key structural fact is
Proposition 7.52 of Wedhorn: an element $`f \in A` is a unit if and only if $`v(f) \ne 0` for every
$`v \in \mathrm{Spa}(A, A^+)`. The proof constructs, for each maximal ideal $`\mathfrak{m}` that is open
(which holds when the topologically nilpotent elements are open, as in a Tate ring ({uses "tate-ring"}[])),
a trivial valuation on $`A/\mathfrak{m}` that yields a Spa-point with support $`\mathfrak{m}`.
:::

:::definition "rational-subsets"
Let $`X = \mathrm{Spa}(A, A^+)` ({uses "adic-spectrum"}[]) and $`T \subseteq A` a finite subset,
$`s \in A`. The *rational subset*
$$`R(T/s) = \{ v \in X : v(t) \le v(s) \ne 0 \text{ for all } t \in T \}`
is an open subset of $`X`. The rational subsets form a basis for the topology of $`X` and are
closed under finite intersection. They are the standard building blocks for
the sheaf axioms on adic spaces.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `ValuationSpectrum.rationalOpen`.
:::

## Tate algebras and the structure sheaf

:::definition "tate-algebra"
Let $`A` be a non-archimedean Tate ring ({uses "tate-ring"}[]) with pseudo-uniformiser $`\pi`.
The *Tate algebra in $`n` variables*
$$`A\langle X_1, \ldots, X_n \rangle = \Bigl\{ \sum_{\alpha} a_\alpha X^\alpha : a_\alpha \in A,\; a_\alpha \to 0 \Bigr\}`
is the subring of the power series ring $`A[[X_1,\ldots,X_n]]` consisting of series whose
coefficient family tends to zero along the cofinite filter on $`\mathbb{N}^n`. For
$`A = \mathbb{Q}_p` ({uses "padic-numbers"}[]) and $`n = 1` this is the classical ring of
convergent power series on the closed unit $`p`-adic disc.

The univariate version $`A\langle X \rangle` is formalised as `TateAlgebra A`; the
bivariate version as `TateAlgebra₂ A`. The *Laurent Tate algebra*
$`A\langle \zeta, \zeta^{-1} \rangle = A\langle X, Y \rangle/(XY - 1)` is obtained by inverting
the variable, yielding a ring of restricted Laurent series.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free);
see `TateAlgebra`, `TateAlgebra₂`, `LaurentTateAlgebra`.
:::

:::theorem "sheafy-strongly-noetherian"
*(Wedhorn, Theorem 8.28(b).)* Let $`(A, A^+)` be a *strongly noetherian* Tate ring
({uses "tate-ring"}[]): an affinoid ring for which the Tate algebras
$`A\langle X_1, \ldots, X_n \rangle` ({uses "tate-algebra"}[]) are noetherian for every $`n \ge 0`.
Then the presheaf of complete topological rings $`\mathcal{O}_X` on $`X = \mathrm{Spa}(A, A^+)`
({uses "adic-spectrum"}[]), defined by
$$`\mathcal{O}_X(R(T/s)) = \widehat{A[s^{-1}]}`
(completion of the localisation), is a *sheaf* — i.e. $`(A, A^+)` is *sheafy*.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (in progress):
the algebraic separation (`IsSheafy.gluing`) and the gluing condition are established;
the topological inducing component of the embedding (`productRestrictionSub_isInducing_tate`) carries
a remaining `sorry`.
:::

:::proof "sheafy-strongly-noetherian"
The proof proceeds in two parts, following Wedhorn §8.

**Separation.** For any rational covering $`C = \{R(T_i/s_i)\}` of $`R(T/s)`,
the restriction map $`\mathcal{O}_X(R(T/s)) \to \prod_i \mathcal{O}_X(R(T_i/s_i))`
is injective. This rests on Wedhorn Lemma 7.45: for each prime $`\mathfrak{p}` with
$`s \notin \mathfrak{p}`, there exists a Spa-point in $`R(T/s)` with support $`\mathfrak{p}`.
These Spa-points separate elements of the localisation; the strongly noetherian hypothesis
(via {uses "tate-algebra"}[]) ensures the Tate algebra $`A\langle X \rangle` is noetherian,
which forces the rational covering to refine a Laurent cover, reducing separation to a
3×3 diagram chase (Wedhorn Cor. 8.32).

**Gluing.** For compatible sections on the pieces of a rational cover, a global section
is produced by Tate acyclicity ({uses "tate-algebra"}[]): the sequence
$$`0 \to A\langle X \rangle \to A\langle X \rangle \oplus A\langle X \rangle \to A\langle \zeta, \zeta^{-1} \rangle \to 0`
is exact, encoding the covering of the closed disc by two affinoid subdomains.
Wedhorn's refinement lemma (Lemma 8.34) lifts this from Laurent covers to all rational covers.
:::

## Perfectoid rings

:::definition "perfectoid-ring"
Let $`p` be a prime and $`A` a complete, separated, uniform Tate ring ({uses "tate-ring"}[])
of characteristic $`0`. We say $`A` is *perfectoid* (for the prime $`p`) if there exists
a *pseudo-uniformiser* $`\varpi` with the following properties:
1. $`\varpi` is power-bounded ($`\varpi \in A^\circ`),
2. $`\varpi^p \mid p` in $`A^\circ` (i.e.\ $`p = c \varpi^p` for some $`c \in A^\circ`),
3. the Frobenius $`x \mapsto x^p` is surjective on $`A^\circ / p`.

For a perfectoid *field* $`K`, one additionally requires that the topology on $`K` is induced
by a rank-$`1` valuation ({uses "valuation"}[]) whose valuation ring is $`K^\circ`.

The archetype is $`\mathbb{C}_p = \widehat{\overline{\mathbb{Q}_p}}` (the completion of the
algebraic closure of $`\mathbb{Q}_p`) ({uses "padic-numbers"}[]), which is perfectoid with
pseudo-uniformiser $`p^{1/p^\infty}` (a compatible system of $`p`-power roots of $`p`).
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (sorry-free
for the definition); see `IsPerfectoidRing`, `IsPerfectoidField`.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib
pull requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing
at the live PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the Mathlib-backed valuation and
$`p`-adic nodes of this chapter via `{uses}` edges, and should be re-pointed to `(lean := …)`
once the corresponding PR merges.

:::theorem "completion-rat-padic" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/21950")
*(The completion of $`\mathbb{Q}` at a finite place is $`\mathbb{Q}_p`.)* By Ostrowski's theorem
({uses "ostrowski"}[]) the nontrivial places of $`\mathbb{Q}` are the archimedean place and one
finite place for each prime $`p`, the latter given by the $`p`-adic absolute value
({uses "padic-norm"}[]). For each prime $`p`, the completion of $`\mathbb{Q}` at the finite place
$`p` — the completion of $`\mathbb{Q}` with respect to the $`p`-adic absolute value, formed as a
valued field via its adic valuation — is canonically isomorphic, as a valued (indeed topological)
field, to the field of $`p`-adic numbers:
$$`\widehat{\mathbb{Q}}^{(p)} \;\cong\; \mathbb{Q}_p.`
The isomorphism is compatible with the valuations and carries the completion of $`\mathbb{Z}_{(p)}`
onto $`\mathbb{Z}_p` ({uses "padic-integers"}[]).

PR #21950 identifies the abstract place-completion of $`\mathbb{Q}` with the concrete
$`\mathbb{Q}_p` ({uses "padic-numbers"}[]), reconciling the adic-valuation construction with
mathlib's `Padic`. This is the bridge that lets number-field place-completions specialise
correctly to $`\mathbb{Q}`.
In review — [mathlib PR #21950](https://github.com/leanprover-community/mathlib4/pull/21950).
:::

:::theorem "amice-transform" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/23772")
*(Amice transform / Amice equivalence.)* The *Amice transform* sends a $`p`-adic measure $`\mu`
on $`\mathbb{Z}_p` ({uses "padic-integers"}[]) — equivalently a bounded $`\mathbb{Q}_p`-valued
distribution — to the power series
$$`A_\mu(T) \;=\; \int_{\mathbb{Z}_p} (1 + T)^{x}\, d\mu(x) \;=\; \sum_{n \ge 0} \left(\int_{\mathbb{Z}_p} \binom{x}{n}\, d\mu(x)\right) T^{n}.`
The Amice equivalence is the resulting isomorphism of $`\mathbb{Q}_p`-Banach algebras
({uses "padic-numbers"}[])
$$`\mathcal{M}(\mathbb{Z}_p, \mathbb{Q}_p) \;\xrightarrow{\;\sim\;}\; \mathbb{Q}_p\langle\langle T \rangle\rangle^{b}`
between measures on $`\mathbb{Z}_p` and bounded power series (rigid functions on the open unit
disc), under which convolution of measures corresponds to multiplication of power series.

PR #23772 (with its companion #23791) constructs the Amice transform and proves it is an
isomorphism, the analytic foundation for $`p`-adic $`L`-functions and Iwasawa theory.
In review — [mathlib PR #23772](https://github.com/leanprover-community/mathlib4/pull/23772).
:::

:::definition "valuative-rel-padic" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/26886")
A *valuative relation* on a field axiomatises the comparison $`v(x) \le v(y)` of a valuation
({uses "valuation"}[]) without naming the value group, packaging the divisibility preorder that a
valuation induces. PR #26886 equips the $`p`-adic numbers $`\mathbb{Q}_p`
({uses "padic-numbers"}[]) with their canonical `ValuativeRel` instance: the relation
$$`x \preccurlyeq y \;\iff\; |x|_p \le |y|_p \;\iff\; v_p(x) \ge v_p(y),`
together with the compatibility showing this valuative relation induces the standard $`p`-adic
topology and recovers $`\mathbb{Z}_p` ({uses "padic-integers"}[]) as its ring of integers.

This places $`\mathbb{Q}_p` inside the `ValuativeRel` framework, so that results stated for
abstract valued fields apply uniformly to the $`p`-adic numbers.
In review — [mathlib PR #26886](https://github.com/leanprover-community/mathlib4/pull/26886).
:::
