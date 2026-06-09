import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.NumberTheory.Ostrowski

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "p-adic and Adic Spaces" =>

This chapter covers the $`p`-adic numbers $`\mathbb{Q}_p` and integers $`\mathbb{Z}_p` as
formalised in mathlib: the general language of valuations and valuative relations, the $`p`-adic
valuation on $`\mathbb{N}`, $`\mathbb{Z}`, and $`\mathbb{Q}`, the $`p`-adic norm, the completion
$`\mathbb{Q}_p` and its closed unit ball $`\mathbb{Z}_p`, completeness and compactness, the
discrete-valuation-ring structure of $`\mathbb{Z}_p`, Hensel's lemma, Mahler's theorem on
continuous functions, the $`p`-adic complex numbers $`\mathbb{C}_p` and Krasner's lemma, and the
characterisation of absolute values on $`\mathbb{Q}` by Ostrowski's theorem — together with the
identification of the adic completion of $`\mathbb{Q}` at a finite place with $`\mathbb{Q}_p`.
Throughout, $`p` denotes a prime. Every mathlib node carries a `(lean := …)` reference naming the
exact declaration, and its proof sketch follows the argument that declaration actually uses, naming
the lemmas that proof invokes.

The final part of the chapter records the theory of *adic spaces* proper — Huber rings, Tate rings,
the valuation spectrum, continuous valuations, the adic spectrum $`\mathrm{Spa}`, Tate algebras,
the structure sheaf, perfectoid rings and spaces, Witt-vector period rings, tilting, and the
Fargues–Fontaine curve. These are formalised in the external project
[`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces) (Birkbeck), which builds against a Mathlib
version incompatible with the current AINTLIB build, so those nodes are *informal*: they carry no
`(lean := …)` reference but instead a `Formalised in` provenance line linking to the exact source
declaration and reporting its true Lean sorry-status. They connect into the dependency graph through
the Mathlib-backed valuation and $`p`-adic nodes of this chapter. The Adic-Spaces permalinks are
pinned to the recorded local commit `fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd`, which is ahead of
the currently-published `main`; the links are given against that commit for exact-line provenance
even though they may not yet resolve publicly.

# Valuations and valued rings

:::definition "valuation" (lean := "Valuation")
Let $`R` be a commutative ring and $`\Gamma_0` a linearly ordered commutative monoid with zero.
A *valuation* on $`R` with values in $`\Gamma_0` is a map $`v : R \to \Gamma_0` satisfying

$$`v(0) = 0, \quad v(1) = 1, \quad v(xy) = v(x)\,v(y), \quad v(x + y) \le \max(v(x), v(y)).`

The last condition is the *ultrametric* (non-archimedean) inequality. The bundled mathlib object
`Valuation R Γ₀` is the monoid homomorphism $`R \to \Gamma_0` carrying this extra additivity bound.
:::

:::definition "valuative-rel" (lean := "ValuativeRel")
A *valuative relation* on a commutative ring $`R` axiomatises the comparison $`v(x) \le v(y)` of a
valuation ({uses "valuation"}[]) without naming the value group. It is a binary relation
$`x \preccurlyeq y` (read "$`v(x) \le v(y)`") that is a total preorder, is compatible with
multiplication and addition, and for which $`0 \preccurlyeq x` always and $`1 \not\preccurlyeq 0`.
Every valuation induces one; conversely a valuative relation is induced by a canonical valuation
into a quotient value monoid, so the two encode the same data up to equivalence. This is mathlib's
preferred framework for *abstract* valued fields, letting results be stated once and specialised.
:::

:::definition "valued-ring" (lean := "Valued")
A ring $`R` is a *valued ring* (with value group $`\Gamma_0`) if it is equipped with a distinguished
valuation $`v : R \to \Gamma_0` ({uses "valuation"}[]) together with a compatible topology: the
`Valued` class records that the topology on $`R` is the valuation topology, in which the sets
$`\{y : v(x - y) < \gamma\}` for $`\gamma \in \Gamma_0^\times` form a neighbourhood basis at $`x`.
Equivalently the open additive subgroups $`\{y : v(y) < \gamma\}` are a basis of neighbourhoods of
$`0`, making $`R` a topological ring.
:::

# The p-adic valuation and norm

:::definition "padic-val-nat" (lean := "padicValNat")
For a prime $`p` and a nonzero natural number $`n`, the *$`p`-adic valuation* $`v_p(n)` is the
largest exponent $`k \ge 0` with $`p^k \mid n`. Such a largest $`k` exists because $`n` has a finite
prime factorisation ({uses "fta-existence"}[]); concretely mathlib defines $`v_p(n)` as the
multiplicity $`\mathrm{multiplicity}\ p\ n`, the count of $`p` in that factorisation. By convention
$`v_p(0) = 0` and $`v_p(n) = 0` when $`p` is not prime or $`n = 0`.
:::

:::definition "padic-val-int" (lean := "padicValInt")
For a prime $`p` and an integer $`z`, the *$`p`-adic valuation* of $`z` is that of its absolute
value:
$$`v_p(z) = v_p(|z|) \in \mathbb{N},`
reducing to the natural-number valuation ({uses "padic-val-nat"}[]) on $`|z|`. It satisfies
$`p^{\,v_p(z)} \mid z`, is additive on products, and equals $`1` at $`z = p`.
:::

:::definition "padic-val-rat" (lean := "padicValRat")
For a prime $`p` and a rational number $`q`, the *$`p`-adic valuation* is the difference of the
integer valuations ({uses "padic-val-int"}[]) of numerator and denominator:
$$`v_p(q) = v_p(\mathrm{num}\,q) - v_p(\mathrm{den}\,q) \in \mathbb{Z},`
extending {uses "padic-val-nat"}[] from $`\mathbb{N}` to $`\mathbb{Q}`. It is additive,
$`v_p(qr) = v_p(q) + v_p(r)`, and satisfies the ultrametric bound
$`v_p(q + r) \ge \min(v_p(q), v_p(r))`.
:::

:::definition "padic-norm" (lean := "padicNorm")
The *$`p`-adic norm* on $`\mathbb{Q}` is
$$`|q|_p = p^{-v_p(q)} \quad (q \ne 0), \qquad |0|_p = 0,`
built from the rational $`p`-adic valuation ({uses "padic-val-rat"}[]).
:::

:::lemma_ "padic-norm-nonarchimedean" (lean := "padicNorm.nonarchimedean")
The $`p`-adic norm is non-archimedean and multiplicative: for all $`q, r \in \mathbb{Q}`,
$$`|qr|_p = |q|_p\,|r|_p, \qquad |q + r|_p \le \max(|q|_p,\, |r|_p).`
:::

:::proof "padic-norm-nonarchimedean"
Multiplicativity is immediate from additivity of the valuation $`v_p(qr) = v_p(q) + v_p(r)`
({uses "padic-val-rat"}[]), since $`p^{-(a+b)} = p^{-a} p^{-b}`. For the ultrametric inequality
mathlib reduces, when $`q, r, q+r` are all nonzero, to the valuation bound
$`v_p(q + r) \ge \min(v_p(q), v_p(r))`: applying $`p^{-(\cdot)}` (an order-reversing map) turns the
minimum of valuations into the maximum of norms. The valuation bound itself is the divisibility fact
that if $`p^k` divides both numerator-cleared forms of $`q` and $`r` then it divides that of
$`q + r`; the degenerate cases where one term is $`0` are checked directly.
:::

# The p-adic numbers and integers

:::definition "padic-numbers" (lean := "Padic")
The field $`\mathbb{Q}_p` of *$`p`-adic numbers* is the completion of $`\mathbb{Q}` with respect to
the $`p`-adic norm $`|\cdot|_p` ({uses "padic-norm"}[]). Mathlib constructs it as the ring of Cauchy
sequences `PadicSeq p` of rationals under $`|\cdot|_p`, modulo the maximal ideal of sequences
converging to $`0`; this quotient is a field. There is a canonical isometric embedding
$`\mathbb{Q} \hookrightarrow \mathbb{Q}_p`, and the norm extends to $`\mathbb{Q}_p` via the limiting
value `padicNormE`.
:::

:::definition "padic-numbers-valuation" (lean := "Padic.addValuation")
The *additive $`p`-adic valuation* on $`\mathbb{Q}_p` is the additive valuation
$$`v_p : \mathbb{Q}_p \to \mathbb{Z} \cup \{\infty\}, \qquad v_p(0) = \infty,`
extending {uses "padic-val-rat"}[] continuously: for nonzero $`x`, $`v_p(x)` is the integer with
$`\|x\|_p = p^{-v_p(x)}`. As an `AddValuation` it satisfies $`v_p(xy) = v_p(x) + v_p(y)` and
$`v_p(x + y) \ge \min(v_p(x), v_p(y))`, packaging the non-archimedean structure of $`\mathbb{Q}_p`
in valuation-theoretic form (with values in $`\mathbb{Z} \cup \{\infty\}` rather than the
multiplicative $`p^{\mathbb{Z}}`).
:::

:::definition "padic-integers" (lean := "PadicInt")
The ring $`\mathbb{Z}_p` of *$`p`-adic integers* is the closed unit ball in $`\mathbb{Q}_p`:
$$`\mathbb{Z}_p = \{ x \in \mathbb{Q}_p : \|x\|_p \le 1 \}.`
It is a subring of $`\mathbb{Q}_p` ({uses "padic-numbers"}[]) containing $`\mathbb{Z}` as a dense
subring, and $`\mathbb{Q}_p` is its field of fractions ({uses "zp-fraction-field"}[]).
:::

:::lemma_ "zp-fraction-field" (lean := "PadicInt.isFractionRing")
The field of fractions of $`\mathbb{Z}_p` is $`\mathbb{Q}_p`: the inclusion
$`\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p` ({uses "padic-integers"}[]) exhibits $`\mathbb{Q}_p` as
the localisation of $`\mathbb{Z}_p` at its nonzero elements.
:::

:::proof "zp-fraction-field"
Every $`x \in \mathbb{Q}_p` with $`\|x\|_p = p^{m}` for some $`m \ge 0` is a quotient $`x = y / p^{m}`
with $`y = p^{m} x \in \mathbb{Z}_p`, since $`\|p^m x\|_p = p^{-m}\|x\|_p \le 1`. mathlib's
`isFractionRing` instance records exactly this: the map from $`\mathbb{Z}_p` is injective, every
nonzero $`p`-adic integer is sent to a unit of $`\mathbb{Q}_p`, and every $`p`-adic number is such a
fraction, the denominators being powers of $`p`.
:::

# Metric, compactness, and analytic properties

:::lemma_ "qp-nonarchimedean" (lean := "Padic.nonarchimedean")
For all $`q, r \in \mathbb{Q}_p`,
$$`\|q + r\|_p \le \max(\|q\|_p,\, \|r\|_p).`
That is, the $`p`-adic norm on $`\mathbb{Q}_p` is non-archimedean (ultrametric).
:::

:::proof "qp-nonarchimedean"
The inequality holds for $`\mathbb{Q}` with the $`p`-adic norm ({uses "padic-norm-nonarchimedean"}[]),
where it is the valuation bound. Representing $`q` and $`r` as limits of Cauchy sequences of
rationals, the bound passes to the limit because $`\max` is continuous and the extended norm
`padicNormE` is the limit of the rational norms; mathlib transports the rational ultrametric
inequality through this limiting process.
:::

:::theorem "qp-complete" (lean := "Padic.complete'")
The field $`\mathbb{Q}_p` is complete: every Cauchy sequence in $`\mathbb{Q}_p` converges. Concretely,
for a Cauchy sequence $`(f_i)` there is $`q \in \mathbb{Q}_p` with $`\|q - f_i\|_p \to 0`.
:::

:::proof "qp-complete"
By construction $`\mathbb{Q}_p` is the quotient of Cauchy sequences of rationals
({uses "padic-numbers"}[]). Given a Cauchy sequence in $`\mathbb{Q}_p`, mathlib approximates each
term by a rational to within $`2^{-i}` (the rationals are dense), forming a *diagonal* rational
sequence; this diagonal sequence is Cauchy in $`(\mathbb{Q}, |\cdot|_p)`, so it represents an element
$`q \in \mathbb{Q}_p`, and the triangle inequality shows the original sequence converges to $`q`.
The packaged instance `Padic.complete : CauSeq.IsComplete ℚ_[p] norm` records this completeness.
:::

:::theorem "zp-complete" (lean := "PadicInt.completeSpace")
The ring $`\mathbb{Z}_p` is complete as a metric space.
:::

:::proof "zp-complete"
The unit ball $`\mathbb{Z}_p = \{x : \|x\|_p \le 1\} \subseteq \mathbb{Q}_p`
({uses "padic-integers"}[]) is closed, being the preimage of the closed set $`[0,1]` under the
continuous norm. A closed subspace of the complete space $`\mathbb{Q}_p` ({uses "qp-complete"}[]) is
itself complete, which is what `PadicInt.completeSpace` derives.
:::

:::theorem "zp-compact" (lean := "PadicInt.compactSpace, PadicInt.totallyBounded_univ")
The ring of $`p`-adic integers $`\mathbb{Z}_p` is compact.
:::

:::proof "zp-compact"
mathlib proves $`\mathbb{Z}_p` is *totally bounded* and complete, hence compact. For total
bounds (`totallyBounded_univ`): given $`\varepsilon > 0`, choose $`k` with $`p^{-k} < \varepsilon`;
the finitely many residues $`\{\,\overline{0}, \dots, \overline{p^k - 1}\,\}` obtained from the
approximation map $`x \mapsto x \bmod p^k` (`PadicInt.appr`) are an $`\varepsilon`-net, because
$`x - (x \bmod p^k)` lies in $`p^k\mathbb{Z}_p` and so has norm $`\le p^{-k} < \varepsilon`. Total
boundedness together with completeness ({uses "zp-complete"}[]) gives compactness
(`compactSpace`); this is the statement that $`\mathbb{Z}_p` is the inverse limit of the finite rings
$`\mathbb{Z}/p^k\mathbb{Z}`.
:::

:::theorem "qp-proper" (lean := "Padic.instProperSpace")
The field $`\mathbb{Q}_p` is a *proper* metric space: every closed ball is compact. Consequently
$`\mathbb{Q}_p` is locally compact.
:::

:::proof "qp-proper"
A closed ball $`\overline{B}(0, p^{n})` in $`\mathbb{Q}_p` is $`p^{-n}\mathbb{Z}_p`, the image of the
compact set $`\mathbb{Z}_p` ({uses "zp-compact"}[]) under multiplication by $`p^{-n}`, hence compact;
every closed ball is a translate of one of these. mathlib derives `ProperSpace ℚ_[p]` from the
compactness of $`\mathbb{Z}_p` via the normed-field criterion that a closed ball around $`0` is
compact. Local compactness is immediate, since the closed unit ball is then a compact neighbourhood
of $`0`.
:::

# Discrete valuation ring structure

:::definition "dvr" (lean := "IsDiscreteValuationRing")
A commutative integral domain $`R` is a *discrete valuation ring* (DVR) if it is a local principal
ideal domain that is not a field. Equivalently $`R` is a noetherian local domain whose maximal ideal
is principal and nonzero. Such an $`R` carries a discrete valuation ({uses "valuation"}[]) $`v` for
which it is the valuation ring: there is a unique nonzero prime ideal $`\mathfrak{m}`, every nonzero
ideal is a power $`\mathfrak{m}^n`, and $`\mathfrak{m}` is generated by a single *uniformiser* $`\pi`.
:::

:::theorem "zp-is-dvr" (lean := "PadicInt.instIsDiscreteValuationRing")
The ring $`\mathbb{Z}_p` is a discrete valuation ring ({uses "dvr"}[]) with uniformiser $`p`.
:::

:::proof "zp-is-dvr"
mathlib verifies the criterion `ofHasUnitMulPowIrreducibleFactorization`: there is an irreducible
element $`\pi` such that every nonzero $`x` factors as $`x = u\,\pi^{n}` with $`u` a unit. Here
$`\pi = p`, which is irreducible (`PadicInt.irreducible_p`, from `prime_p`,
{uses "zp-maximal-ideal"}[]), and the factorisation is $`x = \mathrm{unitCoeff}(x)\cdot p^{\,v(x)}`
where $`v(x)` is the integer valuation of $`x` and `unitCoeff x` is the unit $`x / p^{v(x)}` of norm
$`1` ({uses "padic-integers"}[]). This exhibits $`\mathbb{Z}_p` as a DVR.
:::

:::lemma_ "zp-maximal-ideal" (lean := "PadicInt.maximalIdeal_eq_span_p, PadicInt.prime_p")
The element $`p` is prime in $`\mathbb{Z}_p` and generates the maximal ideal:
$$`\mathfrak{m} = p\,\mathbb{Z}_p = \{\, x \in \mathbb{Z}_p : \|x\|_p < 1 \,\}.`
The residue field is $`\mathbb{Z}_p / p\mathbb{Z}_p \cong \mathbb{F}_p`.
:::

:::proof "zp-maximal-ideal"
The local ring $`\mathbb{Z}_p` has maximal ideal the set of non-units, and $`x` is a unit of
$`\mathbb{Z}_p` exactly when $`\|x\|_p = 1`; thus $`\mathfrak{m} = \{x : \|x\|_p < 1\}`. mathlib
identifies this with $`p\mathbb{Z}_p` through the norm characterisation of divisibility by $`p`
(`norm_lt_one_iff_dvd`: $`\|x\|_p < 1 \iff p \mid x`), giving
$`\mathfrak{m} = \mathrm{span}\{p\}` (`maximalIdeal_eq_span_p`). Primality of $`p` (`prime_p`) follows
because $`\mathrm{span}\{p\}` is then a nonzero maximal, hence prime, ideal. The residue field
$`\mathbb{Z}_p/p\mathbb{Z}_p` has $`p` elements, the residues $`0, \dots, p-1`, so is $`\mathbb{F}_p`.
:::

:::lemma_ "zp-ideals" (lean := "PadicInt.ideal_eq_span_pow_p")
Every nonzero ideal of $`\mathbb{Z}_p` is a power of the maximal ideal: for $`\mathfrak{a} \ne 0`
there is $`n \ge 0` with
$$`\mathfrak{a} = p^{n}\,\mathbb{Z}_p.`
:::

:::proof "zp-ideals"
This is the general structure of ideals in a discrete valuation ring ({uses "zp-is-dvr"}[]) applied
with the uniformiser $`p`: `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible` says every nonzero
ideal of a DVR is generated by a power of any fixed irreducible element. Since $`p` is irreducible in
$`\mathbb{Z}_p` ({uses "zp-maximal-ideal"}[]), the ideal is $`\mathrm{span}\{p^{n}\} = p^{n}\mathbb{Z}_p`
where $`n` is the minimal valuation attained on $`\mathfrak{a}`.
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
mathlib's proof is the $`p`-adic Newton iteration, carried out explicitly. When $`F(a) = 0` the
point $`a` already works. Otherwise the sequence $`a_0 = a`, $`a_{n+1} = a_n - F(a_n)/F'(a_n)` is
built by `newton_seq_aux`, each step staying in $`\mathbb{Z}_p` because the hypothesis
$`\|F(a)\|_p < \|F'(a)\|_p^2` keeps Newton's correction small. The distance estimates
`newton_seq_dist` show $`\|a_{n+1} - a_n\|_p` decreases geometrically, so $`(a_n)` is Cauchy; by
completeness of $`\mathbb{Z}_p` ({uses "zp-complete"}[]) it converges to a limit $`z = `
`soln_gen`. Continuity of polynomial evaluation gives $`F(z) = 0` (`eval_soln`), the telescoped
distance bound gives $`\|z - a\|_p < \|F'(a)\|_p`, and the ultrametric inequality
({uses "qp-nonarchimedean"}[]) gives $`\|F'(z)\|_p = \|F'(a)\|_p`. Uniqueness (`soln_unique`) follows
because any two roots within $`\|F'(a)\|_p` of $`a` would have to coincide, the same norm estimate
forcing their difference to $`0`.
:::

# Mahler's theorem

:::definition "mahler-basis" (lean := "mahler")
For each $`k \in \mathbb{N}` the *Mahler basis function* $`\binom{x}{k}` is the unique continuous
map $`\mathbb{Z}_p \to \mathbb{Z}_p` agreeing with the binomial coefficient $`n \mapsto \binom{n}{k}`
on the dense subset $`\mathbb{N} \subseteq \mathbb{Z}_p`. It is realised as the generalised binomial
coefficient $`\mathrm{Ring.choose}\ x\ k`, a polynomial of degree $`k` in $`x` with rational
coefficients that nonetheless takes $`p`-adic integer values.
:::

:::theorem "mahler-theorem" (lean := "PadicInt.mahlerEquiv")
*(Mahler's theorem.)* Let $`E` be a normed $`\mathbb{Z}_p`-module that is complete. Every continuous
function $`f : \mathbb{Z}_p \to E` has a uniformly convergent *Mahler expansion*
$$`f(x) = \sum_{k \ge 0} \binom{x}{k}\,(\Delta^{k} f)(0),`
where $`\Delta` is the forward difference operator and the coefficients $`(\Delta^{k}f)(0)` tend to
$`0`. The map $`f \mapsto \bigl(k \mapsto (\Delta^{k}f)(0)\bigr)` is an isometric isomorphism of
Banach spaces
$$`C(\mathbb{Z}_p, E) \;\xrightarrow{\;\sim\;}\; C_0(\mathbb{N}, E)`
between continuous functions on $`\mathbb{Z}_p` and null sequences in $`E`.
:::

:::proof "mahler-theorem"
Following Bojanić, mathlib first bounds the Mahler basis ({uses "mahler-basis"}[]): each
$`\binom{x}{k}` has supremum norm $`\le 1` on $`\mathbb{Z}_p`. For a continuous $`f`, the forward
differences $`(\Delta^{k}f)(0)` tend to $`0` (`fwdDiff_tendsto_zero`), using uniform continuity of
$`f` on the compact space $`\mathbb{Z}_p` ({uses "zp-compact"}[]) and the non-archimedean estimate
that $`\Delta^{k}` averages values of $`f` over a shrinking ball. Hence the *Mahler series*
$`\sum_k \binom{x}{k}\,(\Delta^{k}f)(0)` converges uniformly (a null-coefficient series of
norm-$`\le 1` functions converges in the ultrametric setting, `hasSum_mahlerSeries`), defining a
continuous function. It agrees with $`f` on $`\mathbb{N}` by the finite-difference calculus
$`f(n) = \sum_k \binom{n}{k}\Delta^k f(0)`, and both sides are continuous, so they agree on the dense
set $`\mathbb{Z}_p` — this is `hasSum_mahler`. The assignment is norm-preserving in both directions,
yielding the isometric Banach-space isomorphism `mahlerEquiv`.
:::

# The p-adic complex numbers and Krasner's lemma

:::definition "padic-complex" (lean := "PadicComplex")
The field $`\mathbb{C}_p` of *$`p`-adic complex numbers* is the completion of an algebraic closure of
$`\mathbb{Q}_p`:
$$`\mathbb{C}_p = \widehat{\overline{\mathbb{Q}_p}},`
where $`\overline{\mathbb{Q}_p}` (mathlib's `PadicAlgCl p`) is a fixed algebraic closure of
$`\mathbb{Q}_p` ({uses "padic-numbers"}[]), equipped with the unique extension of the $`p`-adic
absolute value (the spectral norm). $`\mathbb{C}_p` carries both a normed-field and a valued-field
({uses "valued-ring"}[]) structure; its ring of integers $`\mathcal{O}_{\mathbb{C}_p}` is the closed
unit ball.
:::

:::lemma_ "padic-complex-norm" (lean := "PadicComplex.norm_extends, PadicComplex.isNonarchimedean")
The norm on $`\mathbb{C}_p` extends the $`p`-adic norm on $`\mathbb{Q}_p` ({uses "padic-norm"}[]) and
is non-archimedean: for $`x \in \mathbb{Q}_p`, $`\|x\|_{\mathbb{C}_p} = \|x\|_p`, and for all
$`x, y \in \mathbb{C}_p`,
$$`\|x + y\|_{\mathbb{C}_p} \le \max(\|x\|_{\mathbb{C}_p}, \|y\|_{\mathbb{C}_p}).`
:::

:::proof "padic-complex-norm"
On $`\overline{\mathbb{Q}_p}` the norm is the *spectral norm* $`\|x\| = \|N_{\mathbb{Q}_p(x)/\mathbb{Q}_p}(x)\|_p^{1/[\mathbb{Q}_p(x):\mathbb{Q}_p]}`,
the unique multiplicative extension of $`|\cdot|_p` to each finite subextension; mathlib's
`isNonarchimedean_spectralNorm` shows it is non-archimedean, and it visibly restricts to $`|\cdot|_p`
on $`\mathbb{Q}_p` (`norm_extends`). Completing preserves both properties: the ultrametric inequality
is a closed condition, so it persists in $`\mathbb{C}_p`, and the norm of a limit is the limit of the
norms, so the extension property persists too.
:::

:::definition "krasner-property" (lean := "IsKrasner")
For a field extension $`L/K` with $`L` a normed field, the predicate $`\mathrm{IsKrasner}\ K\ L`
abstracts the conclusion of Krasner's lemma: whenever $`x \in L` is separable over $`K` with all its
$`K`-conjugates in $`L`, $`y \in L` is integral over $`K`, and $`y` is strictly closer to $`x` than
any other conjugate root,
$$`\|x - y\| < \|x - x'\| \text{ for every conjugate } x' \ne x \;\Longrightarrow\; x \in K(y),`
then $`x` lies in the subfield $`K(y)` generated by $`y`.
:::

:::theorem "krasner" (lean := "IsKrasner.of_completeSpace")
*(Krasner's lemma.)* Let $`K` be a complete, non-trivially valued, ultrametric (non-archimedean)
field — its absolute value coming from a valuation ({uses "valuation"}[]) — and $`L/K` an algebraic
extension whose norm extends that of $`K`. Then
$`\mathrm{IsKrasner}\ K\ L` holds ({uses "krasner-property"}[]): if $`y` is closer to a separable
element $`x` than $`x` is to any of its other conjugates, then $`x \in K(y)`.
:::

:::proof "krasner"
mathlib reduces (`of_completeSpace`) to the case where $`L/K` is normal (`of_completeSpace_of_normal`)
by passing to a normal closure $`C`. In the normal case, suppose for contradiction $`x \notin K(y)`.
Then some $`K(y)`-automorphism $`\sigma` of the extension moves $`x`, so $`\sigma(x) = x'` is a
conjugate of $`x` distinct from $`x`. Because $`\sigma` fixes $`y` and the norm is invariant under
$`K`-automorphisms of a complete non-archimedean field (the extension of a complete valuation to an
algebraic extension is unique, hence Galois-stable),
$$`\|x - x'\| = \|x - \sigma(x)\| = \|\sigma(x - y) - (x - y)\|_{\phantom{p}} \le \|x - y\|,`
using the ultrametric bound and $`\|\sigma(x-y)\| = \|x-y\|`. This contradicts the hypothesis
$`\|x - y\| < \|x - x'\|`. Hence $`x \in K(y)`.
:::

:::theorem "padic-complex-alg-closed" (lean := "PadicComplex.isAlgClosed")
The field $`\mathbb{C}_p` is algebraically closed.
:::

:::proof "padic-complex-alg-closed"
This is the $`p`-adic analogue of the fact that completions of algebraically closed valued fields
stay algebraically closed, and it rests on Krasner's lemma ({uses "krasner"}[]). The algebraic
closure $`\overline{\mathbb{Q}_p}` of the $`p`-adic numbers $`\mathbb{Q}_p` ({uses "padic-numbers"}[])
is algebraically closed by construction; mathlib shows its
completion $`\mathbb{C}_p` remains so via the dense-image criterion: given a monic polynomial $`g`
over $`\mathbb{C}_p`, approximate it by a polynomial $`f` over the dense subfield
$`\overline{\mathbb{Q}_p}`. A root $`b` of $`f` lies in $`\overline{\mathbb{Q}_p}`, and Krasner's
lemma ({uses "krasner"}[]) shows a chosen root $`a` of $`g` is so close to $`b` that
$`\mathbb{C}_p(a) = \mathbb{C}_p(b)`, placing the root of $`g` already in $`\mathbb{C}_p`. Hence every
polynomial splits and $`\mathbb{C}_p` is algebraically closed.
:::

# Ostrowski's theorem and the adic completion of the rationals

:::theorem "ostrowski" (lean := "Rat.AbsoluteValue.equiv_real_or_padic")
*(Ostrowski's theorem.)* Every non-trivial absolute value on $`\mathbb{Q}` is equivalent to either
the standard archimedean absolute value $`|\cdot|_\infty`, or to the $`p`-adic absolute value
$`|\cdot|_p` ({uses "padic-norm"}[]) for a unique prime $`p`. Two absolute values are *equivalent*
when each is a fixed positive real power of the other.
:::

:::proof "ostrowski"
mathlib splits on whether the absolute value $`f` is *bounded* on $`\mathbb{N}`.

**Non-archimedean case** (`equiv_padic_of_bounded`). If $`f(n) \le 1` for all $`n \in \mathbb{N}`,
let $`p` be the least natural with $`0 < f(p) < 1`; mathlib shows $`p` is prime
(`is_prime_of_minimal_nat_zero_lt_and_lt_one`), since a composite would factor with one factor of
absolute value $`< 1`, contradicting minimality. Writing $`f(p) = p^{-t}` for some $`t > 0`, the
ultrametric inequality ({uses "padic-norm-nonarchimedean"}[]) forces $`f(n) = 1` for every $`n`
coprime to $`p`, so $`f = (|\cdot|_p)^{t}` on all of $`\mathbb{Q}` by multiplicativity; uniqueness of
$`p` is the minimality.

**Archimedean case** (`equiv_real_of_unbounded`). If $`f(n) > 1` for some $`n`, then comparing the
base-$`n` expansions of large integers bounds $`f(m) \le C\,m^{s}` with $`s = \log f(n)/\log n`
independent of $`m`; pushing this through powers $`m^k` and taking $`k`-th roots removes the constant,
giving $`f(m) = m^{s} = |m|_\infty^{\,s}`, so $`f` is equivalent to the real absolute value.
:::

:::theorem "completion-rat-padic" (lean := "Padic.adicCompletionEquiv, Rat.HeightOneSpectrum.adicCompletion.padicEquiv")
*(The completion of $`\mathbb{Q}` at a finite place is $`\mathbb{Q}_p`.)* By Ostrowski's theorem
({uses "ostrowski"}[]) the finite places of $`\mathbb{Q}` are indexed by the primes $`p`, each given
by the $`p`-adic absolute value ({uses "padic-norm"}[]). For each prime $`p`, the adic completion of
$`\mathbb{Q}` at the corresponding height-one prime $`v` of $`\mathbb{Z}` — the uniform-space
completion $`\widehat{\mathbb{Q}}_v` for the $`v`-adic valuation — is canonically isomorphic, as a
continuous $`\mathbb{Q}`-algebra (indeed as a valued, hence topological, field), to the field of
$`p`-adic numbers:
$$`\widehat{\mathbb{Q}}_v \;\cong\; \mathbb{Q}_p.`
:::

:::proof "completion-rat-padic"
The height-one primes of $`\mathbb{Z}` are exactly the primes $`p` (`primesEquiv`), and for the prime
$`v` over $`p` the $`v`-adic absolute value on $`\mathbb{Q}` is a fixed power of $`|\cdot|_p`
({uses "ostrowski"}[]), so the two completions are completions of $`\mathbb{Q}` for the same uniform
structure. mathlib builds the continuous $`\mathbb{Q}`-algebra isomorphism `adicCompletion.padicEquiv`
between $`\widehat{\mathbb{Q}}_v` and $`\mathbb{Q}_p` ({uses "padic-numbers"}[]) by extending the
identity on the common dense subfield $`\mathbb{Q}` and checking it is bijective
(`padicEquiv_bijOn`) and an isometry; `Padic.adicCompletionEquiv` is the inverse. The isomorphism
restricts to a continuous $`\mathbb{Z}`-algebra isomorphism of rings of integers
$`\widehat{\mathbb{Z}}_v \cong \mathbb{Z}_p` ({uses "padic-integers"}[]), namely
`PadicInt.adicCompletionIntegersEquiv`. This identifies the abstract place-completion with mathlib's
concrete `Padic`, the bridge that lets number-field place-completions specialise correctly to
$`\mathbb{Q}`.
:::

:::definition "padic-valuative-rel" (lean := "Padic.instValuativeRel")
The $`p`-adic numbers carry a canonical *valuative relation* ({uses "valuative-rel"}[]): the relation
$$`x \preccurlyeq y \;\iff\; \|x\|_p \le \|y\|_p \;\iff\; v_p(x) \ge v_p(y)`
induced by the multiplicative $`p`-adic valuation ({uses "padic-numbers-valuation"}[]). With this
instance $`\mathbb{Q}_p` becomes a non-trivially, rank-one valued field in mathlib's `ValuativeRel`
framework: $`\|p\|_p < 1` witnesses non-triviality, and the value group $`p^{\mathbb{Z}}` is
archimedean (rank one). The relation induces the standard $`p`-adic topology and recovers
$`\mathbb{Z}_p` ({uses "padic-integers"}[]) as its ring of integers, so results stated for abstract
valued fields apply uniformly to the $`p`-adic numbers.
:::

# Adic spaces: Huber rings and Tate rings

The constructions above — valuations, the $`p`-adic numbers, and the DVR structure of
$`\mathbb{Z}_p` — are the arithmetic building blocks for Huber's theory of *adic spaces*, the
correct foundations for $`p`-adic geometry and perfectoid spaces. The nodes in the remainder of this
chapter are *informal*: they are formalised in the external project
[`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces), built against an incompatible Mathlib
version, so they carry no `(lean := …)` reference. Each records the relevant Lean declaration, an
exact-source permalink (pinned to commit `fb55cd8`), and its true sorry-status, and connects into the
graph through the Mathlib-backed valuation nodes above.

:::definition "huber-ring"
A topological ring $`A` is a *Huber ring* (or *$`f`-adic ring*) if it admits a *pair of definition*:
an open subring $`A_0 \subseteq A` together with a finitely generated ideal $`I \subseteq A_0` such
that the subspace topology on $`A_0` equals the $`I`-adic topology — equivalently, the powers
$`I^{n}` form a neighbourhood basis of $`0` in $`A_0`. The ring $`A_0` is a *ring of definition* and
$`I` an *ideal of definition*; $`I` is not unique, but any two ideals of definition of $`A_0` have
the same radical, and the topologically nilpotent elements of $`I` are open. Following Wedhorn §6.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`PairOfDefinition`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/HuberRings.lean#L56), [`IsHuberRing`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/HuberRings.lean#L70) — sorry-free.
:::

:::definition "tate-ring"
A *Tate ring* is a Huber ring ({uses "huber-ring"}[]) that contains a *topologically nilpotent unit*:
an element $`u \in A^\times` with $`u^{n} \to 0`. Such a $`u` is a *pseudo-uniformiser*, the role of a
uniformising parameter in non-archimedean geometry. In a Tate ring the set $`A^{\circ\circ}` of
topologically nilpotent elements is open (Proposition 6.13(1)), and every $`p`-adic field
$`\mathbb{Q}_p` ({uses "padic-numbers"}[]) is a Tate ring with pseudo-uniformiser $`p`. Following
Wedhorn Definition 6.10.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`IsTateRing`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/HuberRings.lean#L77), [`IsTateRing.isOpen_topologicalNilradical`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/HuberRings.lean#L306) — sorry-free.
:::

# The valuation spectrum and continuous valuations

:::definition "valuation-spectrum"
The *valuation spectrum* $`\mathrm{Spv}(A)` of a commutative ring $`A` is the set of equivalence
classes of valuations ({uses "valuation"}[]) on $`A`, where $`v_1` and $`v_2` are equivalent if
$$`v_1(x) \le v_1(y) \iff v_2(x) \le v_2(y) \quad \text{for all } x, y \in A.`
A point is presented as a *valuative relation* ({uses "valuative-rel"}[]) on $`A`. The topology is
generated by the *basic open sets*
$$`\mathrm{Spv}(A)(f/s) = \{ v : v(f) \le v(s) \ne 0 \}, \qquad f, s \in A,`
and the support map $`v \mapsto \{a : v(a) = 0\}` is a continuous map
$`\mathrm{Spv}(A) \to \mathrm{Spec}(A)`. Following Wedhorn Definition 4.1.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`ValuationSpectrum`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/ValuationSpectrum.lean#L33), [`basicOpen`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/ValuationSpectrum.lean#L54), [`supp`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/ValuationSpectrum.lean#L132) — sorry-free.
:::

:::definition "continuous-valuation"
Let $`A` be a topological ring and $`v : A \to \Gamma_0` a valuation ({uses "valuation"}[]). Then
$`v` is *continuous* if for every $`\gamma \in \Gamma_0` the set $`\{a : v(a) < \gamma\}` is open in
$`A`. The continuous points of $`\mathrm{Spv}(A)` ({uses "valuation-spectrum"}[]) form the subspace
$`\mathrm{Cont}(A) \subseteq \mathrm{Spv}(A)`. For a discrete topology every valuation is continuous;
the $`p`-adic absolute value on $`\mathbb{Q}_p` is continuous in this sense. Following Wedhorn
Definition 7.7.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`Valuation.IsContinuous`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/ContinuousValuations.lean#L34), [`Cont`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/ContinuousValuations.lean#L136) — sorry-free.
:::

# The adic spectrum

:::definition "affinoid-ring"
Let $`A` be a topological ring. A subring $`A^{+} \subseteq A` is a *ring of integral elements* if it
is open, integrally closed in $`A`, and contained in the subring $`A^{\circ}` of power-bounded
elements. The pair $`(A, A^{+})` is then an *affinoid ring* (or *Huber pair*). Every ring of integral
elements automatically contains all topologically nilpotent elements. Following Wedhorn
Definition 7.14, Remark 7.15.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`IsRingOfIntegralElements`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AffinoidRings.lean#L42), [`IsAffinoidRing`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AffinoidRings.lean#L77) — sorry-free.
:::

:::definition "adic-spectrum"
Let $`(A, A^{+})` be an affinoid ring ({uses "affinoid-ring"}[]). The *adic spectrum*
$$`\mathrm{Spa}(A, A^{+}) = \{ v \in \mathrm{Cont}(A) : v(f) \le 1 \text{ for all } f \in A^{+} \}`
is the subspace of $`\mathrm{Cont}(A)` ({uses "continuous-valuation"}[]) of continuous valuations
bounded by $`1` on $`A^{+}`. Each point $`v` has a *support* prime $`\ker v = \{a : v(a) = 0\} \in
\mathrm{Spec}(A)`. The assignment $`(A, A^{+}) \mapsto \mathrm{Spa}(A, A^{+})` is the fundamental
functor of Huber's theory; its rational subsets are defined in {uses "rational-subsets"}[]. Following
Wedhorn Definition 7.23.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`Spa`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AdicSpectrum.lean#L110), [`PlusSubring`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AdicSpectrum.lean#L96) — sorry-free.
:::

:::theorem "spa-support-surjective"
*(Wedhorn Proposition 7.51.)* For an affinoid ring $`(A, A^{+})` ({uses "affinoid-ring"}[]), every
open maximal ideal $`\mathfrak{m}` of $`A` arises as the support of a point of
$`\mathrm{Spa}(A, A^{+})` ({uses "adic-spectrum"}[]): there is $`v \in \mathrm{Spa}(A, A^{+})` with
$`\ker v = \mathfrak{m}`.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`exists_mem_spa_supp_eq`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AdicSpectrum.lean#L157) — sorry-free.
:::

:::proof "spa-support-surjective"
That $`\mathrm{Spa}(A, A^{+})` carries the subspace topology from $`\mathrm{Spv}(A)`
({uses "valuation-spectrum"}[]) is immediate from its definition as a subspace of
$`\mathrm{Cont}(A)`. For the support statement, when $`\mathfrak{m}` is open the residue field
$`A/\mathfrak{m}` is a topological field on which the only continuous valuation is trivial; the
trivial valuation on $`A/\mathfrak{m}`, pulled back along $`A \twoheadrightarrow A/\mathfrak{m}`,
gives a continuous valuation on $`A` with support $`\mathfrak{m}` and value $`\le 1` on $`A^{+}`
(since $`A^{+}` maps into the valuation ring), hence a point of $`\mathrm{Spa}(A, A^{+})`. Openness of
$`\mathfrak{m}` holds in a Tate ring ({uses "tate-ring"}[]) because there the topologically nilpotent
elements, contained in every maximal ideal, are open.
:::

:::definition "rational-subsets"
Let $`X = \mathrm{Spa}(A, A^{+})` ({uses "adic-spectrum"}[]), $`T \subseteq A` a finite subset, and
$`s \in A`. The *rational subset*
$$`R(T/s) = \{ v \in X : v(t) \le v(s) \ne 0 \text{ for all } t \in T \}`
is open in $`X`. Rational subsets are stable under finite intersection — explicitly
$`R(T_1/s_1) \cap R(T_2/s_2) = R(T_1 T_2 / s_1 s_2)` — and form a basis for the topology of $`X`.
They are the building blocks of the structure sheaf. Following Wedhorn Definition 7.29, Remark 7.30,
Theorem 7.35(2).
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`rationalOpen`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AdicSpectrum.lean#L230), [`IsRationalSubset.inter`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/RationalSubsets.lean#L58) — sorry-free.
:::

:::theorem "spa-analytic"
*(Wedhorn Proposition 8.36.)* A point $`v \in \mathrm{Spv}(A)` is *analytic* if its support
$`\mathrm{supp}(v)` is not an open ideal of $`A`. If $`A` is a Tate ring ({uses "tate-ring"}[]), then
every point of $`\mathrm{Spv}(A)` ({uses "valuation-spectrum"}[]) is analytic; in particular every
point of the adic spectrum $`\mathrm{Spa}(A, A^{+})` ({uses "adic-spectrum"}[]) is analytic.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`IsAnalytic`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AnalyticPoints.lean#L40), [`IsTateRing.isAnalytic`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/AnalyticPoints.lean#L44) — sorry-free.
:::

:::proof "spa-analytic"
A point fails to be analytic exactly when its support is open. In a Tate ring there is a
topologically nilpotent unit $`u`; for any valuation point $`v`, since $`u` is a unit one has
$`v(u) \ne 0`, while $`u^{n} \to 0` forces $`v(u) < 1`. If the support $`\mathrm{supp}(v)` were open
it would contain a neighbourhood of $`0`, hence some power $`u^{n}`, making $`v(u^{n}) = 0` and so
$`v(u) = 0` — contradiction. Therefore $`\mathrm{supp}(v)` is never open, i.e. every point is
analytic. This is the content of `IsTateRing.isAnalytic`.
:::

:::theorem "spa-quasicompact"
*(Quasi-compactness of the adic spectrum.)* For a Tate affinoid ring $`(A, A^{+})` with
pseudo-uniformiser, the adic spectrum $`\mathrm{Spa}(A, A^{+})` ({uses "adic-spectrum"}[]) is
quasi-compact.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`isCompact_spa_of_tate_pseudouniformizer`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/SpaCompact.lean#L538), [`instCompactSpace_spa_of_tate_pseudouniformizer`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/SpaCompact.lean#L561) — sorry-free.
:::

:::proof "spa-quasicompact"
Unlike $`\mathrm{Spv}(A)`, the set $`\mathrm{Spa}(A, A^{+})` is not in general closed in
$`\mathrm{Spv}(A)`, so the naive "closed-in-compact" route fails. Instead the project embeds
$`\mathrm{Spv}(A)` into the compact Hausdorff space $`(A \times A \to \mathrm{Bool})` via the Huber
indicator $`\iota: v \mapsto \bigl((f,s) \mapsto [\,v(f) \le v(s) \ne 0\,]\bigr)`; the image of
$`\mathrm{Spv}(A)` is closed there (`ValuationSpectrumCompact`). Each integrality condition
$`v(a) \le 1` for $`a \in A^{+}` is a clopen coordinate condition, so $`\iota(\mathrm{Spa}(A, A^{+}))`
is the intersection of the closed image with clopen sets, hence closed and therefore compact;
transporting back through the embedding gives quasi-compactness of $`\mathrm{Spa}(A, A^{+})`. The Tate
pseudo-uniformiser is what supplies the discrete-on-value-groups input the embedding needs.
:::

# Tate algebras and the structure sheaf

:::definition "tate-algebra"
Let $`A` be a non-archimedean Tate ring ({uses "tate-ring"}[]) with pseudo-uniformiser $`\pi`. The
*Tate algebra in one variable*
$$`A\langle X \rangle = \Bigl\{ \sum_{n} a_n X^{n} : a_n \in A,\; a_n \to 0 \Bigr\}`
is the subring of $`A[[X]]` of restricted power series — those whose coefficients tend to $`0` along
the cofinite filter. For $`A = \mathbb{Q}_p` ({uses "padic-numbers"}[]) this is the ring of
convergent power series on the closed unit $`p`-adic disc. The bivariate version is $`A\langle X, Y
\rangle`, and the *Laurent Tate algebra* $`A\langle \zeta, \zeta^{-1} \rangle = A\langle X, Y
\rangle/(XY - 1)` inverts the variable. Following Wedhorn §6.9, §8.29–8.33.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`TateAlgebra`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/TateAlgebra.lean#L76), [`TateAlgebra₂`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/TateAlgebra.lean#L142), [`LaurentTateAlgebra`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/TateAlgebra.lean#L177) — sorry-free.
:::

:::theorem "sheafy-strongly-noetherian"
*(Wedhorn Theorem 8.28(b).)* Let $`(A, A^{+})` be a *strongly noetherian* Tate ring
({uses "tate-ring"}[]) — one for which all Tate algebras $`A\langle X_1, \dots, X_n \rangle`
({uses "tate-algebra"}[]) are noetherian — that is complete. Then the structure presheaf
$`\mathcal{O}_X` on $`X = \mathrm{Spa}(A, A^{+})` ({uses "adic-spectrum"}[]), with
$`\mathcal{O}_X(R(T/s)) = \widehat{A[s^{-1}]}` on rational subsets ({uses "rational-subsets"}[]), is a
*sheaf*, i.e. $`(A, A^{+})` is *sheafy*.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`isSheafy_of_stronglyNoetherian_828b`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Wedhorn828.lean#L2599) — in progress: the gluing condition ([`lemma_8_34_gluing`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Wedhorn828.lean#L2581)) and the algebraic separation ([`cor_8_32_productRestrictionSub_injective`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Wedhorn828.lean#L2515)) are established, but the topological inducing half of the embedding ([`cor_8_32_productRestrictionSub_isInducing`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Wedhorn828.lean#L2540)) still carries a `sorry`.
:::

:::proof "sheafy-strongly-noetherian"
In Lean, $`\mathrm{IsSheafy}\ A` is the pair of an *embedding* condition and a *gluing* condition on
every rational covering. The proof follows Wedhorn §8 top-down.

**Separation and the embedding.** By Corollary 8.32, the restriction map
$`\mathcal{O}_X(X) \to \prod_i \mathcal{O}_X(U_i)` over a rational covering is faithfully flat, hence
injective (`cor_8_32_productRestrictionSub_injective`); the topological strengthening to an
*embedding* additionally needs that this injection is inducing, the input from the Banach open-mapping
theorem (`BanachOMT`) — this last inducing step is the remaining `sorry`. Faithful flatness comes from
Lemma 8.31: the Tate algebra $`A\langle X \rangle` is faithfully flat over $`A` and the quotients
$`A\langle X\rangle/(f - X)`, $`A\langle X\rangle/(1 - fX)` are flat ({uses "tate-algebra"}[]), using
the strongly noetherian hypothesis to identify $`\mathcal{O}_X(U) = A\langle X\rangle/(\text{closed
ideal})` (Examples 6.38/6.39).

**Gluing.** For compatible sections over a rational cover, a global section is produced by Tate
acyclicity (`lemma_8_34_gluing`): the two-element Laurent cover $`\{R(f/1), R(1/f)\}` gives the exact
sequence
$$`0 \to A\langle X \rangle \to A\langle X \rangle \oplus A\langle X \rangle \to A\langle \zeta, \zeta^{-1} \rangle \to 0`
({uses "tate-algebra"}[]), Lemma 8.33; Wedhorn's refinement (Prop A.3) lifts acyclicity from Laurent
covers to all rational covers, and Prop A.4 packages acyclicity into the sheaf property.
:::

# Perfectoid rings and spaces

:::definition "perfectoid-ring"
Let $`p` be a prime and $`A` a complete, separated, uniform Tate ring ({uses "tate-ring"}[]) of
characteristic $`0`. Then $`A` is *perfectoid* (for $`p`) if there is a pseudo-uniformiser $`\varpi`
that is power-bounded, with
1. $`\varpi^{p} \mid p` in $`A^{\circ}` (i.e. $`p = c\,\varpi^{p}` for some power-bounded $`c`), and
2. the Frobenius $`x \mapsto x^{p}` surjective on $`A^{\circ}/p` (every power-bounded $`x` is
   $`y^{p} + p z` with $`y, z` power-bounded).

A *perfectoid field* is a perfectoid ring that is a field. The archetype is
$`\mathbb{C}_p` ({uses "padic-complex"}[]), perfectoid with pseudo-uniformiser a compatible system
$`p^{1/p^{\infty}}` of $`p`-power roots of $`p`. Following Scholze, *Perfectoid Spaces*,
Definition 3.5; this is the Scholze (Frobenius-on-$`A^\circ/p`) formulation.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`IsPerfectoidRing`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/PerfectoidRing.lean#L66), [`IsPerfectoidField`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/PerfectoidRing.lean#L106) — sorry-free (the definition).
:::

:::definition "perfectoid-space"
An *affinoid perfectoid space* is $`\mathrm{Spa}(A, A^{+})` ({uses "adic-spectrum"}[]) for a
perfectoid ring $`A` ({uses "perfectoid-ring"}[]). A *perfectoid space* is an adic space every point
of which has an open affinoid neighbourhood isomorphic to $`\mathrm{Spa}(A, A^{+})` for some
perfectoid ring $`A`. Following Scholze, *Perfectoid Spaces*, Definition 3.19.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`AffinoidPerfectoidSpace`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/PerfectoidSpace.lean#L44), [`IsPerfectoidSpace`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/PerfectoidSpace.lean#L97) — in progress (assembling an affinoid perfectoid space into an adic space, [`toAdicSpace`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/PerfectoidSpace.lean#L82), needs sheafiness of perfectoid rings and carries a `sorry`).
:::

# Witt vectors, tilting, and the Fargues–Fontaine curve

:::definition "witt-primitive"
Let $`k` be a perfect ring of characteristic $`p` and $`\mathbb{W}(k)` its ring of $`p`-typical Witt
vectors. An element $`\xi \in \mathbb{W}(k)` is *primitive of degree $`1`* (for a nonzerodivisor
$`\varpi \in k`) if
$$`\xi = p + [\varpi]\cdot\alpha, \qquad \alpha \in \mathbb{W}(k),`
where $`[\,\cdot\,]` is the Teichmüller lift. A primitive element has nonzero $`0`-th coordinate, is
nonzero, and does not lie in $`(p)`. These elements generate the kernels of Fontaine's period maps.
Following Scholze–Weinstein, *Berkeley Lectures*, Definitions 6.2.9–6.2.10.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`WittVector.IsPrimitive`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/WittVectorPrimitive.lean#L52), [`WittVector.IsPrimitive.not_mem_span_p_of`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/WittVectorPrimitive.lean#L89) — sorry-free.
:::

:::theorem "witt-ker-principal"
*(Scholze–Weinstein, Berkeley Lectures, Lemma 6.2.8.)* Let $`\theta : \mathbb{W}(k) \to R` be a ring
homomorphism and $`\xi \in \ker\theta` a primitive element of degree $`1` ({uses "witt-primitive"}[]).
Suppose every kernel element divides into a $`\xi`-part and a $`p`-part staying in the kernel: for
each $`x \in \ker\theta` there are $`q, r` with $`x = \xi q + p r` and $`r \in \ker\theta`. Then the
kernel is generated by $`\xi`: every $`x \in \ker\theta` is
$$`x = \xi\, q \qquad \text{for some } q \in \mathbb{W}(k),`
so $`\ker\theta = (\xi)`.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`WittVector.ker_of_primitive_and_division`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/WittVectorPrimitive.lean#L207) — sorry-free.
:::

:::proof "witt-ker-principal"
Iterate the division hypothesis. Starting from $`r_0 = x`, each step writes $`r_n = \xi\,q_n + p\,r_{n+1}`
with $`r_{n+1} \in \ker\theta`, so after $`N` steps
$$`x = \xi\Bigl(\sum_{n < N} q_n\,p^{n}\Bigr) + p^{N} r_N.`
Since $`r_N \in \ker\theta`, the remainder $`p^{N} r_N` lies in $`(p^{N})`, so the partial sums
approximate $`x` to ever-higher $`p`-adic order. By $`p`-adic completeness and Hausdorffness of
$`\mathbb{W}(k)` (the ideal $`(p)` is adically complete), the partial sums $`\sum_{n<N} q_n p^{n}`
converge to a limit $`q` with $`x = \xi\,q`. Primitivity of $`\xi` ({uses "witt-primitive"}[]) — its
$`0`-th coordinate is a unit and $`\xi \notin (p)` — is what makes the division at each step well-posed.
This is the algebraic core of Berkeley Lectures Lemma 6.2.8, and is exactly the recursion the
formalised proof carries out.
:::

:::definition "tilt"
Let $`A` be a perfectoid ring ({uses "perfectoid-ring"}[]) for $`p`. Its *tilt* is the perfection
$$`A^{\flat} = \varprojlim_{x \mapsto x^{p}} A^{\circ}/(p),`
a perfect ring of characteristic $`p`. The associated period ring is $`A_{\inf} = \mathbb{W}(A^{\flat})`,
the $`p`-typical Witt vectors of the tilt, and *Fontaine's theta map* is the canonical surjection
$$`\theta : A_{\inf} \twoheadrightarrow A^{\circ}`
whose kernel is principal, generated by a primitive element of degree $`1`
({uses "witt-primitive"}[]). For a perfectoid *field* the tilt is again a perfectoid field, and
tilting is an equivalence of categories. Following Scholze, *Perfectoid Spaces*, §3.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`PerfectoidRing.tilt`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Tilting.lean#L91), [`PerfectoidRing.theta`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Tilting.lean#L213) — in progress (surjectivity of theta, [`theta_surjective`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Tilting.lean#L246), and principality of its kernel, [`ker_theta_principal`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/Tilting.lean#L429), still rest on `sorry`s).
:::

:::definition "fargues-fontaine-curve"
Fix a perfectoid field $`E` of characteristic $`p` with ring of integers $`\mathcal{O}_E` and
pseudo-uniformiser $`\pi`. The *adic Fargues–Fontaine curve* is built from the Witt vectors
$`\mathbb{W}(\mathcal{O}_E)` ({uses "witt-primitive"}[]): one forms the pre-curve
$$`Y_{FF} = \mathrm{Spa}\bigl(\mathbb{W}(\mathcal{O}_E), \mathbb{W}(\mathcal{O}_E)\bigr) \setminus V(p, [\pi]),`
the locus where $`p` and the Teichmüller lift $`[\pi]` do not simultaneously vanish
({uses "adic-spectrum"}[]), and quotients by the Frobenius action $`\varphi^{\mathbb{Z}}`:
$$`X_{FF} = Y_{FF}/\varphi^{\mathbb{Z}}.`
Following Fargues–Fontaine. The expected geometry — $`X_{FF}` noetherian, regular, of Krull dimension
$`1`, with classical points the untilts of $`E` up to Frobenius — is stated but not yet proved.
Formalised in [`Adic-Spaces`](https://github.com/CBirkbeck/Adic-Spaces): [`FarguesFontaine.Y_FF`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/FarguesFontaine.lean#L219), [`FarguesFontaine.X_FF`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/FarguesFontaine.lean#L337) — in progress (the curve is constructed, but its properties [`X_FF.dim_one`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/FarguesFontaine.lean#L401) and [`X_FF.classicalPoints`](https://github.com/CBirkbeck/Adic-Spaces/blob/fb55cd85e70cc7bf5f968b9b06197dc01d4b89fd/Adic%20spaces/FarguesFontaine.lean#L416) are `sorry`).
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib pull
requests (the `t-number-theory` queue). Each carries a `pr_url` pointing at the live PR and **no**
`(lean := …)` reference: the declarations are not yet in mathlib v4.30.0-rc2. They connect into the
dependency graph through the Mathlib-backed $`p`-adic nodes of this chapter via `{uses}` edges, and
should be re-pointed to `(lean := …)` once the corresponding PR merges.

:::theorem "amice-transform" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/23772")
*(Amice transform / Amice equivalence.)* The *Amice transform* sends a $`p`-adic measure $`\mu` on
$`\mathbb{Z}_p` ({uses "padic-integers"}[]) — equivalently a bounded $`\mathbb{Q}_p`-valued
distribution — to the power series
$$`A_\mu(T) \;=\; \int_{\mathbb{Z}_p} (1 + T)^{x}\, d\mu(x) \;=\; \sum_{n \ge 0} \left(\int_{\mathbb{Z}_p} \binom{x}{n}\, d\mu(x)\right) T^{n},`
whose coefficients are exactly the moments of $`\mu` against the Mahler basis ({uses "mahler-basis"}[]).
The Amice equivalence is the resulting isomorphism of $`\mathbb{Q}_p`-Banach algebras
({uses "padic-numbers"}[])
$$`\mathcal{M}(\mathbb{Z}_p, \mathbb{Q}_p) \;\xrightarrow{\;\sim\;}\; \mathbb{Q}_p\langle\langle T \rangle\rangle^{b}`
between measures on $`\mathbb{Z}_p` and bounded power series, under which convolution corresponds to
multiplication.

PR #23772 (with companion #23791) constructs the Amice transform and proves it an isomorphism, the
analytic foundation for $`p`-adic $`L`-functions and Iwasawa theory; it builds directly on Mahler's
theorem ({uses "mahler-theorem"}[]).
In review — [mathlib PR #23772](https://github.com/leanprover-community/mathlib4/pull/23772).
:::
