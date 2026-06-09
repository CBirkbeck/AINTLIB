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

# Adic spaces (beyond mathlib)

The constructions above — valuations, the $`p`-adic numbers,
and the DVR structure of $`\mathbb{Z}_p` —
are the arithmetic building blocks for Huber's theory of *adic spaces*, which provides the
correct foundations for $`p`-adic geometry and perfectoid spaces. Adic spaces proper are not
yet formalised in mathlib; they are scheduled for Phase 3 of the AINTLIB project, drawing on
the `Condensed` and `LiquidTensor` work.
