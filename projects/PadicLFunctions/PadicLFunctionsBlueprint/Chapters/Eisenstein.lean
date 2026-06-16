import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The p-adic family of Eisenstein series" =>

We close Part I with a brief detour illustrating a second flavour of $`p`-adic
variation in number theory: the $`p`-adic variation of *modular forms*. Almost all
the work has already been done. In building the Kubota–Leopoldt $`p`-adic
$`L`-function we constructed a pseudo-measure $`\zeta_p` on $`\Zpx` interpolating
the values $`\zeta(1-k)`; we will now see that these values are exactly the
constant terms of a family of Eisenstein series, and that the *remaining* Fourier
coefficients of that family are far easier to interpolate. Assembling the two
gives a single power series — a $`\Lam`-adic modular form — whose specialisations
are honest modular forms.

Throughout, $`p` is a fixed prime, $`\uhp = \set{z \in \C : \mathrm{Im}(z) > 0}`
is the upper half-plane and $`q = e^{2\pi i z}`.

# Eisenstein series and their q-expansions

:::definition "eis-series" (lean := "ModularForm.E, EisensteinSeries.q_expansion_bernoulli, PadicLFunctions.rjwEisenstein")
For an even integer $`k \geq 4`, the *Eisenstein series of weight $`k`* is the
holomorphic function on $`\uhp` given by
$$`G_k(z) := \sum_{\substack{c,d \in \Z \\ (c,d) \neq (0,0)}} \frac{1}{(cz+d)^k}.`
It is a modular form of weight $`k` for $`\mathrm{SL}_2(\Z)`, and may be viewed as
a two-dimensional analogue of the zeta value $`\zeta(k)`. Its normalisation
$$`E_k(z) := \frac{(k-1)!}{2\,(2\pi i)^k}\, G_k(z)`
has the rational $`q`-expansion
$$`E_k(z) = \frac{\zeta(1-k)}{2} + \sum_{n \geq 1} \sigma_{k-1}(n)\, q^n,
\qquad \sigma_{k-1}(n) = \sum_{0 < d \mid n} d^{k-1}.`
The constant term is the special value {uses "special-values-zeta"}[]
$`\zeta(1-k) = -B_k/k`.

Mathlib already provides the level-1 Eisenstein series and its q-expansion
(`ModularForm.E`, normalised with constant term $`1`, and
`EisensteinSeries.q_expansion_bernoulli` giving
$`E = 1 - (2k/B_k)\sum \sigma_{k-1}(n)q^n`); the notes' normalisation is the
rescale `rjwEisenstein` $`= (\zeta(1-k)/2)\cdot E`, under which the
$`n`-th coefficient becomes exactly $`\sigma_{k-1}(n)`.
:::

The constant term $`\zeta(1-k)/2` is precisely the special value interpolated by
$`\zeta_p`. The shape of the $`q`-expansion already tells us what is left to do:
interpolate the divisor sums $`\sigma_{k-1}(n)`, which only requires interpolating
the power maps $`k \mapsto d^{k}`.

:::proposition "eis-dirac-interpolation" (lean := "PadicLFunctions.unitOfNat_coe, PadicLFunctions.divisorMeasure_moment")
Let $`d` be an integer coprime to $`p`. Then the Dirac measure
$`\delta_d \in \Lam(\Zpx)` at $`d`, i.e.\ evaluation at $`d`, interpolates the
power map: for every $`k \in \Z`,
$$`\int_{\Zpx} x^{k} \cdot \delta_d = d^{k}.`
This rests on {uses "iwasawa-algebra"}[].

Formalised at natural exponents and directly in the summed form the family
needs: `divisorMeasure_moment` evaluates the divisor-sum measure
$`A_n = \sum_{p\nmid d\mid n}\delta_d` against $`x^k` to
$`\sigma^p_k(n)`; the single-Dirac case is its $`n`-prime instance, with
`unitOfNat_coe` realising "viewing $`d` as an element of $`\Zpx`".
:::

:::proof "eis-dirac-interpolation"
Because $`d` is coprime to $`p` it is a unit, hence a genuine point of $`\Zpx`. The
Dirac measure $`\delta_d` is by definition the point mass at $`d`, so integration
against it is evaluation: $`\int_{\Zpx} f \cdot \delta_d = f(d)` for every
continuous $`f`. Taking $`f` to be the character $`x \mapsto x^{k}` gives
$`\int_{\Zpx} x^{k} \cdot \delta_d = d^{k}`. The identity holds for every
$`k \in \Z` since $`x \mapsto x^k` is a continuous (indeed locally analytic)
function on $`\Zpx` for all integer exponents, including negative ones — exactly
the contrast with $`k \mapsto p^k`, where no such point exists.
:::

:::proposition "eis-no-measure-at-p" (lean := "PadicLFunctions.noMeasure_interpolates_pPow")
The power map $`k \mapsto p^{k}` *cannot* be $`p`-adically interpolated by a measure
on $`\Zpx`: there is no $`p`-adic measure {uses "p-adic-measure"}[] $`\theta_p` on
$`\Zpx` with $`\int_{\Zpx} x^{k} \cdot \theta_p = p^{k}` for all $`k`.

The Lean proof replaces the notes' sequential-limit gloss with a single
finitary congruence level: with $`K = 1 + \varphi(p^2)`, the uniform Euler
congruence $`x^K \equiv x \bmod p^2` on $`\Zpx` forces
$`|p^K - p| \le p^{-2}`, which is absurd. Notably $`p = 2` is allowed.
:::

:::proof "eis-no-measure-at-p"
The obstruction is twofold. First, $`p \notin \Zpx`, so there is no Dirac measure
at $`p`. More fundamentally, suppose such a $`\theta_p` existed and pick a strictly
increasing sequence of integers $`k_n` converging $`p`-adically to a limit $`k`.
Integration against a measure is continuous in the character, so
$`p^{k_n} = \int_{\Zpx} x^{k_n} \cdot \theta_p \to \int_{\Zpx} x^{k} \cdot
\theta_p = p^{k}`. But $`\val_p(p^{k_n}) = k_n \to \infty`, so $`p^{k_n} \to 0`
in $`\Cp`, forcing $`p^k = 0`, a contradiction. The map $`k \mapsto p^k` simply
behaves too badly to be continuous.
:::

# p-stabilisation

The way around the obstruction is classical: pass to the *$`p`-stabilisation*,
which removes the divisors of $`n` that are divisible by $`p` and lowers the level
to $`\Gamma_0(p)`.

:::definition "eis-p-stabilisation" (lean := "PadicLFunctions.sigmaP, PadicLFunctions.stabilisedCoeff, PadicLFunctions.hasSum_stabilisedEisenstein, PadicLFunctions.stabilisedEisenstein, PadicLFunctions.stabilisedEisenstein_apply")
The *$`p`-stabilisation* of $`E_k` is
$$`E_k^{(p)}(z) := E_k(z) - p^{k-1} E_k(pz).`
Its $`q`-expansion is
$$`E_k^{(p)}(z) = \frac{(1 - p^{k-1})\,\zeta(1-k)}{2} + \sum_{n \geq 1}
\sigma_{k-1}^{p}(n)\, q^n, \qquad
\sigma_{k-1}^{p}(n) = \sum_{\substack{0 < d \mid n \\ p \nmid d}} d^{k-1}.`
It is a modular form of weight $`k` and level
$`\Gamma_0(p) = \set{\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)
\in \mathrm{SL}_2(\Z) : p \mid c}`. This depends on {uses "eis-series"}[].

Fully formalised: the rational coefficient sequence is `stabilisedCoeff`,
the q-expansion is the convergence statement `hasSum_stabilisedEisenstein`,
and the $`\Gamma_0(p)`-modularity — the "Note" of the source, given there
without proof — is the genuine `ModularForm ((Gamma0 p).map (mapGL ℝ)) k`
`stabilisedEisenstein`, built on the level-raising operator
$`\iota_p f = f(p\,\cdot)` of the LeanModularForms strong-multiplicity-one
project (Miyake §4.6, Lemma 4.6.1).
:::

:::proof "eis-p-stabilisation"
Substituting $`q \mapsto q^p` (i.e.\ $`z \mapsto pz`) into the $`q`-expansion of
$`E_k` and forming $`E_k - p^{k-1} E_k(p\,\cdot)` multiplies the $`n`-th
coefficient of the second copy by $`p^{k-1}`. On the constant term this produces
the Euler factor $`1 - p^{k-1}`. On the coefficient of $`q^n` it subtracts
$`p^{k-1}\sigma_{k-1}(n/p)` (when $`p \mid n`) from $`\sigma_{k-1}(n)`; since
$`p^{k-1} d^{k-1} = (pd)^{k-1}`, this cancels exactly the divisors of $`n` that
are divisible by $`p`, leaving the $`p`-restricted divisor sum
$`\sigma_{k-1}^{p}(n)`. The constant term is now the Euler-factor-twisted value
$`(1 - p^{k-1})\zeta(1-k)/2` — precisely the quantity interpolated by $`\zeta_p`.
:::

The crucial gain is that $`\sigma_{k-1}^{p}(n)` involves only divisors *coprime to
$`p`*, so it is built entirely from the well-behaved power maps $`k \mapsto d^{k}`
with $`p \nmid d`, which Dirac measures interpolate.

# The Lambda-adic family

We can now assemble the family. The constant term is interpolated by $`\zeta_p`
(after a shift in the variable), and each non-constant coefficient by a finite sum
of Dirac measures.

:::theorem "p-adic-eisenstein-family" (lean := "PadicLFunctions.eisensteinFamily, PadicLFunctions.eisensteinFamily_interpolation, PadicLFunctions.unitsTwist, PadicLFunctions.twistedZetaHalf, PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure, PadicLFunctions.twistedZetaHalf_moments")
There exists a power series
$$`\mathbf{E}(z) = \sum_{n \geq 0} A_n\, q^n \in Q(\Zpx)[\![q]\!]`
with coefficients in the fraction ring $`Q(\Zpx)` of the Iwasawa algebra, such
that:

* the constant term $`A_0` is a pseudo-measure and $`A_n \in \Lam(\Zpx)` is a
  genuine measure for all $`n \geq 1`;
* for every even $`k \geq 4`, integrating coefficient-by-coefficient against
  $`x^{k-1}` recovers the $`p`-stabilised Eisenstein series:
$$`\int_{\Zpx} x^{k-1} \cdot \mathbf{E}(z) := \sum_{n \geq 0}
\Big( \int_{\Zpx} x^{k-1} \cdot A_n \Big) q^n = E_k^{(p)}(z).`

This rests on {uses "eis-p-stabilisation"}[], {uses "eis-dirac-interpolation"}[],
{uses "kubota-leopoldt"}[], {uses "interpolation-property"}[] and
{uses "pseudo-measure"}[].

**Erratum (errata.md #11).** As stated in the notes, "(a) $`A_0` is a
pseudo-measure" fails for the notes' own Definition 3.34: the
$`x`-twist moves the pole of $`\zeta_p` from the trivial character to the
character $`x^{-1}`, so $`([g]-[1])\,x\zeta_p \notin \Lam` for $`g \neq 1`.
The formalisation realises the $`x`-twist as a ring automorphism
`unitsTwist` of $`\Lam(\Zpx)` (extended to $`Q(\Zpx)`), defines
$`A_0 = x\zeta_p/2` as `twistedZetaHalf`, and proves the corrected claim
$`(g[g]-[1])A_0 \in \Lam(\Zpx)` for all $`g`
(`twistedZetaHalf_isTwistedPseudoMeasure`), together with the moment
interpolation in the same witness encoding as $`\zeta_p`'s
(`twistedZetaHalf_moments`). The full coefficientwise display is
`eisensteinFamily_interpolation`, whose target coefficients tie to the
complex $`E_k^{(p)}` through `stabilisedCoeff` and
`hasSum_stabilisedEisenstein`; evenness of $`k` enters only on that complex
side.
:::

:::proof "p-adic-eisenstein-family"
Define the coefficient measures explicitly. For the non-constant terms set
$$`A_n = \sum_{\substack{0 < d \mid n \\ p \nmid d}} \delta_d \in \Lam(\Zpx)
\qquad (n \geq 1),`
a finite sum of Dirac measures at units, hence a genuine measure. For the constant
term take the pseudo-measure $`A_0 = x\,\zeta_p / 2`, i.e.\ $`\zeta_p` shifted by
one in the variable (in the opposite direction to the shift used when constructing
$`\zeta_p`), so that integrating $`x^{k-1}` against $`A_0` is integrating $`x^{k}`
against $`\zeta_p/2`.

For the interpolation, the non-constant coefficients follow from
{bpref "eis-dirac-interpolation"}[]:
$$`\int_{\Zpx} x^{k-1} \cdot A_n = \sum_{\substack{0 < d \mid n \\ p \nmid d}}
\int_{\Zpx} x^{k-1} \cdot \delta_d = \sum_{\substack{0 < d \mid n \\ p \nmid d}}
d^{k-1} = \sigma_{k-1}^{p}(n),`
which is exactly the $`q^n`-coefficient of $`E_k^{(p)}`. For the constant term, the
interpolation property of $`\zeta_p` gives
$`\int_{\Zpx} x^{k-1} \cdot A_0 = \tfrac{1}{2}\int_{\Zpx} x^{k} \cdot \zeta_p =
\tfrac{1}{2}(1 - p^{k-1})\zeta(1-k)`, matching the constant term of $`E_k^{(p)}`
computed in {bpref "eis-p-stabilisation"}[]. Coefficient-by-coefficient the two
power series agree, proving the claim.
:::

# Lambda-adic modular forms and weight space

The series $`\mathbf{E}` is the prototypical example of a *$`\Lam`-adic modular
form*. Informally it says: Eisenstein series vary $`p`-adically continuously in
the weight — if $`k` and $`k'` are close $`p`-adically then the $`q`-expansions of
$`E_k` and $`E_{k'}` are close $`p`-adically. This point of view originates with
Serre, who used $`p`-adic families of Eisenstein series to give a new construction
of the $`p`-adic zeta function of a totally real field: if one can interpolate all
the *non-constant* coefficients — which, as we have just seen, is easy — then one
automatically interpolates the *constant* term, namely the $`p`-adic zeta
function, which is far harder to interpolate directly.

These results are often phrased over the *weight space* $`\cW`, the rigid analytic
space whose $`\Cp`-points parametrise continuous characters of $`\Zpx`. The
integers embed via $`\kappa_k : x \mapsto x^k`, and $`k \equiv k' \pmod{p-1}` iff
$`\kappa_k` and $`\kappa_{k'}` lie in the same connected unit ball. Writing
$`\cO^+(\cW)` for the bounded rigid analytic functions on $`\cW` (which correspond
to measures on $`\Zpx`) and $`Q(\cW)` for the rigid meromorphic functions with at
worst a simple pole at the trivial character (corresponding to pseudo-measures),
one rewrites $`\mathbf{E} = \sum_{n \geq 0} B_n q^n \in Q(\cW)[\![q]\!]` with
$`B_n \in \cO^+(\cW)` for $`n > 0`, satisfying
$`\mathbf{E}(\kappa_k) = E_k^{(p)}` for all even $`k \geq 4`. Thus $`\mathbf{E}` is
literally a $`p`-adic interpolation of the Eisenstein series across weight space.

Pioneering work of Hida pushed this much further, producing analogous *Hida
families* for far more general modular forms; these were in turn generalised to
Coleman families and eigenvarieties, parametrising the $`p`-adic variation of
modular and automorphic forms over weight space. Such families are central to the
modern construction and study of $`p`-adic $`L`-functions, foreshadowing the
$`\mathrm{GL}(2)` picture taken up in Part II.
