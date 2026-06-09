import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Diophantine Equations and Transcendence" =>

This chapter covers four interlocking strands of the theory of Diophantine equations and
transcendence, as they are formalised in mathlib: the ring $`\mathbb{Z}[\sqrt{d}]` and its norm
form; Pell's equation $`x^2 - dy^2 = 1`, its solution group and fundamental solution, the recursive
Pell sequences of Matiyasevich's theorem, and the resulting Diophantine definition of the power
function (the last ingredient of the negative solution to Hilbert's tenth problem); generalised
continued fractions, their convergents, the determinant formula, and their convergence to a real
number, together with Dirichlet's approximation theorem and Legendre's converse; and the theory of
transcendence — algebraic versus transcendental elements, Liouville's theorem that every Liouville
number is transcendental, and the transcendence of the Liouville constants. Throughout, $`d`
denotes an integer (positive and non-square where Pell's equation is at issue), $`\mathbb{Z}` the
integers, $`\mathbb{Q}` the rationals, and $`\mathbb{R}` the reals. Every mathlib-backed node carries
a `(lean := …)` reference naming the exact declaration, and its proof sketch follows the argument
that declaration actually uses, naming the lemmas that proof invokes. The Newton polygon theory of
$`p`-adic power series, formalised in the external `NewtonPolys` project, is recorded as a family of
informal nodes at the end of the chapter. The Gelfond–Schneider theorem is the subject of an open
mathlib pull request and is blueprinted informally as forthcoming.

# The ring of integers of a real quadratic field and its norm

## The ring of quadratic integers
:::definition "zsqrtd" (lean := "Zsqrtd")
For an integer $`d`, the *ring $`\mathbb{Z}[\sqrt{d}]`* (written $`\mathbb{Z}\sqrt{d}` or `ℤ√d` in
Lean) consists of formal expressions $`a + b\sqrt{d}` with $`a, b \in \mathbb{Z}`. Addition and
multiplication are defined componentwise by
$$`(a + b\sqrt{d}) + (a' + b'\sqrt{d}) = (a + a') + (b + b')\sqrt{d},`
$$`(a + b\sqrt{d})(a' + b'\sqrt{d}) = (aa' + dbb') + (ab' + ba')\sqrt{d}.`
The components $`a` and $`b` are the *real part* (`.re`) and the *imaginary part* (`.im`). For $`d` a
non-square with $`d \equiv 2, 3 \pmod 4`, this is exactly the ring of integers
({uses "ring-of-integers"}[]) of the real quadratic field $`\mathbb{Q}(\sqrt{d})`; the conjugation
$`a + b\sqrt{d} \mapsto a - b\sqrt{d}` is the `star` operation, making $`\mathbb{Z}[\sqrt{d}]` a
`StarRing`.
:::

## The norm on quadratic integers
:::definition "zsqrtd-norm" (lean := "Zsqrtd.norm")
The *norm* of an element $`\alpha = a + b\sqrt{d} \in \mathbb{Z}[\sqrt{d}]` ({uses "zsqrtd"}[]) is the
integer
$$`N(\alpha) \coloneqq a\cdot a - d\, b\cdot b = a^2 - d\,b^2,`
computed in Lean from the real and imaginary parts as `n.re * n.re - d * n.im * n.im`. It is the
product $`\alpha\,\bar\alpha` of $`\alpha` with its conjugate, cast back to $`\mathbb{Z}`.
:::

## Norm as Product with Conjugate
:::lemma_ "zsqrtd-norm-conj" (lean := "Zsqrtd.norm_eq_mul_conj")
The norm of $`\alpha \in \mathbb{Z}[\sqrt{d}]` is the product of $`\alpha` with its conjugate: as
elements of $`\mathbb{Z}[\sqrt{d}]`,
$$`(N(\alpha) : \mathbb{Z}[\sqrt{d}]) = \alpha \cdot \overline{\alpha},`
where $`\overline{\alpha} = \texttt{star}\,\alpha` is the conjugate ({uses "zsqrtd-norm"}[]).
:::

:::proof "zsqrtd-norm-conj"
Expand both sides on the real and imaginary parts (`Zsqrtd.ext_iff`): the product
$`(a + b\sqrt d)(a - b\sqrt d)` has real part $`a^2 - db^2` and imaginary part $`ab - ba = 0`, which is
the cast of $`N(\alpha)` into $`\mathbb{Z}[\sqrt{d}]`. mathlib's `norm_eq_mul_conj` discharges this by
`ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]` ({uses "zsqrtd"}[]).
:::

## Multiplicativity of the Norm
:::lemma_ "zsqrtd-norm-mul" (lean := "Zsqrtd.norm_mul")
The norm is multiplicative: for all $`\alpha, \beta \in \mathbb{Z}[\sqrt{d}]`,
$$`N(\alpha\beta) = N(\alpha)\, N(\beta).`
Equivalently, `Zsqrtd.normMonoidHom : ℤ√d →* ℤ` is a monoid homomorphism.
:::

:::proof "zsqrtd-norm-mul"
A direct computation. Unfolding the norm ({uses "zsqrtd-norm"}[]) and the real and imaginary parts of
a product (`re_mul`, `im_mul`, {uses "zsqrtd"}[]) turns the claim into the polynomial identity
$$`(aa' + dbb')^2 - d(ab' + ba')^2 = (a^2 - db^2)(a'^2 - db'^2),`
the Brahmagupta–Fibonacci identity, closed by `ring`. mathlib's proof is exactly
`simp only [norm, im_mul, re_mul]; ring`; the homomorphism `normMonoidHom` packages this together with
$`N(1) = 1`.
:::

## Norm One Iff Unitary
:::lemma_ "zsqrtd-norm-unitary" (lean := "Zsqrtd.norm_eq_one_iff_mem_unitary")
An element $`\alpha \in \mathbb{Z}[\sqrt{d}]` has norm $`1` if and only if it is *unitary*, i.e.
$`\alpha\,\overline{\alpha} = 1`:
$$`N(\alpha) = 1 \iff \alpha \in \mathrm{unitary}\bigl(\mathbb{Z}[\sqrt{d}]\bigr).`
:::

:::proof "zsqrtd-norm-unitary"
By the conjugate formula ({uses "zsqrtd-norm-conj"}[]), $`(N(\alpha) : \mathbb{Z}[\sqrt{d}]) =
\alpha\,\overline{\alpha}`, and since the conjugation is a star operation fixing $`\mathbb{Z}`, the
condition $`\alpha\,\overline{\alpha} = 1 = \overline{\alpha}\,\alpha` is precisely membership in the
unitary submonoid. As the integer cast into $`\mathbb{Z}[\sqrt{d}]` is injective, $`N(\alpha) = 1`
($`\mathbb{Z}`) is equivalent to $`(N(\alpha) : \mathbb{Z}[\sqrt{d}]) = 1`, hence to unitarity. This
identification is the bridge by which a Pell solution becomes a norm-one element of
$`\mathbb{Z}[\sqrt{d}]`.
:::

# Generalised continued fractions and their convergents

## Generalised Continued Fractions
:::definition "gcf" (lean := "GenContFract")
A *generalised continued fraction* over a type $`\alpha` is an expression
$$`h + \cfrac{a_0}{b_0 + \cfrac{a_1}{b_1 + \cfrac{a_2}{b_2 + \cdots}}}`
with *head term* $`h \in \alpha` and a (possibly infinite) `Stream'.Seq` of *partial
numerator–denominator pairs* $`(a_i, b_i)`. It is a *simple continued fraction* (`SimpContFract`,
{uses "gcf"}[]) when every partial numerator $`a_i = 1`, and a *(regular) continued fraction*
(`ContFract`) when additionally every partial denominator $`b_i > 0`. The continued fraction
*terminates at $`n`* (`TerminatedAt`) if the sequence of pairs has run out by index $`n`.
:::

## Convergents of a Continued Fraction
:::definition "gcf-convergents" (lean := "GenContFract.convs")
The *$`n`-th convergent* $`A_n/B_n` of a generalised continued fraction ({uses "gcf"}[]) is computed
from the *continuants* $`(A_n, B_n)` — the numerator (`nums`) and denominator (`dens`) — via the
three-term recurrence
$$`A_{-1} = 1,\quad A_0 = h,\quad A_n = b_{n-1}A_{n-1} + a_{n-1}A_{n-2},`
$$`B_{-1} = 0,\quad B_0 = 1,\quad B_n = b_{n-1}B_{n-1} + a_{n-1}B_{n-2},`
and the $`n`-th convergent is $`\mathrm{convs}(n) = A_n / B_n`. mathlib stores the continuant pairs
as the stream `contsAux`, with `conts`, `nums`, `dens`, and `convs` derived from it; the alternative
`convs'` evaluates the truncated fraction directly, and the two agree.
:::

## Determinant Formula for Continuants
:::theorem "cf-determinant" (lean := "SimpContFract.determinant")
*(Determinant formula.)* For a simple continued fraction ({uses "gcf"}[]) that does not terminate at
$`n`, the consecutive continuants ({uses "gcf-convergents"}[]) satisfy
$$`A_n\,B_{n+1} - B_n\,A_{n+1} = (-1)^{n+1}.`
Consequently the consecutive convergents $`A_n/B_n` and $`A_{n+1}/B_{n+1}` differ by
$`(-1)^{n+1}/(B_n B_{n+1})`.
:::

:::proof "cf-determinant"
By induction on $`n`, via the auxiliary statement `determinant_aux` on the continuant stream
`contsAux`. The base case $`n = 0` is computed directly from `contsAux`. For the inductive step,
the continuant recurrence (`contsAux_recurrence`, {uses "gcf-convergents"}[]) is unfolded once at the
nonterminating index $`n` (the pair $`(a_n, b_n)` exists because $`\neg\mathrm{TerminatedAt}\,n`);
using that the simple continued fraction has $`a_n = 1` (the `SimpContFract` property), the goal
$`pA(ppB + b_n\,pB) - pB(ppA + b_n\,pA) = (-1)^{n+1}` reduces by `ring` to $`ppA\cdot pB - ppB\cdot pA
= (-1)^n`, which is the induction hypothesis (carried back across the nonterminating index by
`terminated_stable`).
:::

## Convergence of Continued Fractions
:::theorem "cf-convergence" (lean := "GenContFract.of_convergence")
*(Convergence of the continued fraction expansion.)* Let $`v` lie in a linearly ordered, Archimedean
field with order topology. The convergents of the regular continued fraction expansion
$`\mathrm{of}\,v` of $`v` converge to $`v`:
$$`\lim_{n \to \infty} (\mathrm{of}\,v).\mathrm{convs}(n) = v.`
:::

:::proof "cf-convergence"
The metric form `of_convergence_epsilon` does the work; `of_convergence` repackages it as a
`Filter.Tendsto` statement. Given $`\varepsilon > 0`, the Archimedean property (`exists_nat_gt`)
produces $`N'` with $`1/\varepsilon < N'`; set $`N = \max(N', 5)`. For $`n \ge N`: if the expansion
terminates at $`n` then $`v = \mathrm{convs}(n)` exactly (`of_correctness_of_terminatedAt`); otherwise
the determinant formula ({uses "cf-determinant"}[]) yields $`|v - \mathrm{convs}(n)| \le
1/(B_n B_{n+1})` (`abs_sub_convs_le`), and the denominators are bounded below by Fibonacci numbers,
$`\mathrm{fib}(n+1) \le B_n` and $`\mathrm{fib}(n+2) \le B_{n+1}` (`succ_nth_fib_le_of_nth_den`).
Since $`n \le \mathrm{fib}(n)` for $`n \ge 5` (`le_fib_self`), the product $`B_n B_{n+1}` exceeds
$`N' > 1/\varepsilon`, forcing $`1/(B_n B_{n+1}) < \varepsilon`.
:::

# Dirichlet's approximation theorem and Legendre's converse

## Dirichlet's Approximation Theorem
:::theorem "dirichlet-approx" (lean := "Real.exists_int_int_abs_mul_sub_le")
*(Dirichlet's approximation theorem.)* For any real number $`\xi` and any positive integer $`n`,
there exist integers $`j` and $`k` with $`0 < k \le n` such that
$$`|k\xi - j| \le \frac{1}{n+1}.`
Equivalently, there is a rational $`j/k` with $`|\xi - j/k| \le 1/(k(n+1))`.
:::

:::proof "dirichlet-approx"
The proof is the pigeonhole on fractional parts in mathlib's exact form. Consider the map
$`f(m) = \lfloor \mathrm{fract}(\xi m)\cdot(n+1)\rfloor`, which sends each integer $`m` into
$`\{0, 1, \ldots, n\}`. Two cases. If some $`m \in \{0, \ldots, n\}` has $`f(m) = n`, then
$`\mathrm{fract}(\xi m)` is within $`1/(n+1)` of $`1`, and $`(\lfloor\xi m\rfloor + 1, m)` gives the
bound directly. Otherwise $`f` maps the $`n+1` points of $`\{0,\ldots,n\}` into the $`n` values
$`\{0,\ldots,n-1\}`, so by pigeonhole (`exists_ne_map_eq_of_card_lt_of_maps_to`) two distinct $`x < y`
collide, $`f(x) = f(y)`; then $`k = y - x` and $`j = \lfloor\xi y\rfloor - \lfloor\xi x\rfloor` work,
since $`|\mathrm{fract}(\xi y) - \mathrm{fract}(\xi x)|\cdot(n+1) \le 1`
(`abs_sub_lt_one_of_floor_eq_floor`). The rational reformulation is
`Real.exists_rat_abs_sub_le_and_den_le`.
:::

## Infinitely Many Good Rational Approximations
:::lemma_ "dirichlet-good-approx" (lean := "Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational")
*(Infinitely many good approximations.)* An irrational real number $`\xi` has infinitely many
rational approximations $`q` (in lowest terms) with
$$`\left|\xi - q\right| < \frac{1}{q.\mathrm{den}^2}.`
:::

:::proof "dirichlet-good-approx"
Iterating Dirichlet's theorem produces, from any rational approximation $`q`, a strictly better one
$`q'` with $`|\xi - q'| < 1/(q'.\mathrm{den})^2` and $`|\xi - q'| < |\xi - q|`
(`exists_rat_abs_sub_lt_and_lt_of_irrational`): choose $`n > 1/|\xi - q|` and apply
{uses "dirichlet-approx"}[] in its denominator-bounded form ({uses "dirichlet-good-approx"}[] uses
`Real.exists_rat_abs_sub_le_and_den_le`), whose output beats $`q` because $`\xi` is irrational, hence
$`\xi \neq q`. Since each good approximation can be strictly improved, no finite set of them can be
exhaustive, so infinitely many exist. This is the infinitude that drives the existence of nontrivial
Pell solutions.
:::

## Real Convergents
:::definition "real-convergent" (lean := "Real.convergent")
For a real number $`\xi`, mathlib gives a *direct recursive* definition of the convergents of its
continued fraction expansion as rational numbers (so that Legendre's theorem can be stated without
leaving $`\mathbb{Q}`):
$$`\xi.\mathrm{convergent}(0) = \lfloor\xi\rfloor,\qquad
   \xi.\mathrm{convergent}(n+1) = \lfloor\xi\rfloor + \bigl((\mathrm{fract}\,\xi)^{-1}.\mathrm{convergent}(n)\bigr)^{-1}.`
This agrees with $`(\mathrm{of}\,\xi).\mathrm{convs}` ({uses "gcf-convergents"}[]) where the latter is
defined (`Real.convs_eq_convergent`), using the convention $`1/0 = 0` to make it total.
:::

## Legendre's Theorem on Best Approximations
:::theorem "legendre-convergent" (lean := "Real.exists_rat_eq_convergent")
*(Legendre's theorem.)* If a rational $`q` satisfies
$$`\left|\xi - q\right| < \frac{1}{2\,q.\mathrm{den}^2},`
then $`q` is a convergent of the continued fraction expansion of $`\xi`
({uses "real-convergent"}[]): $`q = \xi.\mathrm{convergent}(n)` for some $`n`.
:::

:::proof "legendre-convergent"
mathlib reduces to the technical statement `exists_rat_eq_convergent'`, phrased through the predicate
`ContfracLegendre.Ass ξ u v`: $`u` and $`v` are coprime and
$`|\xi - u/v| < 1/(v(2v-1))`. Writing $`q = u/v` in lowest terms, the hypothesis
$`|\xi - q| < 1/(2q.\mathrm{den}^2)` supplies exactly this assumption. The technical version is proved
by *strong induction on the denominator $`v`*: for $`v \le 1` the approximation is the zeroth
convergent $`\lfloor\xi\rfloor`; for $`v \ge 2` one passes to $`(\mathrm{fract}\,\xi)^{-1}` and shows
the assumption is inherited with the strictly smaller denominator $`u - \lfloor\xi\rfloor v`
(the `invariant` lemma), so the induction hypothesis gives a convergent of $`(\mathrm{fract}\,\xi)^{-1}`,
which the recursion ({uses "real-convergent"}[]) turns into the next convergent of $`\xi`. This is the
quantitative converse to Dirichlet's theorem ({uses "dirichlet-approx"}[]): approximation past order
$`2` forces the approximant to be a convergent.
:::

# Pell's equation, its solution group, and the fundamental solution

## Pell's Equation
:::definition "pell-ispell" (lean := "Pell.IsPell")
For an integer $`d`, an element $`\alpha = x + y\sqrt{d} \in \mathbb{Z}[\sqrt{d}]` ({uses "zsqrtd"}[])
*is a Pell solution* (`Pell.IsPell`) when
$$`x^2 - d\,y^2 = 1,`
i.e. when $`N(\alpha) = 1` ({uses "zsqrtd-norm"}[]). By the conjugate description of the norm this is
equivalent to $`\alpha\,\overline{\alpha} = 1` (`Pell.isPell_norm`) and hence to $`\alpha` being
unitary (`Pell.isPell_iff_mem_unitary`, the analogue of {uses "zsqrtd-norm-unitary"}[]); the Pell
solutions are therefore closed under multiplication (`Pell.isPell_mul`) and conjugation, which is the
source of their group structure.
:::

## The Type of Pell Solutions
:::definition "pell-solution" (lean := "Pell.Solution₁")
For an integer $`d`, the type $`\mathrm{Solution}_1(d)` (`Pell.Solution₁`) is the subtype of unitary
elements of $`\mathbb{Z}[\sqrt{d}]` ({uses "zsqrtd-norm-unitary"}[]) — equivalently the pairs
$`(x, y)` of integers solving $`x^2 - dy^2 = 1` ({uses "pell-ispell"}[]). An element $`a` has
coordinates $`a.x` and $`a.y` with $`a.x^2 - d\,a.y^2 = 1` (`Pell.Solution₁.prop`).
:::

## Group Structure of Pell Solutions
:::theorem "pell-group" (lean := "Pell.Solution₁.instCommGroup")
The set $`\mathrm{Solution}_1(d)` ({uses "pell-solution"}[]) of solutions to Pell's equation is a
commutative group under the multiplication inherited from $`\mathbb{Z}[\sqrt{d}]` ({uses "zsqrtd"}[]):
$$`(x, y) \cdot (x', y') = (xx' + dyy',\; xy' + yx'),`
with identity $`(1, 0)` and inverse $`(x, y)^{-1} = (x, -y)` (the conjugate). The sign $`-1` acts by
$`-(x,y) = (-x,-y)` (a `HasDistribNeg` structure).
:::

:::proof "pell-group"
The norm-one elements of $`\mathbb{Z}[\sqrt{d}]` form the unitary submonoid
({uses "zsqrtd-norm-unitary"}[]), and as a subset of the commutative ring $`\mathbb{Z}[\sqrt{d}]`
closed under multiplication and inverse (the conjugate of a norm-one element is its inverse, since
$`\alpha\,\overline{\alpha} = 1`), it inherits a commutative group structure. The product law in
coordinates is `Pell.Solution₁.x_mul`, `Pell.Solution₁.y_mul` and the inverse is
`Pell.Solution₁.x_inv`, `Pell.Solution₁.y_inv`, read off from multiplication and conjugation in
$`\mathbb{Z}[\sqrt{d}]` ({uses "pell-ispell"}[]).
:::

## Existence of Nontrivial Pell Solutions
:::theorem "pell-exists" (lean := "Pell.exists_of_not_isSquare")
If $`d > 0` is not a perfect square, then the equation $`x^2 - dy^2 = 1` has a solution with
$`y \ne 0`.
:::

:::proof "pell-exists"
Set $`\xi = \sqrt{d}`, which is irrational because $`d` is a non-square integer
(`irrational_nrt_of_notint_nrt`). Fix an integer $`M > 2|\xi| + 1`. Using the infinitude of good
rational approximations to $`\xi` ({uses "dirichlet-good-approx"}[]), the set of rationals $`q` with
$`|q.\mathrm{num}^2 - d\,q.\mathrm{den}^2| < M` is infinite. Hence some fixed nonzero value $`m`
($`|m| < M`) is attained on an infinite set $`\{q : q.\mathrm{num}^2 - d\,q.\mathrm{den}^2 = m\}`
(otherwise the union over $`m` of finite sets would be finite). Mapping each such $`q` to
$`(q.\mathrm{num} \bmod |m|,\ q.\mathrm{den} \bmod |m|) \in \mathbb{Z}/|m| \times \mathbb{Z}/|m|`,
the pigeonhole principle (`exists_ne_map_eq_of_mapsTo`) produces two distinct $`q_1 \ne q_2` with the
same residues. The Brahmagupta composition then makes
$$`x = \frac{q_1.\mathrm{num}\,q_2.\mathrm{num} - d\,q_1.\mathrm{den}\,q_2.\mathrm{den}}{m}, \qquad
   y = \frac{q_1.\mathrm{num}\,q_2.\mathrm{den} - q_2.\mathrm{num}\,q_1.\mathrm{den}}{m}`
an integer pair (the numerators are divisible by $`m` by the matching residues) solving
$`x^2 - dy^2 = 1` ({uses "pell-solution"}[]), with $`y \ne 0` since $`q_1 \ne q_2`. The full
equivalence — a nontrivial solution exists iff $`d` is not a square — is
`Pell.exists_iff_not_isSquare`.
:::

## The Fundamental Solution
:::definition "pell-fundamental" (lean := "Pell.IsFundamental")
A solution $`a \in \mathrm{Solution}_1(d)` ({uses "pell-solution"}[]) with $`d > 0` non-square is the
*fundamental solution* (`Pell.IsFundamental`) if $`a.x > 1`, $`a.y > 0`, and $`a.x` is least among
the $`x`-coordinates of all solutions with $`x > 1`.
:::

## Existence of the Fundamental Solution
:::theorem "pell-fundamental-exists" (lean := "Pell.IsFundamental.exists_of_not_isSquare")
If $`d > 0` is not a perfect square, a fundamental solution exists
({uses "pell-fundamental"}[]).
:::

:::proof "pell-fundamental-exists"
By {uses "pell-exists"}[] there is a nontrivial solution, and replacing it by absolute values gives one
with $`a.x > 1` and $`a.y > 0` (`Pell.Solution₁.exists_pos_of_not_isSquare`). Transferring the
$`x`-coordinate to $`\mathbb{N}` lets one minimise it with `Nat.find`: the least natural $`x_1 > 1`
that occurs as the $`x`-coordinate of a positive solution, together with its $`y`-coordinate, is
fundamental, the minimality clause being exactly `Nat.find_min'`.
:::

## Uniqueness of the Fundamental Solution
:::theorem "pell-fundamental-unique" (lean := "Pell.IsFundamental.subsingleton")
The fundamental solution ({uses "pell-fundamental"}[]) is unique: any two fundamental solutions are
equal.
:::

:::proof "pell-fundamental-unique"
If $`a` and $`b` are both fundamental then each minimality clause bounds the other's $`x`-coordinate,
so $`a.x = b.x` by antisymmetry. The Pell relation then gives $`d\,a.y^2 = d\,b.y^2`, and since
$`d > 0` ({uses "pell-fundamental"}[]) and both $`y`-coordinates are positive, $`a.y = b.y`; hence
$`a = b` (`Pell.Solution₁.ext`).
:::

## Strict Monotonicity of Pell y-Coordinates
:::lemma_ "pell-y-strictmono" (lean := "Pell.IsFundamental.y_strictMono")
Let $`a` be the fundamental solution ({uses "pell-fundamental"}[]). The map $`n \mapsto (a^n).y` from
$`\mathbb{Z}` to $`\mathbb{Z}` is strictly increasing.
:::

:::proof "pell-y-strictmono"
It suffices to show $`(a^n).y < (a^{n+1}).y` for every $`n` (`strictMono_int_of_lt_succ`). Expanding
$`a^{n+1} = a^n \cdot a` with the product law ({uses "pell-group"}[]),
$$`(a^{n+1}).y - (a^n).y = (a^n).x\,(a.y) + (a^n).y\,(a.x - 1),`
and both summands are nonnegative — the first strictly positive — using that the $`x`-coordinate of a
power of a positive solution is positive (`x_zpow_pos`) and $`a.x > 1`, $`a.y > 0`. For negative $`n`
the claim follows by applying the nonnegative case to $`-n-1` and conjugating (`y_inv`). Strict
monotonicity makes distinct powers distinct and underlies the uniqueness of the exponent in the
classification of the solution group.
:::

## Structure of the Solution Group
:::theorem "pell-classification" (lean := "Pell.IsFundamental.eq_zpow_or_neg_zpow")
*(Structure of the solution group.)* Let $`d > 0` be non-square with fundamental solution $`a_1`
({uses "pell-fundamental"}[]). Every solution $`a \in \mathrm{Solution}_1(d)` satisfies
$$`a = a_1^{\,n} \quad\text{or}\quad a = -\,a_1^{\,n}`
for some $`n \in \mathbb{Z}`; the exponent and sign are unique. Thus $`\mathrm{Solution}_1(d) \cong
\{\pm 1\} \times \mathbb{Z}` as a group ({uses "pell-group"}[]).
:::

:::proof "pell-classification"
First reduce a general solution $`a` to a *positive variant* $`b` — one with $`b.x > 0` and
$`b.y \ge 0` — lying in $`\{a, a^{-1}, -a, -a^{-1}\}` (`Pell.Solution₁.exists_pos_variant`). The core
lemma `eq_pow_of_nonneg` shows every such nonnegative solution is $`a_1^{\,n}` for some $`n \in
\mathbb{N}`, by strong induction on its $`x`-coordinate: multiplying $`b` by $`a_1^{-1}` keeps the
$`x`-coordinate positive (`mul_inv_x_pos`) and the $`y`-coordinate nonnegative (`mul_inv_y_nonneg`)
while *strictly decreasing* the $`x`-coordinate (`mul_inv_x_lt_x`), so the descent terminates at the
identity $`a_1^0`. Undoing the four cases of the positive variant turns $`b = a_1^{\,n}` into
$`a = \pm\,a_1^{\,\pm n}`. Uniqueness of the exponent is the strict monotonicity of $`n \mapsto
(a_1^n).y` ({uses "pell-y-strictmono"}[]), and the sign is forced because no power of $`a_1` equals the
negative of a power (`zpow_ne_neg_zpow`, as the two have $`x`-coordinates of opposite sign).
:::

# Pell sequences and Matiyasevich's theorem

The constructive theory of Pell's equation in the special case $`d = a^2 - 1` underlies Davis's
variant of Matiyasevich's theorem and the Diophantine definition of the power function — the final
ingredient of the negative answer to Hilbert's tenth problem (the DPRM theorem). The nodes here use
$`d = a^2 - 1` throughout.

## Pell Sequences
:::definition "pell-sequence" (lean := "Pell.xn")
Fix $`a > 1` and put $`d = a^2 - 1`. The *Pell sequences* $`x_n` (`Pell.xn`) and $`y_n` (`Pell.yn`)
are defined by the simultaneous recurrence starting from the trivial solution $`(1, 0)`:
$$`x_0 = 1,\ y_0 = 0,\qquad x_{n+1} = x_n\,a + d\,y_n,\quad y_{n+1} = x_n + y_n\,a,`
equivalently $`x_n + y_n\sqrt{d} = (a + \sqrt{d})^n` in $`\mathbb{Z}[\sqrt{d}]` ({uses "zsqrtd"}[]).
Each pair is a Pell solution, $`x_n^2 - d\,y_n^2 = 1` (`Pell.pell_eq`, {uses "pell-ispell"}[]).
:::

## Every Pell Solution Is a Pell Sequence Term
:::theorem "pell-eq-pell" (lean := "Pell.eq_pell")
For $`d = a^2 - 1` with $`a > 1`, every natural-number solution of Pell's equation is a term of the
Pell sequence ({uses "pell-sequence"}[]): if $`x^2 - d\,y^2 = 1` then $`x = x_n` and $`y = y_n` for
some $`n`.
:::

:::proof "pell-eq-pell"
Viewing $`(x, y)` as the element $`x + y\sqrt{d} \in \mathbb{Z}[\sqrt{d}]`, the Pell relation says it
is unitary ({uses "zsqrtd-norm-unitary"}[]) and $`\ge 1`. The key lemma `eq_pellZd` shows every
unitary element $`\ge 1` is a power $`(a + \sqrt{d})^n` — proved by descent against the smallest
nontrivial solution $`a + \sqrt{d}`, exactly as in the general classification
({uses "pell-classification"}[]) but with the explicit fundamental solution $`(a, 1)`. Reading off
coordinates gives $`x = x_n`, $`y = y_n`.
:::

## Matiyasevich's Theorem
:::theorem "matiyasevic" (lean := "Pell.matiyasevic")
*(Matiyasevich's theorem, Davis's form.)* For naturals $`a, k, x, y`, the statement "$`a > 1` and
$`(x, y) = (x_k, y_k)`" ({uses "pell-sequence"}[]) is equivalent to a finite system of Pell equations
and congruences: $`1 < a`, $`k \le y`, and either $`(x, y) = (1, 0)`, or there exist
$`u, v, s, t, b` with
$$`x^2 - (a^2-1)y^2 = 1,\quad u^2 - (a^2-1)v^2 = 1,\quad s^2 - (b^2-1)t^2 = 1,`
$$`1 < b,\ \ b \equiv 1 \!\!\pmod{4y},\ \ b \equiv a \!\!\pmod{u},\ \ 0 < v,\ \ y^2 \mid v,\ \
   s \equiv x \!\!\pmod{u},\ \ t \equiv k \!\!\pmod{4y}.`
Because each clause is polynomial, the graph $`\{(a,k,x,y) : x = x_k\}` of the Pell-index relation is
*Diophantine*.
:::

:::proof "matiyasevic"
The forward direction instantiates the auxiliary variables from larger terms of the same Pell
sequence: with $`x = x_k`, $`y = y_k`, $`m = 2ky`, $`u = x_m`, $`v = y_m`, one checks $`k \le y`
(`yn_ge_n`), $`y^2 \mid v` (`ysq_dvd_yy`), and the congruences from the step-recurrence and the
divisibility/periodicity laws of the sequence (`yn_modEq_two`, `xy_coprime`, the
$`x_{4n+j} \equiv x_j \pmod{x_n}` and $`y_n \equiv n \pmod{a-1}` relations). The reverse direction is
the content of Davis's chain of lemmas: the congruences pin down, modulo $`u`, that $`x` equals
$`x_k` for the Pell sequence attached to $`a`, the auxiliary $`b`-equation supplying a sequence dense
enough (via $`b \equiv 1 \pmod{4y}`) to separate the index $`k` (`modEq_of_xn_modEq`). The pairwise
Pell relations are the unitary-element identities of the respective $`\mathbb{Z}[\sqrt{\cdot}]`
({uses "pell-ispell"}[]).
:::

## The Power Function Is Diophantine
:::theorem "pow-diophantine" (lean := "Pell.eq_pow_of_pell")
*(The power function is Diophantine.)* For naturals $`m, n, k`, the relation $`n^k = m` is equivalent
to a system of Pell equations and congruences in finitely many auxiliary natural variables; concretely
$`n^k = m` holds iff $`k = 0 \wedge m = 1`, or $`0 < k` and either $`n = 0 \wedge m = 0`, or $`0 < n`
and there exist $`w, a, t, z` with $`1 < a`,
$$`x_k \equiv y_k\,(a - n) + m \pmod{t},\quad 2an = t + (n^2 + 1),\quad m < t,`
$$`n \le w,\quad k \le w,\quad a^2 - \bigl((w+1)^2 - 1\bigr)(wz)^2 = 1,`
where $`x_k, y_k` are the Pell sequence for $`d = a^2 - 1` ({uses "pell-sequence"}[]). Hence
exponentiation is a Diophantine function.
:::

:::proof "pow-diophantine"
The exponential is recovered from the Pell sequence by the congruence
$`x_k \equiv y_k(a - n) + n^k \pmod{2an - n^2 - 1}` (an instance of
$`x_k + y_k\sqrt{d} = (a + \sqrt{d})^k` reduced modulo the relation $`\sqrt{d} \equiv -n`, valid once
$`a` is large enough relative to $`n^k`). Choosing $`a = x_{w+1, w}` for $`w = \max(n, k)` makes
$`a` exceed every relevant quantity (`strictMono_x`, `n_lt_xn`), so the congruence determines $`n^k`
exactly, with $`m < t` removing ambiguity. Building $`a` itself as a Pell value of the larger modulus
$`(w+1)^2 - 1` keeps the whole description polynomial ({uses "matiyasevic"}[]). This is the last step
of the DPRM theorem: combined with the Diophantine closure properties of `NumberTheory.Dioph`, it
shows every recursively enumerable set is Diophantine, so Hilbert's tenth problem is unsolvable.
:::

# Algebraic and transcendental numbers

## Algebraic and Transcendental Elements
:::definition "transcendental-def" (lean := "Transcendental")
Let $`A` be an algebra over a commutative ring $`R`. An element $`x \in A` is *algebraic* over $`R`
(`IsAlgebraic`) if it is a root of some nonzero polynomial $`p \in R[X]`, i.e.
$`\exists p \ne 0,\ \mathrm{aeval}_x\,p = 0`; it is *transcendental* over $`R` (`Transcendental`) if it
is not algebraic. Equivalently (`transcendental_iff`),
$$`x \text{ transcendental over } R \iff \forall p \in R[X],\ \mathrm{aeval}_x\,p = 0 \to p = 0.`
A real number is transcendental in the usual sense precisely when it is transcendental over
$`\mathbb{Z}` (equivalently over $`\mathbb{Q}`).
:::

## Liouville Numbers
:::definition "liouville-number" (lean := "Liouville")
A real number $`x` is a *Liouville number* (`Liouville`) if for every $`n \in \mathbb{N}` there exist
integers $`a, b` with $`b > 1` such that
$$`0 < \left|x - \frac{a}{b}\right| < \frac{1}{b^n}.`
In Lean the strict positivity is encoded as $`x \ne a/b`. Thus a Liouville number is approximable by
rationals to *every* order — far better than Dirichlet's universal order $`2`
({uses "dirichlet-approx"}[]).
:::

## Liouville Numbers Are Irrational
:::theorem "liouville-irrational" (lean := "Liouville.irrational")
Every Liouville number ({uses "liouville-number"}[]) is irrational.
:::

:::proof "liouville-irrational"
By contradiction: suppose $`x = a/b` with $`a \in \mathbb{Z}`, $`b \in \mathbb{N}` positive, is a
Liouville number. Apply the defining property at $`n = b + 1` to get $`p, q` with $`q > 1`,
$`a/b \ne p/q`, and $`|a/b - p/q| < 1/q^{b+1}`. Clearing denominators, $`a/b - p/q = (aq - bp)/(bq)`
with $`aq - bp` a *nonzero integer*, so $`|aq - bp| \ge 1`; this is the decisive gain. Then
$`|aq - bp|\cdot q^{b+1} < bq` while $`|aq-bp| \ge 1` and $`q > 1` force $`bq \le |aq-bp|\cdot q^{b+1}`
(`Nat.mul_lt_mul_pow_succ`), a contradiction.
:::

## Liouville's Theorem on Transcendence
:::theorem "liouville-transcendental" (lean := "Liouville.transcendental")
*(Liouville's theorem.)* Every Liouville number ({uses "liouville-number"}[]) is transcendental over
$`\mathbb{Z}` ({uses "transcendental-def"}[]).
:::

:::proof "liouville-transcendental"
Suppose for contradiction that the Liouville number $`x` is algebraic, the root of a nonzero
$`f \in \mathbb{Z}[X]` of degree $`d`. The heart is `exists_pos_real_of_irrational_root`, which (since
$`x` is irrational, {uses "liouville-irrational"}[]) produces a constant $`A > 0` with
$$`1 \le (b+1)^{d}\cdot\bigl|x - \tfrac{a}{b+1}\bigr|\cdot A \qquad\text{for all } a \in \mathbb{Z},\ b \in \mathbb{N}.`
That lemma combines three inputs: $`f` has finitely many roots, so there is a closed ball around $`x`
in which $`x` is its only root (`exists_closedBall_inter_eq_singleton_of_discrete`); $`f` is Lipschitz
there because its derivative is bounded on a compact interval, via the Mean Value Theorem
(`Convex.norm_image_sub_le_of_norm_deriv_le`); and the *integrality* bound — $`f(a/b)\,b^{d}` is a
nonzero integer, hence $`\ge 1` in absolute value (`one_le_pow_mul_abs_eval_div`) — which would fail
only if $`a/b` were a rational root, excluded by irrationality. Now use the Archimedean property to
pick $`r` with $`A < 2^{r}` (`pow_unbounded_of_one_lt`), and apply the Liouville property
({uses "liouville-number"}[]) at exponent $`r + d` to obtain $`a, b` with
$`|x - a/b| < 1/b^{\,r+d}`. Chaining the two bounds gives
$`b^{d}\,|x - a/b| < 1/A \le b^{d}\,|x - a/b|`, contradicting `lt_irrefl`. This is the exact
counterpoint to Dirichlet's theorem ({uses "dirichlet-approx"}[]): an algebraic irrational of degree
$`d` cannot be approximated past order $`d`.
:::

## Liouville's Constant
:::definition "liouville-constant" (lean := "liouvilleNumber")
For a real number $`m`, the *Liouville constant to base $`m`* is the series
$$`L_m \coloneqq \sum_{i=0}^{\infty} \frac{1}{m^{\,i!}}.`
The series converges for $`m > 1`; for other $`m` the sum is defined to be $`0` (mathlib's `tsum`
convention). The classical Liouville number is $`L_2 = 0.1100010000\ldots_2`.
:::

## Transcendence of Liouville's Constant
:::theorem "liouville-constant-transcendental" (lean := "transcendental_liouvilleNumber")
For every integer $`m \ge 2`, the Liouville constant $`L_m` ({uses "liouville-constant"}[]) is
transcendental over $`\mathbb{Z}` ({uses "transcendental-def"}[]).
:::

:::proof "liouville-constant-transcendental"
It suffices to show $`L_m` is a Liouville number, for then Liouville's theorem
({uses "liouville-transcendental"}[]) applies — indeed `transcendental_liouvilleNumber` is literally
`(liouville_liouvilleNumber hm).transcendental`. To verify the Liouville condition
({uses "liouville-number"}[]) at level $`n`, truncate the series at index $`n`: the partial sum
$`\sum_{i=0}^{n} m^{-i!}` is a rational $`p/b` with denominator $`b = m^{\,n!}` (`partialSum_eq_rat`,
$`b > 1`). The remainder $`\sum_{i > n} m^{-i!}` is strictly positive (`remainder_pos`) and, by
comparison with a geometric series, bounded by $`1/(m^{\,n!})^{n} = 1/b^{n}` (`remainder_lt`). Hence
$`0 < |L_m - p/b| < 1/b^{n}`, which is exactly the Liouville inequality.
:::

# Newton polygons of p-adic power series

The nodes in this section are *informal*: the `NewtonPolys` project
([`CBirkbeck/NewtonPoly`](https://github.com/CBirkbeck/NewtonPoly), main branch) is built against
mathlib v4.28.0-rc1 and therefore carries no `(lean := …)` reference in this v4.30 chapter. Each node
records the declaration that formalises it, an exact-source permalink at the project's recorded commit
`a6d9970`, and the true Lean status (the file is sorry-free). The cross-chapter edges to
{bpref "valuation"}[] and {bpref "padic-val-rat"}[] reflect genuine dependence: the Newton polygon of
a $`p`-adic power series is built from the valuation ({bpref "valuation"}[]) of its coefficients, and
its slopes encode the $`p`-adic valuations ({bpref "padic-val-rat"}[]) of the roots. Following Gouvêa
§7.4, the project abstracts a power series to its *valuation sequence* and proves the geometric
"supporting line" facts and the radius-of-convergence theorem; the root-distribution functions are
defined but the root-counting theorem itself is recorded only as Gouvêa-cited motivation, not as a
proved statement.

## Valuation Sequences
:::definition "newton-valseq"
The *valuation sequence* of a power series $`f = \sum_i a_i X^i` over a ring equipped with a map
$`v` to $`\mathbb{Z} \cup \{\infty\}` ({uses "valuation"}[]) is the function
$`\mathrm{vs}_f : \mathbb{N} \to \mathbb{Z} \cup \{\infty\}`, $`\mathrm{vs}_f(i) = v(a_i)`, with the
value $`\infty` (encoded $`\top`) marking a zero coefficient. The Newton polygon below is computed
solely from this sequence; the $`p`-adic instance takes $`\mathrm{vs}_f(i) = v_p(a_i)`
({uses "padic-val-rat"}[]). In Lean this is the type
`NewtonPolygon.ValSeq := ℕ → WithTop ℤ`, with `toValSeq f v` extracting it from an actual
`PowerSeries`.
Formalised in [`NewtonPolys`](https://github.com/CBirkbeck/NewtonPoly): [`NewtonPolygon.ValSeq`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L99), [`NewtonPolygon.toValSeq`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L448) — sorry-free.
:::

## Newton Polygons
:::definition "newton-polygon"
Let $`f(X) = \sum_{i \ge 0} a_i X^i` be a power series over a field with a non-archimedean valuation
$`v` ({uses "valuation"}[]). Plot the points $`(i, v(a_i))` for $`a_i \ne 0` and take their lower
convex hull: starting from the leftmost point, rotate a line counterclockwise about the current vertex
until it meets the next lattice point, which becomes the new vertex, and repeat. The slopes of the
successive segments are non-decreasing rationals; the polygon may end in a *final ray* when the
infimum of remaining slopes is not attained at a lattice point. In Lean the result is encoded as a
`NewtonPolygonData` record — a list of `Segment`s (each carrying start/end index and valuation) and an
optional `FinalRay` — and the rotating-line step is the function `nextStep`, which at a vertex
$`(i_0, v_0)` computes the infimum $`\mathrm{sInf}` of the real slope set ({uses "newton-valseq"}[])
and branches on whether it is attained, attained infinitely often, or not attained.
Formalised in [`NewtonPolys`](https://github.com/CBirkbeck/NewtonPoly): [`NewtonPolygon.NewtonPolygonData`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L240), [`NewtonPolygon.nextStep`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L168) — sorry-free.
:::

## Supporting Property of the Newton Polygon
:::theorem "newton-supporting"
The Newton polygon ({uses "newton-polygon"}[]) is *well-formed* and its segments are *supporting*. A
`NewtonPolygonData` is well-formed when consecutive segments share a vertex, segment slopes are
non-decreasing, and any final ray's slope is at least the last segment slope; the empty polygon (for
a constant or zero series) is well-formed. Each segment is *tight* — its right endpoint lies exactly
on the line extending it — and *supporting*: writing $`m = \mathrm{sInf}\,S` for the slope set $`S`
from a vertex $`(i_0, v_0)`, every later lattice point lies on or above the line of slope $`m`,
$$`v(a_i) \ge v_0 + m\,(i - i_0) \qquad (i > i_0,\ a_i \ne 0).`
Formalised in [`NewtonPolys`](https://github.com/CBirkbeck/NewtonPoly): [`NewtonPolygon.minSlope_supporting`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L331), [`NewtonPolygon.Segment.tight_of_slope`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L308), [`NewtonPolygon.achievingSet_onLine`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L359), [`NewtonPolygon.emptyPolygon_wellFormed`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L394) — sorry-free.
:::

:::proof "newton-supporting"
Tightness (`Segment.tight_of_slope`) is the computation that, with the segment's own slope
$`m = (v_1 - v_0)/(i_1 - i_0)`, the value $`v_0 + m(i_1 - i_0)` equals $`v_1`; it is closed by
`field_simp; ring` after clearing the nonzero denominator $`i_1 - i_0 > 0`. The supporting property
(`minSlope_supporting`) is the heart: the real slope to any later point $`(i, v(a_i))` belongs to the
slope set $`S`, hence is $`\ge \mathrm{sInf}\,S = m` by `csInf_le` (using $`S` bounded below); since
$`i - i_0 > 0`, multiplying through and rearranging by `linarith` gives $`v(a_i) \ge v_0 + m(i - i_0)`,
which is the infimum characterisation of the slope geometrically. Points achieving the minimum slope
lie exactly on the line (`achievingSet_onLine`), the same `field_simp; ring` computation as
tightness. Well-formedness of the empty polygon (`emptyPolygon_wellFormed`) is immediate, all four
clauses being vacuous. (The project proves these supporting facts about the rotating-line step; it
does not prove that the fully iterated `buildNewtonPolygon` output is well-formed.)
:::

## Radius of Convergence via the Newton Polygon
:::theorem "newton-convergence"
*(Radius of convergence, Gouvêa Lemma 7.4.8.)* The Newton polygon ({uses "newton-polygon"}[]) governs
where a $`p`-adic power series $`f = \sum a_i X^i` converges. Convergence on a closed ball is the
condition $`v(a_i) - b\,i \to +\infty`. **Convergence direction:** if there is a supporting line
({uses "newton-supporting"}[]) of slope $`s` from some vertex $`(i_0, v_0)` and $`b < s`, then $`f`
converges on the ball of radius $`p^{b}`. **Divergence direction:** if $`b > m` and infinitely many
coefficients lie on a line $`y = m\,x` through the origin, then $`f` diverges at radius $`p^{b}`.
Together these pin the radius of convergence to $`p^{m}` for $`m` the supremum of Newton slopes; for
the geometric series $`1 + pX + pX^2 + \cdots` the supremum is $`0` and the radius is $`1`.
Formalised in [`NewtonPolys`](https://github.com/CBirkbeck/NewtonPoly): [`NewtonPolygon.lemma_7_4_8_convergence`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L1268), [`NewtonPolygon.lemma_7_4_8_divergence`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L1310), [`NewtonPolygon.geometricSeries_radius_of_convergence`](https://github.com/CBirkbeck/NewtonPoly/blob/a6d9970de20a9c1ba2a5340d666aaaaba8a94517/NewtonPolys/NewtonPolygon.lean#L1542) — sorry-free.
:::

:::proof "newton-convergence"
**Convergence** (`lemma_7_4_8_convergence`). From the supporting line, $`v(a_i) \ge v_0 + s(i - i_0)`
for all large $`i` with $`a_i \ne 0`. For any target $`C`, set $`C' = C - v_0 + s\,i_0`; since
$`s - b > 0`, the linear term $`(s - b)\,i` eventually exceeds $`C'` (`exists_nat_mul_gt`), and the
lower bound then yields $`v(a_i) - b\,i > C` for all large $`i`, i.e. $`v(a_i) - b\,i \to +\infty`.
**Divergence** (`lemma_7_4_8_divergence`). If convergence held at radius $`p^{b}` then for $`C = 0`
some tail has $`v(a_i) - b\,i > 0`; but on the cofinal set of indices with $`v(a_i) = m\,i` one gets
$`(m - b)\,i < 0` (as $`b > m`, $`i \ge 1`), a contradiction. Combining the two directions across the
limiting slope determines the radius $`p^{m}`; the geometric-series instance verifies it concretely,
with the complementary divergence `geometricSeries_diverges_outside` showing radius exactly $`1`. The
project's root-distribution functions (`rootCountAtSlope`, `rootDistribution`) record the Gouvêa
correspondence "a segment of slope $`m` and length $`\ell` carries $`\ell` roots of valuation $`m`" as
the intended meaning of the data, but that root-counting statement is not itself formalised as a
theorem.
:::

# Forthcoming in mathlib

The node below is an *informal* statement of a result that is the subject of an open mathlib pull
request (the `t-number-theory` queue, as of June 2026). It carries a `pr_url` pointing at the live PR
and **no** `(lean := …)` reference: the declarations are not yet in mathlib v4.30.0-rc2. It connects
into the dependency graph through the mathlib-backed transcendence and Diophantine-approximation nodes
of this chapter via `{uses}` edges, and should be re-pointed to `(lean := …)` once the PR merges.

## The Gelfond-Schneider Theorem
:::theorem "gelfond-schneider" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/35735")
*(Gelfond–Schneider theorem, Hilbert's seventh problem.)* Let $`\alpha, \beta` be algebraic numbers
({uses "transcendental-def"}[]) with $`\alpha \ne 0`, $`\alpha \ne 1`, and $`\beta \notin \mathbb{Q}`.
Then any value of
$$`\alpha^{\beta} = \exp(\beta \log \alpha)`
is transcendental. In particular $`2^{\sqrt{2}}` (the Gelfond–Schneider constant) and
$`e^{\pi} = (-1)^{-i}` are transcendental.

The proof is the auxiliary-function method: assuming $`\alpha^\beta` algebraic, one builds an
auxiliary polynomial in $`\alpha^x` and $`\alpha^{\beta x}` that vanishes to high order at many
integer points, then derives a contradiction between an arithmetic lower bound on its nonzero
derivatives and an analytic upper bound — the same tension between good rational/algebraic
approximation and transcendence that drives Liouville's theorem
({uses "liouville-transcendental"}[]), with the pigeonhole construction of the auxiliary function
resting on Diophantine approximation ({uses "dirichlet-approx"}[]). PR #35735 formalises the analytic
core (non-vanishing and lower bounds for the Gelfond–Schneider auxiliary function; companion PRs
#33050, #35743, #35744 supply further analytic lemmas).
In review — [mathlib PR #35735](https://github.com/leanprover-community/mathlib4/pull/35735).
:::
