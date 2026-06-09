import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.NumberTheory.DiophantineApproximation.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Diophantine Equations and Transcendence" =>

This chapter covers four interlocking topics: the ring $`\mathbb{Z}[\sqrt{d}]` and its norm, Pell's equation $`x^2 - dy^2 = 1`, the theory of continued fractions and their convergents, and Liouville's theorem on transcendental numbers. Throughout, $`d` denotes a non-square positive integer, $`\mathbb{Z}` the integers, and $`\mathbb{R}` the real numbers. Results in Gelfond–Schneider, full Lindemann–Weierstrass, and Newton polygons are forthcoming mathlib PRs or the `NewtonPolys` project (Phase 3) and are not blueprinted here.

# The ring $`\mathbb{Z}[\sqrt{d}]` and its norm

:::definition "zsqrtd" (lean := "Zsqrtd")
For an integer $`d`, the *ring $`\mathbb{Z}[\sqrt{d}]`* consists of formal expressions $`a + b\sqrt{d}` with $`a, b \in \mathbb{Z}`. Addition and multiplication are defined by
$$`(a + b\sqrt{d}) + (a' + b'\sqrt{d}) = (a + a') + (b + b')\sqrt{d}`
$$`(a + b\sqrt{d})(a' + b'\sqrt{d}) = (aa' + dbb') + (ab' + ba')\sqrt{d}.`
The components $`a` and $`b` are called the *real part* (`.re`) and the *imaginary part* (`.im`) respectively. For $`d` a non-square with $`d \equiv 2, 3 \pmod 4`, this is exactly the ring of integers ({uses "ring-of-integers"}[]) of the real quadratic field $`\mathbb{Q}(\sqrt{d})`.
:::

:::definition "zsqrtd-norm" (lean := "Zsqrtd.norm")
The *norm* of an element $`\alpha = a + b\sqrt{d} \in \mathbb{Z}[\sqrt{d}]` is the integer
$$`N(\alpha) \coloneqq a^2 - d\, b^2.`
:::

:::lemma_ "zsqrtd-norm-mul" (lean := "Zsqrtd.norm_mul")
The norm is multiplicative: for all $`\alpha, \beta \in \mathbb{Z}[\sqrt{d}]`,
$$`N(\alpha\beta) = N(\alpha)\, N(\beta).`
:::

:::proof "zsqrtd-norm-mul"
A direct computation using {uses "zsqrtd"}[]: expanding both sides of $`N((a + b\sqrt{d})(a' + b'\sqrt{d}))` and applying the definition {uses "zsqrtd-norm"}[] yields $`(aa' + dbb')^2 - d(ab' + ba')^2 = (a^2 - db^2)(a'^2 - db'^2)`, which is the Brahmagupta–Fibonacci identity.
:::

# Pell's equation

:::definition "pell-solution" (lean := "Pell.Solution₁")
Let $`d` be an integer. A *solution to Pell's equation* $`x^2 - dy^2 = 1` is a pair of integers $`(x, y)` satisfying this identity. The set of all solutions is denoted $`\mathrm{Solution}_1(d)` and carries the structure of a commutative group, with multiplication
$$`(x, y) \cdot (x', y') = (xx' + dyy',\; xy' + yx').`
This law arises from multiplication in $`\mathbb{Z}[\sqrt{d}]` ({uses "zsqrtd"}[]): a pair $`(x, y)` solves the equation precisely when $`x + y\sqrt{d}` has norm $`1` ({uses "zsqrtd-norm"}[]).
:::

:::theorem "pell-exists" (lean := "Pell.exists_of_not_isSquare")
If $`d > 0` is not a perfect square, then the equation $`x^2 - dy^2 = 1` has a solution with $`y \ne 0`.
:::

:::proof "pell-exists"
Since $`d` is not a square, $`\sqrt{d}` is irrational. By Dirichlet's approximation theorem ({uses "dirichlet-approx"}[]) the set of rationals $`a/b` with $`|a^2 - db^2| < C` (for a suitable bound $`C`) is infinite. By pigeonhole some residue class modulo $`C` contains infinitely many such pairs; subtracting two pairs in the same class yields a non-trivial solution in $`\mathbb{Z}[\sqrt{d}]` of norm $`1`, i.e.\ a solution to Pell's equation ({uses "pell-solution"}[]).
:::

:::definition "pell-fundamental" (lean := "Pell.IsFundamental")
A solution $`(x_1, y_1)` to $`x^2 - dy^2 = 1` with $`d > 0` non-square is called the *fundamental solution* if $`x_1 > 1`, $`y_1 > 0`, and $`x_1` is as small as possible among all solutions with $`x > 1`.
:::

:::theorem "pell-fundamental-exists" (lean := "Pell.IsFundamental.exists_of_not_isSquare")
If $`d > 0` is not a perfect square, there exists a unique fundamental solution.
:::

:::proof "pell-fundamental-exists"
Existence of the fundamental solution ({uses "pell-fundamental"}[]) follows from {uses "pell-exists"}[]: the non-trivial solutions with $`x > 1` and $`y > 0` form a non-empty set, and $`x` takes a minimum value since solutions with bounded $`x` are finite, so the defining minimality condition is met. Uniqueness: if $`(x_1, y_1)` and $`(x_1', y_1')` are both fundamental, then $`x_1 \le x_1' \le x_1`, hence $`x_1 = x_1'`, and the Pell equation forces $`y_1^2 = y_1'^2`, giving $`y_1 = y_1'` since both are positive.
:::

:::theorem "pell-group-structure" (lean := "Pell.IsFundamental.eq_zpow_or_neg_zpow")
Let $`d > 0` be a non-square integer and let $`(x_1, y_1)` be the fundamental solution. Every solution $`(x, y)` to $`x^2 - dy^2 = 1` satisfies
$$`(x, y) = \pm\, (x_1, y_1)^n`
for a unique $`n \in \mathbb{Z}`, where the power is taken in the group $`\mathrm{Solution}_1(d)` ({uses "pell-solution"}[]).
:::

:::proof "pell-group-structure"
Since $`\mathrm{Solution}_1(d)` is an abelian group ({uses "pell-solution"}[]) and the $`y`-coordinate of $`(x_1, y_1)^n` is strictly increasing in $`n` ({uses "pell-fundamental-exists"}[]), distinct powers $`\pm(x_1,y_1)^n` are distinct. One shows by induction that every solution with $`x > 1`, $`y > 0` lies between consecutive powers of $`(x_1, y_1)`, and the minimality of $`x_1` forces the solution to equal some power.
:::

# Continued fractions

:::definition "gcf" (lean := "GenContFract")
A *generalised continued fraction* over a type $`\alpha` is an expression of the form
$$`h + \dfrac{a_0}{b_0 + \dfrac{a_1}{b_1 + \dfrac{a_2}{b_2 + \cdots}}}`
with *head term* $`h \in \alpha` and a (possibly infinite) sequence of *partial numerator–denominator pairs* $`(a_i, b_i)`.  When all $`a_i = 1` the expression is a *simple continued fraction*; when additionally all $`b_i > 0` it is a *(regular) continued fraction*.
:::

:::definition "gcf-convergents" (lean := "GenContFract.convs")
The *$`n`-th convergent* $`C_n` of a generalised continued fraction ({uses "gcf"}[]) is the rational number obtained by truncating the expansion after the $`n`-th partial denominator. Convergents are computed by the recurrence
$$`A_{-1} = 1,\quad A_0 = h,\quad A_n = b_{n-1}A_{n-1} + a_{n-1}A_{n-2}`
$$`B_{-1} = 0,\quad B_0 = 1,\quad B_n = b_{n-1}B_{n-1} + a_{n-1}B_{n-2}`
$$`C_n = A_n / B_n,`
where $`A_n` and $`B_n` are the *numerator* and *denominator continuants*.
:::

:::theorem "cf-determinant" (lean := "SimpContFract.determinant")
For a simple continued fraction, the consecutive convergents satisfy the *determinant formula*
$$`A_n B_{n+1} - B_n A_{n+1} = (-1)^{n+1}.`
In particular, consecutive convergents $`C_n = A_n/B_n` and $`C_{n+1} = A_{n+1}/B_{n+1}` satisfy $`|C_n - C_{n+1}| = 1/(B_n B_{n+1})`.
:::

:::proof "cf-determinant"
By induction on $`n`. The base case $`n = 0` is $`A_0 B_1 - B_0 A_1 = h \cdot (b_0 + h) - 1 \cdot \ldots` which gives $`-1 = (-1)^1` after unfolding the recurrences ({uses "gcf-convergents"}[]). The inductive step uses the recurrence for continuants to factor out a $`b_n` and apply the induction hypothesis, picking up a sign flip each step.
:::

:::theorem "cf-convergence" (lean := "GenContFract.of_convergence")
For any real number $`v`, the sequence of convergents of the regular continued fraction expansion of $`v` converges to $`v`:
$$`\lim_{n \to \infty} C_n = v.`
:::

:::proof "cf-convergence"
By the determinant formula ({uses "cf-determinant"}[]), consecutive convergents satisfy $`|C_n - C_{n+1}| = 1/(B_n B_{n+1})`. Since the denominators $`B_n` are bounded below by Fibonacci numbers, $`B_n \to \infty`, and $`|v - C_n| \le 1/(B_n B_{n+1}) \to 0`. An $`\varepsilon`/`N` argument using the Archimedean property then gives the stated convergence.
:::

# Dirichlet's approximation theorem

:::theorem "dirichlet-approx" (lean := "Real.exists_int_int_abs_mul_sub_le")
*(Dirichlet's approximation theorem.)* For any real number $`\xi` and any positive integer $`n`, there exist integers $`j` and $`k` with $`0 < k \le n` such that
$$`|k\xi - j| \le \frac{1}{n+1}.`
Equivalently, there is a rational $`j/k` with $`|\xi - j/k| \le 1/(k(n+1))`.
:::

:::proof "dirichlet-approx"
Partition the unit interval $`[0, 1)` into $`n+1` subintervals of length $`1/(n+1)`. Consider the $`n+2` numbers $`\{m\xi\}` for $`m = 0, 1, \ldots, n`, where $`\{t\}` denotes the fractional part. By pigeonhole, two of these lie in the same subinterval: $`|\{k\xi\} - \{k'\xi\}| < 1/(n+1)`. Setting $`k = |k - k'|` and $`j = \lfloor k\xi \rfloor` or the nearest integer gives the inequality.
:::

:::theorem "legendre-convergent" (lean := "Real.exists_rat_eq_convergent")
*(Legendre's theorem.)* If a rational $`q = p/r` satisfies
$$`\left|\xi - \frac{p}{r}\right| < \frac{1}{2r^2},`
then $`p/r` is a convergent of the continued fraction expansion of $`\xi`.
:::

:::proof "legendre-convergent"
This is the converse to the best-approximation property quantified by Dirichlet's approximation theorem ({uses "dirichlet-approx"}[]): among all fractions with denominator at most $`r`, the convergents $`A_n/B_n` are the best approximations. If $`|p/r - \xi|` is smaller than $`1/(2r^2)`, it is in particular smaller than $`|A_n/B_n - \xi|` for all $`n` with $`B_n \le r`; tracing through the continued fraction algorithm ({uses "gcf-convergents"}[]) shows $`p/r` must itself appear as a convergent.
:::

# Liouville numbers and transcendence

:::definition "liouville-number" (lean := "Liouville")
A real number $`x` is a *Liouville number* if for every $`n \in \mathbb{N}` there exist integers $`a, b` with $`b > 1` such that
$$`0 < \left|x - \frac{a}{b}\right| < \frac{1}{b^n}.`
:::

:::theorem "liouville-irrational" (lean := "Liouville.irrational")
Every Liouville number is irrational.
:::

:::proof "liouville-irrational"
Suppose $`x = p/q` is rational with $`q > 0`. Take $`n = q + 1`. Any approximation $`a/b` satisfying the Liouville condition would give $`|pq^{-1} - a/b| < b^{-(q+1)}`, but clearing denominators shows $`|pb - aq| \ge 1` (since this is a nonzero integer), so $`|p/q - a/b| = |pb - aq|/(qb) \ge 1/(qb)`; for $`b > 1` this exceeds $`b^{-(q+1)}`, a contradiction.
:::

:::theorem "liouville-transcendental" (lean := "Liouville.transcendental")
*(Liouville's theorem.)* Every Liouville number is transcendental.
:::

:::proof "liouville-transcendental"
Suppose $`x` is a Liouville number ({uses "liouville-number"}[]) and suppose for contradiction that $`x` is algebraic over $`\mathbb{Z}`, a root of a nonzero polynomial $`f \in \mathbb{Z}[X]` of degree $`d`. Since $`x` is irrational ({uses "liouville-irrational"}[]) and $`f` has finitely many roots, there is a positive $`A` such that for all integers $`a, b` with $`b > 0`:
$$`\left|\frac{a}{b} - x\right| \ge \frac{A}{b^d}.`
This Liouville inequality is the exact counterpoint to Dirichlet's approximation theorem ({uses "dirichlet-approx"}[]): whereas Dirichlet guarantees *every* irrational is approximable to order $`2`, an algebraic irrational of degree $`d` cannot be approximated past order $`d`. The lower bound—coming from the fact that $`f(a/b)` is a nonzero integer divided by $`b^d`, together with Lipschitz continuity of $`f` near $`x`—contradicts the definition of a Liouville number for $`n` larger than $`d + \log_2(1/A)`, which produces approximations far better than order $`d`.
:::

:::definition "liouville-constant" (lean := "liouvilleNumber")
For a real number $`m > 1`, the *Liouville constant to base $`m`* is the series
$$`L_m \coloneqq \sum_{i=0}^{\infty} \frac{1}{m^{i!}}.`
The classical Liouville number corresponds to $`m = 2`, giving $`L_2 = 0.1100010000\ldots` in binary.
:::

:::theorem "liouville-constant-transcendental" (lean := "transcendental_liouvilleNumber")
For every integer $`m \ge 2`, the Liouville constant $`L_m` is transcendental.
:::

:::proof "liouville-constant-transcendental"
It suffices to show $`L_m` is a Liouville number ({uses "liouville-transcendental"}[]), i.e.\ that it is super-well-approximable by rationals. For each $`n`, truncate the series at index $`k = n`: the partial sum $`\sum_{i=0}^n m^{-i!}` is a rational with denominator $`m^{n!}`. The tail $`\sum_{i > n} m^{-i!}` is bounded above by a geometric series giving $`\text{tail} < 1/(m^{n!})^n`, which is $`(m^{n!})^{-n}`. Since the denominator is $`b = m^{n!}`, this approximation satisfies $`|L_m - p/b| < b^{-n}`, confirming the Liouville condition ({uses "liouville-constant"}[]).
:::
