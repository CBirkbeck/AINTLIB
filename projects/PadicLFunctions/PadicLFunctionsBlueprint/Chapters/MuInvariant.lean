import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Iwasawa mu-invariant" =>

We close the formalisation with classical Iwasawa theory: the $`\mu`- and
$`\lambda`-invariants of a $`\Zp`-extension. Proving Iwasawa's growth formula for
class numbers develops exactly the tools needed to see that the Galois modules
appearing in the {Informal.citet "RJW"}[] theory are finitely generated torsion
$`\Lam`-modules — the algebraic input to the Iwasawa Main Conjecture beyond the
Vandiver case. Throughout, $`p` is a fixed prime and $`F` a number field.

# The setup

:::definition "mu-zp-extension"
Let $`F` be a number field. A *$`\Zp`-extension* of $`F` is a Galois extension
$`F_\infty / F` with $`\Gal(F_\infty / F) \cong \Zp`. Writing $`\Gamma := \Gal(F_\infty/F)`,
the closed subgroups of $`\Zp` are $`p^n\Zp`, so for each $`n` there is a unique
subextension $`F_n` with $`\Gal(F_n/F) \cong \Z/p^n\Z`, and $`F_\infty = \bigcup_n F_n`.
:::

:::proposition "mu-cyclotomic-extension"
Every number field $`F` admits at least one $`\Zp`-extension, the *cyclotomic
$`\Zp`-extension*, contained in $`F(\mu_{p^\infty})`.
:::

:::proof "mu-cyclotomic-extension"
By Galois theory $`\Gal(F(\mu_{p^\infty})/F)` is an open subgroup of
$`\Gal(\Q(\mu_{p^\infty})/\Q) \cong \Zpx`. Now $`\Zpx \cong \mu_{p-1} \times (1 + p\Zp)`
(for $`p` odd) has a maximal quotient isomorphic to $`\Zp`, namely the quotient by
the finite torsion subgroup $`\mu_{p-1}`. Pulling this quotient back to the open
subgroup and taking the fixed field gives a $`\Zp`-extension of $`F`. For
$`F = \Q(\mu_p)` this is $`F_\infty = \Q(\mu_{p^\infty})`, with $`F_n = \Q(\mu_{p^{n+1}})`.
:::

*Leopoldt's conjecture* predicts that the number of independent $`\Zp`-extensions
of $`F` is exactly $`r_2 + 1`, where $`r_2` is the number of complex places; in
particular a totally real field should have only the cyclotomic $`\Zp`-extension.
This is known for $`F` abelian over $`\Q` or over an imaginary quadratic field.

# Iwasawa's theorem

Fix a $`\Zp`-extension $`F_\infty/F` and a topological generator $`\gamma_0` of
$`\Gamma = \Gal(F_\infty/F) \cong \Zp`. We identify the Iwasawa algebra
$`\Lam(\Gamma)` with $`\Lam := \Zp[[T]]` by sending $`\gamma_0 \mapsto 1 + T`
(this works for *any* choice of $`\gamma_0`; when $`\gamma_0 \mapsto 1` under
$`\Gamma \cong \Zp` it is the Mahler transform of {bpref "iwasawa-isomorphism"}[]).

:::definition "mu-iwasawa-module"
Let $`\sL_n` (resp. $`\sL_\infty`) be the maximal unramified abelian $`p`-extension
of $`F_n` (resp. the maximal unramified abelian pro-$`p`-extension of $`F_\infty`).
By class field theory
$$`\sY_n := \Gal(\sL_n/F_n) \;=\; \Cl(F_n) \otimes \Zp,`
the $`p`-Sylow subgroup of the ideal class group of $`F_n`. Set
$$`\sY_\infty := \varprojlim_n \sY_n,`
a compact $`\Lam`-module, and write $`e_n := \vp(\#\sY_n)` for the exponent of $`p`
in the class number of $`F_n`.
:::

:::theorem "mu-invariant"
*(Iwasawa.)* There exist integers $`\lambda \ge 0`, $`\mu \ge 0`, $`\nu \ge 0` and
an integer $`n_0`, such that for all $`n \ge n_0`
$$`e_n = \mu\, p^{n} + \lambda\, n + \nu.`
This rests on {uses "mu-iwasawa-module"}[], the finite generation
{uses "mu-Yinf-fg"}[], the level-recovery {uses "mu-Yn-quotient"}[], and the size
computation {uses "mu-size-of-A"}[] together with {uses "mu-error-bounded"}[].
:::

:::proof "mu-invariant"
The class number $`\#\sY_n = p^{e_n}`, so $`e_n = \vp\,\abs{\sY_n}`. By
{uses "mu-Yn-quotient"}[] we have $`\sY_n = \sY_\infty/\varphi^n(T)\sY_\infty`,
where $`\varphi^n(T) = (1+T)^{p^n}-1`. By {uses "mu-Yinf-fg"}[] the module
$`\sY_\infty` is finitely generated over $`\Lam`, so the structure theorem
{uses "lambda-module-structure"}[] gives a quasi-isomorphism to a standard module
$`\sA`. The error lemma {uses "mu-error-bounded"}[] reduces the computation of
$`\abs{\sY_n}` to that of $`\abs{\sA/\varphi^n(T)}` up to a bounded constant
$`p^c`, and {uses "mu-size-of-A"}[] evaluates the latter as $`p^{\mu p^n + \lambda n + c'}`
with $`\mu = \sum m_i` and $`\lambda = \sum k_j \deg f_j`. Combining, for
$`n \ge n_0`, $`e_n = \mu p^n + \lambda n + \nu`.
:::

We prove the theorem under the simplifying hypothesis (which covers
$`F = \Q(\mu_{p^m})` or $`\Q(\mu_{p^m})^+` with $`F_\infty/F` cyclotomic): there is
a *single* prime $`\mathfrak{p}` of $`F` above $`p`, and it is *totally ramified*
in $`F_\infty`. The general case reduces to this one. The proof has two steps:
first that $`\sY_\infty` is a finitely generated $`\Lam`-module, then a size
computation via the structure theorem.

## First step: finite generation

Because $`\mathfrak{p}` is totally ramified in $`F_\infty` while $`\sL_n/F_n` is
unramified, $`F_{n+1} \cap \sL_n = F_n`, whence
$$`\sY_n = \Gal(\sL_n/F_n) = \Gal(\sL_n F_{n+1}/F_{n+1}) = \sY_{n+1}/\Gal(\sL_{n+1}/\sL_n F_{n+1}),`
so $`\sY_{n+1}` surjects onto $`\sY_n`. Under $`\Lam \cong \Zp[[T]]`, the element
$`1 + T` acts as $`\gamma_0`. Let $`G := \Gal(\sL_\infty/F)`, let
$`I \subseteq G` be the inertia group of a prime of $`\sL_\infty` above
$`\mathfrak{p}`. Since $`\sL_\infty/F_\infty` is unramified, all inertia lies in
$`F_\infty/F`; thus $`I \cap \sY_\infty = 1` and, $`F_\infty/F` being totally
ramified, $`I \hookrightarrow G/\sY_\infty \cong \Gamma` is an isomorphism. Hence
$$`G = I\,\sY_\infty = \Gamma\,\sY_\infty.`
Let $`\sigma \in I` map to $`\gamma_0`.

:::proposition "mu-commutator"
Let $`G'` be the closure of the commutator subgroup of $`G`. Then
$$`G' = (\gamma_0 - 1)\cdot \sY_\infty = T\,\sY_\infty.`
:::

:::proof "mu-commutator"
Write $`a = \alpha x`, $`b = \beta y` with $`\alpha,\beta \in \Gamma` and
$`x,y \in \sY_\infty`. Since $`\Gamma` and $`\sY_\infty` are abelian and $`\Gamma`
acts on $`\sY_\infty` through the $`\Lam`-structure, a direct expansion of the
commutator gives
$$`aba^{-1}b^{-1} = (x^{\alpha})^{1-\beta}\,(y^{\beta})^{\alpha-1}.`
Taking $`\beta = 1`, $`\alpha = \gamma_0` shows $`(\gamma_0-1)\sY_\infty \subseteq G'`.
Conversely, writing $`\beta = \gamma_0^c` with $`c \in \Zp`, the binomial
expansion $`1 - \beta = -\sum_{n\ge 1}\binom{c}{n}(\gamma_0-1)^n \in T\Lam`, and
likewise $`\alpha - 1 \in T\Lam`; so every commutator lies in $`T\,\sY_\infty`.
:::

Recall $`\varphi^n(T) := (1+T)^{p^n} - 1` (the $`n`-th power of the Frobenius on
$`\Zp[[T]]`), with $`\varphi^0(T) = T`.

:::proposition "mu-Yn-quotient"
For all $`n \ge 0`,
$$`\sY_n = \sY_\infty / \varphi^n(T)\,\sY_\infty.`
This uses {uses "mu-commutator"}[].
:::

:::proof "mu-Yn-quotient"
Take $`n = 0`. As $`\sL_0` is the maximal unramified abelian $`p`-extension of
$`F` and $`\sL_\infty/F` is a pro-$`p`-extension, $`\sL_0/F` is the maximal
unramified abelian subextension of $`\sL_\infty`. Thus $`\sY_0 = \Gal(\sL_0/F)`
is $`G` modulo the subgroup generated by $`G'` and the inertia $`I`. Using
{uses "mu-commutator"}[] ($`G' = T\sY_\infty`) and $`G = I\,\sY_\infty`,
$$`\sY_0 = G/\langle G', I\rangle = \sY_\infty/(\gamma_0-1)\sY_\infty = \sY_\infty/T\,\sY_\infty.`
For $`n \ge 1` repeat with $`F` replaced by $`F_n` and $`\gamma_0` by
$`\gamma_0^{p^n}`; then $`(\gamma_0^{p^n}-1)\sY_\infty = ((1+T)^{p^n}-1)\sY_\infty
= \varphi^n(T)\sY_\infty`, giving the claim.
:::

:::lemma_ "mu-nakayama"
*(Nakayama's lemma for $`\Lam`-modules.)* Let $`\sY` be a compact $`\Lam`-module.
Then $`\sY` is finitely generated over $`\Lam` if and only if $`\sY/(p,T)\sY` is
finite. Moreover, if $`x_1,\dots,x_m` generate $`\sY/(p,T)\sY` over $`\Z`, they
generate $`\sY` over $`\Lam`; in particular $`\sY/(p,T)\sY = 0` implies $`\sY = 0`.
:::

:::proof "mu-nakayama"
This is the topological Nakayama lemma for the complete local ring $`\Lam`, whose
maximal ideal is $`\mathfrak{m} = (p,T)`. If $`\sY` is finitely generated then
$`\sY/\mathfrak{m}\sY` is a finite-dimensional vector space over the residue field
$`\Lam/\mathfrak{m} = \Fp`, hence finite. Conversely, suppose $`\sY/\mathfrak{m}\sY`
is finite, with classes of $`x_1,\dots,x_m` spanning it. Let $`M \subseteq \sY` be
the closed $`\Lam`-submodule they generate. Then $`\sY = M + \mathfrak{m}\sY`, so
iterating, $`\sY = M + \mathfrak{m}^k\sY` for every $`k`. Because $`\sY` is compact
and $`\bigcap_k \mathfrak{m}^k\sY = 0` (the $`\mathfrak{m}`-adic topology is
Hausdorff on the compact module), any $`y \in \sY` is a limit of elements of $`M`
modulo $`\mathfrak{m}^k`; completeness of $`\Lam` lets the correcting coefficients
converge, placing $`y \in M`. Thus $`\sY = M` is finitely generated. The same
argument with $`\sY/\mathfrak{m}\sY = 0` gives $`\sY = \mathfrak{m}\sY = 0`.
:::

:::proposition "mu-Yinf-fg"
$`\sY_\infty` is a finitely generated $`\Lam`-module. This uses
{uses "mu-Yn-quotient"}[] and {uses "mu-nakayama"}[].
:::

:::proof "mu-Yinf-fg"
Since $`\varphi(T) = (1+T)^p - 1 = \sum_{k=1}^p \binom{p}{k} T^k \in (p,T)`, the
quotient $`\sY_\infty/(p,T)\sY_\infty` is a quotient of $`\sY_\infty/\varphi(T)\sY_\infty
= \sY_1 = \Cl(F_1)\otimes\Zp` by {uses "mu-Yn-quotient"}[], which is finite. By
{uses "mu-nakayama"}[], $`\sY_\infty` is finitely generated over $`\Lam`.
:::

## Second step: the size computation

Finite generation lets us invoke the structure theorem
{bpref "lambda-module-structure"}[]: there is an exact sequence
$$`0 \to Q \to \sY_\infty \to \sA \to R \to 0,`
with $`Q, R` finite and
$$`\sA = \Lam^r \oplus \Big(\bigoplus_{i=1}^s \Lam/(p^{m_i})\Big) \oplus \Big(\bigoplus_{j=1}^t \Lam/(f_j(T)^{k_j})\Big),`
for integers $`r,s,t \ge 0`, $`m_i, k_j \ge 1` and distinguished polynomials
$`f_j(T)`. We must compute $`\abs{\sY_n} = \abs{\sY_\infty/\varphi^n(T)}`.

:::lemma_ "mu-error-bounded"
There are a constant $`c` and an integer $`n_0` such that, for all $`n \ge n_0`,
$$`\abs{\sY_\infty/\varphi^n(T)} = p^c\,\abs{\sA/\varphi^n(T)}.`
:::

:::proof "mu-error-bounded"
Place the two short exact sequences
$$`0 \to \varphi^n(T)\sY_\infty \to \sY_\infty \to \sY_\infty/\varphi^n(T) \to 0`
and the analogous one for $`\sA` in a commutative ladder, with vertical maps induced
by the quasi-isomorphism $`\sY_\infty \to \sA` of finite kernel $`Q` and cokernel
$`R`. The middle vertical map has kernel $`Q` and cokernel $`R`, both of order
bounded uniformly in $`n`. Applying the snake lemma to the squares gives, for the
third vertical map $`\sY_\infty/\varphi^n(T) \to \sA/\varphi^n(T)`, kernels and
cokernels that are sub- and sub-quotients of $`Q`, $`R` and the snake connecting
maps. As $`Q, R` are finite, these are uniformly bounded; one checks they moreover
*stabilise* for $`n \ge n_0` (the connecting maps eventually no longer change because
$`\varphi^n(T)` annihilates $`Q` and $`R` once $`n` is large). Comparing orders
across the third column, $`\abs{\sY_\infty/\varphi^n(T)}` and
$`\abs{\sA/\varphi^n(T)}` differ by the fixed factor $`p^c`.
:::

:::proposition "mu-size-of-A"
With $`\sA` as above, set $`m = \sum_i m_i` and $`\ell = \sum_j k_j\,\deg(f_j)`.
If $`\sA/\varphi^n(T)\sA` is finite for all $`n \ge 0`, then $`r = 0` and there are
constants $`n_0, c` with, for all $`n \ge n_0`,
$$`\abs{\sA/\varphi^n(T)} = p^{\,m p^n + \ell n + c}.`
This uses {uses "mu-phi-distinguished"}[].
:::

:::proof "mu-size-of-A"
*Step 1 ($`r=0`).* The polynomial $`\varphi^n(T) = T^{p^n} + \sum_{k=1}^{p^n-1}\binom{p^n}{k}T^k`
is distinguished. By Weierstrass division (a $`p`-adic Euclidean algorithm) every
$`f \in \Zp[[T]]` is uniquely $`q(T)\varphi^n(T) + r(T)` with $`\deg r \le p^n-1`,
so
$$`\Lam/\varphi^n(T) \cong \{r(T) \in \Zp[T] : \deg r \le p^n-1\}`
is infinite. As $`\sA/\varphi^n(T)` is finite, the free part must vanish:
$`r = 0`.

*Step 2 (the $`\Lam/(p^{m_i})` summands).* Reducing the displayed isomorphism mod
$`p^k`, $`\Lam/(p^k,\varphi^n(T))` is the space of degree $`\le p^n-1` polynomials
over $`\Z/p^k\Z`, so has order $`p^{k p^n}`. Summing, the second part of $`\sA`
contributes $`p^{m p^n}`, with $`m = \sum_i m_i`.

*Step 3 (the $`\Lam/(f_j^{k_j})` summands).* Let $`g` be distinguished of degree
$`d` and $`V = \Lam/(g)`. By {uses "mu-phi-distinguished"}[], for $`n` large
$`\varphi^{n+1}(T)V = p\,\varphi^n(T)V`. Since $`(p,g)`-coprimality makes
multiplication by $`p` injective on $`V`, and $`\abs{V/pV} = \abs{\Lam/(p,T^d)} = p^d`,
an induction gives $`\abs{V/\varphi^{n+1}(T)V} = p^{d}\,\abs{V/\varphi^n(T)V}`, hence
$`\abs{V/\varphi^n(T)V} = p^{nd + c}`. Applying with $`g = f_j^{k_j}` and summing,
the third part contributes $`p^{\ell n + c}`, $`\ell = \sum_j k_j\deg f_j`.
Multiplying the three contributions proves the formula.
:::

:::lemma_ "mu-phi-distinguished"
Let $`g(T) \in \Zp[T]` be distinguished of degree $`d`, $`V = \Lam/(g)`, and let
$`n_0` satisfy $`p^{n_0} \ge d`. Then for every $`n > n_0`,
$$`\varphi^{n+1}(T)\cdot V = p\,\varphi^n(T)\cdot V.`
:::

:::proof "mu-phi-distinguished"
As $`g` is distinguished, $`T^k \equiv p\cdot(\text{poly}) \pmod{g}` for all
$`k \ge d`. For $`k \ge n_0` we have $`p^k \ge d`, so $`\varphi^k(T) = T^{p^k} +
p\,(\text{poly}) \equiv p\,Q_k(T) \pmod g`. From the factorisation
$`X^{p^{k+1}}-1 = (X^{p^k}-1)\big(X^{p^k(p-1)} + \cdots + 1\big)` with $`X = 1+T`,
$$`\varphi^{k+1}(T) \equiv \varphi^{k}(T)\Big[(pQ_k+1)^{p-1} + \cdots + (pQ_k+1) + 1\Big] \pmod g.`
Every term in the bracket is divisible by $`p` except the $`p` constant terms,
which sum to $`p`; hence $`\varphi^{k+1}(T) \equiv p\,\varphi^k(T) \pmod g`. Taking
$`k = n_0` forces $`Q_{n_0+1} \equiv 0 \pmod p`, and inductively $`Q_n \equiv 0
\pmod p` for all $`n > n_0`. Re-running the computation with $`k = n > n_0`: now
each binomial term is divisible by $`p^2` except the constant terms summing to
$`p`, so
$$`\varphi^{n+1}(T) \equiv p\,\varphi^n(T)\big[p\cdot(\text{poly}) + 1\big] \pmod g,`
and $`p\cdot(\text{poly})+1` is a unit in $`V`. Therefore $`\varphi^{n+1}(T)V =
p\,\varphi^n(T)V`.
:::

:::corollary "mu-fg-torsion"
Let $`\sY` be a finitely generated $`\Lam`-module. If $`\sY/\varphi^n(T)\sY` is
finite for all $`n`, then $`\sY` is torsion. This uses {uses "mu-size-of-A"}[] and
{uses "characteristic-ideal"}[].
:::

:::proof "mu-fg-torsion"
By {uses "mu-size-of-A"}[], finiteness of all $`\sA/\varphi^n(T)` forces $`r = 0`
in the structure theorem, so the standard module $`\sA` is torsion — every element
is annihilated by its characteristic ideal {uses "characteristic-ideal"}[]. As
$`\sY` is quasi-isomorphic to such an $`\sA` (finite kernel and cokernel) and
torsionness is preserved under quasi-isomorphism, $`\sY` is torsion.
:::

This corollary is precisely the algebraic input promised at the outset: applied to
the modules of the {bpref "fundamental-exact-sequence"}[], it shows they are
finitely generated torsion $`\Lam`-modules, feeding the Iwasawa Main Conjecture
{bpref "iwasawa-main-conjecture"}[].

# Consequences

We have already seen one application (in stating the Main Conjecture): if one class
number in a $`\Zp`-extension is prime to $`p`, so are all the others. For a finite
abelian group $`A`, the *$`p`-rank* is $`\rk_p(A) = \dim_{\Fp}(A/pA) = \dim_{\Fp}(A[p])`,
the number of cyclic summands of $`p`-power order.

:::corollary "mu-rank-bounded"
Let $`F_\infty/F` be a $`\Zp`-extension. Then $`\mu = 0` if and only if
$`\rk_p(\Cl(F_n))` is bounded independently of $`n`. This uses
{uses "mu-size-of-A"}[].
:::

:::proof "mu-rank-bounded"
By {uses "mu-error-bounded"}[] and {uses "mu-Yn-quotient"}[], $`\Cl(F_n)\otimes\Zp =
\sY_n` sits in an exact sequence $`0 \to C_n \to \sY_n \to \sA_n \to B_n \to 0` with
$`\sA_n = \sA/\varphi^n(T)` and $`\abs{B_n}, \abs{C_n}` bounded; so it suffices to
bound $`\dim_{\Fp}(\sA_n/p\sA_n)`. Now
$$`\sA/(p,\varphi^n(T)) = \Big(\bigoplus_{i=1}^s \Lam/(p,\varphi^n(T))\Big) \oplus \Big(\bigoplus_{j=1}^t \Lam/(p,g_j,\varphi^n(T))\Big).`
For $`n` large that $`p^n \ge \deg g_j`, both $`g_j` and $`\varphi^n(T)` are
distinguished, so $`\Lam/(p,\varphi^n(T)) = \Lam/(p,T^{p^n})` and
$`\Lam/(p,g_j,\varphi^n(T)) = \Lam/(p,T^{\deg g_j})`. Hence the total is
$`(\Z/p\Z)^{s p^n + t g}` with $`g = \sum_j \deg g_j`, whose dimension is bounded in
$`n` iff $`s = 0`, i.e. iff $`\mu = \sum_i m_i = 0`.
:::

:::theorem "mu-ferrero-washington"
*(Ferrero–Washington.)* If $`F` is an abelian number field and $`F_\infty/F` is
its cyclotomic $`\Zp`-extension, then $`\mu = 0`.
:::

:::proof "mu-ferrero-washington"
The proof is genuinely analytic and orthogonal to the algebraic theory above. For
$`F` abelian over $`\Q`, the Iwasawa Main Conjecture identifies the characteristic
power series of the relevant component of $`\sY_\infty` with a branch of the
Kubota–Leopoldt $`p`-adic $`L`-function {uses "kubota-leopoldt"}[]; concretely,
each Dirichlet character $`\chi` of $`F` contributes a power series $`g_\chi(T) \in
\Zp[[T]]` interpolating the values $`L_p(\chi\omega^j, s)`, and the $`\mu`-invariant
of $`\sY_\infty` is the minimum over $`\chi` of the largest power of $`p` dividing
$`g_\chi`. Ferrero and Washington show this minimum is $`0`, i.e. that $`g_\chi` is
*not* divisible by $`p`, by exhibiting one coefficient that is a $`p`-adic unit. The
coefficients are explicit sums of fractional parts $`\{a/p^n\}` weighted by $`\chi`,
and the key input is a *normality* statement: the base-$`p` digits of these
generalised Bernoulli/Stickelberger expressions are equidistributed, so they cannot
all be divisible by $`p` simultaneously. Hence $`\mu = 0` for the analytic side, and
the Main Conjecture transports the vanishing to the algebraic module $`\sY_\infty`.
:::

:::definition "mu-greenberg-conjecture"
*(Greenberg's conjecture.)* For any totally real field $`F` and any
$`\Zp`-extension $`F_\infty/F`, one expects $`\mu = \lambda = 0`; equivalently, the
class numbers $`\#\Cl(F_n)` are bounded as $`n \to \infty`. This remains open.
:::
