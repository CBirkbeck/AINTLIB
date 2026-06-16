import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "What a p-adic L-function should be" =>

This chapter motivates the definition and study of $`p`-adic $`L`-functions. We
begin with the classical complex $`L`-functions, recall how special values encode
arithmetic, and then lean slowly towards the $`p`-adic world. The running example
— and the central object of these notes — is the Riemann zeta function. The
chapter closes by fixing the *interpolation property* that the Kubota–Leopoldt
$`p`-adic $`L`-function $`\zeta_p` must satisfy; constructing such an object is
the goal of the next several chapters.

Throughout, $`p` is a fixed prime and $`\ell` ranges over rational primes.

# Classical L-functions

:::definition "riemann-zeta" (lean := "riemannZeta")
The *Riemann zeta function* is
$$`\zeta(s) = \sum_{n\geq 1} n^{-s} = \prod_{\ell}\left(1 - \ell^{-s}\right)^{-1},`
the product — an *Euler product* — running over all primes $`\ell`; the second
equality expresses unique factorisation of integers. The sum converges absolutely
on the right half-plane $`\set{s\in\C : \mathrm{Re}(s) > 1}`, where it defines a
holomorphic function. It admits a meromorphic continuation to all of $`\C` and
satisfies a *functional equation* relating $`\zeta(s)` and $`\zeta(1-s)`.
:::

:::definition "mot-dedekind-zeta" (lean := "NumberField.dedekindZeta")
Let $`F` be a number field with ring of integers $`\roi_F`. The *Dedekind zeta
function of $`F`* is
$$`\zeta_F(s) = \sum_{0\neq I\subseteq\roi_F} \Nm(I)^{-s} = \prod_{\mathfrak p}\left(1 - \Nm(\mathfrak p)^{-s}\right)^{-1},`
where $`I` runs over the non-zero ideals of $`\roi_F` and $`\mathfrak p` over the
non-zero prime ideals. It converges for $`\mathrm{Re}(s)>1`, continues
meromorphically to $`\C`, and satisfies a functional equation relating $`\zeta_F(s)`
and $`\zeta_F(1-s)`. The Euler product again reflects unique factorisation of
ideals. (Mathlib's `NumberField.dedekindZeta` is exactly this Dirichlet series; the
meromorphic continuation is not yet formalised there, though the residue behaviour
at $`s=1` is.)
:::

:::definition "dirichlet-L-function" (lean := "DirichletCharacter.LFunction")
Let $`\chi:(\Z/N\Z)^{\times}\to\C^{\times}` be a Dirichlet character. Extend $`\chi`
to $`\chi:\Z\to\C` by $`\chi(m)=\chi(m\bmod N)` when $`(m,N)=1` and $`\chi(m)=0`
otherwise. The *Dirichlet $`L`-function of $`\chi`* is
$$`L(\chi,s) = \sum_{n\geq 1}\chi(n)n^{-s} = \prod_{\ell}\left(1 - \chi(\ell)\ell^{-s}\right)^{-1}.`
It converges for $`\mathrm{Re}(s)>1`, continues meromorphically to $`\C` (analytically
when $`\chi` is non-trivial), and satisfies a functional equation relating $`s` and
$`1-s`. The Riemann zeta function is the case $`\chi=1`.
:::

:::definition "mot-elliptic-L-function"
Let $`E/\Q` be an elliptic curve of conductor $`N`, and write
$`a_\ell(E)=\ell+1-\#E(\F_\ell)` for the trace of Frobenius at a good prime
$`\ell` (with $`\F_\ell` the field of $`\ell` elements). The *$`L`-function of $`E`* is
$$`L(E,s) = \sum_{n\geq 1}a_n(E)n^{-s} = \prod_{\ell\nmid N}\left(1 - a_\ell(E)\ell^{-s} + \ell^{1-2s}\right)^{-1}\prod_{\ell\mid N}L_\ell(s),`
the coefficients $`a_n(E)` being built recursively from the $`a_\ell(E)`, and the
bad Euler factors $`L_\ell(s)` depending on the reduction type at $`\ell`. The sum
converges for $`\mathrm{Re}(s)>3/2`, continues analytically to $`\C`, and satisfies a
functional equation relating $`s` and $`2-s`.
:::

:::definition "mot-modular-L-function"
Let $`f=\sum_{n\geq 1}a_n(f)q^n\in S_k(\Gamma_0(N),\Teich_f)` be a normalised
newform of weight $`k`, level $`N` and nebentypus $`\Teich_f`. The *$`L`-function
of $`f`* is
$$`L(f,s) = \sum_{n\geq 1}a_n(f)n^{-s} = \prod_{\ell\nmid N}\left(1 - a_\ell(f)\ell^{-s} + \Teich_f(\ell)\ell^{k-1-2s}\right)^{-1}\prod_{\ell\mid N}\left(1 - a_\ell(f)\ell^{-s}\right)^{-1}.`
It converges for $`\mathrm{Re}(s)>(k+1)/2`, continues analytically to $`\C`, and
satisfies a functional equation relating $`s` and $`k-s`.
:::

The examples above share three features that the *arithmetic* $`L`-functions of
interest should possess (each property can nonetheless be very deep):

- an Euler product converging absolutely in a right half-plane;
- a meromorphic continuation to all of $`\C`;
- a functional equation relating $`s` and $`k-s` for some $`k\in\R`.

:::definition "mot-galois-L-function"
More generally, let $`\cG_\Q=\Gal(\Qbar/\Q)` and let $`V` be a $`p`-adic Galois
representation, i.e. a finite-dimensional vector space over a finite extension $`L`
of $`\Qp` with a continuous linear $`\cG_\Q`-action. Its *global $`L`-function* is
the formal Euler product $`L(V,s)=\prod_\ell L_\ell(V,s)` of local factors. For
$`\ell\neq p` one sets
$$`L_\ell(V,s) = \det\!\left(\mathrm{Id} - \Frob_\ell^{-1}\ell^{-s}\,\middle|\, V^{I_\ell}\right)^{-1},`
with $`\Frob_\ell` the arithmetic Frobenius and $`I_\ell` the inertia at $`\ell`;
at $`\ell=p` one uses the crystalline module,
$`L_p(V,s)=\det(\mathrm{Id}-\varphi^{-1}p^{-s}\mid\Dcris(V))^{-1}`. When $`V` is the
representation attached to an arithmetic object the two notions of $`L`-function
agree; for $`V=\Qp(\chi)` one recovers the Dirichlet $`L`-function
{bpref "dirichlet-L-function"}[] of $`\chi`.
:::

# Special values and arithmetic

There are deep results and conjectures relating special values of $`L`-functions
to arithmetic invariants. A prototype is the class number formula.

:::theorem "mot-class-number-formula" (lean := "NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT")
Let $`F` be a number field with $`r_1` real embeddings, $`r_2` pairs of complex
embeddings, $`w` roots of unity, discriminant $`D`, regulator $`R` and class number
$`h_F`. Then $`\zeta_F` has a simple pole at $`s=1` with residue
$$`\Res_{s=1}\zeta_F(s) = \frac{2^{r_1}(2\pi)^{r_2}R}{w\sqrt{\abs{D}}}\,h_F.`
This rests on {uses "mot-dedekind-zeta"}[]. (Mathlib formalises this as the
statement that $`(s-1)\zeta_F(s)` tends to the displayed residue as
$`s \to 1^{+}` along the reals.)
:::

:::proof "mot-class-number-formula"
This is a classical analytic class number formula; we record it for motivation
rather than prove it. The left-hand side is an analytic invariant of the
meromorphic function $`\zeta_F`, while the right-hand side is a product of
arithmetic invariants of $`F`. The bridge between them comes from comparing the
Dirichlet series $`\zeta_F(s)` with a sum over lattice points in the ideal class
groups: the residue at $`s=1` counts ideals of bounded norm, which by the geometry
of numbers is governed by the covolume of the unit lattice (the regulator $`R`),
the number of roots of unity $`w`, the discriminant $`D`, and the number of ideal
classes $`h_F`.
:::

:::theorem "mot-bsd"
*(Birch–Swinnerton-Dyer conjecture.)* Let $`E/\Q` be an elliptic curve. Then the
Mordell–Weil group $`E(\Q)` is finitely generated, and
$$`\ord_{s=1}L(E,s) = \mathrm{rank}_{\Z}\,E(\Q).`
Moreover the leading Taylor coefficient of $`L(E,s)` at $`s=1` is given by an
explicit product of arithmetic invariants of $`E`. This concerns
{uses "mot-elliptic-L-function"}[].
:::

:::proof "mot-bsd"
This is an open conjecture, included to motivate the $`p`-adic theory; no proof is
claimed. As with the class number formula, the left-hand side is analytic and the
right-hand side arithmetic, and the two worlds are so different that even the
existence of the left-hand side — that $`L(E,s)` is defined at $`s=1` — requires
the analytic continuation supplied (over $`\Q`) by the modularity theorem. The
known low-rank cases proceed through Heegner points and Euler systems, which give
the two inequalities $`\ord_{s=1}L(E,s)\le\mathrm{rank}\,E(\Q)` and
$`\ge`, respectively, when the relevant Tate–Shafarevich group $`\Sha(E/\Q)[p^\infty]`
is finite. These same Iwasawa-theoretic tools are what the present notes develop
in the simpler setting of the Riemann zeta function.
:::

Iwasawa theory seeks $`p`-adic analogues of such statements, replacing complex
analysis (poorly suited to arithmetic) by $`p`-adic analysis (where arithmetic
arises naturally). For an elliptic curve $`E` and each prime $`p` there is an
*Iwasawa Main Conjecture* equating a $`p`-adic analytic $`L`-function with
$`p`-adic arithmetic invariants of $`E`; the bottom row of the BSD/IMC square is
far more tractable than the top, and the IMC for elliptic curves is known much
more widely (Kato; Skinner–Urban) than BSD itself. In these notes we treat the
simplest instance of the picture: the Main Conjecture for the $`p`-adic Riemann
zeta function, formulated by Iwasawa, which is known completely for every prime.

# The Riemann zeta function via the Mellin transform

The Riemann zeta function is the central player of these notes, so we recall how
its special values are computed. The tool is a general analytic-continuation
result for the Mellin transform.

:::theorem "mot-mellin-transform"
Let $`f:\R_{\geq 0}\to\R` be a rapidly decreasing $`\cC^{\infty}`-function (so $`f`
and all its derivatives decay exponentially at $`\infty`), and let
$`\Gamma(s)=\int_0^\infty e^{-t}t^{s-1}\,dt` be the Gamma function. The *Mellin
transform of $`f`* is
$$`L(f,s) := \frac{1}{\Gamma(s)}\int_0^\infty f(t)\,t^{s-1}\,dt,\qquad s\in\C.`
It converges to a holomorphic function for $`\mathrm{Re}(s)>0`, admits an analytic
continuation to all of $`\C`, and satisfies, for every $`n\geq 0`,
$$`L(f,-n) = (-1)^n f^{(n)}(0).`
:::

:::proof "mot-mellin-transform"
The key step is the recursion
$$`L(f,s) = -L(f',s+1),\qquad \mathrm{Re}(s)>1,`
obtained by integration by parts. Taking $`u=f(t)` and $`dv=t^{s-1}\,dt`, so
$`v=t^s/s`, gives
$`\int_0^\infty f(t)t^{s-1}\,dt = \big[f(t)t^s/s\big]_0^\infty -
\tfrac1s\int_0^\infty f'(t)\,t^s\,dt`. The boundary terms vanish: at $`\infty` by
the rapid decay of $`f`, at $`0` because $`\mathrm{Re}(s)>1`. Dividing by
$`\Gamma(s)` and using the functional equation $`\Gamma(s+1)=s\,\Gamma(s)` turns the
remaining integral into $`-\Gamma(s+1)^{-1}\int_0^\infty f'(t)t^{(s+1)-1}\,dt =
-L(f',s+1)`, which is the displayed recursion. Since $`f'` is again rapidly
decreasing, the right-hand side is holomorphic on $`\mathrm{Re}(s)>-1`, so the
recursion provides the analytic continuation of $`L(f,s)` one strip to the left;
iterating with $`f',f'',\dots` continues it to all of $`\C`. Applying the recursion
$`n+1` times gives $`L(f,-n)=(-1)^{n+1}L(f^{(n+1)},1)`, and since
$`L(g,1)=\Gamma(1)^{-1}\int_0^\infty g(t)\,dt=\int_0^\infty g(t)\,dt`, the
fundamental theorem of calculus yields
$`L(f,-n)=(-1)^{n+1}\int_0^\infty f^{(n+1)}(t)\,dt=(-1)^{n+1}\big[-f^{(n)}(0)\big]
=(-1)^n f^{(n)}(0)`, using once more that $`f^{(n)}` vanishes at $`\infty`.
:::

To recover $`\zeta` we apply this to the generating function of the Bernoulli
numbers,
$$`f(t) = \frac{t}{e^t-1} = \sum_{n\geq 0}B_n\frac{t^n}{n!}.`
The Bernoulli numbers $`B_n` are rational, with $`B_0=1`, $`B_1=-\tfrac12`,
$`B_2=\tfrac16`, $`B_3=0`, $`B_4=-\tfrac1{30},\dots`, and $`B_k=0` for odd $`k\geq 3`.

:::lemma_ "mot-bernoulli-decay"
The function $`f(t)=t/(e^t-1)` and all of its derivatives decay exponentially as
$`t\to\infty`.
:::

:::proof "mot-bernoulli-decay"
For $`t>0` expand as a geometric series
$`f(t)=t(e^{-t}+e^{-2t}+e^{-3t}+\cdots)=:tF(t)`. Differentiating $`f=tF`
repeatedly via the Leibniz rule gives $`f^{(n)}(t)=nF^{(n-1)}(t)+tF^{(n)}(t)`. Each
$`F^{(m)}(t)=(-1)^m(e^{-t}+2^m e^{-2t}+3^m e^{-3t}+\cdots)` is, term by term,
exponentially small, dominated by its leading term $`(-1)^m e^{-t}`. Hence
$`f^{(n)}(t)\sim(-1)^n t e^{-t}` as $`t\to\infty`, which decays exponentially.
:::

:::lemma_ "mot-formula-zeta"
For $`f(t)=t/(e^t-1)` as above, $`(s-1)\zeta(s) = L(f,s-1)`. This rests on
{uses "riemann-zeta"}[] and {uses "mot-mellin-transform"}[].
:::

:::proof "mot-formula-zeta"
Substituting $`t\mapsto nt` in the integral defining $`\Gamma(s)` gives
$`n^{-s}=\Gamma(s)^{-1}\int_0^\infty e^{-nt}t^{s-1}\,dt`. Summing over $`n\geq 1`
for $`\mathrm{Re}(s)` large and exchanging sum and integral,
$$`\zeta(s) = \frac{1}{\Gamma(s)}\sum_{n\geq 1}\int_0^\infty e^{-nt}t^{s-1}\,dt
= \frac{1}{\Gamma(s)}\int_0^\infty\Big(\sum_{n\geq 1}e^{-nt}\Big)\,t\cdot t^{s-2}\,dt.`
The geometric series gives $`\sum_{n\geq 1}e^{-nt}=1/(e^t-1)`, so the integrand is
$`\big(t/(e^t-1)\big)t^{s-2}=f(t)t^{(s-1)-1}`. Comparing with the definition of the
Mellin transform at the argument $`s-1` (whose $`\Gamma`-normalisation is
$`\Gamma(s-1)=\Gamma(s)/(s-1)`) yields $`\zeta(s)=L(f,s-1)/(s-1)`, i.e.
$`(s-1)\zeta(s)=L(f,s-1)`.
:::

:::corollary "special-values-zeta" (lean := "riemannZeta_neg_nat_eq_bernoulli'")
For every $`n\geq 0`,
$$`\zeta(-n) = -\frac{B_{n+1}}{n+1}.`
In particular $`\zeta(-n)\in\Q`, and $`\zeta(-n)=0` when $`n\geq 2` is even. This
rests on {uses "mot-formula-zeta"}[], {uses "mot-mellin-transform"}[] and
{uses "mot-bernoulli-decay"}[]. (At $`n=0` the formula implicitly uses the
convention $`B_1=+\tfrac12`; mathlib's `riemannZeta_neg_nat_eq_bernoulli'` states
exactly this, via the Bernoulli numbers $`B'_j` with $`B'_1=+\tfrac12`.)
:::

:::proof "special-values-zeta"
By {bpref "mot-bernoulli-decay"}[], $`f` is admissible in
{bpref "mot-mellin-transform"}[], so $`L(f,-m)=(-1)^m f^{(m)}(0)`. The Taylor
expansion $`f(t)=\sum_{j\geq 0}B_j t^j/j!` gives $`f^{(m)}(0)=B_m`, hence
$`L(f,-m)=(-1)^m B_m`. Now evaluate the identity $`(s-1)\zeta(s)=L(f,s-1)` from
{bpref "mot-formula-zeta"}[] at $`s=-n`: the left-hand side is
$`(-n-1)\zeta(-n)`, and the right-hand side is $`L(f,-n-1)=(-1)^{n+1}B_{n+1}`.
Therefore $`\zeta(-n)=(-1)^{n+1}B_{n+1}/(-n-1)=-B_{n+1}/(n+1)`. Since the $`B_j`
are rational, so is $`\zeta(-n)`; and as $`B_{n+1}=0` for $`n+1\geq 3` odd, i.e.
for $`n\geq 2` even, the value vanishes there.
:::

# p-adic L-functions: a first idea

The complex zeta function is an analytic map $`\zeta:\C\to\C` that is rational at
negative integers. Since $`\Z` sits inside both $`\C` and $`\Zp\subseteq\Cp`, it is
natural to look for a $`p`-adic analytic function
$$`\zeta_p:\Zp\longrightarrow\Cp`
agreeing with $`\zeta` at negative integers in the sense that, for some explicit
factor $`(*)`,
$$`\zeta_p(1-n) = (*)\cdot\zeta(1-n).`
One then says $`\zeta_p` *$`p`-adically interpolates the special values of $`\zeta`*,
and ideally these properties characterise $`\zeta_p` uniquely.

In fact there is no *single* analytic function on $`\Zp` interpolating all the
special values; the obstruction is the Teichmüller decomposition of $`\Zpx`, and a
clean way to organise the problem is the idelic viewpoint of Tate (and,
independently, Iwasawa), which packages all Dirichlet $`L`-functions — the Riemann
zeta function included — into a single object.

:::proposition "mot-dirichlet-ideles"
The following hold.

(i) Dirichlet characters are in natural bijection with continuous characters
$`\chi:\prod_{\ell}\Z_\ell^{\times}\to\C^{\times}`, the source carrying the product
of the $`\ell`-adic topologies.

(ii) There is an identification $`\C\cong\Homc(\R_{>0},\C^{\times})` sending $`s`
to $`x\mapsto x^s`.

Consequently each pair $`(\chi,s)` corresponds to the unique continuous character
$$`\kappa_{\chi,s}:\R_{>0}\times\prod_{\ell}\Z_\ell^{\times}\to\C^{\times},
\qquad (x,y)\mapsto x^s\chi(y),`
and every continuous character of this group has this form.
:::

:::proof "mot-dirichlet-ideles"
*(i)* A Dirichlet character $`\chi:(\Z/N\Z)^{\times}\to\C^{\times}` induces a
character of $`\prod_\ell\Z_\ell^{\times}`: when $`N=\ell^n` we use
$`(\Z/\ell^n\Z)^{\times}\cong\Z_\ell^{\times}/(1+\ell^n\Z_\ell)` to inflate $`\chi`
to $`\Z_\ell^{\times}`, and the general case follows by the Chinese remainder
theorem. Conversely, any continuous $`\chi:\prod_\ell\Z_\ell^{\times}\to\C^{\times}`
is trivial on some neighbourhood
$`U_N=\set{x : x\equiv 1\ (\mathrm{mod}\ N)}` of $`1`: its image lies in
$`\set{z\in\C : \abs{z-1}<1}`, whose only compact subgroup is $`\set{1}`. Thus
$`\chi` factors through the finite quotient
$`(\prod_\ell\Z_\ell^{\times})/U_N=(\Z/N\Z)^{\times}`, giving a Dirichlet
character. The two constructions are mutually inverse.

*(ii)* Each $`x\mapsto x^s` is a continuous character of $`\R_{>0}`. Conversely,
taking logarithms reduces the claim to: every continuous additive homomorphism
$`g:\R\to\C` has the form $`g(x)=x\,g(1)`. This holds on $`\Q` by additivity and
extends to $`\R` by continuity.
:::

:::definition "mot-ideles"
The *ideles* of $`\Q` are the restricted product
$$`\A^{\times} := \R^{\times}\times{\prod_{\ell}}'\,\Q_\ell^{\times}
= \set{(x_\R,x_2,x_3,\dots) : x_\ell\in\Z_\ell^{\times}\text{ for almost all }\ell},`
a topological ring with the restricted-product topology (a basis of neighbourhoods
$`U\times\prod_\ell U_\ell` with $`U\subseteq\R^{\times}`,
$`U_\ell\subseteq\Q_\ell^{\times}` open and $`U_\ell=\Z_\ell^{\times}` for almost
all $`\ell`). The units $`\Q^{\times}` embed diagonally, $`x\mapsto(x,x,\dots)`, and
$`\Q^{\times}\backslash\A^{\times}` is the *idele class group* of $`\Q`.
:::

:::proposition "mot-strong-approximation"
*(Strong approximation.)* There is a topological isomorphism
$$`\Q^{\times}\backslash\A^{\times}\cong\R_{>0}\times\prod_{\ell}\Z_\ell^{\times}.`
Hence every continuous character $`\Q^{\times}\backslash\A^{\times}\to\C^{\times}`
is of the form $`\kappa_{\chi,s}` for a Dirichlet character $`\chi` and $`s\in\C`.
This rests on {uses "mot-ideles"}[] and {uses "mot-dirichlet-ideles"}[].
:::

:::proof "mot-strong-approximation"
The isomorphism is the idelic strong approximation theorem for $`\Q`: every idele
class has a unique representative whose finite components lie in
$`\prod_\ell\Z_\ell^{\times}` and whose archimedean component is positive,
obtained by clearing denominators against the diagonal copy of $`\Q^{\times}` and
absorbing the sign. Combined with the classification of characters in
{bpref "mot-dirichlet-ideles"}[], every continuous character of the idele class
group is $`\kappa_{\chi,s}`.
:::

Through the identification $`\C\cong\Homc(\R_{>0},\C^{\times})` one may regard
$`\zeta` as the function $`[x\mapsto x^s]\mapsto\zeta(s)`. More strikingly, by
strong approximation *all* Dirichlet $`L`-functions are values of the single
function
$$`L:\Homc(\Q^{\times}\backslash\A^{\times},\C^{\times})\to\C,\qquad
\kappa_{\chi,s}\mapsto L(\chi,s).`
In Tate's framework $`L` integrates $`\kappa_{\chi,s}` against the Haar measure on
the idele class group; this measure-theoretic viewpoint yields analytic
continuation and functional equations, with the $`\Gamma`-factors and powers of
$`2\pi i` appearing as the Euler factor at the archimedean place.

# p-adic L-functions via measures

To $`p`-adicise the idelic picture one replaces $`\C` by $`\Cp` and studies
$`\Homc(\Q^{\times}\backslash\A^{\times},\Cp^{\times})`. Since $`\R_{>0}` is
connected and $`\Cp` is totally disconnected, any such character is trivial on
$`\R_{>0}`; topological arguments show its restriction to
$`\prod_{\ell\neq p}\Z_\ell^{\times}` factors through a finite quotient, hence comes
from a Dirichlet character of conductor prime to $`p`. The interesting part is the
restriction to $`\Zpx`, i.e. $`\Homc(\Zpx,\Cp^{\times})`. We therefore seek a
$`p`-adic analytic function
$$`\zeta_p:\Homc(\Zpx,\Cp^{\times})\to\Cp`
that *sees* the special values of $`\zeta` in the sense that, for an explicit factor
$`(*)`,
$$`\zeta_p(x\mapsto x^k) = (*)\cdot\zeta(1-k),\qquad k\geq 1.`

The right notion of "$`p`-adic analytic" object here is a {bpref "p-adic-measure"}[$`p`-adic measure]
(or {bpref "pseudo-measure"}[pseudo-measure]) on $`\Zpx`, developed in the chapter
on measures. With that language in hand, the construction culminates in the
following theorem, the goal of Part I.

:::theorem "mot-kubota-leopoldt-goal"
*(Kubota–Leopoldt, Iwasawa.)* There exists a unique pseudo-measure $`\zeta_p` on
$`\Zpx` such that, for all integers $`k>0`,
$$`\int_{\Zpx} x^k\cdot\zeta_p \;=\; \zeta_p(x\mapsto x^k) \;=\; \big(1-p^{k-1}\big)\,\zeta(1-k).`
This is the object constructed in the chapter on $`\zeta_p` as the
{uses "kubota-leopoldt"}[], and rests on {uses "special-values-zeta"}[],
{uses "p-adic-measure"}[], {uses "pseudo-measure"}[] and the
{uses "interpolation-property"}[].
:::

:::proof "mot-kubota-leopoldt-goal"
This is a forward reference to the central construction of these notes; the full
argument occupies the chapters on the construction of $`\zeta_p` and its
interpolation. The spine is as follows. The special values
$`\zeta(1-k)=-B_k/k` lie in $`\Q`, hence in $`\Cp`, by
{bpref "special-values-zeta"}[]. The Euler factor $`1-p^{k-1}` is exactly the
inverse of the local factor $`(1-\ell^{-s})^{-1}` of {bpref "riemann-zeta"}[] at
$`\ell=p`, evaluated at $`s=1-k`; thus the theorem $`p`-adically interpolates the
*$`p`-deprived* zeta function. One builds explicit measures $`\mu_a` on $`\Zp`,
restricts them to $`\Zpx`, and rescales away the auxiliary parameter $`a` to
produce $`\zeta_p`; the interpolation formula is then verified by integrating the
monomials $`x^k` against the Mahler/Mellin description of the measure. Uniqueness
holds because the monomials $`x^k`, $`k>0`, are dense enough in the space of
continuous characters to pin down a pseudo-measure.
:::

The factor $`1-p^{k-1}` is the inverse of the Euler factor at $`p` of
$`\zeta(s)=\prod_\ell(1-\ell^{-s})^{-1}` at $`s=1-k`. Although the Euler product
diverges at $`s=1-k`, {bpref "mot-kubota-leopoldt-goal"}[] morally says that after
*removing the factor at $`p`* the Riemann zeta function interpolates $`p`-adically.
This $`p`-stabilisation is a general feature of the theory.

Although $`\zeta_p` is built using only values of $`\zeta` — with no reference to
Dirichlet characters — the measure-theoretic viewpoint gives far more: the same
pseudo-measure simultaneously interpolates *all* Dirichlet $`L`-functions of
$`p`-power conductor.

:::theorem "mot-interp-dirichlet-ppower"
Let $`\chi` be a Dirichlet character of conductor $`p^n`, $`n\geq 0`, viewed as a
locally constant character on $`\Zpx`. Then for all $`k>0`,
$$`\int_{\Zpx}\chi(x)\,x^k\cdot\zeta_p \;=\; \big(1-\chi(p)p^{k-1}\big)\,L(\chi,1-k).`
This rests on {uses "mot-kubota-leopoldt-goal"}[],
{uses "dirichlet-L-function"}[] and the {uses "interpolation-property"}[].
:::

:::proof "mot-interp-dirichlet-ppower"
This is the character-twisted interpolation property, proved in the interpolation
chapter. The point is that integrating against the locally constant character
$`\chi` only modifies the measure $`\zeta_p` on the cosets of
$`1+p^n\Zp` in $`\Zpx`; reorganising the resulting finite sum of partial integrals
reconstitutes the Dirichlet series $`L(\chi,1-k)`, while the local factor at $`p`
becomes $`1-\chi(p)p^{k-1}` (with $`\chi(p)=0` when $`p\mid` conductor). Since
$`\zeta_p` was defined using untwisted values only, that it also encodes twisted
values is genuinely surprising.
:::

:::theorem "mot-interp-dirichlet-tame"
Let $`D>1` be coprime to $`p` and let $`\eta` be a primitive Dirichlet character of
conductor $`D`. There is a unique measure $`\zeta_\eta` on $`\Zpx` such that, for
every primitive Dirichlet character $`\chi` of conductor $`p^n`, $`n\geq 0`, and all
$`k>0`,
$$`\int_{\Zpx}\chi(x)\,x^k\cdot\zeta_\eta \;=\; \big(1-\chi\eta(p)p^{k-1}\big)\,L(\chi\eta,1-k).`
This rests on {uses "mot-interp-dirichlet-ppower"}[] and
{uses "dirichlet-L-function"}[].
:::

:::proof "mot-interp-dirichlet-tame"
The tame character $`\eta` of conductor prime to $`p` is incorporated by an
auxiliary twist of the construction of $`\zeta_p`, again realised as a $`p`-adic
measure on $`\Zpx`. As $`\eta` ranges over characters of conductor prime to $`p`
the measures $`\zeta_\eta` are compatible under the natural maps
$`(\Z/E\Z)^{\times\wedge}\to(\Z/D\Z)^{\times\wedge}` for $`E\mid D`, so they assemble
into a single function on
$`\Homc(\Zpx,\Cp^{\times})\times(\prod_{\ell\neq p}\Z_\ell^{\times})^{\wedge}
=\Homc(\Q^{\times}\backslash\A^{\times},\Cp^{\times})`. This is precisely the
$`p`-adic counterpart of the idelic function
$`L:\kappa_{\chi,s}\mapsto L(\chi,s)`: a measure on the idele class group of $`\Q`.
:::

:::proposition "kummer-congruences"
*(Generalised Kummer congruences.)* Let $`\eta` be a Dirichlet character of
conductor prime to $`p`. If $`k\equiv j\ (\mathrm{mod}\ p^{m-1}(p-1))` with $`k,j>0`,
then the $`p`-stabilised special values satisfy
$$`\big(1-\eta(p)p^{k-1}\big)L(\eta,1-k) \equiv \big(1-\eta(p)p^{j-1}\big)L(\eta,1-j)\ \ (\mathrm{mod}\ p^m).`
For $`\eta=1` these are the classical Kummer congruences for the Riemann zeta
function. This rests on {uses "special-values-zeta"}[] and
{uses "mot-interp-dirichlet-tame"}[].
:::

:::proof "kummer-congruences"
The congruence $`k\equiv j\ (\mathrm{mod}\ p^{m-1}(p-1))` forces
$`x^k\equiv x^j\ (\mathrm{mod}\ p^m)` for every $`x\in\Zpx`, because the finite
quotient $`\Zpx/(1+p^m\Zp)\cong(\Z/p^m\Z)^{\times}` has order $`p^{m-1}(p-1)`, so
raising to the exponent kills the difference $`k-j`. Hence the two locally
constant functions $`x\mapsto\eta(x)x^k` and $`x\mapsto\eta(x)x^j` are congruent
modulo $`p^m` pointwise on $`\Zpx`. Integrating both against the measure
$`\zeta_\eta` of {bpref "mot-interp-dirichlet-tame"}[] — whose values are
$`p`-adic integers up to the bounded denominators of a measure — and using the
interpolation formula
$`\int_{\Zpx}\eta(x)x^k\cdot\zeta_\eta=(1-\eta(p)p^{k-1})L(\eta,1-k)` yields the
displayed congruence. These congruences underlie Kummer's classification of
irregular primes and were the historical motivation for
{bpref "mot-kubota-leopoldt-goal"}[]; they give the complementary view of $`p`-adic
$`L`-functions as analytic objects packaging systematic congruences between
$`L`-values.
:::
