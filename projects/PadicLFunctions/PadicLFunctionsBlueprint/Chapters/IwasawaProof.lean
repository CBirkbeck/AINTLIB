import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Proof of Iwasawa theorem" =>

This chapter proves *Iwasawa's theorem*, namely that the Coleman map induces an
isomorphism of $`\Lam(\GGam^+)`-modules
$$`\sU^+_{\infty,1}/\CC^+_{\infty,1} \;\xrightarrow{\sim}\; \Lam(\GGam^+)/I(\GGam^+)\zeta_p.`
The strategy has four movements. First we put a $`\Lam(\GGam)`-module structure on
the norm-coherent local units $`\sU_{\infty,1}` and show the Coleman map is
equivariant for it. Next we compute the kernel and cokernel of the Coleman map by
analysing each constituent map; this is the *fundamental exact sequence*. Then we
exhibit explicit cyclic generators of the global and local cyclotomic units over
the relevant group rings. Finally we feed the generators through the Coleman map
to read off the image of the cyclotomic units, and conclude.

Throughout, $`p` is an odd prime, $`F_\infty = \Q(\mu_{p^\infty})`,
$`\GGam = \Gal(F_\infty/\Q) \cong \Zpx` via the cyclotomic character $`\chi`, and
$`\GGam^+` is the quotient by complex conjugation. We write
$`K_n = \Qp(\mu_{p^n})`, $`\pi_n = \xi_{p^n}-1` for a uniformiser, $`\sU_n` for
the local units of $`K_n`, $`\sU_{n,1}` for those congruent to $`1` modulo
$`\pri_n`, and $`\sU_\infty = \varprojlim_n \sU_n`,
$`\sU_{\infty,1} = \varprojlim_n \sU_{n,1}` for the norm-coherent towers. Recall
the Coleman map is the composition
$$`\Col : \sU_\infty \xrightarrow{u\mapsto f_u} (\Zp[[T]]^\times)^{\cN=\mathrm{id}}
\xrightarrow{\dlog} \Zp[[T]] \xrightarrow{1-\varphi\circ\psi} \Zp[[T]]^{\psi=0}
\xrightarrow{\partial^{-1}} \Zp[[T]]^{\psi=0} \xrightarrow{\sA^{-1}} \Lam(\Zpx),`
where $`\sA` is the Mahler transform identifying measures with power series.

# Equivariance properties of the Coleman map

Iwasawa's theorem is a statement about $`\Lam(\GGam^+)`-modules, so it is essential
to work over the *full* Iwasawa algebra rather than just $`\Zp`. Since
$`\Lam(\GGam)` is the completed group ring of $`\GGam` over $`\Zp`, giving
$`\sU_\infty` a $`\Lam(\GGam)`-module structure amounts to equipping it with
compatible actions of $`\Zp` and of $`\GGam`. The Galois group acts naturally; the
obstruction is the $`\Zp`-action, since the integer power map $`u\mapsto u^a` does
not extend continuously from $`\Z` to $`\Zp` on all of $`\sU_\infty`.

:::proposition "iwproof-zp-action"
The Coleman map restricts to a $`\Zp`-equivariant map
$$`\Col : \sU_{\infty,1} \longrightarrow \Lam(\Zpx),`
where $`a\in\Zp` acts on $`u\in\sU_{\infty,1}` by the convergent binomial series
$`u^a := \sum_{k\ge 0}\binom{a}{k}(u-1)^k`.
:::

:::proof "iwproof-zp-action"
It suffices to check $`\Zp`-equivariance of each map in the composition defining
$`\Col`, depending on {uses "coleman-map"}[]. The point is that the binomial
series converges precisely on $`\sU_{\infty,1}`. Writing $`f_u=\sum_{k\ge 0}a_k(u)T^k`
for the Coleman power series of $`u`, one checks $`a_0(u)\equiv 1 \pmod{p}`: indeed
$`f_u(\pi_n)=u_n\equiv 1 \pmod{\pri_n}` and, $`\pi_n` being a uniformiser, this
forces $`a_0(u)\equiv 1 \pmod{\pri_n}`; as $`a_0(u)\in\Zp` we get the congruence.
Hence $`f_u-1\in(p,T)`, and by $`(p,T)`-adic completeness of $`\Zp[[T]]` the series
$`f_u^a=\sum_{j\ge 0}\binom{a}{j}(f_u-1)^j` converges. Since
$`f_u(\pi_n)^a=u_n^a`, the uniqueness of Coleman power series {uses "coleman-theorem"}[]
gives $`f_u^a=f_{u^a}`, so $`u\mapsto f_u` is $`\Zp`-equivariant. The logarithmic
derivative satisfies $`\dlog(f_u^a)=a\,\dlog(f_u)`, hence is equivariant for the
natural $`\Zp`-action on $`\Zp[[T]]`; and $`1-\varphi\circ\psi`, $`\partial^{-1}` and
$`\sA^{-1}` are $`\Zp`-linear by definition. Composing, $`\Col` is $`\Zp`-equivariant
on $`\sU_{\infty,1}`.
:::

:::lemma_ "iwproof-units-split"
There is a direct product decomposition $`\sU_\infty = \mu_{p-1}\times\sU_{\infty,1}`.
:::

:::proof "iwproof-units-split"
At each finite level $`n`, since $`p` is totally ramified in $`K_n` there is a
unique prime $`\pri_n` above $`p`, and reduction modulo $`\pri_n` gives a short
exact sequence $`1\to\sU_{n,1}\to\sU_n\to\mu_{p-1}\to 1`. The Teichmüller lift
splits it, so $`\sU_n=\mu_{p-1}\times\sU_{n,1}`. Passing to the inverse limit over
$`n` gives the claim.
:::

:::lemma_ "iwproof-mu-killed" (lean := "PadicLFunctions.Coleman.Col_eq_zero_of_torsion")
The subgroup $`\mu_{p-1}\subset\sU_\infty` is killed by the Coleman map. In
particular no information is lost in restricting $`\Col` to $`\sU_{\infty,1}`.
:::

:::proof "iwproof-mu-killed"
A root of unity $`v\in\mu_{p-1}\subset\Zpx`, viewed as the constant tower
$`(v)_n`, has constant Coleman power series $`f_v(T)=v`. Constant series are killed
by the logarithmic derivative $`\dlog`, which differentiates. Hence $`v` maps to
$`0` under $`\Col`. Using {uses "iwproof-units-split"}[], this shows the
restriction to $`\sU_{\infty,1}` loses nothing.
:::

:::lemma_ "iwproof-ker-dlog" (lean := "PadicLFunctions.Coleman.dlog_eq_zero_normOp_fixed")
The kernel of $`\dlog` on $`\Zp[[T]]^\times` consists of the constant series.
Consequently the kernel of $`\dlog` restricted to
$`\WW=(\Zp[[T]]^\times)^{\cN=\mathrm{id}}` is exactly $`\mu_{p-1}`.
:::

:::proof "iwproof-ker-dlog"
Since $`\dlog f=(1+T)f'/f`, we have $`\dlog f=0` iff $`f'=0` iff $`f` is a constant
$`c`. For a constant, the defining relation of the norm operator,
$`\varphi(\cN f)=\prod_{\eta\in\mu_p}f((1+T)\eta-1)`, reads $`\varphi(\cN c)=c^p`;
as $`\varphi` is the identity on constants this gives $`\cN(c)=c^p`. Hence
$`\cN`-invariance forces $`c^p=c`, and since $`c` is a unit this means
$`c\in\mu_{p-1}`. Conversely every $`c\in\mu_{p-1}` is a constant, lies in $`\WW`,
and is killed by $`\dlog`. Therefore $`\ker(\dlog|_\WW)=\mu_{p-1}`.
:::

The Galois group $`\GGam=\Gal(F_\infty/\Q)\cong\Gal(K_\infty/\Qp)` acts on
$`\sU_\infty`. For $`a\in\Zpx` we write $`\sigma_a\in\GGam` for the element with
$`\chi(\sigma_a)=a`.

:::proposition "iwproof-galois-equiv" (lean := "PadicLFunctions.Coleman.Col_galNCU")
The Coleman map $`\Col : \sU_\infty \to \Lam(\GGam)` is $`\GGam`-equivariant: for all
$`a\in\Zpx` and $`u\in\sU_\infty`, $`\Col(\sigma_a u) = \sigma_a\,\Col(u)`.
:::

:::proof "iwproof-galois-equiv"
One checks equivariance map-by-map, using that $`\sigma_a` acts on a power series
by $`f(T)\mapsto f((1+T)^a-1)`. For $`u\mapsto f_u`: evaluating
$`(\sigma_a f_u)(\pi_n)=f_u((1+\pi_n)^a-1)=f_u(\xi_{p^n}^a-1)=\sigma_a(u_n)`, so it is
equivariant. The logarithmic derivative satisfies the twisted relation
$`\dlog(\sigma_a f)=a\,\sigma_a(\dlog f)`. On measures, restriction to $`\Zpx`
commutes with $`\sigma_a` since multiplying the variable by $`a\in\Zpx` stabilises
both $`\Zpx` and $`p\Zp`. The operator $`\partial^{-1}` obeys
$`\partial^{-1}\circ\sigma_a=a^{-1}\sigma_a\circ\partial^{-1}`, checked on measures
via $`\int_{\Zpx} f\,\partial^{-1}\sigma_a\mu=\int_{\Zpx}\tfrac{f(ax)}{ax}\mu`.
Finally $`\sA^{-1}` is equivariant by definition. The factor $`a` from $`\dlog`
cancels the factor $`a^{-1}` from $`\partial^{-1}`, leaving $`\Col` equivariant.
This depends on {uses "coleman-map"}[].
:::

Since the $`\GGam`-action fixes $`1\in\mu_{p-1}` it stabilises $`\sU_{\infty,1}`, and
this action commutes with the $`\Zp`-action there. Hence $`\sU_{\infty,1}` is a
$`\Lam(\GGam)`-module, and we may summarise the section as follows.

:::corollary "coleman-equivariance" (lean := "PadicLFunctions.Coleman.Col_lambdaG_equivariant")
The Coleman map restricts to a homomorphism of $`\Lam(\GGam)`-modules
$$`\Col : \sU_{\infty,1} \longrightarrow \Lam(\GGam).`
:::

:::proof "coleman-equivariance"
Combine {uses "iwproof-zp-action"}[] ($`\Zp`-equivariance on $`\sU_{\infty,1}`) with
{uses "iwproof-galois-equiv"}[] ($`\GGam`-equivariance). The two actions commute and
together generate the $`\Lam(\GGam)`-action, so $`\Col` is $`\Lam(\GGam)`-linear.
:::

*Remark.* The renormalisation "divide by $`x`" used in constructing $`\zeta_p`
reappears here as $`\partial^{-1}`. The relation
$`\partial^{-1}\circ\sigma_a=a^{-1}\sigma_a\circ\partial^{-1}` shows $`\partial^{-1}`
is exactly what makes $`\Col` $`\GGam`-equivariant. Conceptually $`\zeta` and
$`\zeta_p` are the $`L`-functions of the trivial Galois representation, the
cyclotomic units form an Euler system for the twist $`\Qp(1)`, and $`\partial^{-1}`
bridges the two.

# The fundamental exact sequence

We now compute the kernel and cokernel of the Coleman map. The factor
$`u\mapsto f_u` is an isomorphism and the last two maps $`\partial^{-1}`,
$`\sA^{-1}` are isomorphisms, so everything reduces to the two middle maps: the
logarithmic derivative $`\Delta=\dlog`, and $`1-\varphi\circ\psi`.

:::definition "iwproof-log-der" (lean := "PadicLFunctions.Coleman.dlog")
For $`f\in\Zp[[T]]^\times` the *logarithmic derivative* is
$$`\Delta(f) := \dlog f = \frac{\partial f}{f} = (1+T)\frac{f'(T)}{f(T)} \in \Zp[[T]].`
:::

:::theorem "iwproof-log-der-seq" (lean := "PadicLFunctions.Coleman.dlog_surjective_onto_psiId, PadicLFunctions.Coleman.dlog_mem_psiIdSeries, PadicLFunctions.Coleman.dlog_eq_zero_normOp_fixed")
The logarithmic derivative induces a short exact sequence
$$`0 \to \mu_{p-1} \to \big(\Zp[[T]]^\times\big)^{\cN=\mathrm{id}}
\xrightarrow{\ \Delta\ } \Zp[[T]]^{\psi=\mathrm{id}} \to 0.`
:::

:::proof "iwproof-log-der-seq"
The kernel is $`\mu_{p-1}` by {uses "iwproof-ker-dlog"}[]. Well-definedness, i.e.
$`\Delta(\WW)\subseteq\Zp[[T]]^{\psi=\mathrm{id}}` for $`\WW=(\Zp[[T]]^\times)^{\cN=\mathrm{id}}`,
is {uses "iwproof-log-der-image"}[]. For surjectivity, {uses "iwproof-log-der-modp"}[]
reduces the problem to equality modulo $`p` of the reductions $`A=\overline{\Delta(\WW)}`
and $`B=\overline{\Zp[[T]]^{\psi=\mathrm{id}}}`. That equality is supplied by
{uses "iwproof-W-modp"}[], which computes $`\overline{\WW}=\Fp[[T]]^\times`, and
{uses "iwproof-B-modp"}[], which computes $`B=\Delta(\Fp[[T]]^\times)`; together
they give $`A=B`.
:::

:::lemma_ "iwproof-log-der-image" (lean := "PadicLFunctions.Coleman.dlog_mem_psiIdSeries")
With $`\WW=(\Zp[[T]]^\times)^{\cN=\mathrm{id}}`, we have
$`\Delta(\WW)\subseteq\Zp[[T]]^{\psi=\mathrm{id}}`.
:::

:::proof "iwproof-log-der-image"
For $`f\in\WW`, norm-invariance gives
$`\varphi(f)=(\varphi\circ\cN)(f)=\prod_{\eta\in\mu_p}f((1+T)\eta-1)`. Applying
$`\Delta` and using the identity $`\Delta\circ\varphi=p\,\varphi\circ\Delta` (immediate
from the definitions on power series), the right-hand side becomes
$`p^{-1}\sum_{\eta\in\mu_p}\Delta(f)((1+T)\eta-1)=(\varphi\circ\psi)(\Delta f)`. Thus
$`\varphi(\Delta f)=\varphi(\psi(\Delta f))`, and injectivity of $`\varphi` yields
$`\psi(\Delta f)=\Delta f`.
:::

:::lemma_ "iwproof-log-der-modp"
If $`A=B` as submodules of $`\Fp[[T]]`, then
$`\Delta(\WW)=\Zp[[T]]^{\psi=\mathrm{id}}`.
:::

:::proof "iwproof-log-der-modp"
This is a successive-approximation argument. Given
$`f_0\in\Zp[[T]]^{\psi=\mathrm{id}}`, the hypothesis $`A=B` produces $`g_1\in\WW` with
$`\Delta(g_1)-f_0=pf_1`; since $`\psi` fixes $`\Delta(g_1)` (by
{uses "iwproof-log-der-image"}[]) and $`f_0`, it fixes $`f_1`, so we may iterate,
obtaining $`g_i\in\WW` and $`\psi`-fixed $`f_i` with $`\Delta(g_i)-f_{i-1}=pf_i`. Set
$`h_n=\prod_{k=1}^{n} g_k^{(-1)^{k-1}p^{k-1}}\in\WW`. Because $`\Delta` turns products
into sums, the telescoping cancellation gives
$`\Delta(h_n)=f_0+(-1)^{n-1}p^{n}f_n`. By compactness of $`\WW`, a subsequence of
$`(h_n)` converges to some $`h\in\WW` with $`\Delta(h)=f_0`.
:::

:::lemma_ "iwproof-W-modp" (lean := "PadicLFunctions.Coleman.exists_normOp_fixed_lift")
The reduction modulo $`p` of $`\WW=(\Zp[[T]]^\times)^{\cN=\mathrm{id}}` is
$`\overline{\WW}=\Fp[[T]]^\times`.
:::

:::proof "iwproof-W-modp"
The inclusion $`\overline{\WW}\subseteq\Fp[[T]]^\times` is clear. Conversely lift
$`f\in\Fp[[T]]^\times` to $`\tilde f_0\in\Zp[[T]]^\times`; by continuity and
contraction properties of the norm operator $`\cN`, the sequence $`\cN^k(\tilde f_0)`
converges to a $`\cN`-invariant element whose reduction modulo $`p` is $`f`.
:::

:::lemma_ "iwproof-B-modp"
We have $`B=\overline{\Zp[[T]]^{\psi=\mathrm{id}}}=\Delta(\Fp[[T]]^\times)` inside
$`\Fp[[T]]`.
:::

:::proof "iwproof-B-modp"
The inclusion $`\Delta(\Fp[[T]]^\times)\subseteq B` follows from
{uses "iwproof-log-der-image"}[] and {uses "iwproof-W-modp"}[]. For the reverse, take
$`f\in B` and use {uses "iwproof-B-modp-decomp"}[] to write $`f=\Delta(a)+b` with
$`a\in\Fp[[T]]^\times` and $`b=\sum_{m\ge 1} d_m\tfrac{T+1}{T}T^{pm}`. Both $`f` and
$`\Delta(a)` are $`\psi`-fixed, so $`\psi(b)=b`. Using
$`\psi(g\cdot\varphi(f))=\psi(g)f`, the relation $`T^{pm}=\varphi(T^m)`, and
$`\psi`-invariance of $`\tfrac{T+1}{T}`, one computes
$`\psi(b)=\sum_m d_m\tfrac{T+1}{T}T^m`. Comparing with $`b` forces every $`d_m=0`, so
$`b=0` and $`f=\Delta(a)`.
:::

:::lemma_ "iwproof-B-modp-decomp" (lean := "PadicLFunctions.Coleman.fp_series_eq_dlog_add_frobC")
In $`\Fp[[T]]` there is a decomposition
$$`\Fp[[T]] = \Delta\big(\Fp[[T]]^\times\big) + \frac{T+1}{T}\,C,\qquad
C=\Big\{\sum_{n\ge 1} a_n T^{pn}\Big\}.`
:::

:::proof "iwproof-B-modp-decomp"
One inclusion is clear. Given $`g`, write $`\tfrac{T}{T+1}g=\sum_{n\ge 1}a_nT^n` and set
$`h=\sum_{(m,p)=1} a_m\sum_{k\ge 0}T^{mp^k}`; then $`\tfrac{T}{T+1}g-h\in C`, so it
suffices to realise $`\tfrac{T+1}{T}h` as a logarithmic derivative. Using
$`\Delta(1-\alpha T^i)=-\tfrac{T+1}{T}\sum_{k\ge 1} i\alpha^k T^{ik}`, one builds, by
induction on $`m`, coefficients $`\alpha_m\in\Fp` killing the lowest surviving term:
where the coefficient $`d_m` of $`\tfrac{T+1}{T}\sum_k d_kT^k` is nonzero, the
periodicity $`d_n=d_{np}` forces $`(m,p)=1`, so $`m` is invertible and one sets
$`\alpha_m=-d_m/m`. The infinite product $`g=\prod_{n\ge 1}(1-\alpha_nT^n)` then
satisfies $`\Delta(g)=\tfrac{T+1}{T}h`.
:::

We have now understood $`\Delta`; the last constituent map to analyse is
$`1-\varphi\circ\psi`, which by the logarithmic-derivative sequence we need only
study on $`\Zp[[T]]^{\psi=\mathrm{id}}`.

:::lemma_ "iwproof-rest-zpx"
There is an exact sequence
$$`0 \to \Zp \to \Zp[[T]]^{\psi=\mathrm{id}} \xrightarrow{\ 1-\varphi\ }
\Zp[[T]]^{\psi=0} \to \Zp \to 0,`
where the first map is the inclusion of constants and the last is evaluation at
$`T=0`.
:::

:::proof "iwproof-rest-zpx"
Injectivity of the inclusion is trivial. For surjectivity of evaluation, note
$`\psi(1+T)=0` (since $`\varphi\psi(1+T)=p^{-1}\sum_{\eta\in\mu_p}\eta(1+T)=0`), and
$`1+T` maps to $`1`. For exactness in the middle, let $`f\in\Zp[[T]]^{\psi=0}` with
$`f(0)=0`; then $`\varphi^n(f)\to 0` in the $`(p,T)`-adic topology, so
$`g=\sum_{n\ge 0}\varphi^n(f)` converges with $`(1-\varphi)g=f`, and since
$`\psi\circ\varphi=\mathrm{id}` and $`\psi(f)=0` one checks $`\psi(g)=g`. Finally, if
$`f` is non-constant, say $`f=a_0+a_rT^r+\cdots` with $`a_r\ne 0`, then
$`\varphi(f)=a_0+pa_rT^r+\cdots\ne f`, so $`\ker(1-\varphi)=\Zp`.
:::

:::definition "iwproof-zp-one" (lean := "PadicLFunctions.Coleman.ZpOne")
Let $`\Zp(1):=\varprojlim_n\mu_{p^n}`: the module $`\Zp` carrying the $`\GGam`-action
$`\sigma\cdot x=\chi(\sigma)x` through the cyclotomic character. It is an integral
form of $`\Qp(1)`.
:::

:::theorem "fundamental-exact-sequence" (lean := "PadicLFunctions.Coleman.mem_ker_Col_iff_mem_ZpOne, PadicLFunctions.Coleman.range_Col_eq_ker_chiMoment")
The Coleman map induces an exact sequence of $`\GGam`-modules
$$`0 \to \mu_{p-1}\times\Zp(1) \longrightarrow \sU_\infty \xrightarrow{\Col}
\Lam(\GGam) \longrightarrow \Zp(1) \to 0,`
where the last map is $`\mu\mapsto\int_\GGam \chi\,d\mu`. Restricting to
$`\sU_{\infty,1}` it induces an exact sequence of $`\Lam(\GGam)`-modules
$$`0 \to \Zp(1) \longrightarrow \sU_{\infty,1} \xrightarrow{\Col}
\Lam(\GGam) \longrightarrow \Zp(1) \to 0.`
:::

:::proof "fundamental-exact-sequence"
Decompose $`\Col` into its five maps. The first, $`u\mapsto f_u`, is an isomorphism
by {uses "coleman-theorem"}[]. The second, $`\Delta`, is surjective with kernel
$`\mu_{p-1}` by {uses "iwproof-log-der-seq"}[]. The third, $`1-\varphi`, has kernel
and cokernel $`\Zp` by {uses "iwproof-rest-zpx"}[]; its kernel is the image of
$`\{(1+T)^a:a\in\Zp\}` under $`\Delta`, which interpolates the tower
$`(\xi_{p^n}^a)_n`, so pulling back to $`\sU_\infty` yields the factor
$`\Zp(1)=\{(\xi_{p^n}^a)_n:a\in\Zp\}`. The fourth and fifth maps are isomorphisms.
Assembling kernels gives kernel $`\mu_{p-1}\times\Zp(1)`, and the only cokernel is
the $`\Zp` from the third map, identified as $`\Zp(1)` via $`\int_\GGam\chi`. For
$`\GGam`-equivariance: $`\mu_{p-1}\times\Zp(1)` is $`\GGam`-stable, $`\Col` is
equivariant by {uses "coleman-equivariance"}[], and the last map is equivariant since
$`\int_\GGam\chi(x)\,\sigma\mu=\chi(\sigma)\int_\GGam\chi\,d\mu`, matching the
$`\GGam`-action on $`\Zp(1)`. Restricting to $`\sU_{\infty,1}` removes the $`\mu_{p-1}`
factor, using {uses "iwproof-units-split"}[] and {uses "iwproof-mu-killed"}[].
:::

# Generators for the global cyclotomic units

Recall the global cyclotomic units $`\DD_n=\cO_{F_n}^\times\cap\ang{\pm\xi_{p^n},\
\xi_{p^n}^a-1}` and $`\DD_n^+=\DD_n\cap F_n^+`. Set
$`c_n(a):=\tfrac{\xi_{p^n}^a-1}{\xi_{p^n}-1}\in\DD_n` and the conjugation-invariant
$$`\gamma_{n,a} := \xi_{p^n}^{(1-a)/2}c_n(a)
= \frac{\xi_{p^n}^{a/2}-\xi_{p^n}^{-a/2}}{\xi_{p^n}^{1/2}-\xi_{p^n}^{-1/2}} \in \DD_n^+.`

:::lemma_ "iwproof-cyc-gen"
Let $`n\ge 1`. Then: (i) $`\DD_n^+` is generated by $`-1` together with
$`\set{\gamma_{n,a} : 1<a<p^n/2,\ (a,p)=1}`; and (ii) $`\DD_n` is generated by
$`\xi_{p^n}` and $`\DD_n^+`.
:::

:::proof "iwproof-cyc-gen"
First reduce to $`a` prime to $`p`: the identity
$`\xi_{p^n}^{bp^m}-1=\prod_{j=0}^{p^m-1}(\xi_{p^n}^{\,b+jp^{n-m}}-1)` (with $`(b,p)=1`)
expresses the $`p`-divisible exponents in terms of prime-to-$`p` ones, and
$`\xi_{p^n}^a-1=-\xi_{p^n}^a(\xi_{p^n}^{-a}-1)` lets us take $`1\le a<p^n/2`. Now write a
general element as $`\gamma=\pm\xi_{p^n}^d\prod_a(\xi_{p^n}^a-1)^{e_a}`. All the
$`\xi_{p^n}^a-1` have equal $`p`-adic valuation $`\tfrac{1}{(p-1)p^{n-1}}` while
$`\xi_{p^n}^d` is a unit, so being in $`\DD_n` forces $`\sum_a e_a=0`. Hence we may
divide each factor by $`\xi_{p^n}-1` and rewrite
$`\gamma=\pm\xi_{p^n}^{e}\prod_a\gamma_{n,a}^{e_a}` with
$`e=d+\tfrac12\sum_a e_a(a-1)`, proving (ii). Each $`\gamma_{n,a}` is real, so
$`\gamma\in\DD_n^+` iff $`e=0`, giving (i).
:::

:::corollary "iwproof-cyc-gen-cyclic"
If $`a` generates $`(\Z/p^n\Z)^\times`, then $`\gamma_{n,a}` generates $`\DD_n^+` as
a $`\Z[\GGam_n^+]`-module.
:::

:::proof "iwproof-cyc-gen-cyclic"
Any $`b` prime to $`p` is $`b\equiv a^r \pmod{p^n}` for some $`r`, and the telescoping
product $`\gamma_{n,b}=\prod_{i=0}^{r-1}\tfrac{\xi_{p^n}^{a^{i+1}}-1}{\xi_{p^n}^{a^i}-1}
=\prod_{i=0}^{r-1}(\gamma_{n,a})^{\sigma_a^i}` exhibits every generator from
{uses "iwproof-cyc-gen"}[] as a $`\Z[\GGam_n^+]`-translate of $`\gamma_{n,a}`.
:::

# Generators for the local cyclotomic units

We pass to the local cyclotomic units $`\CC_n` (the $`p`-adic closure of $`\DD_n` in
$`\sU_n`) and their principal/real refinements $`\CC_{n,1}^+`,
$`\CC_{\infty,1}^+=\varprojlim_n\CC_{n,1}^+`. Since $`\CC_n^+` is not a $`\Zp`-module,
one must work with the principal units $`\CC_{n,1}^+` to get a $`\Zp`-structure. The
following lemma identifies $`p`-adic closures with $`\Zp`-spans.

:::lemma_ "iwproof-closure"
Let $`g_1,\dots,g_r\in\sU_{n,1}` and let $`X=\ang{g_1,\dots,g_r}` be the (multiplicative)
$`\Z`-module they generate. Then the $`p`-adic closure $`\overline X` of $`X` in
$`\sU_{n,1}` is the $`\Zp`-submodule generated by $`g_1,\dots,g_r`.
:::

:::proof "iwproof-closure"
If $`a\in\Zp` and $`a_j\to a` with $`a_j\in\Z`, then since $`g_i-1\equiv 0\pmod{\pri_n}`
the binomial series gives
$`g_i^{a_j}=\sum_k\binom{a_j}{k}(g_i-1)^k\to\sum_k\binom{a}{k}(g_i-1)^k=g_i^a`, so the
$`\Zp`-span lies in $`\overline X`. Conversely, for $`g\in\overline X` choose integer
exponent vectors $`(a_{1,j},\dots,a_{r,j})` with $`\prod_i g_i^{a_{i,j}}\to g`; by
compactness of $`\Zp^r` a subsequence of exponents converges to some
$`(b_1,\dots,b_r)\in\Zp^r`, and by the same continuity
$`\prod_i g_i^{b_i}=g`. Hence $`g` is in the $`\Zp`-span.
:::

:::lemma_ "iwproof-global-gen-2"
Let $`a\in\Z` be a topological generator of $`\Zpx` and $`w\in\mu_{p-1}\subset\sU_n`
with $`aw\equiv 1\pmod{\pri_n}`. Then: (i) $`w\gamma_{n,a}\in\sU_{n,1}`; and (ii)
$`(w\gamma_{n,a})^{p-1}=\gamma_{n,a}^{p-1}\in\sU_{n,1}^+` generates the cyclic
$`\Z[\GGam_n^+]`-module $`(p-1)\DD_n^+=\set{\gamma^{p-1}:\gamma\in\DD_n^+}`.
:::

:::proof "iwproof-global-gen-2"
(i) We claim $`\gamma_{n,a}\equiv a\pmod{\pri_n}`. Since
$`\gamma_{n,a}=\xi_{p^n}^{a/2}c_n(a)` and $`\xi_{p^n}^{a/2}\equiv 1\pmod{\pri_n}`, it
suffices to show $`c_n(a)\equiv a`. For any unit $`u`, $`u_n=f_u(\pi_n)\equiv
f_u(0)\pmod{\pri_n}`; applied to the Coleman power series
$`f_{c(a)}=((1+T)^a-1)/T` this gives $`c_n(a)\equiv f_{c(a)}(0)=a`. Hence $`w` is the
unique root of unity with $`w\gamma_{n,a}\equiv 1\pmod{\pri_n}`, so
$`w\gamma_{n,a}\in\sU_{n,1}`. (ii) By {uses "iwproof-cyc-gen-cyclic"}[] $`\gamma_{n,a}`
generates $`\DD_n^+`, so $`\gamma_{n,a}^{p-1}` generates $`(p-1)\DD_n^+`; and
$`w^{p-1}=1` gives $`\gamma_{n,a}^{p-1}=(w\gamma_{n,a})^{p-1}`.
:::

:::lemma_ "iwproof-local-gen"
Let $`a\in\Z` be a topological generator of $`\Zpx` and $`w\in\mu_{p-1}` with
$`aw\equiv 1\pmod{\pri_n}`. Then: (i) $`\CC_{n,1}^+` is a cyclic $`\Zp[\GGam_n^+]`-module
generated by $`w\gamma_{n,a}`; and (ii) $`\CC_{\infty,1}^+` is a cyclic
$`\Lam(\GGam^+)`-module generated by $`(w\gamma_{n,a})_{n\ge 1}`.
:::

:::proof "iwproof-local-gen"
(i) By {uses "iwproof-global-gen-2"}[], $`(p-1)\DD_{n,1}^+\subset\sU_{n,1}^+` is
generated over $`\Z[\GGam_n^+]` by $`(w\gamma_{n,a})^{p-1}`. By
{uses "iwproof-closure"}[], its $`p`-adic closure $`(p-1)\CC_{n,1}^+` is generated over
$`\Zp[\GGam_n^+]` by the same element. As $`p-1` is invertible in $`\Zp`,
$`(p-1)\CC_{n,1}^+=\CC_{n,1}^+`; and since $`w\gamma_{n,a}\equiv 1\pmod{\pri_n}` is the
unique $`(p-1)`-th root of $`(w\gamma_{n,a})^{p-1}` lying in $`\CC_{n,1}^+`, the module
is generated by $`w\gamma_{n,a}`. (ii) Taking the inverse limit,
$`\CC_{\infty,1}^+\cong\varprojlim_n\Zp[\GGam_n^+]\cdot w\gamma_{n,a}
\cong\Lam(\GGam^+)\cdot(w\gamma_{n,a})_n`. This depends on {uses "cyclotomic-units"}[].
:::

# End of the proof

We can now assemble the pieces and prove Iwasawa's theorem.

:::theorem "iwproof-iwasawa-final" (lean := "PadicLFunctions.Coleman.iwasawa_theorem, PadicLFunctions.Coleman.iwasawa_exact_sequence")
The Coleman map induces: (i) a short exact sequence of $`\Lam(\GGam)`-modules
$$`0 \to \sU_{\infty,1}/\CC_{\infty,1} \to \Lam(\GGam)/I(\GGam)\zeta_p \to \Zp(1) \to 0;`
and (ii) an isomorphism of $`\Lam(\GGam^+)`-modules
$$`\sU^+_{\infty,1}/\CC^+_{\infty,1} \xrightarrow{\sim} \Lam(\GGam^+)/I(\GGam^+)\zeta_p.`
Part (ii) is the statement of {uses "iwasawa-zeros-theorem"}[Iwasawa's theorem].
:::

:::proof "iwproof-iwasawa-final"
Start from the fundamental exact sequence
$`0\to\Zp(1)\to\sU_{\infty,1}\xrightarrow{\Col}\Lam(\GGam)\to\Zp(1)\to 0` of
{uses "fundamental-exact-sequence"}[]. It remains to compute the image of the
cyclotomic units. By {uses "iwproof-local-gen"}[] it suffices to evaluate $`\Col` on
$`(\xi_{p^n}^b\gamma_{n,a})_n` for $`a,b\in\Zpx`. Since $`\xi_{p^n}^b` lies in the
kernel of $`\Col` (it sits in the $`\mu_{p-1}\times\Zp(1)` factor) and
$`\gamma_{n,a}=\xi_{p^n}^{(1-a)/2}c_n(a)`, this reduces to $`\Col(c(a))`, which by the
Coleman computation of $`\zeta_p` equals $`([\sigma_a]-[1])\zeta_p`, depending on
{uses "kubota-leopoldt"}[]. As $`a` ranges over $`\Zpx`, the elements
$`[\sigma_a]-[1]` generate the augmentation ideal, so the image of $`\CC_{\infty,1}`
(resp. $`\CC_{\infty,1}^+`) is $`I(\GGam)\zeta_p` (resp. $`I(\GGam^+)\zeta_p`), depending
on {uses "ideal-of-zeta-p"}[]. Quotienting the fundamental sequence by this image
gives the exact sequence
$`0\to\sU_{\infty,1}/\CC_{\infty,1}\to\Lam(\GGam)/I(\GGam)\zeta_p\to\Zp(1)\to 0`,
which is (i). For (ii), take invariants under the order-two group
$`\ang{c}\subset\GGam` generated by complex conjugation. As $`p` is odd this functor
is exact, and $`c` acts on $`\Zp(1)` by $`-1`, so $`\Zp(1)^{\ang c}=0`; the sequence
collapses to the isomorphism
$`\sU_{\infty,1}^+/\CC_{\infty,1}^+\xrightarrow{\sim}\Lam(\GGam^+)/I(\GGam^+)\zeta_p`.
:::
