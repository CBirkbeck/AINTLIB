import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The abandoned reflection route" =>

This chapter records a second possible route to the plus-to-minus divisibility step.
It is not the route used in the proof of Kummer's criterion. Its purpose here is to
isolate the remaining mathematical input and to explain how the reflection argument
would proceed if that input were supplied.

# The aim

Let $`p` be an odd prime and let $`K=\mathbb{Q}(\zeta_p)`. Put
$$`A=\mathrm{Cl}(\mathcal{O}_K)/p\,\mathrm{Cl}(\mathcal{O}_K),`
with the natural action of
$`\Delta=\operatorname{Gal}(K/\mathbb{Q})\simeq(\mathbb{Z}/p\mathbb{Z})^\times`. The
reflection route tries to prove
$`p\mid h^+(K)\Longrightarrow p\mid h^-(K)` by proving a statement about the
character components of $`A`. If $`A_i` denotes the $`i`-th eigenspace, the desired
reflection statement is that a nonzero even component forces a nonzero reflected
component: $`A_i\ne0 \Longrightarrow A_{1-i}\ne0`. The index $`1-i` is always
understood modulo $`p-1`, in the standard representative range.

# The unproved reciprocity input

:::theorem "thm:abandoned-oskr" (lean := "BernoulliRegular.Furtwaengler.oneSidedKummerPrincipalReciprocity_canonical")
**One-sided Kummer principal reciprocity.** Let
$`\alpha,\beta\in\mathcal{O}_K` be nonzero, coprime, and prime to $`p`. Assume that
$`\alpha` is a $`p`-th power in the $`(\zeta_p-1)`-adic completion of $`K`. Then the
canonical $`p`-th-power residue symbols satisfy
$$`\left(\frac{\alpha}{(\beta)}\right)_p = \left(\frac{\beta}{(\alpha)}\right)_p.`
:::

This is the single missing mathematical input for the reflection route as recorded
here. It is intentionally stated as a concrete reciprocity theorem, not as a packaged
reflection principle.

The immediate consequence needed below is the following principal-denominator
vanishing statement. If $`\eta` is locally a $`p`-th power at $`\zeta_p-1`, prime to
$`p`, and $`(\eta)=\mathfrak b^p`, then for every admissible principal denominator
$`(\gamma)` one has $`\left(\frac{\eta}{(\gamma)}\right)_p=1`. Indeed, reciprocity
gives $`\left(\frac{\eta}{(\gamma)}\right)_p = \left(\frac{\gamma}{(\eta)}\right)_p`,
and the denominator $`(\eta)=\mathfrak b^p` makes the right hand side trivial by
multiplicativity in the denominator.

# Component reflection

:::theorem "thm:abandoned-component-reflection" (lean := "BernoulliRegular.weakReflection_componentNontrivial")
**Component reflection.** Let $`i` be an even reflection index. If the
$`i`-component of $`\mathrm{Cl}(\mathcal{O}_K)/p\,\mathrm{Cl}(\mathcal{O}_K)` is
nonzero, then the reflected component is nonzero:
$`A_i\ne0\Longrightarrow A_{1-i}\ne0`.

{uses "thm:abandoned-oskr"}[]
:::

:::proof "thm:abandoned-component-reflection"
The proof has five mathematical steps. First, the nonzero component $`A_i` gives a
nonzero locally-primary singular pseudo-unit. More precisely, one obtains
$`\eta\in\mathcal{O}_K`, $`(\eta)=\mathfrak b^p`, $`\eta\notin K^{\times p}`, where
$`\eta` is prime to $`p`, locally a $`p`-th power at $`\zeta_p-1`, and has Galois
weight $`i` up to multiplication by global $`p`-th powers.

Second, use the residue symbol to define a character on ideal classes:
$`\chi_\eta([\mathfrak a]) = \left(\frac{\eta}{\mathfrak a}\right)_p`. The
representative $`\mathfrak a` is chosen coprime to a finite bad set containing the
primes above $`p`, the primes dividing $`(\eta)`, and the Kummer-Dedekind conductor.
Such representatives exist by ideal avoidance. The principal-denominator vanishing
consequence of {bpref "thm:abandoned-oskr"}[] makes the value independent of this
choice. Thus $`\chi_\eta` descends to a character of $`A`.

Third, the character is nonzero. If it were zero, then for every prime ideal
$`\mathfrak q` outside the bad set the residue symbol
$`(\eta/\mathfrak q)_p` would be trivial. Hence the reduction of $`\eta` would be a
$`p`-th power in $`\mathcal{O}_K/\mathfrak q`, so $`T^p-\eta` would split modulo
$`\mathfrak q`. Kummer-Dedekind would then show that almost all primes of $`K` split
completely in $`K(\eta^{1/p})/K`. The weak splitting lemma forces this extension to be
trivial, contradicting $`\eta\notin K^{\times p}`.

Fourth, the Galois weight of $`\eta` gives the covariance relation
$`\chi_\eta(\sigma_a x)=a^{1-i}\chi_\eta(x)` ($`a\in(\mathbb{Z}/p\mathbb{Z})^\times`).
Thus the nonzero character is supported on the reflected component.

Finally, the boundary case $`i=p-1` is treated separately. The zero-character
component of $`A` is trivial: if an ideal class is fixed by all Galois conjugates, the
product of all its conjugates is represented by a Galois-stable ideal, hence by a
principal ideal. The class therefore has order dividing both $`p` and $`p-1`, so it
is trivial. The remaining case is the interior even case handled by the preceding
argument.
:::

# From reflection to class numbers

:::theorem "thm:abandoned-reflection-plus-minus" (lean := "BernoulliRegular.weakReflection_dvd_hMinus_of_dvd_hPlus")
**Reflection-route plus-to-minus implication.** For an odd prime $`p`,
$$`p\mid h^+(K)\Longrightarrow p\mid h^-(K).`

{uses "thm:abandoned-component-reflection"}[]
:::

:::proof "thm:abandoned-reflection-plus-minus"
Assume $`p\mid h^+(K)` and $`p\nmid h^-(K)`. Since $`h(K)=h^+(K)h^-(K)`, the first
assumption implies $`p\mid h(K)`, so the group $`A` is nonzero. Decompose $`A` into
character components and choose a nonzero component $`A_k`. The assumption
$`p\nmid h^-(K)` says that complex conjugation acts trivially on the relevant mod-$`p`
class group. Therefore no odd component can be nonzero. The zero component is also
trivial, as in the boundary argument above. Hence the chosen nonzero component is even
and nonzero. Component reflection gives a nonzero reflected component, but the
reflected index is odd, contradicting the trivial action of complex conjugation. Thus
$`p\nmid h^-(K)` is impossible.
:::

Once the plus-to-minus implication is known, the reflection route also recovers the
same class-number criterion as the main proof:
$$`(p:\mathbb{N})\mid h(K) \quad\Longleftrightarrow\quad \exists k,\ 1\le k,\ 2k\le p-3,\quad (p:\mathbb{Z})\mid (B_{2k})_{\mathrm{num}}.`
Indeed, by the factorisation $`h(K)=h^+(K)h^-(K)`, divisibility of $`h(K)` by the
prime $`p` means that $`p` divides either $`h^+(K)` or $`h^-(K)`. The plus-to-minus
implication transfers the first case to the second. Thus
$`p\mid h(K)\Longleftrightarrow p\mid h^-(K)`. The minus class-number criterion
identifies the latter condition with Bernoulli numerator divisibility in Kummer's
range.

# How the reciprocity input is to be proved

The intended source for {bpref "thm:abandoned-oskr"}[] is the classical
Furtwaengler–Kummer reciprocity argument, in the form developed by Ireland–Rosen. The
already completed part of that source proves the integer-denominator Eisenstein
reciprocity theorem.

:::theorem "thm:ireland-rosen-integer-reciprocity" (lean := "BernoulliRegular.Furtwaengler.IrelandRosen.eisensteinReciprocity_theorem1")
**Ireland–Rosen integer reciprocity.** Let $`\alpha\in\mathcal{O}_K` be primary and
prime to $`p`, and let $`a\in\mathbb{Z}` be nonzero, prime to $`p`, and coprime to
$`(\alpha)`. Then
$$`\left(\frac{\alpha}{(a)}\right)_p = \left(\frac{a}{(\alpha)}\right)_p .`
:::

:::proof "thm:ireland-rosen-integer-reciprocity"
The proof follows the Gauss–Jacobi sum construction. For every prime ideal
$`P\nmid p`, one constructs an element $`\Phi(P)` whose principal ideal is controlled
by the Stickelberger element: $`(\Phi(P))=P^\theta`. This is proved without assuming
that $`P` has residue degree one. The construction also supplies the semiprimary
normalization, the conjugation-norm identity, and the Frobenius residue-symbol
identity for $`\Phi(P)`.

For a general principal ideal $`(\alpha)`, take the product over the prime
factorization of $`(\alpha)`:
$`\Phi(\alpha)= \prod_{P\mid(\alpha)}\Phi(P)^{v_P((\alpha))}`. The Stickelberger
identities multiply to give $`(\Phi(\alpha))=(\alpha^\theta)`. Hence
$`\Phi(\alpha)=\varepsilon\,\alpha^\theta` for a unit $`\varepsilon`. The primary-unit
lemma says that when $`\alpha` is primary, this unit contributes only a sign, and a
sign has trivial $`p`-th-power residue symbol because $`p` is odd.

Combining the product identity, the primary-unit cancellation, and the denominator
norm calculation gives the ideal-norm reciprocity formula. Taking the denominator
ideal to be $`(a)` gives the displayed integer reciprocity law.
:::

To finish the reflection route one still has to pass from this integer-denominator
theorem to the full one-sided principal reciprocity statement of
{bpref "thm:abandoned-oskr"}[]. The missing step is not a new reflection theorem; it
is the remaining principal-denominator reciprocity argument that allows a general
coprime principal denominator $`(\beta)` in place of a rational integer denominator
$`(a)`, with the local-primary hypothesis on the numerator preserved throughout.
