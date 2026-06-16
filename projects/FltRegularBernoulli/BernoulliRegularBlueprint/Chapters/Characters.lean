import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Characters of the cyclotomic Galois group" =>

This chapter fixes the character-theoretic notation used later.

# The Galois group

:::definition "def:galois-cyclotomic" (lean := "BernoulliRegular.cyclotomicGalEquivZMod, BernoulliRegular.cyclotomicSigmaOfUnit, BernoulliRegular.cyclotomicGalEquivZMod_sigmaOfUnit, BernoulliRegular.cyclotomicSigmaOfUnit_apply_zeta")
The extension $`\mathbb{Q}(\zeta_p)/\mathbb{Q}` is Galois of degree $`p-1`. The
assignment
$$`\sigma_a(\zeta_p)=\zeta_p^a \qquad (a\in (\mathbb{Z}/p\mathbb{Z})^\times)`
identifies $`\operatorname{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q})` with
$`(\mathbb{Z}/p\mathbb{Z})^\times`.
:::

# Dirichlet characters

:::definition "def:dirichlet-character" (lean := "DirichletCharacter")
Let $`N\ge 1` and let $`R` be a commutative ring. A *Dirichlet character modulo
$`N`* with values in $`R` is a multiplicative map
$`\chi : \mathbb{Z}/N\mathbb{Z} \to R` which vanishes on non-units.
:::

When $`p` is prime, the non-trivial characters modulo $`p` are exactly the
characters of the cyclic group $`(\mathbb{Z}/p\mathbb{Z})^\times`. In particular they
form a cyclic group of order $`p-1`, and every non-trivial character satisfies the
orthogonality relation $`\sum_{a\in \mathbb{Z}/p\mathbb{Z}} \chi(a) = 0`.

:::definition "def:teichmuller" (lean := "BernoulliRegular.teichmullerCharQp")
**Teichmüller character.** The *Teichmüller character* is the unique character
$$`\omega : (\mathbb{Z}/p\mathbb{Z})^\times \longrightarrow \mathbb{Z}_p^\times`
such that $`\omega(a)\equiv a\pmod p` for every nonzero residue class $`a`. It
generates the character group.

{uses "def:dirichlet-character"}[]
:::

Thus every Dirichlet character modulo $`p` can be written uniquely as a power
$`\omega^j` with $`0\le j\le p-2`.

# Even and odd characters

:::definition "def:even-odd" (lean := "DirichletCharacter.Even")
A Dirichlet character $`\chi` is *even* if $`\chi(-1)=1` and *odd* if
$`\chi(-1)=-1`.

{uses "def:dirichlet-character"}[]
:::

Exactly half of the characters modulo $`p` are even and exactly half are odd. The
even characters are precisely those that factor through the quotient
$`(\mathbb{Z}/p\mathbb{Z})^\times / \{\pm 1\}`, which is the Galois group of the
maximal real subfield $`\mathbb{Q}(\zeta_p)^+`. This parity distinction is the source
of the even/odd decomposition in the analytic class number formula.

Finally, because $`p` is prime, every non-trivial Dirichlet character modulo $`p` is
primitive. Hence the functional equation for primitive Dirichlet $`L`-functions
applies to every odd character that appears later.
