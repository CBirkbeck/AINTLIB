import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevDensityBlueprint.Refs
import CebotarevDensityBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Decomposition, inertia, Frobenius" =>

Let $`L/K` be a finite Galois extension of number fields with $`G = \Gal{L/K}`.
The Galois group acts on ideals of $`\mathcal{O}_L` (via the canonical $`G`-action
restricted to $`\mathcal{O}_L` and extended multiplicatively), and in particular
permutes the primes lying above a given prime $`\mathfrak{p}` of $`\mathcal{O}_K`.

:::definition "def:unramified-in" (lean := "Chebotarev.UnramifiedIn")
A nonzero prime ideal $`\mathfrak{p}` of $`\mathcal{O}_K` is *unramified in $`L`*
if every prime $`\mathfrak{P}` of $`\mathcal{O}_L` lying over $`\mathfrak{p}` has
ramification index $`1`, i.e. $`\mathfrak{p}\mathcal{O}_L` factors into distinct
primes.
:::

:::definition "def:decomposition-group"
For a prime $`\mathfrak{P}` of $`\mathcal{O}_L`, the *decomposition group* at
$`\mathfrak{P}` is
$$`D_\mathfrak{P} \;=\; \{\sigma \in G : \sigma(\mathfrak{P}) = \mathfrak{P}\} \;=\; \operatorname{Stab}_G(\mathfrak{P}).`
In the formalisation this is mathlib's stabiliser `MulAction.stabilizer G 𝔓` of the
$`G`-action on the primes of $`\mathcal{O}_L`, so it is not restated as a separate
project definition.
:::

:::definition "def:inertia-group"
The *inertia group* at $`\mathfrak{P}` is
$$`I_\mathfrak{P} \;=\; \{\sigma \in G : \forall x \in \mathcal{O}_L,\ \sigma(x) \equiv x \pmod{\mathfrak{P}}\}.`
This is the generic ideal-inertia subgroup `Ideal.inertia` from mathlib,
instantiated at the natural action of $`G` on $`\mathcal{O}_L`; acting trivially
mod $`\mathfrak{P}` forces stabilising $`\mathfrak{P}`, so $`I_\mathfrak{P}` sits
inside $`D_\mathfrak{P}`, and is the kernel of the action of $`D_\mathfrak{P}` on
the residue field $`\mathcal{O}_L/\mathfrak{P}`.

{uses "def:decomposition-group"}[]
:::

When $`\mathfrak{P}` is unramified the inertia group is trivial:
$`|I_\mathfrak{P}| = e(\mathfrak{P} \mid \mathfrak{p}) = 1`. Hence the surjection
$`D_\mathfrak{P} \to \Gal{(\mathcal{O}_L/\mathfrak{P})/(\mathcal{O}_K/\mathfrak{p})}`
(mathlib's `IsFractionRing.stabilizerHom_surjective`) is an isomorphism, and the
residue Galois group of a finite-field extension is cyclic with distinguished
generator the absolute Frobenius $`x \mapsto x^{\Norm\mathfrak{p}}`. So
$`D_\mathfrak{P}` contains a unique element acting as
$`x \mapsto x^{\Norm\mathfrak{p}}` on $`\mathcal{O}_L/\mathfrak{P}`. In the
formalisation this existence and uniqueness is supplied directly by mathlib's
arithmetic-Frobenius API (`IsArithFrobAt.exists_of_isInvariant` for existence,
`IsArithFrobAt.mul_inv_mem_inertia` together with trivial inertia for uniqueness),
so it is not restated as a separate project result.

:::definition "def:frobenius-at"
For an unramified nonzero prime $`\mathfrak{P}` of $`\mathcal{O}_L`, the *Frobenius
automorphism* $`\Frob_\mathfrak{P} \in G` is mathlib's `arithFrobAt` for the action
of $`G` on $`\mathcal{O}_L`: the unique element of $`D_\mathfrak{P}` characterised
by $`\Frob_\mathfrak{P}(x) \equiv x^{\Norm\mathfrak{p}} \pmod{\mathfrak{P}}` for all
$`x \in \mathcal{O}_L`.

{uses "def:decomposition-group"}[] {uses "def:unramified-in"}[]
:::

:::definition "def:frobenius-class" (lean := "Chebotarev.frobeniusClass")
For a nonzero prime $`\mathfrak{p}` of $`\mathcal{O}_K` unramified in $`L`, the
*Frobenius conjugacy class* is
$$`\sigma_\mathfrak{p} \;=\; \{\Frob_\mathfrak{P} : \mathfrak{P} \mid \mathfrak{p}\} \;\in\; \operatorname{Conj}(G),`
the conjugacy class in $`G` containing $`\Frob_\mathfrak{P}` for any (equivalently
every) prime $`\mathfrak{P}` of $`\mathcal{O}_L` above $`\mathfrak{p}`. The class is
independent of the choice of $`\mathfrak{P}`.

{uses "def:frobenius-at"}[]
:::

:::lemma_ "lem:exists-frobenius-class" (lean := "Chebotarev.exists_frobeniusClass")
For a nonzero prime $`\mathfrak{p}` of $`\mathcal{O}_K` unramified in $`L`, there
exists a conjugacy class $`C \subseteq \Gal{L/K}` such that for every prime
$`\mathfrak{P}` of $`\mathcal{O}_L` above $`\mathfrak{p}`,
$`C = [\Frob_\mathfrak{P}]`. (Equivalently, the Frobenius elements above
$`\mathfrak{p}` are all conjugate.)

{uses "def:frobenius-at"}[]
:::

:::lemma_ "lem:frobenius-class-eq-mk" (lean := "Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt")
For a nonzero prime $`\mathfrak{p}` of $`\mathcal{O}_K` unramified in $`L`, and any
prime $`\mathfrak{P}` of $`\mathcal{O}_L` above $`\mathfrak{p}`,
$$`\sigma_\mathfrak{p} \;=\; [\Frob_\mathfrak{P}].`

{uses "def:frobenius-class"}[] {uses "def:frobenius-at"}[] {uses "lem:exists-frobenius-class"}[]
:::

:::proof "lem:frobenius-class-eq-mk"
Unfold $`\sigma_\mathfrak{p}` at the unramified positive case to expose the choice
function from {bpref "lem:exists-frobenius-class"}[]; the witness property of its
specification at $`\mathfrak{P}` closes the goal.

{uses "lem:exists-frobenius-class"}[]
:::

:::lemma_ "lem:finite-ramified-primes" (lean := "Chebotarev.finite_ramifiedIn")
Only finitely many nonzero primes of $`\mathcal{O}_K` ramify in $`L`.

{uses "def:unramified-in"}[]
:::

:::proof "lem:finite-ramified-primes"
The primes ramifying in $`L` are exactly the divisors of the relative different
ideal $`\mathfrak{d}_{L/K} \subseteq \mathcal{O}_L`, which has a finite prime
factorisation in the Dedekind domain $`\mathcal{O}_L`.
:::
