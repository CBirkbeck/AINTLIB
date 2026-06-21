import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanModularForms.Chapters.HeckePairs
import LeanModularForms.Chapters.RingStructure
import LeanModularForms.Chapters.DegreeHom
import LeanModularForms.Chapters.Commutativity
import LeanModularForms.Chapters.GL2Operators
import LeanModularForms.Chapters.MultiplicationTable
import LeanModularForms.Chapters.CongruenceHecke
import LeanModularForms.Chapters.PolynomialStructure
import LeanModularForms.Chapters.HeckeOperators
import LeanModularForms.Chapters.Petersson
import LeanModularForms.Chapters.CharacterSpaces
import LeanModularForms.Chapters.AdjointSpectral
import LeanModularForms.Chapters.NewformTheory
import LeanModularForms.Chapters.Dimensions
import LeanModularForms.Chapters.StrongMultiplicityOne
import LeanModularForms.Chapters.Curves
import LeanModularForms.Chapters.CPV
import LeanModularForms.Chapters.Winding
import LeanModularForms.Chapters.Conditions
import LeanModularForms.Chapters.HW33
import LeanModularForms.Chapters.WindingElliptic
import LeanModularForms.Chapters.ValenceFormula

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "LeanModularForms Blueprint" =>

This blueprint documents the *LeanModularForms* project. It runs three
narratives.

*Part I — Hecke rings.* A *Hecke pair* $`(G,H,\Delta)` produces a free
$`\mathbb{Z}`-module on the double cosets $`H\backslash\Delta/H`. A
convolution product whose structure constants count coset overlaps makes this
an associative unital ring, carrying a degree homomorphism to $`\mathbb{Z}`.
An *anti-involution* of the pair that fixes every double coset forces the
ring to be commutative; for $`\mathrm{GL}_n` the transpose
$`g\mapsto {}^{t}g` is such an anti-involution, so the $`\mathrm{GL}_n`
Hecke algebra is commutative. Specialising to $`\mathrm{GL}_2` gives the
operators $`T(a,d)` and $`T(m)=\sum_{a\mid m}T(a,m/a)`, which obey Shimura's
multiplication table (Theorem 3.24). The congruence pair
$`(\Gamma_0(N),\Delta_0(N))` receives a surjection from the full-level ring
(Shimura Theorem 3.35), and the $`p`-local subring is a polynomial ring on
the diagonal generators (Shimura Theorem 3.20).

*Part II — Hecke operators on modular forms and Strong Multiplicity One.*
The Hecke ring acts on modular forms through the weight-$`k` slash action,
yielding the diamond operators $`\langle d\rangle` and the operators $`T(n)`
with their classical multiplicativity, recurrences, and Fourier-coefficient
formulas. The Petersson inner product makes the cusp space a
finite-dimensional inner-product space on which the $`T(n)` (for
$`(n,N)=1`) are normal, so a simultaneous orthogonal eigenbasis exists; the
old/new decomposition and the Atkin–Lehner Main Lemma then rigidify
eigensystems, culminating in Strong Multiplicity One (Miyake
Theorem 4.6.12).

*Part III — the generalised residue theorem and the valence formula.* A
closed piecewise-$`C^{1}` immersion $`\gamma` in an open
$`U \subseteq \mathbb{C}` may pass *through* poles of $`f`. Replacing the
contour integral by a multi-point Cauchy principal value and the winding
number by a generalised (fractional) winding number, the
Hungerbühler–Wasem residue theorem (HW 3.3) recovers
$`\operatorname{PV}\!\int_\gamma f = \sum_{s} 2\pi i\,
\operatorname{gWN}(\gamma,s)\operatorname{Res}(f,s)` under the paper
conditions (A′) and (B) on the crossing geometry. Applied to the logarithmic
derivative $`f'/f` of a modular form around the boundary of the standard
fundamental domain — which crosses the elliptic points $`i` and
$`\rho` — this yields the classical valence formula for modular forms on
$`\operatorname{SL}_2(\mathbb{Z})`.

{include 0 LeanModularForms.Chapters.HeckePairs}
{include 0 LeanModularForms.Chapters.RingStructure}
{include 0 LeanModularForms.Chapters.DegreeHom}
{include 0 LeanModularForms.Chapters.Commutativity}
{include 0 LeanModularForms.Chapters.GL2Operators}
{include 0 LeanModularForms.Chapters.MultiplicationTable}
{include 0 LeanModularForms.Chapters.CongruenceHecke}
{include 0 LeanModularForms.Chapters.PolynomialStructure}
{include 0 LeanModularForms.Chapters.HeckeOperators}
{include 0 LeanModularForms.Chapters.Petersson}
{include 0 LeanModularForms.Chapters.CharacterSpaces}
{include 0 LeanModularForms.Chapters.AdjointSpectral}
{include 0 LeanModularForms.Chapters.NewformTheory}
{include 0 LeanModularForms.Chapters.Dimensions}
{include 0 LeanModularForms.Chapters.StrongMultiplicityOne}
{include 0 LeanModularForms.Chapters.Curves}
{include 0 LeanModularForms.Chapters.CPV}
{include 0 LeanModularForms.Chapters.Winding}
{include 0 LeanModularForms.Chapters.Conditions}
{include 0 LeanModularForms.Chapters.HW33}
{include 0 LeanModularForms.Chapters.WindingElliptic}
{include 0 LeanModularForms.Chapters.ValenceFormula}

{blueprint_graph}
{blueprint_summary}
