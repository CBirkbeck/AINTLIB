import PadicLFunctions.Basic
import PadicLFunctions.Measure.Basic
import PadicLFunctions.Measure.MahlerTransform
import PadicLFunctions.Measure.Convolution
import PadicLFunctions.Measure.Toolbox
import PadicLFunctions.Measure.UnitsZp
import PadicLFunctions.Measure.Fubini
import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.KubotaLeopoldt.ZetaValues
import PadicLFunctions.KubotaLeopoldt.ZetaValuesComplex
import PadicLFunctions.KubotaLeopoldt.MuA
import PadicLFunctions.KubotaLeopoldt.ZetaP
import PadicLFunctions.Coefficients
import PadicLFunctions.MeasureR.Basic
import PadicLFunctions.MeasureR.MahlerTransform
import PadicLFunctions.MeasureR.Convolution
import PadicLFunctions.MeasureR.Toolbox
import PadicLFunctions.MeasureR.UnitsZp
import PadicLFunctions.MeasureR.Fubini
import PadicLFunctions.MeasureR.UnitsRing
import PadicLFunctions.MeasureR.BaseChange
import PadicLFunctions.Interpolation.Characters
import PadicLFunctions.Interpolation.GenBernoulli
import PadicLFunctions.Interpolation.GenBernoulliComplex
import PadicLFunctions.Interpolation.Sawtooth
import PadicLFunctions.Interpolation.Twist
import PadicLFunctions.Interpolation.TameConductor
import PadicLFunctions.Interpolation.NonTame
import PadicLFunctions.Interpolation.Branches
import PadicLFunctions.Interpolation.LpFunction
import PadicLFunctions.PadicExp
import PadicLFunctions.ExtLog
import PadicLFunctions.MeasureR.FormalPsi
import PadicLFunctions.ValuesAtOneComplex
import PadicLFunctions.ValuesAtOne
import PadicLFunctions.ResidueZeta
import PadicLFunctions.EisensteinFamily
import PadicLFunctions.EisensteinComplex
import PadicLFunctions.Coleman.Tower
import PadicLFunctions.Coleman.NormOperator
import PadicLFunctions.Coleman.Theorem
import PadicLFunctions.Coleman.Map
import PadicLFunctions.Iwasawa.PlusPart
import PadicLFunctions.Iwasawa.ZetaGalois
import PadicLFunctions.Iwasawa.LocalUnits
import PadicLFunctions.Iwasawa.CyclotomicUnits
import PadicLFunctions.Iwasawa.StructureTheory.IwasawaAlgebra
import PadicLFunctions.Iwasawa.StructureTheory.PseudoIso
import PadicLFunctions.Iwasawa.StructureTheory.StructureTheorem
import PadicLFunctions.Iwasawa.StructureTheory.CharIdeal
import PadicLFunctions.Iwasawa.StructureTheory.Isotypic
import PadicLFunctions.IwasawaProof.GaloisAction
import PadicLFunctions.IwasawaProof.LogDerivative
import PadicLFunctions.IwasawaProof.Equivariance
import PadicLFunctions.IwasawaProof.FundamentalSequence
import PadicLFunctions.IwasawaProof.Generators
import PadicLFunctions.IwasawaProof.Main
import PadicLFunctions.IwasawaProof.Galois.ClassFieldTheory
import PadicLFunctions.IwasawaProof.Galois.Modules
import PadicLFunctions.IwasawaProof.Galois.Coinvariants
import PadicLFunctions.IwasawaProof.Galois.Bridge
import PadicLFunctions.IwasawaProof.Galois.Sequence
import PadicLFunctions.IwasawaProof.MainConjecture

/-!
# p-adic L-functions

A Lean 4 / Mathlib formalisation following

> J. Rodrigues Jacinto and C. Williams,
> *An introduction to p-adic L-functions*, arXiv:2309.15692.

The mathematical roadmap for the whole paper lives in the companion Verso
blueprint (`PadicLFunctionsBlueprint`). Individual results are laid down as
`sorry`-skeletons by `/develop` and discharged by `/beastmode`; the blueprint
dependency graph colours in automatically as the referenced declarations are
completed.
-/
