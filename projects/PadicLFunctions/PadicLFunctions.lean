module

public import PadicLFunctions.Basic
public import PadicLFunctions.Common.DelOperator
public import PadicLFunctions.Measure.Basic
public import PadicLFunctions.Measure.MahlerTransform
public import PadicLFunctions.Measure.Convolution
public import PadicLFunctions.Measure.Toolbox
public import PadicLFunctions.Measure.UnitsZp
public import PadicLFunctions.Measure.Fubini
public import PadicLFunctions.Measure.PseudoMeasure
public import PadicLFunctions.KubotaLeopoldt.ZetaValues
public import PadicLFunctions.KubotaLeopoldt.ZetaValuesComplex
public import PadicLFunctions.KubotaLeopoldt.MuA
public import PadicLFunctions.KubotaLeopoldt.ZetaP
public import PadicLFunctions.Coefficients
public import PadicLFunctions.MeasureR.Basic
public import PadicLFunctions.MeasureR.MahlerTransform
public import PadicLFunctions.MeasureR.Convolution
public import PadicLFunctions.MeasureR.Toolbox
public import PadicLFunctions.MeasureR.UnitsZp
public import PadicLFunctions.MeasureR.Fubini
public import PadicLFunctions.MeasureR.UnitsRing
public import PadicLFunctions.MeasureR.BaseChange
public import PadicLFunctions.Interpolation.Characters
public import PadicLFunctions.Interpolation.GenBernoulli
public import PadicLFunctions.Interpolation.GenBernoulliComplex
public import PadicLFunctions.Interpolation.Sawtooth
public import PadicLFunctions.Interpolation.Twist
public import PadicLFunctions.Interpolation.TameConductor
public import PadicLFunctions.Interpolation.NonTame
public import PadicLFunctions.Interpolation.Branches
public import PadicLFunctions.Interpolation.LpFunction
public import PadicLFunctions.PadicExp
public import PadicLFunctions.ExtLog
public import PadicLFunctions.MeasureR.FormalPsi
public import PadicLFunctions.ValuesAtOneComplex
public import PadicLFunctions.ValuesAtOne
public import PadicLFunctions.ResidueZeta
public import PadicLFunctions.EisensteinFamily
public import PadicLFunctions.EisensteinComplex
public import PadicLFunctions.Coleman.Tower
public import PadicLFunctions.Coleman.NormOperator
public import PadicLFunctions.Coleman.Theorem
public import PadicLFunctions.Coleman.Map
public import PadicLFunctions.Iwasawa.PlusPart
public import PadicLFunctions.Iwasawa.ZetaGalois
public import PadicLFunctions.Iwasawa.LocalUnits
public import PadicLFunctions.Iwasawa.CyclotomicUnits
public import PadicLFunctions.IwasawaProof.GaloisAction
public import PadicLFunctions.IwasawaProof.LogDerivative
public import PadicLFunctions.IwasawaProof.Equivariance
public import PadicLFunctions.IwasawaProof.FundamentalSequence
public import PadicLFunctions.IwasawaProof.Generators
public import PadicLFunctions.IwasawaProof.Main

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

@[expose] public section
