# Inventory: ./HasseWeil.lean

## Summary

`HasseWeil.lean` is a **pure import aggregator** — it contains no declarations of its own
(no `def`, `lemma`, `theorem`, `instance`, `structure`, `class`, `abbrev`, or any other
declaration). Its sole purpose is to re-export the entire project by importing every
top-level module.

**Total lines:** 89 (88 `import` lines + 1 trailing blank line)
**Total declarations:** 0
**Sorries:** none
**set_option maxHeartbeats:** none

## Imported modules (88 total)

| # | Import |
|---|--------|
| 1 | `HasseWeil.Auxiliary.DivisionPolynomial` |
| 2 | `HasseWeil.Auxiliary.PullbackKaehler` |
| 3 | `HasseWeil.Basic` |
| 4 | `HasseWeil.Curves.BaseChange` |
| 5 | `HasseWeil.Curves.Basic` |
| 6 | `HasseWeil.Curves.CurveMap` |
| 7 | `HasseWeil.Curves.Differentials` |
| 8 | `HasseWeil.Curves.Divisors` |
| 9 | `HasseWeil.Curves.DVR` |
| 10 | `HasseWeil.Curves.ProjectiveDivisor` |
| 11 | `HasseWeil.Curves.NormValuation` |
| 12 | `HasseWeil.Curves.FiniteOverKx` |
| 13 | `HasseWeil.Curves.GaloisAction` |
| 14 | `HasseWeil.Curves.NormBezout` |
| 15 | `HasseWeil.Curves.ProjectiveTuple` |
| 16 | `HasseWeil.Curves.RamificationAtInfinity` |
| 17 | `HasseWeil.Curves.RationalMap` |
| 18 | `HasseWeil.Curves.Valuation` |
| 19 | `HasseWeil.FormalGroup.Associated` |
| 20 | `HasseWeil.FormalGroup.CharP` |
| 21 | `HasseWeil.FormalGroup.EvalGroup` |
| 22 | `HasseWeil.FormalGroup.Height` |
| 23 | `HasseWeil.FormalGroup.Hom` |
| 24 | `HasseWeil.FormalGroup.InvariantDiff` |
| 25 | `HasseWeil.FormalGroup.Inverse` |
| 26 | `HasseWeil.FormalGroup.Logarithm` |
| 27 | `HasseWeil.FormalGroup.MulByNat` |
| 28 | `HasseWeil.FormalGroup.OrderSubst` |
| 29 | `HasseWeil.FormalGroup.PadicValFactorial` |
| 30 | `HasseWeil.InvariantDifferential` |
| 31 | `HasseWeil.Endomorphism` |
| 32 | `HasseWeil.DualIsogeny` |
| 33 | `HasseWeil.EC.MulByIntBaseCase` |
| 34 | `HasseWeil.EC.MulByIntComp` |
| 35 | `HasseWeil.EC.AffinePointMap` |
| 36 | `HasseWeil.EC.GenericPoint` |
| 37 | `HasseWeil.EC.GenericPointZsmul` |
| 38 | `HasseWeil.EC.IsogenyKernel` |
| 39 | `HasseWeil.EC.IsogenyOrdTransport` |
| 40 | `HasseWeil.EC.MulByIntUnramified` |
| 41 | `HasseWeil.EC.PointMapSurjective` |
| 42 | `HasseWeil.DegreeQuadraticForm` |
| 43 | `HasseWeil.Frobenius` |
| 44 | `HasseWeil.Hasse.BoundOfWitnesses` |
| 45 | `HasseWeil.Hasse.PointFix` |
| 46 | `HasseWeil.EC.PointMap` |
| 47 | `HasseWeil.Hasse.Separability` |
| 48 | `HasseWeil.Hasse.TorsionCard` |
| 49 | `HasseWeil.HasseBound` |
| 50 | `HasseWeil.InvariantDifferentialPullback` |
| 51 | `HasseWeil.PullbackCoeff` |
| 52 | `HasseWeil.RouteBInduction` |
| 53 | `HasseWeil.GapQfKernel` |
| 54 | `HasseWeil.HasseWeilSkeleton` |
| 55 | `HasseWeil.GapSpines` |
| 56 | `HasseWeil.Pic0.RouteCAssembly` |
| 57 | `HasseWeil.Pic0.RouteCGeometric` |
| 58 | `HasseWeil.Pic0.RouteCTheoremOfSquare` |
| 59 | `HasseWeil.Pic0.RouteCTheoremOfSquareDiv` |
| 60 | `HasseWeil.Pic0.RouteCAddFormula` |
| 61 | `HasseWeil.WeilPairing.Assembly` |
| 62 | `HasseWeil.WeilPairing.TorsionSeparable` |
| 63 | `HasseWeil.WeilPairing.SigmaBridge` |
| 64 | `HasseWeil.WeilPairing.WeilFunction` |
| 65 | `HasseWeil.WeilPairing.RootsOfUnity` |
| 66 | `HasseWeil.WeilPairing.Constancy` |
| 67 | `HasseWeil.WeilPairing.PairingProps` |
| 68 | `HasseWeil.WeilPairing.DetDeg` |
| 69 | `HasseWeil.WeilPairing.HasseAssembly` |
| 70 | `HasseWeil.WeilPairing.FrobMatrixData` |
| 71 | `HasseWeil.WeilPairing.FrobeniusGalois` |
| 72 | `HasseWeil.WeilPairing.DivisorGalois` |
| 73 | `HasseWeil.WeilPairing.FrobeniusDivisorGalois` |
| 74 | `HasseWeil.WeilPairing.FrobeniusGaloisScaling` |
| 75 | `HasseWeil.WeilPairing.OneSubScaling` |
| 76 | `HasseWeil.WeilPairing.IsogenyBaseChangeConcrete` |
| 77 | `HasseWeil.WeilPairing.OneSubWitnesses` |
| 78 | `HasseWeil.WeilPairing.OneSubDualDivisor` |
| 79 | `HasseWeil.WeilPairing.PencilDualDivisor` |
| 80 | `HasseWeil.WeilPairing.SeparableWitnesses` |
| 81 | `HasseWeil.WeilPairing.MapTranslateGenericAdditive` |
| 82 | `HasseWeil.WeilPairing.FrobeniusGenericCovariance` |
| 83 | `HasseWeil.WeilPairing.PencilSeparable` |
| 84 | `HasseWeil.WeilPairing.OneSubProjOrdTransport` |
| 85 | `HasseWeil.WeilPairing.PencilCovariance` |
| 86 | `HasseWeil.WeilPairing.PencilComapScaling` |
| 87 | `HasseWeil.WeilPairing.PencilComapWitnesses` |
| 88 | `HasseWeil.WeilPairing.HasseBound` |

## Notes

This file is the project's **umbrella/façade module**. It exists so that `import HasseWeil`
in any downstream file or test gives access to the entire library without needing to enumerate
individual sub-modules. It carries no mathematical content and no proof obligations of its own.
All actual declarations live in the 88 imported sub-modules listed above.
