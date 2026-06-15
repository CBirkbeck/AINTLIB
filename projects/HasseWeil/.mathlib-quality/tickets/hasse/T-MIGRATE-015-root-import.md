# T-MIGRATE-015: Update HasseWeil.lean root file

**Status**: OPEN
**Module**: `HasseWeil.lean`
**Owner**: (unassigned)
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: M

## Depends on
- T-MIGRATE-002..014 (all migrations done)

## Blocks
- (FINAL)

## Statement
Update the root `HasseWeil.lean` file to import the new tree:
```lean
import HasseWeil.Auxiliary.Universal
import HasseWeil.Auxiliary.PullbackKaehler
import HasseWeil.Auxiliary.DiffQuotientRule
import HasseWeil.Auxiliary.DivisionPolynomial
import HasseWeil.Auxiliary.EllipticDivisibilitySequence
import HasseWeil.Curves.Basic
import HasseWeil.Curves.Maps
import HasseWeil.Curves.Divisors
import HasseWeil.Curves.Differentials
import HasseWeil.EC.Weierstrass
import HasseWeil.EC.GroupLaw
import HasseWeil.EC.PicE
import HasseWeil.EC.Isogeny
import HasseWeil.EC.IsogenyFactor
import HasseWeil.EC.InvariantDiff
import HasseWeil.EC.DualIsogeny
import HasseWeil.EC.DegreeForm
import HasseWeil.FormalGroup.Definition
import HasseWeil.FormalGroup.Curve
import HasseWeil.FormalGroup.Operations
import HasseWeil.FormalGroup.Associated
import HasseWeil.FormalGroup.InvariantDiff
import HasseWeil.FormalGroup.Logarithm
import HasseWeil.FormalGroup.DVR
import HasseWeil.FormalGroup.Height
import HasseWeil.FormalGroup.Bridge
import HasseWeil.Frobenius.AsAlgHom
import HasseWeil.Frobenius.PointFix
import HasseWeil.Frobenius.Inseparable
import HasseWeil.Hasse.PointCount
import HasseWeil.Hasse.CauchySchwarz
import HasseWeil.Hasse.HasseBound
```

## Acceptance criteria
- Root file imports the new tree
- `lake build HasseWeil` succeeds with 0 sorries

## Progress log
