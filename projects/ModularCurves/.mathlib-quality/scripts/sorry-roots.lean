/-
`sorry`-ROOT BISECTOR — which sorried declarations does a target actually depend on?

Usage:  lake env lean projects/ModularCurves/.mathlib-quality/scripts/sorry-roots.lean

`#print axioms T` tells you *that* `T` inherits `sorryAx`; it never tells you *from where*.
This walks the value-level dependency cone of `T` and reports every declaration in it whose
own body mentions `sorryAx` — i.e. the actual leaves you must close to make `T`
axiom-verified. Edit the name list at the bottom.

GOTCHA (cost a pass to find): in this Lean, `ConstantInfo.value?` takes an
`allowOpaque := false` argument and returns `none` for THEOREMS. A traversal written with
`ci.value?` therefore visits exactly one node and reports 0 roots — silently. Match on
`.thmInfo v => v.value` explicitly, as below.

Note the cone is large (≈ 55k–85k constants for the Y(ρ̄) targets); each report takes a
minute or two. Run it under `timeout 1800`.
-/
import ModularCurves.ModularCurve.RhoPoints
import ModularCurves.ModularCurve.YFullFromYOne
import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.GammaHClosure

open Lean

private def usedConsts (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

private partial def go (env : Environment) (visited : IO.Ref NameSet)
    (roots : IO.Ref (Array Name)) (n : Name) : IO Unit := do
  if (← visited.get).contains n then return
  visited.modify (·.insert n)
  match env.find? n with
  | none => pure ()
  | some ci =>
    let us := usedConsts ci
    if us.contains `sorryAx then roots.modify (·.push n)
    for d in us do go env visited roots d

private def report (env : Environment) (n : Name) : IO Unit := do
  let visited ← IO.mkRef ({} : NameSet)
  let roots ← IO.mkRef (#[] : Array Name)
  go env visited roots n
  let rs ← roots.get
  IO.println s!"=== {n}: {rs.size} sorry-roots (visited {(← visited.get).size}) ==="
  for r in rs.qsort (fun a b => a.toString < b.toString) do IO.println s!"  {r}"

run_cmd Lean.Elab.Command.liftCoreM do
  let env ← getEnv
  for n in [``ModularCurves.yRho_representable,
            ``ModularCurves.yRho_geometricallyIrreducible,
            ``ModularCurves.YFull.exists_representing_smooth_affine,
            ``ModularCurves.yFullCandidate_representableBy,
            ``ModularCurves.YFull.gammaFullNaive_representable_assembly,
            ``ModularCurves.gammaOneNaive_representable,
            ``ModularCurves.gammaFullNaive_rigid_and_representable,
            ``ModularCurves.gammaFullDrinfeld_rigid_and_representable] do
    report env n
