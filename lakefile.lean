import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint.git" @ "11c82ed5b84417b0aecc4a22b89ee536ee832ff4"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

package AINTLIB where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩, ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`weak.verso.blueprint.autoDeps, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩ ]

@[default_target]
lean_lib AINTLIB where

lean_exe «blueprint-gen» where
  root := `AINTLIBMain
  supportInterpreter := true
