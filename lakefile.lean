import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint.git" @ "v4.30.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "229580e5e4f991a61279c96e55b6c45c88866718"

package AINTLIB where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩, ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩ ]

@[default_target]
lean_lib AINTLIB where

lean_exe «blueprint-gen» where
  root := `AINTLIBMain
  supportInterpreter := true
