import Lake
open Lake DSL

require ExtremeValueProject from ".."
-- Last commit of the `v4.34.0` release line of Verso Blueprint on Lean v4.34.0-rc2.
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint" @ "cd210bfbf567bb3720fa798e00bb3bafdd3e500b"

package ExtremeValueProjectBlueprint where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib ExtremeValueProjectBlueprint where
