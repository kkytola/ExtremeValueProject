import Lake
open Lake DSL

package «ExtremeValueProject» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0-rc2"

@[default_target]
lean_lib «ExtremeValueProject» where
  -- add any library configuration options here

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.34.0-rc2"