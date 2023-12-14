import Lake
open Lake DSL

package «Root» where
  -- add configuration options here

require «Gamine» from "Gamine"
require «RegEx» from "RegEx"
require «LString» from "LString"
require «SoupL» from "SoupL"

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.1.0"

@[default_target]
lean_exe Root where
  root := `Main
