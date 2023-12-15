import Lake
open System Lake DSL

package «RegEx»

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.1.0"
require «Gamine» from ".."/"Gamine"
require «LString» from ".."/"LString"

@[default_target]
lean_lib «RegEx»
