import Lake
open Lake DSL

package «formalMAA302» {
  -- add any package configuration options here
}

@[default_target]
lean_lib «FormalMAA302» {
  -- add any library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"