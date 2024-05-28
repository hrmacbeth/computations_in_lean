import Lake
open Lake DSL


package «polyrith-tutorial» {
  -- add package configuration options here
}

@[default_target]
lean_lib PolyrithTutorial {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ s!"8932a3d688d2bbf500429c4c888de4181086aad5"
