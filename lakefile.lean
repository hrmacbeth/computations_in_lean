import Lake
open Lake DSL


package «polyrith-tutorial» {
  -- add package configuration options here
}

@[default_target]
lean_lib PolyrithTutorial {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ s!"v{Lean.versionString}"