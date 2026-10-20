import Lake

open System Lake DSL

package «tsp_research» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "953c8992d174b4e56955e01e101d46668c68f2bb"

@[default_target]
lean_lib «TSPComplexity» where
  roots := #[`TSPComplexity, `Christofides]
