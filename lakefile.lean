import Lake

open System Lake DSL

package «tsp_research» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

@[default_target]
lean_lib «TSPComplexity» where
  roots := #[`TSPComplexity, `Christofides, `ChallengeTSPComplexity, `ChallengeChristofides]
