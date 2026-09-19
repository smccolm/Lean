# Frozen ANTEDB compatibility subset

This package contains the exact source of the ten ANTEDB modules needed for
the first Tao--Trudgian--Yang compatibility and exponent-sum layers, copied
from `teorth/expdb` commit
`088040634e8300f87e80f431d8bdc38c42cc8e11`.

The upstream files target Lean `v4.32.0`. This frozen package intentionally
pins Lean `v4.30.0` and the local Riemann Zeta mathlib revision so that every
required compatibility change is visible in version control. The initial
copy was source-identical. The Lean 4.30 backport currently contains only the
following compatibility edits and retains the upstream Apache-2.0 license:

- removed redundant conversion subgoals and obsolete simplifier arguments in
  `Basic/PowerAsymptotics.lean`, while preserving the same statements; and
- replaced the newer `intervalIntegral.integral_congr_Ioo_of_le` helper in
  `ExponentialSums/LogPhase.lean` with the Lean 4.30
  `intervalIntegral.integral_congr` theorem and an explicit unordered-interval
  membership proof.

`SOURCE_SHA256SUMS.txt` records every frozen source file. The project runner
must verify it before building.
