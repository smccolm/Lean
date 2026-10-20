/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-! # Integral reduction input for original unitary arithmetic quotient finiteness

Adapted from TauCetiProject/TauCeti, commit
9fc5d5a87d00cb696e606ccdae66420cc837c05e, under Apache-2.0.
Only the dependency needed for positive definite integral form classes is
ported. The exact open chain is DUB-17 -> integral unitary auxiliary
automorphic modules -> finite original arithmetic double cosets ->
bounded classes of the actual integral trace lattices. The construction,
local comparison and determinant bound for those original lattices remain
separate obligations; this result alone does not close that chain.
-/

namespace Dubon2026

noncomputable section

/-- Every integer lies within `μ / 2` of a multiple of a positive integer `μ`. -/
theorem int_exists_nearest_multiple (t : ℤ) {μ : ℤ} (hμ : 0 < μ) :
    ∃ c : ℤ, 2 * |t - c * μ| ≤ μ := by
  set c := round ((t : ℚ) / μ)
  refine ⟨c, ?_⟩
  have hμ' : (0 : ℚ) < μ := by exact_mod_cast hμ
  have hr : |(t : ℚ) / μ - c| ≤ 1 / 2 := abs_sub_round _
  have hrel : ((t - c * μ : ℤ) : ℚ) = μ * ((t : ℚ) / μ - c) := by
    push_cast
    field_simp
  have hq : 2 * |((t - c * μ : ℤ) : ℚ)| ≤ μ := by
    rw [hrel, abs_mul, abs_of_pos hμ']
    nlinarith
  exact_mod_cast hq


end
end Dubon2026
