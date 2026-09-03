import GafniTao.HeathBrownClosePairs

/-!
# Heath-Brown's block parameter

The refined counting argument chooses `K = 1 + floor(4 A lambda N)`.
The strict inequality supplied by the floor is essential: it makes the
last derivative-coordinate vary by at most `1/2` within a block when
`A lambda <= 1/4`.  These lemmas keep that strict margin explicit.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownBlockParameter
    (A lambda : ℝ) (N : ℕ) : ℕ :=
  1 + ⌊4 * A * lambda * N⌋₊

theorem heathBrownBlockParameter_pos
    (A lambda : ℝ) (N : ℕ) :
    0 < heathBrownBlockParameter A lambda N := by
  unfold heathBrownBlockParameter
  omega

theorem heathBrown_scale_lt_blockParameter
    {A lambda : ℝ} {N : ℕ} :
    4 * A * lambda * N <
      (heathBrownBlockParameter A lambda N : ℝ) := by
  unfold heathBrownBlockParameter
  push_cast
  simpa [add_comm] using Nat.lt_floor_add_one (4 * A * lambda * N)

/-- The exact strict half-unit margin used to remove wrapping in the last
coordinate. -/
theorem heathBrown_block_scale_lt_half
    {A lambda : ℝ} {N : ℕ}
    (hsmall : A * lambda ≤ 1 / 4) :
    A * lambda *
        (1 + (N : ℝ) / heathBrownBlockParameter A lambda N) <
      1 / 2 := by
  let K := heathBrownBlockParameter A lambda N
  have hKposNat : 0 < K := heathBrownBlockParameter_pos A lambda N
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hKposNat
  have hscale : 4 * A * lambda * N < (K : ℝ) :=
    heathBrown_scale_lt_blockParameter
  have hquot : A * lambda * (N : ℝ) / K < 1 / 4 := by
    rw [div_lt_iff₀ hKpos]
    nlinarith
  have hrewrite :
      A * lambda * (1 + (N : ℝ) / K) =
        A * lambda + A * lambda * (N : ℝ) / K := by ring
  rw [hrewrite]
  linarith

theorem heathBrown_block_scale_le_half
    {A lambda : ℝ} {N : ℕ}
    (hsmall : A * lambda ≤ 1 / 4) :
    A * lambda *
        (1 + (N : ℝ) / heathBrownBlockParameter A lambda N) ≤
      1 / 2 :=
  (heathBrown_block_scale_lt_half hsmall).le

#print axioms heathBrownBlockParameter_pos
#print axioms heathBrown_scale_lt_blockParameter
#print axioms heathBrown_block_scale_lt_half
#print axioms heathBrown_block_scale_le_half

end

end GafniTao
