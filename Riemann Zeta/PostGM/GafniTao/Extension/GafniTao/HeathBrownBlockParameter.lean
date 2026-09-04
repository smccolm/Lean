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

/-- A nonnegative derivative bounded by `M` controls the absolute difference
between two sampled values. -/
theorem heathBrown_abs_difference_le_deriv_bound
    {N : ℕ} {g : ℝ → ℝ} {M : ℝ}
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), 0 ≤ deriv g x)
    (hderivUpper : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), deriv g x ≤ M)
    {m n : ℕ} (hm : m ≤ N) (hn : n ≤ N) :
    |g m - g n| ≤ M * |(m : ℝ) - n| := by
  have hmI : (m : ℝ) ∈ Set.Icc (0 : ℝ) N :=
    ⟨by positivity, by exact_mod_cast hm⟩
  have hnI : (n : ℝ) ∈ Set.Icc (0 : ℝ) N :=
    ⟨by positivity, by exact_mod_cast hn⟩
  rcases le_total m n with hmn | hnm
  · have hlower := heathBrown_lower_slope hg hgd hderivLower hmI hnI
      (by exact_mod_cast hmn)
    have hupper := heathBrown_upper_slope hg hgd hderivUpper hmI hnI
      (by exact_mod_cast hmn)
    rw [abs_of_nonpos (sub_nonpos.mpr (by linarith)),
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hmn)), neg_sub, neg_sub]
    exact hupper
  · have hlower := heathBrown_lower_slope hg hgd hderivLower hnI hmI
      (by exact_mod_cast hnm)
    have hupper := heathBrown_upper_slope hg hgd hderivUpper hnI hmI
      (by exact_mod_cast hnm)
    rw [abs_of_nonneg (sub_nonneg.mpr (by linarith)),
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm))]
    exact hupper

/-- The actual localized-pair separation supplied by the natural quotient is
no larger than the real block length used in the source estimate. -/
theorem heathBrown_pairCountTwo_index_le_block_length
    {A lambda : ℝ} {N k H m n : ℕ} {f : ℝ → ℝ}
    (hp : (m, n) ∈ heathBrownPairCountTwo N k H
      (heathBrownBlockParameter A lambda N) f) :
    |(m : ℝ) - n| ≤
      1 + (N : ℝ) / heathBrownBlockParameter A lambda N := by
  rw [mem_heathBrownPairCountTwo] at hp
  let L := 1 + N / heathBrownBlockParameter A lambda N
  have hNat : Nat.dist m n ≤ L := hp.2.2.2.2.1
  have hcast : |(m : ℝ) - n| ≤ (L : ℝ) := by
    rcases le_total m n with hmn | hnm
    · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hmn)), neg_sub,
        ← Nat.cast_sub hmn]
      rw [Nat.dist_eq_sub_of_le hmn] at hNat
      exact_mod_cast hNat
    · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm)),
        ← Nat.cast_sub hnm]
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hnm] at hNat
      exact_mod_cast hNat
  calc
    |(m : ℝ) - n| ≤ (L : ℝ) := hcast
    _ = 1 + ((N / heathBrownBlockParameter A lambda N : ℕ) : ℝ) := by
      simp [L]
    _ ≤ 1 + (N : ℝ) / heathBrownBlockParameter A lambda N := by
      gcongr
      exact Nat.cast_div_le

#print axioms heathBrownBlockParameter_pos
#print axioms heathBrown_scale_lt_blockParameter
#print axioms heathBrown_block_scale_lt_half
#print axioms heathBrown_block_scale_le_half
#print axioms heathBrown_abs_difference_le_deriv_bound
#print axioms heathBrown_pairCountTwo_index_le_block_length

end

end GafniTao
