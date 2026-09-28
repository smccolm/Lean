import TaoTrudgianYang2025.ZetaLowHeightObstruction

open TaoTrudgianYang2025

namespace PrintedOldPairObstruction

/- The frozen paper's equation lvz-340 quantifies over every positive tau.
This test preserves its full domain and uses the existing actual-pattern
counterexample; it is not a counterexample to the old exponent pair,
the zeta-growth bound, or the high-height density applications. -/

theorem exact_source_threshold :
    (7/10 : ℝ)+(3/40)*(1/4) = 23/32 ∧ (23/32 : ℝ) < 3/4 := by
  norm_num

theorem printed_old_pair_nonexistence_is_false :
    ¬ (∀ σ τ : ℝ, 0 < τ → 1/2 ≤ σ → σ ≤ 1 →
      7/10+(3/40)*τ < σ → zetaLargeValueExponent σ τ = ⊥) := by
  intro h
  exact zetaLargeValueExponent_three_quarters_quarter_ne_bot
    (h (3/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

#print axioms exact_source_threshold
#print axioms printed_old_pair_nonexistence_is_false

end PrintedOldPairObstruction
