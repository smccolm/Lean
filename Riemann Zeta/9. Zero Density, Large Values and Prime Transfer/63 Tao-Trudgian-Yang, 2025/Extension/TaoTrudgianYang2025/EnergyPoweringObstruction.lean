import TaoTrudgianYang2025.EnergyExponentTransfer

/-!
# Obstruction to the pinned source's five-coordinate powering claim

The unnormalized double zeta sum has exponent at least two. Singleton
patterns attain two, so the source assertion `s' ≤ s/k` cannot hold for
`k = 2`. This module records a counterexample, not a replacement powering
theorem or a claim against the paper's advertised endpoint estimates.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem singletonLargeValuePattern_doubleZetaSum
    (N : ℕ) (σ τ : ℝ) (hN : 1 < N) (hσ : σ ≤ 1) :
    doubleZetaSum (singletonLargeValuePattern N σ τ hN hσ) = (N + 1 : ℝ) ^ 2 := by
  have hcard : 2 * N + 1 - N = N + 1 := by omega
  simp only [doubleZetaSum, singletonLargeValuePattern, Finset.sum_singleton,
    sub_self, dirichletPhase_zero, Finset.sum_const, Nat.card_Icc,
    nsmul_one, Complex.norm_natCast]
  rw [hcard, Nat.cast_add, Nat.cast_one]

/-- Genuine singleton patterns realize `(σ, τ, 0, 0, 2)` at arbitrarily
large scales, with all approximation quantifiers in region membership. -/
theorem singleton_mem_largeValueEnergyRegion
    (σ τ : ℝ) (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    InLargeValueEnergyRegion σ τ 0 0 2 := by
  refine ⟨hσLower, hσUpper, hτ, le_rfl, le_rfl, ?_⟩
  intro ε hε δ hδ C _hC
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (max C (max 2 ((4 : ℝ) ^ (1 / ε))))
  have hCN : C ≤ (N : ℝ) := (le_max_left _ _).trans hNlarge.le
  have hNtwo : (2 : ℝ) < N := (le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hNlarge)
  have hN : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  have hNreal : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hFour : (4 : ℝ) ≤ (N : ℝ) ^ ε := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hNlarge.le)) hε.le
    have heq : ((4 : ℝ) ^ (1 / ε)) ^ ε = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        one_div_mul_cancel hε.ne', Real.rpow_one]
    rwa [heq] at hp
  have hOneLower : (N : ℝ) ^ (0 - ε) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : 0 - ε ≤ 0)
  have hOneUpper : (1 : ℝ) ≤ (N : ℝ) ^ (0 + ε) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : 0 ≤ 0 + ε)
  have hSumLower : (N : ℝ) ^ (2 - ε) ≤ (N + 1 : ℝ) ^ 2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : 2 - ε ≤ 2)
    rw [Real.rpow_two] at hp
    nlinarith
  have hSumUpper : (N + 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 + ε) := by
    rw [Real.rpow_add hNpos, Real.rpow_two]
    calc
      (N + 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * 4 := by nlinarith
      _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hFour (sq_nonneg _)
  refine ⟨singletonLargeValuePattern N σ τ hN hσUpper, hCN, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : τ - δ ≤ τ)
  · exact Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : τ ≤ τ + δ)
  · exact Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : σ - δ ≤ σ)
  · exact Real.rpow_le_rpow_of_exponent_le hNreal (by linarith : σ ≤ σ + δ)
  · simpa only [singletonLargeValuePattern, Finset.card_singleton, Nat.cast_one] using hOneLower
  · simpa only [singletonLargeValuePattern, Finset.card_singleton, Nat.cast_one] using hOneUpper
  · simpa only [singletonLargeValuePattern_energy, Nat.cast_one] using hOneLower
  · simpa only [singletonLargeValuePattern_energy, Nat.cast_one] using hOneUpper
  · simpa only [singletonLargeValuePattern_doubleZetaSum] using hSumLower
  · simpa only [singletonLargeValuePattern_doubleZetaSum] using hSumUpper

/-- The diagonal constraint and nonnegative cardinality exponent force
every point of the actual five-dimensional region to have `s ≥ 2`. -/
theorem InLargeValueEnergyRegion.two_le_s
    {σ τ ρ ρstar s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    2 ≤ s := by
  have hρ := h.2.2.2.1
  have hs := h.rho_add_two_le_s
  linarith

/-- Even a single output point with the coordinate upper bounds required
by source Lemma 62 is impossible for this input and `k = 2`. Thus the
source's stronger three-witness statement is false as printed. -/
theorem energyPowering_source_counterexample :
    InLargeValueEnergyRegion (3 / 4) 2 0 0 2 ∧
      ¬ ∃ ρ' ρstar' s' : ℝ,
        InLargeValueEnergyRegion (3 / 4) (2 / 2) ρ' ρstar' s' ∧
          ρ' ≤ 0 / 2 ∧ ρstar' ≤ 0 / 2 ∧ s' ≤ 2 / 2 := by
  constructor
  · exact singleton_mem_largeValueEnergyRegion _ _ (by norm_num) (by norm_num) (by norm_num)
  · rintro ⟨ρ', ρstar', s', hregion, _hρ, _hρstar, hs⟩
    have hlower := hregion.two_le_s
    norm_num at hs
    linarith

end TaoTrudgianYang2025
