import TaoTrudgianYang2025.ZetaShortPatterns

/-!
# Actual cancellation below twice the value exponent

On 7/10 <= sigma <= 3/4, every actual short zeta pattern is eventually empty
when 1 <= tau < 2*sigma. Emptiness follows from the literal polynomial bound.
-/

noncomputable section

open Filter MeasureTheory Set

namespace TaoTrudgianYang2025

theorem exists_zetaBelowTwiceSigma_empty_uniform_threshold {σ τ : ℝ}
    (_hσ : 7 / 10 ≤ σ) (hσhi : σ ≤ 3 / 4) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
      P.N ^ (σ - δ) ≤ P.V → P.ordinates = ∅ := by
  let δ : ℝ := (2 * σ - τ) / 8
  let β : ℝ := σ - 2 * δ
  let K : ℝ := 2 + 200 * Real.sqrt 2 + 12 * Real.pi
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδhi : δ ≤ 1 / 16 := by dsimp [δ]; linarith
  have hτδ : τ + 8 * δ = 2 * σ := by dsimp [δ]; ring
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβδ : δ ≤ β := by dsimp [β]; linarith
  have hevent : ∀ᶠ N : ℝ in atTop, K < N ^ δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_gt_atTop K)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 4 N₀, δ, (by have := le_max_left (4 : ℝ) N₀; linarith), hδ, ?_⟩
  intro P hN hTl hTu hVl
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hNfour : 4 ≤ P.N := (le_max_left _ _).trans hN
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have htint : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have htone : 1 ≤ t := (Real.one_le_rpow P.one_lt_N.le
    (by linarith : 0 ≤ τ - δ)).trans (hTl.trans htint.1)
  have htupper : t ≤ 2 * P.N ^ (3 / 2 : ℝ) := htint.2.trans
    ((mul_le_mul_of_nonneg_left hTu (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
        (by linarith : τ + δ ≤ 3 / 2)) (by norm_num)))
  have hhalf : 2 ≤ P.N ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (by norm_num : (2 : ℝ) = Real.sqrt 4) ▸ Real.sqrt_le_sqrt hNfour
  have htNsq : t ≤ P.N ^ 2 := by
    calc
      _ ≤ 2 * P.N ^ (3 / 2 : ℝ) := htupper
      _ ≤ P.N ^ (1 / 2 : ℝ) * P.N ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hNpos.le _)
      _ = _ := by rw [← Real.rpow_add hNpos]; norm_num
  have hsqrt : Real.sqrt t ≤ Real.sqrt 2 * P.N ^ β := by
    have hpow : t ≤ 2 * P.N ^ (2 * β) := htint.2.trans
      ((mul_le_mul_of_nonneg_left hTu (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
          (by dsimp [β]; linarith : τ + δ ≤ 2 * β)) (by norm_num)))
    calc
      _ ≤ Real.sqrt (2 * P.N ^ (2 * β)) := Real.sqrt_le_sqrt hpow
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (P.N ^ (2 * β)),
          ← Real.rpow_mul hNpos.le]
        congr 2
        ring
  have hquot : P.N / t ≤ P.N ^ β := by
    apply (div_le_iff₀ (zero_lt_one.trans_le htone)).2
    calc
      _ = P.N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ P.N ^ (β + (τ - δ)) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
      _ = P.N ^ β * P.N ^ (τ - δ) := Real.rpow_add hNpos _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hTl.trans htint.1) (Real.rpow_nonneg hNpos.le _)
  have hmajorant : 2 + 200 * Real.sqrt t + 12 * Real.pi * P.N / t ≤ K * P.N ^ β := by
    have hone := Real.one_le_rpow P.one_lt_N.le hβ
    have hq := mul_le_mul_of_nonneg_left hquot (by positivity : 0 ≤ 12 * Real.pi)
    dsimp [K]
    rw [← mul_div_assoc] at hq
    nlinarith
  have hstrict : K * P.N ^ β < P.N ^ (σ - δ) := by
    calc
      _ < P.N ^ δ * P.N ^ β := mul_lt_mul_of_pos_right
        (hN₀ P.N ((le_max_right _ _).trans hN)) (Real.rpow_pos_of_pos hNpos _)
      _ = P.N ^ (δ + β) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by dsimp [β]; linarith)
  exact (not_lt_of_ge hVl) (((P.large t ht).trans
    ((P.polynomial_norm_le_short_majorant htone htNsq).trans hmajorant)).trans_lt hstrict)

theorem zetaBelowTwiceSigma_largeValueBound_any {σ τ : ℝ}
    (hσ : 7 / 10 ≤ σ) (hσhi : σ ≤ 3 / 4) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) (B : ℝ) :
    IsZetaLargeValueBound σ τ B := by
  obtain ⟨C, δ, hC, hδ, h⟩ := exists_zetaBelowTwiceSigma_empty_uniform_threshold hσ hσhi hτ hτhi
  intro ε _
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl _
  rw [h P hN hTl hTu hVl, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)

theorem zetaBelowTwiceSigma_energyBound_any {σ τ : ℝ}
    (hσ : 7 / 10 ≤ σ) (hσhi : σ ≤ 3 / 4) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) (B : ℝ) :
    IsZetaLargeValueEnergyBound σ τ B := by
  have h := (zetaBelowTwiceSigma_largeValueBound_any hσ hσhi hτ hτhi (B / 3)).toEnergyBound_three_mul
  convert h using 1
  ring

end TaoTrudgianYang2025
