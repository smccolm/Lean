import TaoTrudgianYang2025.ZetaPerronEntry

/-!
# Perron entry with a threshold-relative error

The fourth-order tail need not be bounded by a constant. On the short
height range it is absorbed against the actual large-value threshold.
-/

noncomputable section

open Filter Set

namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.perron_entry_with_scaled_error (P : ZetaLargeValuePattern)
    (hscale : P.N ^ (23 / 16 : ℝ) ≤ P.T)
    (hvalue : 2 * zetaPerronError * P.N ^ (5 / 8 : ℝ) ≤ P.V)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  obtain ⟨a, b, hactive⟩ := P.active_isInterval
  have hne := P.active_nonempty_of_mem_ordinates ht
  have hinterval : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hscale
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by norm_num : (1 : ℝ) ≤ 23 / 16)
  have hone : 1 ≤ P.N ^ (5 / 8 : ℝ) := Real.one_le_rpow P.one_lt_N.le (by norm_num)
  have hres : zetaCutoffMellinConstant 4 1 * P.N ^ 4 / (1 + |t|) ^ 4 ≤
      zetaCutoffMellinConstant 4 1 * P.N ^ (5 / 8 : ℝ) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hone (zetaCutoffMellinConstant_pos _ _).le)
    rw [mul_one]
    apply (div_le_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).2
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hNpos.le (by linarith [hinterval.1, le_abs_self t]) 4)
      (zetaCutoffMellinConstant_pos _ _).le
  have hTp : P.N ^ (23 / 8 : ℝ) ≤ P.T ^ 2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le (23 / 16)) hscale 2
    have heq : (P.N ^ (23 / 16 : ℝ)) ^ 2 = P.N ^ (23 / 8 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hNpos.le]
      norm_num
    rwa [heq] at h
  have hfarPower : P.N ^ (7 / 2 : ℝ) ≤ P.N ^ (5 / 8 : ℝ) * P.T ^ 2 := by
    calc
      _ = P.N ^ (5 / 8 : ℝ) * P.N ^ (23 / 8 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hTp (Real.rpow_nonneg hNpos.le _)
  have hfar : 120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / P.T ^ 2 ≤
      120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (5 / 8 : ℝ) := by
    apply (div_le_iff₀ (pow_pos P.T_pos 2)).2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfarPower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 120) (zetaCutoffMellinConstant_pos _ _).le)
  have hpoly := (P.large t ht).trans
    (P.polynomial_norm_le_convolution_and_errors hactive hne hinterval)
  unfold zetaPerronError at hvalue
  unfold zetaPerronConstant
  nlinarith

theorem exists_zetaPerron_short_uniform_threshold :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ σ τ δ : ℝ, 3 / 4 ≤ σ → 3 / 2 ≤ τ → δ ≤ 1 / 16 →
        P.N ^ (τ - δ) ≤ P.T → P.N ^ (σ - δ) ≤ P.V →
          ∀ t ∈ P.ordinates,
            P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  have hevent : ∀ᶠ N : ℝ in atTop, 2 * zetaPerronError ≤ N ^ (1 / 16 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).eventually
      (eventually_ge_atTop (2 * zetaPerronError))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro P hN σ τ δ hσ hτ hδ hT hV t ht
  apply P.perron_entry_with_scaled_error _ _ ht
  · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith : (23 / 16 : ℝ) ≤ τ - δ)).trans hT
  · have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
    calc
      _ ≤ P.N ^ (1 / 16 : ℝ) * P.N ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (hN₀ P.N ((le_max_right _ _).trans hN))
          (Real.rpow_nonneg hNpos.le _)
      _ = P.N ^ (11 / 16 : ℝ) := by rw [← Real.rpow_add hNpos]; norm_num
      _ ≤ P.N ^ (σ - δ) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
      _ ≤ P.V := hV

end TaoTrudgianYang2025
