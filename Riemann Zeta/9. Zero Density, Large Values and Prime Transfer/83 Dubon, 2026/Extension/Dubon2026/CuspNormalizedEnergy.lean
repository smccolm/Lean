import Dubon2026.CuspRankinSeries
import Dubon2026.WeightedEnergyAbel

/-! # The linear upper bound for genuine normalized cusp square sums -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup MeasureTheory Set

noncomputable section

/-- The actual Parseval bound also holds at every real cutoff above one. -/
theorem cusp_squareSummatory_le_power {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ‖cuspCoefficients f n‖ ^ 2) ≤ C * (N : ℝ) ^ k)
    {x : ℝ} (hx : 1 ≤ x) :
    squareSummatory (cuspCoefficients f) x ≤ C * x ^ (k : ℝ) := by
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hh := hb ⌊x⌋₊ hfloor
  rw [← Real.rpow_intCast] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith))
      (by exact_mod_cast hk)) hC)

/-- Abel summation converts the proved weight-k Parseval estimate into an actual linear
bound for the automorphically normalized coefficients, without assuming a Rankin asymptotic. -/
theorem exists_normalized_cusp_square_upper {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2) ≤ B * N := by
  obtain ⟨C, hC, hb⟩ := exists_cusp_coefficient_energy_upper f
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  refine ⟨C * (k : ℝ), mul_pos hC (by exact_mod_cast hk), fun N => ?_⟩
  by_cases hN : N = 0
  · subst N
    simp
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by positivity
  have he : (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2) =
      coefficientEnergy (cuspCoefficients f) N (((k : ℝ) - 1) / 2) := by
    unfold coefficientEnergy
    apply Finset.sum_congr rfl
    intro n _
    rw [norm_sq_normalizedCuspCoefficients]
    congr 2
    ring
  rw [he, coefficientEnergy_abel _ hN1]
  have hterm : squareSummatory (cuspCoefficients f) N *
      (N : ℝ) ^ (-2 * (((k : ℝ) - 1) / 2)) ≤ C * N := by
    calc
      _ ≤ (C * (N : ℝ) ^ (k : ℝ)) * (N : ℝ) ^ (-2 * (((k : ℝ) - 1) / 2)) :=
        mul_le_mul_of_nonneg_right (cusp_squareSummatory_le_power f hk.le hC.le hb hNr)
          (Real.rpow_nonneg hN0.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hN0]
        convert rfl using 1
        ring_nf
        simp
  have hint : (∫ x in Ioc (1 : ℝ) N, squareSummatory (cuspCoefficients f) x *
      x ^ (-2 * (((k : ℝ) - 1) / 2) - 1)) ≤ C * ((N : ℝ) - 1) := by
    calc
      _ ≤ ∫ _x in Ioc (1 : ℝ) N, C := by
        apply integral_mono_ae
          ((squareSummatory_integrable_power _ N _).mono_set Ioc_subset_Icc_self)
          (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hx0 : 0 < x := by linarith [hx.1]
        calc
          _ ≤ (C * x ^ (k : ℝ)) * x ^ (-2 * (((k : ℝ) - 1) / 2) - 1) :=
            mul_le_mul_of_nonneg_right (cusp_squareSummatory_le_power f hk.le hC.le hb hx.1.le)
              (Real.rpow_nonneg hx0.le _)
          _ = C := by
            rw [mul_assoc, ← Real.rpow_add hx0]
            convert mul_one C using 2
            ring_nf
            simp
      _ = _ := by simp [sub_nonneg.mpr hNr, mul_comm]
  have hi := mul_le_mul_of_nonneg_left hint
    (show 0 ≤ 2 * (((k : ℝ) - 1) / 2) by linarith)
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hk1)]

end
end Dubon2026
