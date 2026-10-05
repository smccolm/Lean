import DongWangWangZhang2026.SmallRangeZeroCriterion
import DongWangWangZhang2026.LargeSumEstimate

/-!
# Theorem 1.2: cancellation from the actual local zero-window hypothesis

The absolute window constant is chosen before A. The bound constant is
chosen before delta, epsilon, heights and cutoffs. The two closed cutoff
ranges meet at sqrt T, and the public epsilon condition remains strict.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex

/-- The large-x power saving implies the required logarithmic saving uniformly on x ≤ T^A. -/
theorem large_x_zeta_sum_log_bound {T t x A : ℝ} (hT : 4096 ≤ T)
    (htlow : T ≤ |t|) (httop : |t| ≤ 2 * T) (hx : Real.sqrt T ≤ x)
    (hA : 0 < A) (hxA : x ≤ T ^ A) :
    ‖zetaSum x t‖ ≤ (3000 * A ^ (1 / 100 : ℝ)) * x /
      (Real.log x) ^ (1 / 100 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hroot : 2 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hY : 0 < Real.log x := Real.log_pos hx1
  have hYpow : 0 < (Real.log x) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hY _
  have hlog : Real.log x ≤ A * T := by
    have h := Real.log_le_log hx0 hxA
    rw [Real.log_rpow hT0] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.log_le_self hT0.le) hA.le)
  have hpower : (Real.log x) ^ (1 / 100 : ℝ) ≤
      A ^ (1 / 100 : ℝ) * T ^ (1 / 100 : ℝ) := by
    have h := Real.rpow_le_rpow hY.le hlog (by norm_num : (0 : ℝ) ≤ 1 / 100)
    simpa only [Real.mul_rpow hA.le hT0.le] using h
  have hsaving : T ^ (-1 / 13 : ℝ) * T ^ (1 / 100 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hT0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
  apply (le_div_iff₀ hYpow).mpr
  calc
    _ ≤ (3000 * x * T ^ (-1 / 13 : ℝ)) * (Real.log x) ^ (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right (large_x_zeta_sum_bound hT htlow httop hx) hYpow.le
    _ ≤ (3000 * x * T ^ (-1 / 13 : ℝ)) *
        (A ^ (1 / 100 : ℝ) * T ^ (1 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = ((3000 * A ^ (1 / 100 : ℝ)) * x) *
        (T ^ (-1 / 13 : ℝ) * T ^ (1 / 100 : ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hsaving

/-- The exact public source Theorem 1.2 on the full polynomial cutoff range. -/
theorem local_zero_windows_force_zeta_sum_cancellation :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A →
      ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T t ε : ℝ,
          T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
          (Real.log T) ^ (-1 / 3 : ℝ) < ε →
          (∀ u : ℝ, |u - t| ≤ C * (Real.log T) ^ (1 / 100 : ℝ) →
            (zeroCountIn (sourceZeroWindow u δ) : ℝ) ≤ δ * ε ^ 2 * Real.log T / 400) →
          ∀ x : ℝ, T ^ ε ≤ x → x ≤ T ^ A →
            ‖zetaSum x t‖ ≤ K * x / (Real.log x) ^ (1 / 100 : ℝ) := by
  obtain ⟨C, hC, hsmall⟩ := exists_small_range_local_zero_cancellation
  refine ⟨C, hC, ?_⟩
  intro A hA
  let K := max 1 (3000 * A ^ (1 / 100 : ℝ))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKlarge : 3000 * A ^ (1 / 100 : ℝ) ≤ K := le_max_right _ _
  refine ⟨K, by linarith, ?_⟩
  intro δ hδ hδ4
  obtain ⟨T₁, hT₁, hsmallδ⟩ := hsmall δ hδ hδ4
  refine ⟨max T₁ 4096, hT₁.trans (le_max_left _ _), ?_⟩
  intro T t ε hT₀ htlow httop hε hwindows x hxlow hxtop
  have hTold : T₁ ≤ T := (le_max_left _ _).trans hT₀
  have hTlarge : 4096 ≤ T := (le_max_right _ _).trans hT₀
  have hT0 : 0 < T := by linarith
  have hQ : 0 < Real.log T := Real.log_pos (by linarith)
  have hε0 : 0 < ε := (Real.rpow_pos_of_pos hQ _).trans hε
  have hx0 : 0 < x := (Real.rpow_pos_of_pos hT0 ε).trans_le hxlow
  have hY : 0 < Real.log x := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hT0 ε) hxlow
    rw [Real.log_rpow hT0] at h
    exact (mul_pos hε0 hQ).trans_le h
  by_cases hxsmall : x ≤ Real.sqrt T
  · apply (hsmallδ T t ε hTold htlow httop hε hwindows x hxlow hxsmall).trans
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
    nlinarith only [mul_le_mul_of_nonneg_right hK1 hx0.le]
  · apply (large_x_zeta_sum_log_bound hTlarge htlow httop (lt_of_not_ge hxsmall).le hA hxtop).trans
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
    exact mul_le_mul_of_nonneg_right hKlarge hx0.le

end
end DongWangWangZhang2026

