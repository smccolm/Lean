import Dubon2026.UnitLogTail
import Dubon2026.UnitIntervalAverage

/-! # A uniform logarithmic truncation bound for symmetric vertical means -/

namespace Dubon2026

open MeasureTheory Set

noncomputable section

theorem intervalIntegrable_verticalFamily_logTruncationError (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (z : PrimeTorus N) {ε : ℝ} (hε : 0 < ε) (left right : ℝ) :
    IntervalIntegrable (fun t => logTruncationError ε (verticalFamily a N σ z t))
      volume left right := by
  have hc : Continuous (verticalFamily a N σ z) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticAt_verticalFamily a N σ z t).continuousAt)
  exact (((truncatedLogNorm ε hε).continuous.comp hc).intervalIntegrable left right).sub
    (intervalIntegrable_vertical_log (twistedCoefficients a N z) N σ left right)

theorem exists_uniform_vertical_logTruncationError_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∃ (K : ℕ) (η C : ℝ), 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ R : ℝ, 0 ≤ R → ∀ T : ℝ, 1 ≤ T →
        (2 * T)⁻¹ * (∫ t in -T..T,
          logTruncationError (η * Real.exp (-(K : ℝ) * R))
            (dirichletSum a N ((σ : ℂ) + Complex.I * t))) ≤
          2 * (K : ℝ) * C * Real.exp (-R) := by
  obtain ⟨K, η, C, hK, hη, hC, hb⟩ := exists_uniform_unit_logTruncationError_bound hN ha σ
  refine ⟨K, η, C, hK, hη, hC, ?_⟩
  intro R hR T hT
  let ε := η * Real.exp (-(K : ℝ) * R)
  let f : ℝ → ℝ := fun t => logTruncationError ε (verticalFamily a N σ 0 t)
  have hε : 0 < ε := mul_pos hη (Real.exp_pos _)
  have hf : ∀ x y, IntervalIntegrable f volume x y :=
    intervalIntegrable_verticalFamily_logTruncationError a N σ 0 hε
  have hn : 0 ≤ᵐ[volume] f := by
    filter_upwards [verticalFamily_ne_zero_ae hN ha σ 0] with t ht
    exact logTruncationError_nonneg ht
  have hu (x : ℝ) : (∫ t in x..x + 1, f t) ≤ (K : ℝ) * C * Real.exp (-R) := by
    have he : (∫ t in x..x + 1, f t) = ∫ t in (0 : ℝ)..1,
        logTruncationError ε (verticalFamily a N σ (primeTorusFlow N x) t) := by
      calc
        _ = ∫ t in (0 : ℝ)..1, f (t + x) := by
          simpa only [zero_add, add_comm x 1] using
            (intervalIntegral.integral_comp_add_right (a := 0) (b := 1) f x).symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro t _
          simp only [f, verticalFamily_add_height, zero_add]
    rw [he, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact hb (primeTorusFlow N x) R hR
  have havg := symmetric_mean_le_two_of_unit_bound hf hn
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg K) hC.le) (Real.exp_pos _).le) hu hT
  simpa only [f, ε, verticalFamily_zero_phase, mul_assoc] using havg

end

end Dubon2026
