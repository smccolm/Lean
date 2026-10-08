import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Genuine Banach-valued power series from the original geometric coefficient bound -/

namespace Dubon2026

noncomputable section

/-- The genuine vector power series with its supplied original coefficient vectors. -/
def vectorPowerSeries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ → E) (z : ℂ) : E := ∑' n : ℕ, z ^ n • q n

/-- Original geometrically bounded vector coefficients have an exact geometric majorant on every smaller complex disk. -/
theorem vectorPowerSeries_term_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ → E) {K R : ℝ} (hR : 0 ≤ R)
    (hq : ∀ n : ℕ, ‖q n‖ ≤ K * 2 ^ n) {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖z ^ n • q n‖ ≤ K * (2 * R) ^ n := by
  calc
    _ = ‖z‖ ^ n * ‖q n‖ := by rw [norm_smul, norm_pow]
    _ ≤ R ^ n * (K * 2 ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz n) (hq n) (norm_nonneg _) (pow_nonneg hR n)
    _ = K * (2 * R) ^ n := by rw [mul_pow]; ring

/-- The original vector power series converges absolutely at every point of its proved disk. -/
theorem vectorPowerSeries_summable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (q : ℕ → E) {K : ℝ}
    (hq : ∀ n : ℕ, ‖q n‖ ≤ K * 2 ^ n) {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    Summable (fun n : ℕ => z ^ n • q n) := by
  have hg : ‖2 * ‖z‖‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hs : Summable (fun n : ℕ => K * (2 * ‖z‖) ^ n) :=
    (summable_geometric_of_norm_lt_one hg).mul_left K
  exact Summable.of_norm_bounded hs (fun n =>
    vectorPowerSeries_term_bound q (norm_nonneg z) hq le_rfl n)

/-- The genuine original vector power series is holomorphic on the full open disk forced by its proved coefficient bound. -/
theorem vectorPowerSeries_differentiableOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (q : ℕ → E) {K : ℝ}
    (hq : ∀ n : ℕ, ‖q n‖ ≤ K * 2 ^ n) :
    DifferentiableOn ℂ (vectorPowerSeries q) (Metric.ball 0 (1 / 2 : ℝ)) := by
  intro z hz
  have hz' : ‖z‖ < (1 / 2 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨R, hRz, hR⟩ := exists_between hz'
  have hR0 : 0 < R := (norm_nonneg z).trans_lt hRz
  have hg : ‖2 * R‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
  have hs : Summable (fun n : ℕ => K * (2 * R) ^ n) :=
    (summable_geometric_of_norm_lt_one hg).mul_left K
  have hd : DifferentiableOn ℂ (vectorPowerSeries q) (Metric.ball 0 R) :=
    Complex.differentiableOn_tsum_of_summable_norm hs
      (fun n => by fun_prop) Metric.isOpen_ball
      (fun n w hw => vectorPowerSeries_term_bound q hR0.le hq
        (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hw)) n)
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds
    (by simpa only [Metric.mem_ball, dist_zero_right] using hRz))).differentiableWithinAt

end
end Dubon2026
