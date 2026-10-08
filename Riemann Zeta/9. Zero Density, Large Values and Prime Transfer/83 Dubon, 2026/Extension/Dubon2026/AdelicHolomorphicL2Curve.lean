import Dubon2026.AdelicProjectiveHolomorphicSlice
import Dubon2026.VectorGeometricPowerSeries
import Dubon2026.BoundedL2Series

/-! # The actual original holomorphic curve in the genuine arithmetic quotient L2 space -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory Filter
open scoped MatrixGroups Topology BigOperators

/-- The genuine L2-valued Taylor series of the original measurable adelic jets. -/
def adelicHolomorphicL2Curve (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (z : ℂ) :
    Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) :=
  vectorPowerSeries (adelicUnipotentTaylorCoefficient N f) z

/-- The original jet series is genuinely holomorphic in the arithmetic quotient L2 norm. -/
theorem adelicHolomorphicL2Curve_differentiableOn (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    DifferentiableOn ℂ (adelicHolomorphicL2Curve N f) (Metric.ball 0 (1 / 2 : ℝ)) := by
  obtain ⟨K, _, hK⟩ := adelicUnipotentTaylorCoefficient_norm_bound N f
  exact vectorPowerSeries_differentiableOn (adelicUnipotentTaylorCoefficient N f) hK

/-- The original pointwise Taylor terms have a common geometric bound over every original projective coordinate. -/
theorem adelicUnipotentTaylorTerm_bound (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z : ℂ, ∀ p : AdelicProjectiveGroup,
      ‖(n.factorial : ℂ)⁻¹ • z ^ n • adelicUnipotentPointwiseJet N f n 0 p‖ ≤
        C * (2 * ‖z‖) ^ n := by
  obtain ⟨C, hC0, hC⟩ := adelicUnipotentPointwiseJet_bound N f
  refine ⟨C, hC0, fun n z p => ?_⟩
  rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * (‖z‖ ^ n * ((n.factorial : ℝ) * C / (1 / 2 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hC n 0 p) (by positivity)) (by positivity)
    _ = C * (2 * ‖z‖) ^ n := by
      have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have he : (1 / 2 : ℝ) ^ n = (2 ^ n : ℝ)⁻¹ := by rw [one_div_pow, one_div]
      rw [he, div_inv_eq_mul, mul_pow]
      field_simp

/-- The holomorphic L2 series equals precisely the genuine L2 realization of the original complex slash slice. -/
theorem adelicHolomorphicL2Curve_eq_toLp (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    adelicHolomorphicL2Curve N f z =
      (adelicProjectiveHolomorphicSlice_memLp N f hz).toLp (adelicProjectiveHolomorphicSlice N f z) := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  let q : ℕ → AdelicProjectiveGroup → ℂ := fun n p =>
    (n.factorial : ℂ)⁻¹ • z ^ n • adelicUnipotentPointwiseJet N f n 0 p
  have hq (n : ℕ) : MemLp (q n) 2 μ :=
    ((adelicUnipotentPointwiseJet_memLp N f n 0).const_smul (z ^ n)).const_smul
      ((n.factorial : ℂ)⁻¹)
  obtain ⟨C, hC0, hC⟩ := adelicUnipotentTaylorTerm_bound N f
  have hg : ‖2 * ‖z‖‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hu : Summable (fun n : ℕ => C * (2 * ‖z‖) ^ n) :=
    (summable_geometric_of_norm_lt_one hg).mul_left C
  have ht := toLp_partialSums_tendsto q (adelicProjectiveHolomorphicSlice N f z) hq
    (adelicProjectiveHolomorphicSlice_memLp N f hz) (fun n => C * (2 * ‖z‖) ^ n)
    (fun n => by positivity) hu (fun n p => hC n z p)
    (fun p => (adelicProjectiveHolomorphicSlice_hasSum N f hz p).tendsto_sum_nat)
  have he (n : ℕ) : (hq n).toLp (q n) = z ^ n • adelicUnipotentTaylorCoefficient N f n := by
    change (((adelicUnipotentPointwiseJet_memLp N f n 0).const_smul (z ^ n)).const_smul
      ((n.factorial : ℂ)⁻¹)).toLp
      (((n.factorial : ℂ)⁻¹) • ((z ^ n) • adelicUnipotentPointwiseJet N f n 0)) =
      z ^ n • ((n.factorial : ℂ)⁻¹ • adelicUnipotentL2Jet N f n 0)
    rw [MemLp.toLp_const_smul _ ((adelicUnipotentPointwiseJet_memLp N f n 0).const_smul (z ^ n)),
      MemLp.toLp_const_smul _ (adelicUnipotentPointwiseJet_memLp N f n 0)]
    exact smul_comm ((n.factorial : ℂ)⁻¹) (z ^ n) (adelicUnipotentL2Jet N f n 0)
  simp only [he] at ht
  obtain ⟨K, _, hK⟩ := adelicUnipotentTaylorCoefficient_norm_bound N f
  have hs := vectorPowerSeries_summable (adelicUnipotentTaylorCoefficient N f) hK hz
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht

/-- The actual holomorphic L2 curve has the literal original complex slice as its almost-everywhere representative. -/
theorem adelicHolomorphicL2Curve_ae_slice (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    ⇑(adelicHolomorphicL2Curve N f z) =ᵐ[
      adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      adelicProjectiveHolomorphicSlice N f z := by
  rw [adelicHolomorphicL2Curve_eq_toLp N f hz]
  exact (adelicProjectiveHolomorphicSlice_memLp N f hz).coeFn_toLp

end
end Dubon2026
