import Dubon2026.RankinConvolutionRegular
import GafniTao.WienerSource

/-! # The leading mean asymptotic of the genuine nonnegative Rankin convolution -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The actual convolution coefficient equals its real embedding. -/
theorem rankinConvolutionCoefficients_ofReal_re {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    ((rankinConvolutionCoefficients f n).re : ℂ) = rankinConvolutionCoefficients f n :=
  Complex.ext (by simp) (by simp [rankinConvolutionCoefficients_im])

/-- The actual nonnegative convolution coefficient has norm equal to its real part. -/
theorem rankinConvolutionCoefficients_norm {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    ‖rankinConvolutionCoefficients f n‖ = (rankinConvolutionCoefficients f n).re := by
  conv_lhs => rw [← rankinConvolutionCoefficients_ofReal_re f n]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rankinConvolutionCoefficients_re_nonneg f n)]

/-- The imported range convention agrees with the true positive-index convolution sum. -/
theorem rankin_convolution_cumsum_succ {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (N : ℕ) :
    cumsum (fun n => (rankinConvolutionCoefficients f n).re) (N + 1) =
      ∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re := by
  have he : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [cumsum, he, Finset.sum_insert (by simp)]
  simp [rankinConvolutionCoefficients_zero]

/-- The genuine convolution satisfies the linear partial-sum premise of the cleaned Wiener theorem. -/
theorem rankin_convolution_cheby {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    cheby (rankinConvolutionCoefficients f) := by
  obtain ⟨B, hB, hb⟩ := exists_rankinConvolution_sum_upper f hk
  refine ⟨B, fun N => ?_⟩
  simp only [rankinConvolutionCoefficients_norm]
  cases N with
  | zero => simp
  | succ N =>
    rw [rankin_convolution_cumsum_succ]
    exact (hb N).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Nat.le_succ N) hB.le)

/-- The literal convolution cumsum has the leading mean fixed by its proved analytic residue. -/
theorem tendsto_rankin_convolution_cumsum_div {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun N : ℕ => cumsum (fun n => (rankinConvolutionCoefficients f n).re) N / N)
      atTop (𝓝 (rankinConvolutionResidue f)) := by
  apply WienerIkeharaTheorem' (G := rankinConvolutionRegular f)
  · exact rankinConvolutionCoefficients_re_nonneg f
  · intro σ hσ
    simpa only [← nterm_eq_norm_term, rankinConvolutionCoefficients_ofReal_re] using
      (rankinConvolution_lseriesSummable f hk.le (s := (σ : ℂ)) hσ).norm
  · simpa only [rankinConvolutionCoefficients_ofReal_re] using rankin_convolution_cheby f hk
  · exact continuousOn_rankinConvolutionRegular f hk
  · intro s hs
    simpa only [rankinConvolutionCoefficients_ofReal_re] using
      rankinConvolutionRegular_eq_series_sub_pole f hk hs

/-- The actual positive-index Rankin convolution mean tends to its genuine positive-residue constant. -/
theorem tendsto_rankin_convolution_mean {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re) / N)
      atTop (𝓝 (rankinConvolutionResidue f)) := by
  have hm := (tendsto_rankin_convolution_cumsum_div f hk).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_div, inv_one] using
      (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ)).inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have hp := hm.mul hr
  simp only [mul_one] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  rw [rankin_convolution_cumsum_succ, Nat.cast_add, Nat.cast_one]
  field_simp [hN0, hN1]

end
end Dubon2026
