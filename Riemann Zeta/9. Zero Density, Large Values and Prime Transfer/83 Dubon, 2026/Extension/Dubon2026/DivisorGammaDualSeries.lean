import Dubon2026.GeneralRankinReflection
import Dubon2026.GammaDualFiniteTransform

/-! # Actual convergent Gamma dual series for every level divisor -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The real part recovers the entire actual divisor coefficient because its imaginary part is proved zero. -/
theorem divisorRectangularDualCoefficients_ofReal_re {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (n : ℕ) :
    ((divisorRectangularDualCoefficients f d n).re : ℂ) = divisorRectangularDualCoefficients f d n := by
  apply Complex.ext
  · rfl
  · exact (divisorRectangularDualCoefficients_positive f d).2.2 n |>.symm

/-- Taking actual real coefficients preserves this genuine Dirichlet series exactly. -/
theorem divisorRectangularDual_LSeries_re {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (s : ℂ) :
    LSeries (fun n => ((divisorRectangularDualCoefficients f d n).re : ℂ)) s =
      LSeries (divisorRectangularDualCoefficients f d) s := by
  simp only [divisorRectangularDualCoefficients_ofReal_re]

/-- Every actual component has the complete nonnegative linear mean including its zero index. -/
theorem exists_divisorRectangularDual_sum_zero_upper {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (d : Q.divisors) :
    ∃ B : ℝ, 0 < B ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 0 X, (divisorRectangularDualCoefficients f d n).re) ≤ B * X := by
  obtain ⟨B, hB, hb⟩ := exists_divisorRectangularDual_sum_upper f hk d
  refine ⟨B, hB, fun X => ?_⟩
  rw [sum_Icc_zero_eq_positive (by rw [(divisorRectangularDualCoefficients_positive f d).1, zero_re])]
  exact hb X

/-- The actual divisor component with the original cusp weight and its precise positive conductor. -/
def divisorGammaDualSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (x : ℝ) : ℂ :=
  gammaRieszDualSeries (fun n => (divisorRectangularDualCoefficients f d n).re)
    k (divisorRankinConductor Q d.val) x

/-- The component is the literal complex-coefficient series with its reciprocal positive index and degree-four Gamma kernel. -/
theorem divisorGammaDualSeries_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (x : ℝ) :
    divisorGammaDualSeries f d x = ∑' n : ℕ,
      (divisorRectangularDualCoefficients f d n / (n : ℂ)) *
        ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (divisorRankinConductor Q d.val * n * x)) := by
  unfold divisorGammaDualSeries gammaRieszDualSeries
  apply tsum_congr
  intro n
  simp only [gammaRieszDualTerm, Complex.ofReal_div, Complex.ofReal_natCast,
    divisorRectangularDualCoefficients_ofReal_re]

/-- The original cusp form supplies absolute convergence of every actual divisor Gamma series. -/
theorem summable_norm_divisorGammaDualTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (d : Q.divisors)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖(divisorRectangularDualCoefficients f d n / (n : ℂ)) *
      ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (divisorRankinConductor Q d.val * n * x))‖) := by
  obtain ⟨B, hB, hb⟩ := exists_divisorRectangularDual_sum_zero_upper f (by omega) d
  have hs := summable_norm_gammaRieszDualTerm (by exact_mod_cast hk : (2 : ℝ) ≤ k)
    (divisorRankinConductor_pos d) (divisorRectangularDualCoefficients_positive f d).2.1 hB.le hb hx
  simpa only [gammaRieszDualTerm, Complex.ofReal_div, Complex.ofReal_natCast,
    divisorRectangularDualCoefficients_ofReal_re] using hs

/-- The actual finite-cutoff component series converges to the genuine divisor Gamma series, using the proved uniform summable majorant. -/
theorem tendsto_divisorGammaDualCutoffSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (d : Q.divisors)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => ∑' n : ℕ,
      gammaRieszDualCutoffTerm (fun n => (divisorRectangularDualCoefficients f d n).re)
        k (divisorRankinConductor Q d.val) x T n) atTop (𝓝 (divisorGammaDualSeries f d x)) := by
  obtain ⟨B, hB, hb⟩ := exists_divisorRectangularDual_sum_zero_upper f (by omega) d
  exact tendsto_gammaRieszDualCutoffSeries (by exact_mod_cast hk : (2 : ℝ) ≤ k)
    (divisorRankinConductor_pos d) (divisorRectangularDualCoefficients_positive f d).2.1 hB.le hb hx

end
end Dubon2026
