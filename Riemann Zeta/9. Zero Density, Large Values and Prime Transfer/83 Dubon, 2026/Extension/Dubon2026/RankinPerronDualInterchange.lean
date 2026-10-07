import Dubon2026.RankinPerronTermTransform
import Dubon2026.RankinPerronCutoffs
import Dubon2026.LSeriesFiniteContourInterchange

/-! # Justified finite-contour interchange for the genuine reflected Rankin series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Set

noncomputable section

/-- The actual reflected Gamma weight is continuous on the complete left vertical line. -/
theorem continuous_rankinPerron_reflected_weight {k a x : ℝ}
    (hk : 2 ≤ k) (ha : 0 < a) (hx : 0 < x) :
    Continuous (fun t : ℝ => (x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2) *
      (a : ℂ) ^ (2 * gammaVerticalPoint (-1 / 8) t - 1) *
      gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) := by
  have hg : Continuous (fun t : ℝ => gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hh := (differentiableAt_gammaRieszMellinFunction hk (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 1) (s := gammaVerticalPoint (-1 / 8) t)
      (by norm_num [gammaVerticalPoint_re]) (by norm_num [gammaVerticalPoint_re])).continuousAt.comp
      (show ContinuousAt (gammaVerticalPoint (-1 / 8)) t by unfold gammaVerticalPoint; fun_prop)
    simpa only [Function.comp_def, gammaRieszMellinFunction, Complex.ofReal_one,
      Complex.one_cpow, one_mul] using hh
  have hpx : Continuous (fun t : ℝ => (x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2)) :=
    continuous_const.cpow (by unfold gammaVerticalPoint; fun_prop)
      (fun _ => Or.inl hx)
  have hpa : Continuous (fun t : ℝ => (a : ℂ) ^ (2 * gammaVerticalPoint (-1 / 8) t - 1)) :=
    continuous_const.cpow (by unfold gammaVerticalPoint; fun_prop)
      (fun _ => Or.inl ha)
  exact (hpx.mul hpa).mul hg

/-- The true full-level left Perron cutoff is the convergent series of actual Gamma cutoffs, with the exact conductor. -/
theorem rankinPerronVerticalCutoff_eq_dualCutoffs {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    rankinPerronVerticalCutoff f x (-1 / 8) T =
      ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∑' n : ℕ,
        gammaRieszDualCutoffTerm (fun n => (rankinConvolutionCoefficients f n).re)
          k ((4 * Real.pi ^ 2) ^ 2) x T n := by
  let a : ℝ := 4 * Real.pi ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hs := hasSum_intervalIntegral_mul_LSeries
    (rankinConvolution_lseriesSummable f (by omega : 0 ≤ k)
      (s := ((9 / 8 : ℝ) : ℂ)) (by norm_num))
    (z := fun t => 1 - gammaVerticalPoint (-1 / 8) t)
    (u := -T) (v := T) (by unfold gammaVerticalPoint; fun_prop)
    (by intro t _; norm_num [gammaVerticalPoint_re])
    (continuous_rankinPerron_reflected_weight (by exact_mod_cast hk : (2 : ℝ) ≤ k) ha hx).continuousOn
  have hn := hs.const_smul (1 / (2 * Real.pi) : ℝ)
  have hn' : HasSum (fun n : ℕ => (a : ℂ)⁻¹ * gammaRieszDualCutoffTerm
      (fun n => (rankinConvolutionCoefficients f n).re) k (a ^ 2) x T n)
      (rankinPerronVerticalCutoff f x (-1 / 8) T) := by
    convert hn using 1
    · funext n
      exact (rankinPerron_reflected_term_integral f ha hx T n).symm
    · rw [rankinPerronVerticalCutoff]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [a, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow] using
        rankinPerronContinuation_reflected f (by omega : 0 ≤ k) x
          (s := gammaVerticalPoint (-1 / 8) t) (by norm_num [gammaVerticalPoint_re])
          (by norm_num [gammaVerticalPoint_re])
  exact hn'.tsum_eq.symm.trans tsum_mul_left

end
end Dubon2026
