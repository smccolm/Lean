import Dubon2026.GammaRieszRecurrence

/-! # Joint continuity of the actual weighted Riesz Gamma integrands -/

namespace Dubon2026

open Complex Set

noncomputable section

/-- The actual Gamma symbol is continuous along the common vertical line for all nonnegative orders. -/
theorem continuous_gammaRieszSymbol_common_line {k r : ℝ} (hk : 2 ≤ k) (hr : 0 ≤ r) :
    Continuous (fun t : ℝ => gammaRieszSymbol k r (gammaVerticalPoint (3 / 8) t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hh := (differentiableAt_gammaRieszMellinFunction hk hr (by norm_num : (0 : ℝ) < 1)
    (s := gammaVerticalPoint (3 / 8) t) (by norm_num [gammaVerticalPoint_re])
    (by norm_num [gammaVerticalPoint_re])).continuousAt.comp
    (show ContinuousAt (gammaVerticalPoint (3 / 8)) t by unfold gammaVerticalPoint; fun_prop)
  simpa only [Function.comp_def, gammaRieszMellinFunction, Complex.ofReal_one, Complex.one_cpow, one_mul] using hh

/-- The genuine weighted integrand is jointly continuous in the positive parameter and height. -/
theorem continuousAt_gammaRieszWeightedIntegrand_joint {k r c x : ℝ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hc : 0 < c) (hx : 0 < x) (t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => gammaRieszWeightedIntegrand k r c (3 / 8) p.2 p.1) (x, t) := by
  have hwR : ContinuousAt (fun p : ℝ × ℝ => p.1 ^ r) (x, t) := by
    exact continuousAt_fst.rpow_const (Or.inl hx.ne')
  have hw : ContinuousAt (fun p : ℝ × ℝ => ((p.1 ^ r : ℝ) : ℂ)) (x, t) :=
    Complex.continuous_ofReal.continuousAt.comp hwR
  have hp : ContinuousAt (fun p : ℝ × ℝ => ((c * p.1 : ℝ) : ℂ) ^
      gammaVerticalPoint (3 / 8) p.2) (x, t) := by
    apply ContinuousAt.cpow
    · fun_prop
    · unfold gammaVerticalPoint
      fun_prop
    · exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hc hx)
  exact hw.mul (hp.mul ((continuous_gammaRieszSymbol_common_line hk hr).continuousAt.comp continuousAt_snd))

/-- At every positive parameter the genuine weighted integrand is continuous in height. -/
theorem continuous_gammaRieszWeightedIntegrand_height {k r c x : ℝ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hc : 0 < c) (hx : 0 < x) :
    Continuous (fun t => gammaRieszWeightedIntegrand k r c (3 / 8) t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (continuousAt_gammaRieszWeightedIntegrand_joint hk hr hc hx t).comp
    (continuousAt_const.prodMk continuousAt_id)

end
end Dubon2026
