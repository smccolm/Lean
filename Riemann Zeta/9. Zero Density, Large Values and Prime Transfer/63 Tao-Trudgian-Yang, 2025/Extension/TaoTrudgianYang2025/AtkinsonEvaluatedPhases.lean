import TaoTrudgianYang2025.AtkinsonStationaryEvaluation

/-!
# Evaluated carrier phases with both Bessel signs

The Fresnel phase cancels the positive quarter-turn and contributes
minus I to the negative carrier. Both actual saddle amplitudes remain.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

theorem exp_positive_saddle_mul_fresnel (f : ℝ) :
    Complex.exp (((f + Real.pi / 4 : ℝ) : ℂ) * I) *
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) = Complex.exp ((f : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_negative_saddle_mul_fresnel (f : ℝ) :
    Complex.exp (((-f - Real.pi / 4 : ℝ) : ℂ) * I) *
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) = (-I) * Complex.exp ((-f : ℂ) * I) := by
  have hquarter : Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * I) = -I := by
    simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      Complex.exp_neg_pi_div_two_mul_I
  rw [← hquarter, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem atkinsonStationaryMain_sqrt {T : ℝ} (hT : 0 < T)
    (G L α : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L α (Real.sqrt n) =
      (2 * atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n *
        Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
          Complex.exp ((atkinsonSourcePhase T n : ℂ) * I)) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (Real.sqrt n)) : ℂ) := by
  rw [atkinsonStationaryMain_eq_phase hT, atkinsonRootKernel_at_saddle hT,
    exp_zetaAtkinsonPhase_saddle_sqrt hT n]
  change 2 * atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (Real.sqrt n)) * _ * _ = _
  rw [atkinsonPowerWeight_at_saddle hT G L α n]
  calc
    _ = (2 * atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n *
      Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
        (Complex.exp (((atkinsonSourcePhase T n + Real.pi / 4 : ℝ) : ℂ) * I) *
          Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I))) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (Real.sqrt n)) : ℂ) := by ring
    _ = _ := by rw [exp_positive_saddle_mul_fresnel]

theorem atkinsonStationaryMain_neg_sqrt {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L α (-Real.sqrt n) =
      ((-I) * 2 * atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n *
        Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
          Complex.exp ((-atkinsonSourcePhase T n : ℂ) * I)) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (-Real.sqrt n)) : ℂ) := by
  rw [atkinsonStationaryMain_eq_phase hT, atkinsonRootKernel_at_saddle hT,
    exp_zetaAtkinsonPhase_saddle_neg_sqrt hT n]
  change 2 * atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (-Real.sqrt n)) * _ * _ = _
  rw [atkinsonPowerWeight_at_neg_saddle hT hG L α n]
  calc
    _ = (2 * atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n *
      Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
        (Complex.exp (((-atkinsonSourcePhase T n - Real.pi / 4 : ℝ) : ℂ) * I) *
          Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I))) /
            (Real.sqrt (2 * atkinsonSaddleCurvature T (-Real.sqrt n)) : ℂ) := by ring
    _ = _ := by rw [exp_negative_saddle_mul_fresnel]; ring

end TaoTrudgianYang2025

