import TaoTrudgianYang2025.AtkinsonFiniteStationaryMain

/-!
# Both signed finite stationary main terms in source-phase normalization

The actual cutoff and Mellin profile are retained independently at the two
saddles. Only the quadratic Gaussian is identified between the signs.
No conjugacy of the remaining amplitude or cancellation of a saddle is assumed.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def atkinsonSaddleProfile (T G L α b : ℝ) : ℂ :=
  ((T ^ (-α) : ℝ) : ℂ) *
    atkinsonPowerProfile α (zetaAtkinsonSaddle T b / T) *
      (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ) *
        zetaSquareReflectedGammaPhase T

theorem atkinsonRootKernel_at_saddle {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
      Complex.exp ((zetaAtkinsonPhase T b (zetaAtkinsonSaddle T b) : ℂ) * I) := by
  rw [zetaAtkinsonSaddle, zetaAtkinsonPhase_sq T b (atkinsonSaddleRoot_pos (by positivity) b)]
  unfold atkinsonRootKernel
  congr 1
  push_cast
  ring

theorem atkinsonPowerWeight_at_saddle {T : ℝ} (hT : 0 < T) (G L α : ℝ) (n : ℕ) :
    atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (Real.sqrt n)) =
      atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n := by
  unfold atkinsonPowerWeight atkinsonSaddleProfile
  rw [zetaGaussianQuadraticIntegral_at_saddle hT G n]

theorem atkinsonPowerWeight_at_neg_saddle {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α : ℝ) (n : ℕ) :
    atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (-Real.sqrt n)) =
      atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n := by
  unfold atkinsonPowerWeight atkinsonSaddleProfile
  rw [zetaGaussianQuadraticIntegral_at_neg_saddle hT hG n]

theorem atkinsonFiniteStationaryMain_sqrt {T : ℝ} (hT : 0 < T)
    (G L α H : ℝ) (n : ℕ) :
    atkinsonFiniteStationaryMain T G L α (Real.sqrt n) H =
      2 * atkinsonSaddleProfile T G L α (Real.sqrt n) * atkinsonSaddleGaussian T G n *
        Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
          Complex.exp (((atkinsonSourcePhase T n + Real.pi / 4 : ℝ) : ℂ) * I) *
            atkinsonQuadraticWindow (atkinsonSaddleCurvature T (Real.sqrt n)) H := by
  unfold atkinsonFiniteStationaryMain
  rw [atkinsonRootKernel_at_saddle hT, exp_zetaAtkinsonPhase_saddle_sqrt hT n]
  change 2 * atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (Real.sqrt n)) * _ * _ = _
  rw [atkinsonPowerWeight_at_saddle hT G L α n]
  ring

theorem atkinsonFiniteStationaryMain_neg_sqrt {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α H : ℝ) (n : ℕ) :
    atkinsonFiniteStationaryMain T G L α (-Real.sqrt n) H =
      2 * atkinsonSaddleProfile T G L α (-Real.sqrt n) * atkinsonSaddleGaussian T G n *
        Complex.exp ((atkinsonCentralPhase T : ℂ) * I) * (-1 : ℂ) ^ n *
          Complex.exp (((-atkinsonSourcePhase T n - Real.pi / 4 : ℝ) : ℂ) * I) *
            atkinsonQuadraticWindow (atkinsonSaddleCurvature T (-Real.sqrt n)) H := by
  unfold atkinsonFiniteStationaryMain
  rw [atkinsonRootKernel_at_saddle hT, exp_zetaAtkinsonPhase_saddle_neg_sqrt hT n]
  change 2 * atkinsonPowerWeight T G L α (zetaAtkinsonSaddle T (-Real.sqrt n)) * _ * _ = _
  rw [atkinsonPowerWeight_at_neg_saddle hT hG L α n]
  ring

end TaoTrudgianYang2025

