import TaoTrudgianYang2025.AtkinsonEvaluatedPhases

/-!
# Exact common fourth-root amplitude of the two actual saddles

The power of the saddle and its curvature cancel together. The cutoff and
Mellin weight remain separate at the two saddles; neither is replaced by one.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def atkinsonCommonSaddleFactor (T b : ℝ) : ℝ :=
  1 / (Real.sqrt 2 * Real.sqrt (Real.sqrt (b^2 + 4*(T/(2*Real.pi)))))

def atkinsonSaddleResidual (T G L b : ℝ) : ℂ :=
  zetaMainMellinProfile (zetaAtkinsonSaddle T b / T) *
    (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)

theorem atkinsonCommonSaddleFactor_neg (T b : ℝ) :
    atkinsonCommonSaddleFactor T (-b) = atkinsonCommonSaddleFactor T b := by
  simp only [atkinsonCommonSaddleFactor, neg_sq]

theorem atkinsonCommonSaddleFactor_pos {T : ℝ} (hT : 0 < T) (b : ℝ) :
    0 < atkinsonCommonSaddleFactor T b := by
  unfold atkinsonCommonSaddleFactor
  positivity

theorem atkinsonCommonSaddleFactor_eq_rpow {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonCommonSaddleFactor T b =
      (1/Real.sqrt 2) * (b^2+4*(T/(2*Real.pi)))^(-(1/4 : ℝ)) := by
  have hD : 0 ≤ b^2+4*(T/(2*Real.pi)) := by positivity
  have hs : Real.sqrt (Real.sqrt (b^2+4*(T/(2*Real.pi)))) =
      (b^2+4*(T/(2*Real.pi)))^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hD]
    norm_num
  rw [atkinsonCommonSaddleFactor,hs,Real.rpow_neg hD]
  ring

theorem atkinsonSaddle_quarter_power_curvature {T : ℝ} (hT : 0 < T) (b : ℝ) :
    T^(-(1/4 : ℝ)) * (zetaAtkinsonSaddle T b/T)^(-(1/4 : ℝ)) /
      Real.sqrt (2*atkinsonSaddleCurvature T b) = atkinsonCommonSaddleFactor T b := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hc : 0 < atkinsonSaddleCurvature T b := by
    linarith [one_lt_atkinsonSaddleCurvature hT b]
  have hp : T^(-(1/4 : ℝ)) * (zetaAtkinsonSaddle T b/T)^(-(1/4 : ℝ)) =
      (Real.sqrt r)⁻¹ := by
    rw [← Real.mul_rpow hT.le (by unfold zetaAtkinsonSaddle; positivity),
      mul_div_cancel₀ _ hT.ne']
    change (r^2)^(-(1/4 : ℝ)) = _
    rw [← Real.rpow_natCast,← Real.rpow_mul hr.le]
    norm_num only [show (2:ℝ)*(-(1/4:ℝ)) = -(1/2) by norm_num]
    rw [Real.rpow_neg hr.le,← Real.sqrt_eq_rpow]
  have hs := atkinsonSaddle_squareRoot_normalization hT b
  change Real.sqrt (atkinsonSaddleCurvature T b) * Real.sqrt r = _ at hs
  rw [hp,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  change _ = 1/(Real.sqrt 2 * Real.sqrt (Real.sqrt (b^2+4*(T/(2*Real.pi)))))
  calc
    _ = 1/(Real.sqrt 2*(Real.sqrt (atkinsonSaddleCurvature T b)*Real.sqrt r)) := by ring
    _ = _ := by rw [hs]

theorem atkinsonSaddleProfile_div_curvature {T : ℝ} (hT : 0 < T) (G L b : ℝ) :
    atkinsonSaddleProfile T G L (1/4) b /
      (Real.sqrt (2*atkinsonSaddleCurvature T b) : ℂ) =
        (atkinsonCommonSaddleFactor T b : ℂ) *
          atkinsonSaddleResidual T G L b * zetaSquareReflectedGammaPhase T := by
  have he : ((T^(-(1/4:ℝ)) : ℝ) : ℂ) *
      (((zetaAtkinsonSaddle T b/T)^(-(1/4:ℝ)) : ℝ) : ℂ) /
        (Real.sqrt (2*atkinsonSaddleCurvature T b) : ℂ) =
          (atkinsonCommonSaddleFactor T b : ℂ) := by
    exact_mod_cast atkinsonSaddle_quarter_power_curvature hT b
  unfold atkinsonSaddleProfile atkinsonPowerProfile atkinsonSaddleResidual
  calc
    _ = (((T^(-(1/4:ℝ)) : ℝ) : ℂ) *
      (((zetaAtkinsonSaddle T b/T)^(-(1/4:ℝ)) : ℝ) : ℂ) /
        (Real.sqrt (2*atkinsonSaddleCurvature T b) : ℂ)) *
      (zetaMainMellinProfile (zetaAtkinsonSaddle T b/T) *
        (zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)) *
          zetaSquareReflectedGammaPhase T := by ring
    _ = _ := by rw [he]

theorem atkinsonStationaryMain_sqrt_normalized {T : ℝ} (hT : 0 < T)
    (G L : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L (1/4) (Real.sqrt n) =
      2*(atkinsonCommonSaddleFactor T (Real.sqrt n) : ℂ) *
        atkinsonSaddleResidual T G L (Real.sqrt n) * zetaSquareReflectedGammaPhase T *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((atkinsonSourcePhase T n : ℂ)*I) := by
  rw [atkinsonStationaryMain_sqrt hT]
  calc
    _ = 2*(atkinsonSaddleProfile T G L (1/4) (Real.sqrt n) /
      (Real.sqrt (2*atkinsonSaddleCurvature T (Real.sqrt n)) : ℂ)) *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((atkinsonSourcePhase T n : ℂ)*I) := by ring
    _ = _ := by rw [atkinsonSaddleProfile_div_curvature hT]; ring

theorem atkinsonStationaryMain_neg_sqrt_normalized {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (n : ℕ) :
    atkinsonStationaryMain T G L (1/4) (-Real.sqrt n) =
      (-I)*2*(atkinsonCommonSaddleFactor T (Real.sqrt n) : ℂ) *
        atkinsonSaddleResidual T G L (-Real.sqrt n) * zetaSquareReflectedGammaPhase T *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I) := by
  rw [atkinsonStationaryMain_neg_sqrt hT hG]
  calc
    _ = (-I)*2*(atkinsonSaddleProfile T G L (1/4) (-Real.sqrt n) /
      (Real.sqrt (2*atkinsonSaddleCurvature T (-Real.sqrt n)) : ℂ)) *
        atkinsonSaddleGaussian T G n * Complex.exp ((atkinsonCentralPhase T : ℂ)*I) *
        (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I) := by ring
    _ = _ := by
      rw [atkinsonSaddleProfile_div_curvature hT,atkinsonCommonSaddleFactor_neg]
      ring

end TaoTrudgianYang2025

