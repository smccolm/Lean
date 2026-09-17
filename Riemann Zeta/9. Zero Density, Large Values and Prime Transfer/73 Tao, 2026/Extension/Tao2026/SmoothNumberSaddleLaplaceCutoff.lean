import Tao2026.SmoothNumberSaddlePrimeTaylor
import Tao2026.SmoothNumberSaddleLocalLimit

/-!
# Laplace form of the smooth saddle cutoff

The saddle cutoff is rewritten here as a one-sided Laplace moment of the
same centered, variance-normalized logarithmic variable whose characteristic
function was treated in `SmoothNumberSaddlePrimeTaylor`.  This identifies the
precise shrinking-scale local-limit quantity that remains after pointwise
Gaussian characteristic convergence.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- The tilted mass, extended from positive smooth integers to all natural
numbers by zero. -/
noncomputable def smoothTiltedNatMass (y : ℕ) (sigma : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Nat.smoothNumbers (y + 1) then
    (n : ℝ) ^ (-sigma) / smoothDirichletSeries (y + 1) sigma
  else 0

/-- The centered logarithmic displacement in saddle standard-deviation
units. -/
noncomputable def smoothSaddleNormalizedLog
    (X y n : ℕ) : ℝ :=
  (Real.log (n : ℝ) - Real.log (X : ℝ)) /
    smoothSaddleStandardDeviation X y

/-- The Laplace rate induced by the exact saddle parameter. -/
noncomputable def smoothSaddleLaplaceRate (X y : ℕ) : ℝ :=
  smoothSaddlePoint X y * smoothSaddleStandardDeviation X y

/-- The one-sided Laplace moment over the literal smooth-number cutoff. -/
noncomputable def smoothSaddleCutoffLaplaceMoment
    (X y : ℕ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
    smoothTiltedNatMass y (smoothSaddlePoint X y) n *
      Real.exp (smoothSaddleLaplaceRate X y *
        smoothSaddleNormalizedLog X y n)

/-- On its smooth support, the natural-indexed tilted mass is the original
subtype-indexed mass. -/
theorem smoothTiltedNatMass_eq_smoothTiltedMass
    {y n : ℕ} {sigma : ℝ} (hn : n ∈ Nat.smoothNumbers (y + 1)) :
    smoothTiltedNatMass y sigma n =
      smoothTiltedMass y sigma ⟨n, hn⟩ := by
  simp [smoothTiltedNatMass, hn, smoothTiltedMass]

/-- The normalized Laplace exponential is exactly the cutoff tilt
`(n/X)^sigma`. -/
theorem exp_smoothSaddleLaplaceRate_mul_normalizedLog
    {X y n : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (hn : n ≠ 0) :
    Real.exp (smoothSaddleLaplaceRate X y *
        smoothSaddleNormalizedLog X y n) =
      ((n : ℝ) / X) ^ smoothSaddlePoint X y := by
  have hXpos : (0 : ℝ) < X := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  rw [Real.rpow_def_of_pos (div_pos hnpos hXpos)]
  congr 1
  rw [Real.log_div hnpos.ne' hXpos.ne']
  unfold smoothSaddleLaplaceRate smoothSaddleNormalizedLog
  field_simp [hsd.ne']

/-- The original saddle cutoff factor is exactly the one-sided normalized
Laplace moment. -/
theorem smoothSaddleCutoffFactor_eq_laplaceMoment
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleCutoffFactor X y (smoothSaddlePoint X y) =
      smoothSaddleCutoffLaplaceMoment X y := by
  unfold smoothSaddleCutoffFactor smoothSaddleCutoffLaplaceMoment
  symm
  calc
    (∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
        smoothTiltedNatMass y (smoothSaddlePoint X y) n *
          Real.exp (smoothSaddleLaplaceRate X y *
            smoothSaddleNormalizedLog X y n)) =
        ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
          (((n : ℝ) / X) ^ smoothSaddlePoint X y *
            (n : ℝ) ^ (-smoothSaddlePoint X y)) /
              smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hsmooth : n ∈ Nat.smoothNumbers (y + 1) :=
        (Nat.mem_smoothNumbersUpTo.mp hn).2
      have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsmooth
      rw [smoothTiltedNatMass, if_pos hsmooth,
        exp_smoothSaddleLaplaceRate_mul_normalizedLog hX hy hn0]
      ring
    _ = (∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
          ((n : ℝ) / X) ^ smoothSaddlePoint X y *
            (n : ℝ) ^ (-smoothSaddlePoint X y)) /
              smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) := by
      rw [Finset.sum_div]

/-- The Gaussian prefactor is `sqrt(2*pi)` times the exact Laplace rate. -/
theorem smoothSaddleGaussianScale_eq_sqrtTwoPi_mul_laplaceRate
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleGaussianScale X y =
      Real.sqrt (2 * Real.pi) * smoothSaddleLaplaceRate X y := by
  have hphi : 0 ≤ smoothSaddlePhiTwo y (smoothSaddlePoint X y) :=
    (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)).le
  unfold smoothSaddleGaussianScale smoothSaddleLaplaceRate
    smoothSaddleStandardDeviation
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  ring

/-- Exact replacement of the local-limit target by its normalized one-sided
Laplace moment. -/
theorem smoothSaddleCutoffFactor_mul_gaussianScale_eq_laplaceTarget
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleCutoffFactor X y (smoothSaddlePoint X y) *
        smoothSaddleGaussianScale X y =
      Real.sqrt (2 * Real.pi) * smoothSaddleLaplaceRate X y *
        smoothSaddleCutoffLaplaceMoment X y := by
  rw [smoothSaddleCutoffFactor_eq_laplaceMoment hX hy,
    smoothSaddleGaussianScale_eq_sqrtTwoPi_mul_laplaceRate hX hy]
  ring

/-- The Laplace rate diverges in every critical smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleLaplaceRate_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleLaplaceRate (X n) (y n)) atTop atTop := by
  have hsd : Tendsto (fun n => smoothSaddleStandardDeviation (X n) (y n))
      atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp
      (hregime.tendsto_smoothSaddlePhiTwo_saddle_atTop hα)
  have hsigma : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ smoothSaddlePoint (X n) (y n) :=
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  refine tendsto_atTop_mono' atTop ?_
    (hsd.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsigma, hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hs hX hy
  unfold smoothSaddleLaplaceRate
  exact mul_le_mul_of_nonneg_right hs
    (smoothSaddleStandardDeviation_pos hX hy).le

/-- Source-facing saddle asymptotics are equivalent to convergence of the
explicit one-sided Laplace target. -/
theorem criticalSmoothSaddleAsymptotic_iff_laplaceTarget :
    TaoCriticalSmoothSaddleAsymptoticConclusion ↔
      ∀ (α : ℝ) (X y : ℕ → ℕ), 0 < α →
        IsTaoCriticalSmoothRegime X y α →
          Tendsto (fun n =>
            Real.sqrt (2 * Real.pi) *
              smoothSaddleLaplaceRate (X n) (y n) *
                smoothSaddleCutoffLaplaceMoment (X n) (y n))
            atTop (nhds 1) := by
  rw [criticalSmoothSaddleAsymptotic_iff_tiltedLocalLimit]
  constructor
  · intro hlocal α X y hα hregime
    have h := hlocal α X y hα hregime
    apply h.congr'
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact smoothSaddleCutoffFactor_mul_gaussianScale_eq_laplaceTarget hX hy
  · intro hlaplace α X y hα hregime
    have h := hlaplace α X y hα hregime
    apply h.congr'
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact (smoothSaddleCutoffFactor_mul_gaussianScale_eq_laplaceTarget hX hy).symm

end

end Tao2026
