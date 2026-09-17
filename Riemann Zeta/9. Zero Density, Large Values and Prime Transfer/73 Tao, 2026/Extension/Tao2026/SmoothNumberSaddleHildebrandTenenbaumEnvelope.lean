import Tao2026.SmoothNumberSaddleIndexedHeightCeiling

/-!
# The Hildebrand--Tenenbaum minor-arc envelope

Lemma 8(ii) of Hildebrand--Tenenbaum's saddle-point proof controls the finite
Euler product by an exponential whose loss is proportional to

`u * t^2 / ((1 - sigma)^2 + t^2)`.

This module names that exact loss, proves its radial monotonicity, formulates
the corresponding source-facing characteristic-function contract, transfers
it to the normalized physical Perron integrand, and integrates any finite
symmetric minor-arc shell.  The analytic proof of the contract and the
finite-height Perron truncation estimate remain separate obligations.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

/-- The dimensionless large-frequency loss in Hildebrand--Tenenbaum
Lemma 8(ii). -/
noncomputable def smoothSaddleHildebrandTenenbaumLoss
    (X y : ℕ) (t : ℝ) : ℝ :=
  smoothRankinRatio X y * t ^ 2 /
    ((1 - smoothSaddlePoint X y) ^ 2 + t ^ 2)

theorem smoothSaddleHildebrandTenenbaumLoss_nonneg
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    0 ≤ smoothSaddleHildebrandTenenbaumLoss X y t := by
  unfold smoothSaddleHildebrandTenenbaumLoss
  exact div_nonneg
    (mul_nonneg (smoothRankinRatio_pos hX hy).le (sq_nonneg t))
    (add_nonneg (sq_nonneg _) (sq_nonneg t))

theorem smoothSaddleHildebrandTenenbaumLoss_neg
    (X y : ℕ) (t : ℝ) :
    smoothSaddleHildebrandTenenbaumLoss X y (-t) =
      smoothSaddleHildebrandTenenbaumLoss X y t := by
  unfold smoothSaddleHildebrandTenenbaumLoss
  ring

theorem smoothSaddleHildebrandTenenbaumLoss_abs
    (X y : ℕ) (t : ℝ) :
    smoothSaddleHildebrandTenenbaumLoss X y |t| =
      smoothSaddleHildebrandTenenbaumLoss X y t := by
  unfold smoothSaddleHildebrandTenenbaumLoss
  rw [sq_abs]

/-- The HT loss increases with the absolute physical frequency. -/
theorem smoothSaddleHildebrandTenenbaumLoss_mono
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    smoothSaddleHildebrandTenenbaumLoss X y a ≤
      smoothSaddleHildebrandTenenbaumLoss X y b := by
  let u := smoothRankinRatio X y
  let d := 1 - smoothSaddlePoint X y
  have hu : 0 < u := smoothRankinRatio_pos hX hy
  have hb : 0 < b := ha.trans_le hab
  have hdenA : 0 < d ^ 2 + a ^ 2 := by positivity
  have hdenB : 0 < d ^ 2 + b ^ 2 := by positivity
  have habSq : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hcross : u * a ^ 2 * (d ^ 2 + b ^ 2) ≤
      u * b ^ 2 * (d ^ 2 + a ^ 2) := by
    have hnonneg : 0 ≤ u * d ^ 2 * (b ^ 2 - a ^ 2) := by positivity
    nlinarith
  unfold smoothSaddleHildebrandTenenbaumLoss
  change u * a ^ 2 / (d ^ 2 + a ^ 2) ≤
    u * b ^ 2 / (d ^ 2 + b ^ 2)
  exact (div_le_div_iff₀ hdenA hdenB).2 hcross

/-- The precise finite-range HT minor-arc assertion, expressed using the
centered saddle characteristic at physical frequency `t`. -/
def SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
    (X y : ℕ) (c lower upper : ℝ) : Prop :=
  ∀ t : ℝ, lower ≤ |t| → |t| ≤ upper →
    ‖smoothSaddleNormalizedCharacteristic X y
        (-t * smoothSaddleStandardDeviation X y)‖ ≤
      Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t))

/-- The HT characteristic estimate controls the literal normalized Perron
integrand, since the exact Laplace kernel has norm at most one. -/
theorem norm_smoothSaddlePerronLineIntegrand_le_of_hildebrandTenenbaum
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {c lower upper t : ℝ}
    (hminor : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      X y c lower upper)
    (htLower : lower ≤ |t|) (htUpper : |t| ≤ upper) :
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
      Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t)) := by
  rw [smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy,
    norm_mul]
  calc
    ‖smoothSaddleNormalizedCharacteristic X y
          (-t * smoothSaddleStandardDeviation X y)‖ *
        ‖smoothSaddleLaplaceFourierKernel X y
          (-t * smoothSaddleStandardDeviation X y)‖ ≤
      Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t)) * 1 :=
        mul_le_mul (hminor t htLower htUpper)
          (norm_smoothSaddleLaplaceFourierKernel_le_one X y _)
          (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- A finite symmetric minor-arc shell is bounded by its left-endpoint HT
loss. This is the integration step used after Lemma 8(ii). -/
theorem norm_smoothSaddleSymmetricPerronShellContribution_le_hildebrandTenenbaum
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {c lower upper : ℝ} (hc : 0 ≤ c) (hlower : 0 < lower)
    (hlu : lower ≤ upper)
    (hminor : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      X y c lower upper) :
    ‖smoothSaddleSymmetricPerronShellContribution X y lower upper‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * Real.exp (-(c *
          smoothSaddleHildebrandTenenbaumLoss X y lower)) *
            (upper - lower)) := by
  apply norm_smoothSaddleSymmetricPerronShellContribution_le
    hX hy hlower.le hlu
  intro t htLower htUpper
  have habsPos : 0 < |t| := hlower.trans_le htLower
  have hloss := smoothSaddleHildebrandTenenbaumLoss_mono
    hX hy hlower (show lower ≤ |t| from htLower)
  rw [smoothSaddleHildebrandTenenbaumLoss_abs] at hloss
  calc
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
        Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t)) :=
      norm_smoothSaddlePerronLineIntegrand_le_of_hildebrandTenenbaum
        hX hy hminor htLower htUpper
    _ ≤ Real.exp (-(c *
        smoothSaddleHildebrandTenenbaumLoss X y lower)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Sequence-level closure of the finite HT integration step. The displayed
real envelope is exactly the remaining parameter estimate. -/
theorem IsTaoCriticalSmoothRegime.tendsto_symmetricPerronShellContribution_zero_of_hildebrandTenenbaum
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) {c : ℝ} (hc : 0 ≤ c) {lower upper : ℕ → ℝ}
    (hlower : ∀ᶠ n in atTop, 0 < lower n)
    (hlu : ∀ᶠ n in atTop, lower n ≤ upper n)
    (hminor : ∀ᶠ n in atTop,
      SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
        (X n) (y n) c (lower n) (upper n))
    (henvelope : Tendsto (fun n =>
      (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
        (2 * Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss
          (X n) (y n) (lower n))) * (upper n - lower n)))
      atTop (𝓝 0)) :
    Tendsto (fun n => smoothSaddleSymmetricPerronShellContribution
      (X n) (y n) (lower n) (upper n)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    henvelope
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα, hlower, hlu, hminor] with
      n hX hy hLower hLU hMinor
  exact norm_smoothSaddleSymmetricPerronShellContribution_le_hildebrandTenenbaum
    hX hy hc hLower hLU hMinor

end

end Tao2026
