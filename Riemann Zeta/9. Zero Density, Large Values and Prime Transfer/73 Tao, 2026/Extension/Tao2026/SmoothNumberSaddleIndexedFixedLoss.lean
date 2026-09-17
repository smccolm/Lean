import Tao2026.SmoothNumberSaddleIndexedFixedDepth

/-!
# Critical-regime loss on every fixed indexed shell

The fixed-depth scale package also supplies the cofactor range needed by the
CEP alphabet.  Consequently the uniform indexed phase theorem specializes
eventually to every fixed shell in a Tao-critical regime.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

/-- At every fixed indexed depth, the iterated-root prime scale eventually
dominates the square of the critical Rankin ratio. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_le_sqrt_iteratedPrimeScale
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (k : ℕ) :
    ∀ᶠ n in atTop, smoothRankinRatio (X n) (y n) ≤
      Real.sqrt (smoothSaddleIteratedPrimeScale k (y n)) := by
  let δ : ℝ := (1 / 5 : ℝ) * (1 / 2 : ℝ) ^ k
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hrankin := hregime.eventually_rankinRatio_le_y_rpow hα hδ
  filter_upwards [hrankin,
    hregime.eventually_indexedIteratedRoot_scale_bounds hα k,
    hregime.eventually_two_le_y hα] with n hu hscale hy
  let N := smoothSaddleIteratedPrimeScale k (y n)
  have hyPos : (0 : ℝ) < y n := by positivity
  have hNPos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by dsimp only [N]; omega)
  have hlogyNonneg : 0 ≤ Real.log (y n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y n by omega))
  have hlogN : (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k *
      Real.log (y n : ℝ) ≤ Real.log (N : ℝ) := by
    simpa only [N] using hscale.2.1
  have hpow : (y n : ℝ) ^ δ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hyPos, Real.rpow_def_of_pos hNPos]
    apply Real.exp_le_exp.mpr
    dsimp only [δ]
    nlinarith
  calc
    smoothRankinRatio (X n) (y n) ≤ (y n : ℝ) ^ δ := hu
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hpow
    _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow]

/-- Every fixed indexed shell eventually carries the full CEP cosine-loss
bound throughout its exact physical frequency band. -/
theorem IsTaoCriticalSmoothRegime.eventually_indexedOuterMultiShell_cosineLoss_lower
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      smoothSaddleIndexedOuterUpperHeight (k - 1) (y n) ≤ t →
      t ≤ smoothSaddleIndexedOuterUpperHeight k (y n) →
      (cepDyadicCofactorCutoff
          (smoothSaddleIteratedPrimeScale k (y n))
          (smoothRankinRatio (X n) (y n)) : ℝ) ^
            (1 - smoothSaddlePoint (X n) (y n)) /
          (16 * Real.log 2 *
            Real.log (smoothRankinRatio (X n) (y n))) ≤
        smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t := by
  obtain ⟨B, hB, hpnt⟩ := exists_chebyshevTheta_quarter_threshold
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hloguTop := Real.tendsto_log_atTop.comp huTop
  filter_upwards [hregime.eventually_indexedIteratedRoot_scale_bounds hα k,
    hregime.eventually_two_le_y hα,
    hloguTop.eventually (eventually_ge_atTop (12 : ℝ)),
    huTop.eventually (eventually_ge_atTop (B : ℝ)),
    hregime.eventually_rankinRatio_le_sqrt_iteratedPrimeScale hα k,
    hregime.eventually_smoothSaddlePoint_lt_one hα] with
      n hscale hy hlogU hBu huN hsigmaOne
  intro t htLower htUpper
  exact indexedOuterMultiShell_cosineLoss_lower
    hk hB (by omega) hy (smoothSaddleIteratedPrimeScale_le k (y n))
    hlogU hBu huN hscale.2.1 hscale.2.2 hpnt hsigmaOne.le
    htLower htUpper

end

end Tao2026
