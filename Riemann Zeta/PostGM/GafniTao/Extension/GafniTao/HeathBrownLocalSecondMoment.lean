import GafniTao.HeathBrownOneSidedDivisorAFE
import GafniTao.HeathBrownTwelfthStatement

/-!
# The actual local critical-line second moment

This file fixes the real-valued source object used in Heath--Brown's Lemma 3
and Ivić's Theorem 6.2.  It also connects the ordinary-zeta limit of the
one-sided AFE to the square of the critical-line norm.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The local second moment centered at `center`, with half-width `G`. -/
noncomputable def heathBrownLocalSecondMoment (center G : ℝ) : ℝ :=
  ∫ t in center - G..center + G,
    heathBrownCriticalZetaNorm t ^ (2 : ℕ)

theorem continuous_heathBrownCriticalZetaNorm :
    Continuous heathBrownCriticalZetaNorm := by
  unfold heathBrownCriticalZetaNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  apply ContinuousAt.comp (g := riemannZeta)
      (f := fun u : ℝ => (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
  · exact (differentiableAt_riemannZeta hne).continuousAt
  · fun_prop

theorem continuous_heathBrownCriticalZetaNorm_sq :
    Continuous (fun t : ℝ => heathBrownCriticalZetaNorm t ^ (2 : ℕ)) :=
  continuous_heathBrownCriticalZetaNorm.pow 2

theorem intervalIntegrable_heathBrownCriticalZetaNorm_sq (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => heathBrownCriticalZetaNorm t ^ (2 : ℕ)) volume a b :=
  continuous_heathBrownCriticalZetaNorm_sq.intervalIntegrable a b

theorem heathBrownLocalSecondMoment_nonneg
    {center G : ℝ} (hG : 0 ≤ G) :
    0 ≤ heathBrownLocalSecondMoment center G := by
  unfold heathBrownLocalSecondMoment
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _

/-- The norm of the one-sided AFE residue is exactly the source integrand. -/
theorem norm_riemannZetaSquare_eq_heathBrownCriticalZetaNorm_sq (t : ℝ) :
    ‖riemannZeta (afeCriticalPoint t) ^ 2‖ =
      heathBrownCriticalZetaNorm t ^ (2 : ℕ) := by
  have hp : afeCriticalPoint t =
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    simp [afeCriticalPoint]
  rw [hp]
  simp [heathBrownCriticalZetaNorm, norm_pow]

/-- Norm form of the exact divisor AFE.  The limit is the actual local
second-moment integrand, not a separately supplied majorant. -/
theorem heathBrownOneSidedAFE_norm_limit_native
    (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      ‖(VIntegral' (heathBrownOneSidedContourIntegrand t) c (-H) H +
        VIntegral' (heathBrownOneSidedContourIntegrand (-t)) c (-H) H) /
          heathBrownOneSidedGammaNormalization t‖)
      atTop (𝓝 (heathBrownCriticalZetaNorm t ^ (2 : ℕ))) := by
  have h :=
    (heathBrownOneSidedAFE_zeta_vertical_limit_native t hc).norm
  rw [← norm_riemannZetaSquare_eq_heathBrownCriticalZetaNorm_sq t]
  simpa only [norm_div] using h


end

end GafniTao
