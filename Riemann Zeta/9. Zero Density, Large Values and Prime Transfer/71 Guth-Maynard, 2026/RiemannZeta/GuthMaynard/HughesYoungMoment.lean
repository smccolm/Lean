import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RiemannZeta.GuthMaynard.HughesYoungCutoff
import RiemannZeta.GuthMaynard.TypeIIFourthMomentReduction

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Entry from the sharp Maynard--Pratt moment to Hughes--Young

The analytic theorem is proved for a smooth height weight.  The lemmas below
make the majorization of the project's sharp interval exact.
-/

/-- The actual smooth moment to which the Hughes--Young calculation is
applied. -/
noncomputable def hughesYoungSmoothedMoment (T : ℝ) : ℝ :=
  ∫ t : ℝ, hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t

theorem continuous_twistedZetaMomentIntegrand (T : ℝ) :
    Continuous (twistedZetaMomentIntegrand T) := by
  have h := (continuous_criticalTwistedNorm T).pow 4
  simpa only [criticalTwistedNorm_pow_four] using h

theorem integrable_hughesYoungSmoothedMoment_integrand {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ =>
      hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t) := by
  have hcontinuous : Continuous (fun t : ℝ =>
      hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t) :=
    (contDiff_hughesYoungHeightWeight T).continuous.mul
      (continuous_twistedZetaMomentIntegrand T)
  have hcutoffCompact : HasCompactSupport (hughesYoungCutoff : ℝ → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      hughesYoungCutoff.support
  have hweightCompact : HasCompactSupport (hughesYoungHeightWeight T) := by
    simpa only [hughesYoungHeightWeight] using
      hcutoffCompact.comp_smul (inv_ne_zero hT.ne')
  exact hcontinuous.integrable_of_hasCompactSupport hweightCompact.mul_right

theorem hughesYoungSmoothedMoment_nonneg (T : ℝ) :
    0 ≤ hughesYoungSmoothedMoment T := by
  unfold hughesYoungSmoothedMoment
  exact integral_nonneg fun t =>
    mul_nonneg (hughesYoungHeightWeight_nonneg T t) (by
      unfold twistedZetaMomentIntegrand
      positivity)

/-- The source smooth moment dominates the exact sharp interval used in
`twistedZetaFourthMoment`. -/
theorem twistedZetaFourthMoment_le_hughesYoungSmoothedMoment
    {T : ℝ} (hT : 0 < T) :
    twistedZetaFourthMoment T ≤ hughesYoungSmoothedMoment T := by
  have hOrder : T / 2 ≤ 3 * T := by linarith
  let F : ℝ → ℝ := twistedZetaMomentIntegrand T
  let G : ℝ → ℝ := fun t => hughesYoungHeightWeight T t * F t
  have hGint : Integrable G := by
    simpa only [G, F] using integrable_hughesYoungSmoothedMoment_integrand hT
  have hEq : ∀ t ∈ Set.Ioc (T / 2) (3 * T), F t = G t := by
    intro t ht
    have hw := hughesYoungHeightWeight_eq_one hT (Set.Ioc_subset_Icc_self ht)
    simp [G, hw]
  have hGnonneg : ∀ t, 0 ≤ G t := by
    intro t
    exact mul_nonneg (hughesYoungHeightWeight_nonneg T t) (by
      dsimp [F]
      unfold twistedZetaMomentIntegrand
      positivity)
  rw [twistedZetaFourthMoment, intervalIntegral.integral_of_le hOrder]
  change (∫ t in Set.Ioc (T / 2) (3 * T), F t) ≤ ∫ t, G t
  calc
    (∫ t in Set.Ioc (T / 2) (3 * T), F t) =
        ∫ t in Set.Ioc (T / 2) (3 * T), G t := by
      exact setIntegral_congr_fun measurableSet_Ioc hEq
    _ ≤ ∫ t, G t :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall hGnonneg) hGint

end RiemannZeta.GuthMaynard
