import Dubon2026.BinomialJessen
import Dubon2026.ConvexDerivatives

/-! # The atom and the factor of two pi in the source's normalization example -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem convexOn_binomialJessen {κ : ℝ} (hκ : 0 < κ) :
    ConvexOn ℝ univ (binomialJessen κ) := by
  have hlin := (LinearMap.mul ℝ ℝ (-κ)).convexOn (s := univ) convex_univ
  have hh := (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))).sup hlin
  have he : binomialJessen κ = (fun x => max 0 (-κ * x)) := funext (binomialJessen_eq hκ)
  rw [he]
  exact hh

theorem rightDeriv_binomialJessen {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    derivWithin (binomialJessen κ) (Ioi x) x = if x < 0 then -κ else 0 := by
  by_cases hx : x < 0
  · rw [if_pos hx]
    have hd : HasDerivWithinAt (fun y : ℝ => -κ * y) (-κ) (Ioi x) x := by
      simpa only [mul_one] using ((hasDerivAt_id x).const_mul (-κ)).hasDerivWithinAt
    have he : binomialJessen κ =ᶠ[𝓝[>] x] (fun y => -κ * y) := by
      filter_upwards [(eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy
      rw [binomialJessen_eq hκ, max_eq_right (mul_nonneg_of_nonpos_of_nonpos (by linarith) hy.le)]
    exact (hd.congr_of_eventuallyEq he
      (by rw [binomialJessen_eq hκ, max_eq_right
        (mul_nonneg_of_nonpos_of_nonpos (by linarith) hx.le)])).derivWithin
          (uniqueDiffWithinAt_Ioi x)
  · rw [if_neg hx]
    have hx0 : 0 ≤ x := le_of_not_gt hx
    have hd : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ioi x) x :=
      (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
    have he : binomialJessen κ =ᶠ[𝓝[>] x] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [binomialJessen_eq hκ, max_eq_left (mul_nonpos_of_nonpos_of_nonneg
        (by linarith) (hx0.trans hy.le))]
    exact (hd.congr_of_eventuallyEq he
      (by rw [binomialJessen_eq hκ, max_eq_left
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hx0)])).derivWithin
          (uniqueDiffWithinAt_Ioi x)

/-- The positive Stieltjes second derivative of the example's actual Jessen function. -/
def binomialJessenMeasure {κ : ℝ} (hκ : 0 < κ) : Measure ℝ :=
  (convexDerivativeStieltjes (convexOn_binomialJessen hκ)).measure

theorem binomialJessenMeasure_eq_dirac {κ : ℝ} (hκ : 0 < κ) :
    binomialJessenMeasure hκ = ENNReal.ofReal κ • Measure.dirac 0 := by
  unfold binomialJessenMeasure
  apply Measure.ext_of_Ioc
  intro a b hab
  change (convexDerivativeStieltjes (convexOn_binomialJessen hκ)).measure (Ioc a b) = _
  rw [StieltjesFunction.measure_Ioc, convexDerivativeStieltjes_apply,
    convexDerivativeStieltjes_apply, rightDeriv_binomialJessen hκ, rightDeriv_binomialJessen hκ,
    Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc]
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · simp [ha, hb, not_le_of_gt hb]
  · simp [ha, hb, le_of_not_gt hb]
  · have hb0 : ¬b < 0 := not_lt.mpr ((le_of_not_gt ha).trans hab.le)
    exact (hb0 hb).elim
  · simp [ha, hb]

theorem scaled_binomialJessenMeasure_eq_dirac {κ : ℝ} (hκ : 0 < κ) :
    ENNReal.ofReal (1 / (2 * Real.pi)) • binomialJessenMeasure hκ =
      ENNReal.ofReal (κ / (2 * Real.pi)) • Measure.dirac 0 := by
  rw [binomialJessenMeasure_eq_dirac, smul_smul, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

end

end Dubon2026
