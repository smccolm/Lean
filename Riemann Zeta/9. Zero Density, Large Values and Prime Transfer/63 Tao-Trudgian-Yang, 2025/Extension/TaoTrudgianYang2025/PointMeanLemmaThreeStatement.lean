import TaoTrudgianYang2025.PointMeanIntegralOverlap

/-!
Adapted from the adjacent Gafni--Tao development, using the literal target
critical-line zeta norm and the local contour and Gamma-kernel proofs.

# Heath--Brown's Lemma 3: exact source statement and coordinate bridge

The proposition below is the literal local critical-line inequality on page
455 of Heath--Brown (1978), with its absolute Vinogradov constant exposed.
This file gives its statement and exact coordinate and interval-enlargement
bridges. `PointMeanLemmaThreeTail` proves an instance from the local contour
argument; this statement module does not postulate one.
-/

open Finset MeasureTheory
open scoped BigOperators Interval

namespace TaoTrudgianYang2025

noncomputable section

/-- The truncated exponentially weighted critical-line second moment in the
coordinates printed in Heath--Brown's Lemma 3. -/
noncomputable def heathBrownLemmaThreeMoment (t L : ℝ) : ℝ :=
  ∫ u in -L..L,
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

/-- Heath--Brown (1978), Lemma 3, with an explicit absolute constant. -/
def HeathBrownLemmaThree : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 10 ≤ t →
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t *
          (1 + heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)))

/-- Translation from the source's increment coordinate `u` to the physical
ordinate coordinate.  This is an exact identity with the literal
exponential kernel. -/
theorem heathBrownLemmaThreeMoment_eq_centered (t L : ℝ) :
    heathBrownLemmaThreeMoment t L =
      ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) := by
  let f : ℝ → ℝ := fun v ↦
    Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ)
  have hshift := intervalIntegral.integral_comp_add_right f t
      (a := -L) (b := L)
  unfold heathBrownLemmaThreeMoment
  calc
    (∫ u in -L..L,
        Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) =
        ∫ u in -L..L, f (u + t) := by
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [f, show t - (u + t) = -u by ring, abs_neg]
      rw [add_comm]
    _ = ∫ v in -L + t..L + t, f v := hshift
    _ = ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) := by
      congr 1 <;> dsimp [f] <;> ring

/-- A source Lemma-3 moment may be enlarged to any symmetric radius which
dominates `(log t)^2`. -/
theorem heathBrownLemmaThreeMoment_le_centered
    (t L : ℝ) (hlogL : Real.log t ^ (2 : ℕ) ≤ L) :
    heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)) ≤
      ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) := by
  rw [heathBrownLemmaThreeMoment_eq_centered]
  apply intervalIntegral.integral_mono_interval
  · linarith
  · nlinarith [sq_nonneg (Real.log t)]
  · linarith
  · filter_upwards with v
    positivity
  · exact intervalIntegrable_exp_neg_abs_sub_mul
      (fun v : ℝ ↦ zetaMomentCriticalNorm v ^ (2 : ℕ))
      (continuous_zetaMomentCriticalNorm.pow 2) t (t - L) (t + L)


end

end TaoTrudgianYang2025
