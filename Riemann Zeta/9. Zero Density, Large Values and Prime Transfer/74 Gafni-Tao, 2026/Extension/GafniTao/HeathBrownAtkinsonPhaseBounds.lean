import GafniTao.HeathBrownAtkinsonPhaseDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Monotonicity and curvature of Heath--Brown's Atkinson phase

The source proof repeatedly compares equation-(11) phases at nearby heights.
These lemmas derive the required sign and monotonicity facts from the exact
differential identities, on the physical half-line `T > 0`.
-/

open Set

namespace GafniTao

noncomputable section

theorem heathBrownAtkinsonRatio_pos
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    0 < heathBrownAtkinsonRatio T n := by
  unfold heathBrownAtkinsonRatio
  positivity

theorem heathBrownAtkinsonRoot_pos
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    0 < heathBrownAtkinsonRoot T n := by
  unfold heathBrownAtkinsonRoot
  exact Real.sqrt_pos.2 (heathBrownAtkinsonRatio_pos hT hn)

theorem heathBrownAtkinsonPhaseSlope_pos
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    0 < 2 * Real.arsinh (heathBrownAtkinsonRoot T n) := by
  have hx := heathBrownAtkinsonRoot_pos hT hn
  have ha : 0 < Real.arsinh (heathBrownAtkinsonRoot T n) := by
    rwa [Real.arsinh_pos_iff]
  positivity

theorem heathBrownAtkinsonPhaseCurvature_neg
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    -heathBrownAtkinsonRoot T n /
        (T * Real.sqrt (1 + (heathBrownAtkinsonRoot T n) ^ 2)) < 0 := by
  have hx := heathBrownAtkinsonRoot_pos hT hn
  have hs : 0 < Real.sqrt
      (1 + (heathBrownAtkinsonRoot T n) ^ 2) := by
    positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hx) (mul_pos hT hs)

/-- For fixed positive `n`, the literal Atkinson phase is strictly increasing
with height. -/
theorem strictMonoOn_heathBrownAtkinsonPhase (n : ℕ) (hn : 0 < n) :
    StrictMonoOn (fun T => heathBrownAtkinsonPhase T n) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro T hT
    exact (hasDerivAt_heathBrownAtkinsonPhase hT hn).continuousAt.continuousWithinAt
  · intro T hT
    simp only [interior_Ioi, mem_Ioi] at hT
    rw [(hasDerivAt_heathBrownAtkinsonPhase hT hn).deriv]
    exact heathBrownAtkinsonPhaseSlope_pos hT hn

/-- For fixed positive `n`, the exact phase slope is strictly decreasing with
height. -/
theorem strictAntiOn_heathBrownAtkinsonPhaseSlope (n : ℕ) (hn : 0 < n) :
    StrictAntiOn
      (fun T => 2 * Real.arsinh (heathBrownAtkinsonRoot T n))
      (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro T hT
    exact (hasDerivAt_heathBrownAtkinsonPhaseSlope hT hn).continuousAt.continuousWithinAt
  · intro T hT
    simp only [interior_Ioi, mem_Ioi] at hT
    rw [(hasDerivAt_heathBrownAtkinsonPhaseSlope hT hn).deriv]
    exact heathBrownAtkinsonPhaseCurvature_neg hT hn

theorem heathBrownAtkinsonPhase_lt_of_lt
    {T₁ T₂ : ℝ} {n : ℕ} (hT₁ : 0 < T₁) (hT₂ : T₁ < T₂)
    (hn : 0 < n) :
    heathBrownAtkinsonPhase T₁ n < heathBrownAtkinsonPhase T₂ n :=
  strictMonoOn_heathBrownAtkinsonPhase n hn hT₁ (hT₁.trans hT₂) hT₂

theorem heathBrownAtkinsonPhaseSlope_lt_of_lt
    {T₁ T₂ : ℝ} {n : ℕ} (hT₁ : 0 < T₁) (hT₂ : T₁ < T₂)
    (hn : 0 < n) :
    2 * Real.arsinh (heathBrownAtkinsonRoot T₂ n) <
      2 * Real.arsinh (heathBrownAtkinsonRoot T₁ n) :=
  strictAntiOn_heathBrownAtkinsonPhaseSlope n hn hT₁
    (hT₁.trans hT₂) hT₂


end

end GafniTao
