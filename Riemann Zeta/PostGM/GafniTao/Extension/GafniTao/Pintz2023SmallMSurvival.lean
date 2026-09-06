import GafniTao.Pintz2023LargeMAbsorption
import GafniTao.Pintz2023SmallMIntervalPower

/-!
# Pintz (2023), equation (4.15): removal of the negligible large-m part

This file contains the exact reverse-triangle step between (4.14) and
(4.15).  Keeping it as a theorem prevents the later powering argument from
silently reverting to the original unsplit coefficient.
-/

open Complex Finset

namespace GafniTao

noncomputable section

/-- Exact subtraction inequality on an arbitrary finite source interval. -/
theorem pintz2023_smallM_survives_largeM_subtraction
    (X : ℕ) (R : ℝ) (Iset : Finset ℕ) (s : ℂ) (V E : ℝ)
    (hFull : V ≤ ‖pintz2023IntervalBlock X Iset s‖)
    (hLarge :
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023LargeMCoeff X n R) Iset s‖ ≤ E) :
    V - E ≤
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R) Iset s‖ := by
  have hSplit := pintz2023IntervalBlock_eq_largeM_add_smallM
    X Iset R s
  have hTriangle :
      ‖pintz2023IntervalBlock X Iset s‖ ≤
        ‖pintz2023SplitIntervalBlock
          (fun n => pintz2023LargeMCoeff X n R) Iset s‖ +
        ‖pintz2023SplitIntervalBlock
          (fun n => pintz2023SmallMCoeff X n R) Iset s‖ := by
    rw [hSplit]
    exact norm_add_le _ _
  linarith

/-- The convenient half-strength form used after the eventual comparison
`E ≤ V/2`. -/
theorem pintz2023_smallM_survives_half
    (X : ℕ) (R : ℝ) (Iset : Finset ℕ) (s : ℂ) (V E : ℝ)
    (hFull : V ≤ ‖pintz2023IntervalBlock X Iset s‖)
    (hLarge :
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023LargeMCoeff X n R) Iset s‖ ≤ E)
    (hError : E ≤ V / 2) :
    V / 2 ≤
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R) Iset s‖ := by
  have h := pintz2023_smallM_survives_largeM_subtraction
    X R Iset s V E hFull hLarge
  linarith

/-- A positive lower bound forces the selected, possibly truncated, source
interval to be nonempty. -/
theorem pintz2023LocalizedInterval_nonempty_of_positive_block
    {X Y r : ℕ} {R V : ℝ} {s : ℂ}
    (hV : 0 < V)
    (hBlock : V ≤
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R)
        (pintz2023LocalizedInterval X Y r) s‖) :
    (pintz2023LocalizedInterval X Y r).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hBlock
  simp [pintz2023SplitIntervalBlock] at hBlock
  linarith

/-- The exact endpoint comparison needed by the equation-(4.14) consumer is
forced by nonemptiness of the literal localized interval. -/
theorem pintz2023LocalizedInterval_left_le_right_add_one_of_nonempty
    {X Y r : ℕ}
    (hNonempty : (pintz2023LocalizedInterval X Y r).Nonempty) :
    2 ^ r * X ≤ min (2 * (2 ^ r * X)) Y + 1 := by
  obtain ⟨n, hn⟩ := hNonempty
  unfold pintz2023LocalizedInterval at hn
  rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc] at hn
  omega

#print axioms pintz2023_smallM_survives_largeM_subtraction
#print axioms pintz2023_smallM_survives_half
#print axioms pintz2023LocalizedInterval_nonempty_of_positive_block
#print axioms pintz2023LocalizedInterval_left_le_right_add_one_of_nonempty

end

end GafniTao
