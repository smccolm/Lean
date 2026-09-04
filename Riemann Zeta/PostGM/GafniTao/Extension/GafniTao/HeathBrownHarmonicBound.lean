import GafniTao.HeathBrownHarmonicSum
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The logarithmic loss in Heath-Brown's shift sum

The source replaces the harmonic sum over positive shifts by `O(log N)`.
This file records that replacement with its exact finite endpoint behavior.
-/

namespace GafniTao

noncomputable section

theorem harmonic_cast_le_one_add_log_of_le
    {D N : ℕ} (hDN : D ≤ N) (hN : 1 ≤ N) :
    (harmonic D : ℝ) ≤ 1 + Real.log N := by
  by_cases hD0 : D = 0
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
    simp [hD0]
    linarith
  · have hDpos : (0 : ℝ) < D := by
      exact_mod_cast (Nat.pos_of_ne_zero hD0)
    calc
      (harmonic D : ℝ) ≤ 1 + Real.log D := harmonic_le_one_add_log D
      _ ≤ 1 + Real.log N := by
        exact add_le_add_right
          (Real.log_le_log hDpos
            (by exact_mod_cast hDN : (D : ℝ) ≤ (N : ℝ))) 1

theorem heathBrownShiftBound_harmonic_le
    {N k H : ℕ} {lambda : ℝ} (hN : 1 ≤ N) :
    (harmonic (heathBrownShiftBound N k H lambda) : ℝ) ≤
      1 + Real.log N :=
  harmonic_cast_le_one_add_log_of_le
    (heathBrownShiftBound_le_N N k H lambda) hN

#print axioms harmonic_cast_le_one_add_log_of_le
#print axioms heathBrownShiftBound_harmonic_le

end

end GafniTao
