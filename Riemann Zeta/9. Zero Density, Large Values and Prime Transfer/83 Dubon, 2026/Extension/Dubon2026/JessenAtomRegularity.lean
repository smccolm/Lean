import Dubon2026.RegularAbscissae
import Dubon2026.JessenStieltjes

/-! # Boundary atoms and differentiability of the actual Jessen function -/

namespace Dubon2026

open Set Function

theorem hasDerivAt_jessen_of_atom_eq_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {x : ℝ} (hx : jessenMeasure hN ha {x} = 0) :
    HasDerivAt (jessenFunction a N) (derivWithin (jessenFunction a N) (Ioi x) x) x := by
  have hf := convexOn_jessenFunction hN ha
  have hm := monotone_convex_rightDeriv hf
  apply hasDerivAt_convex_of_continuous_rightDeriv hf
  apply hm.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [leftLim_convex_rightDeriv hf, rightLim_convex_rightDeriv hf]
  rw [jessenMeasure_singleton, ENNReal.ofReal_eq_zero] at hx
  have hh := hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp : x ∈ interior univ)
  linarith

theorem jessenMeasure_atom_eq_zero_of_hasDerivAt {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {x d : ℝ} (hd : HasDerivAt (jessenFunction a N) d x) :
    jessenMeasure hN ha {x} = 0 := by
  rw [jessenMeasure_singleton,
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x),
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x), sub_self, ENNReal.ofReal_zero]

end Dubon2026
