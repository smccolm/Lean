import GafniTao.FordShiftedZeroDetectorInequality
import GafniTao.FordZeroDetectorPoleCorrection

/-!
# The shifted detector's explicit zeta-pole correction

The correction vanishes at real centre one.  For a centre to the right of
one it is a genuine nonnegative term and therefore cannot be deleted from
an upper bound without a separate estimate.
-/

open Complex

namespace GafniTao

noncomputable section

theorem fordShiftedDetector_poleCorrection_eq
    (sigma eta t : ℝ) :
    -(fordCotKernel eta
        (1 - fordShiftedDetectorCenter sigma t)).re =
      (fordCotKernel eta
        (fordShiftedDetectorCenter sigma t - 1)).re := by
  rw [show 1 - fordShiftedDetectorCenter sigma t =
      -(fordShiftedDetectorCenter sigma t - 1) by ring,
    fordCotKernel_neg]
  simp

theorem fordShiftedDetector_poleCorrection_nonneg
    {sigma eta t : ℝ} (hsigma : 1 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1 + eta) (heta : 0 < eta) :
    0 ≤ -(fordCotKernel eta
      (1 - fordShiftedDetectorCenter sigma t)).re := by
  rw [fordShiftedDetector_poleCorrection_eq]
  apply fordCotKernel_re_nonneg heta
  · simp [fordShiftedDetectorCenter]
    linarith
  · simp [fordShiftedDetectorCenter]
    linarith

theorem fordShiftedDetector_poleCorrection_eq_zero_at_one
    (eta t : ℝ) :
    -(fordCotKernel eta
      (1 - fordShiftedDetectorCenter 1 t)).re = 0 := by
  simpa [fordShiftedDetectorCenter, fordDetectorCenter] using
    congrArg Neg.neg
      (re_fordCotKernel_one_sub_center_eq_zero eta t)

end

end GafniTao
