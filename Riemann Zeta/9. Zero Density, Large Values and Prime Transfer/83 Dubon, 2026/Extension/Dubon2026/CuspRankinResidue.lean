import Dubon2026.CuspRankinContinuation
import Dubon2026.CuspPeterssonCore

/-! # Strict positivity of the true Rankin residue for every nonzero cusp form -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The actual Petersson self-pairing of a nonzero cusp form has strictly positive real part. -/
theorem cuspPetersson_re_pos {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    0 < (cuspPetersson f f).re := by
  by_contra h
  have he : (cuspPetersson f f).re = 0 :=
    le_antisymm (le_of_not_gt h) (cuspPetersson_re_nonneg f)
  apply hf
  apply cuspPetersson_definite f
  exact Complex.ext he (cuspPetersson_im_self f)

/-- The genuine real residue of the normalized Rankin square-series continuation. -/
def cuspRankinResidue {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℝ :=
  gamma0EisensteinResidue Q * (cuspPetersson f f).re / (cuspRankinFactor k 1).re

/-- The literal Rankin pole coefficient is strictly positive for nonzero cusp forms of positive weight. -/
theorem cuspRankinResidue_pos {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f :=
  div_pos (mul_pos (gamma0EisensteinResidue_pos Q) (cuspPetersson_re_pos f hf))
    (cuspRankinFactor_one_re_pos hk)

/-- The residue limit of the actual normalized square series is exactly the constructed positive real constant. -/
theorem cuspRankinContinuation_residue_real {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun s : ℂ => (s - 1) * cuspRankinContinuation f s) (𝓝[≠] 1)
      (𝓝 (cuspRankinResidue f : ℂ)) := by
  have hP : ((cuspPetersson f f).re : ℂ) = cuspPetersson f f := by
    apply Complex.ext
    · simp
    · simp [cuspPetersson_im_self]
  have hF : ((cuspRankinFactor k 1).re : ℂ) = cuspRankinFactor k 1 := by
    rw [cuspRankinFactor_one, Complex.ofReal_re]
  have he : (cuspRankinResidue f : ℂ) =
      ((gamma0EisensteinResidue Q : ℂ) * cuspPetersson f f) / cuspRankinFactor k 1 := by
    unfold cuspRankinResidue
    push_cast
    rw [hP, hF]
  rw [he]
  exact cuspRankinContinuation_residue_one f hk

end
end Dubon2026
