import GafniTao.FordShiftedRightBulkBound

/-!
# The local Ford detector after discharging the right vertical edge

This is a direct consumer of the selected local-disk detector.  The right
bulk is replaced by its explicit Euler-product majorant; the pole correction
and the left bulk remain visible for their separate source-faithful bounds.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem eventually_exists_fordLocalDisk_detector_rightBound
    {t R : ℝ} (ht : 0 < t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T → 8 ≤ T →
        t + 2 * (3 * R) / Real.pi ≤ T →
        ∃ eta' RUpper RLower : ℝ,
          (5 / 2 : ℝ) * R < eta' ∧ eta' < (51 / 20 : ℝ) * R ∧
          RUpper ∈ Set.Icc T (T + 1) ∧
          RLower ∈ Set.Icc T (T + 1) ∧
          -(fordDetectorZetaLogDeriv
              (fordShiftedDetectorCenter
                (1 + (6421 / 10000 : ℝ) * R) t)).re <
            -((fordLocalDiskZeroCount t R : ℝ) *
              (fordLocalCotUniformLowerConstant / R)) -
            (fordCotKernel eta'
              (1 - fordShiftedDetectorCenter
                (1 + (6421 / 10000 : ℝ) * R) t)).re +
            Real.log (1 + 1 / (3 * R)) / (2 * eta') +
            fordShiftedDetectorPhysicalVerticalBulk eta'
              (1 + (6421 / 10000 : ℝ) * R) t
              (-eta' : ℂ) (-RLower) RUpper + ε := by
  intro ε hε
  obtain ⟨T0, hT0⟩ :=
    eventually_exists_fordLocalDisk_detector_inequality ht hR hRUpper ε hε
  refine ⟨T0, ?_⟩
  intro T hT0T hT hTlarge
  obtain ⟨eta', RUpper, RLower, hetaLower, hetaUpper,
      hRU, hRL, hdet⟩ := hT0 hT0T hT hTlarge
  have hetaPos : 0 < eta' := (mul_pos (by norm_num) hR).trans hetaLower
  have hsigmaRight :
      1 < (1 + (6421 / 10000 : ℝ) * R) + eta' := by
    nlinarith
  have hden : 3 * R ≤
      (1 + (6421 / 10000 : ℝ) * R) + eta' - 1 := by
    nlinarith
  have hdenPos : 0 <
      (1 + (6421 / 10000 : ℝ) * R) + eta' - 1 := by
    nlinarith
  have hM : 1 + 1 /
        ((1 + (6421 / 10000 : ℝ) * R) + eta' - 1) ≤
      1 + 1 / (3 * R) := by
    gcongr
  have hy : -RLower ≤ RUpper := by
    have hRLowerPos : 0 < RLower := lt_of_lt_of_le (by norm_num) (hT.trans hRL.1)
    have hRUpperPos : 0 < RUpper := lt_of_lt_of_le (by norm_num) (hT.trans hRU.1)
    linarith
  have hright := fordShiftedDetectorPhysicalVerticalBulk_right_lower
    (eta := eta') (sigma := 1 + (6421 / 10000 : ℝ) * R)
    (t := t) (yLower := -RLower) (yUpper := RUpper)
    (M := 1 + 1 / (3 * R)) hetaPos hsigmaRight hM hy
  have hright' :
      -fordShiftedDetectorPhysicalVerticalBulk eta'
          (1 + (6421 / 10000 : ℝ) * R) t
          (eta' : ℂ) (-RLower) RUpper ≤
        Real.log (1 + 1 / (3 * R)) / (2 * eta') := by
    have hneg := neg_le_neg hright
    simpa only [neg_div, neg_neg] using hneg
  refine ⟨eta', RUpper, RLower, hetaLower, hetaUpper, hRU, hRL, ?_⟩
  exact hdet.trans_le (by linarith [hright'])

#print axioms eventually_exists_fordLocalDisk_detector_rightBound

end

end GafniTao
