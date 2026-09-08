import GafniTao.FordLocalCotangentSelected
import GafniTao.FordShiftedZeroDetectorLimit

/-!
# Ford's selected detector with the actual local zero count

The theorem in this file is the first complete consumer of the selected
contour inequality.  It inserts Ford's actual disk, proves all containment
and height comparisons, and replaces the zero sum by the coercive
multiplicity-weighted `N(t,R)` term.
-/

open Complex Finset Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem eventually_exists_fordLocalDisk_detector_inequality
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
                (1 + (6421 / 10000 : ℝ) * R) t)).re -
            fordShiftedDetectorPhysicalVerticalBulk eta'
              (1 + (6421 / 10000 : ℝ) * R) t
              (eta' : ℂ) (-RLower) RUpper +
            fordShiftedDetectorPhysicalVerticalBulk eta'
              (1 + (6421 / 10000 : ℝ) * R) t
              (-eta' : ℂ) (-RLower) RUpper + ε := by
  obtain ⟨_C, _hC, hselected⟩ :=
    eventually_exists_fordShiftedDetector_selected_subset_inequality
  have hsigma : 1 ≤ 1 + (6421 / 10000 : ℝ) * R := by
    nlinarith
  have heta : 0 < (5 / 2 : ℝ) * R := mul_pos (by norm_num) hR
  have hetaMax : (5 / 2 : ℝ) * R < (51 / 20 : ℝ) * R := by
    nlinarith
  have hPole :
      (1 + (6421 / 10000 : ℝ) * R) - 1 ≤ (5 / 2 : ℝ) * R := by
    nlinarith
  have hleft :
      -1 ≤ (1 + (6421 / 10000 : ℝ) * R) -
        (51 / 20 : ℝ) * R := by
    nlinarith
  intro ε hε
  obtain ⟨T0, hT0⟩ := hselected hsigma heta hetaMax hPole hleft ht ε hε
  refine ⟨T0, ?_⟩
  intro T hT0T hT hTlarge
  have hTlargeNarrow :
      t + 2 * ((51 / 20 : ℝ) * R) / Real.pi ≤ T := by
    have hscale : (51 / 20 : ℝ) * R ≤ 3 * R := by nlinarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 2))
      hpi.le
    linarith
  obtain ⟨eta', RUpper, RLower, heta', heta'Upper,
      hRU, hRL, hineq⟩ := hT0 hT0T hT hTlargeNarrow
  have hpiSix : Real.pi < 6 := Real.pi_lt_four.trans (by norm_num)
  have hRScale : R ≤ 2 * (3 * R) / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith
  have hTR : t + R ≤ T := by linarith
  have himLower : -RLower ≤ t - R := by
    have hRLarge : t + R ≤ RLower := hTR.trans hRL.1
    linarith
  have himUpper : t + R ≤ RUpper := hTR.trans hRU.1
  have hsubset : fordLocalDiskZeros t R ⊆
      fordShiftedDetectorPhysicalZeros
        (1 + (6421 / 10000 : ℝ) * R) eta' (-RLower) RUpper := by
    apply fordLocalDiskZeros_subset_physical
    · nlinarith
    · nlinarith
    · exact himLower
    · exact himUpper
  have hdet := hineq (fordLocalDiskZeros t R) hsubset
  have hsum := sum_fordLocalDisk_selected_zeroContribution_le
    (t := t) (eta' := eta') hR heta'.le (by nlinarith : eta' ≤ 3 * R)
  refine ⟨eta', RUpper, RLower, heta', heta'Upper, hRU, hRL, ?_⟩
  linarith

end

end GafniTao
