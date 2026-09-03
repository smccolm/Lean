import GafniTao.PintzWeightedSelection
import RiemannZeta.External.PNT.ZetaBoundsUpstream

/-!
# Uniform zeta control on Pintz's horizontal contour

The horizontal sides of the rectangle in Pintz equation (4.6) cross the
line `Re s = 1`.  Consequently neither the Ford strip estimate nor absolute
convergence alone controls the whole side.  This module keeps the three
genuine regimes separate: Ford on the left of one, the logarithmic PNT bound
across the line one, and the absolutely convergent half-plane from `3/2`
onwards.
-/

open Complex Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The pinned PNT theorem supplies a fixed positive logarithmic zeta
constant throughout the middle portion of Pintz's contour. -/
theorem exists_pintzLogZetaConstant :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t : ℝ}, 3 < |t| →
      1 ≤ sigma → sigma ≤ 3 / 2 →
      ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤ C * Real.log |t| := by
  obtain ⟨A, hA, C, hC, hBound⟩ := ZetaUpperBnd
  refine ⟨C, hC, ?_⟩
  intro sigma t ht hsigmaLower hsigmaUpper
  have hsigmaRange :
      sigma ∈ Set.Icc (1 - A / Real.log |t|) 2 := by
    constructor
    · have hlogPos : 0 < Real.log |t| := by
        exact Real.log_pos (by linarith : 1 < |t|)
      have hfrac : 0 < A / Real.log |t| := div_pos hA.1 hlogPos
      linarith
    · linarith
  simpa [mul_comm] using hBound sigma t ht hsigmaRange

noncomputable def pintzLogZetaConstant : ℝ :=
  Classical.choose exists_pintzLogZetaConstant

/-- A single nonnegative envelope for the three pieces of Pintz's horizontal
contour.  It is deliberately a sum, so each source estimate enters without a
comparison between unrelated absolute constants. -/
noncomputable def pintzHorizontalZetaMajorant (η T : ℝ) : ℝ :=
  fordQualitativeGlobalCoefficient *
      (2 * T) ^ (fordSourceB 3000000 * (2 * η) ^ (3 / 2 : ℝ)) *
      Real.log (2 * T) ^ (2 / 3 : ℝ) +
    pintzLogZetaConstant * Real.log (2 * T) +
    hughesYoungZetaHalfPlaneMajorant

theorem pintzLogZetaConstant_pos : 0 < pintzLogZetaConstant := by
  exact (Classical.choose_spec exists_pintzLogZetaConstant).1

theorem hughesYoungZetaHalfPlaneMajorant_nonneg :
    0 ≤ hughesYoungZetaHalfPlaneMajorant := by
  unfold hughesYoungZetaHalfPlaneMajorant
  exact tsum_nonneg fun _ => norm_nonneg _

theorem pintzHorizontalZetaMajorant_nonneg
    {eta T : ℝ} (hT : 1 / 2 ≤ T) :
    0 ≤ pintzHorizontalZetaMajorant eta T := by
  unfold pintzHorizontalZetaMajorant
  have hbase : 1 ≤ 2 * T := by linarith
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg hbase
  have hford : 0 ≤ fordQualitativeGlobalCoefficient :=
    fordQualitativeGlobalCoefficient_nonneg
  have hpow :
      0 ≤ (2 * T) ^
        (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) :=
    Real.rpow_nonneg (by linarith) _
  have hlogpow : 0 ≤ Real.log (2 * T) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hlog _
  have hpnt : 0 ≤ pintzLogZetaConstant := pintzLogZetaConstant_pos.le
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hford hpow) hlogpow)
      (mul_nonneg hpnt hlog))
    hughesYoungZetaHalfPlaneMajorant_nonneg

/-- The PNT logarithmic estimate in the exact fixed-constant form used in the
middle portion of Pintz's horizontal contour. -/
theorem norm_riemannZeta_le_pintzLogZeta
    {sigma t : ℝ} (ht : 3 < |t|) (hsigmaLower : 1 ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 2) :
    ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      pintzLogZetaConstant * Real.log |t| := by
  exact (Classical.choose_spec exists_pintzLogZetaConstant).2
    ht hsigmaLower hsigmaUpper

/-- Uniform zeta bound on the whole real interval traversed by a Pintz
horizontal edge.  The hypotheses on `t` and `T` are exactly the physical
height window later obtained from the selected zero ordinate. -/
theorem norm_riemannZeta_le_pintzHorizontalZetaMajorant
    {eta sigma t T : ℝ}
    (heta : 0 ≤ eta) (hetaUpper : eta ≤ 1 / 4)
    (hsigmaLower : 1 - 2 * eta ≤ sigma)
    (htLower : 3 < |t|) (htUpper : |t| ≤ 2 * T) :
    ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      pintzHorizontalZetaMajorant eta T := by
  have htwoT : 1 ≤ 2 * T := by linarith
  have htOne : 1 ≤ |t| := by linarith
  have hlogMono : Real.log |t| ≤ Real.log (2 * T) :=
    Real.log_le_log (by positivity) htUpper
  have hlogNonneg : 0 ≤ Real.log (2 * T) := Real.log_nonneg htwoT
  have hfordTermNonneg :
      0 ≤ fordQualitativeGlobalCoefficient *
        (2 * T) ^ (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) *
        Real.log (2 * T) ^ (2 / 3 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg fordQualitativeGlobalCoefficient_nonneg
        (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg hlogNonneg _)
  have hlogTermNonneg :
      0 ≤ pintzLogZetaConstant * Real.log (2 * T) :=
    mul_nonneg pintzLogZetaConstant_pos.le hlogNonneg
  by_cases hsigmaOne : sigma ≤ 1
  · have hsigmaHalf : (1 / 2 : ℝ) ≤ sigma := by linarith
    have hford := ford_qualitative_global_zeta_growth
      hsigmaHalf hsigmaOne htLower.le
    have hgap : 0 ≤ 1 - sigma := by linarith
    have hgapUpper : 1 - sigma ≤ 2 * eta := by linarith
    have hetaTwo : 0 ≤ 2 * eta := by positivity
    have hpowerGap :
        (1 - sigma) ^ (3 / 2 : ℝ) ≤
          (2 * eta) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hgap hgapUpper (by norm_num)
    have hBnonneg : 0 ≤ fordSourceB 3000000 :=
      le_trans (by norm_num) four_le_fordSourceB_three_million
    have hexponent :
        fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ) ≤
          fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ) := by
      gcongr
    have hexponentNonneg :
        0 ≤ fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ) := by
      positivity
    have hheightPower :
        |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
          (2 * T) ^
            (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) := by
      calc
        |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
            (2 * T) ^
              (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg t) htUpper hexponentNonneg
        _ ≤ (2 * T) ^
              (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le htwoT hexponent
    have hlogPower :
        Real.log |t| ^ (2 / 3 : ℝ) ≤
          Real.log (2 * T) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg htOne) hlogMono (by norm_num)
    calc
      ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          fordQualitativeGlobalCoefficient *
            |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            Real.log |t| ^ (2 / 3 : ℝ) := hford
      _ ≤ fordQualitativeGlobalCoefficient *
            (2 * T) ^
              (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) *
            Real.log (2 * T) ^ (2 / 3 : ℝ) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hheightPower
              fordQualitativeGlobalCoefficient_nonneg)
            hlogPower (Real.rpow_nonneg (Real.log_nonneg htOne) _)
            (mul_nonneg fordQualitativeGlobalCoefficient_nonneg
              (Real.rpow_nonneg (by linarith) _))
      _ ≤ pintzHorizontalZetaMajorant eta T := by
        unfold pintzHorizontalZetaMajorant
        linarith [hlogTermNonneg,
            hughesYoungZetaHalfPlaneMajorant_nonneg]
  · have hsigmaOne' : 1 ≤ sigma := le_of_not_ge hsigmaOne
    by_cases hsigmaThreeHalf : sigma ≤ 3 / 2
    · have hpnt := norm_riemannZeta_le_pintzLogZeta
        htLower hsigmaOne' hsigmaThreeHalf
      calc
        ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
            pintzLogZetaConstant * Real.log |t| := hpnt
        _ ≤ pintzLogZetaConstant * Real.log (2 * T) := by
          exact mul_le_mul_of_nonneg_left hlogMono pintzLogZetaConstant_pos.le
        _ ≤ pintzHorizontalZetaMajorant eta T := by
          unfold pintzHorizontalZetaMajorant
          linarith [hfordTermNonneg,
            hughesYoungZetaHalfPlaneMajorant_nonneg]
    · have habs := norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant
        (s := (sigma : ℂ) + I * t) (by simp; linarith)
      exact habs.trans (by
        unfold pintzHorizontalZetaMajorant
        linarith)

#print axioms norm_riemannZeta_le_pintzLogZeta
#print axioms norm_riemannZeta_le_pintzHorizontalZetaMajorant

end

end GafniTao
