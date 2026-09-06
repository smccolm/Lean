import GafniTao.Pintz2023PhysicalScale
import GafniTao.Pintz2023CriticalScaleMonotone

/-!
# Pintz equation (4.14) at the source scales

This is the first complete consumer of the factorized large-`m` block.  The
common critical point is evaluated at `2T`, which contains every displaced
ordinate, while the polynomial itself retains Pintz's literal cutoff formed
from `T`.
-/

open Complex Finset

namespace GafniTao

noncomputable section

theorem pintz2023_largeM_localized_source_bound
    (k : ℕ) (epsilon : ℝ) (hk : 4 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T eta xi t : ℝ) (X q : ℕ),
        4 ≤ T → 0 ≤ eta → xi ≤ eta →
        eta + 6 * epsilon < pintz2023HBAlpha k →
        0 < 1 - ((k : ℝ) - 1) * eta - 6 * (k : ℝ) * epsilon →
        0 ≤ xi →
        T + 2 * pintz2023SourceLambda T k ≤ 2 * T →
        T / 4 < |t| → |t| ≤ T + 2 * pintz2023SourceLambda T k →
        1 ≤ X →
        2 ^ q * X ≤
          min (2 * (2 ^ q * X))
            (pintz2023Cutoff (pintz2023SourceLambda T k)) + 1 →
        ‖pintz2023SplitIntervalBlock
            (fun n => pintz2023LargeMCoeff X n
              (pintz2023CriticalScale k eta epsilon (2 * T)))
            (pintz2023LocalizedInterval X
              (pintz2023Cutoff (pintz2023SourceLambda T k)) q)
            (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          C * (X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ) *
            (pintz2023CriticalScale k eta epsilon (2 * T)) ^
              (-3 * epsilon) := by
  have hB : 0 < pintz2023CorThreePhysicalConstant := by
    unfold pintz2023CorThreePhysicalConstant
    positivity
  obtain ⟨C, hC, hCorThree⟩ :=
    pintz2023SplitLargeM_localized_corollary_three
      k epsilon pintz2023CorThreePhysicalConstant (show 3 ≤ k by omega)
        hepsilon hB
  refine ⟨C, hC, ?_⟩
  intro T eta xi t X q hT heta hxi hAlpha hdenEta hxiNonneg
    hShiftUpper hPhysical hUpper hX hNonempty
  have hTOne : 1 ≤ T := by linarith
  have hTwoTOne : 1 ≤ 2 * T := by linarith
  have hTwoT : 4 ≤ 2 * T := by linarith
  have hdenXi :
      0 < 1 - ((k : ℝ) - 1) * xi - 6 * (k : ℝ) * epsilon := by
    have hkNonneg : 0 ≤ (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hxi hkNonneg
    linarith
  have hxiAlpha : xi ≤ pintz2023HBAlpha k - 6 * epsilon := by
    linarith
  have hxiOne : xi + 3 * epsilon ≤ 1 := by
    have hAlphaOne : pintz2023HBAlpha k ≤ 1 := by
      unfold pintz2023HBAlpha
      have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hk
      have hkMinus : (3 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      have hprod : (1 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
      exact (div_le_one (by positivity)).2 hprod
    linarith
  have hQ : 1 ≤ pintz2023CriticalScale k eta epsilon (2 * T) :=
    one_le_pintz2023CriticalScale (show 0 < k by omega) hTwoTOne hdenEta
  have hCritical :
      pintz2023CriticalScale k xi epsilon (2 * T) ≤
        pintz2023CriticalScale k eta epsilon (2 * T) :=
    pintz2023CriticalScale_mono_xi (show 0 < k by omega) hxi hTwoTOne hdenEta
  have htPos : 0 < |t| := by linarith
  have htUpper : |t| ≤ 2 * T := hUpper.trans hShiftUpper
  have hA : 2 ^ q * X ≤
      pintz2023Cutoff (pintz2023SourceLambda T k) + 1 := by omega
  apply hCorThree xi (pintz2023CriticalScale k eta epsilon (2 * T))
    t (2 * T) X (pintz2023Cutoff (pintz2023SourceLambda T k)) q
    hxiAlpha hdenXi hxiNonneg hxiOne hQ hCritical htPos htUpper
    hTwoTOne hX hNonempty
  intro d hd hdX
  exact pintz2023_localized_physical_scale hk hTOne hTwoT
    (by linarith : T ≤ 2 * T) heta hAlpha hA
    (by nlinarith [hPhysical])

#print axioms pintz2023_largeM_localized_source_bound

end

end GafniTao
