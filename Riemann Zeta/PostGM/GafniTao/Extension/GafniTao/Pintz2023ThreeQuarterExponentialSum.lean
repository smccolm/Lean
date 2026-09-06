import GafniTao.Pintz2023ThreeQuarterZetaExponent
import GafniTao.ClassicalA2BOptimization
import GafniTao.HeathBrownEP1Fixed
import GafniTao.HeathBrownEP1Large

/-!
# Pintz's logarithmic exponential sum down to real part three quarters

This is the exact unweighted prefix estimate required by the off-diagonal
Gram kernel when `eta < 1 / 24`.  The proof uses the four ranges whose
exponent arithmetic was checked in `Pintz2023ThreeQuarterZetaExponent`.
-/

namespace GafniTao

noncomputable section

/-- Native logarithmic-prefix bound with Pintz's coefficient `1/2`, uniform
for `3/4 ≤ sigma ≤ 1` and every terminal point of the dyadic block. -/
theorem norm_pintz2023ExponentialBlock_le_threeQuarter_target
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℝ) (N R : ℕ) (tau : ℝ),
      sigma ≤ 1 → 3 / 4 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N → 2 ≤ tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ pintzNearOneUnweightedTarget sigma epsilon tau := by
  obtain ⟨C₅ₐ, hC₅ₐ, hkfiveA⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_kfive_constant epsilon hepsilon
  obtain ⟨C₅ₑ, hC₅ₑ, hkfiveB⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_kfive_sloping epsilon hepsilon
  obtain ⟨Cₗ, hCₗ, hlarge⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_large epsilon hepsilon
  let C : ℝ := 90 + 49 + 43 + C₅ₐ + C₅ₑ + Cₗ
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro sigma N R tau hsigmaUpper hsigmaLower hN hNR hR htau
  have hNPos : 0 < N := by omega
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have htargetNonneg :
      0 ≤ (N : ℝ) ^ pintzNearOneUnweightedTarget sigma epsilon tau :=
    Real.rpow_nonneg (by positivity) _
  by_cases hab : tau ≤ 9 / 4
  · have hraw := norm_pintz2023ExponentialBlock_le_AB_log_power
      hN hNR hR htau (hab.trans (by norm_num))
    have hexp := pintz_threeQuarter_AB_exponent_le
      hsigmaUpper hsigmaLower hepsilon.le htau hab
    calc
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
          90 * (N : ℝ) ^ ((tau + 3) / 6) := hraw
      _ ≤ 90 * (N : ℝ) ^
          pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
      _ ≤ C * (N : ℝ) ^
          pintzNearOneUnweightedTarget sigma epsilon tau := by
        apply mul_le_mul_of_nonneg_right _ htargetNonneg
        dsimp only [C]
        nlinarith
  · have htauA2 : 9 / 4 ≤ tau := le_of_not_ge hab
    by_cases ha2 : tau ≤ 25 / 8
    · have hraw := norm_pintz2023ExponentialBlock_le_A2B_power
        hN hNR hR htauA2 (ha2.trans (by norm_num))
      have hexp := pintz_threeQuarter_A2B_exponent_le
        hsigmaUpper hsigmaLower hepsilon.le htauA2 ha2
      calc
        ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
            49 * (N : ℝ) ^ ((tau + 10) / 14) := hraw
        _ ≤ 49 * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
        _ ≤ C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau := by
          apply mul_le_mul_of_nonneg_right _ htargetNonneg
          dsimp only [C]
          nlinarith
    · have htauA3 : 25 / 8 ≤ tau := le_of_not_ge ha2
      by_cases ha3 : tau ≤ 7 / 2
      · have hraw := norm_pintz2023ExponentialBlock_le_A3B_power
          hN hNR hR htauA3 ha3
        have hexp := pintz_threeQuarter_A3B_exponent_le
          hsigmaUpper hsigmaLower hepsilon.le htauA3 ha3
        calc
          ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
              43 * (N : ℝ) ^ ((tau + 25) / 30) := hraw
          _ ≤ 43 * (N : ℝ) ^
              pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
          _ ≤ C * (N : ℝ) ^
              pintzNearOneUnweightedTarget sigma epsilon tau := by
            apply mul_le_mul_of_nonneg_right _ htargetNonneg
            dsimp only [C]
            nlinarith
      · have htauSeven : 7 / 2 ≤ tau := le_of_not_ge ha3
        have hep := pintz_nearOne_EP1_exponent_le
          hsigmaUpper hepsilon.le htauSeven
        by_cases hfour : tau ≤ 4
        · have hraw := hkfiveA N R tau hNPos hNR hR htauSeven hfour
          calc
            ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
                C₅ₐ * (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
            _ ≤ C₅ₐ * (N : ℝ) ^
                pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
            _ ≤ C * (N : ℝ) ^
                pintzNearOneUnweightedTarget sigma epsilon tau := by
              apply mul_le_mul_of_nonneg_right _ htargetNonneg
              dsimp only [C]
              nlinarith
        · have hfourLower : 4 ≤ tau := le_of_not_ge hfour
          by_cases hthirteen : tau ≤ 13 / 3
          · have hraw := hkfiveB N R tau hNPos hNR hR hfourLower hthirteen
            calc
              ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
                  C₅ₑ * (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
              _ ≤ C₅ₑ * (N : ℝ) ^
                  pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
              _ ≤ C * (N : ℝ) ^
                  pintzNearOneUnweightedTarget sigma epsilon tau := by
                apply mul_le_mul_of_nonneg_right _ htargetNonneg
                dsimp only [C]
                nlinarith
          · have hthirteenLower : 13 / 3 ≤ tau := le_of_not_ge hthirteen
            have hraw := hlarge N R tau hNPos hNR hR hthirteenLower
            calc
              ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
                  Cₗ * (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
              _ ≤ Cₗ * (N : ℝ) ^
                  pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
              _ ≤ C * (N : ℝ) ^
                  pintzNearOneUnweightedTarget sigma epsilon tau := by
                apply mul_le_mul_of_nonneg_right _ htargetNonneg
                dsimp only [C]
                nlinarith

#print axioms norm_pintz2023ExponentialBlock_le_threeQuarter_target

end

end GafniTao
