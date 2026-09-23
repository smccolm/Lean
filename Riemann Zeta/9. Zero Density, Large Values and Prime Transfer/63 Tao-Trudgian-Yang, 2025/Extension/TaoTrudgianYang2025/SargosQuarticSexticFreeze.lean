import TaoTrudgianYang2025.SargosQuarticParameterTransfer
import TaoTrudgianYang2025.SargosSixthStripTransfer

/-! Exact freezing of the genuine sextic correction at a parameter-rectangle corner. -/

noncomputable section

open Set GafniTao MeasureTheory
open scoped BigOperators ENNReal

namespace TaoTrudgianYang2025

def sargosQuarticFrozenSexticCoeff (c d : ℝ) (n : ℤ) : ℂ :=
  fordAdditiveCharacter (4*d^2/c*(n:ℝ)^6)

def sargosQuarticFrozenSexticPhase (c d x y t : ℝ) : ℝ :=
  4*(y^2/x-d^2/c)*t^6

theorem sargosQuarticFrozenSexticCoeff_norm (c d : ℝ) (n : ℤ) :
    ‖sargosQuarticFrozenSexticCoeff c d n‖ = 1 := by
  exact sargos_character_norm _

theorem sargosQuarticSexticPrefix_freeze (N H : ℕ) (c d x y : ℝ) :
    sargosSlowQuarticPrefix N H (fun _ => 1) x y (fun t => 4*y^2/x*t^6) =
      sargosSlowQuarticPrefix N H (sargosQuarticFrozenSexticCoeff c d) x y
        (sargosQuarticFrozenSexticPhase c d x y) := by
  unfold sargosSlowQuarticPrefix
  apply Finset.sum_congr rfl
  intro n hn
  rw [one_mul,sargosQuarticFrozenSexticCoeff,← fordAdditiveCharacter_add]
  congr 1
  unfold sargosQuarticFrozenSexticPhase
  ring

theorem sargosQuarticSexticMaximum_freeze (N : ℕ) (c d x y : ℝ) :
    sargosSlowQuarticMaximum N (fun _ => 1) x y (fun t => 4*y^2/x*t^6) =
      sargosSlowQuarticMaximum N (sargosQuarticFrozenSexticCoeff c d) x y
        (sargosQuarticFrozenSexticPhase c d x y) := by
  unfold sargosSlowQuarticMaximum
  apply Finset.sup'_congr _ rfl
  intro H hH
  rw [sargosQuarticSexticPrefix_freeze]

theorem sargosQuarticFrozenSexticPhase_deriv (c d x y t : ℝ) :
    HasDerivAt (sargosQuarticFrozenSexticPhase c d x y)
      (24*(y^2/x-d^2/c)*t^5) t := by
  convert ((hasDerivAt_id t).pow 6).const_mul (4*(y^2/x-d^2/c)) using 1
  dsimp
  ring

end TaoTrudgianYang2025
