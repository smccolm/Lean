import Dubon2026.SourceModularCharTwoGenusLower
import Dubon2026.SourceOriginalArithmeticGenus
import Dubon2026.SourceModularReductionSourceGenus

/-! Actual characteristic-two genus preservation for modular Gauss
reduction. The lower wild bound, upper reduction bound and numerical
genus identity are proved inputs. This removes the characteristic-two
genus premise from the DUB-17/18 good-reduction dependency chain. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_residue_genusFF_eq_originalGenus_of_char_two
    [CharP kk 2] (hNk : (N : kk) ≠ 0) :
    genusFF kk (modularFunctionFieldCoeff N kk) = originalGenus N Qbar := by
  apply le_antisymm (modular_residue_genusFF_le_originalGenus A N hNk)
  have h := coeff_genus_lower_of_char_two N kk hNk
  rw [← originalGenus_arithmetic_eq_genusFormula N] at h
  exact_mod_cast h

end
end Dubon2026.SourceFunctionField.GaussReduction
