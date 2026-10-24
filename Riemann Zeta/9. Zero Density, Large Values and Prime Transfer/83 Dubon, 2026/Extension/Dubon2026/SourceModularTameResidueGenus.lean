import Dubon2026.SourceOriginalArithmeticGenus
import Dubon2026.SourceModularCoefficientGenusLowerFive
import Dubon2026.SourceModularReductionSourceGenus

/-! DUB-17/18 -> modular good reduction -> genus equality. The actual
Gauss residue field over an arithmetic valuation has the same adelic genus
as the original arithmetic modular field whenever its characteristic is at
least five and the level is nonzero. The upper reduction bound, lower
exceptional-fiber bound and arithmetic numerical genus are all derived.
Wild characteristics and the required place comparison remain separate. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_residue_genusFF_eq_originalGenus_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    genusFF kk (modularFunctionFieldCoeff N kk) = originalGenus N Qbar := by
  apply le_antisymm (modular_residue_genusFF_le_originalGenus A N hNk)
  have h := coeff_genus_lower_of_five_le N kk p hp hNk
  rw [← originalGenus_arithmetic_eq_genusFormula N] at h
  exact_mod_cast h

end
end Dubon2026.SourceFunctionField.GaussReduction
