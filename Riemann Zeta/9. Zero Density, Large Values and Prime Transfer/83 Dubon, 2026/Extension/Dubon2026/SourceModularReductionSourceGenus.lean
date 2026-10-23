import Dubon2026.SourceModularReductionGenusBound
import Dubon2026.SourceCurveRepartitionIndex
import Dubon2026.SourceResidueOriginalSpecialization
import Dubon2026.SourceOriginalRiemannRoch

/-! DUB-17/18 -> actual modular good reduction -> genus comparison.
The proved index inequality is transported through the literal source H1
quotient, and the original coefficient field is identified with the existing
arithmetic modular field and its canonical genus. These are proved bridges,
not a new convention for genus. The reverse inequality and place comparison
remain open. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_residue_genusFF_le (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0) :
    genusFF kk (modularFunctionFieldCoeff N kk) ≤ genusFF L (modularFunctionFieldCoeff N L) := by
  haveI := hasPrincipalDivisors_coeff_field N L
  calc
    genusFF kk (modularFunctionFieldCoeff N kk) =
      indexOfSpecialty (0 : Divisor kk (modularFunctionFieldCoeff N kk)) :=
        @genusFF_eq_zero_index kk (modularFunctionFieldCoeff N kk) _ _ _
          (hasPrincipalDivisors_coeff_field N kk)
    _ ≤ indexOfSpecialty (0 : Divisor L (modularFunctionFieldCoeff N L)) :=
      modular_residue_index_zero_le A N hNL hNk
    _ = genusFF L (modularFunctionFieldCoeff N L) := genusFF_eq_zero_index.symm

omit [CharZero L] in
theorem coefficient_genusFF_eq_originalGenus [Algebra ℚ L] :
    genusFF L (modularFunctionFieldCoeff N L) = originalGenus N L := by
  haveI := hasPrincipalDivisors_original N L
  rw [← original_field_eq_coefficient_field N L, genusFF_eq_zero_index,
    ← originalGenus_eq_zero_index]

theorem modular_residue_genusFF_le_originalGenus [Algebra ℚ L] (hNk : (N : kk) ≠ 0) :
    genusFF kk (modularFunctionFieldCoeff N kk) ≤ originalGenus N L := by
  rw [← coefficient_genusFF_eq_originalGenus N]
  exact modular_residue_genusFF_le A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk

end
end Dubon2026.SourceFunctionField.GaussReduction
