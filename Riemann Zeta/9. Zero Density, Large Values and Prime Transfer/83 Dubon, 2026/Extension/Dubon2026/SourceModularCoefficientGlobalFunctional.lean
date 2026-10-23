import Dubon2026.SourceModularCoefficientGlobalResidues
import Dubon2026.SourceModularCoefficientResidueFunctional

/-! The actual modular coefficient-field residue functional vanishes on
principal repartitions. This discharges the global premise of residue
duality and canonical degree on the DUB-17/18 reverse-genus path. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- Actual global coefficient-field functions as diagonal repartitions. -/
def coeffPrincipalAdele : modularFunctionFieldCoeff N K →ₗ[K]
    adeleSpace K (modularFunctionFieldCoeff N K) := by
  haveI := hasPrincipalDivisors_coeff_field N K
  exact (diagonalHom K (modularFunctionFieldCoeff N K)).codRestrict
    (adeleSpace K (modularFunctionFieldCoeff N K)) diagonal_mem_adeleSpace

/-- The residue functional evaluates on a principal adele by its actual global sum. -/
theorem coeffResidueFunctional_diagonal_apply
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0)
    (f : modularFunctionFieldCoeff N K) :
    coeffResidueFunctional N K hω (coeffPrincipalAdele N K f) =
      ∑ᶠ v : Place K (modularFunctionFieldCoeff N K),
        kaehlerResidueTermKFam (coeffCanonicalLocalResidueData N K) ω
          (diagonalHom K (modularFunctionFieldCoeff N K) f) v := rfl

/-- The actual residue functional annihilates every global coefficient-field function. -/
theorem coeffResidueFunctional_diagonal_zero
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0)
    (f : modularFunctionFieldCoeff N K) :
    coeffResidueFunctional N K hω (coeffPrincipalAdele N K f) = 0 := by
  rw [coeffResidueFunctional_diagonal_apply]
  exact coeff_global_residue_sum_zero N K ω f

end Dubon2026.SourceFunctionField
