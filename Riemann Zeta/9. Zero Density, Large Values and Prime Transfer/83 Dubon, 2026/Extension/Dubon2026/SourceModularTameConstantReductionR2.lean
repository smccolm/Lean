import Dubon2026.SourceCurveConstantReductionR2
import Dubon2026.SourceModularTamePrincipalDivisorMap

/-! DUB-17/18 -> original Frobenius/inertia -> actual modular good reduction.
The proved arithmetic Gauss residue map, actual principal-divisor place map,
closed place residues and genus equality construct the source constant-
reduction object and prove its good-reduction condition in characteristic
at least five. The full wild-characteristic cases remain required.
This supplies the real upstream object for Picard and torsion reduction. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_constant_reduction_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧ genusFF kk Fb = genusFF Qbar FF := by
  dsimp only
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  letI hFdim : FiniteDimensional (IntermediateField.adjoin Qbar {jCoeff N Qbar}) FF :=
    finiteDimensional_coeff_field N Qbar
  letI hFbdim : FiniteDimensional (IntermediateField.adjoin kk {jCoeff N kk}) Fb :=
    finiteDimensional_coeff_field N kk
  obtain ⟨r, hr⟩ := exists_modular_principal_divisor_reduction_map_of_five_le A N p hp hNk
  let R : ConstantReduction A FF Fb := ConstantReduction.ofPlaceMap
    (modularRegularProlongation A N hNQ hNk) r
    (fun P => place_residue_bijective_of_finite_coordinate (jCoeff N Qbar) P)
    (fun Q => place_residue_bijective_of_finite_coordinate (jCoeff N kk) Q) hr
  refine ⟨R, rfl, ?_⟩
  change genusFF kk Fb = genusFF Qbar FF
  exact (modular_residue_genusFF_eq_originalGenus_of_five_le A N p hp hNk).trans
    (coefficient_genusFF_eq_originalGenus N).symm

end
end Dubon2026.SourceFunctionField.GaussReduction
