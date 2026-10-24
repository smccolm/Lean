import Dubon2026.SourceCurveConstantReductionR2
import Dubon2026.SourceModularGenusPrincipalDivisorMap

/-! DUB-17/18 -> modular good reduction and invertible Picard torsion.
The actual modular principal-divisor map and closed place residues construct a constant reduction under the narrower genus-equality hypothesis.
The actual characteristic-three consumer discharges genus equality;
characteristic two and the later arithmetic chain remain required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_constant_reduction_of_genus_eq
    (hNk : (N : kk) ≠ 0) (hgen : genusFF kk Fb = genusFF Qbar FF) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧ genusFF kk Fb = genusFF Qbar FF := by
  dsimp only
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  letI hFdim : FiniteDimensional (IntermediateField.adjoin Qbar {jCoeff N Qbar}) FF :=
    finiteDimensional_coeff_field N Qbar
  letI hFbdim : FiniteDimensional (IntermediateField.adjoin kk {jCoeff N kk}) Fb :=
    finiteDimensional_coeff_field N kk
  obtain ⟨r, hr⟩ := exists_modular_principal_divisor_reduction_map_of_genus_eq A N hNk hgen
  let R : ConstantReduction A FF Fb := ConstantReduction.ofPlaceMap
    (modularRegularProlongation A N hNQ hNk) r
    (fun P => place_residue_bijective_of_finite_coordinate (jCoeff N Qbar) P)
    (fun Q => place_residue_bijective_of_finite_coordinate (jCoeff N kk) Q) hr
  refine ⟨R, rfl, ?_⟩
  change genusFF kk Fb = genusFF Qbar FF
  exact hgen

end
end Dubon2026.SourceFunctionField.GaussReduction
