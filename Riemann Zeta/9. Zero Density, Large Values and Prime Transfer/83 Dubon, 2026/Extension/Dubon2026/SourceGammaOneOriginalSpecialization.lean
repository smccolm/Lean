import Dubon2026.SourceGammaOneGenusSpecialization

/-! DUB-17/18 -> original Gamma1 Tate Frobenius/inertia -> original Picard
specialization. Consume the place-map construction at the literal Gamma1
subgroup. Finite index and translation membership are discharged here.
Only the actual coordinate-degree and adelic-genus comparisons remain. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A

theorem exists_gammaOne_constant_reduction_of_degree_genus_eq
    (hdeg : Module.finrank
      (IntermediateField.adjoin Qbar {jCoordinateOver Δ Qbar}) (functionFieldOver Δ Qbar) =
      Module.finrank (IntermediateField.adjoin kk {residueJCoordinate A Δ}) (residueImage A Δ))
    (hgen : genusFF kk (residueImage A Δ) = genusFF Qbar (functionFieldOver Δ Qbar)) :
    ∃ R : ConstantReduction A (functionFieldOver Δ Qbar) (residueImage A Δ),
      R.toRegularProlongation = regularProlongation A Δ := by
  exact exists_constant_reduction_of_degree_genus_eq A Δ
    (by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]) hdeg hgen

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
