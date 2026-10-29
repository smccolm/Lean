import Dubon2026.SourceGammaOneGenusSpecialization
import Dubon2026.SourceReductionPrincipalDivisorCharts

/-! DUB-17/18 -> original Gamma1 Picard inertia -> exact specialization
charts. Retain the two chart descriptions from the existing native gluing
theorem. Coordinate-degree and actual adelic-genus equality remain explicit;
the new information is the chart specification needed for arithmetic transport. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
  (hT : ModularGroup.T ∈ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Γ Qbar
local notation "Fb" => residueImage A Γ

include hT

theorem exists_principal_reduction_map_with_charts_of_degree_genus_eq
    (hdeg : Module.finrank (IntermediateField.adjoin Qbar {jCoordinateOver Γ Qbar}) FF =
      Module.finrank (IntermediateField.adjoin kk {residueJCoordinate A Γ}) Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF) :
    ∃ r : Place Qbar FF → Place kk Fb,
      (∀ P Q, residueJCoordinate A Γ ∈ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoordinateOver Γ Qbar) ∧
          ChartReducesTo A (regularProlongation A Γ) (jCoordinateOver Γ Qbar) P Q)) ∧
      (∀ P Q, residueJCoordinate A Γ ∉ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoordinateOver Γ Qbar)⁻¹ ∧
          ChartReducesTo A (regularProlongation A Γ) (jCoordinateOver Γ Qbar)⁻¹ P Q)) ∧
      ∀ f : coefficientGaussRing Γ A, residueToImage A Γ f ≠ 0 →
        ∀ D : Divisor Qbar FF, (∀ P, D P = P.ord (f : FF)) →
          ∀ Q, Finsupp.mapDomain r D Q = Q.ord (residueToImage A Γ f) := by
  haveI := valuation_residue_isAlgClosed A
  haveI := functionFieldOver_isCurveOver Γ Qbar hT
  haveI := residueImage_isCurveOver A Γ hT
  let R := regularProlongation A Γ
  let x : R.integers := ⟨jCoordinateOver Γ Qbar, jCoordinateOver_mem_gaussRing A Γ⟩
  have hres : R.residue x = residueJCoordinate A Γ := regularProlongation_jCoordinateOver A Γ
  have hx : Transcendental kk (R.residue x) := by
    rw [hres]
    exact transcendental_residueJCoordinate A Γ
  have hdim : FiniteDimensional (IntermediateField.adjoin kk {R.residue x}) Fb := by
    rw [hres]
    exact (finite_residueCoordinate_and_degree_le A Γ hT).1
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin kk {R.residue x}) Fb := by
    rw [hres]
    exact isSeparable_residueCoordinate A Γ hT
  have hdegx : Module.finrank (IntermediateField.adjoin Qbar {(x : FF)}) FF =
      Module.finrank (IntermediateField.adjoin kk {R.residue x}) Fb := by
    rw [hres]
    exact hdeg
  have hfin : 0 < Module.finrank (IntermediateField.adjoin kk {R.residue x}) Fb := by
    haveI := hdim
    exact Module.finrank_pos
  have hcharts := @integral_charts_lift_of_degree_genus_eq
    Qbar _ _ _ A FF _ _ Fb _ _ R x hx hdim hsep hdegx hgen
  have hc := @exists_principal_divisor_reduction_map_with_charts
    Qbar _ _ _ A FF _ _ _ Fb _ _ _ R x hx hsep hfin hdegx hcharts
  simpa only [hres] using hc

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
