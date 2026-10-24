import Dubon2026.SourceJointChartUniformResidues
import Dubon2026.SourceModularKummerJointChartSpacesR2
import Dubon2026.SourceJointChartDimensionAssembly
import Dubon2026.SourceJointChartWeightedSpans
import Dubon2026.SourceModularCoordinateChartGeneration
import Dubon2026.SourceModularKummerRegularReductionsR2
import Dubon2026.SourceCurveFiniteCoordinateExtension
import Dubon2026.SourceModularCoefficientGlobalSpaces

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality. The actual modular Kummer reductions satisfy the
eventual two-chart dimension inequality. Their exact degree, coordinate
separability and finite pole spaces discharge the generic chart assumptions.
The common residue-chart constants and the genus inequality remain to prove. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
open SourceCurve.RegularProlongation.JointChartAssembly
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual coefficient algebra on the modular residue field. -/
local instance jointDimensionCoreResidueModularAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- Closed residue constants for the arithmetic coefficient valuation. -/
local instance jointDimensionCoreResidueClosed : IsAlgClosed kk := valuation_residue_isAlgClosed A

theorem joint_chart_dimension_of_coordinate_degree
    (q : ℕ) [NeZero q] (E : Type*) [Field E] [Algebra Qbar E]
    (S : Fin q → RegularProlongation A E Fbar)
    (hSinj : Function.Injective fun i => (S i).integers)
    (t : E) (ht : ∀ i, t ∈ (S i).integers)
    (hres : ∀ i, (S i).residue ⟨t, ht i⟩ = jCoeff N kk)
    (htotal : Module.finrank (IntermediateField.adjoin Qbar ({t} : Set E)) E =
      Module.finrank (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar * q)
    (ht0 : t ≠ 0)
    (hpos : 0 < Module.finrank (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional kk ↥(modularJointChart A N q S t ⊓
        modularJointWeightedChart A N q S t M) ∧
      Module.finrank kk ↥(modularJointChart A N q S t ⊓
        modularJointWeightedChart A N q S t M) + q ≤
      q * Module.finrank kk ↥(LSpace (M • modularJPole N kk)) +
        Module.finrank kk ↥(modularJointChart A N q S t ⊓
          modularJointChart A N q S t⁻¹) := by
  classical
  letI : FiniteDimensional (IntermediateField.adjoin Qbar ({t} : Set E)) E :=
    Module.finite_of_finrank_pos (by rw [htotal]; exact Nat.mul_pos hpos (Nat.pos_of_ne_zero (NeZero.ne q)))
  letI : Module.Free (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar :=
    Module.Free.of_divisionRing _ _
  letI : FiniteDimensional (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hpos
  letI (D : Divisor kk Fbar) : FiniteDimensional kk ↥(LSpace D) := finite_coeff_lSpace N kk D
  let D' : Divisor kk Fbar := poleDivisor (jCoeff N kk)⁻¹
    (finite_coeff_divisor_support N kk (jCoeff N kk)⁻¹)
  have heq : Fintype.card (Fin q) * Module.finrank
      (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar =
      Module.finrank (IntermediateField.adjoin Qbar ({t} : Set E)) E := by
    rw [Fintype.card_fin, htotal, Nat.mul_comm]
  have h := @eventual_uniform_residue_chart_dimension Qbar E inferInstance A inferInstance
    inferInstance (Fin q) inferInstance (Fbar : Type) inferInstance
    (modularFunctionFieldCoeff N kk).toSubalgebra.algebra
    S hSinj t ht ht0 inferInstance (jCoeff N kk) (transcendental_jCoeff N kk) hres
    inferInstance (fun D => finite_coeff_lSpace N kk D) heq (modularJPole N kk) D'
    (modularJPole_apply N kk) (fun _ => max_comm _ _)
    (modular_j_chart_generating_window N kk) (modular_inverse_j_chart_generating_window N kk)
  simpa only [Fintype.card_fin] using h


end
end Dubon2026.SourceFunctionField.GaussReduction
