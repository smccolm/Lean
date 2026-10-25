import Dubon2026.SourceReductionPrincipalDivisorCharts
import Dubon2026.SourceModularGenusIntegralCharts
import Dubon2026.SourceModularCoefficientCurve

/-! DUB-17/18 -> original arithmetic inertia -> place-map invariance.
The proved modular integral-chart lifts construct the principal-divisor
reduction map together with its exact two-chart specification. This keeps
the geometric witness required by the arithmetic comparison. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_principal_divisor_reduction_map_with_charts_of_genus_eq
    (hNk : (N : kk) ≠ 0) (hgen : genusFF kk Fb = genusFF Qbar FF) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    let R := modularRegularProlongation A N hNQ hNk
    ∃ r : Place Qbar FF → Place kk Fb,
      (∀ P Q, jCoeff N kk ∈ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoeff N Qbar) ∧ ChartReducesTo A R (jCoeff N Qbar) P Q)) ∧
      (∀ P Q, jCoeff N kk ∉ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoeff N Qbar)⁻¹ ∧ ChartReducesTo A R (jCoeff N Qbar)⁻¹ P Q)) ∧
      ∀ f : gaussRing A N, modularResidueHom A N hNQ hNk f ≠ 0 →
        ∀ D : Divisor Qbar FF, (∀ P, D P = P.ord (f : FF)) →
          ∀ Q, Finsupp.mapDomain r D Q = Q.ord (modularResidueHom A N hNQ hNk f) := by
  dsimp only
  letI hPF : HasPrincipalDivisors Qbar FF := hasPrincipalDivisors_coeff_field N Qbar
  letI hPb : HasPrincipalDivisors kk Fb := hasPrincipalDivisors_coeff_field N kk
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  let R := modularRegularProlongation A N hNQ hNk
  let x : R.integers := ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩
  have hres : R.residue x = jCoeff N kk := modularResidueHom_jCoeff A N hNQ hNk
  have hx : Transcendental kk (R.residue x) := by
    rw [hres]
    exact transcendental_jCoeff N kk
  haveI : Algebra.IsSeparable (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres]
    exact isSeparable_coeff_field N kk
  have hfin : 0 < Module.finrank (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres]
    exact (reduction_coordinate_degree A N hNQ hNk).2
  have hdeg : Module.finrank (IntermediateField.adjoin Qbar ({(x : FF)} : Set FF)) FF =
      Module.finrank (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres]
    exact (reduction_coordinate_degree A N hNQ hNk).1
  have hc := exists_principal_divisor_reduction_map_with_charts R x hx hfin hdeg (by
    rw [hres]
    exact modular_integral_charts_lift_of_genus_eq A N hNk hgen)
  simpa only [hres] using hc

end
end Dubon2026.SourceFunctionField.GaussReduction
