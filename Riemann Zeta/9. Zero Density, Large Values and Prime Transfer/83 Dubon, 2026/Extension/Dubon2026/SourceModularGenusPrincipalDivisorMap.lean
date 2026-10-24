import Dubon2026.SourceReductionPrincipalDivisorMap
import Dubon2026.SourceModularGenusIntegralCharts
import Dubon2026.SourceModularCoefficientCurve

/-! DUB-17/18 -> modular good reduction and invertible Picard torsion.
Both actual integral chart lifts construct a global modular reduction-place map whose literal pushforward preserves every principal divisor. Only genus equality remains explicit.
The actual characteristic-three consumer discharges genus equality;
characteristic two and the later arithmetic chain remain required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_principal_divisor_reduction_map_of_genus_eq
    (hNk : (N : kk) ≠ 0) (hgen : genusFF kk Fb = genusFF Qbar FF) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ r : Place Qbar FF → Place kk Fb,
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
  apply exists_principal_divisor_reduction_map R x hx hfin hdeg
  rw [hres]
  exact modular_integral_charts_lift_of_genus_eq A N hNk hgen

end
end Dubon2026.SourceFunctionField.GaussReduction
