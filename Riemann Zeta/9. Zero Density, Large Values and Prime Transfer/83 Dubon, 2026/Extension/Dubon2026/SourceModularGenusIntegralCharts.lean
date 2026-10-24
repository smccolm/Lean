import Dubon2026.SourceModularIntegralChartLifting
import Dubon2026.SourceModularReductionSourceGenus

/-! DUB-17/18 -> modular good reduction and invertible Picard torsion.
Both actual modular integral charts lift under the narrower genus-equality hypothesis. The original proved chart-lifting theorems supply the lifts in every characteristic.
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

theorem modular_integral_charts_lift_of_genus_eq
    (hNk : (N : kk) ≠ 0) (hgen : genusFF kk Fb = genusFF Qbar FF) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    (∀ g : Fb, IsIntegral (Algebra.adjoin kk {jCoeff N kk}) g →
      ∃ f : gaussRing A N, IsIntegral (Algebra.adjoin Qbar {jCoeff N Qbar}) (f : FF) ∧
        modularResidueHom A N hNQ hNk f = g) ∧
    (∀ g : Fb, IsIntegral (Algebra.adjoin kk {(jCoeff N kk)⁻¹}) g →
      ∃ f : gaussRing A N, IsIntegral (Algebra.adjoin Qbar {(jCoeff N Qbar)⁻¹}) (f : FF) ∧
        modularResidueHom A N hNQ hNk f = g) := by
  exact ⟨fun g hg => exists_modular_integral_j_lift_of_genus_eq A N _ hNk hgen g hg,
    fun g hg => exists_modular_integral_inverse_j_lift_of_genus_eq A N _ hNk hgen g hg⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
