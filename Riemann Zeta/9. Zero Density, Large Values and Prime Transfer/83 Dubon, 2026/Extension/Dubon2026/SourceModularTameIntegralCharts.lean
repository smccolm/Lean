import Dubon2026.SourceModularIntegralChartLifting
import Dubon2026.SourceModularTameResidueGenus

/-! DUB-17/18 -> modular good reduction -> integral-chart comparison.
The proved tame genus equality discharges the last premise in both chart
lifting theorems for the actual arithmetic Gauss valuation. Every function
integral over either residue j chart has an integral lift over that same
original chart. Wild characteristics and the place-map assembly remain open. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_integral_charts_lift_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    (∀ g : Fb, IsIntegral (Algebra.adjoin kk {jCoeff N kk}) g →
      ∃ f : gaussRing A N, IsIntegral (Algebra.adjoin Qbar {jCoeff N Qbar}) (f : FF) ∧
        modularResidueHom A N hNQ hNk f = g) ∧
    (∀ g : Fb, IsIntegral (Algebra.adjoin kk {(jCoeff N kk)⁻¹}) g →
      ∃ f : gaussRing A N, IsIntegral (Algebra.adjoin Qbar {(jCoeff N Qbar)⁻¹}) (f : FF) ∧
        modularResidueHom A N hNQ hNk f = g) := by
  have hgen : genusFF kk Fb = genusFF Qbar FF :=
    (modular_residue_genusFF_eq_originalGenus_of_five_le A N p hp hNk).trans
      (coefficient_genusFF_eq_originalGenus N).symm
  exact ⟨fun g hg => exists_modular_integral_j_lift_of_genus_eq A N _ hNk hgen g hg,
    fun g hg => exists_modular_integral_inverse_j_lift_of_genus_eq A N _ hNk hgen g hg⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
