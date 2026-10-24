import Dubon2026.SourceReductionChartPlaceUniqueness
import Dubon2026.SourceModularTameIntegralCharts

/-! DUB-17/18 -> original Frobenius/inertia -> modular good reduction ->
actual reduction places. At every original place with integral j-value,
the actual arithmetic Gauss reduction determines one unique residue place
compatible with every integral j-chart function. The tame genus and chart
lifting theorems supply surjectivity; original modular field results supply
transcendence, finite separability and degree equality. No place or chart
certificate remains assumed. The inverse chart, global assembly and the
principal-divisor pushforward identity remain subsequent obligations. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem existsUnique_modular_j_chart_place_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0)
    (P : Place Qbar FF)
    (hP : ∃ a : A, jCoeff N Qbar - algebraMap Qbar FF a ∈ P.toValuationSubring.nonunits) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃! Q : Place kk Fb,
      ∀ f : gaussRing A N, IsIntegral (Algebra.adjoin Qbar {jCoeff N Qbar}) (f : FF) →
        ∀ a : A, (f : FF) - algebraMap Qbar FF a ∈ P.toValuationSubring.nonunits →
          modularResidueHom A N hNQ hNk f - algebraMap kk Fb (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits := by
  dsimp only
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
  apply RegularProlongation.existsUnique_reduction_chart_place R x hx hfin hdeg ?_ P hP
  intro g hg
  rw [hres] at hg
  exact (modular_integral_charts_lift_of_five_le A N p hp hNk).1 g hg

end
end Dubon2026.SourceFunctionField.GaussReduction
