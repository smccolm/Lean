import Dubon2026.SourceModularTameChartPlace

/-! DUB-17/18 -> original Frobenius/inertia -> modular good reduction ->
actual reduction places. The inverse-j chart has the same unique place
comparison. The original j is a Gauss unit because its residue is
transcendental. Its inverse gives the literal second reduction coordinate;
existing modular finite separability and degree equality apply unchanged.
Global compatibility, principal-divisor pushforward and wild characteristics
remain required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem existsUnique_modular_inverse_j_chart_place_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0)
    (P : Place Qbar FF)
    (hP : ∃ a : A, (jCoeff N Qbar)⁻¹ - algebraMap Qbar FF a ∈ P.toValuationSubring.nonunits) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃! Q : Place kk Fb,
      ∀ f : gaussRing A N, IsIntegral (Algebra.adjoin Qbar {(jCoeff N Qbar)⁻¹}) (f : FF) →
        ∀ a : A, (f : FF) - algebraMap Qbar FF a ∈ P.toValuationSubring.nonunits →
          modularResidueHom A N hNQ hNk f - algebraMap kk Fb (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits := by
  dsimp only
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  let R := modularRegularProlongation A N hNQ hNk
  let J : gaussRing A N := ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩
  have hJ : R.residue J = jCoeff N kk := modularResidueHom_jCoeff A N hNQ hNk
  have hjb : jCoeff N kk ≠ 0 := fun h => transcendental_jCoeff N kk (h ▸ isAlgebraic_zero)
  have hJU : IsUnit J := R.isUnit_of_residue_ne_zero (f := J) (hJ.trans_ne hjb)
  obtain ⟨u, hu⟩ := hJU
  let x : gaussRing A N := ↑u⁻¹
  have hxF : (x : FF) = (jCoeff N Qbar)⁻¹ := by
    change (gaussRing A N).subtype ↑u⁻¹ = _
    rw [map_units_inv, hu]
    rfl
  have hres : R.residue x = (jCoeff N kk)⁻¹ := by
    change modularResidueHom A N hNQ hNk (↑u⁻¹ : gaussRing A N) = _
    rw [map_units_inv, hu]
    exact congrArg Inv.inv hJ
  have hx : Transcendental kk (R.residue x) := by
    rw [hres]
    exact fun h => transcendental_jCoeff N kk (IsAlgebraic.inv_iff.mp h)
  haveI : Algebra.IsSeparable (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres, adjoin_singleton_inv_eq]
    exact isSeparable_coeff_field N kk
  have hfin : 0 < Module.finrank (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hres, adjoin_singleton_inv_eq]
    exact (reduction_coordinate_degree A N hNQ hNk).2
  have hdeg : Module.finrank (IntermediateField.adjoin Qbar ({(x : FF)} : Set FF)) FF =
      Module.finrank (IntermediateField.adjoin kk ({R.residue x} : Set Fb)) Fb := by
    rw [hxF, hres, adjoin_singleton_inv_eq, adjoin_singleton_inv_eq]
    exact (reduction_coordinate_degree A N hNQ hNk).1
  have hchart : ∀ g : Fb, IsIntegral (Algebra.adjoin kk {R.residue x}) g →
      ∃ f : R.integers, IsIntegral (Algebra.adjoin Qbar {(x : FF)}) (f : FF) ∧ R.residue f = g := by
    intro g hg
    rw [hres] at hg
    rw [hxF]
    exact (modular_integral_charts_lift_of_five_le A N p hp hNk).2 g hg
  have hPx : ∃ a : A, (x : FF) - algebraMap Qbar FF a ∈ P.toValuationSubring.nonunits := by
    rwa [hxF]
  have H := RegularProlongation.existsUnique_reduction_chart_place R x hx hfin hdeg hchart P hPx
  rw [hxF] at H
  exact H

end
end Dubon2026.SourceFunctionField.GaussReduction
