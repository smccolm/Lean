import Dubon2026.SourceReductionChartGluing
import Dubon2026.SourceModularTameInverseChartPlace

/-! DUB-17/18 -> original Frobenius/inertia -> modular good reduction ->
global reduction-place comparison. The two actual tame modular chart-place
theorems give a map on every original arithmetic place, with the precise
finite-j and infinite-j fiber descriptions required by the source
principal-divisor formula. Chart coverage, overlap compatibility and
uniqueness are derived. No place map or chart comparison is assumed.
The principal-divisor identity and wild-characteristic comparison remain
required before modular good reduction is complete. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_reduction_place_map_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    let R := modularRegularProlongation A N hNQ hNk
    ∃ r : Place Qbar FF → Place kk Fb,
      (∀ P Q, jCoeff N kk ∈ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoeff N Qbar) ∧
          ChartReducesTo A R (jCoeff N Qbar) P Q)) ∧
      (∀ P Q, jCoeff N kk ∉ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoeff N Qbar)⁻¹ ∧
          ChartReducesTo A R (jCoeff N Qbar)⁻¹ P Q)) := by
  dsimp only
  let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  let R := modularRegularProlongation A N hNQ hNk
  let x : gaussRing A N := ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩
  have hx : R.residue x = jCoeff N kk := modularResidueHom_jCoeff A N hNQ hNk
  have hx0 : R.residue x ≠ 0 := hx.trans_ne
    (fun h => transcendental_jCoeff N kk (h ▸ isAlgebraic_zero))
  have hxu : IsUnit x := R.isUnit_of_residue_ne_zero (f := x) hx0
  obtain ⟨u, hu⟩ := hxu
  let xi : gaussRing A N := ↑u⁻¹
  have hxiF : (xi : FF) = (x : FF)⁻¹ := by
    change (gaussRing A N).subtype ↑u⁻¹ = _
    rw [map_units_inv, hu]
    rfl
  have hxires : R.residue xi = (R.residue x)⁻¹ := by
    change modularResidueHom A N hNQ hNk (↑u⁻¹ : gaussRing A N) = _
    rw [map_units_inv, hu]
    rfl
  haveI := finiteDimensional_coeff_field N Qbar
  have hres (P : Place Qbar FF) : Function.Surjective (algebraMap Qbar P.ResidueField) :=
    (place_residue_bijective_of_finite_coordinate (jCoeff N Qbar) P).surjective
  have E₁ : ∀ P : Place Qbar FF, ChartDomain A P (x : FF) →
      ∃! Q, ChartReducesTo A R (x : FF) P Q := by
    intro P hP
    exact existsUnique_modular_j_chart_place_of_five_le A N p hp hNk P hP
  have E₂ : ∀ P : Place Qbar FF, ChartDomain A P (xi : FF) →
      ∃! Q, ChartReducesTo A R (xi : FF) P Q := by
    rw [hxiF]
    intro P hP
    exact existsUnique_modular_inverse_j_chart_place_of_five_le A N p hp hNk P hP
  obtain ⟨r, hr₁, hr₂⟩ := exists_reduction_place_map_of_two_charts R x xi hx0 hxiF hxires hres E₁ E₂
  rw [hx] at hr₁ hr₂
  rw [hxiF] at hr₂
  exact ⟨r, hr₁, hr₂⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
