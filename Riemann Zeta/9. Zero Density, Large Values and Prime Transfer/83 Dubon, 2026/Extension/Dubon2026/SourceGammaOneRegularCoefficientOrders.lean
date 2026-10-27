import Mathlib.Analysis.Complex.Polynomial.Basic
import Dubon2026.SourceGammaOneCurveGeometry
import Dubon2026.SourceCurveExactDerivativeOrder
import Dubon2026.SourceCurveRegularComparison

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> cancellation
of analytic branching. Regularity of x D(j) gives its exact coefficient
order bound at any place where j-c has nonzero order. All local differential
and residue prerequisites are derived from the existing actual field. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve KaehlerDifferential
open scoped MatrixGroups

theorem regular_coefficient_order_bound
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (x : functionFieldOver Γ ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (functionFieldOver Γ ℂ) (jCoordinateOver Γ ℂ) ∈
      regularDifferentials ℂ (functionFieldOver Γ ℂ))
    (v : Place ℂ (functionFieldOver Γ ℂ)) (c : ℂ)
    (hc : v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c) ≠ 0) :
    1 - v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c) ≤ v.ord x := by
  letI := functionFieldOver_dCoordGenerates Γ ℂ hT v
  letI := functionFieldOver_localDifferentials Γ ℂ hT v
  letI := finiteDimensional_jCoordinateOver hT ℂ
  letI := finite_coordinate_place_residue (jCoordinateOver Γ ℂ) v
  letI : Algebra.IsSeparable ℂ v.ResidueField := inferInstance
  have hDj := D_jCoordinateOver_ne_zero Γ ℂ
  letI : Nontrivial Ω[functionFieldOver Γ ℂ⁄ℂ] := nontrivial_of_ne _ _ hDj
  have hcoeff := RegularDifferentialsComparison.differentialCoeff_ne_zero hDj v
  obtain ⟨a, ha, he⟩ := (mem_regularDifferentials_iff.mp hreg) v
  have hr : 0 ≤ v.ordDifferential (x • D ℂ (functionFieldOver Γ ℂ) (jCoordinateOver Γ ℂ)) := by
    change 0 ≤ v.ord (v.differentialCoeff _)
    rw [v.differentialCoeff_unique he]
    exact v.ord_nonneg_of_mem ha
  rw [v.ordDifferential_smul hx hcoeff] at hr
  have hD : D ℂ (functionFieldOver Γ ℂ)
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c) =
        D ℂ (functionFieldOver Γ ℂ) (jCoordinateOver Γ ℂ) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have ho := v.ordDifferential_D_eq_ord_sub_one hc
  rw [hD] at ho
  omega

end
end Dubon2026.SourceFunctionField.GammaOne
