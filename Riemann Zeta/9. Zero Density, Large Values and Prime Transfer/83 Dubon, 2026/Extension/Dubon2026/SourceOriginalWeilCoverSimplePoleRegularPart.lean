import Dubon2026.SourceOriginalWeilCoverDifferentialResidues
import Dubon2026.SourceOriginalWeilCoverReadFieldLaws
import Dubon2026.SourceCurveRationalResidueValues

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)

theorem cover_simple_pole_regular_part (v : Place ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (c : ℂ)
    (hc : v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = c) :
    v.differentialCoeff η - algebraMap ℂ EE c * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
  let a := v.uniformizer * v.differentialCoeff η - algebraMap ℂ EE c
  have ha : a ∈ v.toValuationSubring :=
    sub_mem ((cover_simple_pole_bound_iff N n radicand v η).mp hη) (v.algebraMap_mem' c)
  have hzero : v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) a = 0 := by
    rw [v.rationalEval_sub_algebraMap (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      ((cover_simple_pole_bound_iff N n radicand v η).mp hη), hc, sub_self]
  have he : v.differentialCoeff η - algebraMap ℂ EE c * v.uniformizer⁻¹ = a * v.uniformizer⁻¹ := by
    dsimp [a]
    field_simp [v.uniformizer_ne_zero]
  rw [he]
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul]
    exact zero_mem _
  · have hp := (v.rationalEval_eq_zero_iff_ord_pos (originalWeilKummerCover_residue_bijective N ℂ n radicand v) ha ha0).mp hzero
    apply v.mem_of_ord_nonneg
    rw [v.ord_mul ha0 (inv_ne_zero v.uniformizer_ne_zero), v.ord_inv, v.ord_uniformizer]
    omega


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
