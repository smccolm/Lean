import Dubon2026.SourceCurveIntegralDifferentialOrders
import Dubon2026.SourceCurveFiniteCoordinateGeometry

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison. Consume the
two exact integral expressions to prove regularity of y D(j). Keeping this
valuation calculation over the abstract actual function field avoids
unfolding its Laurent presentation in every local differential instance. -/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]

theorem regular_smul_D_of_two_integral_expressions
    (j y : F) [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    (hD : D K F j ≠ 0) (M : ℕ) [NeZero M]
    (hfinite : IsIntegral (Algebra.adjoin K ({j} : Set F))
      (y ^ 6 * j ^ 4 * (j - algebraMap K F 1728) ^ 3))
    (hcusp : IsIntegral (Algebra.adjoin K ({j⁻¹} : Set F))
      (y ^ (2 * M) * j ^ (M + 1) * (j - algebraMap K F 1728) ^ M)) :
    y • D K F j ∈ regularDifferentials K F := by
  by_cases hy : y = 0
  · rw [hy, zero_smul]; exact Submodule.zero_mem _
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hD
  apply mem_regularDifferentials_iff.mpr
  intro v
  letI := finite_coordinate_place_dCoordGenerates j v
  letI := finite_coordinate_place_differentials j v
  letI := finite_coordinate_place_residue j v
  letI : Algebra.IsSeparable K v.ResidueField := inferInstance
  have ho : 0 ≤ v.ordDifferential (y • D K F j) := by
    by_cases hv : v.ord j < 0
    · have hc := v.cusp_coefficient_order_of_integral_expression M j y hy hv hcusp
      rw [v.ordDifferential_smul hy
        (RegularDifferentialsComparison.differentialCoeff_ne_zero hD v),
        v.ordDifferential_D_eq_ord_sub_one (ne_of_lt hv)]
      omega
    · apply v.ordDifferential_nonneg_of_finite_expression y j (by norm_num : (1728 : K) ≠ 0)
      exact v.ord_nonneg_of_integral_coordinate (le_of_not_gt hv) hfinite
  exact ⟨v.differentialCoeff (y • D K F j), v.mem_of_ord_nonneg ho,
    (v.differentialCoeff_smul_dCoord _).symm⟩

end
end Dubon2026.SourceCurve
