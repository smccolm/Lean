import Dubon2026.SourceReductionMonicEquation
import Dubon2026.SourceCurveChartIntegralCriterion
import Dubon2026.SourceCurveRiemannRochSpace

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison -> preservation of pole spaces. The already proved original
chart-integrality criterion turns a pole bound into integrality on both the
coordinate and inverse-coordinate charts. Characteristic zero is required
only for the original constants in this reused criterion; the residue field
remains unrestricted. This avoids a general valuation-extension argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
variable {L F : Type*} [Field L] [Field F] [Algebra L F] [CharZero L]

theorem integral_charts_of_pole_bound (x : F) (hx : Transcendental L x)
    [FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F]
    (D : Divisor L F) (hD : ∀ v, D v = max 0 (-v.ord x)) (m : ℕ)
    {f : F} (hf : f ∈ LSpace (m • D)) :
    IsIntegral (Algebra.adjoin L ({x} : Set F)) f ∧
      IsIntegral (Algebra.adjoin L ({x⁻¹} : Set F)) (f * (x ^ m)⁻¹) := by
  by_cases hf0 : f = 0
  · subst f
    simpa only [zero_mul] using
      (And.intro (isIntegral_zero : IsIntegral (Algebra.adjoin L ({x} : Set F)) (0 : F))
        (isIntegral_zero : IsIntegral (Algebra.adjoin L ({x⁻¹} : Set F)) (0 : F)))
  have hford := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hxi : Transcendental L x⁻¹ := fun h => hx (IsAlgebraic.inv_iff.mp h)
  have heq : IntermediateField.adjoin L ({x⁻¹} : Set F) =
      IntermediateField.adjoin L ({x} : Set F) := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      exact Set.singleton_subset_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self L x))
    · apply IntermediateField.adjoin_le_iff.mpr
      apply Set.singleton_subset_iff.mpr
      simpa only [inv_inv] using inv_mem (IntermediateField.mem_adjoin_simple_self L x⁻¹)
  haveI : FiniteDimensional (IntermediateField.adjoin L ({x⁻¹} : Set F)) F := by
    rw [heq]
    infer_instance
  constructor
  · apply isIntegral_adjoin_of_nonnegative_orders x hx f
    intro v hv
    have h := hford v
    simpa only [Finsupp.smul_apply, nsmul_eq_mul, hD, max_eq_left (neg_nonpos.mpr hv),
      mul_zero, neg_zero] using h
  · apply isIntegral_adjoin_of_nonnegative_orders x⁻¹ hxi (f * (x ^ m)⁻¹)
    intro v hv
    rw [v.ord_inv] at hv
    have h := hford v
    simp only [Finsupp.smul_apply, nsmul_eq_mul, hD, max_eq_right hv] at h
    rw [v.ord_mul hf0 (inv_ne_zero (pow_ne_zero m hx0)), v.ord_inv,
      ← zpow_natCast, v.ord_zpow]
    linarith

end
end Dubon2026.SourceCurve.RegularProlongation
