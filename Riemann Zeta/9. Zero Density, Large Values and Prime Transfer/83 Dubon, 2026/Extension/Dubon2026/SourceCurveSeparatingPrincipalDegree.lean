import Dubon2026.SourceCurveSeparatingCoordinateDegree
import Dubon2026.SourceCurveSeparatingFunctionSupport
import Dubon2026.SourceCurvePrincipalDegree

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
rational-function base of Galois descent. A separating coordinate has
degree-zero literal orders in any characteristic: its zero and pole
degrees are the equal degrees of the same rational subfield. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem sum_orders_eq_zero_of_separating_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F]
    [Algebra.IsSeparable K⟮t⟯ F] :
    (∑ᶠ v : Place K F, v.ord t * (Module.finrank K v.ResidueField : ℤ)) = 0 := by
  have hti : Transcendental K t⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
  haveI : FiniteDimensional K⟮t⁻¹⟯ F := by rw [adjoin_singleton_inv_eq]; infer_instance
  haveI : Algebra.IsSeparable K⟮t⁻¹⟯ F := by rw [adjoin_singleton_inv_eq]; infer_instance
  rw [sum_orders_eq_positive_sub_inverse t (finite_function_support_of_separating_coordinate t ht t),
    sum_positive_orders_eq_finrank_separating t ht,
    sum_positive_orders_eq_finrank_separating t⁻¹ hti, adjoin_singleton_inv_eq, sub_self]

end
end Dubon2026.SourceCurve
