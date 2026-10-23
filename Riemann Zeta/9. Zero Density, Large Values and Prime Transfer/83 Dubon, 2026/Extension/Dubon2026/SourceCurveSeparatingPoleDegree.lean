import Dubon2026.SourceCurveSeparatingCoordinateDegree
import Dubon2026.SourceCurvePoleDivisor

/-! DUB-17/18 -> good reduction -> residue genus. The existing separating
coordinate degree formula computes the actual pole divisor in every
characteristic and supplies a place. No separability of arbitrary function
coordinates is needed. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_poleDivisor_eq_finrank_separating (t : F) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]
    (hf : {v : Place K F | v.ord t ≠ 0}.Finite) :
    Divisor.degree (poleDivisor t hf) = (Module.finrank K⟮t⟯ F : ℤ) := by
  have hti : Transcendental K t⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
  haveI : FiniteDimensional K⟮t⁻¹⟯ F := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  haveI : Algebra.IsSeparable K⟮t⁻¹⟯ F := by
    rw [adjoin_singleton_inv_eq]
    infer_instance
  rw [degree_poleDivisor_eq_positive_inverse,
    sum_positive_orders_eq_finrank_separating t⁻¹ hti, adjoin_singleton_inv_eq]

theorem nonempty_place_of_separating_coordinate (t : F) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Nonempty (Place K F) := by
  by_contra hn
  haveI : IsEmpty (Place K F) := not_nonempty_iff.mp hn
  have h := sum_positive_orders_eq_finrank_separating t ht
  simp only [finsum_of_isEmpty] at h
  have hp : 0 < Module.finrank K⟮t⟯ F := Module.finrank_pos
  omega

end
end Dubon2026.SourceCurve
