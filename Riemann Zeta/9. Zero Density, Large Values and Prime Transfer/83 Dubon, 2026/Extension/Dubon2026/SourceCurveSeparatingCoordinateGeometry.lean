import Dubon2026.SourceCurveSeparatingLocalFinite
import Dubon2026.SourceCurveFiniteCoordinateGeometry
import Dubon2026.SourceCurveIntegralDerivatives

/-! DUB-17/18 -> original all-weight association -> homogeneous Gamma1
realization -> original genus preservation -> reverse genus -> actual residue
Hurwitz bound. Reuse the proved two-chart local finiteness and integral
derivative argument with explicit separability. This supplies local differential
generation and curve structure for the separating original residue j in every
characteristic; no inseparable-coordinate or arbitrary-extension theory is added. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]

theorem separating_coordinate_place_essFiniteType (ht : Transcendental K t)
    (v : Place K F) : Algebra.EssFiniteType K v.toValuationSubring := by
  rcases v.toValuationSubring.mem_or_inv_mem t with hv | hv
  · exact essFiniteType_place_of_separating_coordinate t ht v hv
  · have hti : Transcendental K t⁻¹ := fun h => ht (IsAlgebraic.inv_iff.mp h)
    haveI : FiniteDimensional K⟮t⁻¹⟯ F := by rw [adjoin_singleton_inv_eq]; infer_instance
    haveI : Algebra.IsSeparable K⟮t⁻¹⟯ F := by rw [adjoin_singleton_inv_eq]; infer_instance
    exact essFiniteType_place_of_separating_coordinate t⁻¹ hti v hv

theorem separating_coordinate_place_differentials (ht : Transcendental K t)
    (v : Place K F) : Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] := by
  letI := separating_coordinate_place_essFiniteType t ht v
  exact KaehlerDifferential.finite K v.toValuationSubring

theorem separating_coordinate_place_dCoordGenerates [IsAlgClosed K]
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) (v : Place K F) :
    v.DCoordGenerates := by
  letI := separating_coordinate_place_differentials t ht v
  letI := finite_coordinate_place_residue t v
  letI : Algebra.IsSeparable K v.ResidueField := inferInstance
  have hD : v.dCoord ≠ 0 := by
    intro hz
    have hzero : ∀ f : F, f ∈ v.toValuationSubring → D K F f = 0 := by
      intro f hf
      obtain ⟨g, _, hg⟩ := v.exists_integral_D_eq_smul_dCoord hf
      rw [hg, hz, smul_zero]
    rcases v.toValuationSubring.mem_or_inv_mem t with hv | hv
    · exact hDt (hzero _ hv)
    · have hi := hzero _ hv
      rw [Derivation.leibniz_inv] at hi
      have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
      exact hDt ((smul_eq_zero.mp hi).resolve_left
        (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero ht0))))
  exact ⟨(finrank_eq_one_iff_of_nonzero _ hD).mp
    ((finrank_eq_one_iff_of_nonzero _ hDt).mpr
      (SourceDifferential.span_D_eq_top_of_transcendental K t ht))⟩

theorem isCurveOver_separating_coordinate [IsAlgClosed K]
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) : IsCurveOver K F where
  toHasPrincipalDivisors := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  finiteResidue := finite_coordinate_place_residue t
  kaehler_free_rank_one := ⟨inferInstance,
    (finrank_eq_one_iff_of_nonzero _ hDt).mpr
      (SourceDifferential.span_D_eq_top_of_transcendental K t ht)⟩

end
end Dubon2026.SourceCurve
