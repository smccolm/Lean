import Dubon2026.SourceCurveFilteredOrders
import Dubon2026.SourceCurveSeparatingPoleDegree
import Dubon2026.SourceCurveSeparatingFunctionSupport
import Dubon2026.SourceCurveFiniteCoordinateResidues
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
total chart orders of normalized coordinate factors. The existing separating
coordinate pole-degree formula computes this total directly. Finite-coordinate
residue bijectivity removes residue-degree weights. No auxiliary place,
constant-field certificate or Riemann--Roch dimension premise is needed. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped Classical
open IntermediateField

theorem chartOrderSum_sub_algebraMap
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] (t : F) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] (β : K)
    (I : Place K F → Prop) (hI₁ : ∀ P, I P → t ∈ P.toValuationSubring)
    (hI₂ : ∀ P, 0 < P.ord (t - algebraMap K F β) → I P) :
    chartOrderSum I (t - algebraMap K F β) = (Module.finrank K⟮t⟯ F : ℤ) := by
  set s : F := t - algebraMap K F β with hs
  have hs_tr : Transcendental K s := by
    intro h
    apply ht
    have := h.add (isAlgebraic_algebraMap (A := F) β)
    simpa [hs] using this
  have hy : Transcendental K s⁻¹ := fun h => hs_tr (IsAlgebraic.inv_iff.mp h)
  have hadj : K⟮s⁻¹⟯ = K⟮t⟯ := by
    apply le_antisymm
    · rw [adjoin_simple_le_iff]
      exact inv_mem (sub_mem (mem_adjoin_simple_self K t) (IntermediateField.algebraMap_mem _ β))
    · rw [adjoin_simple_le_iff]
      have h1 : s ∈ K⟮s⁻¹⟯ := by
        have := inv_mem (mem_adjoin_simple_self K s⁻¹)
        rwa [inv_inv] at this
      have h2 : t = s + algebraMap K F β := by simp [hs]
      rw [h2]
      exact add_mem h1 (IntermediateField.algebraMap_mem _ β)
  haveI : FiniteDimensional K⟮s⁻¹⟯ F := by rw [hadj]; infer_instance
  haveI : Algebra.IsSeparable K⟮s⁻¹⟯ F := by rw [hadj]; infer_instance
  have hf : {v : Place K F | v.ord s⁻¹ ≠ 0}.Finite :=
    finite_function_support_of_separating_coordinate t ht s⁻¹
  let D : Divisor K F := (principalOrderDivisor K s).filter I
  have hDeq : D = poleDivisor s⁻¹ hf := by
    ext P
    rw [poleDivisor_apply, P.ord_inv, neg_neg]
    change ((principalOrderDivisor K s).filter I) P = _
    rw [Finsupp.filter_apply, principalOrderDivisor_apply]
    by_cases hIP : I P
    · rw [if_pos hIP, max_eq_left (P.ord_nonneg_of_mem
        (sub_mem (hI₁ P hIP) (P.algebraMap_mem' β)))]
    · rw [if_neg hIP, max_eq_right (not_lt.mp fun h => hIP (hI₂ P h))]
  have hr (P : Place K F) : Module.finrank K P.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (place_residue_bijective_of_finite_coordinate t P)
  have hsum : Divisor.degree D = chartOrderSum I s := by
    rw [Divisor.degree_eq_sum_support]
    simp only [hr, Nat.cast_one, mul_one]
    change (∑ P ∈ ((principalOrderDivisor K s).filter I).support,
      ((principalOrderDivisor K s).filter I) P) = _
    rw [Finsupp.support_filter]
    unfold chartOrderSum
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hP).2, principalOrderDivisor_apply]
  rw [← hsum, hDeq, degree_poleDivisor_eq_finrank_separating s⁻¹ hy hf, hadj]

end
end Dubon2026.SourceCurve
