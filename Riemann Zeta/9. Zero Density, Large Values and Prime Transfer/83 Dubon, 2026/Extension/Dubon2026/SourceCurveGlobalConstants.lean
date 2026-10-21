import Dubon2026.SourceCurveRiemannRochSpace
import Dubon2026.SourceCurveTranscendentalDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> regular differential dimension -> finite Riemann--Roch
spaces. Global regular functions are algebraic: otherwise the proved degree
formula applied to their inverse supplies a pole. Over closed constants this
identifies L(0) with the actual base field, without an additional place
existence or rational-point hypothesis.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

theorem isAlgebraic_of_forall_ord_nonneg
    (hfinite : ∀ t : F, Transcendental K t → FiniteDimensional K⟮t⟯ F)
    {f : F} (hf : ∀ v : Place K F, 0 ≤ v.ord f) : IsAlgebraic K f := by
  by_contra ht
  have hti : Transcendental K f⁻¹ := fun hi => ht (IsAlgebraic.inv_iff.mp hi)
  haveI : FiniteDimensional K⟮f⁻¹⟯ F := hfinite f⁻¹ hti
  haveI : IsEmpty {v : Place K F // 0 < v.ord f⁻¹} := ⟨by
    rintro ⟨v, hv⟩
    rw [v.ord_inv] at hv
    have := hf v
    omega⟩
  have h := sum_positive_orders_eq_finrank_adjoin f⁻¹ hti
  simp only [finsum_of_isEmpty] at h
  have hp : 0 < Module.finrank K⟮f⁻¹⟯ F := Module.finrank_pos
  omega

theorem lSpace_zero_eq_range [IsAlgClosed K]
    (hfinite : ∀ t : F, Transcendental K t → FiniteDimensional K⟮t⟯ F) :
    LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := by
  ext f
  constructor
  · intro hf
    have ha : IsAlgebraic K f := by
      apply isAlgebraic_of_forall_ord_nonneg hfinite
      rcases mem_lSpace_iff_ord.mp hf with rfl | hf
      · intro v
        rw [v.ord_zero]
      · simpa only [Finsupp.zero_apply, neg_zero] using hf
    haveI : Algebra.IsAlgebraic K K⟮f⟯ := isAlgebraic_adjoin_simple ha.isIntegral
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := K) (K := K⟮f⟯)).surjective
      (⟨f, mem_adjoin_simple_self K f⟩ : K⟮f⟯)
    exact ⟨c, congrArg (fun x : K⟮f⟯ => (x : F)) hc⟩
  · rintro ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

theorem finite_lSpace_zero [IsAlgClosed K]
    (hfinite : ∀ t : F, Transcendental K t → FiniteDimensional K⟮t⟯ F) :
    Module.Finite K (LSpace (0 : Divisor K F)) := by
  rw [lSpace_zero_eq_range hfinite]
  infer_instance

theorem finrank_lSpace_zero [IsAlgClosed K]
    (hfinite : ∀ t : F, Transcendental K t → FiniteDimensional K⟮t⟯ F) :
    Module.finrank K (LSpace (0 : Divisor K F)) = 1 := by
  rw [lSpace_zero_eq_range hfinite, LinearMap.finrank_range_of_inj
    (f := Algebra.linearMap K F) (algebraMap K F).injective, Module.finrank_self]

end
end Dubon2026.SourceCurve
