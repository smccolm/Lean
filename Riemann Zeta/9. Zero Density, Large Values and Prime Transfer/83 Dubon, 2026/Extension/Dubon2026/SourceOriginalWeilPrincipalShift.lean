import Dubon2026.SourceOriginalWeilEvaluationPowers
import Dubon2026.SourceOriginalWeilTorsionValues

/-! DUB-17/18 -> original Weil pairing descent -> invariance under
a principal shift of the first divisor. Actual proved reciprocity supplies
the cancellation factor. Adapted from WeilDatum.pairing_eq_of_addPrincipalLeft,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilDatum
noncomputable section
open SourceCurve
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable {n : ℕ}

theorem pairing_eq_of_addPrincipalLeft (d d' : OriginalWeilDatum N L n)
    {E : Divisor L (modularFunctionFieldOver N L)} {h : modularFunctionFieldOver N L}
    (hh : h ≠ 0) (hE : ∀ v : Place L (modularFunctionFieldOver N L), E v = v.ord h)
    (hD₁ : d'.D₁ = d.D₁ + E) (hD₂ : d'.D₂ = d.D₂)
    (hf₁ : d'.f₁ = d.f₁ * h ^ n) (hf₂ : d'.f₂ = d.f₂) :
    d'.pairing = d.pairing := by
  classical
  have hE0 (v : Place L (modularFunctionFieldOver N L)) (hv : d.D₂ v ≠ 0) : E v = 0 := by
    have h1 := (d.disjoint v).resolve_right hv
    have h2 := (d'.disjoint v).resolve_right (by rwa [hD₂])
    rw [hD₁, Finsupp.add_apply, h1, zero_add] at h2
    exact h2
  have hordh (v : Place L (modularFunctionFieldOver N L)) (hv : v ∈ d.D₂.support) :
      v.ord h = 0 := (hE v).symm.trans (hE0 v (Finsupp.mem_support_iff.mp hv))
  have hordf₂E (v : Place L (modularFunctionFieldOver N L)) (hv : v ∈ E.support) :
      v.ord d.f₂ = 0 := by
    have hz : d.D₂ v = 0 := by
      by_contra he
      exact Finsupp.mem_support_iff.mp hv (hE0 v he)
    rw [d.ord_f₂, hz, mul_zero]
  have hnum : originalDivisorEval N L d'.f₁ d'.D₂ =
      originalDivisorEval N L d.f₁ d.D₂ * originalDivisorEval N L h d.D₂ ^ n := by
    rw [hf₁, hD₂, originalDivisorEval_mul N L _ _ _ (fun v hv => by
      apply v.mem_of_ord_nonneg
      rw [d.ord_f₁, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero])
      (fun v hv => pow_mem (v.mem_of_ord_nonneg (hordh v hv).ge) n),
      originalDivisorEval_pow N L h d.D₂ (fun v hv => v.mem_of_ord_nonneg (hordh v hv).ge)]
  have hdiv : originalPrincipalDivisor N L h = E := by
    ext v
    exact (hE v).symm
  have hrecip : originalDivisorEval N L h d.D₂ ^ n = originalDivisorEval N L d.f₂ E := by
    have hr := original_weil_reciprocity L N h d.f₂ hh d.f₂_ne_zero (fun v hv => by
      apply hordf₂E v
      exact Finsupp.mem_support_iff.mpr (by rwa [hE v]))
    rwa [d.principalDivisor_second, hdiv, originalDivisorEval_nsmul] at hr
  have hden : originalDivisorEval N L d'.f₂ d'.D₁ =
      originalDivisorEval N L d.f₂ d.D₁ * originalDivisorEval N L d.f₂ E := by
    rw [hf₂, hD₁]
    apply originalDivisorEval_add
    intro v hv
    apply originalPlaceEval_ne_zero_of_ord_eq_zero N L v d.f₂_ne_zero
    rcases hv with hv | hv
    · rw [d.ord_f₂, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]
    · exact hordf₂E v hv
  have hne := originalDivisorEval_ne_zero N L d.f₂ d.f₂_ne_zero E hordf₂E
  change originalDivisorEval N L d'.f₁ d'.D₂ / originalDivisorEval N L d'.f₂ d'.D₁ = _
  rw [hnum, hrecip, hden, mul_div_mul_right _ _ hne]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalWeilDatum
