import Dubon2026.SourceCurveRationalResidueValues
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> cover chart compatibility -> actual residue-value field laws.
Reuse the original inversion and uniformizer-decomposition proofs for the
existing rational evaluation. Its zero-at-poles convention is preserved. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]
variable (v : Place ℂ E) (hv : Function.Bijective (algebraMap ℂ v.ResidueField))

theorem rationalEval_zero : v.rationalEval hv 0 = 0 := by
  simpa only [map_zero] using v.rationalEval_algebraMap hv 0

theorem rationalEval_inv (f : E) : v.rationalEval hv f⁻¹ = (v.rationalEval hv f)⁻¹ := by
  classical
  by_cases hf0 : f = 0
  · subst f
    have hz : v.rationalEval hv 0 = 0 := by
      simpa only [map_zero] using v.rationalEval_algebraMap hv 0
    rw [inv_zero, hz, inv_zero]
  by_cases hf : f ∈ v.toValuationSubring
  · by_cases hfi : f⁻¹ ∈ v.toValuationSubring
    · have hp : v.rationalEval hv f * v.rationalEval hv f⁻¹ = 1 := by
        rw [v.rationalEval_of_mem hv hf, v.rationalEval_of_mem hv hfi, ← map_mul]
        have he : (⟨f, hf⟩ : v.toValuationSubring) * ⟨f⁻¹, hfi⟩ = 1 :=
          Subtype.ext (mul_inv_cancel₀ hf0)
        rw [he, map_one]
      exact (inv_eq_of_mul_eq_one_right hp).symm
    · have ho : 0 < v.ord f := by
        rw [v.mem_iff_ord_nonneg, v.ord_inv] at hfi
        omega
      have hz := (v.rationalEval_eq_zero_iff_ord_pos hv hf hf0).mpr ho
      have hi : v.rationalEval hv f⁻¹ = 0 := by
        simp only [Place.rationalEval, dif_neg hfi]
      rw [hi, hz, inv_zero]
  · have hfi : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have ho : 0 < v.ord f⁻¹ := by
      rw [v.mem_iff_ord_nonneg] at hf
      rw [v.ord_inv]
      omega
    have hi := (v.rationalEval_eq_zero_iff_ord_pos hv hfi (inv_ne_zero hf0)).mpr ho
    have hz : v.rationalEval hv f = 0 := by
      simp only [Place.rationalEval, dif_neg hf]
    rw [hi, hz, inv_zero]


theorem rationalEval_decomp {t f : E}
    (ht : t ∈ v.toValuationSubring) (hf : f ∈ v.toValuationSubring) (c z : ℂ) :
    v.rationalEval hv (algebraMap ℂ E c + (t - algebraMap ℂ E z) * f) =
      c + (v.rationalEval hv t - z) * v.rationalEval hv f := by
  rw [v.rationalEval_of_mem hv
    (add_mem (v.algebraMap_mem' c) (mul_mem (sub_mem ht (v.algebraMap_mem' z)) hf)),
    v.rationalEval_of_mem hv ht, v.rationalEval_of_mem hv hf]
  change v.rationalRegularEval hv
    (algebraMap ℂ v.toValuationSubring c +
      (⟨t, ht⟩ - algebraMap ℂ v.toValuationSubring z) * ⟨f, hf⟩) = _
  rw [map_add, map_mul, map_sub, rationalRegularEval_algebraMap,
    rationalRegularEval_algebraMap]

end
end Dubon2026.SourceCurve.Place
