import Dubon2026.SourceCurveRationalFunctionEvaluation

/-! DUB-17/18 -> original Weil reciprocity -> rational-coordinate case.
The existing original residue arguments apply to the same actual rational
residue evaluation on a finite rational-field extension. These value identities
serve evaluation at zero and infinity in the coordinate reciprocity formula. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) (hv : Function.Bijective (algebraMap K v.ResidueField))

theorem rationalEval_sub_algebraMap {f : F} (hf : f ∈ v.toValuationSubring) (c : K) :
    v.rationalEval hv (f - algebraMap K F c) = v.rationalEval hv f - c := by
  rw [rationalEval_of_mem v hv (sub_mem hf (v.algebraMap_mem' c)),
    rationalEval_of_mem v hv hf]
  change v.rationalRegularEval hv (⟨f, hf⟩ - algebraMap K v.toValuationSubring c) = _
  rw [map_sub, rationalRegularEval_algebraMap]

theorem rationalEval_eq_zero_iff_ord_pos {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    v.rationalEval hv f = 0 ↔ 0 < v.ord f := by
  rw [rationalEval_of_mem v hv hf]
  change (RingEquiv.ofBijective (algebraMap K v.ResidueField) hv).symm
    (residue v.toValuationSubring ⟨f, hf⟩) = 0 ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.ofBijective (algebraMap K v.ResidueField) hv).symm.injective,
    residue_eq_zero_iff, v.mem_maximalIdeal_iff_ord_pos hf0 hf]

theorem rationalEval_eq_of_ord_sub_pos (f : F) (c : K)
    (h : 0 < v.ord (f - algebraMap K F c)) : v.rationalEval hv f = c := by
  have hm := v.mem_of_ord_nonneg h.le
  have hf : f ∈ v.toValuationSubring := by
    simpa only [sub_add_cancel] using add_mem hm (v.algebraMap_mem' c)
  have hn : f - algebraMap K F c ≠ 0 := by
    intro he
    rw [he, v.ord_zero] at h
    exact (lt_irrefl 0) h
  have hz := (v.rationalEval_eq_zero_iff_ord_pos hv hm hn).mpr h
  rw [rationalEval_sub_algebraMap v hv hf] at hz
  exact sub_eq_zero.mp hz

theorem rationalEval_div_of_ord_eq_zero {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg0 : g ≠ 0) (hg : v.ord g = 0) :
    v.rationalEval hv (f / g) = v.rationalEval hv f / v.rationalEval hv g := by
  have hm := v.mem_of_ord_nonneg hg.ge
  have hi : g⁻¹ ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg (by rw [v.ord_inv, hg, neg_zero])
  have hp : v.rationalRegularEval hv ⟨g, hm⟩ *
      v.rationalRegularEval hv ⟨g⁻¹, hi⟩ = 1 := by
    rw [← map_mul]
    have he : (⟨g, hm⟩ : v.toValuationSubring) * ⟨g⁻¹, hi⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hg0)
    rw [he, map_one]
  rw [div_eq_mul_inv, rationalEval_of_mem v hv (mul_mem hf hi),
    rationalEval_of_mem v hv hf, rationalEval_of_mem v hv hm, div_eq_mul_inv]
  change v.rationalRegularEval hv (⟨f, hf⟩ * ⟨g⁻¹, hi⟩) = _
  rw [map_mul, (inv_eq_of_mul_eq_one_right hp).symm]

end
end Dubon2026.SourceCurve.Place
