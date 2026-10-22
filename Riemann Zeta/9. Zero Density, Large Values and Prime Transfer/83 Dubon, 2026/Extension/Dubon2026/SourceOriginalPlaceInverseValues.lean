import Dubon2026.SourceOriginalPlaceEvaluation

/-! DUB-17/18 -> original torsion cardinality -> original complex charts
-> meromorphic values for functions with poles. The literal convention
assigns zero both at a pole and to the inverse of a zero. Evaluation thus
commutes with inversion. At units this follows from the actual residue
homomorphism, and at zeros/poles from the proved order criterion. This
extends the regular chart comparison to every original rational function.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem originalPlaceEval_inv (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (v : Place L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver N L) :
    originalPlaceEval N L v f⁻¹ = (originalPlaceEval N L v f)⁻¹ := by
  classical
  by_cases hf0 : f = 0
  · subst f
    have hz : originalPlaceEval N L v 0 = 0 := by
      simpa only [map_zero] using originalPlaceEval_algebraMap N L v 0
    rw [inv_zero, hz, inv_zero]
  by_cases hf : f ∈ v.toValuationSubring
  · by_cases hfi : f⁻¹ ∈ v.toValuationSubring
    · have hp : originalPlaceEval N L v f * originalPlaceEval N L v f⁻¹ = 1 := by
        rw [originalPlaceEval_of_mem N L v hf, originalPlaceEval_of_mem N L v hfi, ← map_mul]
        have he : (⟨f, hf⟩ : v.toValuationSubring) * ⟨f⁻¹, hfi⟩ = 1 :=
          Subtype.ext (mul_inv_cancel₀ hf0)
        rw [he, map_one]
      exact (inv_eq_of_mul_eq_one_right hp).symm
    · have ho : 0 < v.ord f := by
        rw [v.mem_iff_ord_nonneg, v.ord_inv] at hfi
        omega
      have hz := (originalPlaceEval_eq_zero_iff_ord_pos N L v hf hf0).mpr ho
      have hi : originalPlaceEval N L v f⁻¹ = 0 := by
        simp only [originalPlaceEval, dif_neg hfi]
      rw [hi, hz, inv_zero]
  · have hfi : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have ho : 0 < v.ord f⁻¹ := by
      rw [v.mem_iff_ord_nonneg] at hf
      rw [v.ord_inv]
      omega
    have hi := (originalPlaceEval_eq_zero_iff_ord_pos N L v hfi (inv_ne_zero hf0)).mpr ho
    have hz : originalPlaceEval N L v f = 0 := by
      simp only [originalPlaceEval, dif_neg hf]
    rw [hi, hz, inv_zero]

end
end Dubon2026.SourceFunctionField
