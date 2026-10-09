import Dubon2026.ValuationGL2Pivot
import Dubon2026.FinitePlaceIntegralElementary

/-! # Scaling and integral coordinate permutations give an actual integral matrix with first pivot one -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original scalar matrix multiplies each actual general-linear matrix entry by its genuine unit. -/
theorem gl2Scalar_mul_entry {R : Type*} [CommRing R] (u : Rˣ)
    (g : GeneralLinearGroup (Fin 2) R) (i j : Fin 2) :
    (GeneralLinearGroup.scalar (Fin 2) u * g).val i j = (u : R) * g.val i j := by
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.scalar, Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every original local invertible matrix becomes integral with first pivot exactly one after a genuine scalar and two original integral coordinate permutations. -/
theorem finitePlaceGL2_integral_pivot (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ u : (v.adicCompletion ℚ)ˣ, ∃ l r : finitePlaceGL2Gamma0 1 v,
      (GeneralLinearGroup.scalar (Fin 2) u⁻¹ * (l.val * g * r.val)).val 0 0 = 1 ∧
      ∀ i j : Fin 2, (GeneralLinearGroup.scalar (Fin 2) u⁻¹ * (l.val * g * r.val)).val i j ∈
        v.adicCompletionIntegers ℚ := by
  obtain ⟨i, j, hn, hi⟩ := valuationSubring_gl2_pivot (v.adicCompletionIntegers ℚ) g
  let u : (v.adicCompletion ℚ)ˣ := Units.mk0 (g.val i j) hn
  refine ⟨u, ⟨gl2IndexSwap i, finitePlace_indexSwap_integral v i⟩,
    ⟨gl2IndexSwap j, finitePlace_indexSwap_integral v j⟩, ?_, ?_⟩
  · rw [gl2Scalar_mul_entry, gl2IndexSwap_pivot]
    exact inv_mul_cancel₀ hn
  · intro a b
    rw [gl2Scalar_mul_entry]
    obtain ⟨c, d, he⟩ := gl2IndexSwap_entry g i j a b
    rw [he]
    change (g.val i j)⁻¹ * g.val c d ∈ v.adicCompletionIntegers ℚ
    rw [mul_comm, ← div_eq_mul_inv]
    exact hi c d

end
end Dubon2026
