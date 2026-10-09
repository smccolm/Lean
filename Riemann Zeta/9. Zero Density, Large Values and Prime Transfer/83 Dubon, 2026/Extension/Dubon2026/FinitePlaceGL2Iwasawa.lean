import Dubon2026.ValuationGL2FirstRow
import Dubon2026.FinitePlaceIntegralElementary
import Dubon2026.GeneralLinearUpperZero

/-! # The genuine local Iwasawa factorization into a lower Borel and the original integral group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Every original local GL2 matrix is the product of an actual lower-triangular invertible matrix and an original integral GL2 matrix. -/
theorem finitePlaceGL2_iwasawa (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ b : gl2UpperZeroSubgroup (v.adicCompletion ℚ), ∃ k : finitePlaceGL2Gamma0 1 v,
      g = b.val * k.val := by
  obtain ⟨j, hn, hi⟩ := valuationSubring_gl2_firstRow_pivot (v.adicCompletionIntegers ℚ) g
  let r : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) := gl2IndexSwap j
  let h := g * r
  have hp : h.val 0 0 = g.val 0 j := by
    fin_cases j <;> simp [h, r, gl2IndexSwap, gl2CoordinateSwap, Matrix.mul_apply, Fin.sum_univ_two]
  have h0 : h.val 0 0 ≠ 0 := by rw [hp]; exact hn
  have ht : h.val 0 1 / h.val 0 0 ∈ v.adicCompletionIntegers ℚ := by
    fin_cases j
    · simpa [h, r, gl2IndexSwap, Matrix.mul_apply, Fin.sum_univ_two] using hi 1
    · simpa [h, r, gl2IndexSwap, gl2CoordinateSwap, Matrix.mul_apply, Fin.sum_univ_two] using hi 0
  let u := toGL (ringUpperUnipotent (-(h.val 0 1 / h.val 0 0)))
  have hu : u ∈ finitePlaceGL2Gamma0 1 v :=
    finitePlace_upperUnipotent_integral v _ ((v.adicCompletionIntegers ℚ).toSubring.neg_mem ht)
  have hb : h * u ∈ gl2UpperZeroSubgroup (v.adicCompletion ℚ) := by
    change (h * u).val 0 1 = 0
    simp only [u, Units.val_mul, toGL, ringUpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
    change h.val 0 0 * (-(h.val 0 1 / h.val 0 0)) + h.val 0 1 * 1 = 0
    field_simp [h0]
    ring
  refine ⟨⟨h * u, hb⟩, ⟨(r * u)⁻¹, (finitePlaceGL2Gamma0 1 v).inv_mem
    ((finitePlaceGL2Gamma0 1 v).mul_mem (finitePlace_indexSwap_integral v j) hu)⟩, ?_⟩
  change g = (g * r * u) * (r * u)⁻¹
  rw [mul_assoc g r u, mul_inv_cancel_right]

end
end Dubon2026
