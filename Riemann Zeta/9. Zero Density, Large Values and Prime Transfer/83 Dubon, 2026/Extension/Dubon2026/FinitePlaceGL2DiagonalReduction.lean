import Dubon2026.FinitePlaceGL2IntegralReduction
import Dubon2026.GL2UnitDiagonalPair
import Dubon2026.AdelicRealScalar

/-! # A genuine scalar and two integral local matrices reduce every original local GL2 element to a diagonal -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Every original local GL2 matrix is a genuine scalar times two actual integral factors around a diagonal with one and an integral nonzero entry. -/
theorem finitePlaceGL2_integral_diagonal (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ∃ u t : (v.adicCompletion ℚ)ˣ, ∃ l r : finitePlaceGL2Gamma0 1 v,
      (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ ∧
      g = GeneralLinearGroup.scalar (Fin 2) u * l.val * gl2UnitDiagonalPair 1 t * r.val := by
  obtain ⟨u, l, r, hpivot, hint⟩ := finitePlaceGL2_integral_pivot v g
  let h := GeneralLinearGroup.scalar (Fin 2) u⁻¹ * (l.val * g * r.val)
  let a := toGL (ringLowerUnipotent (h.val 1 0))
  let b := toGL (ringUpperUnipotent (h.val 0 1))
  let t := GeneralLinearGroup.det h
  have ha : a ∈ finitePlaceGL2Gamma0 1 v := finitePlace_lowerUnipotent_integral v _ (hint 1 0)
  have hb : b ∈ finitePlaceGL2Gamma0 1 v := finitePlace_upperUnipotent_integral v _ (hint 0 1)
  have ht : (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    change h.val.det ∈ v.adicCompletionIntegers ℚ
    rw [Matrix.det_fin_two]
    exact (v.adicCompletionIntegers ℚ).toSubring.sub_mem
      ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hint 0 0) (hint 1 1))
      ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hint 0 1) (hint 1 0))
  have he : h = a * gl2UnitDiagonalPair 1 t * b := by
    simpa only [inv_one, Units.val_one, mul_one] using gl2_gauss_unit_pivot h 1 hpivot
  have hr : GeneralLinearGroup.scalar (Fin 2) u * l.val⁻¹ * h * r.val⁻¹ = g := by
    rw [gl2Scalar_mul_comm u l.val⁻¹]
    simp only [h, map_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  refine ⟨u, t, ⟨l.val⁻¹ * a, (finitePlaceGL2Gamma0 1 v).mul_mem
    ((finitePlaceGL2Gamma0 1 v).inv_mem l.property) ha⟩,
    ⟨b * r.val⁻¹, (finitePlaceGL2Gamma0 1 v).mul_mem hb
      ((finitePlaceGL2Gamma0 1 v).inv_mem r.property)⟩, ht, ?_⟩
  rw [← hr, he]
  simp only [mul_assoc]

end
end Dubon2026
