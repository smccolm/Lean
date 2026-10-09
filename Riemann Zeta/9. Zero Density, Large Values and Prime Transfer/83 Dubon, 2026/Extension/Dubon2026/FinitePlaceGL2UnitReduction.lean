import Dubon2026.FinitePlaceGL2DiagonalReduction

/-! # Exact determinant diagonal when the original integral matrix has a genuine unit pivot -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- An actual integral local matrix with a genuine integral-unit first pivot is in the exact integral double coset of the original determinant diagonal. -/
theorem finitePlaceGL2_unit_pivot_diagonal (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hint : ∀ i j, g.val i j ∈ v.adicCompletionIntegers ℚ)
    (a : (v.adicCompletionIntegers ℚ)ˣ) (ha : g.val 0 0 = (a.val : v.adicCompletion ℚ)) :
    ∃ l r : finitePlaceGL2Gamma0 1 v,
      g = l.val * gl2UnitDiagonalPair 1 (GeneralLinearGroup.det g) * r.val := by
  let u := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom a
  have huinv : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := (a⁻¹).val.property
  let L := toGL (ringLowerUnipotent (g.val 1 0 * ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)))
  let U := toGL (ringUpperUnipotent (g.val 0 1 * ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)))
  let B := GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype (gl2UnitDiagonalPair a a⁻¹)
  have hL : L ∈ finitePlaceGL2Gamma0 1 v := finitePlace_lowerUnipotent_integral v _
    ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hint 1 0) huinv)
  have hU : U ∈ finitePlaceGL2Gamma0 1 v := finitePlace_upperUnipotent_integral v _
    ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hint 0 1) huinv)
  have hB : B ∈ finitePlaceGL2Gamma0 1 v := finitePlaceGL2_integral_mem v _
  have he : gl2UnitDiagonalPair u (GeneralLinearGroup.det g * u⁻¹) =
      B * gl2UnitDiagonalPair 1 (GeneralLinearGroup.det g) := by
    dsimp only [B]
    rw [gl2UnitDiagonalPair_map, map_inv, gl2UnitDiagonalPair_mul, mul_one]
    congr 1
    exact mul_comm _ _
  refine ⟨⟨L * B, (finitePlaceGL2Gamma0 1 v).mul_mem hL hB⟩, ⟨U, hU⟩, ?_⟩
  have hg := gl2_gauss_unit_pivot g u ha
  rw [he] at hg
  simpa only [L, U, mul_assoc] using hg

end
end Dubon2026
