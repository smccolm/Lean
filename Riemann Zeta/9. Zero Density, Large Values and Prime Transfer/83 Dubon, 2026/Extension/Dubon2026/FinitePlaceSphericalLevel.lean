import Dubon2026.FinitePlaceLevel
import Dubon2026.RationalPrimePlace

/-! # Identification of the original good-prime level group with the actual integral local group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Away from the original level, the actual local level matrix condition is exactly integrality of its original entries. -/
theorem finitePlaceLevelMatrix_iff_integral (N : ℕ) (v : HeightOneSpectrum ℤ)
    (hN : (N : ℤ) ∉ v.asIdeal) (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    finitePlaceLevelMatrix N v a ↔ ∀ i j, a i j ∈ v.adicCompletionIntegers ℚ := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, (v.adicCompletionIntegers ℚ).toSubring.mul_mem
      (finitePlace_inverse_level_integral N v hN) (h 1 0)⟩

/-- At level one, the actual original local level matrix condition is precisely ordinary integrality. -/
theorem finitePlaceLevelMatrix_one_iff_integral (v : HeightOneSpectrum ℤ)
    (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    finitePlaceLevelMatrix 1 v a ↔ ∀ i j, a i j ∈ v.adicCompletionIntegers ℚ := by
  apply finitePlaceLevelMatrix_iff_integral
  exact v.isPrime.one_notMem

/-- At every original good rational prime, the local K0(N) is exactly the genuine full integral local GL2 subgroup K0(1). -/
theorem finitePlaceGL2Gamma0_good_eq_one (N p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) :
    finitePlaceGL2Gamma0 N (rationalPrimePlace p hp) = finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp) := by
  have hN : (N : ℤ) ∉ (rationalPrimePlace p hp).asIdeal := by
    rw [rationalPrimePlace_nat_mem_iff]
    exact hp.coprime_iff_not_dvd.mp hpN
  ext g
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [finitePlaceLevelMatrix_iff_integral N _ hN, finitePlaceLevelMatrix_iff_integral N _ hN,
    finitePlaceLevelMatrix_one_iff_integral, finitePlaceLevelMatrix_one_iff_integral]

/-- An actual invertible matrix over the genuine local integer ring belongs to the original full integral local group. -/
theorem finitePlaceGL2_integral_mem (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers ℚ)) :
    GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype g ∈ finitePlaceGL2Gamma0 1 v := by
  constructor
  · exact (finitePlaceLevelMatrix_one_iff_integral v _).mpr (fun i j => (g.val i j).property)
  · exact (finitePlaceLevelMatrix_one_iff_integral v _).mpr (fun i j => ((g⁻¹).val i j).property)

/-- Both original matrix and inverse integrality reconstruct a genuine GL2 matrix over the actual local integer ring. -/
def finitePlaceIntegralMatrix (v : HeightOneSpectrum ℤ) (g : finitePlaceGL2Gamma0 1 v) :
    GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers ℚ) where
  val := fun i j => ⟨g.val.val i j, g.property.1.1 i j⟩
  inv := fun i j => ⟨(g.val⁻¹).val i j, g.property.2.1 i j⟩
  val_inv := by
    funext i j
    apply Subtype.ext
    by_cases h : i = j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h] using
        congrArg (fun a => a i j) g.val.val_inv
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h] using
        congrArg (fun a => a i j) g.val.val_inv
  inv_val := by
    funext i j
    apply Subtype.ext
    by_cases h : i = j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h] using
        congrArg (fun a => a i j) g.val.inv_val
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h] using
        congrArg (fun a => a i j) g.val.inv_val

/-- The original local integer-ring matrix recovers precisely its genuine local field matrix. -/
theorem finitePlaceIntegralMatrix_map (v : HeightOneSpectrum ℤ) (g : finitePlaceGL2Gamma0 1 v) :
    GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype (finitePlaceIntegralMatrix v g) = g.val := by
  apply Units.ext
  rfl

end
end Dubon2026
