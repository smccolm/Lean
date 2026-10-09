import Dubon2026.GL2CoordinatePivot
import Dubon2026.FinitePlaceHeckeSwap
import Dubon2026.RingSL2Elementary

/-! # Original integral elementary matrices and coordinate swaps in the actual local level-one group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup

/-- Every actual local index permutation belongs to the genuine integral local general-linear group. -/
theorem finitePlace_indexSwap_integral (v : HeightOneSpectrum ℤ) (i : Fin 2) :
    (gl2IndexSwap i : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) ∈ finitePlaceGL2Gamma0 1 v := by
  fin_cases i
  · simpa only [gl2IndexSwap, ↓reduceIte] using (finitePlaceGL2Gamma0 1 v).one_mem
  · simpa [gl2IndexSwap] using finitePlace_coordinateSwap_integral v

/-- Original integral upper-unipotent entries and their actual inverses remain in the genuine local integral group. -/
theorem finitePlace_upperUnipotent_integral (v : HeightOneSpectrum ℤ)
    (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ) :
    toGL (ringUpperUnipotent t) ∈ finitePlaceGL2Gamma0 1 v := by
  constructor
  · apply (finitePlaceLevelMatrix_one_iff_integral v _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ringUpperUnipotent, toGL, ht]
  · apply (finitePlaceLevelMatrix_one_iff_integral v _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [ringUpperUnipotent, toGL, coe_inv, Matrix.adjugate_fin_two, ht]

/-- Original integral lower-unipotent entries and their actual inverses remain in the genuine local integral group. -/
theorem finitePlace_lowerUnipotent_integral (v : HeightOneSpectrum ℤ)
    (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ) :
    toGL (ringLowerUnipotent t) ∈ finitePlaceGL2Gamma0 1 v := by
  constructor
  · apply (finitePlaceLevelMatrix_one_iff_integral v _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ringLowerUnipotent, toGL, ht]
  · apply (finitePlaceLevelMatrix_one_iff_integral v _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [ringLowerUnipotent, toGL, coe_inv, Matrix.adjugate_fin_two, ht]

end
end Dubon2026
