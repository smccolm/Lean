import Dubon2026.FinitePlaceLevel

/-! # Exact removal of one original finite-place coordinate -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Remove the genuine v-coordinate from the original finite adelic matrix by its actual one-place embedding. -/
def finiteAdelicPlaceRemoval (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  (finiteAdelicLocalGL2 v (GeneralLinearGroup.map (finiteAdelePlace v) a))⁻¹ * a

/-- The removed original coordinate is exactly the identity. -/
theorem finiteAdelicPlaceRemoval_same (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicPlaceRemoval v a) = 1 := by
  rw [finiteAdelicPlaceRemoval, map_mul, map_inv, finiteAdelicLocalGL2_same, inv_mul_cancel]

/-- Every other original local coordinate survives the removal unchanged. -/
theorem finiteAdelicPlaceRemoval_ne (v w : HeightOneSpectrum ℤ) (h : w ≠ v)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    GeneralLinearGroup.map (finiteAdelePlace w) (finiteAdelicPlaceRemoval v a) =
      GeneralLinearGroup.map (finiteAdelePlace w) a := by
  rw [finiteAdelicPlaceRemoval, map_mul, map_inv, finiteAdelicLocalGL2_ne v w h, inv_one, one_mul]

/-- The literal original finite adelic matrix factors as its actual single-place part times the genuine remaining coordinates. -/
theorem finiteAdelicLocal_mul_removal (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    finiteAdelicLocalGL2 v (GeneralLinearGroup.map (finiteAdelePlace v) a) *
      finiteAdelicPlaceRemoval v a = a := by
  rw [finiteAdelicPlaceRemoval, mul_inv_cancel_left]

/-- If the original matrix is in the genuine level group away from one place, its actual remaining-coordinate factor is in the original full level group. -/
theorem finiteAdelicPlaceRemoval_mem_level (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (ha : ∀ w, w ≠ v → GeneralLinearGroup.map (finiteAdelePlace w) a ∈ finitePlaceGL2Gamma0 N w) :
    finiteAdelicPlaceRemoval v a ∈ finiteAdeleGL2Gamma0 N := by
  apply (finiteAdeleGL2Gamma0_iff_places N _).mpr
  intro w
  by_cases h : w = v
  · subst w
    rw [finiteAdelicPlaceRemoval_same]
    exact (finitePlaceGL2Gamma0 N v).one_mem
  · rw [finiteAdelicPlaceRemoval_ne v w h]
    exact ha w h

end
end Dubon2026
