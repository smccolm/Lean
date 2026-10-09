import Dubon2026.FiniteAdelicCoordinateRestriction

/-! # Genuine coordinate restriction homomorphisms and complementary finite adelic factors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable (S : Set (HeightOneSpectrum ℤ))

/-- Retaining any actual place set preserves the genuine identity matrix. -/
theorem finiteAdelicGL2On_one : finiteAdelicGL2On S 1 = 1 := by
  apply finiteAdelicGL2_ext
  intro v
  by_cases hv : v ∈ S
  · rw [finiteAdelicGL2On_mem S _ v hv, map_one]
  · rw [finiteAdelicGL2On_not_mem S _ v hv, map_one]

/-- Coordinate restriction preserves actual finite adelic matrix multiplication. -/
theorem finiteAdelicGL2On_mul (g h : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    finiteAdelicGL2On S (g * h) = finiteAdelicGL2On S g * finiteAdelicGL2On S h := by
  apply finiteAdelicGL2_ext
  intro v
  rw [map_mul]
  by_cases hv : v ∈ S
  · rw [finiteAdelicGL2On_mem S _ v hv, finiteAdelicGL2On_mem S _ v hv, finiteAdelicGL2On_mem S _ v hv, map_mul]
  · rw [finiteAdelicGL2On_not_mem S _ v hv, finiteAdelicGL2On_not_mem S _ v hv,
      finiteAdelicGL2On_not_mem S _ v hv, one_mul]

/-- Actual coordinate restriction is a genuine finite adelic group homomorphism. -/
def finiteAdelicGL2OnHom : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →*
    GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) where
  toFun := finiteAdelicGL2On S
  map_one' := finiteAdelicGL2On_one S
  map_mul' := finiteAdelicGL2On_mul S

/-- The original finite adelic matrix is exactly the product of its actual complementary coordinate restrictions. -/
theorem finiteAdelicGL2On_mul_compl (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    finiteAdelicGL2On S g * finiteAdelicGL2On Sᶜ g = g := by
  apply finiteAdelicGL2_ext
  intro v
  rw [map_mul]
  by_cases hv : v ∈ S
  · rw [finiteAdelicGL2On_mem S _ v hv, finiteAdelicGL2On_not_mem Sᶜ _ v (fun h => h hv), mul_one]
  · rw [finiteAdelicGL2On_not_mem S _ v hv, finiteAdelicGL2On_mem Sᶜ _ v hv, one_mul]

/-- Original matrices supported on complementary actual place sets commute. -/
theorem finiteAdelicGL2On_compl_commute (g h : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Commute (finiteAdelicGL2On S g) (finiteAdelicGL2On Sᶜ h) := by
  apply finiteAdelicGL2_ext
  intro v
  simp only [map_mul]
  by_cases hv : v ∈ S
  · rw [finiteAdelicGL2On_not_mem Sᶜ _ v (fun h => h hv), mul_one, one_mul]
  · rw [finiteAdelicGL2On_not_mem S _ v hv, mul_one, one_mul]

end
end Dubon2026
