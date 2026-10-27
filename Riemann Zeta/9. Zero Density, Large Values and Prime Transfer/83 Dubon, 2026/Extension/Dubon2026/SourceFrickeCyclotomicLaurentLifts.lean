import Dubon2026.SourceFrickeLaurentIntegralSpan

/-! DUB-17/18 -> rational Fourier spanning -> holomorphic recovery of integral
Fricke Laurent summands. Each element of the original cyclotomic Laurent
algebra has an actual cyclotomic j/Fricke function representative. Native
fraction-ring surjectivity then gives the actual numerator and denominator
for each element of the original generated Laurent field. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold MatrixGroups ModularForm IntermediateField IntermediateField.algebraAdjoinAdjoin

theorem exists_cyclotomic_function_of_laurent_algebra {N : ℕ} [NeZero N]
    {A : LaurentSeries ℂ} (hA : A ∈ Algebra.adjoin (kN N) (frickeLaurentGenerators N)) :
    ∃ a ∈ cyclotomicLevelRing N, CuspTaylor.Represents A (cuspFunction N a) := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    rcases hA with rfl | ⟨i, rfl⟩
    · exact ⟨JMultiplicity.jf, Algebra.subset_adjoin (Set.mem_insert _ _), represents_jqNModC N⟩
    · exact ⟨frickeF N i.1, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩),
        represents_frickeLaurentK N i⟩
  | algebraMap c =>
    exact ⟨algebraMap (kN N) (ℍ → ℂ) c, Subalgebra.algebraMap_mem _ c,
      CuspTaylor.represents_cusp_const N (c : ℂ)⟩
  | add X Y _ _ hX hY =>
    obtain ⟨a, ha, hAr⟩ := hX
    obtain ⟨b, hb, hBr⟩ := hY
    exact ⟨a + b, Subalgebra.add_mem _ ha hb, hAr.cusp_add hBr⟩
  | mul X Y _ _ hX hY =>
    obtain ⟨a, ha, hAr⟩ := hX
    obtain ⟨b, hb, hBr⟩ := hY
    exact ⟨a * b, Subalgebra.mul_mem _ ha hb, hAr.cusp_mul hBr⟩

theorem exists_cyclotomic_function_fraction_of_laurent_field {N : ℕ} [NeZero N]
    {X : LaurentSeries ℂ} (hX : X ∈ ConstantDescent.KFld (kN N) (frickeLaurentGenerators N)) :
    ∃ (a b : ℍ → ℂ) (A B : LaurentSeries ℂ),
      a ∈ cyclotomicLevelRing N ∧ b ∈ cyclotomicLevelRing N ∧ b ≠ 0 ∧ B ≠ 0 ∧
      CuspTaylor.Represents A (cuspFunction N a) ∧
      CuspTaylor.Represents B (cuspFunction N b) ∧ X = A / B := by
  let R := Algebra.adjoin (kN N) (frickeLaurentGenerators N)
  let E := IntermediateField.adjoin (kN N) (frickeLaurentGenerators N)
  obtain ⟨A, B, hB, hAB⟩ := IsFractionRing.div_surjective (A := R) (⟨X, hX⟩ : E)
  have hB0 : (B : LaurentSeries ℂ) ≠ 0 := fun h => (nonZeroDivisors.ne_zero hB) (Subtype.ext h)
  have hfrac : (A : LaurentSeries ℂ) / (B : LaurentSeries ℂ) = X := by
    have h := congrArg (fun y : E => (y : LaurentSeries ℂ)) hAB
    simpa only [IntermediateField.coe_div, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
      using h
  obtain ⟨a, ha, hAr⟩ := exists_cyclotomic_function_of_laurent_algebra A.property
  obtain ⟨b, hb, hBr⟩ := exists_cyclotomic_function_of_laurent_algebra B.property
  have hb0 : b ≠ 0 := by
    intro h
    have hz : CuspTaylor.Represents 0 (cuspFunction N b) := by
      simpa only [h, map_zero] using CuspTaylor.represents_cusp_const (N : ℝ) 0
    exact hB0 (hBr.eq_series hz)
  exact ⟨a, b, A, B, ha, hb, hb0, hB0, hAr, hBr, hfrac.symm⟩

end
end Dubon2026.SourceFricke