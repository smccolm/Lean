import Dubon2026.AdelicUnitReferenceVector
import Dubon2026.AdelicLocalFullAwayTensorCompletion
import Dubon2026.TensorReferenceInclusion

/-! # Exact original unit reference compatibility of the genuine local tensor isometry -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual original unit reference viewed inside its genuine algebraic local orbit core. -/
def adelicLocalUnitReference (v : HeightOneSpectrum ℤ) : adelicLocalCyclicCore f v :=
  (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ •
    ⟨adelicCyclicHilbertGenerator f, adelicLocalCyclicCore_generator_mem f v⟩

/-- The actual original unit reference viewed inside its genuine full complementary algebraic orbit core. -/
def adelicFullAwayUnitReference (v : HeightOneSpectrum ℤ) : adelicFullAwayCyclicCore f v :=
  (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ •
    ⟨adelicCyclicHilbertGenerator f, adelicFullAwayCyclicCore_generator_mem f v⟩

/-- The genuine local reference is literally the original normalized Hilbert generator. -/
theorem adelicLocalUnitReference_val (v : HeightOneSpectrum ℤ) :
    (adelicLocalUnitReference f v).val = adelicCyclicUnitReference f := rfl

/-- The genuine complementary reference is literally the same original normalized Hilbert generator. -/
theorem adelicFullAwayUnitReference_val (v : HeightOneSpectrum ℤ) :
    (adelicFullAwayUnitReference f v).val = adelicCyclicUnitReference f := rfl

/-- The original local reference has unit norm in the actual inherited local inner-product space. -/
theorem adelicLocalUnitReference_norm (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    ‖adelicLocalUnitReference f v‖ = 1 := adelicCyclicUnitReference_norm f hf

/-- The original complementary reference has unit norm in the actual inherited complementary inner-product space. -/
theorem adelicFullAwayUnitReference_norm (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    ‖adelicFullAwayUnitReference f v‖ = 1 := adelicCyclicUnitReference_norm f hf

/-- The genuine original tensor isometry sends the tensor of original unit reference vectors to exactly the original global unit reference vector. -/
theorem adelicLocalFullAwayTensorIsometry_unit_reference {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗ₜ[ℂ]
        adelicFullAwayUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
      adelicCyclicUnitReference F.toCuspForm := by
  have hb := adelicLocalFullAwayTensorIsometry_family F hpN (1, 1)
  simp only [adelicLocalFullAwayTensorFamily, adelicLocalFullAwayMixedFamily,
    map_one, Module.End.one_apply] at hb
  have hn : (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr
      (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F))
  exact @tensorMap_inverse_scalar_references
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap
    ⟨adelicCyclicHilbertGenerator F.toCuspForm, adelicLocalCyclicCore_generator_mem F.toCuspForm _⟩
    ⟨adelicCyclicHilbertGenerator F.toCuspForm, adelicFullAwayCyclicCore_generator_mem F.toCuspForm _⟩
    (adelicCyclicHilbertGenerator F.toCuspForm) (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) hn hb

end
end Dubon2026
