import Dubon2026.CanonicalAdelicLiftLinear
import Dubon2026.PrimitiveFullEigen

/-! # Actual finite-adelic Hecke eigenvalues of the original primitive cusp generator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

/-- The original algebraic adelic generator has its genuine good-prime Hecke eigenvalue with exactly the pinned determinant-root normalization. -/
theorem adelicAlgebraicHeckeTrace_primitive_generator {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (f : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicAlgebraicHeckeTrace f.toCuspForm p hpN (adelicCyclicGenerator N f.toCuspForm) =
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * cuspCoefficients f.toCuspForm p) •
        adelicCyclicGenerator N f.toCuspForm := by
  apply Subtype.ext
  have ht := adelicAlgebraicHeckeTrace_classical_full f.toCuspForm p hpN
    (adelicCyclicGenerator N f.toCuspForm) f.toCuspForm rfl
  have he : cuspHecke p f.toCuspForm = cuspCoefficients f.toCuspForm p • f.toCuspForm :=
    primitiveCuspForm_eigenvector_all f (Fact.out : p.Prime).pos
  rw [he, smul_smul] at ht
  exact ht.trans (canonicalAdelicGL2CuspLift_smul N k _ f.toCuspForm)

/-- The original completed primitive cusp generator has precisely the same actual finite-adelic Hecke eigenvalue. -/
theorem adelicHilbertHeckeTrace_primitive_generator {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (f : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicHilbertHeckeTrace f.toCuspForm p hpN (adelicCyclicHilbertGenerator f.toCuspForm) =
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * cuspCoefficients f.toCuspForm p) •
        adelicCyclicHilbertGenerator f.toCuspForm := by
  change adelicHilbertHeckeTrace f.toCuspForm p hpN
    (adelicCyclicHilbertEmbedding f.toCuspForm (adelicCyclicGenerator N f.toCuspForm)) = _
  rw [← adelicHeckeTrace_embedding, adelicAlgebraicHeckeTrace_primitive_generator, map_smul]
  rfl

end
end Dubon2026
