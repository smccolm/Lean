import Dubon2026.AdelicLocalSphericalFormula
import Dubon2026.AdelicUnitReferenceVector

/-! # The actual unit-reference local spherical function with its exact normalized formula -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original normalized local unit-reference radial coefficient is exactly the spherical polynomial of the actual primitive Fourier eigenvalue. -/
theorem adelicLocalUnitReference_radial_formula {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicCyclicUnitReference F.toCuspForm) (adelicCyclicUnitReference F.toCuspForm) n =
      sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n := by
  have he := adelicCyclicLocal_primitive_radial_formula F hpN
    (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _) n
  have hn : inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicHilbertGenerator F.toCuspForm) ≠ 0 :=
    (@inner_self_ne_zero ℂ (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
      (adelicCyclicHilbertGenerator F.toCuspForm)).mpr
      (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F))
  refine (@complex_inverse_norm_coefficient
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _)
    (adelicCyclicHilbertGenerator F.toCuspForm)
    ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p)) ^ n)).trans ?_
  exact (congrArg (fun z : ℂ => z / inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicHilbertGenerator F.toCuspForm)) he).trans (mul_div_cancel_left₀ _ hn)

end
end Dubon2026
