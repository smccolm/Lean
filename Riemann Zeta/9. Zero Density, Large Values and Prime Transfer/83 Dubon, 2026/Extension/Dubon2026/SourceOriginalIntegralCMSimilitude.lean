import Dubon2026.SourceOriginalIntegralOdd

/-! DUB-17/18 -> actual mixed-characteristic CM deformation input. The
original integral determinant with the native quadratic sign correction gives
the required odd integral similitude. Its restriction to the actual CM kernel
reduces to the determinant multiplier of the original residual symmetric power. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix
open scoped NumberField

/-- Preserve the original rational scalar structure in the integral multiplier. -/
private local instance originalIntegralCMUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F]
  (C : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F C]
  {O : Type} [CommRing O]
  (n : ℕ) (ρi : finiteBaseArithmeticGaloisGroup a F →* GeneralLinearGroup (Fin 2) O)

/-- The original integral determinant, with the exact native CM sign correction. -/
def originalIntegralCMSymmetricSimilitude : finiteBaseArithmeticGaloisGroup a F →* Oˣ :=
  (GeneralLinearGroup.det.comp ρi) ^ n *
    (polarizedComponentSign.comp (finiteBaseQuadraticComponent a F C).toMonoidHom) ^ (n + 1)

/-- On the genuine CM kernel the integral character is the original determinant power. -/
theorem original_integral_cm_similitude_kernel (g : FiniteBaseCMKernel a F C) :
    originalIntegralCMSymmetricSimilitude a F C n ρi g.val =
      (GeneralLinearGroup.det (ρi g.val)) ^ n := by
  change (GeneralLinearGroup.det (ρi g.val)) ^ n *
    (polarizedComponentSign (finiteBaseQuadraticComponent a F C g.val)) ^ (n + 1) = _
  have hg : finiteBaseQuadraticComponent a F C g.val = 1 := g.property
  rw [hg, map_one, one_pow, mul_one]

/-- The original integral real sign supplies an odd CM similitude in every degree. -/
theorem original_integral_cm_similitude_odd [IsTotallyReal F] [IsTotallyComplex C]
    (hodd : (ρi (finiteBaseRealConjugation a F)).val.det = -1) :
    originalIntegralCMSymmetricSimilitude a F C n ρi (finiteBaseRealConjugation a F) = -1 := by
  have hd : GeneralLinearGroup.det (ρi (finiteBaseRealConjugation a F)) = -1 := Units.ext hodd
  have hs : polarizedComponentSign (R := O) (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
    change (if (1 : ZMod 2) = 0 then 1 else (-1 : Oˣ)) = -1
    norm_num
  have hp : (-1 : Oˣ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  change (GeneralLinearGroup.det (ρi (finiteBaseRealConjugation a F))) ^ n *
    (polarizedComponentSign (finiteBaseQuadraticComponent a F C (finiteBaseRealConjugation a F))) ^ (n + 1) = -1
  rw [hd, finiteBaseCMComponent_conjugation, hs, pow_succ, ← mul_assoc, hp, one_mul]

/-- Literal residual reduction of the original integral matrices supplies the
native CM-kernel multiplier equation; no independent lifting certificate is assumed. -/
theorem original_integral_cm_similitude_reduction
    {L : Type} [Field L] (r : O →+* L)
    (ρr : finiteBaseArithmeticGaloisGroup a F →* GeneralLinearGroup (Fin 2) L)
    (hred : ∀ g i j, (ρr g).val i j = r ((ρi g).val i j))
    (g : FiniteBaseCMKernel a F C) :
    (GeneralLinearGroup.det (ρr g.val)) ^ n =
      Units.map r (originalIntegralCMSymmetricSimilitude a F C n ρi g.val) := by
  rw [original_integral_cm_similitude_kernel, map_pow]
  congr 1
  apply Units.ext
  exact (original_integral_residual_determinant_map r ρi ρr hred g.val).symm

end
end Dubon2026.SourceDickson
