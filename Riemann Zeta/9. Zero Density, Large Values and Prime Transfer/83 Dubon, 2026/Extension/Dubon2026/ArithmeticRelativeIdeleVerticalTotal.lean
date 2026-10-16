import Dubon2026.ArithmeticOrbitCommonPrimeSelfDegree
import Dubon2026.ArithmeticRelativeStageIdeleCommonInvariant
import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeComparison
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant

/-! # Canonical idele invariants under same-base extension

The lower orbit and its chosen representative stay fixed under vertical
extension. The original local comparison therefore has degree factor one
at every canonical prime. This is the total-preservation step needed to
identify DUB-17's class invariant through a principal lift.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKL : K ≤ L) (hLM : L ≤ M)
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKL.trans hLM)).toAlgebra
    IsGalois K M]

/-- Same-base extension preserves the canonical lower-orbit invariant of every actual idele class. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_vertical_orbit
    (p : ℕ) (hp : p.Prime)
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a K)
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL) :
    rationalArithmeticRelativeStageIdeleOrbitInvariant a p hp K M (hKL.trans hLM) c
      (rationalArithmeticRelativeStageIdeleBaseChange a K K L M le_rfl hKL (hKL.trans hLM) hLM x) =
      rationalArithmeticRelativeStageIdeleOrbitInvariant a p hp K L hKL c x := by
  have hA : (IntermediateField.inclusion (le_refl K)).toAlgebra = Algebra.id K := by
    ext x
    rfl
  have h := rationalArithmeticRelativeStageIdeleBaseChange_commonInvariant
    (hGalKE := by rw [hA]; infer_instance) (hGalKL := hGalKL) (hGalEM := hGalKM)
    a K K L M le_rfl hKL (hKL.trans hLM) hLM p hp c.out x
  simpa only [rationalArithmeticOrbitCommonPrimeDegree_self, one_nsmul,
    rationalArithmeticRelativeStageIdeleRepresentativeInvariant_out] using h

/-- Same-base extension preserves each actual canonical original-prime coordinate. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_vertical_prime
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL) :
    rationalArithmeticRelativeStageIdelePrimeInvariant a K M (hKL.trans hLM) w
      (rationalArithmeticRelativeStageIdeleBaseChange a K K L M le_rfl hKL (hKL.trans hLM) hLM x) =
      rationalArithmeticRelativeStageIdelePrimeInvariant a K L hKL w x := by
  let p := rationalArithmeticOriginalPrimeBase a K w
  exact rationalArithmeticRelativeStageIdeleBaseChange_vertical_orbit
    (hGalKL := hGalKL) (hGalKM := hGalKM) a K L M hKL hLM p.val p.property _ x

/-- Same-base extension preserves the canonical finite sum of all original-prime invariants. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_vertical_total
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKL.trans hLM)
      (rationalArithmeticRelativeStageIdeleBaseChange a K K L M le_rfl hKL (hKL.trans hLM) hLM x) =
      rationalArithmeticRelativeStageIdeleTotalInvariant a K L hKL x := by
  exact finsum_congr fun w => rationalArithmeticRelativeStageIdeleBaseChange_vertical_prime
    (hGalKL := hGalKL) (hGalKM := hGalKM) a K L M hKL hLM w x

end
end Dubon2026
