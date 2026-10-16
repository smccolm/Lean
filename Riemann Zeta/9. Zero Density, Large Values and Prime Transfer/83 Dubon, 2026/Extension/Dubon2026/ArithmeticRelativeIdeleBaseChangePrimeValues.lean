import Dubon2026.ArithmeticRelativeStageIdeleCommonInvariant
import Dubon2026.ArithmeticRelativeStageIdelePrimeRepresentative
import Dubon2026.ArithmeticOrbitCommonPrimeDegreeCard

/-! # The canonical original-prime values of the auxiliary base change

Convert the constructed source representative values into the canonical
target-prime coordinates. The local factor is the actual decomposition
group order, and its support is the actual original prime fibre. This is
the coordinate identification needed before DUB-17's finite-fibre sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]

/-- Actual source representative values determine every canonical target-prime value of the same base-changed idele class, with the proved local decomposition degree. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_primeValues
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (z : AddCircle (1 : ℚ))
    (hx : ∀ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp K L hKL σ x =
        if rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ) = v then z else 0)
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    rationalArithmeticRelativeStageIdelePrimeInvariant a E M hEM u
      (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) =
      if originalFinitePrimeBelow K E u = v then
        Nat.card (OriginalFiniteDecompositionGroup K E u) • z else 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGalKE
  obtain ⟨p, hp, σ, hu, hi⟩ :=
    rationalArithmeticRelativeStageIdelePrimeInvariant_exists_representative a E M hEM u
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K E hKE σ
  have hv : rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ) =
      originalFinitePrimeBelow K E u :=
    (originalFinitePrimeBelow_eq_of_liesOver K E
      (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ))).symm.trans
        (congrArg (originalFinitePrimeBelow K E) hu)
  have hd := rationalArithmeticOrbitCommonPrimeDegree_eq_decomposition_card a p hp K E hKE σ
  rw [hi, rationalArithmeticRelativeStageIdeleBaseChange_commonInvariant,
    hx p hp σ, hv, hd, hu]
  simp only [smul_ite, smul_zero]

end
end Dubon2026
